// solver_strong.cpp -- df-pn solver for the strong (maker-maker) polyomino achievement game
// on an n x n board (n <= 8), question: can X (first player) force a win within K of its own moves?
//
// Rules: X and O alternately claim a free cell, X first. The first player to own all cells of a
// placement (translation/rotation/reflection of the shape) wins. A full board is a draw.
// "X wins within K" = X completes a copy on one of its first K moves and O has not completed one before.
//
// Usage: see ../README.md. Every run ends with a line "DONE ..." or "ABORT ...".
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>
#include <algorithm>
#include <chrono>
#include <unordered_set>
#include <sys/resource.h>
#include <unistd.h>
using namespace std;
typedef uint64_t u64;
typedef uint32_t u32;

// ---------------------------------------------------------------- board, placements, symmetry
static int n, N;
static u64 FULL;
static vector<u64> PL;
static int K;

static void buildPlacements(const vector<pair<int,int>> &shape) {
  vector<u64> all;
  for (int s = 0; s < 8; s++) {
    vector<pair<int,int>> T;
    for (auto [x, y] : shape) {
      int a = x, b = y;
      if (s & 1) swap(a, b);
      if (s & 2) a = -a;
      if (s & 4) b = -b;
      T.push_back({a, b});
    }
    // plain index loops: clang 21 -O2 loop vectorizer miscompiled a range-for version of this (../README.md, build note)
    int mx = 1 << 20, my = 1 << 20, w = 0, h = 0;
    for (size_t i = 0; i < T.size(); i++) { if (T[i].first < mx) mx = T[i].first; if (T[i].second < my) my = T[i].second; }
    for (size_t i = 0; i < T.size(); i++) {
      T[i].first -= mx; T[i].second -= my;
      if (T[i].first + 1 > w) w = T[i].first + 1;
      if (T[i].second + 1 > h) h = T[i].second + 1;
    }
    for (int ox = 0; ox + w <= n; ox++)
      for (int oy = 0; oy + h <= n; oy++) {
        u64 m = 0;
        for (auto [a, b] : T) m |= 1ULL << ((oy + b) * n + ox + a);
        all.push_back(m);
      }
  }
  sort(all.begin(), all.end());
  all.erase(unique(all.begin(), all.end()), all.end());
  PL = all;
}

static int symCell[8][64];          // image of cell c under symmetry s
static int symInv[8];
static u64 symTab[8][8][256];
static void initSym() {
  for (int s = 0; s < 8; s++)
    for (int c = 0; c < N; c++) {
      int x = c % n, y = c / n;
      int a = x, b = y;
      if (s & 1) swap(a, b);
      if (s & 2) a = n - 1 - a;
      if (s & 4) b = n - 1 - b;
      symCell[s][c] = b * n + a;
    }
  for (int s = 0; s < 8; s++)
    for (int t = 0; t < 8; t++) {
      bool ok = true;
      for (int c = 0; c < N; c++) if (symCell[t][symCell[s][c]] != c) { ok = false; break; }
      if (ok) symInv[s] = t;
    }
  for (int s = 0; s < 8; s++)
    for (int byte = 0; byte < 8; byte++)
      for (int v = 0; v < 256; v++) {
        u64 o = 0;
        for (int bit = 0; bit < 8; bit++)
          if (v >> bit & 1) { int c = byte * 8 + bit; if (c < N) o |= 1ULL << symCell[s][c]; }
        symTab[s][byte][v] = o;
      }
}
static inline u64 applySym(int s, u64 x) {
  u64 o = 0;
  for (int b = 0; b < 8 && x; b++, x >>= 8) o |= symTab[s][b][x & 255];
  return o;
}
// canonical form: lexicographically least (X',O') over the 8 maps; returns the map used
static inline int canon(u64 X, u64 O, u64 &cx, u64 &co) {
  cx = X; co = O; int best = 0;
  for (int s = 1; s < 8; s++) {
    u64 a = applySym(s, X);
    if (a > cx) continue;
    u64 b = applySym(s, O);
    if (a < cx || b < co) { cx = a; co = b; best = s; }
  }
  return best;
}

// ---------------------------------------------------------------- limits / stats
static chrono::steady_clock::time_point T0;
static double timeLimit = 1e18;
static long maxRssMb = 6000;
static u64 nodes = 0;
static bool aborted = false;
static string abortReason;
static double elapsed() { return chrono::duration<double>(chrono::steady_clock::now() - T0).count(); }
static long rssMb() {
  struct rusage ru; getrusage(RUSAGE_SELF, &ru);
#ifdef __APPLE__
  return ru.ru_maxrss >> 20;
#else
  return ru.ru_maxrss >> 10;
#endif
}
static long curRssMb() {  // current resident size is approximated by the peak (monotone, conservative)
  return rssMb();
}
static double progSecG = 600, lastProg = 0, lastCk = 0;
static void progressHook();
static void checkLimits() {
  if (aborted) return;
  progressHook();
  if (elapsed() > timeLimit) { aborted = true; abortReason = "time"; }
  else if (curRssMb() > maxRssMb) { aborted = true; abortReason = "rss"; }
}

// ---------------------------------------------------------------- pairing (weak Breaker) leaf
static bool usePairing = true;
static int pairBudget = 2000;
// Disjoint pairs of free cells such that every X-live placement with 2 <= miss <= r contains a pair.
static int pairSteps;
static bool pairRec(vector<u64> &need, u64 used, vector<pair<int,int>> &out) {
  if (++pairSteps > pairBudget) return false;
  // pick uncovered placement with fewest options
  int bi = -1, bopt = 1000;
  for (size_t i = 0; i < need.size(); i++) {
    u64 m = need[i];
    if (!m) continue;
    // covered? (a chosen pair inside) -- handled by removing; here m is list of free cells not yet used
    int f = __builtin_popcountll(m & ~used);
    int opt = f * (f - 1) / 2;
    if (opt < bopt) { bopt = opt; bi = (int)i; }
  }
  if (bi < 0) return true;
  if (bopt == 0) return false;
  u64 m = need[bi] & ~used;
  int cs[64], k = 0;
  for (u64 t = m; t; t &= t - 1) cs[k++] = __builtin_ctzll(t);
  for (int i = 0; i < k; i++)
    for (int j = i + 1; j < k; j++) {
      u64 pr = (1ULL << cs[i]) | (1ULL << cs[j]);
      vector<u64> sav;
      sav.reserve(need.size());
      // mark covered placements
      vector<int> cov;
      for (size_t q = 0; q < need.size(); q++) if (need[q] && (need[q] & pr) == pr) { cov.push_back((int)q); }
      for (int q : cov) { sav.push_back(need[q]); need[q] = 0; }
      out.push_back({cs[i], cs[j]});
      if (pairRec(need, used | pr, out)) return true;
      out.pop_back();
      for (size_t z = 0; z < cov.size(); z++) need[cov[z]] = sav[z];
      if (pairSteps > pairBudget) return false;
    }
  return false;
}
static bool findPairing(u64 X, u64 O, int r, vector<pair<int,int>> *out) {
  vector<u64> need;
  for (u64 p : PL) {
    if (p & O) continue;
    u64 m = p & ~X;
    int c = __builtin_popcountll(m);
    if (c > r) continue;
    if (c < 2) return false;
    need.push_back(m);
  }
  vector<pair<int,int>> tmp;
  pairSteps = 0;
  bool ok = pairRec(need, 0, tmp);
  if (ok && out) *out = tmp;
  return ok;
}

// ---------------------------------------------------------------- node evaluation
// status: 0 unknown, 1 X wins (proved), 2 X does not win (disproved)
struct Gen { int status; int nm; int mv[64]; };
static u64 statPair = 0;

// X to move. r = moves X still may make.
static void genX(u64 X, u64 O, Gen &g, bool full) {
  g.status = 0; g.nm = 0;
  int r = K - __builtin_popcountll(X);
  u64 freeC = FULL & ~(X | O);
  if (r <= 0 || !freeC) { g.status = 2; return; }
  u64 T = 0, rel = 0;
  int score[64];
  if (full) memset(score, 0, sizeof(score));
  static const int Wt[9] = {1, 6, 36, 216, 1296, 7776, 46656, 279936, 1679616};
  bool anyXrel = false;
  for (u64 p : PL) {
    if (!(p & O)) {
      u64 m = p & ~X; int c = __builtin_popcountll(m);
      if (c == 1) { g.status = 1; g.nm = 1; g.mv[0] = __builtin_ctzll(m); return; }
      if (c <= r) {
        rel |= m; anyXrel = true;
        if (full) { int w = Wt[__builtin_popcountll(p & X)]; for (u64 t = m; t; t &= t - 1) score[__builtin_ctzll(t)] += w; }
      }
    }
    if (!(p & X)) {
      u64 m = p & ~O; int c = __builtin_popcountll(m);
      if (c == 1) T |= m;
      else if (c <= r - 1) {
        rel |= m;
        if (full) { int w = Wt[__builtin_popcountll(p & O)]; for (u64 t = m; t; t &= t - 1) score[__builtin_ctzll(t)] += w; }
      }
    }
  }
  if (T & (T - 1)) { g.status = 2; return; }      // two O threats: X cannot complete now, O completes next
  if (r == 1) { g.status = 2; return; }           // no immediate completion on X's last move
  if (!anyXrel) { g.status = 2; return; }         // X has no live placement completable within r moves
  if (T) { g.nm = 1; g.mv[0] = __builtin_ctzll(T); return; }
  if (usePairing && full && findPairing(X, O, r, nullptr)) { statPair++; g.status = 2; return; }
  if (!full) { g.nm = __builtin_popcountll(rel); return; }
  for (u64 t = rel; t; t &= t - 1) g.mv[g.nm++] = __builtin_ctzll(t);
  sort(g.mv, g.mv + g.nm, [&](int a, int b) { return score[a] > score[b] || (score[a] == score[b] && a < b); });
}
// O to move. r = moves X still may make.
static void genO(u64 X, u64 O, Gen &g, bool full) {
  g.status = 0; g.nm = 0;
  int r = K - __builtin_popcountll(X);
  u64 freeC = FULL & ~(X | O);
  if (r <= 0 || !freeC) { g.status = 2; return; }
  u64 T = 0, rel = 0;
  int score[64];
  if (full) memset(score, 0, sizeof(score));
  static const int Wt[9] = {1, 6, 36, 216, 1296, 7776, 46656, 279936, 1679616};
  bool anyXrel = false;
  for (u64 p : PL) {
    if (!(p & X)) {
      u64 m = p & ~O; int c = __builtin_popcountll(m);
      if (c == 1) { g.status = 2; g.nm = 1; g.mv[0] = __builtin_ctzll(m); return; }  // O completes
      if (c <= r) {
        rel |= m;
        if (full) { int w = Wt[__builtin_popcountll(p & O)]; for (u64 t = m; t; t &= t - 1) score[__builtin_ctzll(t)] += w; }
      }
    }
    if (!(p & O)) {
      u64 m = p & ~X; int c = __builtin_popcountll(m);
      if (c == 1) T |= m;
      if (c <= r) {
        rel |= m; anyXrel = true;
        if (full) { int w = Wt[__builtin_popcountll(p & X)]; for (u64 t = m; t; t &= t - 1) score[__builtin_ctzll(t)] += 2 * w; }
      }
    }
  }
  if (T & (T - 1)) { g.status = 1; return; }      // two X threats, O cannot complete now
  if (!anyXrel) { g.status = 2; return; }
  if (T) { g.nm = 1; g.mv[0] = __builtin_ctzll(T); return; }
  if (r == 1) { g.status = 2; return; }           // X has no threat and only one move left
  if (!full) { g.nm = __builtin_popcountll(rel); return; }
  for (u64 t = rel; t; t &= t - 1) g.mv[g.nm++] = __builtin_ctzll(t);
  sort(g.mv, g.mv + g.nm, [&](int a, int b) { return score[a] > score[b] || (score[a] == score[b] && a < b); });
}

// ---------------------------------------------------------------- transposition table
static const u32 INF = 0x3fffffff;
struct Ent { u64 x, o; u32 pn, dn; u32 work; u32 pad; };
static Ent *tt; static u64 ttMask; static int ttLog = 24;
static inline u64 hsh(u64 a, u64 b) {
  u64 h = a * 0x9E3779B97F4A7C15ULL ^ (b + 0x632BE59BD9B4E019ULL) * 0xC2B2AE3D27D4EB4FULL;
  h ^= h >> 29; h *= 0xBF58476D1CE4E5B9ULL; h ^= h >> 32;
  return h;
}
static const int BUCKET = 4;
static inline Ent *ttFind(u64 x, u64 o) {
  Ent *b = &tt[(hsh(x, o) & ttMask) * BUCKET];
  for (int i = 0; i < BUCKET; i++) if (b[i].x == x && b[i].o == o && (b[i].pn | b[i].dn)) return &b[i];
  return nullptr;
}
static u64 ttStores = 0, ttOver = 0;
static inline void ttStore(u64 x, u64 o, u32 pn, u32 dn, u32 work) {
  Ent *b = &tt[(hsh(x, o) & ttMask) * BUCKET];
  Ent *v = nullptr;
  for (int i = 0; i < BUCKET; i++) if (b[i].x == x && b[i].o == o && (b[i].pn | b[i].dn)) { v = &b[i]; break; }
  if (!v) {
    for (int i = 0; i < BUCKET; i++) if (!(b[i].pn | b[i].dn)) { v = &b[i]; break; }
    if (!v) {
      ttOver++;
      // replace the entry with the least work; proved/disproved entries get a bonus
      u64 bestScore = ~0ULL;
      for (int i = 0; i < BUCKET; i++) {
        u64 sc = (u64)b[i].work * ((b[i].pn == 0 || b[i].dn == 0) ? 4 : 1);
        if (sc < bestScore) { bestScore = sc; v = &b[i]; }
      }
    }
  }
  v->x = x; v->o = o; v->pn = pn; v->dn = dn; v->work = work; ttStores++;
}

// ---------------------------------------------------------------- df-pn
static int epsShift = 2;   // 1+eps trick, eps = 1/4
struct Child { u64 x, o; u32 ipn, idn; int mv; };

static inline u32 addSat(u32 a, u32 b) { u64 s = (u64)a + b; return s >= INF ? INF - 1 : (u32)s; }

// node = (X,O) actual (not canonical); xTurn derived from counts
static void mid(u64 X, u64 O, u32 thpn, u32 thdn, u32 &rpn, u32 &rdn, u32 &rwork) {
  nodes++;
  if ((nodes & 0xFFFF) == 0) checkLimits();
  bool xTurn = __builtin_popcountll(X) == __builtin_popcountll(O);
  u64 cx, co; canon(X, O, cx, co);
  Gen g;
  if (xTurn) genX(X, O, g, true); else genO(X, O, g, true);
  if (g.status) {
    rpn = g.status == 1 ? 0 : INF; rdn = g.status == 1 ? INF : 0; rwork = 1;
    ttStore(cx, co, rpn, rdn, 1);
    return;
  }
  int nc = g.nm;
  Child ch[64];
  for (int i = 0; i < nc; i++) {
    u64 X2 = X, O2 = O;
    if (xTurn) X2 |= 1ULL << g.mv[i]; else O2 |= 1ULL << g.mv[i];
    ch[i].mv = g.mv[i];
    canon(X2, O2, ch[i].x, ch[i].o);
    Gen h;
    if (xTurn) genO(X2, O2, h, false); else genX(X2, O2, h, false);
    if (h.status == 1) { ch[i].ipn = 0; ch[i].idn = INF; }
    else if (h.status == 2) { ch[i].ipn = INF; ch[i].idn = 0; }
    else if (xTurn) { ch[i].ipn = h.nm; ch[i].idn = 1; }   // child is an AND node (O to move)
    else { ch[i].ipn = 1; ch[i].idn = h.nm; }              // child is an OR node (X to move)
  }
  u32 work = 1;
  u32 pn = 0, dn = 0;
  while (true) {
    int best = -1; u32 b1 = INF + 1, b2 = INF + 1, bestOther = 0;
    u32 sum = 0;
    for (int i = 0; i < nc; i++) {
      Ent *e = ttFind(ch[i].x, ch[i].o);
      u32 cpn = e ? e->pn : ch[i].ipn, cdn = e ? e->dn : ch[i].idn;
      if (xTurn) {
        sum = addSat(sum, cdn);
        if (cpn < b1) { b2 = b1; b1 = cpn; best = i; bestOther = cdn; }
        else if (cpn < b2) b2 = cpn;
      } else {
        sum = addSat(sum, cpn);
        if (cdn < b1) { b2 = b1; b1 = cdn; best = i; bestOther = cpn; }
        else if (cdn < b2) b2 = cdn;
      }
    }
    if (xTurn) { pn = b1; dn = (b1 == 0) ? INF : sum; if (pn >= INF) { pn = INF; dn = 0; } }
    else { dn = b1; pn = (b1 == 0) ? INF : sum; if (dn >= INF) { dn = INF; pn = 0; } }
    if (pn == 0 || dn == 0) break;
    if (pn >= thpn || dn >= thdn || aborted) break;
    u32 cth1, cth2, cpn, cdn, cw;
    u64 X2 = X, O2 = O;
    if (xTurn) {
      X2 |= 1ULL << ch[best].mv;
      u32 lim = b2 >= INF ? INF : min<u64>((u64)INF, (u64)b2 + max<u32>(1, b2 >> epsShift));
      cth1 = min(thpn, lim);
      cth2 = (u32)min<u64>(INF, (u64)thdn - dn + bestOther);
      mid(X2, O2, cth1, cth2, cpn, cdn, cw);
    } else {
      O2 |= 1ULL << ch[best].mv;
      u32 lim = b2 >= INF ? INF : min<u64>((u64)INF, (u64)b2 + max<u32>(1, b2 >> epsShift));
      cth2 = min(thdn, lim);
      cth1 = (u32)min<u64>(INF, (u64)thpn - pn + bestOther);
      mid(X2, O2, cth1, cth2, cpn, cdn, cw);
    }
    work = addSat(work, cw);
    if (aborted) break;
  }
  rpn = pn; rdn = dn; rwork = work;
  ttStore(cx, co, pn, dn, work);
}

// solve from a position with full thresholds; returns 1 X wins, 2 X fails, 0 aborted
static int solve(u64 X, u64 O) {
  u64 cx, co; canon(X, O, cx, co);
  Ent *e = ttFind(cx, co);
  if (e && e->pn == 0) return 1;
  if (e && e->dn == 0) return 2;
  u32 pn, dn, w;
  mid(X, O, INF, INF, pn, dn, w);
  if (aborted) return 0;
  return pn == 0 ? 1 : (dn == 0 ? 2 : 0);
}

// ---------------------------------------------------------------- certificate export
static FILE *certF = nullptr;
static u64 certLines = 0, certPairs = 0;
static unordered_set<unsigned __int128> seenX, seenO;
static inline unsigned __int128 key128(u64 a, u64 b) { return ((unsigned __int128)a << 64) | b; }
static bool exportFail = false;
static string exportMsg;
static long maxCertMb = 20000;

static bool completes(u64 S) { for (u64 p : PL) if ((p & S) == p) return true; return false; }

// X-win strategy: X-to-move positions -> X move. Exhaustive over O replies.
static void expXwinX(u64 X, u64 O);
static void expXwinO(u64 X, u64 O) {  // O to move, every free cell
  u64 freeC = FULL & ~(X | O);
  for (u64 t = freeC; t && !exportFail && !aborted; t &= t - 1) {
    u64 O2 = O | (t & -t);
    if (completes(O2)) { exportFail = true; exportMsg = "O completes in X-win export"; return; }
    expXwinX(X, O2);
  }
}
static void expXwinX(u64 X, u64 O) {
  if (exportFail || aborted) return;
  u64 cx, co; int s = canon(X, O, cx, co);
  if (!seenX.insert(key128(cx, co)).second) return;
  if ((++certLines & 0xFFF) == 0) { checkLimits(); if (ftell(certF) > maxCertMb * 1048576L) { aborted = true; abortReason = "cert_size"; } }
  if (__builtin_popcountll(X) >= K) { exportFail = true; exportMsg = "budget exhausted in X-win export"; return; }
  // immediate completion?
  int mv = -1;
  for (u64 p : PL) if (!(p & O)) { u64 m = p & ~X; if (__builtin_popcountll(m) == 1) { mv = __builtin_ctzll(m); break; } }
  if (mv < 0) {
    Gen g; genX(X, O, g, true);
    vector<int> cand(g.mv, g.mv + g.nm);
    // prefer moves already proved in the TT
    for (int pass = 0; pass < 2 && mv < 0; pass++) {
      for (int c : cand) {
        u64 X2 = X | (1ULL << c), a, b; canon(X2, O, a, b);
        Ent *e = ttFind(a, b);
        if (pass == 0) { if (e && e->pn == 0) { mv = c; break; } }
        else { int r = solve(X2, O); if (r == 1) { mv = c; break; } if (r == 0) return; }
      }
    }
    if (mv < 0) { exportFail = true; exportMsg = "no winning X move found in export"; return; }
  }
  fprintf(certF, "X %llx %llx %d\n", (unsigned long long)cx, (unsigned long long)co, symCell[s][mv]);
  u64 X2 = X | (1ULL << mv);
  if (completes(X2)) return;
  if (!(FULL & ~(X2 | O))) { exportFail = true; exportMsg = "board full in X-win export"; return; }
  expXwinO(X2, O);
}

// O strategy (X does not win within K): O-to-move positions -> O move; pairing leaves at X-to-move.
static void expOX(u64 X, u64 O);
static bool xHopeless(u64 X, u64 O, int r) {
  for (u64 p : PL) if (!(p & O) && __builtin_popcountll(p & ~X) <= r) return false;
  return true;
}
static void expOO(u64 X, u64 O) {   // O to move
  if (exportFail || aborted) return;
  int r = K - __builtin_popcountll(X);
  u64 freeC = FULL & ~(X | O);
  if (!freeC || r <= 0 || xHopeless(X, O, r)) return;   // leaves the checker accepts by itself
  u64 cx, co; int s = canon(X, O, cx, co);
  if (!seenO.insert(key128(cx, co)).second) return;
  if ((++certLines & 0xFFF) == 0) { checkLimits(); if (ftell(certF) > maxCertMb * 1048576L) { aborted = true; abortReason = "cert_size"; } }
  int mv = -1;
  for (u64 p : PL) if (!(p & X)) { u64 m = p & ~O; if (__builtin_popcountll(m) == 1) { mv = __builtin_ctzll(m); break; } }
  bool oWins = mv >= 0;
  if (!oWins) {
    Gen g; genO(X, O, g, true);
    vector<int> cand(g.mv, g.mv + g.nm);
    for (u64 t = freeC; t; t &= t - 1) { int c = __builtin_ctzll(t); if (find(cand.begin(), cand.end(), c) == cand.end()) cand.push_back(c); }
    for (int pass = 0; pass < 2 && mv < 0; pass++) {
      for (int c : cand) {
        u64 O2 = O | (1ULL << c), a, b; canon(X, O2, a, b);
        Ent *e = ttFind(a, b);
        if (pass == 0) { if (e && e->dn == 0) { mv = c; break; } }
        else { int rr = solve(X, O2); if (rr == 2) { mv = c; break; } if (rr == 0) return; }
      }
    }
    if (mv < 0) { exportFail = true; exportMsg = "no refuting O move found in export"; return; }
  }
  fprintf(certF, "O %llx %llx %d\n", (unsigned long long)cx, (unsigned long long)co, symCell[s][mv]);
  if (!oWins) expOX(X, O | (1ULL << mv));
}
static void expOX(u64 X, u64 O) {   // X to move: every free cell
  if (exportFail || aborted) return;
  int r = K - __builtin_popcountll(X);
  u64 freeC = FULL & ~(X | O);
  if (!freeC || r <= 0 || xHopeless(X, O, r)) return;
  u64 cx, co; int s = canon(X, O, cx, co);
  if (!seenX.insert(key128(cx, co)).second) return;
  vector<pair<int,int>> prs;
  if (usePairing && findPairing(X, O, r, &prs)) {
    fprintf(certF, "P %llx %llx", (unsigned long long)cx, (unsigned long long)co);
    for (auto [a, b] : prs) fprintf(certF, " %d,%d", symCell[s][a], symCell[s][b]);
    fprintf(certF, "\n"); certPairs++;
    return;
  }
  for (u64 t = freeC; t && !exportFail && !aborted; t &= t - 1) {
    u64 X2 = X | (t & -t);
    if (completes(X2)) { exportFail = true; exportMsg = "X completes in O-strategy export"; return; }
    expOO(X2, O);
  }
}

// ---------------------------------------------------------------- checkpoint
static string ckptPath; static double ckptSec = 0;
static bool saveTT(const string &path) {
  string tmp = path + ".tmp";
  FILE *f = fopen(tmp.c_str(), "wb"); if (!f) return false;
  u64 hdr[4] = {0x5354524f4e473601ULL, (u64)ttLog, (u64)K, (u64)PL.size()};
  fwrite(hdr, sizeof(hdr), 1, f);
  u64 cnt = 0;
  for (u64 i = 0; i < (ttMask + 1) * BUCKET; i++) if (tt[i].pn | tt[i].dn) cnt++;
  fwrite(&cnt, 8, 1, f);
  for (u64 i = 0; i < (ttMask + 1) * BUCKET; i++) if (tt[i].pn | tt[i].dn) fwrite(&tt[i], sizeof(Ent), 1, f);
  bool ok = fclose(f) == 0;
  if (ok) rename(tmp.c_str(), path.c_str());
  return ok;
}
static long loadTT(const string &path) {
  FILE *f = fopen(path.c_str(), "rb"); if (!f) return -1;
  u64 hdr[4], cnt;
  if (fread(hdr, sizeof(hdr), 1, f) != 1 || hdr[0] != 0x5354524f4e473601ULL || hdr[2] != (u64)K || hdr[3] != PL.size()) { fclose(f); return -2; }
  if (fread(&cnt, 8, 1, f) != 1) { fclose(f); return -2; }
  Ent e; long got = 0;
  for (u64 i = 0; i < cnt; i++) { if (fread(&e, sizeof(Ent), 1, f) != 1) break; ttStore(e.x, e.o, e.pn, e.dn, e.work); got++; }
  fclose(f);
  return got;
}

// ---------------------------------------------------------------- main
static FILE *resF = nullptr;
static string tag, shapeStr;
static void rec(const char *fmt, ...) __attribute__((format(printf, 1, 2)));
#include <cstdarg>
static void rec(const char *fmt, ...) {
  if (!resF) return;
  va_list ap; va_start(ap, fmt); vfprintf(resF, fmt, ap); va_end(ap);
  fflush(resF);
}

static void progressHook() {
  double el = elapsed();
  if (el - lastProg >= progSecG) {
    lastProg = el;
    u64 used = 0; for (u64 i = 0; i < (ttMask + 1) * BUCKET; i++) if (tt[i].pn | tt[i].dn) used++;
    printf("progress t=%.0fs nodes=%llu tt_used=%llu stores=%llu overwrites=%llu pair_leaves=%llu rss=%ldMB\n", el, (unsigned long long)nodes,
           (unsigned long long)used, (unsigned long long)ttStores, (unsigned long long)ttOver, (unsigned long long)statPair, rssMb());
    fflush(stdout);
    rec("{\"tag\":\"%s\",\"type\":\"progress\",\"board\":%d,\"shape\":\"%s\",\"K\":%d,\"t\":%.0f,\"nodes\":%llu,\"tt_used\":%llu,\"tt_overwrites\":%llu,\"rss_mb\":%ld}\n",
        tag.c_str(), n, shapeStr.c_str(), K, el, (unsigned long long)nodes, (unsigned long long)used, (unsigned long long)ttOver, rssMb());
  }
  if (!ckptPath.empty() && ckptSec > 0 && el - lastCk >= ckptSec) {
    lastCk = el; bool ok = saveTT(ckptPath);
    printf("checkpoint %s %s t=%.0fs\n", ckptPath.c_str(), ok ? "ok" : "FAILED", elapsed()); fflush(stdout);
  }
}

int main(int argc, char **argv) {
  string certPath, resPath, resumePath, kind;
  n = 6; K = 18; shapeStr = "0,0;1,0;2,0;3,0";
  double progSec = 600;
  for (int i = 1; i < argc; i++) {
    string a = argv[i];
    auto nx = [&]() { if (i + 1 >= argc) { fprintf(stderr, "missing value for %s\n", a.c_str()); exit(2); } return string(argv[++i]); };
    if (a == "--board") n = stoi(nx());
    else if (a == "--shape") shapeStr = nx();
    else if (a == "--K") K = stoi(nx());
    else if (a == "--tt-log2") ttLog = stoi(nx());
    else if (a == "--max-rss-mb") maxRssMb = stol(nx());
    else if (a == "--time-limit") timeLimit = stod(nx());
    else if (a == "--cert") certPath = nx();
    else if (a == "--max-cert-mb") maxCertMb = stol(nx());
    else if (a == "--results") resPath = nx();
    else if (a == "--tag") tag = nx();
    else if (a == "--no-pairing") usePairing = false;
    else if (a == "--pair-budget") pairBudget = stoi(nx());
    else if (a == "--eps-shift") epsShift = stoi(nx());
    else if (a == "--progress-sec") progSec = stod(nx());
    else if (a == "--checkpoint") ckptPath = nx();
    else if (a == "--checkpoint-sec") ckptSec = stod(nx());
    else if (a == "--resume") resumePath = nx();
    else { fprintf(stderr, "unknown option %s\n", a.c_str()); return 2; }
  }
  if (n < 2 || n > 8) { fprintf(stderr, "board must be 2..8\n"); return 2; }
  N = n * n; FULL = N == 64 ? ~0ULL : ((1ULL << N) - 1);
  vector<pair<int,int>> shape;
  { size_t p = 0; string s = shapeStr;
    while (p < s.size()) { size_t q = s.find(';', p); if (q == string::npos) q = s.size();
      string t = s.substr(p, q - p); size_t c = t.find(',');
      shape.push_back({stoi(t.substr(0, c)), stoi(t.substr(c + 1))}); p = q + 1; } }
  buildPlacements(shape);
  initSym();
  // the placement family must be invariant under the 8 maps (canonical TT keys rely on it)
  { unordered_set<u64> S(PL.begin(), PL.end());
    for (int s = 0; s < 8; s++) for (u64 p : PL) if (!S.count(applySym(s, p))) { fprintf(stderr, "placements not symmetric s=%d p=%llx img=%llx n=%zu\n", s, (unsigned long long)p, (unsigned long long)applySym(s, p), PL.size()); return 2; } }
  u64 entries = (1ULL << ttLog) * BUCKET;
  long ttMb = (long)(entries * sizeof(Ent) >> 20);
  if (ttMb + 150 > maxRssMb) { printf("ABORT config tt %ld MB + 150 > --max-rss-mb %ld\n", ttMb, maxRssMb); return 1; }
  tt = (Ent *)calloc(entries, sizeof(Ent));
  if (!tt) { printf("ABORT alloc\n"); return 1; }
  ttMask = (1ULL << ttLog) - 1;
  if (!resPath.empty()) resF = fopen(resPath.c_str(), "a");
  printf("board=%dx%d shape=%s placements=%zu K=%d tt=%ld MB pairing=%d\n", n, n, shapeStr.c_str(), PL.size(), K, ttMb, (int)usePairing);
  fflush(stdout);
  T0 = chrono::steady_clock::now();
  if (!resumePath.empty()) {
    long got = loadTT(resumePath);
    printf("resume %s: %ld entries\n", resumePath.c_str(), got); fflush(stdout);
    if (got == -2) { printf("ABORT resume file does not match this run\n"); return 1; }
  }
  u32 pn = 1, dn = 1, w = 0;
  progSecG = progSec;
  mid(0, 0, INF, INF, pn, dn, w);
  double searchT = elapsed();
  const char *verdict = pn == 0 ? "x_wins" : (dn == 0 ? "x_cannot_win" : "unknown");
  if (aborted) {
    if (!ckptPath.empty()) { bool ok = saveTT(ckptPath); printf("checkpoint %s %s\n", ckptPath.c_str(), ok ? "ok" : "FAILED"); }
    rec("{\"tag\":\"%s\",\"type\":\"abort\",\"reason\":\"%s\",\"board\":%d,\"shape\":\"%s\",\"K\":%d,\"t\":%.1f,\"nodes\":%llu,\"root_pn\":%u,\"root_dn\":%u,\"rss_mb\":%ld,\"pair_leaves\":%llu}\n",
        tag.c_str(), abortReason.c_str(), n, shapeStr.c_str(), K, searchT, (unsigned long long)nodes, pn, dn, rssMb(), (unsigned long long)statPair);
    printf("ABORT %s K=%d t=%.1fs nodes=%llu root pn=%u dn=%u rss=%ldMB\n", abortReason.c_str(), K, searchT, (unsigned long long)nodes, pn, dn, rssMb());
    return 1;
  }
  printf("search %s K=%d t=%.1fs nodes=%llu pair_leaves=%llu tt_overwrites=%llu rss=%ldMB\n", verdict, K, searchT, (unsigned long long)nodes,
         (unsigned long long)statPair, (unsigned long long)ttOver, rssMb());
  fflush(stdout);
  rec("{\"tag\":\"%s\",\"type\":\"result\",\"result\":\"%s\",\"board\":%d,\"shape\":\"%s\",\"K\":%d,\"t\":%.1f,\"nodes\":%llu,\"pair_leaves\":%llu,\"rss_mb\":%ld,\"tt_log2\":%d,\"pairing\":%d}\n",
      tag.c_str(), verdict, n, shapeStr.c_str(), K, searchT, (unsigned long long)nodes, (unsigned long long)statPair, rssMb(), ttLog, (int)usePairing);
  if (!certPath.empty()) {
    certF = fopen(certPath.c_str(), "w");
    if (!certF) { printf("ABORT cannot open cert\n"); return 1; }
    fprintf(certF, "# strong6 solver certificate\nboard %d %d\nshape", n, n);
    for (auto [x, y] : shape) fprintf(certF, " %d,%d", x, y);
    fprintf(certF, "\nkind %s\nbudget %d\nkeys canonical\n", pn == 0 ? "xwin" : "ostrategy", K);
    if (pn == 0) expXwinX(0, 0); else expOX(0, 0);
    if (!exportFail && !aborted) fprintf(certF, "end\n");
    fclose(certF);
    double et = elapsed() - searchT;
    if (exportFail || aborted) {
      remove(certPath.c_str());
      const char *why = aborted ? abortReason.c_str() : exportMsg.c_str();
      rec("{\"tag\":\"%s\",\"type\":\"abort_export\",\"reason\":\"%s\",\"K\":%d,\"lines\":%llu,\"t_export\":%.1f,\"rss_mb\":%ld}\n", tag.c_str(), why, K, (unsigned long long)certLines, et, rssMb());
      printf("ABORT export_%s lines=%llu t=%.1fs rss=%ldMB (partial certificate deleted)\n", why, (unsigned long long)certLines, et, rssMb());
      return 1;
    }
    u64 nl = seenX.size() + seenO.size();
    rec("{\"tag\":\"%s\",\"type\":\"cert\",\"kind\":\"%s\",\"K\":%d,\"positions\":%llu,\"x_positions\":%llu,\"o_positions\":%llu,\"pair_leaves\":%llu,\"t_export\":%.1f,\"rss_mb\":%ld,\"file\":\"%s\"}\n",
        tag.c_str(), pn == 0 ? "xwin" : "ostrategy", K, (unsigned long long)nl, (unsigned long long)seenX.size(), (unsigned long long)seenO.size(),
        (unsigned long long)certPairs, et, rssMb(), certPath.c_str());
    printf("certificate %s kind=%s x_positions=%zu o_positions=%zu pair_leaves=%llu t=%.1fs rss=%ldMB\n", certPath.c_str(), pn == 0 ? "xwin" : "ostrategy",
           seenX.size(), seenO.size(), (unsigned long long)certPairs, et, rssMb());
  }
  printf("DONE %s board=%d shape=%s K=%d\n", verdict, n, shapeStr.c_str(), K);
  return 0;
}
