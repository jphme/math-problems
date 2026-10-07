// Maker-Breaker (weak) and maker-maker (strong) polyomino achievement game solver
// on bounded rectangular boards. See README.md for the rules, the soundness of
// every pruning rule, and the certificate format.
//
// Build: clang++ -O2 -std=c++17 -o solver solver.cpp
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <set>
#include <string>
#include <vector>
#include <sys/resource.h>

using namespace std;
typedef uint64_t u64;

static const int NW = 6;  // up to 384 cells
struct Bits {
  u64 w[NW];
  void clear() { memset(w, 0, sizeof w); }
  void set(int i) { w[i >> 6] |= 1ULL << (i & 63); }
  bool get(int i) const { return (w[i >> 6] >> (i & 63)) & 1; }
  void orr(const Bits& o) { for (int k = 0; k < NW; k++) w[k] |= o.w[k]; }
  bool operator<(const Bits& o) const { return memcmp(w, o.w, sizeof w) < 0; }
};

// ---------------- configuration -------------------------------------------
static int W = 0, H = 0, N = 0, S = 0;     // board, cells, shape size
static vector<vector<int>> PL;               // placements: cells
static vector<vector<int>> CPL;              // cell -> placements
static vector<vector<int>> SYM;              // symmetry maps (cell -> cell)
static vector<vector<int>> ISYM;
static int NS = 1;
static const int INF = 1000;                 // "unlimited" Maker move budget

// ---------------- state ----------------------------------------------------
static vector<int> owner;                    // 0 free, 1 maker, 2 breaker
static vector<int> mk, br;                   // per placement counts
static vector<vector<int>> bucket;           // live placements by free count
static vector<int> bpos;                     // index in bucket
static int nfree;
static u64 Z[400][3];
static u64 hs[8];
static Bits Mset, Bset;

static inline int freeOf(int p) { return S - mk[p] - br[p]; }
static inline void bucketAdd(int p) { int f = freeOf(p); bpos[p] = bucket[f].size(); bucket[f].push_back(p); }
static inline void bucketDel(int p) {
  int f = freeOf(p); auto& b = bucket[f]; int i = bpos[p]; int q = b.back(); b[i] = q; bpos[q] = i; b.pop_back();
}
static void playM(int c) {
  owner[c] = 1; nfree--; Mset.set(c);
  for (int s = 0; s < NS; s++) hs[s] ^= Z[SYM[s][c]][1];
  for (int p : CPL[c]) { if (br[p] == 0) { bucketDel(p); mk[p]++; bucketAdd(p); } else mk[p]++; }
}
static void undoM(int c) {
  owner[c] = 0; nfree++; Mset.w[c >> 6] &= ~(1ULL << (c & 63));
  for (int s = 0; s < NS; s++) hs[s] ^= Z[SYM[s][c]][1];
  for (int p : CPL[c]) { if (br[p] == 0) { bucketDel(p); mk[p]--; bucketAdd(p); } else mk[p]--; }
}
static void playB(int c) {
  owner[c] = 2; nfree--; Bset.set(c);
  for (int s = 0; s < NS; s++) hs[s] ^= Z[SYM[s][c]][2];
  for (int p : CPL[c]) { if (br[p] == 0) bucketDel(p); br[p]++; }
}
static void undoB(int c) {
  owner[c] = 0; nfree++; Bset.w[c >> 6] &= ~(1ULL << (c & 63));
  for (int s = 0; s < NS; s++) hs[s] ^= Z[SYM[s][c]][2];
  for (int p : CPL[c]) { br[p]--; if (br[p] == 0) bucketAdd(p); }
}

// ---------------- transposition table -------------------------------------
struct TTE {
  u64 key;
  uint16_t dwin;   // Maker wins within dwin moves (0xFFFF unknown)
  uint16_t dlose;  // Maker cannot win within dlose moves (0 unknown)
  int16_t move;    // best Maker move (canonical frame), -1 none
  uint16_t pad;
  Bits zone;       // canonical frame, valid if dwin known
};
static vector<TTE> TT;
static u64 TTmask = 0;
static u64 nodes = 0, ttHits = 0, pairCuts = 0, ttStores = 0;

static inline int canon(u64 side, u64& key) {
  int best = 0; u64 bk = hs[0] ^ side;
  for (int s = 1; s < NS; s++) { u64 k = hs[s] ^ side; if (k < bk) { bk = k; best = s; } }
  key = bk | 1;  // never 0
  return best;
}
static TTE* ttFind(u64 key) {
  TTE* e = &TT[(key & TTmask) & ~1ULL];
  if (e[0].key == key) return &e[0];
  if (e[1].key == key) return &e[1];
  return nullptr;
}
static TTE* ttSlot(u64 key) {
  TTE* e = &TT[(key & TTmask) & ~1ULL];
  if (e[0].key == key) return &e[0];
  if (e[1].key == key) return &e[1];
  // replace slot 1, after moving slot 0 down (keep most recent in 0)
  e[1] = e[0];
  e[0].key = key; e[0].dwin = 0xFFFF; e[0].dlose = 0; e[0].move = -1; e[0].zone.clear();
  ttStores++;
  return &e[0];
}
static void toCanon(const Bits& z, int s, Bits& out) {
  out.clear();
  for (int k = 0; k < NW; k++) { u64 x = z.w[k]; while (x) { int b = __builtin_ctzll(x); x &= x - 1; out.set(SYM[s][k * 64 + b]); } }
}
static void fromCanon(const Bits& z, int s, Bits& out) {
  out.clear();
  for (int k = 0; k < NW; k++) { u64 x = z.w[k]; while (x) { int b = __builtin_ctzll(x); x &= x - 1; out.set(ISYM[s][k * 64 + b]); } }
}
static const u64 SIDE_M = 0x9E3779B97F4A7C15ULL, SIDE_B = 0xC2B2AE3D27D4EB4FULL;

// ---------------- options -------------------------------------------------
static int pairBudget = 3000;
static int pairTryLimit = 1000;
static bool usePairing = true;
static bool useNull = true;
static double timeLimit = 1e18;
static long maxRssMb = 4000;
static chrono::steady_clock::time_point T0;
static bool aborted = false;
static const char* abortReason = "";
static double elapsed() { return chrono::duration<double>(chrono::steady_clock::now() - T0).count(); }
// ru_maxrss is in bytes on macOS and in kilobytes on Linux
#ifdef __APPLE__
static long rssMb() { struct rusage r; getrusage(RUSAGE_SELF, &r); return r.ru_maxrss / (1024 * 1024); }
#else
static long rssMb() { struct rusage r; getrusage(RUSAGE_SELF, &r); return r.ru_maxrss / 1024; }
#endif
static FILE* progressFile = nullptr;
static double progressSec = 600, lastProgress = 0;
static string progressTag;
static void checkLimits() {
  if ((nodes & 0x3FF) == 0) {
    double t = elapsed();
    if (t > timeLimit) { aborted = true; abortReason = "time"; }
    if (rssMb() > maxRssMb) { aborted = true; abortReason = "rss"; }
    if (progressFile && t - lastProgress >= progressSec) {
      lastProgress = t;
      fprintf(progressFile, "{\"tag\":\"%s\",\"progress\":true,\"nodes\":%llu,\"seconds\":%.0f,\"rss_mb\":%ld}\n",
              progressTag.c_str(), (unsigned long long)nodes, t, rssMb());
      fflush(progressFile);
    }
  }
}

// ---------------- pairing (Breaker paving) ---------------------------------
// Find disjoint pairs of free cells such that every live placement with
// free count in [2, d] contains both cells of some pair.
static vector<int> partner;
static vector<int> pairList;
static int pbud;
static vector<int> Lset;
static inline bool inPl(int p, int x) { for (int c : PL[p]) if (c == x) return true; return false; }
static bool pairRec(vector<int>& unc) {
  if (unc.empty()) return true;
  if (--pbud < 0) return false;
  int bestp = -1, bestk = 1 << 30;
  for (int p : unc) {
    int k = 0;
    for (int c : PL[p]) if (owner[c] == 0 && partner[c] < 0) k++;
    if (k < bestk) { bestk = k; bestp = p; if (k < 2) break; }
  }
  if (bestk < 2) return false;
  int fc[8], k = 0;
  for (int c : PL[bestp]) if (owner[c] == 0 && partner[c] < 0) fc[k++] = c;
  vector<int> nu; nu.reserve(unc.size());
  for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) {
    int u = fc[i], v = fc[j];
    partner[u] = v; partner[v] = u; pairList.push_back(u); pairList.push_back(v);
    nu.clear();
    for (int p : unc) if (!(inPl(p, u) && inPl(p, v))) nu.push_back(p);
    if (pairRec(nu)) return true;
    partner[u] = -1; partner[v] = -1; pairList.pop_back(); pairList.pop_back();
    if (pbud < 0) return false;
  }
  return false;
}
static bool findPairing(int d, vector<int>* out) {
  if (!bucket[1].empty()) return false;
  Lset.clear();
  int dm = min(d, S);
  for (int f = 2; f <= dm; f++) for (int p : bucket[f]) Lset.push_back(p);
  pairList.clear();
  for (int c = 0; c < N; c++) partner[c] = -1;
  pbud = pairBudget;
  bool ok = pairRec(Lset);
  if (ok && out) *out = pairList;
  for (int c : pairList) partner[c] = -1;
  return ok;
}

// ---------------- move generation -----------------------------------------
static const int WGT[9] = {1, 4, 20, 100, 500, 2500, 12500, 62500, 312500};
static vector<int> scoreBuf;
static void relevantCells(int d, vector<pair<int,int>>& out) {
  // cells in live placements with free count <= d, scored
  out.clear();
  int dm = min(d, S);
  for (int f = 1; f <= dm; f++) for (int p : bucket[f]) {
    int w = WGT[mk[p]];
    for (int c : PL[p]) if (owner[c] == 0) scoreBuf[c] += w;
  }
  for (int f = 1; f <= dm; f++) for (int p : bucket[f])
    for (int c : PL[p]) if (owner[c] == 0 && scoreBuf[c] > 0) { out.push_back({-scoreBuf[c], c}); scoreBuf[c] = 0; }
  sort(out.begin(), out.end());
}

// ---------------- pairing strategies at Maker nodes (rule M-pair) ------------
// At Maker-to-move position P: if Breaker cell c (relevant for budget d-1) and a
// pairing Q exist such that Q is a pairing of P+c (Breaker owns c, Maker to move,
// budget d), then every Maker move m outside cells(Q) and != c is answered by c
// and Breaker wins by Q. Returns the set of Maker moves handled this way.
static int pairStratK = 0;
static inline int dm1(int d) { return d >= INF ? INF : d - 1; }
struct PStrat { int c; vector<int> pairs; };
static void pairStrategies(int d, Bits& covered, vector<PStrat>* out) {
  covered.clear();
  if (pairStratK <= 0 || d < 3) return;
  vector<pair<int,int>> mv; relevantCells(dm1(d), mv);
  int lim = min((int)mv.size(), pairStratK);
  vector<int> prs;
  for (int i = 0; i < lim; i++) {
    int c = mv[i].second;
    playB(c); bool ok = findPairing(d, &prs); undoB(c);
    if (!ok) continue;
    Bits used; used.clear(); used.set(c); for (int x : prs) used.set(x);
    bool gain = false;
    for (int x = 0; x < N; x++) if (owner[x] == 0 && !used.get(x) && !covered.get(x)) { covered.set(x); gain = true; }
    if (gain && out) out->push_back({c, prs});
  }
}

// ---------------- weak game search -----------------------------------------
static bool breakerNode(int d, Bits* zone);


static bool makerWin(int d, Bits* zone) {
  nodes++; checkLimits(); if (aborted) return false;
  if (!bucket[1].empty() && d >= 1) {
    if (zone) { zone->clear(); for (int c : PL[bucket[1][0]]) zone->set(c); }
    return true;
  }
  if (d <= 1 || nfree == 0) return false;
  bool any = false; for (int f = 2; f <= min(d, S); f++) if (!bucket[f].empty()) { any = true; break; }
  if (!any) return false;
  u64 key; int s = canon(SIDE_M, key);
  TTE* e = ttFind(key);
  if (e) {
    ttHits++;
    if (e->dwin <= d) { if (zone) fromCanon(e->zone, s, *zone); return true; }
    if (e->dlose >= d) return false;
  }
  if (usePairing && d >= 3 && findPairing(d, nullptr)) {
    pairCuts++;
    TTE* f = ttSlot(key); if (f->dlose < d) f->dlose = min(d, 0xFFFF);
    return false;
  }
  vector<pair<int,int>> mv; relevantCells(d, mv);
  if (pairStratK > 0) {
    Bits cov; pairStrategies(d, cov, nullptr);
    size_t j = 0; for (size_t i = 0; i < mv.size(); i++) if (!cov.get(mv[i].second)) mv[j++] = mv[i];
    if (j < mv.size()) pairCuts++;
    mv.resize(j);
  }
  // try TT best move first
  if (e && e->move >= 0) {
    int c = ISYM[s][e->move];
    for (size_t i = 0; i < mv.size(); i++) if (mv[i].second == c) { swap(mv[0], mv[i]); break; }
  }
  Bits z;
  for (auto& pr : mv) {
    int c = pr.second;
    playM(c);
    bool r = breakerNode(dm1(d), &z);
    undoM(c);
    if (aborted) return false;
    if (r) {
      z.set(c);
      TTE* f = ttSlot(key);
      if (d < f->dwin) { f->dwin = d; f->move = SYM[s][c]; toCanon(z, s, f->zone); }
      if (zone) *zone = z;
      return true;
    }
  }
  TTE* f = ttSlot(key); if (f->dlose < d) f->dlose = min(d, 0xFFFF);
  return false;
}

static bool breakerNode(int d, Bits* zone) {
  nodes++; checkLimits(); if (aborted) return false;
  if (d <= 0 || nfree == 0) return false;
  // double threat
  if (bucket[1].size() >= 2) {
    int p1 = bucket[1][0], t1 = -1;
    for (int c : PL[p1]) if (owner[c] == 0) t1 = c;
    for (size_t i = 1; i < bucket[1].size(); i++) {
      int p2 = bucket[1][i], t2 = -1;
      for (int c : PL[p2]) if (owner[c] == 0) t2 = c;
      if (t2 != t1) {
        if (zone) { zone->clear(); for (int c : PL[p1]) zone->set(c); for (int c : PL[p2]) zone->set(c); }
        return true;
      }
    }
  }
  u64 key; int s = canon(SIDE_B, key);
  TTE* e = ttFind(key);
  if (e) {
    ttHits++;
    if (e->dwin <= d) { if (zone) fromCanon(e->zone, s, *zone); return true; }
    if (e->dlose >= d) return false;
  }
  Bits z0, z;
  vector<int> cand;
  // Breaker move followed by a pairing (rule B-pair): Breaker plays c, then the
  // position with Maker to move admits a pairing => Maker cannot win within d.
  if (usePairing && d >= 3 && bucket[1].empty()) {
    vector<pair<int,int>> mv; relevantCells(d, mv);
    int lim = min((int)mv.size(), pairTryLimit);
    for (int i = 0; i < lim; i++) {
      int c = mv[i].second;
      playB(c); bool ok = findPairing(d, nullptr); undoB(c);
      if (ok) { pairCuts++; TTE* f = ttSlot(key); if (f->dlose < d) { f->dlose = min(d, 0xFFFF); f->move = SYM[s][c]; } return false; }
    }
  }
  if (useNull) {
    if (!makerWin(d, &z0)) {
      if (aborted) return false;
      TTE* f = ttSlot(key); if (f->dlose < d) f->dlose = min(d, 0xFFFF);
      return false;
    }
    vector<pair<int,int>> mv; relevantCells(d, mv);
    for (auto& pr : mv) if (z0.get(pr.second)) cand.push_back(pr.second);
  } else {
    z0.clear();
    vector<pair<int,int>> mv; relevantCells(d, mv);
    for (auto& pr : mv) cand.push_back(pr.second);
    if (cand.empty()) { TTE* f = ttSlot(key); if (f->dlose < d) f->dlose = min(d, 0xFFFF); return false; }
  }
  Bits acc = z0;
  for (int c : cand) {
    playB(c);
    bool r = makerWin(d, &z);
    undoB(c);
    if (aborted) return false;
    if (!r) { TTE* f = ttSlot(key); if (f->dlose < d) { f->dlose = min(d, 0xFFFF); f->move = SYM[s][c]; } return false; }
    acc.orr(z);
  }
  TTE* f = ttSlot(key);
  if (d < f->dwin) { f->dwin = d; toCanon(acc, s, f->zone); }
  if (zone) *zone = acc;
  return true;
}

// ---------------- certificate export ---------------------------------------
// Maker-win certificate (weak game). Lines:
//   M id cell child|WIN            Maker to move claims cell
//   B id default|- cell:child ...  Breaker to move; explicit replies, default = pass child (Maker node)
// Breaker-win certificate. Lines:
//   m id pass|- cell:child ...     Maker to move: child for every relevant free cell; pass child (Breaker node) for irrelevant cells
//   b id cell child                Breaker to move claims cell
//   P id c1 c2 c3 c4 ...           Maker to move: pairing leaf
//   Z id                           Breaker to move with Maker budget 0
//   D id                           Breaker to move, no live placement completable within budget
static FILE* cf = nullptr;
static int nextId = 0;
struct PosKey { Bits m, b; int d; int side;
  bool operator<(const PosKey& o) const {
    if (side != o.side) return side < o.side; if (d != o.d) return d < o.d;
    int c = memcmp(m.w, o.m.w, sizeof m.w); if (c) return c < 0; return memcmp(b.w, o.b.w, sizeof b.w) < 0; } };
static map<PosKey, pair<int, Bits>> memo;  // id, env
static bool exportFail = false;
// The time, RSS and certificate-size caps also apply during export. Every export
// function calls expAbort() on entry and checks `aborted` after each search call;
// once set, the export unwinds without writing further lines and main() deletes the
// partial certificate and prints ABORT.
static long maxCertMb = 20000;
static u64 expNodes = 0;
static bool expAbort() {
  if (aborted) return true;
  if ((++expNodes & 0xFF) == 0) {
    if (elapsed() > timeLimit) { aborted = true; abortReason = "time"; }
    else if (rssMb() > maxRssMb) { aborted = true; abortReason = "rss"; }
    else if (cf && ftell(cf) / 1048576 > maxCertMb) { aborted = true; abortReason = "cert_size"; }
  }
  return aborted;
}

static int expBreakerM(int d, Bits* env);
static int expMakerM(int d, Bits* env) {
  PosKey k{Mset, Bset, d, 0};
  auto it = memo.find(k); if (it != memo.end()) { *env = it->second.second; return it->second.first; }
  if (expAbort()) { env->clear(); return -1; }
  int id = nextId++;
  Bits e; e.clear();
  if (!bucket[1].empty()) {
    int p = bucket[1][0], t = -1;
    for (int c : PL[p]) { if (owner[c] == 0) t = c; e.set(c); }
    fprintf(cf, "M %d %d WIN\n", id, t);
    memo[k] = {id, e}; *env = e; return id;
  }
  vector<pair<int,int>> mv; relevantCells(d, mv);
  u64 key; int s = canon(SIDE_M, key);
  TTE* te = ttFind(key);
  if (te && te->move >= 0) {
    int c = ISYM[s][te->move];
    for (size_t i = 0; i < mv.size(); i++) if (mv[i].second == c) { swap(mv[0], mv[i]); break; }
  }
  for (auto& pr : mv) {
    int c = pr.second;
    playM(c);
    bool r = breakerNode(dm1(d), nullptr);
    if (aborted) { undoM(c); env->clear(); return -1; }
    if (r) {
      Bits ce; int ch = expBreakerM(dm1(d), &ce);
      undoM(c);
      if (aborted || exportFail) { env->clear(); return -1; }
      fprintf(cf, "M %d %d %d\n", id, c, ch);
      e = ce; e.set(c);
      memo[k] = {id, e}; *env = e; return id;
    }
    undoM(c);
  }
  fprintf(stderr, "export: no winning Maker move found\n"); exportFail = true;
  env->clear(); return -1;
}
static int expBreakerM(int d, Bits* env) {
  PosKey k{Mset, Bset, d, 1};
  auto it = memo.find(k); if (it != memo.end()) { *env = it->second.second; return it->second.first; }
  if (expAbort()) { env->clear(); return -1; }
  int id = nextId++;
  Bits e0; int def = expMakerM(d, &e0);    // pass child
  if (aborted || exportFail) { env->clear(); return -1; }
  Bits acc = e0;
  string line = "B " + to_string(id) + " " + to_string(def);
  for (int c = 0; c < N; c++) if (owner[c] == 0 && e0.get(c)) {
    playB(c);
    bool mw = makerWin(d, nullptr);
    if (aborted) { undoB(c); env->clear(); return -1; }
    if (!mw) { fprintf(stderr, "export: reply %d inside env refutes\n", c); exportFail = true; undoB(c); env->clear(); return -1; }
    Bits ce; int ch = expMakerM(d, &ce);
    undoB(c);
    if (aborted || exportFail) { env->clear(); return -1; }
    acc.orr(ce);
    line += " " + to_string(c) + ":" + to_string(ch);
  }
  fprintf(cf, "%s\n", line.c_str());
  memo[k] = {id, acc}; *env = acc; return id;
}

static int expBreakerB(int d);
static int expMakerB(int d) {  // Maker to move, Maker cannot win within d
  PosKey k{Mset, Bset, d, 2};
  auto it = memo.find(k); if (it != memo.end()) return it->second.first;
  if (expAbort()) return -1;
  int id = nextId++; Bits dummy; dummy.clear(); memo[k] = {id, dummy};
  vector<int> prs;
  if (findPairing(d, &prs)) {
    string line = "P " + to_string(id);
    for (int c : prs) line += " " + to_string(c);
    fprintf(cf, "%s\n", line.c_str()); return id;
  }
  vector<pair<int,int>> mv; relevantCells(d, mv);
  Bits rel; rel.clear(); for (auto& pr : mv) rel.set(pr.second);
  bool irrelevant = false; for (int c = 0; c < N; c++) if (owner[c] == 0 && !rel.get(c)) irrelevant = true;
  string line = "m " + to_string(id) + " ";
  if (irrelevant) { int ch = expBreakerB(dm1(d)); if (aborted || exportFail) return -1; line += to_string(ch); } else line += "-";
  Bits cov; vector<PStrat> strat; pairStrategies(d, cov, &strat);
  vector<int> stratNode(strat.size(), -1);
  for (auto& pr : mv) {
    int c = pr.second;
    int sj = -1;
    if (cov.get(c)) for (size_t j = 0; j < strat.size() && sj < 0; j++) {
      bool inQ = (strat[j].c == c); for (int x : strat[j].pairs) if (x == c) inQ = true;
      if (!inQ) sj = j;
    }
    if (sj >= 0) {
      if (stratNode[sj] < 0) {
        int bid = nextId++, pid = nextId++;
        string pl = "P " + to_string(pid); for (int x : strat[sj].pairs) pl += " " + to_string(x);
        fprintf(cf, "%s\nb %d %d %d\n", pl.c_str(), bid, strat[sj].c, pid);
        stratNode[sj] = bid;
      }
      line += " " + to_string(c) + ":" + to_string(stratNode[sj]);
      continue;
    }
    playM(c);
    int ch = expBreakerB(dm1(d));
    undoM(c);
    if (aborted || exportFail) return -1;
    line += " " + to_string(c) + ":" + to_string(ch);
  }
  fprintf(cf, "%s\n", line.c_str()); return id;
}
static int expBreakerB(int d) {  // Breaker to move, Maker cannot win within d
  PosKey k{Mset, Bset, d, 3};
  auto it = memo.find(k); if (it != memo.end()) return it->second.first;
  if (expAbort()) return -1;
  int id = nextId++; Bits dummy; dummy.clear(); memo[k] = {id, dummy};
  if (d <= 0) { fprintf(cf, "Z %d\n", id); return id; }
  if (nfree == 0) { fprintf(cf, "E %d\n", id); return id; }
  vector<pair<int,int>> mv; relevantCells(d, mv);
  if (mv.empty()) { fprintf(cf, "D %d\n", id); return id; }
  vector<int> cand;
  // forced block first
  if (!bucket[1].empty()) { for (int c : PL[bucket[1][0]]) if (owner[c] == 0) cand.push_back(c); }
  else {
    // a Breaker move followed by a pairing gives a leaf directly
    vector<int> prs;
    for (auto& pr : mv) {
      int c = pr.second;
      playB(c); bool ok = findPairing(d, &prs); undoB(c);
      if (aborted) return -1;
      if (ok) {
        int pid = nextId++;
        string pl = "P " + to_string(pid); for (int x : prs) pl += " " + to_string(x);
        fprintf(cf, "%s\nb %d %d %d\n", pl.c_str(), id, c, pid);
        return id;
      }
    }
  }
  {
    u64 key; int s = canon(SIDE_B, key); TTE* te = ttFind(key);
    if (te && te->move >= 0) cand.push_back(ISYM[s][te->move]);
  }
  for (auto& pr : mv) cand.push_back(pr.second);
  for (int c : cand) {
    playB(c);
    bool r = makerWin(d, nullptr);
    if (aborted) { undoB(c); return -1; }
    if (!r) {
      int ch = expMakerB(d);
      undoB(c);
      if (aborted || exportFail) return -1;
      fprintf(cf, "b %d %d %d\n", id, c, ch);
      return id;
    }
    undoB(c);
  }
  fprintf(stderr, "export: no Breaker move found\n"); exportFail = true; return -1;
}

// ---------------- strong game (maker-maker), small boards only ------------
// First player X wins iff X completes a copy before O does, X making at most d moves.
// State per placement: cx[p], co[p]. Exhaustive alpha-beta (boolean) with TT, no zone pruning.
static vector<int> cx, co;
static u64 snodes = 0;
static bool xComplete1() { // does X have a placement with S-1 X cells and the last free?
  return false;
}
static int sOwner(int c) { return owner[c]; }
static bool strongX(int d);
static bool strongO(int d);
static void sPlay(int c, int who) {
  owner[c] = who; nfree--;
  for (int s = 0; s < NS; s++) hs[s] ^= Z[SYM[s][c]][who];
  for (int p : CPL[c]) { if (who == 1) cx[p]++; else co[p]++; }
}
static void sUndo(int c, int who) {
  owner[c] = 0; nfree++;
  for (int s = 0; s < NS; s++) hs[s] ^= Z[SYM[s][c]][who];
  for (int p : CPL[c]) { if (who == 1) cx[p]--; else co[p]--; }
}
// cell scores and threat detection, computed by scanning placements (small boards)
static bool strongX(int d) {  // X to move, X has d moves left; returns X wins
  snodes++; nodes++; checkLimits(); if (aborted) return false;
  if (d <= 0 || nfree == 0) return false;
  int P = PL.size();
  vector<int> scx(N, 0), sco(N, 0);
  int othreat = -1, nOthreatCells = 0;
  for (int p = 0; p < P; p++) {
    if (co[p] == 0 && cx[p] == S - 1) return true;  // X completes now
  }
  for (int p = 0; p < P; p++) {
    if (cx[p] == 0 && co[p] == S - 1) {
      for (int c : PL[p]) if (owner[c] == 0) { if (othreat != c) { nOthreatCells += (othreat < 0 ? 1 : (othreat != c)); othreat = (othreat < 0 ? c : othreat); } }
    }
    if (co[p] == 0 && S - cx[p] <= d) for (int c : PL[p]) if (owner[c] == 0) scx[c] += WGT[cx[p]];
    if (cx[p] == 0 && S - co[p] <= d) for (int c : PL[p]) if (owner[c] == 0) sco[c] += WGT[co[p]];
  }
  if (d == 1) return false;
  u64 key; canon(SIDE_M ^ 0x5555, key);
  TTE* e = ttFind(key);
  if (e) { ttHits++; if (e->dwin <= d) return true; if (e->dlose >= d) return false; }
  vector<pair<int,int>> mv;
  if (othreat >= 0) {
    // X must block O's immediate threat (X cannot complete now). If O threatens 2 distinct cells, X loses.
    int cnt = 0; set<int> tc;
    for (int p = 0; p < P; p++) if (cx[p] == 0 && co[p] == S - 1) for (int c : PL[p]) if (owner[c] == 0) tc.insert(c);
    if (tc.size() >= 2) return false;
    mv.push_back({0, *tc.begin()}); (void)cnt;
  } else {
    for (int c = 0; c < N; c++) if (owner[c] == 0 && (scx[c] > 0 || sco[c] > 0)) mv.push_back({-(2 * scx[c] + sco[c]), c});
    sort(mv.begin(), mv.end());
  }
  bool win = false;
  for (auto& pr : mv) {
    int c = pr.second; sPlay(c, 1);
    bool r = strongO(d - 1);
    sUndo(c, 1);
    if (aborted) return false;
    if (r) { win = true; break; }
  }
  TTE* f = ttSlot(key);
  if (win) { if (d < f->dwin) f->dwin = d; } else if (f->dlose < d) f->dlose = d;
  return win;
}
static bool strongO(int d) {  // O to move; X has d moves left. returns X wins
  snodes++; nodes++; checkLimits(); if (aborted) return false;
  if (nfree == 0) return false;
  int P = PL.size();
  // O completes now?
  for (int p = 0; p < P; p++) if (cx[p] == 0 && co[p] == S - 1) return false;
  if (d <= 0) return false;
  set<int> xt;
  for (int p = 0; p < P; p++) if (co[p] == 0 && cx[p] == S - 1) for (int c : PL[p]) if (owner[c] == 0) xt.insert(c);
  if (xt.size() >= 2) return true;
  u64 key; canon(SIDE_B ^ 0x5555, key);
  TTE* e = ttFind(key);
  if (e) { ttHits++; if (e->dwin <= d) return true; if (e->dlose >= d) return false; }
  vector<pair<int,int>> mv;
  if (xt.size() == 1) mv.push_back({0, *xt.begin()});
  else {
    vector<int> scx(N, 0), sco(N, 0);
    for (int p = 0; p < P; p++) {
      if (co[p] == 0 && S - cx[p] <= d) for (int c : PL[p]) if (owner[c] == 0) scx[c] += WGT[cx[p]];
      if (cx[p] == 0 && S - co[p] <= d) for (int c : PL[p]) if (owner[c] == 0) sco[c] += WGT[co[p]];
    }
    for (int c = 0; c < N; c++) if (owner[c] == 0 && (scx[c] > 0 || sco[c] > 0)) mv.push_back({-(2 * scx[c] + sco[c]), c});
    sort(mv.begin(), mv.end());
    if (mv.empty()) return false;  // nothing X can still complete within d
  }
  bool xwins = true;
  for (auto& pr : mv) {
    int c = pr.second; sPlay(c, 2);
    bool r = strongX(d);
    sUndo(c, 2);
    if (aborted) return false;
    if (!r) { xwins = false; break; }
  }
  TTE* f = ttSlot(key);
  if (xwins) { if (d < f->dwin) f->dwin = d; } else if (f->dlose < d) f->dlose = d;
  return xwins;
}

// strong-game strategy export: every O reply enumerated (no pruning), positions keyed exactly
static set<pair<string,string>> sMemo;
static string hexOf(int who) {
  string s; char buf[20];
  for (int k = NW - 1; k >= 0; k--) { u64 w = 0; for (int b = 0; b < 64; b++) { int c = k * 64 + b; if (c < N && owner[c] == who) w |= 1ULL << b; } snprintf(buf, sizeof buf, "%016llx", (unsigned long long)w); s += buf; }
  return s;
}
static bool sExpO(int d);
static bool sExpX(int d) {
  if (expAbort()) return false;
  string a = hexOf(1), b = hexOf(2);
  if (!sMemo.insert({a, b}).second) return true;
  int P = PL.size();
  for (int p = 0; p < P; p++) if (co[p] == 0 && cx[p] == S - 1) {
    for (int c : PL[p]) if (owner[c] == 0) { fprintf(cf, "X %s %s %d\n", a.c_str(), b.c_str(), c); return true; }
  }
  // X's candidates in the order strongX searches them (relevance score, then the other cells). The
  // first winning candidate is the strategy move. The search order puts forcing moves first, which keeps
  // the strategy (every O reply is enumerated) small; cell order picks wide winning moves, and every
  // failing candidate costs a full refutation search.
  vector<pair<int,int>> ord; {
    vector<int> scx(N, 0), sco(N, 0);
    for (int p = 0; p < P; p++) {
      if (co[p] == 0 && S - cx[p] <= d) for (int c : PL[p]) if (owner[c] == 0) scx[c] += WGT[cx[p]];
      if (cx[p] == 0 && S - co[p] <= d) for (int c : PL[p]) if (owner[c] == 0) sco[c] += WGT[co[p]];
    }
    for (int c = 0; c < N; c++) if (owner[c] == 0) ord.push_back({(scx[c] > 0 || sco[c] > 0) ? -(2 * scx[c] + sco[c]) : 1, c});
    sort(ord.begin(), ord.end());
  }
  for (auto& pr : ord) {
    int c = pr.second;
    sPlay(c, 1); bool r = strongO(d - 1);
    if (aborted) { sUndo(c, 1); return false; }
    if (r) { fprintf(cf, "X %s %s %d\n", a.c_str(), b.c_str(), c); bool ok = sExpO(d - 1); sUndo(c, 1); return ok; }
    sUndo(c, 1);
  }
  fprintf(stderr, "strong export: no X move\n"); exportFail = true; return false;
}
static bool sExpO(int d) {
  for (int c = 0; c < N; c++) if (owner[c] == 0) {
    if (expAbort()) return false;
    sPlay(c, 2);
    bool xw = strongX(d);
    if (aborted) { sUndo(c, 2); return false; }
    if (!xw) { fprintf(stderr, "strong export: O reply %d refutes\n", c); exportFail = true; sUndo(c, 2); return false; }
    bool ok = sExpX(d); sUndo(c, 2);
    if (!ok) return false;
  }
  return true;
}

// ---------------- setup ----------------------------------------------------
static vector<pair<int,int>> parseShape(const string& s) {
  vector<pair<int,int>> out; size_t i = 0;
  while (i < s.size()) {
    size_t j = s.find(';', i); if (j == string::npos) j = s.size();
    string t = s.substr(i, j - i); size_t k = t.find(',');
    out.push_back({atoi(t.substr(0, k).c_str()), atoi(t.substr(k + 1).c_str())});
    i = j + 1;
  }
  return out;
}
static vector<pair<int,int>> decodeCode(u64 code) {  // A246521 antidiagonal code
  vector<pair<int,int>> out;
  for (int d = 0; d < 11; d++) for (int y = 0; y <= d; y++) {
    int k = d * (d + 1) / 2 + y; if (k < 64 && ((code >> k) & 1)) out.push_back({d - y, y});
  }
  return out;
}
static void setup(vector<pair<int,int>> shape) {
  S = shape.size(); N = W * H;
  if (N > NW * 64 || N > 400) { fprintf(stderr, "board too large\n"); exit(2); }
  set<vector<pair<int,int>>> orients;
  for (int t = 0; t < 8; t++) {
    vector<pair<int,int>> o;
    for (auto [x, y] : shape) {
      int a = x, b = y;
      if (t & 1) a = -a; if (t & 2) b = -b; if (t & 4) swap(a, b);
      o.push_back({a, b});
    }
    int mx = 1 << 30, my = 1 << 30; for (auto& q : o) { mx = min(mx, q.first); my = min(my, q.second); }
    for (auto& q : o) { q.first -= mx; q.second -= my; }
    sort(o.begin(), o.end()); orients.insert(o);
  }
  PL.clear();
  for (auto& o : orients) {
    int ox = 0, oy = 0; for (auto& q : o) { ox = max(ox, q.first); oy = max(oy, q.second); }
    for (int x = 0; x + ox < W; x++) for (int y = 0; y + oy < H; y++) {
      vector<int> cells; for (auto& q : o) cells.push_back((y + q.second) * W + (x + q.first));
      sort(cells.begin(), cells.end()); PL.push_back(cells);
    }
  }
  CPL.assign(N, {});
  for (int p = 0; p < (int)PL.size(); p++) for (int c : PL[p]) CPL[c].push_back(p);
  // board symmetries
  SYM.clear();
  for (int t = 0; t < 8; t++) {
    if ((t & 4) && W != H) continue;
    vector<int> m(N);
    for (int y = 0; y < H; y++) for (int x = 0; x < W; x++) {
      int a = x, b = y;
      if (t & 1) a = W - 1 - a; if (t & 2) b = H - 1 - b; if (t & 4) swap(a, b);
      m[y * W + x] = b * W + a;
    }
    SYM.push_back(m);
  }
  NS = SYM.size();
  ISYM.assign(NS, vector<int>(N));
  for (int s = 0; s < NS; s++) for (int c = 0; c < N; c++) ISYM[s][SYM[s][c]] = c;
  owner.assign(N, 0); mk.assign(PL.size(), 0); br.assign(PL.size(), 0); bpos.assign(PL.size(), 0);
  cx.assign(PL.size(), 0); co.assign(PL.size(), 0);
  bucket.assign(S + 1, {});
  for (int p = 0; p < (int)PL.size(); p++) bucketAdd(p);
  nfree = N; Mset.clear(); Bset.clear();
  for (int s = 0; s < 8; s++) hs[s] = 0;
  u64 x = 0x123456789ABCDEFULL;
  for (int c = 0; c < 400; c++) for (int o = 0; o < 3; o++) {
    x ^= x << 13; x ^= x >> 7; x ^= x << 17; u64 a = x; x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    Z[c][o] = a * 0x9E3779B97F4A7C15ULL ^ x;
  }
  partner.assign(N, -1); scoreBuf.assign(N, 0);
}

static void usage() {
  fprintf(stderr,
    "usage: solver --board W[xH] (--snaky | --shape 'x,y;x,y;..' | --code N)\n"
    "  [--game weak|strong] [--dmin a] [--dmax b] (Maker move budgets to try, ascending; default 1..INF)\n"
    "  [--full] (only the unlimited game)  [--opening 'c,c,..'] (cells played alternately M,B,.. before search)\n"
    "  [--tt-mb 1024] [--max-rss-mb 4000] [--max-cert-mb 20000] [--time-limit sec] (limits cover search and certificate export) [--pair-budget 3000] [--no-pairing] [--no-null]\n"
    "  [--cert FILE] [--results FILE.jsonl] [--tag STR]\n");
  exit(2);
}

// Export failed or hit a cap: delete the partial certificate, record it, print ABORT
// (never DONE). The search verdict above is still printed and recorded per budget.
static int exportAbort(const string& certPath, FILE* rf, const string& tag, const string& game, int d) {
  remove(certPath.c_str());
  const char* why = aborted ? abortReason : "export_failed";
  printf("ABORT export_%s at d=%s cert_nodes=%d elapsed=%.1fs rss=%ldMB (partial certificate deleted)\n", why,
         d >= INF ? "INF" : to_string(d).c_str(), nextId, elapsed(), rssMb());
  if (rf) { fprintf(rf, "{\"tag\":\"%s\",\"board\":\"%dx%d\",\"S\":%d,\"game\":\"%s\",\"d\":%d,\"result\":\"abort_export_%s\",\"seconds\":%.2f,\"rss_mb\":%ld}\n",
                    tag.c_str(), W, H, S, game.c_str(), d >= INF ? -1 : d, why, elapsed(), rssMb()); fclose(rf); }
  return 1;
}

int main(int argc, char** argv) {
  T0 = chrono::steady_clock::now();
  setvbuf(stdout, nullptr, _IOLBF, 0);
  string shapeStr, game = "weak", certPath, resPath, tag, opening;
  long ttMb = 1024; int dmin = 1, dmax = INF; bool full = false;
  vector<pair<int,int>> shape;
  for (int i = 1; i < argc; i++) {
    string a = argv[i];
    auto nx = [&]() { if (i + 1 >= argc) usage(); return string(argv[++i]); };
    if (a == "--board") { string b = nx(); size_t k = b.find('x'); W = atoi(b.c_str()); H = (k == string::npos) ? W : atoi(b.c_str() + k + 1); }
    else if (a == "--snaky") shape = {{0,0},{1,0},{2,0},{3,0},{3,1},{4,1}};
    else if (a == "--shape") shape = parseShape(nx());
    else if (a == "--code") shape = decodeCode(strtoull(nx().c_str(), 0, 10));
    else if (a == "--game") game = nx();
    else if (a == "--dmin") dmin = atoi(nx().c_str());
    else if (a == "--dmax") dmax = atoi(nx().c_str());
    else if (a == "--full") full = true;
    else if (a == "--tt-mb") ttMb = atol(nx().c_str());
    else if (a == "--max-rss-mb") maxRssMb = atol(nx().c_str());
    else if (a == "--max-cert-mb") maxCertMb = atol(nx().c_str());
    else if (a == "--time-limit") timeLimit = atof(nx().c_str());
    else if (a == "--pair-budget") pairBudget = atoi(nx().c_str());
    else if (a == "--no-pairing") usePairing = false;
    else if (a == "--pair-try") pairTryLimit = atoi(nx().c_str());
    else if (a == "--pair-strat") pairStratK = atoi(nx().c_str());
    else if (a == "--no-null") useNull = false;
    else if (a == "--cert") certPath = nx();
    else if (a == "--results") resPath = nx();
    else if (a == "--tag") tag = nx();
    else if (a == "--progress-sec") progressSec = atof(nx().c_str());
    else if (a == "--opening") opening = nx();
    else usage();
  }
  if (W <= 0 || shape.empty()) usage();
  if (ttMb + 200 > maxRssMb) { fprintf(stderr, "refusing: --tt-mb %ld + 200 MB overhead exceeds --max-rss-mb %ld\n", ttMb, maxRssMb); printf("ABORT config\n"); return 3; }
  setup(shape);
  u64 ents = 2; while (ents * 2 * sizeof(TTE) <= (u64)ttMb * 1024 * 1024) ents *= 2;
  TT.assign(ents, TTE{0, 0xFFFF, 0, -1, 0, {}}); TTmask = ents - 1;
  // opening
  vector<int> open;
  if (!opening.empty()) { size_t i = 0; while (i < opening.size()) { size_t j = opening.find(',', i); if (j == string::npos) j = opening.size(); open.push_back(atoi(opening.substr(i, j - i).c_str())); i = j + 1; } }
  for (size_t i = 0; i < open.size(); i++) { if (game == "weak") { if (i % 2 == 0) playM(open[i]); else playB(open[i]); } else sPlay(open[i], i % 2 == 0 ? 1 : 2); }
  bool makerToMove = open.size() % 2 == 0;
  fprintf(stderr, "board %dx%d shape size %d placements %zu syms %d TT entries %llu (%.0f MB)\n", W, H, S, PL.size(), NS,
          (unsigned long long)ents, ents * sizeof(TTE) / 1048576.0);
  FILE* rf = resPath.empty() ? nullptr : fopen(resPath.c_str(), "a");
  progressFile = rf; progressTag = tag;
  vector<int> ds;
  if (full) ds.push_back(INF);
  else { for (int d = dmin; d <= min(dmax, (N + 1) / 2); d++) ds.push_back(d); if (dmax >= INF && (N + 1) / 2 < INF) {} }
  int answer = -1; bool lastWin = false; int lastD = 0;
  for (int d : ds) {
    u64 n0 = nodes; double t0 = elapsed();
    bool r;
    if (game == "weak") r = makerToMove ? makerWin(d, nullptr) : breakerNode(d, nullptr);
    else r = makerToMove ? strongX(d) : strongO(d);
    if (aborted) {
      printf("ABORT %s at d=%d nodes=%llu elapsed=%.1fs rss=%ldMB\n", abortReason, d, (unsigned long long)nodes, elapsed(), rssMb());
      if (rf) { fprintf(rf, "{\"tag\":\"%s\",\"board\":\"%dx%d\",\"S\":%d,\"game\":\"%s\",\"d\":%d,\"result\":\"abort_%s\",\"nodes\":%llu,\"seconds\":%.2f,\"rss_mb\":%ld}\n",
                        tag.c_str(), W, H, S, game.c_str(), d, abortReason, (unsigned long long)(nodes - n0), elapsed() - t0, rssMb()); fclose(rf); }
      return 1;
    }
    const char* res = r ? "maker_wins" : "maker_cannot_win";
    printf("d=%s %s nodes=%llu tthits=%llu paircuts=%llu time=%.2fs\n", d >= INF ? "INF" : to_string(d).c_str(), res,
           (unsigned long long)(nodes - n0), (unsigned long long)ttHits, (unsigned long long)pairCuts, elapsed() - t0);
    fflush(stdout);
    if (rf) { fprintf(rf, "{\"tag\":\"%s\",\"board\":\"%dx%d\",\"S\":%d,\"game\":\"%s\",\"opening\":\"%s\",\"d\":%d,\"result\":\"%s\",\"nodes\":%llu,\"seconds\":%.2f,\"rss_mb\":%ld}\n",
                      tag.c_str(), W, H, S, game.c_str(), opening.c_str(), d >= INF ? -1 : d, res, (unsigned long long)(nodes - n0), elapsed() - t0, rssMb()); fflush(rf); }
    lastWin = r; lastD = d;
    if (r) { answer = d; break; }
  }
  // certificate
  if (!certPath.empty() && game == "weak") {
    cf = fopen(certPath.c_str(), "w");
    fprintf(cf, "# solver certificate\nboard %d %d\nshape", W, H);
    for (auto [x, y] : shape) fprintf(cf, " %d,%d", x, y);
    fprintf(cf, "\nkind %s\nbudget %d\n", lastWin ? "makerwin" : "breakerwin", lastD >= INF ? -1 : lastD);
    fprintf(cf, "opening");
    for (int c : open) fprintf(cf, " %d", c);
    fprintf(cf, "\n");
    int root;
    Bits e;
    if (makerToMove) root = lastWin ? expMakerM(lastD, &e) : expMakerB(lastD);
    else root = lastWin ? expBreakerM(lastD, &e) : expBreakerB(lastD);
    if (aborted || exportFail) { fclose(cf); return exportAbort(certPath, rf, tag, game, lastD); }
    fprintf(cf, "root %d\nend\n", root);
    fclose(cf);
    printf("certificate %s nodes=%d ok\n", certPath.c_str(), nextId);
  }
  if (!certPath.empty() && game == "strong" && makerToMove && lastWin) {
    cf = fopen(certPath.c_str(), "w");
    fprintf(cf, "# solver strong-game strategy\nboard %d %d\nshape", W, H);
    for (auto [x, y] : shape) fprintf(cf, " %d,%d", x, y);
    fprintf(cf, "\nkind strongwin\nbudget %d\nopening", lastD);
    for (int c : open) fprintf(cf, " %d", c);
    fprintf(cf, "\n");
    bool ok = sExpX(lastD);
    if (aborted || exportFail || !ok) { exportFail = true; fclose(cf); return exportAbort(certPath, rf, tag, game, lastD); }
    fprintf(cf, "end\n"); fclose(cf);
    printf("certificate %s positions=%zu ok\n", certPath.c_str(), sMemo.size());
  }
  if (answer >= 0) printf("DONE maker_wins min_moves=%d\n", answer >= INF ? -1 : answer);
  else printf("DONE maker_cannot_win up_to_d=%s\n", lastD >= INF ? "INF" : to_string(lastD).c_str());
  printf("stats nodes=%llu elapsed=%.2fs rss=%ldMB\n", (unsigned long long)nodes, elapsed(), rssMb());
  if (rf) fclose(rf);
  return 0;
}
