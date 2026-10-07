// Independent solver for the polyomino achievement game (Harary) on an n x n board, n <= 7.
// usage: ttt <shape> <n> <weak|strong> <maxMoves> [timeoutSec] [ttBits]
// Prints, for K=1..maxMoves, whether player 1 can force a win within K of its own moves.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <algorithm>
#include <string>
#include <chrono>
using namespace std;
typedef uint64_t u64;

static int n, N;
static bool strongG;
static vector<u64> pl;            // all placements
static u64 FULL;
static double tlimit = 1e18;
static chrono::steady_clock::time_point t0;
static u64 nodes = 0;
struct Timeout {};

// ---------- symmetry tables ----------
static u64 symtab[8][7][256];
static int symcnt;
static void initSym() {
  for (int s = 0; s < 8; s++)
    for (int byte = 0; byte < 7; byte++)
      for (int v = 0; v < 256; v++) {
        u64 out = 0;
        for (int bit = 0; bit < 8; bit++) if (v >> bit & 1) {
          int c = byte * 8 + bit;
          if (c >= N) continue;
          int r = c / n, col = c % n;
          int rr = r, cc = col;
          if (s & 1) { int t = rr; rr = cc; cc = t; }
          if (s & 2) rr = n - 1 - rr;
          if (s & 4) cc = n - 1 - cc;
          out |= 1ULL << (rr * n + cc);
        }
        symtab[s][byte][v] = out;
      }
}
static inline u64 applySym(int s, u64 x) {
  u64 o = 0;
  for (int b = 0; b < 7; b++) o |= symtab[s][b][(x >> (8 * b)) & 255];
  return o;
}
static inline void canon(u64 &A, u64 &B) {
  u64 bA = A, bB = B;
  for (int s = 1; s < 8; s++) {
    u64 a = applySym(s, A), b = applySym(s, B);
    if (a < bA || (a == bA && b < bB)) { bA = a; bB = b; }
  }
  A = bA; B = bB;
}

// ---------- transposition table ----------
struct Ent { u64 a, b; int8_t w, l; };   // w = min r known win (127 none), l = max r known loss (-1 none)
static Ent *tt; static u64 ttmask;
static inline u64 hsh(u64 a, u64 b) {
  u64 h = a * 0x9E3779B97F4A7C15ULL ^ (b + 0x632BE59BD9B4E019ULL) * 0xC2B2AE3D27D4EB4FULL;
  h ^= h >> 29; h *= 0xBF58476D1CE4E5B9ULL; h ^= h >> 32;
  return h;
}
// returns 1 win, 0 loss, -1 unknown
static inline int ttGet(u64 a, u64 b, int r, Ent *&e) {
  e = &tt[hsh(a, b) & ttmask];
  if (e->a == a && e->b == b) {
    if (e->w <= r) return 1;
    if (e->l >= r) return 0;
  }
  return -1;
}
static inline void ttPut(Ent *e, u64 a, u64 b, int r, bool win) {
  if (!(e->a == a && e->b == b)) { e->a = a; e->b = b; e->w = 127; e->l = -1; }
  if (win) { if (r < e->w) e->w = r; } else { if (r > e->l) e->l = r; }
}

static bool p1(u64 A, u64 B, int r);
static bool p2(u64 A, u64 B, int r);

static inline void checkTime() {
  if ((nodes & 0xFFFF) == 0) {
    double el = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    if (el > tlimit) throw Timeout();
  }
}

// Player 1 to move, r = number of moves player 1 still may make (>=0). True iff P1 can force completion within r moves
// (and, in the strong game, without P2 having completed a copy first).
static bool p1(u64 A, u64 B, int r) {
  nodes++; checkTime();
  if (r <= 0) return false;
  // 1. can complete?
  u64 T2 = 0; // P2 threat cells (strong)
  u64 avail = FULL & ~A & ~B;
  if (avail == 0) return false;
  u64 minMiss1 = 0; // unused
  (void)minMiss1;
  int np = pl.size();
  bool any1 = false;
  for (int i = 0; i < np; i++) {
    u64 p = pl[i];
    if (p & B) continue;
    u64 m = p & ~A;
    if (m & (m - 1)) { any1 = true; continue; }
    return true; // exactly one missing (m != 0 as p never fully in A without earlier win)
  }
  if (r == 1) return false;
  if (strongG) {
    for (int i = 0; i < np; i++) {
      u64 p = pl[i];
      if (p & A) continue;
      u64 m = p & ~B;
      if (!(m & (m - 1))) T2 |= m;
    }
    if (T2 & (T2 - 1)) return false;  // two distinct P2 threats, P1 cannot complete and can block only one
    if (T2) return p2(A | T2, B, r - 1);
  }
  (void)any1;
  // 2. TT
  u64 cA = A, cB = B; canon(cA, cB);
  Ent *e; int t = ttGet(cA, cB, r, e);
  if (t >= 0) return t;
  // 3. candidate cells and scores
  int score[49]; memset(score, 0, sizeof(int) * N);
  u64 cand = 0;
  static const int W[8] = {1, 4, 16, 64, 256, 1024, 4096, 16384};
  for (int i = 0; i < np; i++) {
    u64 p = pl[i];
    if (!(p & B)) {
      int miss = __builtin_popcountll(p & ~A);
      if (miss <= r) {
        u64 m = p & ~A; cand |= m;
        int w = W[__builtin_popcountll(p & A)];
        for (u64 x = m; x; x &= x - 1) score[__builtin_ctzll(x)] += w;
      }
    }
    if (strongG && !(p & A)) {
      int miss = __builtin_popcountll(p & ~B);
      if (miss <= r - 1) {   // P2 has r-1 moves before P1's last move
        u64 m = p & ~B; cand |= m;
        int w = W[__builtin_popcountll(p & B)];
        for (u64 x = m; x; x &= x - 1) score[__builtin_ctzll(x)] += w;
      }
    }
  }
  int cells[49], nc = 0;
  for (u64 x = cand; x; x &= x - 1) cells[nc++] = __builtin_ctzll(x);
  sort(cells, cells + nc, [&](int a, int b) { return score[a] > score[b]; });
  bool res = false;
  for (int k = 0; k < nc; k++) {
    if (p2(A | (1ULL << cells[k]), B, r - 1)) { res = true; break; }
  }
  ttPut(e, cA, cB, r, res);
  return res;
}

// Player 2 to move; P1 still has r moves left (r>=0). True iff P1 still forces a win.
static bool p2(u64 A, u64 B, int r) {
  nodes++; checkTime();
  if (r <= 0) return false;
  int np = pl.size();
  u64 T1 = 0;
  for (int i = 0; i < np; i++) {
    u64 p = pl[i];
    if (strongG && !(p & A)) {
      u64 m = p & ~B;
      if (!(m & (m - 1))) return false;  // P2 completes (m != 0 since P2 has never completed before)
    }
    if (!(p & B)) {
      u64 m = p & ~A;
      if (!(m & (m - 1))) T1 |= m;
    }
  }
  if (T1 & (T1 - 1)) return true;  // two distinct P1 threats, P2 cannot complete, blocks only one
  if (T1) return p1(A, B | T1, r);
  if (r == 1) return false;        // P1 has no threat, needs completion on its last move: P2 move cannot create one
  u64 cA = A, cB = B; canon(cA, cB);
  Ent *e; int t = ttGet(cA, cB, r, e);
  if (t >= 0) return t;
  int score[49]; memset(score, 0, sizeof(int) * N);
  u64 cand = 0;
  static const int W[8] = {1, 4, 16, 64, 256, 1024, 4096, 16384};
  for (int i = 0; i < np; i++) {
    u64 p = pl[i];
    if (!(p & B)) {
      int miss = __builtin_popcountll(p & ~A);
      if (miss <= r) {
        u64 m = p & ~A; cand |= m;
        int w = W[__builtin_popcountll(p & A)];
        for (u64 x = m; x; x &= x - 1) score[__builtin_ctzll(x)] += w;
      }
    }
    if (strongG && !(p & A)) {
      int miss = __builtin_popcountll(p & ~B);
      if (miss <= r) {       // P2 has this move plus r-1 later ones
        u64 m = p & ~B; cand |= m;
        int w = W[__builtin_popcountll(p & B)];
        for (u64 x = m; x; x &= x - 1) score[__builtin_ctzll(x)] += w;
      }
    }
  }
  int cells[49], nc = 0;
  for (u64 x = cand; x; x &= x - 1) cells[nc++] = __builtin_ctzll(x);
  sort(cells, cells + nc, [&](int a, int b) { return score[a] > score[b]; });
  bool res = (nc > 0);   // no relevant cell: P1 has no live placement within bound -> P1 fails
  for (int k = 0; k < nc; k++) {
    if (!p1(A, B | (1ULL << cells[k]), r)) { res = false; break; }
  }
  ttPut(e, cA, cB, r, res);
  return res;
}

typedef vector<pair<int,int>> Shape;
static Shape getShape(const string &s) {
  if (s == "I4") return {{0,0},{1,0},{2,0},{3,0}};
  if (s == "L5") return {{0,0},{1,0},{2,0},{3,0},{3,1}};
  if (s == "Y5") return {{0,0},{1,0},{2,0},{3,0},{1,1}};
  if (s == "N5") return {{0,0},{1,0},{2,0},{2,1},{3,1}};
  if (s == "T4") return {{0,0},{1,0},{2,0},{1,1}};
  if (s == "L4") return {{0,0},{1,0},{2,0},{2,1}};
  if (s == "S4") return {{0,0},{1,0},{1,1},{2,1}};
  if (s == "I3") return {{0,0},{1,0},{2,0}};
  if (s == "L3") return {{0,0},{1,0},{0,1}};
  if (s == "P5") return {{0,0},{1,0},{0,1},{1,1},{0,2}};
  if (s == "O4") return {{0,0},{1,0},{0,1},{1,1}};
  fprintf(stderr, "unknown shape\n"); exit(2);
}

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage\n"); return 1; }
  string sh = argv[1]; n = atoi(argv[2]); N = n * n; strongG = string(argv[3]) == "strong";
  int maxK = atoi(argv[4]);
  if (argc > 5) tlimit = atof(argv[5]);
  int bits = argc > 6 ? atoi(argv[6]) : 25;
  FULL = (N == 64) ? ~0ULL : ((1ULL << N) - 1);
  Shape S = getShape(sh);
  // all placements over the 8 symmetries
  vector<u64> all;
  for (int s = 0; s < 8; s++) {
    Shape T;
    for (auto [x, y] : S) {
      int a = x, b = y;
      if (s & 1) swap(a, b);
      if (s & 2) a = -a;
      if (s & 4) b = -b;
      T.push_back({a, b});
    }
    int mx = 99, my = 99;
    for (auto [a, b] : T) { mx = min(mx, a); my = min(my, b); }
    for (auto &c : T) { c.first -= mx; c.second -= my; }
    int w = 0, h = 0;
    for (auto [a, b] : T) { w = max(w, a + 1); h = max(h, b + 1); }
    for (int ox = 0; ox + w <= n; ox++)
      for (int oy = 0; oy + h <= n; oy++) {
        u64 m = 0;
        for (auto [a, b] : T) m |= 1ULL << ((oy + b) * n + ox + a);
        all.push_back(m);
      }
  }
  sort(all.begin(), all.end()); all.erase(unique(all.begin(), all.end()), all.end());
  pl = all;
  initSym();
  tt = (Ent *)malloc(sizeof(Ent) << bits);
  ttmask = (1ULL << bits) - 1;
  for (u64 i = 0; i <= ttmask; i++) { tt[i].a = ~0ULL; tt[i].b = ~0ULL; tt[i].w = 127; tt[i].l = -1; }
  printf("shape=%s n=%d game=%s placements=%zu tt=2^%d\n", sh.c_str(), n, strongG ? "strong" : "weak", pl.size(), bits);
  fflush(stdout);
  t0 = chrono::steady_clock::now();
  int K0 = 1; if (maxK < 0) { K0 = -maxK; maxK = K0; }
  for (int K = K0; K <= maxK; K++) {
    // quick necessary check: some placement fits in K moves is implicit
    try {
      bool w = p1(0, 0, K);
      double el = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
      printf("K=%d %s nodes=%llu time=%.1fs\n", K, w ? "P1_WINS" : "no_win_within_K", (unsigned long long)nodes, el);
      fflush(stdout);
      if (w) break;
    } catch (Timeout &) {
      printf("K=%d TIMEOUT after %.0fs nodes=%llu\n", K, tlimit, (unsigned long long)nodes);
      return 3;
    }
  }
  return 0;
}
