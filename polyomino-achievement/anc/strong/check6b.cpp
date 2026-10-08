// check6b.cpp -- second, independently written checker for the strong-game certificates (ostrategy/xwin).
// Shares no code with solver_strong.cpp or check6.py. Differences from check6.py on purpose:
//  * memoisation on EXACT positions (no symmetry assumption in the memo),
//  * placements enumerated by sliding the 8 transformed shapes over the board,
//  * symmetries implemented as coordinate formulas; the certificate key of a real position is the
//    least (X', O') over the 8 images, the stored move is mapped back by the inverse formula.
// usage: check6b CERT (plain text; pipe gzip: gzip -dc C.gz | check6b -)
// exit 0 PASS, 1 FAIL
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <iostream>
#include <sstream>
#include <fstream>
#include <sys/resource.h>
typedef unsigned long long U;
static int n, NC, K;
static std::vector<U> places;
static std::vector<std::vector<U>> placesAt;
static U ALL;

struct PH { size_t operator()(const std::pair<U,U> &p) const { return std::hash<U>()(p.first * 0x9E3779B97F4A7C15ULL + p.second); } };
static std::unordered_map<std::pair<U,U>, int, PH> moveOf;                    // X or O lines
static std::unordered_map<std::pair<U,U>, std::vector<std::pair<int,int>>, PH> pairsOf;
static std::unordered_set<std::pair<U,U>, PH> okX, okO;
static std::string kind;
static long long cntNodes = 0, cntPair = 0;

static void die(const std::string &m) { printf("FAIL %s\n", m.c_str()); exit(1); }
static void tick() {
  if ((++cntNodes & 0xFFFFF) == 0) {
    struct rusage ru; getrusage(RUSAGE_SELF, &ru);
#ifdef __APPLE__
    long mb = ru.ru_maxrss >> 20;
#else
    long mb = ru.ru_maxrss >> 10;
#endif
    if (mb > 6000) { printf("ABORT rss %ld MB (no verdict)\n", mb); exit(2); }
  }
}
// symmetry k applied to cell (x,y): k = 0..7 -> rotate by (k&3) quarter turns, then mirror if k>=4
static int mapCell(int k, int c) {
  int x = c % n, y = c / n;
  for (int i = 0; i < (k & 3); i++) { int t = x; x = n - 1 - y; y = t; }
  if (k >= 4) y = n - 1 - y;
  return y * n + x;
}
static int unmapCell(int k, int c) {
  for (int j = 0; j < 8; j++) {  // brute-force inverse
    if (mapCell(k, j) == c) return j;
  }
  return -1;
}
static int invTab[8][64], fwdTab[8][64];
static U mapSet(int k, U s) { U o = 0; for (int c = 0; c < NC; c++) if (s >> c & 1) o |= 1ULL << fwdTab[k][c]; return o; }
static std::pair<U,U> key(U X, U O, int &kk) {
  std::pair<U,U> best(~0ULL, ~0ULL); kk = -1;
  for (int k = 0; k < 8; k++) {
    std::pair<U,U> p(mapSet(k, X), mapSet(k, O));
    if (kk < 0 || p < best) { best = p; kk = k; }
  }
  return best;
}
static bool hasCopyThrough(U S, int c) { for (U p : placesAt[c]) if ((p & S) == p) return true; return false; }
static int pc(U x) { return __builtin_popcountll(x); }
static bool noHope(U X, U O, int r) {
  for (U p : places) if (!(p & O) && pc(p & ~X) <= r) return false;
  return true;
}

static void nodeOX(U X, U O);
static void nodeOO(U X, U O) {
  tick();
  int r = K - pc(X);
  U fr = ALL & ~(X | O);
  if (r <= 0 || !fr || noHope(X, O, r)) return;
  std::pair<U,U> me(X, O);
  if (okO.count(me)) return;
  int kk; auto k = key(X, O, kk);
  auto it = moveOf.find(k);
  if (it == moveOf.end()) die("missing O move");
  int mc = it->second;
  if (mc < 0 || mc >= NC) die("bad cell");
  int c = invTab[kk][mc];
  if (!(fr >> c & 1)) die("O move on occupied cell");
  U O2 = O | (1ULL << c);
  if (!hasCopyThrough(O2, c)) nodeOX(X, O2);
  okO.insert(me);
}
static void nodeOX(U X, U O) {
  tick();
  int r = K - pc(X);
  U fr = ALL & ~(X | O);
  if (r <= 0 || !fr || noHope(X, O, r)) return;
  std::pair<U,U> me(X, O);
  if (okX.count(me)) return;
  int kk; auto k = key(X, O, kk);
  auto pit = pairsOf.find(k);
  if (pit != pairsOf.end()) {
    U usedCells = 0; std::vector<U> pm;
    for (auto &pr : pit->second) {
      if (pr.first < 0 || pr.first >= NC || pr.second < 0 || pr.second >= NC) die("bad pair cell");
      int a = invTab[kk][pr.first], b = invTab[kk][pr.second];
      U m = (1ULL << a) | (1ULL << b);
      if (a == b || (m & ~fr) || (m & usedCells)) die("pairs not disjoint free cells");
      usedCells |= m; pm.push_back(m);
    }
    for (U p : places) {
      if ((p & O) || pc(p & ~X) > r) continue;
      bool hit = false;
      for (U m : pm) if ((p & m) == m) { hit = true; break; }
      if (!hit) die("pairing does not cover a placement");
    }
    cntPair++;
    okX.insert(me);
    return;
  }
  for (int c = 0; c < NC; c++) {
    if (!(fr >> c & 1)) continue;
    U X2 = X | (1ULL << c);
    if (hasCopyThrough(X2, c)) die("X completes a copy");
    nodeOO(X2, O);
  }
  okX.insert(me);
}
static void nodeXX(U X, U O) {   // xwin: X to move
  tick();
  std::pair<U,U> me(X, O);
  if (okX.count(me)) return;
  if (pc(X) >= K) die("X budget exhausted");
  int kk; auto k = key(X, O, kk);
  auto it = moveOf.find(k);
  if (it == moveOf.end()) die("missing X move");
  int mc = it->second;
  if (mc < 0 || mc >= NC) die("bad cell");
  int c = invTab[kk][mc];
  U fr = ALL & ~(X | O);
  if (!(fr >> c & 1)) die("X move on occupied cell");
  U X2 = X | (1ULL << c);
  if (!hasCopyThrough(X2, c)) {
    if (pc(X2) >= K) die("X used its budget without a copy");
    U f2 = fr & ~(1ULL << c);
    if (!f2) die("board full without X copy");
    for (int d = 0; d < NC; d++) {
      if (!(f2 >> d & 1)) continue;
      U O2 = O | (1ULL << d);
      if (hasCopyThrough(O2, d)) die("O completes a copy first");
      nodeXX(X2, O2);
    }
  }
  okX.insert(me);
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: check6b CERT|- [--expect-kind K] [--expect-budget B] [--expect-board N] [--expect-shape \"x,y;...\"] [--expect-placements P]\n"); return 2; }
  // claim the certificate must certify; each given option is compared with the header
  std::string eKind, eShape; int eBudget = -1, eBoard = -1; long eplaces = -1;
  for (int i = 2; i < argc; i++) {
    std::string a = argv[i];
    if (i + 1 >= argc) { fprintf(stderr, "missing value for %s\n", a.c_str()); return 2; }
    std::string v = argv[++i];
    if (a == "--expect-kind") eKind = v;
    else if (a == "--expect-budget") eBudget = atoi(v.c_str());
    else if (a == "--expect-board") eBoard = atoi(v.c_str());
    else if (a == "--expect-shape") eShape = v;
    else if (a == "--expect-placements") eplaces = atol(v.c_str());
    else { fprintf(stderr, "unknown option %s\n", a.c_str()); return 2; }
  }
  std::istream *in; std::ifstream fin;
  if (std::string(argv[1]) == "-") in = &std::cin; else { fin.open(argv[1]); if (!fin) die("cannot open"); in = &fin; }
  std::string line; std::vector<std::pair<int,int>> shape; bool end = false; std::string keys;
  n = -1; K = -1;
  long long nX = 0, nO = 0, nP = 0;
  // header first (needed to parse keys), then body
  std::vector<std::string> body;
  while (std::getline(*in, line)) {
    if (line.empty() || line[0] == '#') continue;
    std::istringstream ss(line); std::string t; ss >> t;
    if (end) die("data after end");
    if (t == "board") { int w, h; ss >> w >> h; if (w != h) die("board not square"); n = w; }
    else if (t == "shape") { std::string c; while (ss >> c) { size_t q = c.find(','); shape.push_back({atoi(c.substr(0, q).c_str()), atoi(c.substr(q + 1).c_str())}); } }
    else if (t == "kind") ss >> kind;
    else if (t == "budget") ss >> K;
    else if (t == "keys") ss >> keys;
    else if (t == "end") end = true;
    else if (t == "X" || t == "O" || t == "P") {
      std::string a, b; ss >> a >> b;
      std::pair<U,U> k(strtoull(a.c_str(), 0, 16), strtoull(b.c_str(), 0, 16));
      if (moveOf.count(k) || pairsOf.count(k)) die("duplicate key");
      if (t == "P") {
        std::vector<std::pair<int,int>> v; std::string c;
        while (ss >> c) { size_t q = c.find(','); v.push_back({atoi(c.substr(0, q).c_str()), atoi(c.substr(q + 1).c_str())}); }
        pairsOf[k] = v; nP++;
        if (kind != "ostrategy") die("P line outside ostrategy");
      } else {
        int c; ss >> c; moveOf[k] = c;
        if ((t == "X") != (kind == "xwin")) die("line type does not match kind");
        if (t == "X") nX++; else nO++;
      }
    } else die("unknown line " + t);
  }
  if (!end) die("no end line");
  if (keys != "canonical") die("keys must be canonical");
  if (n < 2 || n > 8 || K < 0 || shape.empty()) die("bad header");
  if (!eKind.empty() && kind != eKind) die("kind " + kind + " != expected " + eKind);
  if (eBudget >= 0 && K != eBudget) die("budget " + std::to_string(K) + " != expected " + std::to_string(eBudget));
  if (eBoard >= 0 && n != eBoard) die("board " + std::to_string(n) + " != expected " + std::to_string(eBoard));
  if (!eShape.empty()) {
    std::vector<std::pair<int,int>> want; std::stringstream es(eShape); std::string c;
    while (std::getline(es, c, ';')) { size_t q = c.find(','); if (q == std::string::npos) die("bad --expect-shape"); want.push_back({atoi(c.substr(0, q).c_str()), atoi(c.substr(q + 1).c_str())}); }
    auto have = shape; std::sort(have.begin(), have.end()); std::sort(want.begin(), want.end());
    if (have != want) die("shape differs from --expect-shape");
  }
  NC = n * n; ALL = NC == 64 ? ~0ULL : ((1ULL << NC) - 1);
  for (int k = 0; k < 8; k++) for (int c = 0; c < NC; c++) { fwdTab[k][c] = mapCell(k, c); }
  for (int k = 0; k < 8; k++) for (int c = 0; c < NC; c++) { int j; for (j = 0; j < NC; j++) if (fwdTab[k][j] == c) break; invTab[k][c] = j; }
  (void)unmapCell;
  // placements: for each of the 8 maps of the shape, normalise and slide
  std::vector<U> pl;
  for (int k = 0; k < 8; k++) {
    std::vector<std::pair<int,int>> t;
    for (auto &q : shape) {
      int x = q.first, y = q.second;
      for (int i = 0; i < (k & 3); i++) { int z = x; x = -y; y = z; }
      if (k >= 4) y = -y;
      t.push_back({x, y});
    }
    int mx = 1000, my = 1000;
    for (auto &q : t) { if (q.first < mx) mx = q.first; if (q.second < my) my = q.second; }
    for (int ox = 0; ox < n; ox++) for (int oy = 0; oy < n; oy++) {
      U m = 0; bool ok = true;
      for (auto &q : t) { int x = q.first - mx + ox, y = q.second - my + oy; if (x >= n || y >= n) { ok = false; break; } m |= 1ULL << (y * n + x); }
      if (ok) pl.push_back(m);
    }
  }
  std::sort(pl.begin(), pl.end()); pl.erase(std::unique(pl.begin(), pl.end()), pl.end());
  places = pl;
  { std::unordered_set<U> S(pl.begin(), pl.end());
    for (int k = 0; k < 8; k++) for (U p : pl) if (!S.count(mapSet(k, p))) die("placements not symmetric"); }
  placesAt.assign(NC, {});
  for (U p : pl) for (int c = 0; c < NC; c++) if (p >> c & 1) placesAt[c].push_back(p);
  if (eplaces >= 0 && (long)pl.size() != eplaces) die("placements " + std::to_string(pl.size()) + " != expected " + std::to_string(eplaces));
  if (kind == "ostrategy") nodeOX(0, 0);
  else if (kind == "xwin") nodeXX(0, 0);
  else die("unknown kind");
  printf("PASS %s board=%dx%d shapecells=%zu budget=%d placements=%zu lines X=%lld O=%lld P=%lld exact_positions X=%zu O=%zu pair_leaf_visits=%lld\n",
         kind.c_str(), n, n, shape.size(), K, pl.size(), nX, nO, nP, okX.size(), okO.size(), cntPair);
  return 0;
}
