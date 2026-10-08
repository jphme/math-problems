"""Independent checker for the strong-game certificates (format: ../README.md, "Strong game, canonical-key format").

Shares no code with solver_strong.cpp. It rebuilds the placements from the header shape, plays the
certificate strategy on the real board against EVERY move of the opponent, and accepts only these
leaves:

  kind xwin       X completes a copy (X's move from the table), with at most `budget` X moves,
                  and O never completes a copy first; a full board or an exhausted budget fails.
  kind ostrategy  X never completes a copy; a line ends when O completes a copy, the board is full,
                  X has made `budget` moves, X has no O-free placement with at most r missing cells
                  (r = X moves left), or at a pairing leaf (P line) that the checker verifies.

Positions are looked up by their canonical key (least (X, O) pair over the 8 board symmetries);
the move stored in the canonical frame is mapped back to the real board, and the real successor
positions are checked. Memoisation is on canonical keys, which is sound because the checker
verifies that the placement family is invariant under the 8 symmetries.

usage: uv run python check6.py CERT[.gz] [--expect-kind K] [--expect-budget B]
       [--expect-board N] [--expect-shape "x,y;..."] [--max-rss-mb M] [--time-limit S]
exit 0 PASS, 1 FAIL, 2 ABORT (cap exceeded, no verdict)
"""
import argparse
import gzip
import resource
import sys
import time


def rss_mb():
    r = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return r / 2**20 if sys.platform == "darwin" else r / 2**10


def shape_cells(text):
    return [tuple(int(v) for v in t.split(",")) for t in text]


def all_placements(shape, n):
    """Every image of the shape under rotations/reflections, translated onto the n x n board."""
    out = set()
    for a, b, c, d in ((1, 0, 0, 1), (0, -1, 1, 0), (-1, 0, 0, -1), (0, 1, -1, 0),
                       (-1, 0, 0, 1), (1, 0, 0, -1), (0, 1, 1, 0), (0, -1, -1, 0)):
        pts = [(a * x + b * y, c * x + d * y) for x, y in shape]
        for tx in range(-3 * n, 3 * n):
            for ty in range(-3 * n, 3 * n):
                cells = [(x + tx, y + ty) for x, y in pts]
                if all(0 <= x < n and 0 <= y < n for x, y in cells):
                    m = 0
                    for x, y in cells:
                        m |= 1 << (y * n + x)
                    out.add(m)
    return sorted(out)


def board_maps(n):
    """The 8 symmetries of the n x n board as cell permutations (list of lists)."""
    maps = []
    for rot in range(4):
        for refl in range(2):
            perm = []
            for c in range(n * n):
                x, y = c % n, c // n
                if refl:
                    x = n - 1 - x
                for _ in range(rot):
                    x, y = n - 1 - y, x
                perm.append(y * n + x)
            maps.append(perm)
    assert len({tuple(p) for p in maps}) == 8
    return maps


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert")
    ap.add_argument("--expect-kind")
    ap.add_argument("--expect-budget", type=int)
    ap.add_argument("--expect-board", type=int)
    ap.add_argument("--expect-shape")
    ap.add_argument("--max-rss-mb", type=float, default=6000)
    ap.add_argument("--time-limit", type=float, default=1e18)
    a = ap.parse_args()
    t0 = time.time()

    def caps():
        if rss_mb() > a.max_rss_mb:
            print(f"ABORT rss {rss_mb():.0f}MB > {a.max_rss_mb} (no verdict)")
            sys.exit(2)
        if time.time() - t0 > a.time_limit:
            print(f"ABORT time > {a.time_limit}s (no verdict)")
            sys.exit(2)

    hdr = {}
    table = {}
    pairs = {}
    ended = False
    opener = gzip.open if a.cert.endswith(".gz") else open
    with opener(a.cert, "rt") as f:
        for i, line in enumerate(f):
            if i % 1000000 == 0:
                caps()
            t = line.split()
            if not t or t[0].startswith("#"):
                continue
            if ended:
                sys.exit("FAIL data after end")
            if t[0] in ("X", "O"):
                k = (int(t[1], 16) << 64) | int(t[2], 16)
                if k in table or k in pairs:
                    print("FAIL duplicate key", t[1], t[2]); sys.exit(1)
                table[k] = (t[0], int(t[3]))
            elif t[0] == "P":
                k = (int(t[1], 16) << 64) | int(t[2], 16)
                if k in table or k in pairs:
                    print("FAIL duplicate key", t[1], t[2]); sys.exit(1)
                pairs[k] = [tuple(int(v) for v in pr.split(",")) for pr in t[3:]]
            elif t[0] == "end":
                ended = True
            else:
                hdr[t[0]] = t[1:]
    if not ended:
        print("FAIL truncated (no end line)"); sys.exit(1)
    W, H = int(hdr["board"][0]), int(hdr["board"][1])
    if W != H:
        print("FAIL board must be square"); sys.exit(1)
    n = W
    N = n * n
    shape = shape_cells(hdr["shape"])
    kind = hdr["kind"][0]
    K = int(hdr["budget"][0])
    if hdr.get("keys") != ["canonical"]:
        print("FAIL keys must be canonical"); sys.exit(1)
    if a.expect_kind is not None and kind != a.expect_kind:
        print(f"FAIL kind {kind} != {a.expect_kind}"); sys.exit(1)
    if a.expect_budget is not None and K != a.expect_budget:
        print(f"FAIL budget {K} != {a.expect_budget}"); sys.exit(1)
    if a.expect_board is not None and n != a.expect_board:
        print(f"FAIL board {n} != {a.expect_board}"); sys.exit(1)
    if a.expect_shape is not None:
        want = shape_cells(a.expect_shape.split(";"))
        if sorted(want) != sorted(shape):
            print(f"FAIL shape {shape} != {want}"); sys.exit(1)
    if kind == "xwin" and pairs:
        print("FAIL P lines in an xwin certificate"); sys.exit(1)
    for k, (who, _) in table.items():
        if (kind == "xwin") != (who == "X"):
            print("FAIL line type does not match kind"); sys.exit(1)

    PL = all_placements(shape, n)
    maps = board_maps(n)
    PLset = set(PL)

    def img(perm, m):
        o = 0
        while m:
            b = m & -m
            o |= 1 << perm[b.bit_length() - 1]
            m ^= b
        return o

    for perm in maps:
        for p in PL:
            if img(perm, p) not in PLset:
                print("FAIL placement family not symmetric"); sys.exit(1)
    inv = []
    for perm in maps:
        q = [0] * N
        for c in range(N):
            q[perm[c]] = c
        inv.append(q)
    through = [[p for p in PL if p >> c & 1] for c in range(N)]
    FULL = (1 << N) - 1

    def canon(X, O):
        best = None
        bi = -1
        for i, perm in enumerate(maps):
            kx, ko = img(perm, X), img(perm, O)
            if best is None or (kx, ko) < best:
                best, bi = (kx, ko), i
        return (best[0] << 64) | best[1], bi

    def completes_with(S, c):
        return any(p & S == p for p in through[c])

    def hopeless(X, O, r):
        for p in PL:
            if not p & O and bin(p & ~X).count("1") <= r:
                return False
        return True

    done_x, done_o = set(), set()
    used = set()
    stats = {"x_nodes": 0, "o_nodes": 0, "pair_leaves": 0, "leaf_hopeless": 0, "leaf_budget": 0,
             "leaf_full": 0, "o_completes": 0, "x_completes": 0, "max_x_moves": 0}
    counter = [0]

    def tick():
        counter[0] += 1
        if counter[0] % 65536 == 0:
            caps()

    def fail(msg):
        print("FAIL", msg)
        sys.exit(1)

    # ---------------- ostrategy
    def ox(X, O):  # X to move
        tick()
        r = K - bin(X).count("1")
        free = FULL & ~(X | O)
        if r <= 0:
            stats["leaf_budget"] += 1; return
        if not free:
            stats["leaf_full"] += 1; return
        if hopeless(X, O, r):
            stats["leaf_hopeless"] += 1; return
        k, gi = canon(X, O)
        if k in done_x:
            return
        if k in pairs:
            used.add(k)
            q = inv[gi]
            seen = 0
            prs = []
            for u, v in pairs[k]:
                if not (0 <= u < N and 0 <= v < N):
                    fail(f"pair cell off the board at X={X:x} O={O:x}")
                cu, cv = q[u], q[v]
                bu, bv = 1 << cu, 1 << cv
                if cu == cv or not (free & bu) or not (free & bv) or (seen & (bu | bv)):
                    fail(f"bad pairing cells at X={X:x} O={O:x}")
                seen |= bu | bv
                prs.append(bu | bv)
            for p in PL:
                if p & O:
                    continue
                if bin(p & ~X).count("1") > r:
                    continue
                if not any(p & pb == pb for pb in prs):
                    fail(f"pairing misses placement {p:x} at X={X:x} O={O:x}")
            stats["pair_leaves"] += 1
            done_x.add(k)
            return
        stats["x_nodes"] += 1
        f = free
        while f:
            b = f & -f
            f ^= b
            c = b.bit_length() - 1
            X2 = X | b
            if completes_with(X2, c):
                fail(f"X completes a copy: X={X2:x} O={O:x}")
            oo(X2, O)
        done_x.add(k)

    def oo(X, O):  # O to move
        tick()
        r = K - bin(X).count("1")
        free = FULL & ~(X | O)
        if r <= 0:
            stats["leaf_budget"] += 1; return
        if not free:
            stats["leaf_full"] += 1; return
        if hopeless(X, O, r):
            stats["leaf_hopeless"] += 1; return
        k, gi = canon(X, O)
        if k in done_o:
            return
        e = table.get(k)
        if e is None:
            fail(f"no O move for X={X:x} O={O:x}")
        used.add(k)
        if not (0 <= e[1] < N):
            fail(f"O move off the board at X={X:x} O={O:x}")
        c = inv[gi][e[1]]
        if not (free >> c & 1):
            fail(f"illegal O move at X={X:x} O={O:x}")
        O2 = O | (1 << c)
        stats["o_nodes"] += 1
        if completes_with(O2, c):
            stats["o_completes"] += 1
        else:
            ox(X, O2)
        done_o.add(k)

    # ---------------- xwin
    def xx(X, O):  # X to move
        tick()
        k, gi = canon(X, O)
        if k in done_x:
            return
        nx = bin(X).count("1")
        if nx >= K:
            fail(f"budget exhausted at X={X:x} O={O:x}")
        e = table.get(k)
        if e is None:
            fail(f"no X move for X={X:x} O={O:x}")
        used.add(k)
        if not (0 <= e[1] < N):
            fail(f"X move off the board at X={X:x} O={O:x}")
        c = inv[gi][e[1]]
        free = FULL & ~(X | O)
        if not (free >> c & 1):
            fail(f"illegal X move at X={X:x} O={O:x}")
        X2 = X | (1 << c)
        stats["x_nodes"] += 1
        stats["max_x_moves"] = max(stats["max_x_moves"], nx + 1)
        if completes_with(X2, c):
            stats["x_completes"] += 1
            done_x.add(k)
            return
        if nx + 1 >= K:
            fail(f"X has used its budget without a copy at X={X2:x} O={O:x}")
        f = free & ~(1 << c)
        if not f:
            fail(f"board full (draw) at X={X2:x} O={O:x}")
        while f:
            b = f & -f
            f ^= b
            d = b.bit_length() - 1
            O2 = O | b
            if completes_with(O2, d):
                fail(f"O completes a copy first at X={X2:x} O={O2:x}")
            xx(X2, O2)
        done_x.add(k)

    sys.setrecursionlimit(100000)
    if kind == "ostrategy":
        ox(0, 0)
    elif kind == "xwin":
        xx(0, 0)
    else:
        fail(f"unknown kind {kind}")
    unused = len(table) + len(pairs) - len(used)
    print(f"PASS {kind} board={n}x{n} shape={';'.join(f'{x},{y}' for x, y in shape)} budget={K} "
          f"placements={len(PL)} table={len(table)} pairs={len(pairs)} unused_entries={unused} "
          + " ".join(f"{k}={v}" for k, v in stats.items())
          + f" time={time.time() - t0:.1f}s rss={rss_mb():.0f}MB")


if __name__ == "__main__":
    main()
