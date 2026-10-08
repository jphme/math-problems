"""Independent checker for strong polyomino achievement game certificates.

Written from a description of the format and semantics (now in ../README.md) only.  Verifies, from the empty
board, either
  xwin       : X (moves first) completes a copy within `budget` of its own moves against every
               O play, and O never completes a copy first;
  ostrategy  : against every X play, X does not complete a copy within `budget` own moves
               (O may win, board may fill, X may run out of budget).
Strong game: whoever completes a copy first wins.

Usage: uv run python chk.py CERT[.gz] --board N --shape "0,0;1,0;..." --kind K --budget B
Exit code 0 = PASS, 1 = FAIL (reason printed), 2 = bad usage.
Positions are verified in canonical form (least (g(X),g(O)) over the 8 board symmetries); the
memo is sound because the placement family is verified invariant under all 8 symmetries.
"""
import argparse, gzip, sys, time, resource

sys.setrecursionlimit(10000)
MAX_RSS = 5.5e9


class Fail(Exception):
    pass


def rss():
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss  # bytes on macOS


# ------------------------------------------------------------------ geometry
def parse_shape(s):
    toks = s.replace(";", " ").split()
    cells = set()
    for t in toks:
        a, b = t.split(",")
        cells.add((int(a), int(b)))
    return frozenset(cells)


def norm(cells):
    mx = min(c[0] for c in cells); my = min(c[1] for c in cells)
    return frozenset((x - mx, y - my) for x, y in cells)


def orientations(cells):
    out = set()
    pts = list(cells)
    for swap in (0, 1):
        for sx in (1, -1):
            for sy in (1, -1):
                q = []
                for x, y in pts:
                    if swap:
                        x, y = y, x
                    q.append((sx * x, sy * y))
                out.add(norm(q))
    return out


def placements(cells, n):
    res = set()
    for o in orientations(cells):
        w = max(c[0] for c in o) + 1; h = max(c[1] for c in o) + 1
        for ox in range(n - w + 1):
            for oy in range(n - h + 1):
                m = 0
                for x, y in o:
                    m |= 1 << ((y + oy) * n + (x + ox))
                res.add(m)
    return sorted(res)


def sym_maps(n):
    """8 dihedral maps of the n x n board as lists cell -> cell."""
    maps = []
    for swap in (0, 1):
        for fx in (0, 1):
            for fy in (0, 1):
                mp = [0] * (n * n)
                for y in range(n):
                    for x in range(n):
                        a, b = (y, x) if swap else (x, y)
                        if fx: a = n - 1 - a
                        if fy: b = n - 1 - b
                        mp[y * n + x] = b * n + a
                maps.append(mp)
    assert len({tuple(m) for m in maps}) == 8
    return maps


CH = 13  # chunk width in bits for the symmetry lookup tables


def make_canon(n):
    N = n * n
    maps = sym_maps(n)
    nch = (N + CH - 1) // CH
    tabs = []
    for mp in maps:
        per = []
        for ci in range(nch):
            t = [0] * (1 << CH)
            for v in range(1, 1 << CH):
                low = v & -v
                b = low.bit_length() - 1
                cell = ci * CH + b
                t[v] = t[v ^ low] | ((1 << mp[cell]) if cell < N else 0)
            per.append(t)
        tabs.append(per)
    lines = ["def canon(x, o):"]
    for s in range(8):
        terms = " | ".join(f"T{s}_{c}[(x >> {c*CH}) & {(1<<CH)-1}]" for c in range(nch))
        lines.append(f"    a{s} = {terms}")
    lines.append("    m = min(" + ", ".join(f"a{s}" for s in range(8)) + ")")
    lines.append("    best = None")
    for s in range(8):
        terms = " | ".join(f"T{s}_{c}[(o >> {c*CH}) & {(1<<CH)-1}]" for c in range(nch))
        lines.append(f"    if a{s} == m:")
        lines.append(f"        b = {terms}")
        lines.append("        if best is None or b < best: best = b")
    lines.append(f"    return (m << {N}) | best")
    g = {}
    for s in range(8):
        for c in range(nch):
            g[f"T{s}_{c}"] = tabs[s][c]
    exec("\n".join(lines), g)
    return g["canon"], maps


# ------------------------------------------------------------------ certificate parsing
def read_cert(path):
    op = gzip.open if path.endswith(".gz") else open
    hdr = {}
    table = {}
    kinds = set()
    ended = False
    with op(path, "rt") as f:
        for ln, line in enumerate(f, 1):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if ended:
                raise Fail(f"line {ln}: content after 'end'")
            if line == "end":
                ended = True
                continue
            p = line.split()
            tag = p[0]
            if tag in ("board", "shape", "kind", "budget", "keys"):
                if tag in hdr:
                    raise Fail(f"line {ln}: duplicate header {tag}")
                if table:
                    raise Fail(f"line {ln}: header after table")
                hdr[tag] = p[1:]
            elif tag in ("O", "X", "P"):
                if len(p) < 4:
                    raise Fail(f"line {ln}: short line")
                try:
                    key = (int(p[1], 16), int(p[2], 16))
                except ValueError:
                    raise Fail(f"line {ln}: bad hex")
                tk = (tag, key)
                if tk in table:
                    raise Fail(f"line {ln}: duplicate key {tag} {p[1]} {p[2]}")
                if tag == "P":
                    prs = []
                    for t in p[3:]:
                        a, b = t.split(",")
                        prs.append((int(a), int(b)))
                    table[tk] = prs
                else:
                    if len(p) != 4:
                        raise Fail(f"line {ln}: extra tokens")
                    table[tk] = int(p[3])
                kinds.add(tag)
            else:
                raise Fail(f"line {ln}: unknown tag {tag!r}")
    if not ended:
        raise Fail("missing 'end'")
    return hdr, table, kinds


# ------------------------------------------------------------------ main check
def run(args):
    t0 = time.time()
    n = args.board
    N = n * n
    shape = norm(parse_shape(args.shape))
    hdr, table, kinds = read_cert(args.cert)
    # header must match the claim
    need = {"board", "shape", "kind", "budget", "keys"}
    if set(hdr) != need:
        raise Fail(f"header keys {sorted(hdr)}")
    if hdr["board"] != [str(n), str(n)]:
        raise Fail(f"board header {hdr['board']} != {n} {n}")
    if orientations(parse_shape(" ".join(hdr["shape"]))) != orientations(shape):
        raise Fail("shape header differs from claimed shape")
    if hdr["kind"] != [args.kind]:
        raise Fail(f"kind header {hdr['kind']} != {args.kind}")
    if hdr["budget"] != [str(args.budget)]:
        raise Fail(f"budget header {hdr['budget']} != {args.budget}")
    if hdr["keys"] != ["canonical"]:
        raise Fail("keys header not 'canonical'")
    K = args.budget
    pls = placements(shape, n)
    canon, maps = make_canon(n)
    # the placement family must be invariant under all 8 symmetries (memo soundness)
    pset = set(pls)
    for mp in maps:
        for m in pls:
            g = 0
            mm = m
            while mm:
                lo = mm & -mm
                g |= 1 << mp[lo.bit_length() - 1]
                mm ^= lo
            if g not in pset:
                raise Fail("placement family not symmetric")
    full = (1 << N) - 1
    pc = [[m for m in pls if m >> c & 1] for c in range(N)]
    print(f"board {n}x{n}, shape {sorted(shape)}, {len(pls)} placements, kind {args.kind}, K={K}, "
          f"table lines {len(table)}")

    def completes(mask, c):
        for m in pc[c]:
            if m & mask == m:
                return True
        return False

    S = N
    MASK = full
    good = set()
    used = set()
    counts = {"a_O_completes": 0, "b_budget": 0, "c_full": 0, "d_hopeless": 0, "e_pairing": 0,
              "xwin_wins": 0, "x_nodes": 0, "o_nodes": 0}
    tick = [0]

    def guard():
        tick[0] += 1
        if tick[0] & 0xFFFF == 0 and rss() > MAX_RSS:
            raise Fail("ABORT: RSS limit exceeded")

    def free_cells(u):
        f = ~u & full
        while f:
            lo = f & -f
            yield lo.bit_length() - 1
            f ^= lo

    def hopeless(x, o, r):
        for p in pls:
            if not p & o and (p & ~x).bit_count() <= r:
                return False
        return True

    def check_pairs(x, o, r, prs):
        seen = set()
        occ = x | o
        for a, b in prs:
            if a == b or not (0 <= a < N and 0 <= b < N):
                raise Fail("pairing: bad cells")
            if occ >> a & 1 or occ >> b & 1:
                raise Fail("pairing: pair cell not free")
            if a in seen or b in seen:
                raise Fail("pairing: pairs not disjoint")
            seen.add(a); seen.add(b)
        pm = [(1 << a) | (1 << b) for a, b in prs]
        for p in pls:
            if p & o == 0 and (p & ~x).bit_count() <= r:
                if not any(p & q == q for q in pm):
                    raise Fail("pairing: uncovered placement")

    # ---------------- ostrategy
    def vx(key):
        if key in good:
            return
        guard()
        x = key >> S; o = key & MASK
        nx = x.bit_count(); r = K - nx
        if r <= 0:
            counts["b_budget"] += 1; good.add(key); return
        if (x | o) == full:
            counts["c_full"] += 1; good.add(key); return
        pl = table.get(("P", (x, o)))
        if pl is not None:
            used.add(("P", (x, o)))
            check_pairs(x, o, r, pl)
            counts["e_pairing"] += 1; good.add(key); return
        if hopeless(x, o, r):
            counts["d_hopeless"] += 1; good.add(key); return
        counts["x_nodes"] += 1
        for c in free_cells(x | o):
            x2 = x | (1 << c)
            if completes(x2, c):
                raise Fail(f"X completes a copy at x={x:x} o={o:x} cell {c}")
            if nx + 1 >= K:
                counts["b_budget"] += 1
                continue
            vo(canon(x2, o))
        good.add(key)

    def vo(key):
        if key in good:
            return
        guard()
        x = key >> S; o = key & MASK
        r = K - x.bit_count()
        if r <= 0:
            counts["b_budget"] += 1; good.add(key); return
        if (x | o) == full:
            counts["c_full"] += 1; good.add(key); return
        tk = ("O", (x, o))
        c = table.get(tk)
        if c is None:
            if hopeless(x, o, r):
                counts["d_hopeless"] += 1; good.add(key); return
            raise Fail(f"no O line for O-to-move x={x:x} o={o:x}")
        used.add(tk)
        if not (0 <= c < N) or (x | o) >> c & 1:
            raise Fail(f"illegal O move {c} at x={x:x} o={o:x}")
        o2 = o | (1 << c)
        counts["o_nodes"] += 1
        if completes(o2, c):
            counts["a_O_completes"] += 1; good.add(key); return
        vx(canon(x, o2))
        good.add(key)

    # ---------------- xwin
    def vxw(key):
        if key in good:
            return
        guard()
        x = key >> S; o = key & MASK
        nx = x.bit_count()
        tk = ("X", (x, o))
        c = table.get(tk)
        if c is None:
            raise Fail(f"no X line for x={x:x} o={o:x}")
        used.add(tk)
        if nx >= K:
            raise Fail("X to move without budget")
        if not (0 <= c < N) or (x | o) >> c & 1:
            raise Fail(f"illegal X move {c} at x={x:x} o={o:x}")
        x2 = x | (1 << c)
        counts["x_nodes"] += 1
        if completes(x2, c):
            counts["xwin_wins"] += 1; good.add(key); return
        if nx + 1 >= K:
            raise Fail(f"X out of budget without a copy at x={x:x} o={o:x}")
        if (x2 | o) == full:
            raise Fail("board full without X copy")
        for d in free_cells(x2 | o):
            o2 = o | (1 << d)
            counts["o_nodes"] += 1
            if completes(o2, d):
                raise Fail(f"O completes a copy at x={x2:x} o={o:x} cell {d}")
            vxw(canon(x2, o2))
        good.add(key)

    if args.kind == "ostrategy":
        if kinds - {"O", "P"}:
            raise Fail("ostrategy certificate contains X lines")
        vx(0)
    elif args.kind == "xwin":
        if kinds - {"X"}:
            raise Fail("xwin certificate contains O/P lines")
        vxw(0)
    else:
        raise Fail("unknown kind")
    unused = len(table) - len(used)
    print("leaf/node counts:", counts)
    print(f"canonical positions verified: {len(good)}; unused table lines: {unused}; "
          f"peak RSS {rss()/1e9:.2f} GB; {time.time()-t0:.1f} s")
    return unused


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert")
    ap.add_argument("--board", type=int, required=True)
    ap.add_argument("--shape", required=True)
    ap.add_argument("--kind", required=True, choices=["xwin", "ostrategy"])
    ap.add_argument("--budget", type=int, required=True)
    args = ap.parse_args()
    try:
        run(args)
    except Fail as e:
        print("FAIL:", e)
        sys.exit(1)
    except Exception as e:  # any parse error = reject
        print("FAIL (malformed):", repr(e))
        sys.exit(1)
    print("PASS")


if __name__ == "__main__":
    main()
