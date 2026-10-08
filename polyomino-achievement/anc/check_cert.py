"""Independent checker for certificates written by solver.cpp (weak / Maker-Breaker game).

Shares no code with the solver. It rebuilds the placements of the shape on the
W x H board from the shape cells in the certificate header, replays the
certificate as a strategy from the stated opening, and checks the rules listed
in README.md ("Certificate format and checker"). Cells are numbered y*W + x.

usage: uv run python check_cert.py CERT [--expect-board WxH] [--expect-shape 'x,y;..']
          [--expect-kind makerwin|breakerwin] [--expect-budget N] [--expect-opening 'c,c,..']
          [--max-rss-mb 4000] [--time-limit SEC]
Prints PASS/FAIL and statistics, or ABORT (exit 2) when a resource cap is exceeded.

Memory: node lines are kept as strings and split on use; checked states are memoised
under one packed integer key (node id, Maker cells, Breaker cells, budget). Peak RSS is
roughly 0.6-1 KB per certificate node.
"""
import resource
import sys
import time

sys.setrecursionlimit(100000)


def orientations(shape):
    out = set()
    for t in range(8):
        pts = []
        for x, y in shape:
            a, b = x, y
            if t & 1:
                a = -a
            if t & 2:
                b = -b
            if t & 4:
                a, b = b, a
            pts.append((a, b))
        mx = min(p[0] for p in pts)
        my = min(p[1] for p in pts)
        out.add(tuple(sorted((a - mx, b - my) for a, b in pts)))
    return out


def placements(shape, W, H):
    pls = set()
    for o in orientations(shape):
        ox = max(p[0] for p in o)
        oy = max(p[1] for p in o)
        for x in range(W - ox):
            for y in range(H - oy):
                m = 0
                for a, b in o:
                    m |= 1 << ((y + b) * W + (x + a))
                pls.add(m)
    return sorted(pls)


def popcount(x):
    return bin(x).count("1")


def main():
    path = sys.argv[1]
    args = sys.argv[2:]
    exp_board = exp_shape = exp_kind = exp_budget = exp_opening = None
    max_rss_mb = 4000
    time_limit = None
    for i, a in enumerate(args):
        if a == "--expect-board":
            exp_board = args[i + 1]
        if a == "--expect-shape":
            exp_shape = args[i + 1]
        if a == "--expect-kind":
            exp_kind = args[i + 1]
        if a == "--expect-budget":
            exp_budget = int(args[i + 1])
        if a == "--expect-opening":
            exp_opening = [int(v) for v in args[i + 1].split(",") if v != ""]
        if a == "--max-rss-mb":
            max_rss_mb = int(args[i + 1])
        if a == "--time-limit":
            time_limit = float(args[i + 1])
    t_start = time.time()

    def rss_mb():
        r = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        return r // (1024 * 1024) if sys.platform == "darwin" else r // 1024

    def check_limits():
        if rss_mb() > max_rss_mb:
            print(f"ABORT rss {rss_mb()}MB > --max-rss-mb {max_rss_mb} (no verdict)")
            sys.exit(2)
        if time_limit is not None and time.time() - t_start > time_limit:
            print(f"ABORT time {time.time() - t_start:.0f}s > --time-limit {time_limit:.0f} (no verdict)")
            sys.exit(2)

    nodes = {}
    hdr = {}
    for ln, line in enumerate(open(path)):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        t = line.split(None, 2)
        if t[0] in ("board", "kind", "budget", "root", "end", "shape", "opening"):
            hdr[t[0]] = line.split()[1:]
            continue
        nid = int(t[1])
        if nid in nodes:
            raise SystemExit(f"FAIL duplicate node id {nid}")
        nodes[nid] = line
        if ln & 0xFFFF == 0:
            check_limits()
    if "end" not in hdr:
        raise SystemExit("FAIL certificate truncated (no end line)")
    W, H = int(hdr["board"][0]), int(hdr["board"][1])
    shape = [tuple(int(v) for v in s.split(",")) for s in hdr["shape"]]
    if exp_board and exp_board != f"{W}x{H}":
        raise SystemExit(f"FAIL board {W}x{H} != expected {exp_board}")
    if exp_shape:
        want = sorted(tuple(int(v) for v in s.split(",")) for s in exp_shape.split(";"))
        if sorted(orientations(want)) != sorted(orientations(shape)):
            raise SystemExit("FAIL shape differs from expected")
    kind = hdr["kind"][0]
    budget = int(hdr["budget"][0])
    if exp_kind is not None and kind != exp_kind:
        raise SystemExit(f"FAIL kind {kind} != expected {exp_kind}")
    if exp_budget is not None and budget != exp_budget:
        raise SystemExit(f"FAIL budget {budget} != expected {exp_budget}")
    if exp_opening is not None and [int(v) for v in hdr.get("opening", [])] != exp_opening:
        raise SystemExit(f"FAIL opening {hdr.get('opening', [])} != expected {exp_opening}")
    UNL = budget < 0
    d0 = 10 ** 9 if UNL else budget
    root = int(hdr["root"][0])
    opening = [int(v) for v in hdr.get("opening", [])]
    PLS = placements(shape, W, H)
    ALL = (1 << (W * H)) - 1
    cell_pls = [[] for _ in range(W * H)]
    for p in PLS:
        for c in range(W * H):
            if p >> c & 1:
                cell_pls[c].append(p)

    def completed(M):
        return any(p & M == p for p in PLS)

    def bit(c):
        if not (0 <= c < W * H):
            raise ValueError(f"cell {c} off board")
        return 1 << c

    M = B = 0
    for i, c in enumerate(opening):
        if (M | B) >> c & 1:
            raise SystemExit("FAIL opening repeats a cell")
        if i % 2 == 0:
            M |= bit(c)
        else:
            B |= bit(c)
    if completed(M):
        raise SystemExit("FAIL opening already contains a Maker copy")
    stats = {"states": 0, "maxdepth": 0}
    NC = W * H
    DB = 32  # bits for the budget in a memo key (unlimited budget is stored as 2**31)

    def memo(fn):
        cache = {}

        def wrapped(nid, M, B, d):
            key = (((nid << NC | M) << NC | B) << DB) | min(d, 1 << 31)
            r = cache.get(key, cache)  # the dict itself is the miss sentinel
            if r is cache:
                r = fn(nid, M, B, d)
                cache[key] = r
                if stats["states"] & 0xFFF == 0:
                    check_limits()
            return r
        return wrapped

    def node(nid):
        line = nodes.get(nid)
        return None if line is None else line.split()

    def relevant(M, B, d):
        """free cells lying in a live placement (no Breaker cell) with at most d free cells"""
        free = ALL & ~(M | B)
        R = 0
        for p in PLS:
            if p & B == 0:
                f = p & free
                if popcount(f) <= d:
                    R |= f
        return R

    # ---------------- Maker-win certificates ----------------
    @memo
    def vM(nid, M, B, d):
        stats["states"] += 1
        t = node(nid)
        if t is None or t[0] != "M":
            raise ValueError(f"node {nid}: expected M node")
        if d < 1:
            raise ValueError(f"node {nid}: Maker move budget exhausted")
        c = int(t[2])
        if (M | B) >> c & 1:
            raise ValueError(f"node {nid}: cell {c} not free")
        M2 = M | bit(c)
        if t[3] == "WIN":
            for p in PLS:
                if p & M2 == p:
                    return p | bit(c)
            raise ValueError(f"node {nid}: WIN claimed but no copy owned by Maker")
        return bit(c) | vB(int(t[3]), M2, B, d - 1 if not UNL else d)

    @memo
    def vB(nid, M, B, d):
        stats["states"] += 1
        t = node(nid)
        if t is None or t[0] != "B":
            raise ValueError(f"node {nid}: expected B node")
        free = ALL & ~(M | B)
        if free == 0:
            raise ValueError(f"node {nid}: board full, Maker has not won")
        env = 0
        dflt = None
        if t[2] != "-":
            dflt = vM(int(t[2]), M, B, d)
            env |= dflt
        explicit = 0
        for item in t[3:]:
            a, b = item.split(":")
            c = int(a)
            if not free >> c & 1:
                raise ValueError(f"node {nid}: explicit reply {c} not free")
            explicit |= bit(c)
            env |= vM(int(b), M, B | bit(c), d)
        uncovered = free & ~explicit
        if uncovered:
            if dflt is None:
                raise ValueError(f"node {nid}: replies without a child and no default")
            if uncovered & dflt:
                raise ValueError(f"node {nid}: reply inside the default subtree's envelope has no explicit child")
        return env

    # ---------------- Breaker-win certificates ----------------
    @memo
    def vm(nid, M, B, d):  # Maker to move; Breaker must prevent a copy within d Maker moves
        stats["states"] += 1
        if completed(M):
            raise ValueError(f"node {nid}: Maker has completed a copy")
        if d == 0:
            return True
        t = node(nid)
        if t is None:
            raise ValueError(f"node {nid} missing")
        free = ALL & ~(M | B)
        if t[0] == "P":
            cells = [int(v) for v in t[2:]]
            if len(cells) % 2:
                raise ValueError(f"node {nid}: odd pairing list")
            used = 0
            pairs = []
            for i in range(0, len(cells), 2):
                u, v = cells[i], cells[i + 1]
                pm = bit(u) | bit(v)
                if u == v or pm & ~free or pm & used:
                    raise ValueError(f"node {nid}: bad pair {u},{v}")
                used |= pm
                pairs.append(pm)
            for p in PLS:
                if p & B == 0 and popcount(p & free) <= d:
                    if not any(pm & p == pm for pm in pairs):
                        raise ValueError(f"node {nid}: live placement {p:x} contains no pair")
            return True
        if t[0] != "m":
            raise ValueError(f"node {nid}: expected m or P node")
        R = relevant(M, B, d)
        kids = {}
        for item in t[3:]:
            a, b = item.split(":")
            kids[int(a)] = int(b)
        nd = d if UNL else d - 1
        for c in range(W * H):
            if R >> c & 1:
                if c not in kids:
                    raise ValueError(f"node {nid}: relevant Maker move {c} has no child")
        for c, ch in kids.items():
            if not free >> c & 1:
                raise ValueError(f"node {nid}: child for non-free cell {c}")
            vb(ch, M | bit(c), B, nd)
        if free & ~R:
            if t[2] == "-":
                raise ValueError(f"node {nid}: irrelevant Maker moves exist but no pass child")
            vb(int(t[2]), M, B, nd)
        return True

    @memo
    def vb(nid, M, B, d):  # Breaker to move
        stats["states"] += 1
        if completed(M):
            raise ValueError(f"node {nid}: Maker has completed a copy")
        t = node(nid)
        if t is None:
            raise ValueError(f"node {nid} missing")
        if t[0] == "Z":
            if d != 0:
                raise ValueError(f"node {nid}: Z leaf with budget {d}")
            return True
        if t[0] == "D":
            if relevant(M, B, d) != 0:
                raise ValueError(f"node {nid}: D leaf but a live placement can still be completed")
            return True
        if t[0] != "b":
            raise ValueError(f"node {nid}: expected b/Z/D node")
        c = int(t[2])
        if (M | B) >> c & 1:
            raise ValueError(f"node {nid}: Breaker cell {c} not free")
        if not relevant(M, B, d) >> c & 1:
            raise ValueError(f"node {nid}: Breaker move {c} is not relevant (rule B-rel)")
        return vm(int(t[3]), M, B | bit(c), d)

    try:
        bto = len(opening) % 2 == 1  # Breaker to move at the root
        if kind == "makerwin":
            env = vB(root, M, B, d0) if bto else vM(root, M, B, d0)
            print(f"PASS makerwin board={W}x{H} shape={len(shape)} cells budget={'unlimited' if UNL else budget} "
                  f"opening={opening} cert_nodes={len(nodes)} checked_states={stats['states']} envelope_cells={popcount(env)}")
        elif kind == "breakerwin":
            vb(root, M, B, d0) if bto else vm(root, M, B, d0)
            print(f"PASS breakerwin board={W}x{H} shape={len(shape)} cells budget={'unlimited' if UNL else budget} "
                  f"opening={opening} cert_nodes={len(nodes)} checked_states={stats['states']}")
        else:
            raise ValueError("unknown kind")
    except ValueError as e:
        print("FAIL", e)
        sys.exit(1)


if __name__ == "__main__":
    main()
