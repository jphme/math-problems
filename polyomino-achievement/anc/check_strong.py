"""Exhaustive checker for strong-game (maker-maker) strategies written by
`solver --game strong --cert FILE`. The file maps every position reached
(X cells, O cells as hex bitmasks) to X's move. The checker plays X's strategy
against every legal O reply, and verifies that O never completes a copy and that
X completes one within the stated number of X moves. No pruning is used.

usage: uv run python check_strong.py FILE
"""
import gzip
import sys

from check_cert import placements


def main():
    strat, hdr = {}, {}
    path = sys.argv[1]
    fh = gzip.open(path, "rt") if path.endswith(".gz") else open(path)
    for line in fh:
        t = line.split()
        if not t or t[0].startswith("#"):
            continue
        if t[0] == "X":
            strat[(int(t[1], 16), int(t[2], 16))] = int(t[3])
        else:
            hdr[t[0]] = t[1:]
    assert "end" in hdr, "truncated"
    W, H = int(hdr["board"][0]), int(hdr["board"][1])
    shape = [tuple(int(v) for v in s.split(",")) for s in hdr["shape"]]
    budget = int(hdr["budget"][0])
    assert hdr["kind"][0] == "strongwin" and not hdr.get("opening")
    PLS = placements(shape, W, H)
    ALL = (1 << (W * H)) - 1

    def done(S):
        return any(p & S == p for p in PLS)

    seen = set()
    worst = 0
    stack = [(0, 0, 0)]
    while stack:
        X, O, k = stack.pop()
        if (X, O) in seen:
            continue
        seen.add((X, O))
        mv = strat.get((X, O))
        if mv is None:
            sys.exit(f"FAIL no move for position X={X:x} O={O:x}")
        if (X | O) >> mv & 1:
            sys.exit("FAIL move on occupied cell")
        X2 = X | 1 << mv
        if k + 1 > budget:
            sys.exit("FAIL budget exceeded")
        if done(X2):
            worst = max(worst, k + 1)
            continue
        free = ALL & ~(X2 | O)
        if not free:
            sys.exit("FAIL board full (draw)")
        for c in range(W * H):
            if free >> c & 1:
                O2 = O | 1 << c
                if done(O2):
                    sys.exit(f"FAIL O completes a copy first (X={X2:x} O={O2:x})")
                stack.append((X2, O2, k + 1))
    print(f"PASS strongwin board={W}x{H} shape={len(shape)} cells: {len(seen)} X-to-move positions, worst {worst} X moves (budget {budget})")


if __name__ == "__main__":
    main()
