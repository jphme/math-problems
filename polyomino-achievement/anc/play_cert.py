"""Concrete-play test of a Maker-win certificate: Maker follows the certificate as a
strategy on the real board, Breaker plays real moves (random, greedy-blocking, or
exhaustive over all replies up to a state limit). Unlike check_cert.py this does
not use the envelope argument; it plays actual games and checks that Maker owns a
real copy at the end. A replies outside the envelope moves the pointer to the
default child while the real board keeps the Breaker cell.

usage: uv run python play_cert.py CERT [--games 2000] [--exhaustive LIMIT] [--seed 1]
"""
import random
import sys

from check_cert import placements


def load(path):
    nodes, hdr = {}, {}
    for line in open(path):
        t = line.split()
        if not t or t[0].startswith("#"):
            continue
        if t[0] in ("board", "kind", "budget", "root", "end", "shape", "opening"):
            hdr[t[0]] = t[1:]
        else:
            nodes[int(t[1])] = t
    return nodes, hdr


def main():
    path = sys.argv[1]
    args = sys.argv[2:]
    games = int(args[args.index("--games") + 1]) if "--games" in args else 2000
    exh = int(args[args.index("--exhaustive") + 1]) if "--exhaustive" in args else 0
    seed = int(args[args.index("--seed") + 1]) if "--seed" in args else 1
    nodes, hdr = load(path)
    assert hdr["kind"][0] == "makerwin"
    W, H = int(hdr["board"][0]), int(hdr["board"][1])
    shape = [tuple(int(v) for v in s.split(",")) for s in hdr["shape"]]
    budget = int(hdr["budget"][0])
    PLS = placements(shape, W, H)
    NC = W * H
    opening = [int(v) for v in hdr.get("opening", [])]
    root = int(hdr["root"][0])

    def maker_step(nid, M, B):
        """At Maker-to-move node nid: return (cell, next B-node id or 'WIN')."""
        t = nodes[nid]
        assert t[0] == "M"
        return int(t[2]), t[3]

    def breaker_child(nid, c):
        t = nodes[nid]
        assert t[0] == "B"
        for item in t[3:]:
            a, b = item.split(":")
            if int(a) == c:
                return int(b)
        assert t[2] != "-", "no default child"
        return int(t[2])

    def won(M):
        return any(p & M == p for p in PLS)

    rng = random.Random(seed)

    def play(policy):
        M = B = 0
        for i, c in enumerate(opening):
            if i % 2 == 0:
                M |= 1 << c
            else:
                B |= 1 << c
        nid = root
        moves = 0
        while True:
            c, nxt = maker_step(nid, M, B)
            if (M | B) >> c & 1:
                return False, f"Maker cell {c} occupied in real play"
            M |= 1 << c
            moves += 1
            if nxt == "WIN":
                return (won(M), "no real copy" if not won(M) else moves)
            if budget >= 0 and moves >= budget:
                return False, "budget exhausted"
            free = [x for x in range(NC) if not (M | B) >> x & 1]
            if not free:
                return False, "board full"
            r = policy(M, B, free)
            B |= 1 << r
            nid = breaker_child(int(nxt), r)

    def pol_random(M, B, free):
        return rng.choice(free)

    def pol_greedy(M, B, free):
        best, bs = None, -1
        for x in free:
            s = 0
            for p in PLS:
                if p >> x & 1 and p & B == 0:
                    s += 4 ** bin(p & M).count("1")
            s += rng.random()
            if s > bs:
                bs, best = s, x
        return best

    worst = 0
    for g in range(games):
        ok, info = play(pol_random if g % 2 else pol_greedy)
        if not ok:
            print("FAIL game", g, info)
            sys.exit(1)
        worst = max(worst, info)
    print(f"PASS {games} concrete games (half random, half greedy Breaker); max Maker moves {worst}")
    if exh:
        # exhaustive over all real Breaker replies, memo on (node, M, B)
        seen = set()
        count = [0]
        worst = [0]

        def rec(nid, M, B, moves):
            key = (nid, M, B)
            if key in seen:
                return
            seen.add(key)
            count[0] += 1
            if count[0] > exh:
                raise OverflowError
            c, nxt = maker_step(nid, M, B)
            assert not (M | B) >> c & 1, "occupied"
            M2 = M | 1 << c
            if nxt == "WIN":
                assert won(M2), "no real copy"
                worst[0] = max(worst[0], moves + 1)
                return
            assert budget < 0 or moves + 1 < budget
            free = [x for x in range(NC) if not (M2 | B) >> x & 1]
            assert free
            for r in free:
                rec(breaker_child(int(nxt), r), M2, B | 1 << r, moves + 1)

        M0 = B0 = 0
        for i, c in enumerate(opening):
            if i % 2 == 0:
                M0 |= 1 << c
            else:
                B0 |= 1 << c
        try:
            rec(root, M0, B0, 0)
            print(f"PASS exhaustive concrete replay: {count[0]} real states, worst {worst[0]} Maker moves")
        except OverflowError:
            print(f"exhaustive replay stopped at {exh} states (no failure found)")


if __name__ == "__main__":
    main()
