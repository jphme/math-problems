#!/usr/bin/env python3
"""
Separate exact certificate checker for a found tiling.

Reads a result record written by searcher2.py (--json) and re-proves, from the
tile coordinates alone and with an implementation that shares no search code,
that the listed triangles tile the target.  Four exact checks:

  1. every triangle is congruent to the tile (multiset of squared side lengths);
  2. every triangle lies in the target (the target is convex, so vertex
     containment suffices);
  3. the interiors are pairwise disjoint -- proved by clipping each pair
     (Sutherland-Hodgman in exact rational arithmetic) and requiring the
     intersection polygon to have zero area;
  4. the areas sum to the target area.

Together these are a complete proof: the tiles are closed, contained in the
target, pairwise interior-disjoint and of total area equal to the target's, so
their union is a closed full-measure subset of the target, hence the target
itself.  (1) makes them congruent copies of the tile.

    uv run python verify_tiling.py results/N189_tiling.json
    uv run python verify_tiling.py results/N189_tiling.json \
        --expect-corners 3 --expect-sides 36 36 63
    uv run python verify_tiling.py results/x29_N73_trapezoid_tiling.json \
        --expect-ideal-trapezoid 29 15
"""

import argparse
import json
import sys
from fractions import Fraction as Fr

# Coordinates are (x, w) meaning (x, w*sqrt(D)); the metric is
#   |(x,w)|^2 = x^2 + D w^2,   cross((x1,w1),(x2,w2)) = x1 w2 - x2 w1  (times sqrt D)
# so orientation and area comparisons need no square roots.


def load(path):
    rec = json.load(open(path))
    tiles = [[(Fr(v[0]), Fr(v[1])) for v in tri] for tri in rec["tiling"]]
    return rec, tiles


def parse_tile_sides(label):
    """'group1 (p,q)=(1,2) (a,b,c)=(2,3,4) ...' or 'group2 (a,b,c)=(5,3,7) ...'"""
    key = "(a,b,c)=("
    i = label.index(key) + len(key)
    j = label.index(")", i)
    return tuple(int(t) for t in label[i:j].split(","))


def parse_field(label, group):
    if group == 2:
        return 3
    key = "D="
    i = label.index(key) + len(key)
    j = i
    while j < len(label) and (label[j].isdigit()):
        j += 1
    return int(label[i:j])


def parse_target(rec):
    """Target vertices are recorded in the log, not the json; rebuild them from
    the label instead:  '... legs L base B' (Group-1 shapes) is enough only with
    the angle, so we take the target from the record's own vertex list if present
    and otherwise require --target."""
    return None


def area2(poly):
    s = Fr(0)
    n = len(poly)
    for i in range(n):
        x1, w1 = poly[i]
        x2, w2 = poly[(i + 1) % n]
        s += x1 * w2 - x2 * w1
    return s


def sq_len(a, b, D):
    dx = b[0] - a[0]
    dw = b[1] - a[1]
    return dx * dx + D * dw * dw


def clip(poly, a, b):
    """Sutherland-Hodgman: keep the part of poly left of the directed line a->b."""
    out = []
    n = len(poly)
    for i in range(n):
        p = poly[i]
        q = poly[(i + 1) % n]
        sp = (b[0] - a[0]) * (p[1] - a[1]) - (b[1] - a[1]) * (p[0] - a[0])
        sq = (b[0] - a[0]) * (q[1] - a[1]) - (b[1] - a[1]) * (q[0] - a[0])
        if sp >= 0:
            out.append(p)
        if (sp > 0 and sq < 0) or (sp < 0 and sq > 0):
            t = sp / (sp - sq)
            out.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
    return out


def ccw(tri):
    return tri if area2(tri) > 0 else [tri[0], tri[2], tri[1]]


def intersection_area2(t1, t2):
    poly = list(ccw(t1))
    c = ccw(t2)
    for i in range(3):
        poly = clip(poly, c[i], c[(i + 1) % 3])
        if len(poly) < 3:
            return Fr(0)
    return abs(area2(poly))


def parse_args(argv):
    parser = argparse.ArgumentParser(
        description="Independently verify an exact tiling certificate.",
    )
    parser.add_argument("certificate", help="JSON certificate written by searcher2.py")
    parser.add_argument(
        "--expect-corners",
        type=int,
        help="require the reconstructed convex hull to have exactly this many corners",
    )
    parser.add_argument(
        "--expect-sides",
        type=int,
        nargs="+",
        metavar="LENGTH",
        help="require this multiset of integral target side lengths",
    )
    parser.add_argument(
        "--expect-ideal-trapezoid",
        type=int,
        nargs=2,
        metavar=("X", "L"),
        help=(
            "require the hull to be the ideal trapezoid T(X,L): cyclic side "
            "lengths X+L,L,X,L with the unequal sides parallel"
        ),
    )
    args = parser.parse_args(argv)
    if args.expect_corners is not None and args.expect_corners < 3:
        parser.error("--expect-corners must be at least 3")
    if args.expect_sides is not None:
        if any(length <= 0 for length in args.expect_sides):
            parser.error("--expect-sides values must be positive")
        if (
            args.expect_corners is not None
            and len(args.expect_sides) != args.expect_corners
        ):
            parser.error("--expect-sides must list one side per expected corner")
    if args.expect_ideal_trapezoid is not None:
        if any(length <= 0 for length in args.expect_ideal_trapezoid):
            parser.error("--expect-ideal-trapezoid values must be positive")
        if args.expect_corners is not None and args.expect_corners != 4:
            parser.error("--expect-ideal-trapezoid requires four expected corners")
    return args


def main(argv):
    args = parse_args(argv)
    rec, tiles = load(args.certificate)
    label = rec["tile"]
    group = 1 if label.startswith("group1") else 2
    a, b, c = parse_tile_sides(label)
    D = parse_field(label, group)
    N = rec["N"]
    print("record: %s" % rec.get("tag", args.certificate))
    print("tile: (a,b,c) = (%d,%d,%d), branch group %d, field D = %d" % (a, b, c, group, D))
    print("tiles listed: %d, N = %d" % (len(tiles), N))
    assert len(tiles) == N, "tile count != N"

    want = sorted((a * a, b * b, c * c))
    tot = Fr(0)
    for k, tri in enumerate(tiles):
        sides = sorted((sq_len(tri[0], tri[1], D), sq_len(tri[1], tri[2], D),
                        sq_len(tri[2], tri[0], D)))
        assert sides == [Fr(x) for x in want], "tile %d not congruent: %s" % (k, sides)
        ar = area2(tri)
        assert ar != 0, "tile %d degenerate" % k
        tot += abs(ar)
    print("[1/4] all %d triangles congruent to the tile" % N)

    # target: the convex hull of all tile vertices (the target is a triangle, so
    # its three vertices are among the tile vertices)
    pts = sorted({v for tri in tiles for v in tri})
    def hull(ps):
        def half(ps):
            h = []
            for p in ps:
                while len(h) >= 2:
                    o, q = h[-2], h[-1]
                    if (q[0]-o[0])*(p[1]-o[1]) - (q[1]-o[1])*(p[0]-o[0]) <= 0:
                        h.pop()
                    else:
                        break
                h.append(p)
            return h
        lo = half(ps)
        hi = half(list(reversed(ps)))
        return lo[:-1] + hi[:-1]
    H = hull(pts)
    print("[2/4] convex hull of the %d distinct tile vertices has %d corners: %s"
          % (len(pts), len(H), " ".join("(%s,%s)" % p for p in H)))
    assert len(H) >= 3, "the tiles do not span a polygon"
    if args.expect_corners is not None:
        assert len(H) == args.expect_corners, (
            "target has %d hull corners, expected %d"
            % (len(H), args.expect_corners)
        )
    hull_area2 = abs(area2(H))
    m = len(H)
    for tri in tiles:                      # convexity: vertices in hull => tile in hull
        for v in tri:
            for i in range(m):
                p, q = H[i], H[(i + 1) % m]
                s = (q[0]-p[0])*(v[1]-p[1]) - (q[1]-p[1])*(v[0]-p[0])
                assert s >= 0, "tile vertex outside the target polygon"
    # side lengths of the target, for the record
    sides = []
    side_squares = []
    for i in range(m):
        p, q = H[i], H[(i + 1) % m]
        s2 = sq_len(p, q, D)
        side_squares.append(s2)
        r = s2.numerator
        import math
        root = math.isqrt(r) if s2.denominator == 1 else None
        sides.append(str(root) if (root is not None and root * root == r) else "sqrt(%s)" % s2)
    print("      target side lengths: %s" % ", ".join(sides))
    if args.expect_sides is not None:
        want_side_squares = sorted(Fr(length * length) for length in args.expect_sides)
        got_side_squares = sorted(side_squares)
        assert got_side_squares == want_side_squares, (
            "target squared side multiset is %s, expected %s"
            % (got_side_squares, want_side_squares)
        )
        print(
            "      expected hull shape confirmed: %d corners, side multiset {%s}"
            % (len(H), ", ".join(str(length) for length in sorted(args.expect_sides)))
        )
    if args.expect_ideal_trapezoid is not None:
        x, L = args.expect_ideal_trapezoid
        assert len(H) == 4, (
            "target has %d hull corners, but an ideal trapezoid has 4" % len(H)
        )
        expected_cycle = (
            Fr((x + L) ** 2),
            Fr(L ** 2),
            Fr(x ** 2),
            Fr(L ** 2),
        )
        got_cycle = tuple(side_squares)

        def cyclic_equal(got, expected):
            for candidate in (expected, tuple(reversed(expected))):
                for shift in range(len(candidate)):
                    rotated = candidate[shift:] + candidate[:shift]
                    if got == rotated:
                        return True
            return False

        assert cyclic_equal(got_cycle, expected_cycle), (
            "target cyclic squared sides are %s, not those of T(%d,%d): %s"
            % (got_cycle, x, L, expected_cycle)
        )
        long_index = got_cycle.index(Fr((x + L) ** 2))
        short_index = (long_index + 2) % 4

        def edge(i):
            p, q = H[i], H[(i + 1) % 4]
            return q[0] - p[0], q[1] - p[1]

        e_long = edge(long_index)
        e_short = edge(short_index)
        parallel_cross = e_long[0] * e_short[1] - e_long[1] * e_short[0]
        assert parallel_cross == 0, (
            "the sides of lengths %d and %d are not parallel" % (x + L, x)
        )
        expected_diagonal_square = Fr(x * x + x * L + L * L)
        diagonals = (
            sq_len(H[0], H[2], D),
            sq_len(H[1], H[3], D),
        )
        assert diagonals == (
            expected_diagonal_square,
            expected_diagonal_square,
        ), (
            "target diagonal squares are %s, expected (%s,%s)"
            % (
                diagonals,
                expected_diagonal_square,
                expected_diagonal_square,
            )
        )
        print(
            "      expected ideal trapezoid T(%d,%d) confirmed: ordered sides, "
            "parallel bases, and both diagonals" % (x, L)
        )

    bad = 0
    for i in range(N):
        for j in range(i + 1, N):
            if intersection_area2(tiles[i], tiles[j]) != 0:
                bad += 1
                if bad < 5:
                    print("    OVERLAP between tiles %d and %d" % (i, j))
    assert bad == 0, "%d overlapping pairs" % bad
    print("[3/4] all %d pairs have exactly zero intersection area (exact clipping)"
          % (N * (N - 1) // 2))

    assert tot == hull_area2, "areas sum to %s, target is %s" % (tot, hull_area2)
    print("[4/4] areas sum exactly to the target area (%s * sqrt(%d) / 2)"
          % (tot, D))
    print("VERIFIED: the %d triangles tile the target." % N)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
