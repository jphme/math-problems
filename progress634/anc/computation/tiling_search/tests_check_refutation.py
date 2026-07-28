#!/usr/bin/env python3
"""Test suite for `check_refutation.py` (the independent certificate checker).

Run with

    uv run python tests_check_refutation.py

Part 1 unit-tests the exact primitives (field arithmetic, areas, simplicity,
triangulation, intersection areas, point location, the wedge enumeration).
Part 2 builds synthetic certificates by hand for the flag-gated test instances
TEST1/TEST2 of `check_refutation.py` and runs the checker as a subprocess: two
valid certificates must be ACCEPTed, and every mutant must be REJECTed with the
expected reason.

Every value below is written out by hand; nothing is imported from the searcher.
"""

import copy
import gzip
import json
import os
import subprocess
import sys
import tempfile
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import check_refutation as C  # noqa: E402

CHECKER = os.path.join(HERE, "check_refutation.py")

FAILURES = []
CHECKS = [0]


def ok(cond, what):
    CHECKS[0] += 1
    if not cond:
        FAILURES.append(what)
        print("  FAIL  %s" % what)


# ---------------------------------------------------------------------------
# part 1: primitives
# ---------------------------------------------------------------------------


def sqrt_bounds(d, prec=10**40):
    """Independent rational bracket lo < sqrt(d) < hi, without check_refutation."""
    n = d * prec * prec
    # integer square root by bisection (independent of C.isqrt_floor)
    lo, hi = 0, n + 1
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid * mid <= n:
            lo = mid
        else:
            hi = mid
    return Fraction(lo, prec), Fraction(lo + 1, prec)


def test_integer_helpers():
    print("integer helpers")
    for n in list(range(0, 200)) + [10**12, 10**12 + 1, 2**61 - 1, 3**40]:
        r = C.isqrt_floor(n)
        ok(r * r <= n < (r + 1) * (r + 1), "isqrt_floor(%d)" % n)
    ok(C.exact_int_sqrt(49) == 7, "exact_int_sqrt(49)")
    ok(C.exact_int_sqrt(50) is None, "exact_int_sqrt(50)")
    ok(C.exact_rat_sqrt(Fraction(25, 196)) == Fraction(5, 14), "exact_rat_sqrt(25/196)")
    ok(C.exact_rat_sqrt(Fraction(2)) is None, "exact_rat_sqrt(2)")
    ok(C.exact_rat_sqrt(Fraction(675, 4)) is None, "exact_rat_sqrt(675/4)")
    ok(C.igcd(-12, 18) == 6, "igcd(-12,18)")


def test_field():
    print("field arithmetic in Q(sqrt(D))")
    for d in (2, 3, 5, 15):
        C.set_field(d)
        lo, hi = sqrt_bounds(d)
        for a in range(-4, 5):
            for b in range(-4, 5):
                for den in (1, 3, 7):
                    u = (a, b, den)
                    v1 = Fraction(a, den) + Fraction(b, den) * lo
                    v2 = Fraction(a, den) + Fraction(b, den) * hi
                    if (v1 > 0 and v2 > 0) or (v1 < 0 and v2 < 0) or (a == 0 and b == 0):
                        want = 0 if (a == 0 and b == 0) else (1 if v1 > 0 else -1)
                        ok(C.fsign(u) == want, "fsign((%d+%d sqrt%d)/%d)" % (a, b, d, den))
    C.set_field(3)
    one_plus = C.fadd(C.frat(1), C.fsurd(1))
    one_minus = C.fsub(C.frat(1), C.fsurd(1))
    ok(C.feq(C.fmul(one_plus, one_minus), C.frat(-2)), "(1+sqrt3)(1-sqrt3) = -2")
    ok(C.feq(C.fmul(one_plus, C.finv(one_plus)), C.frat(1)), "u * u^-1 = 1")
    ok(C.feq(C.fdiv(C.frat(3), C.fsurd(1)), C.fsurd(1)), "3/sqrt3 = sqrt3")
    ok(C.feq(C.fmul(C.fsurd(1), C.fsurd(1)), C.frat(3)), "sqrt3^2 = 3")
    ok(not C.feq(C.frat(1), C.fsurd(1)), "1 != sqrt3")
    ok(C.fsign(C.fsub(C.frat(Fraction(7, 4)), C.fsurd(1))) == 1, "7/4 > sqrt3")
    ok(C.fsign(C.fsub(C.frat(Fraction(17, 10)), C.fsurd(1))) == -1, "17/10 < sqrt3")
    ok(C.fsign(C.fsub(C.fmul(C.fsurd(1), C.fsurd(1)), C.frat(3))) == 0, "sqrt3^2 - 3 = 0")
    try:
        C.set_field(9)
        ok(False, "set_field rejects perfect squares")
    except C.Reject:
        ok(True, "set_field rejects perfect squares")
    C.set_field(3)


def P(x, w, y, wy):
    return (C.fadd(C.frat(x), C.fsurd(w)), C.fadd(C.frat(y), C.fsurd(wy)))


def test_areas_and_polygons():
    print("areas, simplicity, point location")
    C.set_field(3)
    sq = [P(0, 0, 0, 0), P(1, 0, 0, 0), P(1, 0, 1, 0), P(0, 0, 1, 0)]
    ok(C.feq(C.area2(sq), C.frat(2)), "unit square 2A = 2")
    ok(C.feq(C.check_polygon(sq, "sq"), C.frat(2)), "unit square passes check_polygon")
    ok(C.feq(C.area2(list(reversed(sq))), C.frat(-2)), "reversed square 2A = -2")
    try:
        C.check_polygon(list(reversed(sq)), "cw")
        ok(False, "clockwise polygon rejected")
    except C.Reject as e:
        ok("counterclockwise" in str(e), "clockwise polygon rejected")
    bowtie = [P(0, 0, 0, 0), P(1, 0, 0, 0), P(0, 0, Fraction(1, 2), 0), P(1, 0, Fraction(1, 2), 0)]
    try:
        C.check_polygon(bowtie, "bowtie")
        ok(False, "bowtie rejected as non-simple")
    except C.Reject as e:
        ok("not simple" in str(e), "bowtie rejected as non-simple")
    collin = [P(0, 0, 0, 0), P(1, 0, 0, 0), P(2, 0, 0, 0), P(1, 0, 1, 0)]
    try:
        C.check_polygon(collin, "collinear")
        ok(False, "collinear-consecutive rejected")
    except C.Reject as e:
        ok("collinear" in str(e), "collinear-consecutive rejected")
    dup = [P(0, 0, 0, 0), P(1, 0, 0, 0), P(1, 0, 0, 0), P(0, 0, 1, 0)]
    try:
        C.check_polygon(dup, "dup")
        ok(False, "repeated vertex rejected")
    except C.Reject as e:
        ok("repeated" in str(e), "repeated vertex rejected")
    # point location on the unit square
    ok(C.point_in_polygon(P(Fraction(1, 2), 0, Fraction(1, 2), 0), sq) == 1, "pip inside")
    ok(C.point_in_polygon(P(0, 0, Fraction(1, 2), 0), sq) == 0, "pip on edge")
    ok(C.point_in_polygon(P(1, 0, 1, 0), sq) == 0, "pip on vertex")
    ok(C.point_in_polygon(P(2, 0, Fraction(1, 2), 0), sq) == -1, "pip outside right")
    ok(C.point_in_polygon(P(Fraction(-1, 3), 0, Fraction(1, 2), 0), sq) == -1, "pip outside left")
    ok(C.point_in_polygon(P(0, 1, Fraction(1, 2), 0), sq) == -1,
       "pip outside (irrational x)")
    ok(C.point_in_polygon(P(0, Fraction(1, 2), Fraction(1, 2), 0), sq) == 1,
       "pip inside (irrational x)")


def check_triangulation(poly, name):
    tris = C.triangulate(poly)
    tot = C.F0
    for t in tris:
        ok(C.fsign(C.area2(t)) > 0, "%s: triangle CCW" % name)
        tot = C.fadd(tot, C.area2(t))
    ok(C.feq(tot, C.area2(poly)), "%s: triangle areas sum to polygon area" % name)
    for i in range(len(tris)):
        for j in range(i + 1, len(tris)):
            ok(C.fiszero(C.area2_tri_cap_tri(tris[i], tris[j])),
               "%s: triangles %d,%d interior-disjoint" % (name, i, j))
    for t in tris:
        ok(C.contained_tri(t, poly, tris), "%s: triangle contained in polygon" % name)
    return tris


def test_triangulation():
    print("ear clipping")
    C.set_field(3)
    # L-shape (one reflex vertex)
    L = [P(0, 0, 0, 0), P(2, 0, 0, 0), P(2, 0, 1, 0), P(1, 0, 1, 0), P(1, 0, 2, 0), P(0, 0, 2, 0)]
    check_triangulation(L, "L-shape")
    # dart with an irrational coordinate (the TEST1 child region)
    dart = [P(0, 0, 0, 0), P(Fraction(1, 2), 0, 0, Fraction(1, 2)),
            P(1, 0, 0, 0), P(Fraction(1, 2), 0, 0, 1)]
    check_triangulation(dart, "dart")
    # comb: several reflex vertices
    comb = [P(0, 0, 0, 0), P(6, 0, 0, 0), P(6, 0, 3, 0), P(5, 0, 1, 0), P(4, 0, 3, 0),
            P(3, 0, 1, 0), P(2, 0, 3, 0), P(1, 0, 1, 0), P(0, 0, 3, 0)]
    check_triangulation(comb, "comb")
    # a spiral-ish polygon
    sp = [P(0, 0, 0, 0), P(5, 0, 0, 0), P(5, 0, 5, 0), P(1, 0, 5, 0), P(1, 0, 2, 0),
          P(3, 0, 2, 0), P(3, 0, 4, 0), P(4, 0, 4, 0), P(4, 0, 1, 0), P(0, 0, 1, 0)]
    check_triangulation(sp, "spiral")


def test_intersection_areas():
    print("exact intersection areas")
    C.set_field(3)
    t = lambda *pts: tuple(pts)
    A = t(P(0, 0, 0, 0), P(2, 0, 0, 0), P(0, 0, 2, 0))
    # disjoint
    B = t(P(5, 0, 0, 0), P(6, 0, 0, 0), P(5, 0, 1, 0))
    ok(C.fiszero(C.area2_tri_cap_tri(A, B)), "disjoint triangles: area 0")
    # touching at a single point
    Bp = t(P(2, 0, 0, 0), P(4, 0, 0, 0), P(4, 0, 2, 0))
    ok(C.fiszero(C.area2_tri_cap_tri(A, Bp)), "point-touching triangles: area 0")
    # touching along a segment
    Bs = t(P(0, 0, 0, 0), P(2, 0, 0, 0), P(1, 0, -2, 0))
    ok(C.fiszero(C.area2_tri_cap_tri(A, Bs)), "edge-touching triangles: area 0")
    # containment
    Bin = t(P(Fraction(1, 4), 0, Fraction(1, 4), 0), P(1, 0, Fraction(1, 4), 0),
            P(Fraction(1, 4), 0, 1, 0))
    ok(C.feq(C.area2_tri_cap_tri(Bin, A), C.area2(Bin)), "contained triangle: area preserved")
    # partial overlap: A and the triangle (1,1),(3,1),(1,3) overlap in the
    # triangle (1,1),(1,1)... compute against a square instead
    sq = [P(1, 0, 1, 0), P(3, 0, 1, 0), P(3, 0, 3, 0), P(1, 0, 3, 0)]
    sqt = C.triangulate(sq)
    # A cap square = triangle (1,1),(1,1)->? A is x,y>=0, x+y<=2; square x,y in [1,3]
    # intersection = triangle (1,1),(1,1)? points with x>=1,y>=1,x+y<=2 -> only (1,1)
    ok(C.fiszero(C.area2_tri_cap_tris(A, sqt)), "single-point overlap: area 0")
    A2 = t(P(0, 0, 0, 0), P(4, 0, 0, 0), P(0, 0, 4, 0))
    # A2 cap square = {x,y>=1, x+y<=4} inside [1,3]^2 = triangle (1,1),(3,1),(1,3)
    ok(C.feq(C.area2_tri_cap_tris(A2, sqt), C.frat(4)), "partial overlap: 2A = 4")
    # irrational coordinates: equilateral triangle side 1 inside the TEST1 target
    tgt = [P(0, 0, 0, 0), P(1, 0, 0, 0), P(Fraction(1, 2), 0, 0, 1)]
    tgt_t = C.triangulate(tgt)
    tile = t(P(0, 0, 0, 0), P(1, 0, 0, 0), P(Fraction(1, 2), 0, 0, Fraction(1, 2)))
    ok(C.contained_tri(tile, tgt, tgt_t), "unit tile contained in TEST1 target")
    below = t(P(0, 0, 0, 0), P(1, 0, 0, 0), P(Fraction(1, 2), 0, 0, Fraction(-1, 2)))
    below_ccw, _ = C.ccw(below, 0)
    ok(not C.contained_tri(below_ccw, tgt, tgt_t), "mirrored tile not contained")
    # a triangle whose vertices are all inside but which pokes out of a notch
    dart = [P(0, 0, 0, 0), P(4, 0, 0, 0), P(4, 0, 4, 0), P(2, 0, 1, 0), P(0, 0, 4, 0)]
    dart_t = C.triangulate(dart)
    probe = t(P(1, 0, 2, 0), P(3, 0, 2, 0), P(2, 0, 3, 0))
    ok(C.point_in_polygon(probe[0], dart) == 1 and C.point_in_polygon(probe[1], dart) == 1,
       "notch probe vertices inside")
    ok(not C.contained_tri(probe, dart, dart_t), "triangle spanning a notch is not contained")


def test_tile_and_instances():
    print("tile data and instance construction")
    C.set_field(3)
    tile = C.Tile([Fraction(5), Fraction(3), Fraction(7)])
    ok(C.feq(tile.cos[0], C.frat(Fraction(11, 14))), "(5,3,7): cos theta_1 = 11/14")
    ok(C.feq(tile.sin[0], C.fsurd(Fraction(5, 14))), "(5,3,7): sin theta_1 = 5/14 sqrt3")
    ok(C.feq(tile.cos[2], C.frat(Fraction(-1, 2))), "(5,3,7): cos theta_3 = -1/2")
    ok(C.feq(tile.area2, C.fsurd(Fraction(15, 2))), "(5,3,7): 2A = 15/2 sqrt3")
    c, s = C.rot_compose(tile, (1, 1, 1))
    ok(C.feq(c, C.frat(-1)) and C.fiszero(s), "(5,3,7): angles sum to pi")
    t33, target33, n33 = C.instance_N33([Fraction(5), Fraction(3), Fraction(7)])
    ok(n33 == 33, "N33 tile count 33")
    ok(C.feq(target33[1][0], C.frat(33)), "N33 base 33")
    ok(C.feq(target33[2][0], C.frat(Fraction(33, 2))), "N33 apex x = 33/2")
    ok(C.feq(target33[2][1], C.fsurd(Fraction(15, 2))), "N33 apex y = 15/2 sqrt3")
    ratio = C.fdiv(C.area2(target33), t33.area2)
    ok(C.f_is_rational(ratio) and C.f_to_fraction(ratio) == 33, "N33 area ratio 33")
    C.set_field(15)
    t21, target21, n21 = C.instance_N21([Fraction(2), Fraction(3), Fraction(4)])
    ok(n21 == 21, "N21 tile count 21")
    ok(C.feq(target21[2][1], C.fsurd(Fraction(3, 2))), "N21 apex y = 3/2 sqrt15")
    ratio = C.fdiv(C.area2(target21), t21.area2)
    ok(C.f_is_rational(ratio) and C.f_to_fraction(ratio) == 21, "N21 area ratio 21")
    c, s = C.rot_compose(t21, (3, 2, 0))
    ok(C.feq(c, C.frat(-1)) and C.fiszero(s), "(2,3,4): 3 alpha + 2 beta = pi")
    for bad in ([Fraction(2), Fraction(3), Fraction(5)], [Fraction(1), Fraction(1), Fraction(1)]):
        try:
            C.instance_N21(bad)
            ok(False, "N21 rejects tile %s" % bad)
        except C.Reject:
            ok(True, "N21 rejects tile %s" % bad)
    C.set_field(3)


def test_boundary_support():
    print("boundary support")
    C.set_field(3)
    seg = (P(0, 0, 0, 0), P(4, 0, 0, 0))
    ok(C.segment_inside_segment(P(1, 0, 0, 0), P(3, 0, 0, 0), *seg), "sub-segment supported")
    ok(C.segment_inside_segment(P(4, 0, 0, 0), P(0, 0, 0, 0), *seg), "reversed edge supported")
    ok(not C.segment_inside_segment(P(1, 0, 0, 0), P(5, 0, 0, 0), *seg), "overhanging not supported")
    ok(not C.segment_inside_segment(P(1, 0, 0, 0), P(3, 0, 1, 0), *seg), "skew not supported")
    ok(not C.segment_inside_segment(P(0, 0, 1, 0), P(4, 0, 1, 0), *seg), "parallel not supported")
    # the TEST1 dart: chord from (1/2, sqrt3/2) to (1/2, sqrt3) has no support
    tgt = [P(0, 0, 0, 0), P(1, 0, 0, 0), P(Fraction(1, 2), 0, 0, 1)]
    tile = [P(0, 0, 0, 0), P(1, 0, 0, 0), P(Fraction(1, 2), 0, 0, Fraction(1, 2))]
    sup = [(tgt[i], tgt[(i + 1) % 3]) for i in range(3)] + \
          [(tile[i], tile[(i + 1) % 3]) for i in range(3)]
    piece = [P(Fraction(1, 2), 0, 0, Fraction(1, 2)), P(1, 0, 0, 0), P(Fraction(1, 2), 0, 0, 1)]
    ok(C.boundary_support(piece, sup) is not None, "chord piece unsupported")
    dart = [P(0, 0, 0, 0), P(Fraction(1, 2), 0, 0, Fraction(1, 2)), P(1, 0, 0, 0),
            P(Fraction(1, 2), 0, 0, 1)]
    ok(C.boundary_support(dart, sup) is None, "true residual supported")

    # union coverage: two collinear support edges meeting in a point
    e1 = (P(0, 0, 0, 0), P(2, 0, 0, 0))
    e2 = (P(2, 0, 0, 0), P(5, 0, 0, 0))
    ok(C.segment_covered_by(P(1, 0, 0, 0), P(4, 0, 0, 0), [e1, e2]),
       "edge straddling two collinear support edges is covered")
    ok(not C.segment_covered_by(P(1, 0, 0, 0), P(4, 0, 0, 0), [e1]),
       "single short support edge does not cover")
    gap = (P(3, 0, 0, 0), P(5, 0, 0, 0))
    ok(not C.segment_covered_by(P(1, 0, 0, 0), P(4, 0, 0, 0), [e1, gap]),
       "gap between collinear support edges is caught")
    ok(C.segment_covered_by(P(1, 0, 0, 0), P(4, 0, 0, 0), [e1, gap, e2]),
       "overlapping support edges cover")
    ok(not C.segment_covered_by(P(1, 0, 0, 0), P(4, 0, 1, 0),
                                [e1, e2, (P(0, 0, 1, 0), P(9, 0, 1, 0))]),
       "non-collinear support edges do not cover")

    # the real case from N21 node 4 (hand-entered from the certificate):
    # child edge (7, sqrt15) -> (6, 0) is the tile edge (13/2, sqrt15/2)-(7, sqrt15)
    # followed by the collinear region edge (13/2, sqrt15/2)-(6, 0)
    C.set_field(15)
    region = [P(6, 0, 0, 0), P(21, 0, 0, 0), P(Fraction(21, 2), 0, 0, Fraction(3, 2)),
              P(Fraction(7, 2), 0, 0, Fraction(1, 2)), P(Fraction(13, 2), 0, 0, Fraction(1, 2))]
    tile = [P(Fraction(7, 2), 0, 0, Fraction(1, 2)), P(Fraction(13, 2), 0, 0, Fraction(1, 2)),
            P(7, 0, 0, 1)]
    child = [P(6, 0, 0, 0), P(21, 0, 0, 0), P(Fraction(21, 2), 0, 0, Fraction(3, 2)),
             P(7, 0, 0, 1)]
    sup15 = [(region[i], region[(i + 1) % 5]) for i in range(5)] + \
            [(tile[i], tile[(i + 1) % 3]) for i in range(3)]
    ok(C.boundary_support(child, sup15) is None,
       "N21 node 4 child supported by the tile+region edge union")
    ok(not any(C.segment_inside_segment(child[3], child[0], a, b) for a, b in sup15),
       "N21 node 4 child edge lies in no single support edge")
    # an artificial chord in that same region is still caught
    chord_child = [P(6, 0, 0, 0), P(21, 0, 0, 0), P(7, 0, 0, 1)]
    ok(C.boundary_support(chord_child, sup15) is not None,
       "artificial chord in the N21 region rejected")
    C.set_field(3)


def test_wedge():
    print("wedge enumeration")
    C.set_field(3)
    tile = C.Tile([Fraction(5), Fraction(3), Fraction(7)])

    def wedge_holds(poly, v):
        try:
            C.check_wedge(poly, v, tile, 0)
            return True
        except C.Reject as e:
            return str(e)

    # a corner of exactly theta_3 = 120 degrees must be found (counts (0,0,1))
    tri120 = [P(0, 0, 0, 0), P(1, 0, 0, 0),
              P(Fraction(-1, 2), 0, 0, Fraction(1, 2))]  # angle at origin = 120 deg
    res = wedge_holds(tri120, 0)
    ok(isinstance(res, str) and "(2, 2, 0)" in res,
       "120 deg corner matched (2 theta_1 + 2 theta_2, found before theta_3)")
    # a corner of theta_1 + theta_2 = 60 degrees must be found
    tri60 = [P(0, 0, 0, 0), P(1, 0, 0, 0), P(Fraction(1, 2), 0, 0, Fraction(1, 2))]
    res = wedge_holds(tri60, 0)
    ok(isinstance(res, str) and "(1, 1, 0)" in res, "60 deg corner matched by theta_1+theta_2")
    # a 90 degree corner is not a sum of the (5,3,7) angles
    tri90 = [P(0, 0, 0, 0), P(1, 0, 0, 0), P(0, 0, 1, 0)]
    ok(wedge_holds(tri90, 0) is True, "90 deg corner is no sum of tile angles")
    # 2*theta_1 must be found
    c, s = C.rot_compose(tile, (2, 0, 0))
    tri2a = [P(0, 0, 0, 0), P(1, 0, 0, 0), (c, s)]
    res = wedge_holds(tri2a, 0)
    ok(isinstance(res, str) and "(2, 0, 0)" in res, "2*theta_1 corner matched")
    # reflex corner: rejected as not convex (strictness choice S2)
    dart = [P(0, 0, 0, 0), P(4, 0, 0, 0), P(4, 0, 4, 0), P(2, 0, 1, 0), P(0, 0, 4, 0)]
    res = wedge_holds(dart, 3)
    ok(isinstance(res, str) and "not convex" in res, "reflex wedge vertex rejected")
    # equilateral tile: a 60 degree corner matches, a 32.2 degree corner does not
    tile_eq = C.Tile([Fraction(1), Fraction(1), Fraction(1)])
    Q = [P(0, 0, 0, 0), P(Fraction(1, 2), 0, 0, Fraction(1, 2)), P(1, 0, 0, 0),
         P(Fraction(1, 2), 0, 0, 1)]
    try:
        C.check_wedge(Q, 3, tile_eq, 0)
        ok(True, "TEST1 child apex is no sum of 60 deg angles")
    except C.Reject:
        ok(False, "TEST1 child apex is no sum of 60 deg angles")
    try:
        C.check_wedge(Q, 0, tile_eq, 0)
        ok(True, "TEST1 child origin corner is no sum of 60 deg angles")
    except C.Reject:
        ok(False, "TEST1 child origin corner is no sum of 60 deg angles")


def test_short_edge_and_budget():
    print("short_edge and budget primitives")
    C.set_field(3)
    tile = C.Tile([Fraction(5), Fraction(3), Fraction(7)])
    small = [P(0, 0, 0, 0), P(2, 0, 0, 0), P(1, 0, 2, 0)]  # edge 0 has length 2 < 3
    try:
        C.check_short_edge(small, 0, tile, 0)
        ok(True, "short_edge accepts length 2 < min side 3")
    except C.Reject:
        ok(False, "short_edge accepts length 2 < min side 3")
    big = [P(0, 0, 0, 0), P(3, 0, 0, 0), P(1, 0, 2, 0)]  # length 3, not strictly shorter
    try:
        C.check_short_edge(big, 0, tile, 0)
        ok(False, "short_edge rejects length 3")
    except C.Reject as e:
        ok("not less" in str(e), "short_edge rejects length 3")
    # budget: area 2 tiles -> claim false; area 1.5 tiles -> claim holds
    two = C.fmul(tile.area2, C.frat(2))
    try:
        C.check_budget(two, tile, 7)
        ok(False, "budget rejects an integer ratio")
    except C.Reject as e:
        ok("positive integer" in str(e), "budget rejects an integer ratio")
    try:
        C.check_budget(C.fmul(tile.area2, C.frat(Fraction(3, 2))), tile, 7)
        ok(True, "budget accepts ratio 3/2")
    except C.Reject:
        ok(False, "budget accepts ratio 3/2")
    try:
        C.check_budget(C.frat(1), tile, 7)  # rational area, irrational ratio
        ok(True, "budget accepts an irrational ratio")
    except C.Reject:
        ok(False, "budget accepts an irrational ratio")


# ---------------------------------------------------------------------------
# part 2: synthetic certificates
#
# TEST1: tile = unit equilateral (D = 3); target = triangle (0,0), (1,0),
# (1/2, sqrt3) -- area 2 tiles.  Branching at the origin along the base admits
# exactly the 6 candidates with eps = +1 (all equal to the tile placed on the
# base); the 6 with eps = -1 lie below the x-axis.  The complement of that
# placement is the dart Q = (0,0), (1/2, sqrt3/2), (1,0), (1/2, sqrt3), whose
# apex angle (cos = 11/13) is no sum of 60 degree angles: wedge prune.
# Splitting Q along the diagonal from (1/2, sqrt3/2) to (1/2, sqrt3) gives two
# triangles of area half a tile each: budget prunes.
# ---------------------------------------------------------------------------


def co(x, w=0):
    return [str(Fraction(x)), str(Fraction(w))]


def jp(x, w, y, wy):
    return [co(x, w), co(y, wy)]


A = jp(0, 0, 0, 0)
B = jp(1, 0, 0, 0)
APEX = jp(Fraction(1, 2), 0, 0, 1)
MID = jp(Fraction(1, 2), 0, 0, Fraction(1, 2))
MIDN = jp(Fraction(1, 2), 0, 0, Fraction(-1, 2))

TARGET1 = [A, B, APEX]
TILE_UP = [A, B, MID]
TILE_DOWN = [A, B, MIDN]
QUAD = [A, MID, B, APEX]
PIECE_A = [MID, B, APEX]
PIECE_B = [APEX, A, MID]
TARGET2 = [A, B, MID]  # unit equilateral = TEST2 target


def header(instance, node_count, target, tile_sides=("1", "1", "1"), d=3):
    return {
        "type": "header",
        "format": "erdos634-refutation-v1",
        "instance": instance,
        "D": d,
        "tile_sides": list(tile_sides),
        "target": copy.deepcopy(target),
        "config": {"prunes": ["budget", "wedge", "short_edge"]},
        "node_count": node_count,
    }


def root_node(children, refuted_index, child_ids):
    cands = []
    k = 0
    for ci in range(12):
        if ci % 2 == 0:
            cands.append(
                {
                    "tri": copy.deepcopy(TILE_UP),
                    "verdict": "expanded",
                    "children": copy.deepcopy(children),
                    "refuted_index": refuted_index,
                    "refuted_child": child_ids[k],
                }
            )
            k += 1
        else:
            cands.append({"tri": copy.deepcopy(TILE_DOWN), "verdict": "rejected"})
    return {
        "type": "node",
        "id": 0,
        "region": copy.deepcopy(TARGET1),
        "status": "branched",
        "corner": 0,
        "ray": "succ",
        "candidates": cands,
    }


def cert_v1():
    """Valid: one child per placement, refuted by a wedge prune."""
    recs = [header("TEST1", 7, TARGET1), root_node([QUAD], 0, [1, 2, 3, 4, 5, 6])]
    for i in range(1, 7):
        recs.append(
            {
                "type": "node",
                "id": i,
                "region": copy.deepcopy(QUAD),
                "status": "pruned",
                "prune": {"kind": "wedge", "vertex": 3},
            }
        )
    return recs


def cert_v2():
    """INVALID: the residual dart Q is cut along the artificial interior chord
    from (1/2, sqrt3/2) to (1/2, sqrt3).  Every coverage check of obligation 8
    passes (areas add up, pieces are contained and interior-disjoint), so only
    the boundary-support check can catch it."""
    recs = [
        header("TEST1", 7, TARGET1),
        root_node([PIECE_A, PIECE_B], 1, [1, 2, 3, 4, 5, 6]),
    ]
    for i in range(1, 7):
        recs.append(
            {
                "type": "node",
                "id": i,
                "region": copy.deepcopy(PIECE_B),
                "status": "pruned",
                "prune": {"kind": "budget"},
            }
        )
    return recs


# TEST3: two-lobed target; the tile placed on the base touches the reflex vertex
# (1/2, sqrt3/2), so the residual splits into two genuine components, each of
# area 3/2 tiles (budget prune).  Boundary support holds: every child edge is a
# whole edge of the target or of the tile.
T3_V0 = A
T3_V1 = B
T3_V2 = jp(Fraction(3, 2), 0, 0, 1)
T3_V3 = MID
T3_V4 = jp(Fraction(-1, 2), 0, 0, 1)
TARGET3 = [T3_V0, T3_V1, T3_V2, T3_V3, T3_V4]
LOBE_LEFT = [T3_V0, T3_V3, T3_V4]
LOBE_RIGHT = [T3_V1, T3_V2, T3_V3]


def root_node3(children, refuted_index, child_ids):
    cands = []
    k = 0
    for ci in range(12):
        if ci % 2 == 0:
            cands.append(
                {
                    "tri": copy.deepcopy(TILE_UP),
                    "verdict": "expanded",
                    "children": copy.deepcopy(children),
                    "refuted_index": refuted_index,
                    "refuted_child": child_ids[k],
                }
            )
            k += 1
        else:
            cands.append({"tri": copy.deepcopy(TILE_DOWN), "verdict": "rejected"})
    return {
        "type": "node",
        "id": 0,
        "region": copy.deepcopy(TARGET3),
        "status": "branched",
        "corner": 0,
        "ray": "succ",
        "candidates": cands,
    }


def cert_v3(refuted_index=1):
    """Valid: two children per placement (genuine components), budget prunes."""
    recs = [
        header("TEST3", 7, TARGET3),
        root_node3([LOBE_LEFT, LOBE_RIGHT], refuted_index, [1, 2, 3, 4, 5, 6]),
    ]
    region = LOBE_RIGHT if refuted_index == 1 else LOBE_LEFT
    for i in range(1, 7):
        recs.append(
            {
                "type": "node",
                "id": i,
                "region": copy.deepcopy(region),
                "status": "pruned",
                "prune": {"kind": "budget"},
            }
        )
    return recs


def cert_test2(prune):
    return [
        header("TEST2", 1, TARGET2),
        {"type": "node", "id": 0, "region": copy.deepcopy(TARGET2), "status": "pruned",
         "prune": prune},
    ]


def write_cert(path, recs):
    with gzip.open(path, "wt", encoding="utf-8") as fh:
        for r in recs:
            fh.write(json.dumps(r) + "\n")


def run_checker(recs, extra_args=("--allow-test-instance",)):
    with tempfile.TemporaryDirectory() as td:
        path = os.path.join(td, "cert.jsonl.gz")
        write_cert(path, recs)
        proc = subprocess.run(
            [sys.executable, CHECKER, path] + list(extra_args),
            capture_output=True,
            text=True,
        )
    return proc.returncode, (proc.stdout or "").strip()


def expect_accept(name, recs, extra_args=("--allow-test-instance",)):
    rc, out = run_checker(recs, extra_args)
    CHECKS[0] += 1
    if rc == 0 and out.startswith("ACCEPT"):
        print("  ACCEPT  %-34s %s" % (name, out))
    else:
        FAILURES.append("%s should ACCEPT, got rc=%d %r" % (name, rc, out))
        print("  FAIL    %-34s rc=%d %s" % (name, rc, out))


def expect_reject(name, recs, needle, extra_args=("--allow-test-instance",)):
    rc, out = run_checker(recs, extra_args)
    CHECKS[0] += 1
    if rc != 0 and out.startswith("REJECT") and needle in out:
        print("  REJECT  %-34s %s" % (name, out[:130]))
    else:
        FAILURES.append(
            "%s should REJECT with %r, got rc=%d %r" % (name, needle, rc, out)
        )
        print("  FAIL    %-34s rc=%d %s" % (name, rc, out[:130]))


def test_certificates():
    print("synthetic certificates")
    expect_accept("valid v1 (wedge leaves)", cert_v1())
    expect_accept("valid v3 (two components)", cert_v3(1))
    expect_accept("valid v3 (refuted_index 0)", cert_v3(0))
    expect_reject("artificial interior chord", cert_v2(), "boundary support")
    expect_reject("test instance without flag", cert_v1(), "test instance", extra_args=())

    # --- header level ---
    m = cert_v1()
    m[0]["instance"] = "N99"
    expect_reject("unknown instance", m, "unknown instance")

    m = cert_v1()
    m[0]["format"] = "erdos634-refutation-v2"
    expect_reject("unknown format", m, "unknown format")

    m = cert_v1()
    m[0]["tile_sides"] = ["1", "1", "2"]
    expect_reject("wrong tile triple", m, "tile triple must be")

    m = cert_v1()
    m[0]["D"] = 5
    expect_reject("wrong field D", m, "must have D = 3")

    m = cert_v1()
    m[0]["target"] = [A, B, jp(Fraction(1, 2), 0, 0, 2)]
    m[1]["region"] = m[0]["target"]
    expect_reject("target not the instance target", m, "independently constructed target")

    m = cert_v1()
    m[0]["config"] = {"prunes": ["budget", "wedge"]}
    expect_reject("reduced prune set violated", m, "reduced set")

    m = cert_v1()
    m[0]["extra"] = 1
    expect_reject("unknown header key", m, "unknown key(s) extra")

    m = cert_v1()
    m[0]["node_count"] = 8
    expect_reject("node_count too large", m, "node_count = 8")

    m = cert_v1()
    m.append(copy.deepcopy(m[-1]))
    m[-1]["id"] = 7
    expect_reject("surplus node line", m, "more node lines")

    m = cert_v1()
    m[0]["target"][2][1] = ["0", "2/2"]
    m[1]["region"] = m[0]["target"]
    expect_reject("non-reduced rational", m, "lowest terms")

    # --- structure ---
    m = cert_v1()
    m[1]["region"] = [A, B, jp(Fraction(1, 2), 0, 0, Fraction(1, 2))]
    expect_reject("root region != target", m, "node 0 region does not equal")

    m = cert_v1()
    m[3]["id"] = 5
    expect_reject("id not consecutive", m, "not consecutive")

    m = cert_v1()
    m[1]["candidates"][2]["refuted_child"] = 1
    expect_reject("node referenced twice", m, "more than one refuted_child")

    m = cert_v1()
    m[1]["candidates"][0]["refuted_child"] = 0
    expect_reject("refuted_child not later", m, "later node")

    m = cert_v1()
    m[1]["candidates"][0]["refuted_child"] = 9
    expect_reject("refuted_child beyond count", m, "exceeds node_count")

    m = cert_v1()
    m[2]["prune"]["depth"] = 3
    expect_reject("unknown node key", m, "unknown key(s)")

    m = cert_v1()
    m[2]["region"] = PIECE_A
    expect_reject("promised region mismatch", m, "differs from the children")

    # --- prune witnesses ---
    m = cert_v1()
    m[2]["prune"] = {"kind": "wedge", "vertex": 1}
    expect_reject("wedge at reflex vertex", m, "not convex")

    m = cert_v1()
    m[2]["prune"] = {"kind": "budget"}
    expect_reject("budget claim false", m, "budget prune is false")

    m = cert_v1()
    m[2]["prune"] = {"kind": "short_edge", "edge": 0}
    expect_reject("short_edge claim false", m, "short_edge prune on edge 0 is false")

    m = cert_v1()
    m[2]["prune"] = {"kind": "wedge", "vertex": 9}
    expect_reject("prune vertex out of range", m, "out of range")

    m = cert_v1()
    m[2]["prune"] = {"kind": "boundary_invariant"}
    expect_reject("unknown prune kind", m, "unknown prune kind")

    expect_reject("bogus wedge (60 deg = tile angle)",
                  cert_test2({"kind": "wedge", "vertex": 0}), "wedge prune at vertex 0 is false")
    expect_reject("bogus budget (ratio 1)", cert_test2({"kind": "budget"}),
                  "budget prune is false")
    expect_reject("bogus short_edge (len = min side)",
                  cert_test2({"kind": "short_edge", "edge": 0}), "short_edge prune on edge 0")

    # --- branching and candidates ---
    m = cert_v1()
    m[1]["candidates"] = m[1]["candidates"][:11]
    expect_reject("11 candidates", m, "exactly 12 candidates")

    m = cert_v1()
    m[1]["candidates"][0], m[1]["candidates"][1] = m[1]["candidates"][1], m[1]["candidates"][0]
    expect_reject("candidate order permuted", m, "canonical placement")

    m = cert_v1()
    m[1]["candidates"][0]["tri"] = [A, B, jp(Fraction(1, 3), 0, 0, Fraction(1, 2))]
    expect_reject("candidate tri altered", m, "canonical placement")

    m = cert_v1()
    m[1]["corner"] = 2
    expect_reject("irrational ray edge", m, "not rational")

    m = cert_v1()
    m[1]["ray"] = "next"
    expect_reject("bad ray value", m, "ray must be")

    m = cert_v1()
    m[1]["candidates"][0] = {"tri": TILE_UP, "verdict": "rejected"}
    expect_reject("contained candidate rejected", m, "is contained in the region but is marked")

    m = cert_v1()
    m[1]["candidates"][1] = {
        "tri": TILE_DOWN,
        "verdict": "expanded",
        "children": [QUAD],
        "refuted_index": 0,
        "refuted_child": 6,
    }
    expect_reject("uncontained candidate expanded", m, "not contained in the region but is marked")

    m = cert_v1()
    m[1]["candidates"][0]["children"] = []
    expect_reject("expanded with zero children", m, "zero children")

    # one genuine component dropped: coverage and support hold, areas do not
    m = cert_v3(0)
    m[1]["candidates"][0]["children"] = [copy.deepcopy(LOBE_LEFT)]
    m[1]["candidates"][0]["refuted_index"] = 0
    expect_reject("children areas do not sum", m, "!= region area")

    # a genuine component listed twice: supported, but overlapping
    m = cert_v3(0)
    m[1]["candidates"][0]["children"] = [copy.deepcopy(LOBE_LEFT), copy.deepcopy(LOBE_LEFT),
                                        copy.deepcopy(LOBE_RIGHT)]
    expect_reject("children overlap", m, "overlap")

    m = cert_v1()
    m[1]["candidates"][0]["children"] = [
        [jp(0, 0, 1, 0), jp(1, 0, 1, 0), jp(Fraction(1, 2), 0, 1, 1)]
    ]
    expect_reject("child outside region", m, "not contained in the region")

    m = cert_v3(1)
    m[1]["candidates"][0]["refuted_index"] = 0
    expect_reject("refuted_index mismatch", m, "differs from the children")

    m = cert_v3(1)
    m[1]["candidates"][0]["refuted_index"] = 5
    expect_reject("refuted_index out of range", m, "out of range")

    # the right component further cut along an interior chord: all coverage
    # checks pass (contained, interior-disjoint, areas add up) -- only boundary
    # support catches the artificial subdivision
    m = cert_v3(1)
    edge_mid = jp(Fraction(5, 4), 0, 0, Fraction(1, 2))  # midpoint of T3_V1 T3_V2
    m[1]["candidates"][0]["children"] = [
        copy.deepcopy(LOBE_LEFT),
        [T3_V1, edge_mid, T3_V3],
        [edge_mid, T3_V2, T3_V3],
    ]
    expect_reject("chord inside a component", m, "boundary support")

    m = cert_v1()
    m[1]["candidates"][0]["children"] = [list(reversed(QUAD))]
    expect_reject("child clockwise", m, "not counterclockwise")

    m = cert_v1()
    m[1]["candidates"][0]["children"] = [
        [A, B, jp(Fraction(1, 2), 0, Fraction(1, 2), 0), jp(Fraction(3, 2), 0, Fraction(1, 2), 0)]
    ]
    expect_reject("child not simple", m, "not simple")

    m = cert_v1()
    m[1]["candidates"][0]["children"] = [
        [A, jp(Fraction(1, 4), 0, 0, Fraction(1, 4)), MID, B, APEX]
    ]
    expect_reject("child has collinear vertices", m, "collinear")

    m = cert_v1()
    m[1]["candidates"][0]["verdict"] = "maybe"
    expect_reject("unknown verdict", m, "unknown verdict")

    m = cert_v1()
    m[1]["status"] = "open"
    expect_reject("unknown status", m, "unknown status")

    # branching at a reflex corner of the child region
    m = cert_v1()
    m[2] = {
        "type": "node",
        "id": 1,
        "region": QUAD,
        "status": "branched",
        "corner": 1,
        "ray": "succ",
        "candidates": [{"tri": TILE_UP, "verdict": "rejected"} for _ in range(12)],
    }
    m[0]["node_count"] = 7
    expect_reject("branch corner reflex", m, "not a convex vertex")


def main():
    print("=" * 78)
    print("unit tests")
    print("=" * 78)
    test_integer_helpers()
    test_field()
    test_areas_and_polygons()
    test_triangulation()
    test_intersection_areas()
    test_tile_and_instances()
    test_wedge()
    test_boundary_support()
    test_short_edge_and_budget()
    print("=" * 78)
    print("certificate tests")
    print("=" * 78)
    test_certificates()
    print("=" * 78)
    print("%d checks, %d failures" % (CHECKS[0], len(FAILURES)))
    for f in FAILURES:
        print("  - %s" % f)
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.exit(main())
