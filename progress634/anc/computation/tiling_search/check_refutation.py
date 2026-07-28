#!/usr/bin/env python3
"""Independent checker for `erdos634-refutation-v1` refutation certificates.

This program was written solely against `CERT_SPEC.md` (the normative
specification) and shares no code with `searcher2.py`, `searcher.py`,
`verify_tiling.py` or `independent/erdos634_exact_search.py`.  Standard library
only.  Every geometric and arithmetic decision is exact: all coordinates live in
Q(sqrt(D)) and are represented by integer triples, so no floating point value is
ever computed (the module imports no `math`, no `decimal`, no `float`).

Usage
-----
    uv run python check_refutation.py CERT.jsonl.gz [--allow-test-instance] [--progress]

Output
------
Exit status 0 and a final line

    ACCEPT <instance> nodes=<n> sha256=<hash>

iff every obligation of CERT_SPEC.md section 5 holds.  Otherwise exit status 1
and a single line

    REJECT: <first failure, with node id and reason>

There is no third outcome: any unsupported case, internal inconsistency or
exception is reported as REJECT.

Strictness choices for the places where CERT_SPEC.md leaves room (the stricter
reading is always taken, i.e. the one that rejects more certificates):

  S1  A node's JSON object may carry no keys beyond those the spec lists for its
      status; unknown keys are a rejection (the checker refuses to ignore data
      whose meaning it does not know).  Likewise for the header and for
      candidate entries.
  S2  `wedge` prunes are accepted only at *convex* vertices.  The wedge lemma of
      section 6 is stated for convex boundary vertices; at a reflex vertex a tile
      may meet the vertex with the interior of an edge, contributing a straight
      angle, so "not a sum of tile angles" would not imply untileability.
  S3  Polygon simplicity is read strictly: two non-adjacent edges may not even
      touch, and no vertex may lie on a non-adjacent edge.
  S4  The wedge enumeration is not cut off at the corner angle but at pi: every
      multiset of tile angles whose running total stays below pi is enumerated,
      which is exhaustive for any convex corner angle.
  S5  The tile triple must equal the published triple of the instance exactly
      (as an ordered triple), and the instance's defining angle relation is
      verified exactly, not just its algebraic shadow.
  S6  area(target)/area(tile) must equal the tile count published for the
      instance (33 for N33, 21 for N21).

Note on obligation 8's boundary support: what is verified is the property the
component-induction lemma of section 6 needs -- every child edge lies in the
union of the region boundary and the placed tile's boundary, hence meets the
interior of the residual region nowhere, hence cannot subdivide it.  Containment
in one single closed edge is *not* required and would be wrong to require: a
child edge may run straight through the point where a region edge and a collinear
tile edge meet.  That happens in the shipped certificates, e.g. N21 node 4, whose
child edge from (7, sqrt15) to (6, 0) is exactly the tile edge
(13/2, sqrt15/2)-(7, sqrt15) followed by the collinear region edge
(13/2, sqrt15/2)-(6, 0).  Coverage is therefore decided by exact one-dimensional
interval arithmetic on the child edge's supporting line.  Artificial chords are
still rejected: such a chord is either not collinear with any support edge, or the
covering intervals leave a gap.
"""

import argparse
import gzip
import hashlib
import json
import sys
from fractions import Fraction

# ---------------------------------------------------------------------------
# rejection
# ---------------------------------------------------------------------------


class Reject(Exception):
    """Any violated obligation, malformed input or unsupported case."""


# ---------------------------------------------------------------------------
# integer helpers (no `math`: gcd and integer square root are implemented here)
# ---------------------------------------------------------------------------


def igcd(a, b):
    if a < 0:
        a = -a
    if b < 0:
        b = -b
    while b:
        a, b = b, a % b
    return a


def isqrt_floor(n):
    """floor(sqrt(n)) for n >= 0, exact integer Newton iteration."""
    if n < 0:
        raise Reject("internal: isqrt of a negative integer")
    if n == 0:
        return 0
    x = 1 << ((n.bit_length() + 1) // 2)
    while True:
        y = (x + n // x) >> 1
        if y >= x:
            return x
        x = y


def exact_int_sqrt(n):
    """Exact square root of a nonnegative integer, or None."""
    r = isqrt_floor(n)
    return r if r * r == n else None


def exact_rat_sqrt(fr):
    """Exact square root of a nonnegative Fraction, or None."""
    if fr < 0:
        return None
    p = exact_int_sqrt(fr.numerator)
    q = exact_int_sqrt(fr.denominator)
    if p is None or q is None:
        return None
    return Fraction(p, q)


# ---------------------------------------------------------------------------
# exact arithmetic in Q(sqrt(D))
#
# A field element is a triple of ints (a, b, d) with d > 0 denoting
# (a + b*sqrt(D)) / d.  The representation is not required to be reduced;
# `_norm` keeps the integers from growing without bound.  Because sqrt(D) is
# irrational, the pair (a/d, b/d) of rationals is unique, so equality is a
# component-wise rational equality.
# ---------------------------------------------------------------------------

D = None  # set by set_field()

F0 = (0, 0, 1)
F1 = (1, 0, 1)

_NORM_BITS = 96


def set_field(d):
    global D
    if not isinstance(d, int) or isinstance(d, bool) or d < 2:
        raise Reject("header D must be an integer >= 2")
    if exact_int_sqrt(d) is not None:
        raise Reject("header D is a perfect square; Q(sqrt(D)) would not be a quadratic field")
    D = d


def _norm(a, b, d):
    if d.bit_length() > _NORM_BITS:
        if a == 0 and b == 0:
            return F0
        g = igcd(igcd(a, b), d)
        if g > 1:
            return (a // g, b // g, d // g)
    return (a, b, d)


def fred(u):
    """Fully reduce a field element."""
    a, b, d = u
    if a == 0 and b == 0:
        return F0
    g = igcd(igcd(a, b), d)
    if g > 1:
        return (a // g, b // g, d // g)
    return u


def frat(fr):
    """Embed a Fraction (or int) as a field element."""
    fr = Fraction(fr)
    return (fr.numerator, 0, fr.denominator)


def fsurd(fr):
    """The field element fr*sqrt(D)."""
    fr = Fraction(fr)
    return (0, fr.numerator, fr.denominator)


def fadd(u, v):
    a1, b1, d1 = u
    a2, b2, d2 = v
    if d1 == d2:
        return _norm(a1 + a2, b1 + b2, d1)
    return _norm(a1 * d2 + a2 * d1, b1 * d2 + b2 * d1, d1 * d2)


def fsub(u, v):
    a1, b1, d1 = u
    a2, b2, d2 = v
    if d1 == d2:
        return _norm(a1 - a2, b1 - b2, d1)
    return _norm(a1 * d2 - a2 * d1, b1 * d2 - b2 * d1, d1 * d2)


def fneg(u):
    a, b, d = u
    return (-a, -b, d)


def fmul(u, v):
    a1, b1, d1 = u
    a2, b2, d2 = v
    return _norm(a1 * a2 + D * b1 * b2, a1 * b2 + a2 * b1, d1 * d2)


def fiszero(u):
    return u[0] == 0 and u[1] == 0


def feq(u, v):
    a1, b1, d1 = u
    a2, b2, d2 = v
    return a1 * d2 == a2 * d1 and b1 * d2 == b2 * d1


def fsign(u):
    """Exact sign of (a + b*sqrt(D))/d with d > 0."""
    a, b, _ = u
    if b == 0:
        return (a > 0) - (a < 0)
    if a == 0:
        return (b > 0) - (b < 0)
    if a > 0:
        if b > 0:
            return 1
        l = a * a
        r = D * b * b
        return 1 if l > r else (0 if l == r else -1)
    else:
        if b < 0:
            return -1
        l = a * a
        r = D * b * b
        return -1 if l > r else (0 if l == r else 1)


def finv(u):
    a, b, d = u
    den = a * a - D * b * b
    if den == 0:
        # a^2 = D b^2 with (a,b) != (0,0) would make D a rational square
        raise Reject("internal: division by zero in Q(sqrt(D))")
    na, nb = d * a, -d * b
    if den < 0:
        na, nb, den = -na, -nb, -den
    return fred((na, nb, den))


def fdiv(u, v):
    return fmul(u, finv(v))


def f_is_rational(u):
    return u[1] == 0


def f_to_fraction(u):
    if u[1] != 0:
        raise Reject("internal: field element is not rational")
    return Fraction(u[0], u[2])


def fstr(u):
    a, b, d = fred(u)
    if b == 0:
        return str(Fraction(a, d))
    return "%s+%s*sqrt(%d)" % (Fraction(a, d), Fraction(b, d), D)


# ---------------------------------------------------------------------------
# points and polygons (a point is a pair of field elements)
# ---------------------------------------------------------------------------


def peq(p, q):
    return feq(p[0], q[0]) and feq(p[1], q[1])


def psub(p, q):
    return (fsub(p[0], q[0]), fsub(p[1], q[1]))


def cross3(o, a, b):
    """(a-o) x (b-o)."""
    return fsub(
        fmul(fsub(a[0], o[0]), fsub(b[1], o[1])),
        fmul(fsub(a[1], o[1]), fsub(b[0], o[0])),
    )


def area2(poly):
    """Twice the signed area (positive iff counterclockwise)."""
    s = F0
    n = len(poly)
    for i in range(n):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % n]
        s = fadd(s, fsub(fmul(x1, y2), fmul(x2, y1)))
    return fred(s)


def on_segment(a, b, p):
    """p on segment ab, assuming cross3(a,b,p) == 0."""
    return (
        fsign(fsub(p[0], a[0])) * fsign(fsub(p[0], b[0])) <= 0
        and fsign(fsub(p[1], a[1])) * fsign(fsub(p[1], b[1])) <= 0
    )


def segments_touch(p1, p2, p3, p4):
    """True iff closed segments p1p2 and p3p4 have any common point."""
    d1 = fsign(cross3(p3, p4, p1))
    d2 = fsign(cross3(p3, p4, p2))
    d3 = fsign(cross3(p1, p2, p3))
    d4 = fsign(cross3(p1, p2, p4))
    if ((d1 > 0 > d2) or (d1 < 0 < d2)) and ((d3 > 0 > d4) or (d3 < 0 < d4)):
        return True
    if d1 == 0 and on_segment(p3, p4, p1):
        return True
    if d2 == 0 and on_segment(p3, p4, p2):
        return True
    if d3 == 0 and on_segment(p1, p2, p3):
        return True
    if d4 == 0 and on_segment(p1, p2, p4):
        return True
    return False


def point_in_polygon(p, poly):
    """1 strictly inside, 0 on the boundary, -1 outside.  poly simple."""
    px, py = p
    n = len(poly)
    inside = False
    for i in range(n):
        a = poly[i]
        b = poly[(i + 1) % n]
        c = fsign(cross3(a, b, p))
        if c == 0 and on_segment(a, b, p):
            return 0
        say = fsign(fsub(a[1], py))
        sby = fsign(fsub(b[1], py))
        if say <= 0 < sby:
            if c > 0:
                inside = not inside
        elif sby <= 0 < say:
            if c < 0:
                inside = not inside
    return 1 if inside else -1


def point_in_closed_triangle(p, a, b, c):
    """p in the closed triangle abc (abc counterclockwise)."""
    return (
        fsign(cross3(a, b, p)) >= 0
        and fsign(cross3(b, c, p)) >= 0
        and fsign(cross3(c, a, p)) >= 0
    )


def check_polygon(poly, what):
    """Obligation 3: >= 3 points, no repeats, simple, CCW/positive area, no
    collinear consecutive vertices.  Returns twice the (positive) area."""
    n = len(poly)
    if n < 3:
        raise Reject("%s has fewer than 3 vertices" % what)
    for i in range(n):
        for j in range(i + 1, n):
            if peq(poly[i], poly[j]):
                raise Reject("%s has repeated vertices at positions %d and %d" % (what, i, j))
    for i in range(n):
        c = fsign(cross3(poly[(i - 1) % n], poly[i], poly[(i + 1) % n]))
        if c == 0:
            raise Reject("%s has three consecutive collinear vertices at position %d" % (what, i))
    for i in range(n):
        a1, a2 = poly[i], poly[(i + 1) % n]
        for j in range(i + 1, n):
            if j == i or (j + 1) % n == i or (i + 1) % n == j:
                continue  # adjacent edges: they share exactly one endpoint and
                # are non-collinear (checked above), so they meet only there
            b1, b2 = poly[j], poly[(j + 1) % n]
            if segments_touch(a1, a2, b1, b2):
                raise Reject(
                    "%s is not simple: edge %d and edge %d intersect" % (what, i, j)
                )
    a2v = area2(poly)
    s = fsign(a2v)
    if s == 0:
        raise Reject("%s has zero area" % what)
    if s < 0:
        raise Reject("%s is not counterclockwise (negative signed area)" % what)
    return a2v


# ---------------------------------------------------------------------------
# exact triangulation (ear clipping, with a diagonal-split fallback)
# ---------------------------------------------------------------------------


def _find_collinear(v):
    n = len(v)
    for i in range(n):
        pv = v[(i - 1) % n]
        cu = v[i]
        nx = v[(i + 1) % n]
        if fsign(cross3(pv, cu, nx)) == 0:
            if not on_segment(pv, nx, cu):
                raise Reject("triangulation: degenerate spike vertex (polygon not simple)")
            return i
    return None


def _find_ear(v):
    n = len(v)
    for i in range(n):
        ip = (i - 1) % n
        inx = (i + 1) % n
        a, b, c = v[ip], v[i], v[inx]
        if fsign(cross3(a, b, c)) <= 0:
            continue
        ok = True
        for j in range(n):
            if j in (ip, i, inx):
                continue
            if point_in_closed_triangle(v[j], a, b, c):
                ok = False
                break
        if ok:
            return i
    return None


def _is_diagonal(v, i, j):
    n = len(v)
    p, q = v[i], v[j]
    for k in range(n):
        if k in (i, j):
            continue
        if fsign(cross3(p, q, v[k])) == 0 and on_segment(p, q, v[k]):
            return False
    for k in range(n):
        k2 = (k + 1) % n
        if k in (i, j) or k2 in (i, j):
            continue
        if segments_touch(p, q, v[k], v[k2]):
            return False
    mid = (fdiv(fadd(p[0], q[0]), frat(2)), fdiv(fadd(p[1], q[1]), frat(2)))
    return point_in_polygon(mid, v) == 1


def _find_diagonal(v):
    n = len(v)
    for i in range(n):
        for j in range(i + 2, n):
            if i == 0 and j == n - 1:
                continue
            if _is_diagonal(v, i, j):
                return i, j
    return None


def triangulate(poly):
    """Exact triangulation of a simple counterclockwise polygon into
    counterclockwise triangles with pairwise disjoint interiors whose union is
    the polygon."""
    tris = []
    stack = [list(poly)]
    while stack:
        v = stack.pop()
        while len(v) > 3:
            i = _find_collinear(v)
            if i is not None:
                del v[i]
                continue
            e = _find_ear(v)
            if e is not None:
                n = len(v)
                tris.append((v[(e - 1) % n], v[e], v[(e + 1) % n]))
                del v[e]
                continue
            d = _find_diagonal(v)
            if d is None:
                raise Reject("triangulation failed: no ear and no diagonal (polygon not simple?)")
            i, j = d
            stack.append(v[i : j + 1])
            v = v[j:] + v[: i + 1]
        if len(v) == 3:
            s = fsign(area2(v))
            if s > 0:
                tris.append(tuple(v))
            elif s < 0:
                raise Reject("triangulation produced a clockwise triangle (internal inconsistency)")
    if not tris:
        raise Reject("triangulation produced no triangles")
    return tris


# ---------------------------------------------------------------------------
# exact intersection areas
# ---------------------------------------------------------------------------


def clip_halfplane(poly, a, b):
    """Sutherland-Hodgman: keep the part of `poly` with cross3(a,b,p) >= 0."""
    n = len(poly)
    if n == 0:
        return []
    out = []
    dprev = cross3(a, b, poly[-1])
    sprev = fsign(dprev)
    for i in range(n):
        p = poly[i]
        dcur = cross3(a, b, p)
        scur = fsign(dcur)
        if (sprev > 0 > scur) or (sprev < 0 < scur):
            q = poly[i - 1]
            t = fdiv(dprev, fsub(dprev, dcur))
            out.append(
                (
                    fadd(q[0], fmul(t, fsub(p[0], q[0]))),
                    fadd(q[1], fmul(t, fsub(p[1], q[1]))),
                )
            )
        if scur >= 0:
            out.append(p)
        dprev, sprev = dcur, scur
    return out


def area2_tri_cap_tri(t, c):
    """Twice the area of the intersection of triangle t with triangle c, both
    counterclockwise.  Nonnegative."""
    poly = list(t)
    for k in range(3):
        poly = clip_halfplane(poly, c[k], c[(k + 1) % 3])
        if len(poly) < 3:
            return F0
    a = area2(poly)
    if fsign(a) < 0:
        raise Reject("internal: negative clipped area")
    return a


def area2_tri_cap_tris(t, tris):
    s = F0
    for c in tris:
        a = area2_tri_cap_tri(t, c)
        if not fiszero(a):
            s = fadd(s, a)
    return fred(s)


def area2_tris_cap_tris(ta, tb):
    s = F0
    for t in ta:
        a = area2_tri_cap_tris(t, tb)
        if not fiszero(a):
            s = fadd(s, a)
    return fred(s)


def contained_tri(tri, region, region_tris):
    """Exact containment of a counterclockwise triangle in the region."""
    for p in tri:
        if point_in_polygon(p, region) < 0:
            return False
    return feq(area2_tri_cap_tris(tri, region_tris), area2(tri))


def segment_inside_segment(p, q, a, b):
    """The closed segment pq lies inside the closed segment ab (point set)."""
    if fsign(cross3(a, b, p)) != 0 or fsign(cross3(a, b, q)) != 0:
        return False
    return on_segment(a, b, p) and on_segment(a, b, q)


def segment_covered_by(p, q, support_edges):
    """The closed segment pq is contained, as a point set, in the union of the
    closed segments `support_edges`.

    First the spec-literal test (one single support edge contains pq); then the
    union test, which is needed because a child edge may run through a point
    where a region edge and a collinear tile edge meet (see interpretation note
    I1 in the module docstring).  The union test parameterises the line through
    p, q by t (t = 0 at p, t = 1 at q), keeps every support edge collinear with
    that line, clips its parameter interval to [0, 1] and verifies by an exact
    sweep that the clipped intervals cover [0, 1] with no gap."""
    for a, b in support_edges:
        if segment_inside_segment(p, q, a, b):
            return True
    dx = fsub(q[0], p[0])
    dy = fsub(q[1], p[1])
    l2 = fadd(fmul(dx, dx), fmul(dy, dy))
    if fiszero(l2):
        raise Reject("internal: degenerate child edge")
    ivs = []
    for a, b in support_edges:
        if fsign(cross3(p, q, a)) != 0 or fsign(cross3(p, q, b)) != 0:
            continue
        ta = fdiv(fadd(fmul(fsub(a[0], p[0]), dx), fmul(fsub(a[1], p[1]), dy)), l2)
        tb = fdiv(fadd(fmul(fsub(b[0], p[0]), dx), fmul(fsub(b[1], p[1]), dy)), l2)
        if fsign(fsub(ta, tb)) > 0:
            ta, tb = tb, ta
        if fsign(ta) < 0:
            ta = F0
        if fsign(fsub(tb, F1)) > 0:
            tb = F1
        if fsign(fsub(tb, ta)) > 0:
            ivs.append((ta, tb))
    # insertion sort by interval start (exact comparisons)
    for i in range(1, len(ivs)):
        cur = ivs[i]
        j = i - 1
        while j >= 0 and fsign(fsub(ivs[j][0], cur[0])) > 0:
            ivs[j + 1] = ivs[j]
            j -= 1
        ivs[j + 1] = cur
    reach = F0
    for lo, hi in ivs:
        if fsign(fsub(lo, reach)) > 0:
            return False  # gap
        if fsign(fsub(hi, reach)) > 0:
            reach = hi
        if fsign(fsub(reach, F1)) >= 0:
            return True
    return fsign(fsub(reach, F1)) >= 0


def boundary_support(child, support_edges):
    """Obligation 8, boundary support: every edge of `child` lies in the union of
    the closed edges of the region and of the candidate triangle, so no child
    boundary crosses the interior of the residual region.  Returns the index of
    the first unsupported child edge, or None."""
    n = len(child)
    for i in range(n):
        p = child[i]
        q = child[(i + 1) % n]
        if not segment_covered_by(p, q, support_edges):
            return i
    return None


def contained_poly(poly_tris, poly_area2, region, region_tris):
    for t in poly_tris:
        for p in t:
            if point_in_polygon(p, region) < 0:
                return False
    return feq(area2_tris_cap_tris(poly_tris, region_tris), poly_area2)


# ---------------------------------------------------------------------------
# tile data
# ---------------------------------------------------------------------------


class Tile:
    """Side lengths, angles (as exact (cos, sin) pairs) and area of the tile."""

    def __init__(self, sides):
        self.sides = list(sides)  # Fractions
        for s in self.sides:
            if s <= 0:
                raise Reject("tile side lengths must be positive")
        a, b, c = self.sides
        if a + b <= c or a + c <= b or b + c <= a:
            raise Reject("tile side lengths violate the triangle inequality")
        # angle i is opposite side i
        self.cos = []
        self.sin = []
        for i in range(3):
            si = self.sides[i]
            sj = self.sides[(i + 1) % 3]
            sk = self.sides[(i + 2) % 3]
            co = (sj * sj + sk * sk - si * si) / (2 * sj * sk)
            t = 1 - co * co
            if t <= 0:
                raise Reject("degenerate tile angle")
            w2 = t / D
            w = exact_rat_sqrt(w2)
            if w is None or w <= 0:
                raise Reject(
                    "tile angle %d has sin not of the form w*sqrt(%d) with w rational" % (i + 1, D)
                )
            self.cos.append(frat(co))
            self.sin.append(fsurd(w))
        # adjacent sides of angle i, in ascending index order
        self.adj = []
        for i in range(3):
            js = [j for j in range(3) if j != i]
            self.adj.append((self.sides[js[0]], self.sides[js[1]]))
        # twice the area, computed three ways; all must agree
        areas = []
        for i in range(3):
            sj, sk = self.adj[i]
            areas.append(fmul(frat(sj * sk), self.sin[i]))
        if not (feq(areas[0], areas[1]) and feq(areas[1], areas[2])):
            raise Reject("internal: tile area inconsistent across the three angles")
        self.area2 = fred(areas[0])
        self.min_side2 = frat(min(self.sides) ** 2)

    def rot(self, i, eps, u):
        """Rotate the vector u by eps*theta_i (eps = +1 or -1)."""
        c = self.cos[i]
        s = self.sin[i] if eps > 0 else fneg(self.sin[i])
        return (
            fsub(fmul(c, u[0]), fmul(s, u[1])),
            fadd(fmul(s, u[0]), fmul(c, u[1])),
        )


# ---------------------------------------------------------------------------
# instances (obligation 1) -- all data below is independent of the searcher
# ---------------------------------------------------------------------------


def triangle_standard_position(base, leg0, leg1):
    """Triangle with the longest side `base` from (0,0) to (base,0) and apex
    strictly above the x-axis, |apex-(0,0)| = leg0, |apex-(base,0)| = leg1."""
    if base < leg0 or base < leg1:
        raise Reject("instance target: the base is not the longest side")
    x = (base * base + leg0 * leg0 - leg1 * leg1) / (2 * base)
    y2 = leg0 * leg0 - x * x
    if y2 <= 0:
        raise Reject("instance target: degenerate triangle")
    yr = exact_rat_sqrt(y2)
    if yr is not None:
        apex_y = frat(yr)
    else:
        w = exact_rat_sqrt(y2 / D)
        if w is None:
            raise Reject("instance target apex is not representable in Q(sqrt(%d))" % D)
        apex_y = fsurd(w)
    return [
        (frat(0), frat(0)),
        (frat(base), frat(0)),
        (frat(x), apex_y),
    ]


def rot_compose(tile, reps):
    """Exact (cos, sin) of sum_i reps[i]*theta_i."""
    c, s = F1, F0
    for i, k in enumerate(reps):
        for _ in range(k):
            c, s = (
                fsub(fmul(c, tile.cos[i]), fmul(s, tile.sin[i])),
                fadd(fmul(s, tile.cos[i]), fmul(c, tile.sin[i])),
            )
            c, s = fred(c), fred(s)
    return c, s


def instance_N33(tile_sides):
    # Group 2, (a,b,c) = (5,3,7): c^2 = a^2 + ab + b^2, and the angle opposite c
    # is 2*pi/3.
    a, b, c = tile_sides
    if (a, b, c) != (Fraction(5), Fraction(3), Fraction(7)):
        raise Reject("instance N33: tile triple must be (5, 3, 7)")
    if c * c != a * a + a * b + b * b:
        raise Reject("instance N33: tile triple fails c^2 = a^2 + ab + b^2")
    tile = Tile(tile_sides)
    if not (feq(tile.cos[2], frat(Fraction(-1, 2))) and feq(tile.sin[2], fsurd(Fraction(1, 2)))):
        raise Reject("instance N33: the angle opposite side c is not 2*pi/3")
    target = triangle_standard_position(Fraction(33), Fraction(21), Fraction(21))
    return tile, target, 33


def instance_N21(tile_sides):
    # Group 1, (p,q) = (1,2): Beeson's primitive tile (pq, q^2-p^2, q^2) with
    # 3*alpha + 2*beta = pi, alpha opposite pq and beta opposite q^2-p^2.
    p, q = Fraction(1), Fraction(2)
    want = (p * q, q * q - p * p, q * q)
    if tuple(tile_sides) != want:
        raise Reject(
            "instance N21: tile triple must be (pq, q^2-p^2, q^2) = (%s, %s, %s)" % want
        )
    tile = Tile(tile_sides)
    c, s = rot_compose(tile, (3, 2, 0))
    if not (feq(c, frat(-1)) and fiszero(s)):
        raise Reject("instance N21: tile fails the Group 1 relation 3*alpha + 2*beta = pi")
    target = triangle_standard_position(Fraction(21), Fraction(12), Fraction(12))
    return tile, target, 21


def instance_TEST1(tile_sides):
    """Flag-gated test instance: unit equilateral tile, tall isosceles target
    with base 1 and height sqrt(3) (area = 2 tiles)."""
    if tuple(tile_sides) != (Fraction(1), Fraction(1), Fraction(1)):
        raise Reject("instance TEST1: tile triple must be (1, 1, 1)")
    tile = Tile(tile_sides)
    target = [
        (frat(0), frat(0)),
        (frat(1), frat(0)),
        (frat(Fraction(1, 2)), fsurd(1)),
    ]
    return tile, target, 2


def instance_TEST2(tile_sides):
    """Flag-gated test instance: unit equilateral tile, unit equilateral target
    (tileable by one tile; used only for negative tests)."""
    if tuple(tile_sides) != (Fraction(1), Fraction(1), Fraction(1)):
        raise Reject("instance TEST2: tile triple must be (1, 1, 1)")
    tile = Tile(tile_sides)
    target = [
        (frat(0), frat(0)),
        (frat(1), frat(0)),
        (frat(Fraction(1, 2)), fsurd(Fraction(1, 2))),
    ]
    return tile, target, 1


def instance_TEST3(tile_sides):
    """Flag-gated test instance: unit equilateral tile; a two-lobed target whose
    reflex vertex sits exactly at the apex of the tile placed on the base, so the
    residual region has two components (area 3/2 tiles each)."""
    if tuple(tile_sides) != (Fraction(1), Fraction(1), Fraction(1)):
        raise Reject("instance TEST3: tile triple must be (1, 1, 1)")
    tile = Tile(tile_sides)
    target = [
        (frat(0), frat(0)),
        (frat(1), frat(0)),
        (frat(Fraction(3, 2)), fsurd(1)),
        (frat(Fraction(1, 2)), fsurd(Fraction(1, 2))),
        (frat(Fraction(-1, 2)), fsurd(1)),
    ]
    return tile, target, 4


INSTANCES = {
    "N33": (3, instance_N33, False),
    "N21": (15, instance_N21, False),
    "TEST1": (3, instance_TEST1, True),
    "TEST2": (3, instance_TEST2, True),
    "TEST3": (3, instance_TEST3, True),
}


# ---------------------------------------------------------------------------
# JSON decoding
# ---------------------------------------------------------------------------


def parse_int_token(tok):
    if not isinstance(tok, str) or tok == "":
        raise Reject("malformed integer %r" % (tok,))
    body = tok[1:] if tok[0] == "-" else tok
    if body == "" or not body.isdigit():
        raise Reject("malformed integer %r" % (tok,))
    v = int(tok)
    if str(v) != tok:
        raise Reject("non-canonical integer %r" % (tok,))
    return v


def parse_rational(tok):
    """A rational is 'p/q' or 'p' with gcd(p,q) = 1, q > 0."""
    if not isinstance(tok, str):
        raise Reject("rational must be a string, got %r" % (tok,))
    if "/" in tok:
        parts = tok.split("/")
        if len(parts) != 2:
            raise Reject("malformed rational %r" % (tok,))
        p = parse_int_token(parts[0])
        q = parse_int_token(parts[1])
        if q <= 0:
            raise Reject("rational %r has non-positive denominator" % (tok,))
        if igcd(p, q) != 1:
            raise Reject("rational %r is not in lowest terms" % (tok,))
        return Fraction(p, q)
    return Fraction(parse_int_token(tok))


def parse_coord(obj):
    if not isinstance(obj, list) or len(obj) != 2:
        raise Reject("coordinate must be a 2-element list [x, w], got %r" % (obj,))
    x = parse_rational(obj[0])
    w = parse_rational(obj[1])
    return fadd(frat(x), fsurd(w))


def parse_point(obj):
    if not isinstance(obj, list) or len(obj) != 2:
        raise Reject("point must be a 2-element list [X, Y], got %r" % (obj,))
    return (parse_coord(obj[0]), parse_coord(obj[1]))


def parse_polygon(obj, what):
    if not isinstance(obj, list):
        raise Reject("%s must be a list of points" % what)
    return [parse_point(p) for p in obj]


def require_keys(obj, required, what):
    """Strictness choice S1: exactly these keys, no others."""
    if not isinstance(obj, dict):
        raise Reject("%s must be a JSON object" % what)
    keys = set(obj)
    missing = required - keys
    if missing:
        raise Reject("%s is missing key(s) %s" % (what, ", ".join(sorted(missing))))
    extra = keys - required
    if extra:
        raise Reject("%s has unknown key(s) %s" % (what, ", ".join(sorted(extra))))


def require_index(val, n, what):
    if not isinstance(val, int) or isinstance(val, bool):
        raise Reject("%s must be an integer" % what)
    if not (0 <= val < n):
        raise Reject("%s = %d is out of range 0..%d" % (what, val, n - 1))
    return val


# ---------------------------------------------------------------------------
# prune obligations (obligation 5)
# ---------------------------------------------------------------------------


def corner_dirs(poly, i):
    """(N_c, N_s) = (|a||b| cos, |a||b| sin) of the interior angle at vertex i,
    where a points to the previous and b to the next vertex."""
    n = len(poly)
    v = poly[i]
    a = psub(poly[(i - 1) % n], v)
    b = psub(poly[(i + 1) % n], v)
    nc = fadd(fmul(a[0], b[0]), fmul(a[1], b[1]))
    ns = fsub(fmul(b[0], a[1]), fmul(b[1], a[0]))
    return fred(nc), fred(ns)


def check_budget(region_area2, tile, nid):
    """Claim: area(region)/area(tile) is not a positive integer."""
    r = fdiv(region_area2, tile.area2)
    if f_is_rational(r):
        fr = f_to_fraction(r)
        if fr > 0 and fr.denominator == 1:
            raise Reject(
                "node %d: budget prune is false: area(region)/area(tile) = %s is a positive integer"
                % (nid, fr)
            )


def check_wedge(region, vertex, tile, nid):
    """Claim: the interior angle at `vertex` is not a nonempty sum of tile
    angles.  Enumeration: every multiset of tile angles whose running total
    stays below pi (strictness choice S4); the total of a matching multiset is
    the corner angle < pi, and its partial sums are smaller still, so no
    matching multiset is ever cut off -- the search is exhaustive.  It
    terminates because every summand is at least the smallest tile angle."""
    nc, ns = corner_dirs(region, vertex)
    if fsign(ns) <= 0:
        raise Reject(
            "node %d: wedge prune at vertex %d, which is not convex "
            "(the wedge lemma of CERT_SPEC section 6 covers convex vertices only)" % (nid, vertex)
        )

    counts = [0, 0, 0]

    def matches(c, s):
        # (nc, ns) and (c, s) describe the same angle in (0, pi) iff they are
        # positively parallel
        return fiszero(fsub(fmul(nc, s), fmul(ns, c))) and fsign(
            fadd(fmul(nc, c), fmul(ns, s))
        ) > 0

    def rec(start, c, s):
        for i in range(start, 3):
            c2 = fred(fsub(fmul(c, tile.cos[i]), fmul(s, tile.sin[i])))
            s2 = fred(fadd(fmul(s, tile.cos[i]), fmul(c, tile.sin[i])))
            if fsign(s2) > 0:  # running total still in (0, pi)
                counts[i] += 1
                if matches(c2, s2):
                    return tuple(counts)
                r = rec(i, c2, s2)
                counts[i] -= 1
                if r is not None:
                    return r
            # running total >= pi: no extension can equal a convex angle
        return None

    hit = rec(0, F1, F0)
    if hit is not None:
        raise Reject(
            "node %d: wedge prune at vertex %d is false: the angle equals the tile-angle "
            "combination (n1,n2,n3) = %s" % (nid, vertex, hit)
        )


def check_short_edge(region, edge, tile, nid):
    """Claim: both endpoints of the edge are convex and the edge is strictly
    shorter than every tile side."""
    n = len(region)
    j = (edge + 1) % n
    for v in (edge, j):
        _, ns = corner_dirs(region, v)
        if fsign(ns) <= 0:
            raise Reject(
                "node %d: short_edge prune on edge %d is false: endpoint %d is not convex"
                % (nid, edge, v)
            )
    d = psub(region[j], region[edge])
    len2 = fadd(fmul(d[0], d[0]), fmul(d[1], d[1]))
    if fsign(fsub(len2, tile.min_side2)) >= 0:
        raise Reject(
            "node %d: short_edge prune on edge %d is false: edge length^2 = %s is not less "
            "than the smallest tile side squared = %s"
            % (nid, edge, fstr(len2), fstr(tile.min_side2))
        )


# ---------------------------------------------------------------------------
# branching obligations (obligations 6-9)
# ---------------------------------------------------------------------------


def candidate_list(region, corner, ray, tile, nid):
    """The canonical 12-placement list of CERT_SPEC section 3.3."""
    n = len(region)
    _, ns = corner_dirs(region, corner)
    if fsign(ns) <= 0:
        raise Reject("node %d: branch corner %d is not a convex vertex" % (nid, corner))
    p = region[corner]
    if ray == "succ":
        other = region[(corner + 1) % n]
    elif ray == "pred":
        other = region[(corner - 1) % n]
    else:
        raise Reject("node %d: ray must be \"succ\" or \"pred\", got %r" % (nid, ray))
    e = psub(other, p)
    len2 = fadd(fmul(e[0], e[0]), fmul(e[1], e[1]))
    if not f_is_rational(len2):
        raise Reject(
            "node %d: ray edge at corner %d has non-rational squared length %s"
            % (nid, corner, fstr(len2))
        )
    L = exact_rat_sqrt(f_to_fraction(len2))
    if L is None or L <= 0:
        raise Reject(
            "node %d: ray edge at corner %d has length sqrt(%s), which is not rational"
            % (nid, corner, f_to_fraction(len2))
        )
    invL = frat(1 / L)
    u = (fmul(e[0], invL), fmul(e[1], invL))
    out = []
    for i in range(3):
        sj, sk = tile.adj[i]
        for along, oth in ((sj, sk), (sk, sj)):
            for eps in (1, -1):
                r = tile.rot(i, eps, u)
                q1 = (fadd(p[0], fmul(frat(along), u[0])), fadd(p[1], fmul(frat(along), u[1])))
                q2 = (fadd(p[0], fmul(frat(oth), r[0])), fadd(p[1], fmul(frat(oth), r[1])))
                out.append((p, q1, q2))
    return out


def ccw(tri, nid):
    a = area2(tri)
    s = fsign(a)
    if s == 0:
        raise Reject("node %d: degenerate candidate triangle (zero area)" % nid)
    if s < 0:
        return (tri[0], tri[2], tri[1]), fneg(a)
    return tuple(tri), a


# ---------------------------------------------------------------------------
# main check
# ---------------------------------------------------------------------------

HEADER_KEYS = {"type", "format", "instance", "D", "tile_sides", "target", "config", "node_count"}
NODE_BASE_KEYS = {"type", "id", "region", "status"}
PRUNED_KEYS = NODE_BASE_KEYS | {"prune"}
BRANCHED_KEYS = NODE_BASE_KEYS | {"corner", "ray", "candidates"}
CAND_REJ_KEYS = {"tri", "verdict"}
CAND_EXP_KEYS = {"tri", "verdict", "children", "refuted_index", "refuted_child"}
PRUNE_KINDS = {"budget", "wedge", "short_edge"}


def check_certificate(path, allow_test_instance=False, progress=0, out=sys.stderr):
    # ---- SHA-256 of the certificate file --------------------------------
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        while True:
            chunk = fh.read(1 << 20)
            if not chunk:
                break
            h.update(chunk)
    digest = h.hexdigest()

    with gzip.open(path, "rt", encoding="utf-8") as fh:
        # ---- header (obligations 1, 2) ----------------------------------
        first = fh.readline()
        if not first:
            raise Reject("certificate is empty")
        try:
            hdr = json.loads(first)
        except Exception as exc:
            raise Reject("header is not valid JSON (%s)" % exc)
        require_keys(hdr, HEADER_KEYS, "header")
        if hdr["type"] != "header":
            raise Reject("first line is not a header")
        if hdr["format"] != "erdos634-refutation-v1":
            raise Reject("unknown format %r" % (hdr["format"],))
        instance = hdr["instance"]
        if instance not in INSTANCES:
            raise Reject("unknown instance %r" % (instance,))
        want_D, builder, is_test = INSTANCES[instance]
        if is_test and not allow_test_instance:
            raise Reject(
                "instance %r is a test instance; pass --allow-test-instance to check it" % instance
            )
        if hdr["D"] != want_D:
            raise Reject("instance %s must have D = %d, header says %r" % (instance, want_D, hdr["D"]))
        set_field(hdr["D"])
        ts = hdr["tile_sides"]
        if not isinstance(ts, list) or len(ts) != 3:
            raise Reject("tile_sides must be a list of three rationals")
        tile_sides = [parse_rational(t) for t in ts]
        tile, target, want_tiles = builder(tile_sides)
        cfg = hdr["config"]
        require_keys(cfg, {"prunes"}, "header config")
        prunes = cfg["prunes"]
        if not isinstance(prunes, list) or set(prunes) != PRUNE_KINDS or len(prunes) != 3:
            raise Reject(
                "header config prunes must be exactly the reduced set %s"
                % sorted(PRUNE_KINDS)
            )
        node_count = hdr["node_count"]
        if not isinstance(node_count, int) or isinstance(node_count, bool) or node_count < 1:
            raise Reject("node_count must be a positive integer")
        hdr_target = parse_polygon(hdr["target"], "header target")
        target_area2 = check_polygon(hdr_target, "header target")
        if len(hdr_target) != len(target) or not all(
            peq(a, b) for a, b in zip(hdr_target, target)
        ):
            raise Reject(
                "header target does not equal the independently constructed target of instance %s"
                % instance
            )
        # standard position
        if not (fiszero(hdr_target[0][0]) and fiszero(hdr_target[0][1])):
            raise Reject("header target is not in standard position (first vertex != origin)")
        if not fiszero(hdr_target[1][1]):
            raise Reject("header target is not in standard position (second vertex off the x-axis)")
        if fsign(hdr_target[2][1]) <= 0:
            raise Reject("header target is not in standard position (apex not above the x-axis)")
        # strictness choice S6
        ratio = fdiv(target_area2, tile.area2)
        if not f_is_rational(ratio) or f_to_fraction(ratio) != want_tiles:
            raise Reject(
                "instance %s: area(target)/area(tile) = %s, expected %d"
                % (instance, fstr(ratio), want_tiles)
            )

        # ---- nodes -----------------------------------------------------
        pending = {}  # id -> promised region polygon
        seen = 0
        for line in fh:
            if not line.strip():
                raise Reject("blank line in certificate after node %d" % (seen - 1))
            if seen >= node_count:
                raise Reject("more node lines than node_count = %d" % node_count)
            try:
                nd = json.loads(line)
            except Exception as exc:
                raise Reject("node line %d is not valid JSON (%s)" % (seen + 1, exc))
            check_node(nd, seen, pending, hdr_target, tile, node_count)
            seen += 1
            if progress and seen % progress == 0:
                out.write("... %d/%d nodes, %d promises open\n" % (seen, node_count, len(pending)))
                out.flush()
        if seen != node_count:
            raise Reject("certificate has %d node lines, header says node_count = %d" % (seen, node_count))
        if pending:
            k = min(pending)
            raise Reject("node %d is promised by a refuted_child but never appears" % k)
    return instance, node_count, digest


def check_node(nd, expected_id, pending, hdr_target, tile, node_count):
    if not isinstance(nd, dict):
        raise Reject("node line for id %d is not a JSON object" % expected_id)
    if nd.get("type") != "node":
        raise Reject("line for id %d is not a node record" % expected_id)
    nid = nd.get("id")
    if not isinstance(nid, int) or isinstance(nid, bool):
        raise Reject("node after id %d has a non-integer id" % (expected_id - 1))
    if nid != expected_id:
        raise Reject("node ids are not consecutive: expected id %d, got %d" % (expected_id, nid))
    status = nd.get("status")
    if status == "pruned":
        require_keys(nd, PRUNED_KEYS, "node %d" % nid)
    elif status == "branched":
        require_keys(nd, BRANCHED_KEYS, "node %d" % nid)
    else:
        raise Reject("node %d has unknown status %r" % (nid, status))

    region = parse_polygon(nd["region"], "node %d region" % nid)
    region_area2 = check_polygon(region, "node %d region" % nid)

    # obligations 2 and 4: tree structure and root region
    if nid == 0:
        if 0 in pending:
            raise Reject("node 0 is referenced by a refuted_child")
        if len(region) != len(hdr_target) or not all(
            peq(a, b) for a, b in zip(region, hdr_target)
        ):
            raise Reject("node 0 region does not equal the header target")
    else:
        promised = pending.pop(nid, None)
        if promised is None:
            raise Reject("node %d is not referenced by any earlier refuted_child" % nid)
        if len(promised) != len(region) or not all(peq(a, b) for a, b in zip(promised, region)):
            raise Reject(
                "node %d region differs from the children[refuted_index] polygon that promised it"
                % nid
            )

    if status == "pruned":
        pr = nd["prune"]
        if not isinstance(pr, dict) or "kind" not in pr:
            raise Reject("node %d prune record is malformed" % nid)
        kind = pr["kind"]
        if kind == "budget":
            require_keys(pr, {"kind"}, "node %d prune" % nid)
            check_budget(region_area2, tile, nid)
        elif kind == "wedge":
            require_keys(pr, {"kind", "vertex"}, "node %d prune" % nid)
            v = require_index(pr["vertex"], len(region), "node %d prune vertex" % nid)
            check_wedge(region, v, tile, nid)
        elif kind == "short_edge":
            require_keys(pr, {"kind", "edge"}, "node %d prune" % nid)
            e = require_index(pr["edge"], len(region), "node %d prune edge" % nid)
            check_short_edge(region, e, tile, nid)
        else:
            raise Reject("node %d has unknown prune kind %r" % (nid, kind))
        return

    # ---- branched (obligations 6-9) ------------------------------------
    corner = require_index(nd["corner"], len(region), "node %d corner" % nid)
    cands = nd["candidates"]
    if not isinstance(cands, list) or len(cands) != 12:
        raise Reject(
            "node %d must list exactly 12 candidates, got %s"
            % (nid, len(cands) if isinstance(cands, list) else type(cands).__name__)
        )
    expect = candidate_list(region, corner, nd["ray"], tile, nid)
    region_tris = triangulate(region)

    for ci, ent in enumerate(cands):
        if not isinstance(ent, dict):
            raise Reject("node %d candidate %d is not a JSON object" % (nid, ci))
        verdict = ent.get("verdict")
        if verdict == "rejected":
            require_keys(ent, CAND_REJ_KEYS, "node %d candidate %d" % (nid, ci))
        elif verdict == "expanded":
            require_keys(ent, CAND_EXP_KEYS, "node %d candidate %d" % (nid, ci))
        else:
            raise Reject("node %d candidate %d has unknown verdict %r" % (nid, ci, verdict))
        tri = parse_polygon(ent["tri"], "node %d candidate %d tri" % (nid, ci))
        if len(tri) != 3:
            raise Reject("node %d candidate %d tri must have 3 points" % (nid, ci))
        want = expect[ci]
        if not all(peq(a, b) for a, b in zip(tri, want)):
            raise Reject(
                "node %d candidate %d does not match the canonical placement: expected "
                "[(%s, %s), (%s, %s), (%s, %s)]"
                % (
                    nid,
                    ci,
                    fstr(want[0][0]), fstr(want[0][1]),
                    fstr(want[1][0]), fstr(want[1][1]),
                    fstr(want[2][0]), fstr(want[2][1]),
                )
            )
        tri_ccw, tri_area2 = ccw(tri, nid)
        if not feq(tri_area2, tile.area2):
            raise Reject(
                "node %d candidate %d has area %s, tile area is %s (internal inconsistency)"
                % (nid, ci, fstr(tri_area2), fstr(tile.area2))
            )
        is_contained = contained_tri(tri_ccw, region, region_tris)
        if is_contained and verdict != "expanded":
            raise Reject(
                "node %d candidate %d is contained in the region but is marked %r"
                % (nid, ci, verdict)
            )
        if not is_contained and verdict == "expanded":
            raise Reject(
                "node %d candidate %d is not contained in the region but is marked expanded"
                % (nid, ci)
            )
        if verdict != "expanded":
            continue

        children = ent["children"]
        if not isinstance(children, list):
            raise Reject("node %d candidate %d children must be a list" % (nid, ci))
        if len(children) == 0:
            raise Reject(
                "node %d candidate %d is expanded with zero children" % (nid, ci)
            )
        support_edges = [
            (region[i], region[(i + 1) % len(region)]) for i in range(len(region))
        ] + [(tri_ccw[i], tri_ccw[(i + 1) % 3]) for i in range(3)]
        polys, tri_lists, areas = [], [], []
        for k, ch in enumerate(children):
            what = "node %d candidate %d child %d" % (nid, ci, k)
            poly = parse_polygon(ch, what)
            a2 = check_polygon(poly, what)
            tl = triangulate(poly)
            if not contained_poly(tl, a2, region, region_tris):
                raise Reject("%s is not contained in the region" % what)
            bad = boundary_support(poly, support_edges)
            if bad is not None:
                raise Reject(
                    "%s violates boundary support: its edge %d from (%s, %s) to (%s, %s) is not "
                    "covered by the union of the collinear closed edges of the region and of the "
                    "candidate triangle (artificial chord)"
                    % (
                        what,
                        bad,
                        fstr(poly[bad][0]), fstr(poly[bad][1]),
                        fstr(poly[(bad + 1) % len(poly)][0]), fstr(poly[(bad + 1) % len(poly)][1]),
                    )
                )
            polys.append(poly)
            tri_lists.append(tl)
            areas.append(a2)
        # pairwise interior-disjointness of the tile and all children
        parts = [[tri_ccw]] + tri_lists
        names = ["candidate triangle"] + ["child %d" % k for k in range(len(polys))]
        for i in range(len(parts)):
            for j in range(i + 1, len(parts)):
                ov = area2_tris_cap_tris(parts[i], parts[j])
                if not fiszero(ov):
                    raise Reject(
                        "node %d candidate %d: %s and %s overlap (intersection area 2A = %s)"
                        % (nid, ci, names[i], names[j], fstr(ov))
                    )
        total = tile.area2
        for a2 in areas:
            total = fadd(total, a2)
        if not feq(fred(total), region_area2):
            raise Reject(
                "node %d candidate %d: tile area + children areas (2A = %s) != region area "
                "(2A = %s)" % (nid, ci, fstr(total), fstr(region_area2))
            )
        ridx = require_index(
            ent["refuted_index"], len(polys), "node %d candidate %d refuted_index" % (nid, ci)
        )
        rchild = ent["refuted_child"]
        if not isinstance(rchild, int) or isinstance(rchild, bool):
            raise Reject("node %d candidate %d refuted_child must be an integer" % (nid, ci))
        if rchild <= nid:
            raise Reject(
                "node %d candidate %d refuted_child = %d does not refer to a later node"
                % (nid, ci, rchild)
            )
        if rchild >= node_count:
            raise Reject(
                "node %d candidate %d refuted_child = %d exceeds node_count" % (nid, ci, rchild)
            )
        if rchild in pending:
            raise Reject(
                "node %d candidate %d: node %d is referenced by more than one refuted_child"
                % (nid, ci, rchild)
            )
        pending[rchild] = polys[ridx]


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Independent checker for erdos634-refutation-v1 certificates."
    )
    ap.add_argument("certificate", help="path to CERT.jsonl.gz")
    ap.add_argument(
        "--allow-test-instance",
        action="store_true",
        help="also accept the flag-gated synthetic test instances (TEST1, TEST2)",
    )
    ap.add_argument(
        "--progress",
        type=int,
        default=0,
        metavar="N",
        help="print progress to stderr every N nodes",
    )
    args = ap.parse_args(argv)
    try:
        instance, nodes, digest = check_certificate(
            args.certificate,
            allow_test_instance=args.allow_test_instance,
            progress=args.progress,
        )
    except Reject as exc:
        print("REJECT: %s" % exc)
        return 1
    except RecursionError as exc:
        print("REJECT: recursion limit hit (%s)" % exc)
        return 1
    except Exception as exc:  # any unsupported case or internal error
        print("REJECT: %s: %s" % (type(exc).__name__, exc))
        return 1
    print("ACCEPT %s nodes=%d sha256=%s" % (instance, nodes, digest))
    return 0


if __name__ == "__main__":
    sys.exit(main())
