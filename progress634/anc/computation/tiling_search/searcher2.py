#!/usr/bin/env python3
"""
searcher2.py -- field-parametrized exact exhaustive tiling searcher for Erdos 634.

Successor to searcher.py (v1, kept frozen: Q(sqrt3) coordinates, 120-degree
tiles, triangle targets only).  Three things are new, each a ROADMAP item:

  * FIELD PARAMETRIZATION (ROADMAP sec.3, package D).  A point is a pair (x, w)
    of rationals meaning (x, w*sqrt(D)) for a global integer D.  Group 2
    (gamma = 2pi/3) is D = 3.  Beeson's Group 1 (3alpha+2beta = pi, tile
    (pq, q^2-p^2, q^2)) is D = 4q^2-p^2.  In both branches every lattice
    direction has rational cosine and sine in sqrt(D)*Q, so the representation
    is closed under every rotation the search performs -- and it is ~4x faster
    than v1's pairs-of-Q(sqrt3) because a point costs two rationals, not four.

  * GENERAL SUBTRACTION (closes v1's documented completeness gap, ROADMAP G1).
    Removing a tile is done as an exact 1-chain operation d(comp) - d(tile):
    split every edge at every vertex, cancel opposite duplicates, then trace
    faces by the most-clockwise rule.  A flush tile edge spanning two or more
    collinear boundary segments -- the configuration v1's uniform splice could
    not represent, and rejected up front -- is handled by construction.

  * INVARIANT PRUNING (ROADMAP sec.3a).  Every component R of the search tree
    must be tiled by exactly n_R = area(R)/area(tile) tiles, so its boundary
    polynomial must satisfy the universal Laurent congruence
    B(dR) = 0 mod 3ab at z = -d/c, and the two +-1 characters must be N-term
    representable: Phi(dR) = M*Delta with |M| <= n_R and M = n_R mod 2, same
    for Phi'.  All three are O(#edges) exact integer tests.  Group 2 only
    (Group 1's analogue is not verified yet -- see invariants.md sec.5).

Verdicts: TILING FOUND (independently re-verified before printing),
EXHAUSTED: NO TILING EXISTS, or UNDECIDED (limit reached).

Pure Python 3 stdlib.  Run with:  uv run python searcher2.py ...
"""

import sys
import time
import json
import argparse
import resource
from fractions import Fraction as Fr
from math import isqrt, gcd, sqrt as _fsqrt

# ru_maxrss is bytes on macOS, kilobytes on Linux
_RSS_DIV = 1 << 20 if sys.platform == "darwin" else 1 << 10


def rss_mb():
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / _RSS_DIV

sys.setrecursionlimit(1_000_000)

# ---------------------------------------------------------------------------
# The field.  A point is (x, w), meaning the plane point (x, w*sqrt(FIELD_D)).
# ---------------------------------------------------------------------------
FIELD_D = 3
_SQRTD = 1.7320508075688772


def set_field(d):
    """Set the global field parameter D (coordinates are (x, w*sqrt(D)))."""
    global FIELD_D, _SQRTD
    d = int(d)
    if d <= 0:
        raise ValueError("field parameter D must be positive")
    FIELD_D = d
    _SQRTD = _fsqrt(d)


ZERO = Fr(0)
ONE = Fr(1)


def rational_sqrt(x):
    """sqrt(x) as a Fraction if x >= 0 is a perfect rational square, else None."""
    if x < 0:
        return None
    if x == 0:
        return ZERO
    n, d = x.numerator, x.denominator
    rn = isqrt(n)
    if rn * rn != n:
        return None
    rd = isqrt(d)
    if rd * rd != d:
        return None
    return Fr(rn, rd)


# ---------------------------------------------------------------------------
# Vector helpers.  Points/vectors are 2-tuples of Fraction.
# ---------------------------------------------------------------------------
def padd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def psub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def pscale(a, k):
    return (a[0] * k, a[1] * k)


def pneg(a):
    return (-a[0], -a[1])


def dot(u, v):
    """True Euclidean dot product (a rational)."""
    return u[0] * v[0] + FIELD_D * u[1] * v[1]


def cross2(u, v):
    """True cross product divided by sqrt(D) -- same sign as the cross product."""
    return u[0] * v[1] - u[1] * v[0]


def cross3(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def sgn(x):
    return (x > 0) - (x < 0)


def orient(a, b, c):
    """+1 left turn (CCW), -1 right turn, 0 collinear."""
    return sgn(cross3(a, b, c))


def peq(a, b):
    return a[0] == b[0] and a[1] == b[1]


def norm2(v):
    return v[0] * v[0] + FIELD_D * v[1] * v[1]


class OffLattice(Exception):
    """An edge length is not rational -- the configuration left the lattice."""


def seg_len(a, b):
    """Exact length of [a,b]; raises OffLattice if it is not rational."""
    L = rational_sqrt(norm2(psub(b, a)))
    if L is None or L == 0:
        raise OffLattice("edge length not a positive rational: %r -> %r" % (a, b))
    return L


def unit_dir(a, b):
    e = psub(b, a)
    L = seg_len(a, b)
    return (e[0] / L, e[1] / L)


def rot_ccw(v, cs, sw):
    """Rotate v CCW by the angle with cos = cs, sin = sw*sqrt(D)."""
    return (v[0] * cs - FIELD_D * v[1] * sw, v[0] * sw + v[1] * cs)


def to_float(p):
    return (float(p[0]), float(p[1]) * _SQRTD)


def pretty(p):
    if p[1] == 0:
        return "(%s, 0)" % (p[0],)
    return "(%s, %s*sqrt%d)" % (p[0], p[1], FIELD_D)


# ---------------------------------------------------------------------------
# Geometric predicates (all exact)
# ---------------------------------------------------------------------------
def on_segment(p, a, b):
    """p lies on the closed segment [a,b]."""
    if orient(a, b, p) != 0:
        return False
    if dot(psub(p, a), psub(b, a)) < 0:
        return False
    if dot(psub(p, b), psub(a, b)) < 0:
        return False
    return True


def strictly_on_segment(p, a, b):
    return (not peq(p, a)) and (not peq(p, b)) and on_segment(p, a, b)


def seg_proper_cross(a, b, c, d):
    """Open segments (a,b), (c,d) cross transversally.  Collinear overlaps and
    endpoint touchings are NOT proper crossings."""
    d1 = orient(c, d, a)
    d2 = orient(c, d, b)
    d3 = orient(a, b, c)
    d4 = orient(a, b, d)
    return (d1 * d2 < 0) and (d3 * d4 < 0)


def _ray_inside(p, poly):
    """Crossing-number ray cast in +x.  Assumes p is not on the boundary."""
    n = len(poly)
    px, pw = p
    inside = False
    for i in range(n):
        xi, wi = poly[i]
        xj, wj = poly[(i + 1) % n]
        ai = wi > pw
        aj = wj > pw
        if ai != aj:
            t = (pw - wi) / (wj - wi)
            if px < xi + t * (xj - xi):
                inside = not inside
    return inside


def point_in_poly(p, poly):
    """Inside-or-on."""
    n = len(poly)
    for i in range(n):
        if on_segment(p, poly[i], poly[(i + 1) % n]):
            return True
    return _ray_inside(p, poly)


def strictly_inside_poly(p, poly):
    n = len(poly)
    for i in range(n):
        if on_segment(p, poly[i], poly[(i + 1) % n]):
            return False
    return _ray_inside(p, poly)


def strictly_inside_tri(p, a, b, c):
    """Strict interior of the CCW triangle (a,b,c)."""
    return orient(a, b, p) > 0 and orient(b, c, p) > 0 and orient(c, a, p) > 0


def signed_area2(poly):
    """Twice the signed area divided by sqrt(D) (a rational; >0 for CCW)."""
    s = ZERO
    n = len(poly)
    for i in range(n):
        x1, w1 = poly[i]
        x2, w2 = poly[(i + 1) % n]
        s += x1 * w2 - x2 * w1
    return s


# ---------------------------------------------------------------------------
# The universal Laurent boundary invariant (Group 2), used for pruning
# ---------------------------------------------------------------------------
class BoundaryInvariant:
    """Necessary conditions on a component R that must carry exactly n_R tiles.

    Directions in a Group-2 tiling are theta = j*pi/3 + m*alpha; the invariant
    is B(PQ) = |PQ| * (-1)^j z^m, additive, and every tile contributes a unit
    multiple of d+cz or d+c/z (invariants.md sec.1).  Hence for a component:

        B(dR) in (d+cz, d+c/z)      <=>   B(dR)|_{z=-d/c} = 0  (mod 3ab)
        B(dR)|_{z=1}  = M *(a-b+c),  |M|  <= n_R,  M  = n_R (mod 2)
        B(dR)|_{z=-1} = M'*(a-b-c),  |M'| <= n_R,  M' = n_R (mod 2)

    The two character conditions are the N-term representability refinement
    (ROADMAP G5) specialized to z = +-1; they are not implied by membership.
    """

    def __init__(self, a, b, c, cos_a, sin_a, mcap):
        self.a, self.b, self.c = a, b, c
        self.mod = 3 * a * b
        d = a - b
        self.d = d
        if gcd(c, self.mod) != 1 or gcd(abs(d), self.mod) != 1:
            raise ValueError("invariant unavailable: c or d not invertible mod 3ab")
        cinv = pow(c, -1, self.mod)
        self.zval = (-d * cinv) % self.mod
        self.zinv = pow(self.zval, -1, self.mod)
        self.delta = a - b + c
        self.deltap = a - b - c
        if self.delta == 0 or self.deltap == 0:
            raise ValueError("degenerate character value")
        self.mcap = mcap
        self._zpow = {}
        # direction table: unit vector -> (j, m) for theta = j*pi/3 + m*alpha
        base = [(Fr(1), Fr(0)), (Fr(1, 2), Fr(1, 2)), (Fr(-1, 2), Fr(1, 2)),
                (Fr(-1), Fr(0)), (Fr(-1, 2), Fr(-1, 2)), (Fr(1, 2), Fr(-1, 2))]
        for u in base:
            if dot(u, u) != 1:
                raise ValueError("base direction not unit -- field is not D=3")
        table = {}
        for j, u in enumerate(base):
            v = u
            for m in range(0, mcap + 1):
                table.setdefault(v, (j, m))
                v = rot_ccw(v, cos_a, sin_a)
            v = u
            for m in range(1, mcap + 1):
                v = rot_ccw(v, cos_a, -sin_a)
                table.setdefault(v, (j, -m))
        self.table = table

    def zpow(self, m):
        r = self._zpow.get(m)
        if r is None:
            r = pow(self.zval, m, self.mod) if m >= 0 else pow(self.zinv, -m, self.mod)
            self._zpow[m] = r
        return r

    def evaluate(self, edir, elen):
        """Return the Laurent coefficients {m: coeff} or None if a direction is
        not on the lattice table."""
        coeff = {}
        get = self.table.get
        for u, L in zip(edir, elen):
            jm = get(u)
            if jm is None:
                return None
            j, m = jm
            v = -L if (j & 1) else L
            if m in coeff:
                coeff[m] += v
            else:
                coeff[m] = v
        return coeff

    def feasible(self, coeff, budget):
        """False => the component provably carries no tiling with `budget` tiles."""
        tot1 = 0
        totm1 = 0
        totz = 0
        for m, v in coeff.items():
            if v.denominator != 1:
                return False          # tile-edge sums are integers
            iv = int(v)
            if iv == 0:
                continue
            tot1 += iv
            totm1 += iv if not (m & 1) else -iv
            totz += iv * self.zpow(m)
        if totz % self.mod:
            return False
        for tot, delta in ((tot1, self.delta), (totm1, self.deltap)):
            if tot % delta:
                return False
            M = abs(tot // delta)
            if M > budget or ((M - budget) & 1):
                return False
        return True

    def report(self, poly):
        """Human-readable root-level evaluation (used by --selftest and startup)."""
        edir, elen = edge_data(poly)
        coeff = self.evaluate(edir, elen)
        if coeff is None:
            return None
        tot1 = sum(coeff.values())
        totm1 = sum((v if not (m & 1) else -v) for m, v in coeff.items())
        totz = sum(int(v) * self.zpow(m) for m, v in coeff.items()) if all(
            v.denominator == 1 for v in coeff.values()) else None
        out = {"coeff": {int(m): str(v) for m, v in sorted(coeff.items())},
               "Phi": str(tot1), "Delta": self.delta,
               "Phi'": str(totm1), "Delta'": self.deltap,
               "M": str(tot1 / self.delta), "M'": str(totm1 / self.deltap),
               "ideal_residue": (totz % self.mod) if totz is not None else None,
               "mod": self.mod}
        return out


# ---------------------------------------------------------------------------
# Tiles
# ---------------------------------------------------------------------------
class Tile:
    __slots__ = ("group", "a", "b", "c", "p", "q", "angles", "tw2",
                 "min_side", "cos_min", "inv", "label")


TILE = None


def _check_angle(cs, sw, name):
    if cs * cs + FIELD_D * sw * sw != 1:
        raise ValueError("cos^2 + D sin^2 != 1 for angle %s" % name)


def setup_tile_group2(a, b, c, mcap=16, want_invariant=True):
    """120-degree tile: c^2 = a^2+ab+b^2, gamma = 2pi/3 opposite c.  D = 3."""
    a, b, c = int(a), int(b), int(c)
    if not (a > 0 and b > 0 and c > 0):
        raise ValueError("tile sides must be positive")
    if c * c != a * a + a * b + b * b:
        raise ValueError("not a 120-degree tile: c^2 != a^2+ab+b^2 for (%d,%d,%d)"
                         % (a, b, c))
    set_field(3)
    t = Tile()
    t.group = 2
    t.a, t.b, t.c = a, b, c
    t.p = t.q = None
    cos_a, sin_a = Fr(a + 2 * b, 2 * c), Fr(a, 2 * c)
    cos_b, sin_b = Fr(2 * a + b, 2 * c), Fr(b, 2 * c)
    cos_g, sin_g = Fr(-1, 2), Fr(1, 2)
    _check_angle(cos_a, sin_a, "alpha")
    _check_angle(cos_b, sin_b, "beta")
    _check_angle(cos_g, sin_g, "gamma")
    # angle -> the two adjacent sides (alpha is between b and c, etc.)
    t.angles = [(cos_a, sin_a, b, c), (cos_b, sin_b, a, c), (cos_g, sin_g, a, b)]
    t.tw2 = Fr(a * b, 2)                    # = a*b*sin_g, in signed_area2 units
    t.min_side = min(a, b, c)
    t.cos_min = max(cos_a, cos_b, cos_g)
    t.label = "group2 (a,b,c)=(%d,%d,%d) gamma=2pi/3" % (a, b, c)
    t.inv = None
    if want_invariant:
        try:
            t.inv = BoundaryInvariant(a, b, c, cos_a, sin_a, mcap)
        except ValueError as e:
            sys.stderr.write("[warn] boundary invariant unavailable: %s\n" % e)
    global TILE
    TILE = t
    return t


def setup_tile_group1(p, q, **_kw):
    """Beeson's Group-1 tile: 3alpha+2beta = pi, (a,b,c) = (pq, q^2-p^2, q^2),
    sin(alpha/2) = p/(2q), so the geometry lives in Q(sqrt(4q^2-p^2))."""
    p, q = int(p), int(q)
    if not (0 < p < q):
        raise ValueError("need 0 < p < q")
    if gcd(p, q) != 1:
        raise ValueError("need gcd(p,q) = 1")
    D = 4 * q * q - p * p
    if isqrt(D) ** 2 == D:
        sys.stderr.write("[warn] D = %d is a perfect square: tile angles are "
                         "commensurable-looking; geometry still exact\n" % D)
    set_field(D)
    a, b, c = p * q, q * q - p * p, q * q
    t = Tile()
    t.group = 1
    t.a, t.b, t.c = a, b, c
    t.p, t.q = p, q
    cos_a, sin_a = Fr(2 * q * q - p * p, 2 * q * q), Fr(p, 2 * q * q)
    cos_b, sin_b = Fr(p * (3 * q * q - p * p), 2 * q ** 3), Fr(q * q - p * p, 2 * q ** 3)
    cos_g, sin_g = Fr(-p, 2 * q), Fr(1, 2 * q)
    _check_angle(cos_a, sin_a, "alpha")
    _check_angle(cos_b, sin_b, "beta")
    _check_angle(cos_g, sin_g, "gamma")
    # float sanity: angles sum to pi and 3alpha+2beta = pi
    import math
    al = math.atan2(float(sin_a) * _SQRTD, float(cos_a))
    be = math.atan2(float(sin_b) * _SQRTD, float(cos_b))
    ga = math.atan2(float(sin_g) * _SQRTD, float(cos_g))
    if abs(al + be + ga - math.pi) > 1e-9:
        raise ValueError("group-1 angles do not sum to pi")
    if abs(3 * al + 2 * be - math.pi) > 1e-9:
        raise ValueError("group-1 tile does not satisfy 3alpha+2beta = pi")
    t.angles = [(cos_a, sin_a, b, c), (cos_b, sin_b, a, c), (cos_g, sin_g, a, b)]
    t.tw2 = Fr(p * (q * q - p * p), 2)      # = a*b*sin_g
    t.min_side = min(a, b, c)
    t.cos_min = max(cos_a, cos_b, cos_g)
    t.label = ("group1 (p,q)=(%d,%d) (a,b,c)=(%d,%d,%d) 3alpha+2beta=pi, D=%d"
               % (p, q, a, b, c, D))
    t.inv = None                            # not verified for this branch
    global TILE
    TILE = t
    return t


def budget_of(a2):
    """area/tile_area as a positive int, or None."""
    r = a2 / TILE.tw2
    if r.denominator != 1 or r <= 0:
        return None
    return int(r)


# ---------------------------------------------------------------------------
# Boundary-segment semigroup condition (a local prune, unlike the invariant)
# ---------------------------------------------------------------------------
class SegmentSemigroup:
    """Every boundary edge whose two endpoints are both convex corners has a
    length in the numerical semigroup <a,b,c>.

    Proof.  Let e = [A,B] be such an edge and p in its relative interior.  R is
    locally a half-disk at p, so every tile covering p has an edge through p
    collinear with e (an edge in any other direction would put tile area on both
    sides of e).  Such a tile edge cannot extend past A: the interior wedge at A
    has angle < pi and e is one of its two sides, so the backward continuation of
    e leaves R.  Same at B.  Hence e is partitioned by whole tile edges, so
    |e| is a non-negative integer combination of a, b, c.  (Convexity at both
    ends is essential -- at a reflex end the line continues into the interior and
    a tile edge may cross it, which is exactly the multi-collinear-segment
    configuration.)

    Unlike the boundary invariant, this condition is *not* conserved when a tile
    is removed, so it prunes inside the search tree.
    """

    def __init__(self, a, b, c, limit):
        self.limit = int(limit)
        reach = bytearray(self.limit + 1)
        reach[0] = 1
        for i in range(1, self.limit + 1):
            if ((i >= a and reach[i - a]) or (i >= b and reach[i - b])
                    or (i >= c and reach[i - c])):
                reach[i] = 1
        self.reach = reach
        self.gaps = [i for i in range(self.limit + 1) if not reach[i]]

    def ok(self, L):
        """False => provably not a sum of tile edges."""
        if L.denominator != 1:
            return False
        iv = int(L)
        if iv > self.limit:
            return True                     # beyond the table: no information
        return bool(self.reach[iv])


# ---------------------------------------------------------------------------
# Per-component edge data (one pass; reused by every prune and the placement)
# ---------------------------------------------------------------------------
def edge_data(comp):
    """Return (unit directions, lengths) for the edges comp[i] -> comp[i+1]."""
    n = len(comp)
    edir = []
    elen = []
    for i in range(n):
        A = comp[i]
        B = comp[(i + 1) % n]
        e = (B[0] - A[0], B[1] - A[1])
        L = rational_sqrt(e[0] * e[0] + FIELD_D * e[1] * e[1])
        if L is None or L == 0:
            raise OffLattice("component edge %d has irrational length" % i)
        edir.append((e[0] / L, e[1] / L))
        elen.append(L)
    return edir, elen


# ---------------------------------------------------------------------------
# Placement enumeration and the fit test
# ---------------------------------------------------------------------------
def enumerate_placements(P, d, cosw):
    """All flush placements at corner P: a tile angle X <= wedge, one adjacent
    side along d, the other rotated CCW into the interior."""
    out = []
    seen = set()
    for (cs, sw, sA, sB) in TILE.angles:
        if cs >= cosw:                      # X <= theta_wedge
            rot = rot_ccw(d, cs, sw)
            for (flush, other) in ((sA, sB), (sB, sA)):
                Q = padd(P, pscale(d, flush))
                R = padd(P, pscale(rot, other))
                key = (Q, R)
                if key in seen:
                    continue
                seen.add(key)
                out.append((Q, R))
    return out


def cone_contains(u1, u2, d):
    """d lies in the closed cone swept counterclockwise from u1 to u2."""
    return not _more_ccw(u1, d, u2)


def _comp_cone(V, comp):
    """The interior cone of comp at V as (u1, u2) swept CCW, or None if V is not
    on the boundary (then there is no local constraint)."""
    n = len(comp)
    for i in range(n):
        if peq(V, comp[i]):
            return (psub(comp[(i + 1) % n], V), psub(comp[i - 1], V))
    for i in range(n):
        A = comp[i]
        B = comp[(i + 1) % n]
        if strictly_on_segment(V, A, B):
            return (psub(B, V), psub(A, V))     # half-plane left of A->B
    return None


def _tile_cone(V, tri):
    """The tile's interior cone at V as (u1, u2, umid) swept CCW, or None if V is
    not on the tile boundary.  tri must be counterclockwise."""
    for i in range(3):
        if peq(V, tri[i]):
            return (psub(tri[(i + 1) % 3], V), psub(tri[i - 1], V),
                    padd(psub(tri[(i + 1) % 3], V), psub(tri[i - 1], V)))
    for i in range(3):
        A = tri[i]
        B = tri[(i + 1) % 3]
        if strictly_on_segment(V, A, B):
            # half-plane left of A->B; the opposite vertex is strictly inside it
            return (psub(B, V), psub(A, V), psub(tri[(i + 2) % 3], V))
    return None


def fit_test(P, Q, R, comp):
    """The tile (P,Q,R) lies in comp with its interior inside comp's interior.

    (a) no tile edge properly crosses a boundary edge, (b) no boundary vertex is
    strictly inside the tile, (c) the tile's vertices are in comp, (d) its
    centroid is strictly inside comp, and (e) at every point where the two
    boundaries touch, the tile's local cone is contained in comp's local cone.

    (e) is essential and was missing in v1: a tile edge can run straight through
    a *convex* boundary vertex (a T-junction, which is not a proper crossing and
    leaves no vertex strictly inside the tile) and the tile then leaves the
    component past that vertex.  Without (e) such placements are only caught
    later, by area conservation, which reports them as skipped placements.
    """
    tile_edges = ((P, Q), (Q, R), (R, P))
    n = len(comp)
    for i in range(n):
        bA = comp[i]
        bB = comp[(i + 1) % n]
        for (tA, tB) in tile_edges:
            if seg_proper_cross(tA, tB, bA, bB):
                return False
    for v in comp:
        if strictly_inside_tri(v, P, Q, R):
            return False
    for v in (P, Q, R):
        if not point_in_poly(v, comp):
            return False
    cen = ((P[0] + Q[0] + R[0]) / 3, (P[1] + Q[1] + R[1]) / 3)
    if not strictly_inside_poly(cen, comp):
        return False
    tri = (P, Q, R) if signed_area2((P, Q, R)) > 0 else (P, R, Q)
    touch = [P, Q, R]
    for v in comp:
        if v not in touch and any(on_segment(v, A, B) for (A, B) in tile_edges):
            touch.append(v)
    for V in touch:
        tc = _tile_cone(V, tri)
        if tc is None:
            continue
        cc = _comp_cone(V, comp)
        if cc is None:
            continue
        u1, u2 = cc
        if not (cone_contains(u1, u2, tc[0]) and cone_contains(u1, u2, tc[1])
                and cone_contains(u1, u2, tc[2])):
            return False
    return True


# ---------------------------------------------------------------------------
# Subtraction as an exact 1-chain operation (closes ROADMAP G1)
# ---------------------------------------------------------------------------
class ValidationError(Exception):
    pass


def _remove_one_collinear(cyc):
    n = len(cyc)
    if n < 3:
        return cyc, False
    for i in range(n):
        if orient(cyc[i - 1], cyc[i], cyc[(i + 1) % n]) == 0:
            return cyc[:i] + cyc[i + 1:], True
    return cyc, False


def normalize_cycle(cyc):
    """Merge collinear runs and cancel spikes.  Returns a possibly shorter cycle."""
    out = []
    for pt in cyc:
        if not out or not peq(out[-1], pt):
            out.append(pt)
    while len(out) >= 2 and peq(out[0], out[-1]):
        out.pop()
    while len(out) >= 3:
        out, changed = _remove_one_collinear(out)
        if not changed:
            break
    return out


def _dir_group(r, s):
    """Which quarter of the CCW turn from r to s: 0 (zero), 1 (0,pi),
    2 (pi), 3 (pi,2pi).  Scale-invariant."""
    cr = cross2(r, s)
    if cr > 0:
        return 1
    if cr < 0:
        return 3
    return 0 if dot(r, s) > 0 else 2


def _more_ccw(r, s1, s2):
    """True if the CCW angle from r to s1 exceeds that from r to s2."""
    g1 = _dir_group(r, s1)
    g2 = _dir_group(r, s2)
    if g1 != g2:
        return g1 > g2
    if g1 == 0 or g1 == 2:
        return False
    return cross2(s2, s1) > 0


def trace_faces(edges):
    """Trace the faces of a boundary 1-chain (region on the left of every edge).

    `edges` is a list of directed edges, each to be traversed exactly once, with
    no vertex in the interior of an edge.  At each vertex the next edge is the
    first one clockwise from the reverse of the incoming direction, which splits
    the chain at pinch vertices exactly as the region's faces do.
    """
    m = len(edges)
    if m == 0:
        return []
    out = {}
    vec = []
    for idx, (u, v) in enumerate(edges):
        out.setdefault(u, []).append(idx)
        vec.append((v[0] - u[0], v[1] - u[1]))
    used = [False] * m
    faces = []
    for start in range(m):
        if used[start]:
            continue
        cyc = []
        idx = start
        guard = 0
        while True:
            guard += 1
            if guard > m + 2:
                raise ValidationError("face tracing did not terminate")
            used[idx] = True
            u, v = edges[idx]
            cyc.append(u)
            cands = out.get(v)
            if not cands:
                raise ValidationError("open chain at %r" % (v,))
            r = pneg(vec[idx])
            best = None
            for j in cands:
                if best is None or _more_ccw(r, vec[j], vec[best]):
                    best = j
            if best == start:
                break
            if used[best]:
                alt = [j for j in cands if not used[j] and edges[j] == edges[best]]
                if not alt:
                    raise ValidationError("face tracing inconsistency at %r" % (v,))
                best = alt[0]
            idx = best
        faces.append(cyc)
    return faces


def subtract(comp, ci, Q, R):
    """Remove the tile (P,Q,R), P = comp[ci], whose edge [P,Q] is flush along the
    outgoing boundary direction at P.  Returns the CCW components of comp \\ tile.

    Implemented as the 1-chain d(comp) - d(tile): no case analysis, so a flush
    edge spanning several collinear boundary segments is handled like any other.
    """
    P = comp[ci]
    n = len(comp)
    chain = []
    for i in range(n):
        u = comp[i]
        v = comp[(i + 1) % n]
        if not peq(u, v):
            chain.append((u, v))
    tile_pts = [P, Q, R]
    for (u, v) in ((Q, P), (R, Q), (P, R)):     # -d(tile): tile traversed CW
        if not peq(u, v):
            chain.append((u, v))
    ntile = 3                                   # last <=3 entries are tile edges

    # --- split.  comp is simple with no vertex on a non-adjacent edge, so the
    # only splits possible are: comp edges cut by tile vertices, and tile edges
    # cut by comp vertices.
    pieces = []
    ncomp_edges = len(chain) - ntile

    def emit(u, v, inner):
        if not inner:
            pieces.append((u, v))
            return
        duv = (v[0] - u[0], v[1] - u[1])
        inner.sort(key=lambda w: dot((w[0] - u[0], w[1] - u[1]), duv))
        prev = u
        for w in inner:
            if not peq(prev, w):
                pieces.append((prev, w))
            prev = w
        if not peq(prev, v):
            pieces.append((prev, v))

    for k, (u, v) in enumerate(chain):
        if k < ncomp_edges:
            inner = [w for w in tile_pts if strictly_on_segment(w, u, v)]
        else:
            inner = [w for w in comp if strictly_on_segment(w, u, v)]
        emit(u, v, inner)

    # --- cancel opposite duplicates
    cnt = {}
    for e in pieces:
        cnt[e] = cnt.get(e, 0) + 1
    kept = []
    done = set()
    for e, k in cnt.items():
        if e in done:
            continue
        rev = (e[1], e[0])
        done.add(e)
        done.add(rev)
        net = k - cnt.get(rev, 0)
        if net > 0:
            kept.extend([e] * net)
        elif net < 0:
            kept.extend([rev] * (-net))

    # --- trace and validate
    result = []
    for cyc in trace_faces(kept):
        cyc = normalize_cycle(cyc)
        if len(cyc) < 3:
            continue
        a2 = signed_area2(cyc)
        if a2 < 0:
            raise ValidationError("negative-area component after subtraction")
        if a2 == 0:
            continue
        if PARANOID:
            assert_simple(cyc)
        result.append(cyc)
    return result


PARANOID = False


def assert_simple(poly):
    """No two edges cross properly, no vertex inside a non-adjacent edge."""
    n = len(poly)
    for i in range(n):
        a, b = poly[i], poly[(i + 1) % n]
        for j in range(i + 1, n):
            if j == i or (j + 1) % n == i or (i + 1) % n == j:
                continue
            c, d = poly[j], poly[(j + 1) % n]
            if seg_proper_cross(a, b, c, d):
                raise ValidationError("non-simple component: edges cross")
    for k in range(n):
        V = poly[k]
        for i in range(n):
            if i == k or (i + 1) % n == k:
                continue
            a, b = poly[i], poly[(i + 1) % n]
            if not peq(V, a) and not peq(V, b) and on_segment(V, a, b):
                raise ValidationError("non-simple component: vertex on edge")


# ---------------------------------------------------------------------------
# Canonical component key (translation + rotation of the vertex list)
# ---------------------------------------------------------------------------
def canonical(comp):
    v0 = min(comp)
    x0, w0 = v0
    keys = [(p[0] - x0, p[1] - w0) for p in comp]
    n = len(keys)
    best = None
    for r in range(n):
        rot = tuple(keys[(r + k) % n] for k in range(n))
        if best is None or rot < best:
            best = rot
    return best, v0


def translate_tile(tri, off):
    return tuple(padd(v, off) for v in tri)


# ---------------------------------------------------------------------------
# Search
# ---------------------------------------------------------------------------
class LimitReached(Exception):
    pass


class Stats:
    def __init__(self):
        self.nodes = 0
        self.warnings = 0
        self.max_depth = 0
        self.cut_area = 0
        self.cut_wedge = 0
        self.cut_corner = 0
        self.cut_inv = 0
        self.cut_seg = 0
        self.inv_miss = 0
        self.start = time.monotonic()


def solve_component(comp, depth, ctx):
    """A list of placed tiles covering comp, or None if comp is untileable."""
    stats = ctx["stats"]
    failed = ctx["failed"]
    solved = ctx["solved"]

    key, v0 = canonical(comp)
    if key in failed:
        return None
    if key in solved:
        return [translate_tile(t, v0) for t in solved[key]]

    stats.nodes += 1
    if depth > stats.max_depth:
        stats.max_depth = depth
    if stats.nodes % 100000 == 0:
        _progress(ctx, depth)
    if ctx["max_nodes"] is not None and stats.nodes > ctx["max_nodes"]:
        raise LimitReached("max-nodes")
    if ctx["max_seconds"] is not None and (time.monotonic() - stats.start) > ctx["max_seconds"]:
        raise LimitReached("max-seconds")
    if (ctx["max_rss_mb"] is not None and stats.nodes % 1000 == 0
            and rss_mb() > ctx["max_rss_mb"]):
        raise LimitReached("max-rss-mb (%.0f MB)" % rss_mb())

    a2 = signed_area2(comp)
    if a2 <= 0:
        raise ValidationError("non-positive area component reached in search")
    B = budget_of(a2)
    if B is None:
        stats.cut_area += 1
        failed.add(key)
        return None

    edir, elen = edge_data(comp)
    n = len(comp)
    conv = [orient(comp[i - 1], comp[i], comp[(i + 1) % n]) > 0 for i in range(n)]

    # prune: every convex corner must admit the smallest tile angle
    for i in range(n):
        if conv[i]:
            if dot(edir[i], pneg(edir[i - 1])) > TILE.cos_min:
                stats.cut_wedge += 1
                failed.add(key)
                return None

    # prune: an edge between two convex corners is partitioned by whole tile
    # edges, so its length lies in the semigroup <a,b,c>
    sg = ctx["sg"]
    if sg is not None:
        for i in range(n):
            if conv[i] and conv[(i + 1) % n] and not sg.ok(elen[i]):
                stats.cut_seg += 1
                failed.add(key)
                return None

    # prune: boundary invariant + N-term character bounds
    inv = ctx["inv"]
    if inv is not None:
        coeff = inv.evaluate(edir, elen)
        if coeff is None:
            stats.inv_miss += 1
        elif not inv.feasible(coeff, B):
            stats.cut_inv += 1
            failed.add(key)
            return None

    ci = None
    best = None
    for i in range(n):
        if conv[i]:
            if best is None or comp[i] < best:
                best = comp[i]
                ci = i
    P = comp[ci]
    d = edir[ci]
    cosw = dot(d, pneg(edir[ci - 1]))

    # prune: dead corner (outgoing stretch shorter than any tile side and the
    # far end is itself convex, so nothing can bridge it)
    if conv[(ci + 1) % n] and elen[ci] < TILE.min_side:
        stats.cut_corner += 1
        failed.add(key)
        return None

    for (Q, R) in enumerate_placements(P, d, cosw):
        if not fit_test(P, Q, R, comp):
            continue
        ta = signed_area2((P, Q, R))
        if ta != TILE.tw2 and ta != -TILE.tw2:
            stats.warnings += 1
            _warn(ctx, comp, ci, Q, R, "tile area %s != %s" % (ta, TILE.tw2))
            continue
        try:
            subcomps = subtract(comp, ci, Q, R)
        except (ValidationError, OffLattice) as exc:
            stats.warnings += 1
            _warn(ctx, comp, ci, Q, R, "subtract: %s" % exc)
            continue
        total = ZERO
        ok = True
        for cc in subcomps:
            ca2 = signed_area2(cc)
            total += ca2
            if budget_of(ca2) is None:
                ok = False
                break
        if not ok:
            continue
        if total != a2 - TILE.tw2:
            stats.warnings += 1
            _warn(ctx, comp, ci, Q, R,
                  "area not conserved: %s != %s" % (total, a2 - TILE.tw2))
            continue
        placed = [(P, Q, R)]
        good = True
        for cc in subcomps:
            res = solve_component(cc, depth + 1, ctx)
            if res is None:
                good = False
                break
            placed.extend(res)
        if good:
            solved[key] = [translate_tile(t, (-v0[0], -v0[1])) for t in placed]
            return placed

    failed.add(key)
    return None


WARN_DETAIL = False


def _warn(ctx, comp, ci, Q, R, msg):
    """A skipped placement is a completeness hole: dump it so it can be fixed."""
    if not WARN_DETAIL:
        return
    sys.stderr.write("[WARN] %s\n" % msg)
    sys.stderr.write("       comp(ci=%d, D=%d) = %s\n"
                     % (ci, FIELD_D, " ".join("%s,%s" % (p[0], p[1]) for p in comp)))
    sys.stderr.write("       P=%s,%s Q=%s,%s R=%s,%s\n"
                     % (comp[ci][0], comp[ci][1], Q[0], Q[1], R[0], R[1]))
    sys.stderr.flush()


def _progress(ctx, depth):
    stats = ctx["stats"]
    el = time.monotonic() - stats.start
    sys.stderr.write(
        "[progress] nodes=%d depth=%d failed=%d solved=%d warns=%d "
        "cuts(area=%d wedge=%d corner=%d seg=%d inv=%d miss=%d) t=%.1fs %.0f n/s "
        "rss=%.0fMB\n"
        % (stats.nodes, depth, len(ctx["failed"]), len(ctx["solved"]),
           stats.warnings, stats.cut_area, stats.cut_wedge, stats.cut_corner,
           stats.cut_seg, stats.cut_inv, stats.inv_miss, el,
           stats.nodes / el if el else 0, rss_mb()))
    sys.stderr.flush()


# ---------------------------------------------------------------------------
# Target construction
# ---------------------------------------------------------------------------
def tri_from_two_sides(ab, ac, cs, sw):
    """A = origin, B = (ab, 0), C = ac*(cos,sin) for the angle at A."""
    return [(Fr(0), Fr(0)), (Fr(ab), Fr(0)), (Fr(ac) * cs, Fr(ac) * sw)]


def ensure_ccw(poly):
    s = signed_area2(poly)
    if s == 0:
        raise ValueError("degenerate target polygon (zero area)")
    return list(poly) if s > 0 else list(reversed(poly))


def _angle_cos_sin(which):
    (ca, sa, _, _), (cb, sb, _, _), (cg, sg, _, _) = TILE.angles
    if which == "alpha":
        return ca, sa
    if which == "beta":
        return cb, sb
    if which == "gamma":
        return cg, sg
    if which == "2alpha":
        return 2 * ca * ca - 1, 2 * ca * sa
    if which == "alpha+beta":
        return ca * cb - FIELD_D * sa * sb, sa * cb + ca * sb
    if which == "pi/3":
        return Fr(1, 2), Fr(1, 2)
    raise ValueError("unknown angle %r" % which)


# rows of the Group-2 classification (invariants.md sec.1):
#   (|AB|, |AC|, angle at A, |BC|) as functions of the tile and the scale k
ROW_SIDES = {
    "I":   lambda a, b, c, k: (k * (a + 2 * b), k * c, "alpha", k * c),
    "II":  lambda a, b, c, k: (3 * k * b * (a + b), k * (a + 2 * b) * c, "alpha", k * c * c),
    "III": lambda a, b, c, k: (k * (a + b) * c, k * b * (2 * a + b), "alpha", k * a * c),
    "IV":  lambda a, b, c, k: (k * (a + b), k * c, "alpha", k * a),
    "V":   lambda a, b, c, k: (k * c * c, k * b * (2 * a + b), "2alpha", k * a * (a + 2 * b)),
}


def build_row_target(row, a, b, c, k):
    setup_tile_group2(a, b, c)
    if row == "E":
        L = k
        cs, sw = _angle_cos_sin("pi/3")
        poly = tri_from_two_sides(L, L, cs, sw)
        third = L
    else:
        ab, ac, ang, third = ROW_SIDES[row](a, b, c, k)
        cs, sw = _angle_cos_sin(ang)
        poly = tri_from_two_sides(ab, ac, cs, sw)
    got = norm2(psub(poly[1], poly[2]))
    if got != third * third:
        raise AssertionError("row %s: |BC|^2 = %s, expected %d^2" % (row, got, third))
    N = budget_of(signed_area2(ensure_ccw(poly)))
    if N is None:
        raise AssertionError("row %s: target area is not an integer multiple of the tile"
                             % row)
    label = ("row %s, tile (%d,%d,%d), k=%d" % (row, a, b, c, k) if row != "E"
             else "row E (equilateral side %d), tile (%d,%d,%d)" % (k, a, b, c))
    return poly, N, label


def build_trapezoid(a, b, c, L, x):
    """Zhang's ideal trapezoid: parallel sides x and x+L, both base angles pi/3,
    legs L.  N = L(2x+L)/(ab)."""
    setup_tile_group2(a, b, c)
    L = Fr(L)
    x = Fr(x)
    half = L / 2
    poly = [(Fr(0), Fr(0)), (x + L, Fr(0)), (x + half, half), (half, half)]
    for (u, v) in ((poly[1], poly[2]), (poly[3], poly[0])):
        if norm2(psub(v, u)) != L * L:
            raise AssertionError("trapezoid leg length wrong")
    if norm2(psub(poly[2], poly[3])) != x * x:
        raise AssertionError("trapezoid short side wrong")
    N = budget_of(signed_area2(ensure_ccw(poly)))
    if N is None:
        raise AssertionError("trapezoid area is not an integer multiple of the tile "
                             "(need ab | L(2x+L))")
    return poly, N, "ideal trapezoid x=%s L=%s, tile (%d,%d,%d)" % (x, L, a, b, c)


def build_group1_target(shape, p, q, N):
    """Beeson Group-1 targets.  Both open shapes are isosceles:
      shape 4: angles (alpha+beta, alpha+beta, alpha), ray N = (q^2-p^2)n^2
      shape 5: angles (alpha, alpha, alpha+2beta), ray N = (q^2-p^2)(2q^2-p^2)n^2/kappa
    The leg is forced by the area equation, which also decides whether the
    candidate exists at all (the kappa=4 parity correction comes out of the
    rationality test automatically)."""
    setup_tile_group1(p, q)
    N = int(N)
    if shape == 5:
        leg2 = Fr(N * q ** 4 * (q * q - p * p), 2 * q * q - p * p)
        ang = "alpha"
    elif shape == 4:
        leg2 = Fr(N * q * q * (q * q - p * p))
        ang = "alpha+beta"
    else:
        raise ValueError("only Group-1 shapes 4 and 5 are open")
    leg = rational_sqrt(leg2)
    if leg is None:
        raise AssertionError("no Group-1 shape-%d candidate at N=%d for (p,q)=(%d,%d): "
                             "leg^2 = %s is not a rational square"
                             % (shape, N, p, q, leg2))
    cs, sw = _angle_cos_sin(ang)
    base = 2 * leg * cs
    poly = tri_from_two_sides(base, leg, cs, sw)
    if norm2(psub(poly[1], poly[2])) != leg * leg:
        raise AssertionError("group-1 target is not isosceles")
    got = budget_of(signed_area2(ensure_ccw(poly)))
    if got != N:
        raise AssertionError("group-1 shape-%d target area/tile = %s, expected %d"
                             % (shape, got, N))
    return poly, N, ("group1 shape %d, (p,q)=(%d,%d), legs %s base %s"
                     % (shape, p, q, leg, base))


def build_reptile(k):
    """Positive control valid in any branch: the tile scaled by k is tiled by k^2
    copies of the tile.  Exercises the field arithmetic and the placement
    enumeration on a target that is guaranteed tileable."""
    a, b, c = TILE.a, TILE.b, TILE.c
    cs, sw = TILE.angles[0][0], TILE.angles[0][1]        # angle alpha at A
    poly = [(Fr(0), Fr(0)), (Fr(c * k), Fr(0)), (cs * b * k, sw * b * k)]
    if norm2(psub(poly[1], poly[2])) != Fr(a * a * k * k):
        raise AssertionError("reptile control: third side wrong")
    N = budget_of(signed_area2(ensure_ccw(poly)))
    if N != k * k:
        raise AssertionError("reptile control: area/tile = %s, expected %d" % (N, k * k))
    return poly, N, "reptile control: tile scaled x%d, N = %d" % (k, k * k)


# legacy v1 instances, reproduced bit-for-bit in the new coordinates
def build_instance(name):
    if name in ("control4", "control9", "control16"):
        a, b, c = 7, 8, 13
        k = {"control4": 2, "control9": 3, "control16": 4}[name]
        setup_tile_group2(a, b, c)
        ca, sa = Fr(a + 2 * b, 2 * c), Fr(a, 2 * c)
        poly = [(Fr(0), Fr(0)), (Fr(c * k), Fr(0)), (ca * b * k, sa * b * k)]
        return poly, k * k, "%s: tile (7,8,13) scaled x%d" % (name, k)
    table = {
        "N14":  ("E", 7, 8, 13, 28),
        "N56":  ("E", 7, 8, 13, 56),
        "N66":  ("E", 11, 24, 31, 132),
        "N80":  ("E", 5, 16, 19, 80),
        "N21":  ("IV", 5, 16, 19, 4),
        "N30":  ("IV", 7, 8, 13, 4),
        "N55":  ("IV", 39, 16, 49, 4),
        "N105a": ("IV", 8, 7, 13, 7),
        "N105b": ("IV", 16, 5, 19, 5),
        "N120": ("IV", 7, 8, 13, 8),
        "N33":  ("I", 5, 3, 7, 3),
        "N132": ("I", 5, 3, 7, 6),
        "N154": ("I", 8, 7, 13, 7),
        "N184": ("I", 7, 8, 13, 8),
        "N88":  ("III", 3, 5, 7, 1),
        "N143": ("V", 3, 5, 7, 1),
    }
    if name in table:
        row, a, b, c, k = table[name]
        return build_row_target(row, a, b, c, k)
    raise ValueError("unknown instance %r" % (name,))


INSTANCES = ["control4", "control9", "control16", "N14", "N21", "N30", "N33",
             "N55", "N56", "N66", "N80", "N88", "N105a", "N105b", "N120",
             "N132", "N143", "N154", "N184"]


# ---------------------------------------------------------------------------
# Output / verification of a found tiling
# ---------------------------------------------------------------------------
def verify_solution(tiles, target, a, b, c):
    want = sorted((a * a, b * b, c * c))
    tgt2 = signed_area2(target)
    tot = ZERO
    for tri in tiles:
        P0, P1, P2 = tri
        sides = sorted((norm2(psub(P0, P1)), norm2(psub(P1, P2)), norm2(psub(P2, P0))))
        assert sides == [Fr(w) for w in want], "tile not congruent to R: %s" % (sides,)
        a2 = signed_area2(tri)
        assert a2 != 0, "degenerate tile"
        tot += abs(a2)
        for v in tri:
            assert point_in_poly(v, target), "tile vertex outside target"
        cen = ((P0[0] + P1[0] + P2[0]) / 3, (P0[1] + P1[1] + P2[1]) / 3)
        assert strictly_inside_poly(cen, target), "tile centroid outside target"
    assert tot == tgt2, "tile areas %s != target area %s" % (tot, tgt2)
    m = len(tiles)
    for i in range(m):
        Ti = tiles[i]
        ceni = ((Ti[0][0] + Ti[1][0] + Ti[2][0]) / 3, (Ti[0][1] + Ti[1][1] + Ti[2][1]) / 3)
        for j in range(m):
            if i == j:
                continue
            Tj = tiles[j]
            A, Bb, C = Tj if signed_area2(Tj) > 0 else (Tj[0], Tj[2], Tj[1])
            assert not strictly_inside_tri(ceni, A, Bb, C), "overlap: centroid in tile"
            for (x1, x2) in ((Ti[0], Ti[1]), (Ti[1], Ti[2]), (Ti[2], Ti[0])):
                for (y1, y2) in ((Tj[0], Tj[1]), (Tj[1], Tj[2]), (Tj[2], Tj[0])):
                    assert not seg_proper_cross(x1, x2, y1, y2), "overlap: edges cross"
    return True


def print_solution(tiles):
    print("TILING FOUND")
    print("tiles: %d" % len(tiles))
    for idx, tri in enumerate(tiles):
        print("tile %d:" % (idx + 1))
        print("    exact:  %s" % "  ".join(pretty(v) for v in tri))
        print("    float:  %s" % "  ".join("(%.6f , %.6f)" % to_float(v) for v in tri))


def solution_json(tiles):
    return [[[str(v[0]), str(v[1])] for v in tri] for tri in tiles]


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------
def run_search(poly, N, label, max_nodes=None, max_seconds=None, prune_inv=True,
               quiet=False, prune_seg=True, max_rss_mb=None):
    target = ensure_ccw(normalize_cycle(poly))
    assert_simple(target)
    a2 = signed_area2(target)
    got = budget_of(a2)
    print("Tile: %s" % TILE.label)
    print("Target: %s" % label)
    print("Target vertices: %s" % "  ".join(pretty(v) for v in target))
    print("Target twice-area/sqrt(D) = %s;  N = %s;  area/tile = %s" % (a2, N, got))
    inv = TILE.inv if prune_inv else None
    if TILE.inv is not None:
        rep = TILE.inv.report(target)
        if rep is None:
            print("Root invariant: some target direction is off the (j,m) table "
                  "(raise --mcap); pruning will be skipped there")
        else:
            print("Root invariant: Phi=%s=%s*Delta(%d)  Phi'=%s=%s*Delta'(%d)  "
                  "ideal residue %s mod %d"
                  % (rep["Phi"], rep["M"], rep["Delta"], rep["Phi'"], rep["M'"],
                     rep["Delta'"], rep["ideal_residue"], rep["mod"]))
    else:
        print("Root invariant: not available for this branch (no invariant pruning)")
    if got != N:
        print("EXHAUSTED: NO TILING EXISTS (area budget mismatch: %s != %s)" % (got, N))
        return {"verdict": "EXHAUSTED", "reason": "area", "nodes": 0}

    sg = None
    if prune_seg:
        perim = sum(seg_len(target[i], target[(i + 1) % len(target)])
                    for i in range(len(target)))
        if perim.denominator == 1:
            sg = SegmentSemigroup(TILE.a, TILE.b, TILE.c, int(perim))
            print("Segment semigroup <%d,%d,%d>: %d gaps below the perimeter %d"
                  % (TILE.a, TILE.b, TILE.c, len(sg.gaps) - 1, perim))
    ctx = {"stats": Stats(), "failed": set(), "solved": {},
           "max_nodes": max_nodes, "max_seconds": max_seconds,
           "max_rss_mb": max_rss_mb, "inv": inv, "sg": sg}
    stats = ctx["stats"]
    res = None
    verdict = None
    try:
        res = solve_component(target, 0, ctx)
    except LimitReached as e:
        verdict = "UNDECIDED"
        print("UNDECIDED (limit reached: %s)" % e)
    el = time.monotonic() - stats.start
    if verdict is None:
        if res is not None:
            assert len(res) == N, "solution has %d tiles, N = %d" % (len(res), N)
            verify_solution(res, target, TILE.a, TILE.b, TILE.c)
            print("[verified] congruent, interior-disjoint, area-exact, inside target")
            if quiet:
                print("TILING FOUND (%d tiles; coordinates suppressed by --quiet, "
                      "use --json to keep them)" % len(res))
            else:
                print_solution(res)
            verdict = "FOUND"
        else:
            print("EXHAUSTED: NO TILING EXISTS")
            verdict = "EXHAUSTED"
    print("stats: nodes=%d max_depth=%d failed=%d solved=%d warns=%d "
          "cuts(area=%d wedge=%d corner=%d seg=%d inv=%d miss=%d) wall=%.2fs"
          % (stats.nodes, stats.max_depth, len(ctx["failed"]), len(ctx["solved"]),
             stats.warnings, stats.cut_area, stats.cut_wedge, stats.cut_corner,
             stats.cut_seg, stats.cut_inv, stats.inv_miss, el))
    out = {"verdict": verdict, "nodes": stats.nodes, "max_depth": stats.max_depth,
           "failed": len(ctx["failed"]), "solved": len(ctx["solved"]),
           "warns": stats.warnings, "wall": round(el, 2), "rss_mb": round(rss_mb()),
           "cut_area": stats.cut_area, "cut_wedge": stats.cut_wedge,
           "cut_corner": stats.cut_corner, "cut_seg": stats.cut_seg,
           "cut_inv": stats.cut_inv,
           "inv_miss": stats.inv_miss, "N": N, "label": label,
           "tile": TILE.label, "prune_inv": bool(inv), "prune_seg": sg is not None}
    if verdict == "FOUND":
        out["tiling"] = solution_json(res)
    return out


def parse_point(s):
    a, b = s.split(",")
    return (Fr(a), Fr(b))


def main(argv):
    ap = argparse.ArgumentParser(description="Exact tiling searcher for Erdos 634 (v2)")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--instance", choices=INSTANCES)
    ap.add_argument("--row", choices=["I", "II", "III", "IV", "V", "E"])
    ap.add_argument("--tile", nargs=3, type=int, metavar=("a", "b", "c"))
    ap.add_argument("--k", type=int, help="row scale k (row E: the equilateral side)")
    ap.add_argument("--trapezoid", action="store_true")
    ap.add_argument("--L", type=str, help="trapezoid leg")
    ap.add_argument("--x", type=str, help="trapezoid short parallel side")
    ap.add_argument("--group1", action="store_true")
    ap.add_argument("--shape", type=int, choices=[4, 5])
    ap.add_argument("--pq", nargs=2, type=int, metavar=("p", "q"))
    ap.add_argument("--N", type=int, help="tile count for --group1 / --polygon")
    ap.add_argument("--polygon", type=str,
                    help='target as "x1,w1 x2,w2 ..." (point (x, w*sqrt(D)))')
    ap.add_argument("--max-nodes", type=int, default=None)
    ap.add_argument("--max-seconds", type=float, default=None)
    ap.add_argument("--max-rss-mb", type=float, default=6000,
                    help="stop cleanly (UNDECIDED) when peak RSS exceeds this "
                         "many MB; default 6000, 0 disables")
    ap.add_argument("--paranoid", action="store_true")
    ap.add_argument("--no-prune-invariant", action="store_true")
    ap.add_argument("--no-prune-segment", action="store_true")
    ap.add_argument("--reptile", type=int, metavar="k",
                    help="positive control: target = the tile scaled by k, N = k^2 "
                         "(use with --tile a b c or --pq p q)")
    ap.add_argument("--mcap", type=int, default=16)
    ap.add_argument("--json", type=str, help="append the result record to this file")
    ap.add_argument("--tag", type=str, help="job name recorded in the --json record")
    ap.add_argument("--quiet", action="store_true", help="do not print a found tiling")
    ap.add_argument("--warn-detail", action="store_true",
                    help="dump every skipped placement (completeness diagnostics)")
    args = ap.parse_args(argv)

    if args.paranoid:
        global PARANOID
        PARANOID = True
    if args.warn_detail:
        global WARN_DETAIL
        WARN_DETAIL = True

    if args.selftest:
        run_selftests()
        return 0

    if args.reptile:
        if args.tile:
            setup_tile_group2(*args.tile, mcap=args.mcap)
        elif args.pq:
            setup_tile_group1(*args.pq)
        else:
            ap.error("--reptile needs --tile a b c or --pq p q")
        poly, N, label = build_reptile(args.reptile)
    elif args.instance:
        poly, N, label = build_instance(args.instance)
        label = "%s -- %s" % (args.instance, label)
    elif args.row:
        if not (args.tile and args.k):
            ap.error("--row needs --tile a b c and --k")
        poly, N, label = build_row_target(args.row, *args.tile, k=args.k)
    elif args.trapezoid:
        if not (args.tile and args.L is not None and args.x is not None):
            ap.error("--trapezoid needs --tile a b c --L L --x X")
        poly, N, label = build_trapezoid(*args.tile, L=args.L, x=args.x)
    elif args.group1:
        if not (args.shape and args.pq and args.N):
            ap.error("--group1 needs --shape {4,5} --pq p q --N N")
        poly, N, label = build_group1_target(args.shape, args.pq[0], args.pq[1], args.N)
    elif args.polygon:
        if args.tile:
            setup_tile_group2(*args.tile, mcap=args.mcap)
        elif args.pq:
            setup_tile_group1(*args.pq)
        else:
            ap.error("--polygon needs --tile a b c or --pq p q")
        poly = [parse_point(s) for s in args.polygon.split()]
        N = args.N or budget_of(signed_area2(ensure_ccw(poly)))
        label = "explicit polygon (%d vertices)" % len(poly)
    else:
        ap.error("give --selftest, --instance, --row, --trapezoid, --group1 or --polygon")

    if args.mcap != 16 and TILE.inv is not None:
        TILE.inv = BoundaryInvariant(TILE.a, TILE.b, TILE.c,
                                     TILE.angles[0][0], TILE.angles[0][1], args.mcap)
    rec = run_search(poly, N, label, args.max_nodes, args.max_seconds,
                     prune_inv=not args.no_prune_invariant, quiet=args.quiet,
                     prune_seg=not args.no_prune_segment,
                     max_rss_mb=args.max_rss_mb or None)
    if args.json:
        rec["argv"] = argv
        rec["tag"] = args.tag or ""
        with open(args.json, "a") as fh:
            fh.write(json.dumps(rec) + "\n")
    return 0


# ---------------------------------------------------------------------------
# Self-tests
# ---------------------------------------------------------------------------
def _poly(*pts):
    return [(Fr(x), Fr(w)) for (x, w) in pts]


def run_selftests():
    print("Running self-tests...")

    # --- field arithmetic ------------------------------------------------
    set_field(3)
    assert dot((Fr(1), Fr(0)), (Fr(1), Fr(0))) == 1
    assert dot((Fr(1, 2), Fr(1, 2)), (Fr(1, 2), Fr(1, 2))) == 1      # unit at 60 deg
    assert rational_sqrt(Fr(9, 4)) == Fr(3, 2)
    assert rational_sqrt(Fr(2)) is None
    assert seg_len((Fr(0), Fr(0)), (Fr(1, 2), Fr(1, 2))) == 1
    u = unit_dir((Fr(0), Fr(0)), (Fr(3), Fr(0)))
    assert u == (Fr(1), Fr(0))
    # rotating (1,0) by 60 deg six times returns to (1,0)
    v = (Fr(1), Fr(0))
    for _ in range(6):
        v = rot_ccw(v, Fr(1, 2), Fr(1, 2))
    assert v == (Fr(1), Fr(0))
    print("  [ok] field arithmetic, lengths, rotations")

    # --- predicates -----------------------------------------------------
    set_field(1)
    A, B = (Fr(0), Fr(0)), (Fr(2), Fr(2))
    C, D = (Fr(0), Fr(2)), (Fr(2), Fr(0))
    assert seg_proper_cross(A, B, C, D)
    assert not seg_proper_cross(A, B, B, (Fr(3), Fr(3)))
    assert not seg_proper_cross(A, B, (Fr(1), Fr(1)), (Fr(2), Fr(0)))
    sq = _poly((0, 0), (4, 0), (4, 4), (0, 4))
    assert strictly_inside_poly((Fr(2), Fr(2)), sq)
    assert point_in_poly((Fr(2), Fr(0)), sq)
    assert not strictly_inside_poly((Fr(2), Fr(0)), sq)
    assert not point_in_poly((Fr(5), Fr(2)), sq)
    L = _poly((0, 0), (4, 0), (4, 2), (2, 2), (2, 4), (0, 4))
    assert strictly_inside_poly((Fr(1), Fr(3)), L)
    assert not point_in_poly((Fr(3), Fr(3)), L)
    assert signed_area2(sq) == 32
    print("  [ok] predicates (crossing, in-polygon, area)")

    # --- subtraction: the classical cases -------------------------------
    def areas(comps):
        return sorted(signed_area2(c) for c in comps)

    set_field(1)
    # case A: flush edge ends inside the first boundary edge
    r = subtract(sq, 0, (Fr(2), Fr(0)), (Fr(0), Fr(2)))
    assert len(r) == 1 and areas(r) == [Fr(28)], areas(r)
    # case B: flush edge ends exactly at the next vertex
    r = subtract(sq, 0, (Fr(4), Fr(0)), (Fr(0), Fr(4)))
    assert len(r) == 1 and areas(r) == [Fr(16)], areas(r)
    # vertex-on-edge pinch: median triangle of the square -> two components
    r = subtract(sq, 0, (Fr(4), Fr(0)), (Fr(2), Fr(4)))
    assert len(r) == 2 and areas(r) == [Fr(8), Fr(8)], areas(r)
    # interior apex: one component
    r = subtract(sq, 0, (Fr(4), Fr(0)), (Fr(2), Fr(2)))
    assert len(r) == 1 and areas(r) == [Fr(24)], areas(r)
    print("  [ok] subtraction cases A / B / vertex-on-edge pinch / interior apex")

    # --- subtraction: the multi-segment flush edge (ROADMAP G1) ---------
    # A region with a tab hanging below the flush line: the flush edge spans
    # three collinear boundary segments.  v1's uniform splice could not
    # represent this; here it must split off the tab as its own component.
    tab = _poly((0, 0), (1, 0), (1, -1), (2, -1), (2, 0), (3, 0), (3, 3), (0, 3))
    assert signed_area2(tab) == 20      # twice area: 9 + 1
    r = subtract(tab, 0, (Fr(3), Fr(0)), (Fr(0), Fr(3)))
    assert len(r) == 2, [len(x) for x in r]
    assert areas(r) == [Fr(2), Fr(9)], areas(r)     # tab (1) and triangle (4.5)
    # deeper: two tabs, flush edge spanning five collinear segments
    tab2 = _poly((0, 0), (1, 0), (1, -1), (2, -1), (2, 0), (3, 0), (3, -1),
                 (4, -1), (4, 0), (5, 0), (5, 5), (0, 5))
    r = subtract(tab2, 0, (Fr(5), Fr(0)), (Fr(0), Fr(5)))
    assert len(r) == 3, len(r)
    assert areas(r) == [Fr(2), Fr(2), Fr(25)], areas(r)
    # flush edge ending strictly inside the region (boundary returns beyond Q)
    tab3 = _poly((0, 0), (1, 0), (1, -1), (3, -1), (3, 0), (4, 0), (4, 3), (0, 3))
    assert signed_area2(tab3) == 28
    r = subtract(tab3, 0, (Fr(2), Fr(0)), (Fr(0), Fr(1)))
    assert len(r) == 1 and areas(r) == [Fr(26)], areas(r)
    print("  [ok] multi-segment flush splice (1, 2 tabs, and Q strictly inside)")

    # --- instances: areas and the row constructions ---------------------
    expect = {"control4": 4, "control9": 9, "control16": 16, "N14": 14, "N21": 21,
              "N30": 30, "N33": 33, "N55": 55, "N56": 56, "N66": 66, "N80": 80,
              "N88": 88, "N105a": 105, "N105b": 105, "N120": 120, "N132": 132,
              "N143": 143, "N154": 154, "N184": 184}
    for name, N in expect.items():
        poly, got, _ = build_instance(name)
        assert got == N, "%s: area/tile = %s, expected %d" % (name, got, N)
        assert budget_of(signed_area2(ensure_ccw(poly))) == N
    print("  [ok] all %d built-in instances have area = N * tile area" % len(expect))

    # --- the boundary invariant ----------------------------------------
    # N33: the certified-exhaustion instance is boundary-FEASIBLE, with the
    # 33-term representation M = -1, M' = -15 recorded in invariants.md sec.4.
    poly, N, _ = build_instance("N33")
    rep = TILE.inv.report(ensure_ccw(poly))
    assert rep["ideal_residue"] == 0, rep
    assert rep["M"] == "-1" and rep["M'"] == "-15", rep
    assert TILE.inv.feasible(TILE.inv.evaluate(*edge_data(ensure_ccw(poly))), N)
    # rows I/IV/E where b|k resp. ab|L fails must be killed at the root, and
    # the values that survive the algebra must not be.
    # 14, 21, 30, 55 (b | k in rows IV/E) and 66 (ab | L in row E) are exactly the
    # values excluded algebraically in STATUS sec.5 -- the prune must reproduce
    # every one of them at the root, and spare every value that survives there.
    killed = ["N14", "N21", "N30", "N55", "N66"]
    survive = ["N33", "N56", "N80", "N88", "N105a", "N105b", "N120",
               "N132", "N143", "N154", "N184"]
    for name in killed + survive:
        poly, N, _ = build_instance(name)
        target = ensure_ccw(poly)
        coeff = TILE.inv.evaluate(*edge_data(target))
        assert coeff is not None, "%s: direction off the table" % name
        ok = TILE.inv.feasible(coeff, N)
        want = name not in killed
        assert ok == want, "%s: invariant feasible=%s, expected %s" % (name, ok, want)
    print("  [ok] invariant kills 14/21/30/55/66 at the root (= the algebraic "
          "exclusions) and spares the other %d" % len(survive))

    # --- Group-1 geometry ----------------------------------------------
    for (shape, p, q, N, leg, base) in [(5, 1, 2, 21, 12, 21), (5, 1, 2, 189, 36, 63),
                                        (5, 2, 3, 70, 45, 70), (5, 3, 4, 161, 112, 161),
                                        (5, 1, 3, 34, 36, 68), (4, 13, 15, 56, 840, 728),
                                        (4, 5, 9, 56, 504, 280)]:
        poly, got, lab = build_group1_target(shape, p, q, N)
        assert got == N, (shape, p, q, N, got)
        assert seg_len(poly[0], poly[2]) == leg, (lab, seg_len(poly[0], poly[2]))
        assert seg_len(poly[0], poly[1]) == base, (lab, seg_len(poly[0], poly[1]))
    # 189 = 21*3^2 sits on the (1,2) shape-5 ray; 100 does not
    try:
        build_group1_target(5, 1, 2, 100)
        raise AssertionError("N=100 should not be on the (1,2) shape-5 ray")
    except AssertionError as e:
        assert "not a rational square" in str(e), e
    print("  [ok] Group-1 shape-4/5 targets (21, 34, 70, 161, 189, 56x2)")

    # --- trapezoids -----------------------------------------------------
    poly, N, _ = build_trapezoid(3, 5, 7, 15, 3)
    assert N == 21, N
    poly, N, _ = build_trapezoid(3, 5, 7, 15, 34)
    assert N == 83, N        # Zhang's Lemma 1 witness: a^2+b^2 = 34, N = 3^2+5^2+7^2
    print("  [ok] ideal trapezoid targets (N = 2x+15 for (3,5,7); Lemma-1 case N=83)")

    # --- the segment semigroup ------------------------------------------
    sg = SegmentSemigroup(7, 8, 13, 40)
    assert sg.ok(Fr(7)) and sg.ok(Fr(15)) and sg.ok(Fr(21)) and sg.ok(Fr(0))
    assert not sg.ok(Fr(5)) and not sg.ok(Fr(9)) and not sg.ok(Fr(19))
    assert not sg.ok(Fr(15, 2))            # non-integer lengths cannot occur
    assert sg.ok(Fr(41))                   # beyond the table: no information
    sg357 = SegmentSemigroup(3, 5, 7, 40)
    assert sg357.gaps == [1, 2, 4], sg357.gaps
    print("  [ok] segment semigroup membership")

    # --- end-to-end: positive controls, with every prune enabled --------
    # (a prune that killed a real tiling would show up here immediately)
    for name, N in (("control4", 4), ("control9", 9), ("control16", 16)):
        poly, got, label = build_instance(name)
        rec = run_search(poly, got, label, max_nodes=100000, quiet=True)
        assert rec["verdict"] == "FOUND", (name, rec)
        assert rec["warns"] == 0, (name, rec)
    # the same in Group 1 (D = 4q^2-p^2 != 3): reptilings of the (2,3,4) and
    # (12,7,16) tiles, i.e. the geometry package D needs
    for (p, q, k) in ((1, 2, 2), (1, 2, 3), (3, 4, 2)):
        setup_tile_group1(p, q)
        poly, N, label = build_reptile(k)
        rec = run_search(poly, N, label, max_nodes=200000, quiet=True)
        assert rec["verdict"] == "FOUND", ((p, q, k), rec)
        assert rec["warns"] == 0, ((p, q, k), rec)
    print("  [ok] positive controls found and verified: Group-2 reptilings 4/9/16 "
          "and Group-1 reptilings (1,2)x2, (1,2)x3, (3,4)x2")

    print("ALL SELF-TESTS PASSED")


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
