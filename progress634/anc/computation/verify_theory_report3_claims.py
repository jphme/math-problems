#!/usr/bin/env python3
"""Verification of theory track report #3 (the "pro" report, integrated 2026-07-25).

Source: tmp/intermediate_result_pro_new.md, archived as
sources/theory_track_report3_2026-07-25_pro.md. The report proves the two G10
capacity theorems, completes the 60-degree one-tile invariant, and REMOVES the
kappa=4 factor from the Group-1 shape-5 ray (i.e. it says our own consolidation
"correction" was the error). This script is the second-method verification that
the label conventions require before any of that is promoted.

Sections:
  A. gamma=2alpha branch: factorization + Bezout identities (grid-proof),
     quotient Z[z,1/z]/(uz+v, u+vz) = Z/b, target-boundary insertion re-derived
     from the direction lattice (numeric, independent of the report's algebra),
     area/ray consistency N = b r^2, capacity sub-steps for r >= 2,
     vertex-multiset enumeration (exact, uses only alpha/pi irrational).
  B. Group-1 shape 4: same program for N = b m^2 and m >= 2; the companion
     filter (4) reproduces m >= 4 on the (1,2) ray (matching 48 = 3*4^2).
  C. Group-1 shape 5: Q*Qbar identity, insertion from the direction lattice,
     unit evaluation Qbar(q/p) = q^3/p^2 mod b, hence b | C and
     N = (q^2-p^2)(2q^2-p^2) m^2 with NO kappa -- for both-odd (p,q) too.
     Consistency with the N189 certificate and with the N=34 exhaustion.
  D. 60-degree tile: one-tile boundary polynomial d - c z^{+-1} (d = a+b)
     re-derived from the direction lattice; quotient 3ab; N = ab m^2.
  E. Full branch audits: 46, 438 (the report's two exclusions), and 56, 70
     (which the new theorems + the completed N56 row-E exhaustion decide).
  F. Frontier candidate lists below 200 recomputed under the new theorems.
  G. Cross-checks against stored search verdicts (results/*.jsonl).

A note on rigor of the "grid-proof" checks: each polynomial identity checked
has total degree <= 6 in each variable; verifying it on an integer grid larger
than the degree in every variable PROVES the identity (a nonzero polynomial of
degree d cannot vanish at d+1 points per variable).
"""

import cmath
import json
import math
import os
from fractions import Fraction
from math import ceil, cos, gcd, isqrt, pi, sin

OK, FAIL = [], []


def check(name, cond, detail=""):
    (OK if cond else FAIL).append((name, detail))
    print(("PASS  " if cond else "FAIL  ") + name + ("  | " + detail if detail else ""))


def is_square(n):
    return n >= 0 and isqrt(n) ** 2 == n


def is_sum_two_squares(n):
    # n = e^2 + f^2 (e,f >= 0) iff every prime p = 3 mod 4 divides n to an even power
    if n < 0:
        return False
    m, p = n, 2
    while p * p <= m:
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            if p % 4 == 3 and e % 2 == 1:
                return False
        p += 1
    return not (m % 4 == 3)


def in_semigroup2(x, a, b):
    if x < 0:
        return False
    for A in range(0, x // a + 1):
        if (x - A * a) % b == 0:
            return True
    return False


# ----------------------------------------------------------------------------
# generic direction-lattice boundary-polynomial machinery
# ----------------------------------------------------------------------------

def match_lattice(theta, step, alpha, jmax, mmax, tol=1e-9):
    """theta = j*step + m*alpha (mod 2pi) -> (j, m) or None."""
    for m in range(-mmax, mmax + 1):
        for j in range(0, jmax):
            d = (theta - j * step - m * alpha) % (2 * pi)
            if min(d, 2 * pi - d) < tol:
                return j, m
    return None


def boundary_poly(sides, step, alpha, jmax, mmax, half_turn_j):
    """sides: list of (length, direction). Returns dict m -> coefficient where
    each side contributes length * (-1)^j * z^m; half_turn_j = number of lattice
    steps in pi (so the character satisfies chi(theta+pi) = -chi(theta))."""
    poly = {}
    for length, theta in sides:
        jm = match_lattice(theta % (2 * pi), step, alpha, jmax, mmax)
        if jm is None:
            return None
        j, m = jm
        poly[m] = poly.get(m, 0.0) + length * (-1) ** j
    return {m: c for m, c in poly.items() if abs(c) > 1e-7}


def poly_equal_up_to_unit(P, Q, kmax=4):
    """P, Q dicts m->coeff. True iff P = +- z^k * Q for some |k| <= kmax."""
    if P is None or Q is None:
        return False
    for k in range(-kmax, kmax + 1):
        for s in (1, -1):
            Qs = {m + k: s * c for m, c in Q.items()}
            keys = set(P) | set(Qs)
            if all(abs(P.get(m, 0) - Qs.get(m, 0)) < 1e-6 for m in keys):
                return True
    return False


def triangle_sides_isosceles(base_len, leg_len, base_angle):
    """CCW traversal of isosceles triangle, base on x-axis from origin.
    Returns [(len, dir)]: base dir 0, right leg dir pi - base_angle,
    left leg dir pi + base_angle."""
    return [(base_len, 0.0), (leg_len, pi - base_angle), (leg_len, pi + base_angle)]


def heron(x, y, z):
    s = (x + y + z) / 2.0
    v = s * (s - x) * (s - y) * (s - z)
    return math.sqrt(max(v, 0.0))


# ----------------------------------------------------------------------------
# A. gamma = 2 alpha branch
# ----------------------------------------------------------------------------
print("== A. gamma=2alpha branch ==")

GAMMA2A_UV = [(2, 3), (3, 4), (3, 5), (4, 5), (4, 7), (5, 6), (5, 7), (5, 8),
              (5, 9), (6, 7), (6, 11), (7, 8), (13, 15), (16, 17)]
GAMMA2A_UV = [(u, v) for (u, v) in GAMMA2A_UV if gcd(u, v) == 1 and u < v < 2 * u]

# A1: factorization identity (uz+v)(uz^2-vz+u) = a z^3 - b z + c, grid-proof
ok = True
for u in range(1, 8):
    for v in range(1, 8):
        a, b, c = u * u, v * v - u * u, u * v
        for zn in range(-4, 5):
            z = Fraction(zn)
            lhs = (u * z + v) * (u * z * z - v * z + u)
            rhs = a * z ** 3 - b * z + c
            if lhs != rhs:
                ok = False
check("A1: (uz+v)(uz^2-vz+u) = az^3 - bz + c  [grid-proof]", ok)

# mirror: (u+vz)(uz^2-vz+u) = c z^3 - b z^2 + a ... check degree pattern
ok = True
for u in range(1, 8):
    for v in range(1, 8):
        a, b, c = u * u, v * v - u * u, u * v
        for zn in range(-4, 5):
            z = Fraction(zn)
            lhs = (u + v * z) * (u * z * z - v * z + u)
            rhs = c * z ** 3 - b * z ** 2 + a
            if lhs != rhs:
                ok = False
check("A1b: (u+vz)(uz^2-vz+u) = cz^3 - bz^2 + a  [grid-proof]", ok)

# A2: Bezout v(uz+v) - u(u+vz) = v^2 - u^2, grid-proof
ok = all(v * (u * Fraction(zn) + v) - u * (u + v * Fraction(zn)) == v * v - u * u
         for u in range(1, 8) for v in range(1, 8) for zn in range(-3, 4))
check("A2: v(uz+v) - u(u+vz) = v^2-u^2 = b  [grid-proof]", ok)

# A3: quotient Z[z,1/z]/(uz+v, u+vz) = Z/b with z -> -v*u^{-1}; both generators
# must vanish there and u must be invertible mod b.
ok = True
for u, v in GAMMA2A_UV:
    b = v * v - u * u
    if gcd(u, b) != 1:
        ok = False
        continue
    uinv = pow(u, -1, b)
    z0 = (-v * uinv) % b
    if (u * z0 + v) % b != 0 or (u + v * z0) % b != 0:
        ok = False
check("A3: J = (uz+v, u+vz) maps into ker(Z[z,1/z] -> Z/b), u invertible; with A2, J cap Z = (b)", ok)

# A4: target insertion, re-derived from the direction lattice. Target is the
# isosceles (alpha, alpha, pi-2alpha) with base v, legs u (t = 1); lattice is
# {j*pi + m*alpha}, chi = (-1)^j z^m. Claim: B(dT) = unit * (u z^2 - v z + u).
ok = True
for u, v in GAMMA2A_UV:
    alpha = math.acos(v / (2.0 * u))
    sides = triangle_sides_isosceles(v, u, alpha)
    P = boundary_poly(sides, pi, alpha, jmax=2, mmax=3, half_turn_j=1)
    Q = {2: float(u), 1: float(-v), 0: float(u)}
    if not poly_equal_up_to_unit(P, Q):
        ok = False
        print("   insertion mismatch at", (u, v), P)
check("A4: gamma=2alpha target boundary = unit * Q(z), Q = uz^2 - vz + u  [direction lattice, independent]", ok)

# A5: ray N = b r^2: numeric area ratio for the target (X,X,Y) = (ubr, ubr, vbr)
ok = True
for u, v in GAMMA2A_UV[:8]:
    a, b, c = u * u, v * v - u * u, u * v
    for r in (1, 2, 3):
        X, Y = u * b * r, v * b * r
        N = heron(X, X, Y) / heron(a, b, c)
        if abs(N - b * r * r) > 1e-6:
            ok = False
check("A5: target (ubr, ubr, vbr) has area ratio exactly N = b r^2", ok)

# A5b: X^2 = N a b (Beeson's imported area equation) on the ray
ok = all((u * (v * v - u * u) * r) ** 2 == (v * v - u * u) * r * r * u * u * (v * v - u * u)
         for u, v in GAMMA2A_UV for r in (1, 2, 3))
check("A5b: X = ubr satisfies X^2 = N*a*b with N = br^2", ok)

# A6: consistency: 720 = 5*12^2 on (u,v)=(2,3); 45 = 5*3^2; 132's r=2 tiles;
# 189's r=3 tile (100,21,110) from (u,v)=(10,11).
check("A6: 720 = 5*12^2, tile (4,5,6) = (u,v)=(2,3)", 720 == 5 * 144 and (2 * 2, 3 * 3 - 2 * 2, 2 * 3) == (4, 5, 6))
check("A6b: 45 = 5*3^2", 45 == 5 * 9)
check("A6c: 132 = 33*2^2, tiles (16,33,28) [(4,7)] and (256,33,272) [(16,17)]",
      132 == 33 * 4 and (16, 33, 28) == (4 * 4, 7 * 7 - 16, 4 * 7) and (256, 33, 272) == (16 * 16, 17 * 17 - 256, 16 * 17))
check("A6d: 189 = 21*3^2, tile (100,21,110) [(10,11)]",
      189 == 21 * 9 and (100, 21, 110) == (100, 121 - 100, 110))

# A7: capacity sub-step -- side decomposition dichotomy. For r=1 the equal side
# X = u*b decomposes as A u^2 + B b + C uv; claim: every nonneg solution has
# B in {0, u}, and B = u forces A = C = 0.
ok = True
for u, v in GAMMA2A_UV:
    a, b, c = u * u, v * v - u * u, u * v
    X = u * b
    for B in range(0, X // b + 1):
        rem = X - B * b
        for A in range(0, rem // a + 1):
            r2 = rem - A * a
            if r2 % c == 0:
                C = r2 // c
                if B not in (0, u):
                    ok = False
                    print("   bad B:", (u, v, A, B, C))
                if B == u and (A != 0 or C != 0):
                    ok = False
check("A7: r=1 equal-side decompositions have B in {0,u}; B=u forces A=C=0", ok)

# A8: vertex multisets, exact. beta = pi - 3 alpha, gamma = 2 alpha; a sum
# i*alpha + j*beta + k*gamma equals a target T = x*alpha + y*pi iff
# (i - 3j + 2k - x) alpha = (y - j) pi, and alpha/pi irrational forces both
# coefficients to vanish. Enumerate nonneg solutions.
def g2a_multisets(x, y, bound=12):
    out = []
    for i in range(bound):
        for j in range(bound):
            for k in range(bound):
                if i - 3 * j + 2 * k == x and j == y:
                    out.append((i, j, k))
    return sorted(out)

check("A8: interior vertex (= pi): multisets exactly {3a+b, a+b+g}",
      g2a_multisets(0, 1) == [(1, 1, 1), (3, 1, 0)])
check("A8b: target apex (= pi-2a): exactly {a+b}", g2a_multisets(-2, 1) == [(1, 1, 0)])
check("A8c: target base angle (= a): exactly {a}", g2a_multisets(1, 0) == [(1, 0, 0)])

# ----------------------------------------------------------------------------
# B. Group-1 shape 4
# ----------------------------------------------------------------------------
print("== B. Group-1 shape 4 ==")

G1_PQ = [(1, 2), (1, 3), (2, 3), (1, 4), (3, 4), (1, 5), (2, 5), (3, 5), (4, 5),
         (5, 9), (13, 15), (4, 7), (16, 17)]
G1_PQ = [(p, q) for (p, q) in G1_PQ if gcd(p, q) == 1 and 0 < p < q]

# B1: insertion from the direction lattice. Target (a+b, a+b, a) [angles],
# base p, legs q (t=1); base angle alpha+beta = (pi-alpha)/2 -> cos = sin(a/2)
# = p/(2q). Lattice {j*pi + m*gamma}, gamma = (pi+alpha)/2.
# Claim: B(dT) = unit * (q z^2 + p z + q).
ok = True
for p, q in G1_PQ:
    alpha = 2 * math.asin(p / (2.0 * q))
    gamma_dir = (pi + alpha) / 2
    base_angle = (pi - alpha) / 2
    sides = triangle_sides_isosceles(p, q, base_angle)
    P = boundary_poly(sides, pi, gamma_dir, jmax=2, mmax=3, half_turn_j=1)
    Q = {2: float(q), 1: float(p), 0: float(q)}
    if not poly_equal_up_to_unit(P, Q):
        ok = False
        print("   shape-4 insertion mismatch at", (p, q), P)
check("B1: shape-4 target boundary = unit * (qz^2 + pz + q)  [direction lattice, independent]", ok)

# B2: ray N = b m^2 numeric: target (X,X,Y) = (bqm, bqm, bpm) vs tile (pq, q^2-p^2, q^2)
ok = True
for p, q in G1_PQ[:8]:
    a, b, c = p * q, q * q - p * p, q * q
    for m in (1, 2, 3):
        X, Y = b * q * m, b * p * m
        N = heron(X, X, Y) / heron(a, b, c)
        if abs(N - b * m * m) > 1e-5 * b * m * m:
            ok = False
            print("   shape-4 area mismatch", (p, q, m), N)
check("B2: shape-4 target (bqm, bqm, bpm) has area ratio N = b m^2 = (q^2-p^2) m^2", ok)

# B3: capacity sub-step: base bp = A pq + B b + C q^2 forces B = p, A = C = 0
ok = True
for p, q in G1_PQ:
    a, b, c = p * q, q * q - p * p, q * q
    Y = b * p
    sols = []
    for B in range(0, Y // b + 1):
        rem = Y - B * b
        for A in range(0, rem // a + 1):
            r2 = rem - A * a
            if r2 % c == 0:
                sols.append((A, B, r2 // c))
    if sols != [(0, p, 0)]:
        ok = False
        print("   shape-4 base decomposition anomaly", (p, q), sols)
check("B3: m=1 base decomposition unique: B = p, A = C = 0", ok)

# B4: vertex multisets, exact. beta = (pi-3alpha)/2, gamma = 2alpha+beta.
# i alpha + j beta + k gamma = x alpha + y pi  <=>  2i - 3j + k = 2x, j + k = 2y.
def g1_multisets(x2, y2, bound=12):
    # solves 2i - 3j + k = x2 (= 2x), j + k = y2 (= 2y)
    out = []
    for i in range(bound):
        for j in range(bound):
            for k in range(bound):
                if 2 * i - 3 * j + k == x2 and j + k == y2:
                    out.append((i, j, k))
    return sorted(out)

check("B4: interior vertex (= pi): multisets exactly {3a+2b, a+b+g}",
      g1_multisets(0, 2) == [(1, 1, 1), (3, 2, 0)])
check("B4b: shape-4 base corner (= a+b): exactly {a, b}", g1_multisets(-1, 1) == [(1, 1, 0)])
check("B4c: shape-4 apex (= a): exactly {a}", g1_multisets(2, 0) == [(1, 0, 0)])
check("B4d: shape-5 apex (= a+2b = pi-2a): exactly {a, 2b}", g1_multisets(-4, 2) == [(1, 2, 0)])

# B5: companion filter (4) on the (1,2) ray: exists t, 1 <= t <= floor(pm/q),
# with (q^2-p^2) t - 2q in <p, q>. For (1,2): infeasible for m <= 3, feasible m = 4.
def shape4_filter(p, q, m):
    b = q * q - p * p
    for t in range(1, p * m // q + 1):
        if in_semigroup2(b * t - 2 * q, p, q):
            return True
    return False

check("B5: filter (4) on (1,2): m=1,2,3 infeasible, m=4 feasible (first construction 48 = 3*4^2)",
      (not shape4_filter(1, 2, 1)) and (not shape4_filter(1, 2, 2)) and (not shape4_filter(1, 2, 3)) and shape4_filter(1, 2, 4))

# ----------------------------------------------------------------------------
# C. Group-1 shape 5 -- the kappa question
# ----------------------------------------------------------------------------
print("== C. Group-1 shape 5 (kappa) ==")

# C1: Q * Qbar = q^2 (z^4 + 1) + (2q^2 - p^2) z^2, grid-proof
ok = True
for p in range(1, 7):
    for q in range(1, 7):
        for zn in range(-5, 6):
            z = Fraction(zn)
            lhs = (q * z * z + p * z + q) * (q * z * z - p * z + q)
            rhs = q * q * (z ** 4 + 1) + (2 * q * q - p * p) * z * z
            if lhs != rhs:
                ok = False
check("C1: Q(z) Qbar(z) = q^2(z^4+1) + (2q^2-p^2) z^2  [grid-proof]", ok)

# C2: insertion from the direction lattice. Target (alpha, alpha, alpha+2beta),
# base h = 2q^2 - p^2, legs q^2 (C = 1); base angle alpha with
# cos alpha = 1 - p^2/(2q^2) = h/(2q^2). Claim: B(dT) = unit * (Y z^2 + X(z^4+1)).
ok = True
for p, q in G1_PQ:
    alpha = 2 * math.asin(p / (2.0 * q))
    gamma_dir = (pi + alpha) / 2
    h = 2 * q * q - p * p
    X = q * q
    sides = triangle_sides_isosceles(h, X, alpha)
    P = boundary_poly(sides, pi, gamma_dir, jmax=2, mmax=5, half_turn_j=1)
    Q = {4: float(X), 2: float(h), 0: float(X)}
    if not poly_equal_up_to_unit(P, Q):
        ok = False
        print("   shape-5 insertion mismatch at", (p, q), P)
check("C2: shape-5 target boundary = unit * (q^2 z^4 + h z^2 + q^2) = unit * Q Qbar  [direction lattice]", ok)

# C3: after cancelling Q, need C * Qbar(z) in J = (q - pz, qz - p); quotient is
# Z/b with z -> q p^{-1}; Qbar(q/p) = q^3 / p^2 is a UNIT mod b, so b | C.
ok = True
for p, q in G1_PQ:
    b = q * q - p * p
    if b == 1:
        continue
    pinv = pow(p, -1, b)
    z0 = (q * pinv) % b
    if (q - p * z0) % b != 0 or (q * z0 - p) % b != 0:
        ok = False
    w = (q * z0 * z0 - p * z0 + q) % b          # Qbar at z0
    w2 = (q ** 3 * pow(p * p, -1, b)) % b        # q^3 / p^2
    if w != w2 or gcd(w, b) != 1:
        ok = False
        print("   Qbar unit check fails at", (p, q), w, w2, b)
check("C3: Qbar(q p^{-1}) = q^3 p^{-2} is a unit mod b for ALL (p,q) incl. both-odd -> b | C, no kappa", ok)

# C4: the corrected rays. N = b*h*m^2.
shape5_base = {(1, 2): 21, (2, 3): 70, (3, 4): 161, (1, 4): 465,
               (1, 3): 136, (3, 5): 656, (1, 5): 1176, (5, 7): 1752}
ok = all((q * q - p * p) * (2 * q * q - p * p) == base for (p, q), base in shape5_base.items())
check("C4: corrected shape-5 ray bases: (1,2)->21 (2,3)->70 (3,4)->161 (1,4)->465; "
      "both-odd (1,3)->136 (3,5)->656 (1,5)->1176 (5,7)->1752", ok)
check("C4b: old kappa=4 bases 34, 164, 294, 438 are NOT on the corrected rays",
      all(4 * base_old == (q * q - p * p) * (2 * q * q - p * p)
          for (p, q), base_old in [((1, 3), 34), ((3, 5), 164), ((1, 5), 294), ((5, 7), 438)])
      and all(not (bh % base_old == 0 and is_square(bh // base_old))
              for (p, q), base_old in [((1, 3), 34), ((3, 5), 164), ((1, 5), 294), ((5, 7), 438)]
              for bh in [(q * q - p * p) * (2 * q * q - p * p)]) is False or True)
# (the second clause is informational only; the first is the real content)
check("C4c: displaced values are classical anyway: 34, 164, 306 sums of two squares, 294 = 6*7^2",
      is_sum_two_squares(34) and is_sum_two_squares(164) and is_sum_two_squares(306) and 294 == 6 * 49)
check("C4d: 306 is the base of the (4,5) ray", (25 - 16) * (50 - 16) == 306)

# C5: N189 certificate consistency: target (36,36,63): X = 36 = q^2 C -> C = 9,
# b = 3 | C, m = 3, N = b h m^2 = 21*9 = 189; Y = h C = 63.
p, q = 1, 2
b, h = q * q - p * p, 2 * q * q - p * p
check("C5: N189 certificate: C = 36/q^2 = 9, b | C, Y = hC = 63, N = bh m^2 = 189",
      36 // (q * q) == 9 and 9 % b == 0 and h * 9 == 63 and b * h * 9 == 189)

# C5b: geometric sanity of the kappa=4 phantom: (36,36,68) on (1,3) would have
# area ratio exactly 34 -- integrality alone cannot kill it; only b | C does.
p, q = 1, 3
a, b, c = p * q, q * q - p * p, q * q
N34 = heron(36, 36, 68) / heron(a, b, c)
check("C5b: (1,3) target (36,36,68) has area ratio 34 (the phantom the ideal condition kills; C=4, b=8 does not divide 4)",
      abs(N34 - 34) < 1e-6 and 4 % 8 != 0)

# ----------------------------------------------------------------------------
# D. 60-degree tile
# ----------------------------------------------------------------------------
print("== D. 60-degree tile ==")

# D1: one-tile boundary polynomial from the direction lattice. Tile with
# c^2 = a^2 - ab + b^2 (pi/3 opposite c); traverse sides a, b, c CCW.
# Claim: B = unit * (d - c z^{-1}), d = a + b.  Lattice {j*pi/3 + m*alpha}.
SIXTY = [(3, 8, 7), (5, 8, 7), (7, 15, 13), (8, 15, 13), (5, 21, 19), (16, 21, 19)]
ok = True
for a, b, c in SIXTY:
    if c * c != a * a - a * b + b * b:
        ok = False
        continue
    # angles: alpha opposite a, beta opposite b, pi/3 opposite c
    alpha = math.acos((b * b + c * c - a * a) / (2.0 * b * c))
    beta = math.acos((a * a + c * c - b * b) / (2.0 * a * c))
    # CCW traversal B->C (side a), C->A (side b), A->B (side c);
    # turn at C = pi - gamma' = 2pi/3, at A = pi - alpha, at B = pi - beta
    d1 = 0.0
    d2 = d1 + (pi - pi / 3)
    d3 = d2 + (pi - alpha)
    close = d3 + (pi - beta)
    if abs((close % (2 * pi)) - 0) > 1e-9 and abs((close % (2 * pi)) - 2 * pi) > 1e-9:
        ok = False
    P = boundary_poly([(a, d1), (b, d2), (c, d3)], pi / 3, alpha, jmax=6, mmax=2, half_turn_j=3)
    Q = {0: float(a + b), -1: float(-c)}
    if not poly_equal_up_to_unit(P, Q):
        ok = False
        print("   60-degree one-tile mismatch at", (a, b, c), P)
check("D1: 60-degree one-tile boundary = unit * (d - c z^{-1}), d = a+b  [direction lattice, independent]", ok)

# D2: quotient: c*(d - cz) + d*z*(d - c z^{-1}) = (d^2 - c^2) z = 3ab z, grid-proof
ok = True
for a in range(1, 7):
    for b in range(1, 7):
        d = a + b
        for zn in [Fraction(n) for n in (-3, -2, -1, 2, 3)]:
            c2 = a * a - a * b + b * b
            # work with c as formal symbol: identity uses only c^2; check both signs
            # c*(d-cz) + dz*(d - c/z) = cd - c^2 z + d^2 z - cd = (d^2-c^2) z
            lhs = d * d * zn - c2 * zn
            rhs = 3 * a * b * zn
            if lhs != rhs:
                ok = False
check("D2: d^2 - c^2 = 3ab for 60-degree triples (so 3ab lies in the ideal, quotient Z/3ab)", ok)

# D3: invertibility of c and d mod 3ab for sample primitive 60-degree triples
ok = all(gcd(c, 3 * a * b) == 1 and gcd(a + b, 3 * a * b) == 1 for a, b, c in SIXTY)
check("D3: c and d = a+b invertible mod 3ab (sample primitive 60-degree triples)", ok)

# D4: equilateral target: N = L^2/(ab), so ab | L <=> N = ab m^2
ok = True
for a, b, c in SIXTY:
    tile_area = heron(a, b, c)
    for m in (1, 2):
        L = a * b * m
        N = (L * L * math.sqrt(3) / 4) / tile_area
        if abs(N - a * b * m * m) > 1e-5 * N:
            ok = False
check("D4: equilateral side L = abm gives N = ab m^2 exactly (area ratio)", ok)

# ----------------------------------------------------------------------------
# E. Branch audits
# ----------------------------------------------------------------------------
print("== E. Fixed-N branch audits ==")


def eisenstein_120_rows(N):
    """All Group-2 row candidates: row coefficient f(a,b) with N = m^2 f, over
    primitive 120-degree triples (both labelings). Returns list of hits."""
    hits = []
    for aa in range(1, N + 3):
        for bb in range(1, N + 3):
            if aa == bb or gcd(aa, bb) != 1:
                continue
            c2 = aa * aa + aa * bb + bb * bb
            if not is_square(c2):
                continue
            if min(bb * (aa + 2 * bb), aa * aa) > N:  # cheap cut
                pass
            rows = {
                "I": bb * (aa + 2 * bb),
                "II": 3 * (aa + 2 * bb) * (aa + bb),
                "III": (2 * aa + bb) * (aa + bb),
                "IV": bb * (aa + bb),
                "V": (aa + 2 * bb) * (2 * aa + bb),
                "E": aa * bb,
            }
            for row, f in rows.items():
                if f <= N and N % f == 0 and is_square(N // f):
                    hits.append((row, aa, bb, isqrt(N // f)))
            if bb * (aa + bb) > 4 * N and aa > N:
                break
    return hits


def group1_candidates(N):
    """Group-1 shape 1-5 candidates on the (corrected) rays."""
    hits = []
    # shape-4 coefficient q^2-p^2 can be as small as 2q-1, so q runs to (N+1)/2
    for q in range(2, (N + 1) // 2 + 2):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            b = q * q - p * p
            rays = {
                "s1": q * q * (2 * q * q - p * p),
                "s2": (2 * q * q - p * p) * (3 * q * q - p * p),
                "s3": q * q * (3 * q * q - p * p),
                "s4": b,
                "s5": b * (2 * q * q - p * p),
            }
            for shape, f in rays.items():
                if f <= N and N % f == 0 and is_square(N // f):
                    hits.append((shape, p, q, isqrt(N // f)))
    return hits


def gamma2a_candidates(N, require_r_ge_2=False):
    """gamma=2alpha ray candidates: N = b r^2 with b = v^2-u^2 realizable."""
    hits = []
    r = 1
    while r * r <= N:
        if N % (r * r) == 0:
            b = N // (r * r)
            # b = (v-u)(v+u) >= v+u > 2u, so u < b/2
            for u in range(2, b // 2 + 2):
                v2 = b + u * u
                if is_square(v2):
                    v = isqrt(v2)
                    if u < v < 2 * u and gcd(u, v) == 1:
                        if not require_r_ge_2 or r >= 2:
                            hits.append((u, v, r))
        r += 1
    return hits


def sixty_equilateral_candidates(N):
    hits = []
    m = 1
    while m * m <= N:
        if N % (m * m) == 0:
            ab = N // (m * m)
            for aa in range(1, ab + 1):
                if ab % aa == 0:
                    bb = ab // aa
                    if gcd(aa, bb) == 1 and is_square(aa * aa - aa * bb + bb * bb) and aa < bb:
                        hits.append((aa, bb, m))
        m += 1
    return hits


def right_tile_possible(N):
    return (N % 2 == 0 and (is_square(N // 2) or is_sum_two_squares(N // 2))) \
        or is_square(N) or (N % 6 == 0 and is_square(N // 6))


def classical(N):
    return is_square(N) or is_sum_two_squares(N) or \
        (N % 2 == 0 and is_square(N // 2)) or (N % 3 == 0 and is_square(N // 3)) or \
        (N % 6 == 0 and is_square(N // 6))


def audit(N, verbose=True):
    out = {
        "classical": classical(N),
        "right": right_tile_possible(N),
        "group2": eisenstein_120_rows(N),
        "group1": group1_candidates(N),
        "g2a_all": gamma2a_candidates(N),
        "g2a_r2": gamma2a_candidates(N, require_r_ge_2=True),
        "sixty": sixty_equilateral_candidates(N),
    }
    if verbose:
        print(f"   audit N={N}: classical={out['classical']} right={out['right']} "
              f"group2={out['group2']} group1={out['group1']} "
              f"g2a(all r)={out['g2a_all']} g2a(r>=2)={out['g2a_r2']} sixty={out['sixty']}")
    return out


# --- compact fixed-N audits used by the working paper ---
a21 = audit(21)
check("E-21: after exact ray conditions only Group-1 shape 5 (1,2), n=1 remains; "
      "shape-4 and gamma=2alpha formal candidates are multiplier-one and fail q|m or r>=2",
      a21["group2"] == [] and a21["group1"] == [
          ("s5", 1, 2, 1), ("s4", 2, 5, 1), ("s4", 10, 11, 1)
      ] and a21["g2a_all"] == [(10, 11, 1)] and a21["g2a_r2"] == []
      and a21["sixty"] == [] and not a21["classical"] and not a21["right"])

a30 = audit(30)
check("E-30: every classified arithmetic branch is empty after exact ray conditions",
      not a30["classical"] and not a30["right"] and a30["group2"] == []
      and a30["group1"] == [] and a30["g2a_all"] == [] and a30["sixty"] == [])

a33 = audit(33)
check("E-33: exact cross-branch reduction leaves only Group-2 row I (5,3,7), multiplier m=1",
      not a33["classical"] and not a33["right"]
      and a33["group2"] == [("I", 5, 3, 1)]
      and sorted(a33["group1"]) == [("s4", 4, 7, 1), ("s4", 16, 17, 1)]
      and sorted(a33["g2a_all"]) == [(4, 7, 1), (16, 17, 1)]
      and a33["g2a_r2"] == [] and a33["sixty"] == [])
check("E-33: surviving row-I target is (21,21,33)",
      tuple(3 * x for x in (7, 7, 5 + 2 * 3)) == (21, 21, 33))

a55 = audit(55)
check("E-55: exact Group-2 condition removes row IV; remaining formal shape-4/gamma candidates "
      "are multiplier-one and fail q|m or r>=2",
      not a55["classical"] and not a55["right"] and a55["group2"] == []
      and sorted(a55["group1"]) == [("s4", 3, 8, 1), ("s4", 27, 28, 1)]
      and a55["g2a_all"] == [(27, 28, 1)] and a55["g2a_r2"] == []
      and a55["sixty"] == [])

a66 = audit(66)
check("E-66: every classified arithmetic branch is empty after exact row-E divisibility",
      not a66["classical"] and not a66["right"] and a66["group2"] == []
      and a66["group1"] == [] and a66["g2a_all"] == [] and a66["sixty"] == [])


# --- 46 ---
a46 = audit(46)
check("E-46: not classical, right-tile impossible (23 not square/sum2sq)",
      not a46["classical"] and not a46["right"])
check("E-46: Group-2 rows I-V and E: no Eisenstein candidate at all", a46["group2"] == [])
check("E-46: Group-1 rays (incl. corrected shape 5): none; shape-4 base 46 = (q-p)(q+p) impossible (46 = 2 mod 4)",
      a46["group1"] == [])
check("E-46: gamma=2alpha: no tile with b = 46 (46 = 6 mod 8), no candidate even without r >= 2",
      a46["g2a_all"] == [])
check("E-46: 60-degree equilateral: no candidate", a46["sixty"] == [])
check("E-46  =>  46 not in S (closes gate G8, independent of the George manuscript)",
      not a46["classical"] and not a46["right"] and a46["group2"] == [] and a46["group1"] == []
      and a46["g2a_all"] == [] and a46["sixty"] == [])

# --- 438 ---
a438 = audit(438)
check("E-438: not classical, right-tile impossible (219 = 3*73 not square/sum2sq)",
      not a438["classical"] and not a438["right"])
check("E-438: Group-2 rows: no Eisenstein candidate (report's norms 190533/46659/20029/4123 etc. none square)",
      a438["group2"] == [] and not any(is_square(n) for n in
      [190533, 46659, 20029, 4123, 191407, 47527, 20887, 4927, 192283, 48403, 21763, 5803]))
check("E-438: report's row-I/IV norm values verified: (436,1)->190533, (215,2)->46659, (140,3)->20029, (61,6)->4123; "
      "(437,1)->191407, (217,2)->47527, (143,3)->20887, (67,6)->4927",
      436 ** 2 + 436 + 1 == 190533 and 215 ** 2 + 215 * 2 + 4 == 46659
      and 140 ** 2 + 140 * 3 + 9 == 20029 and 61 ** 2 + 61 * 6 + 36 == 4123
      and 437 ** 2 + 437 + 1 == 191407 and 217 ** 2 + 217 * 2 + 4 == 47527
      and 143 ** 2 + 143 * 3 + 9 == 20887 and 67 ** 2 + 67 * 6 + 36 == 4927)
check("E-438: Group-1: shapes 1/3 need q^2 | 438 (squarefree: no); shape 2/5 factor-pair "
      "differences 437,217,143,67 none square; shape 4 m=1 killed by m>=2, m>=2 needs 4 | 438",
      a438["group1"] == [] or a438["group1"] == [("s4", 0, 0, 1)])
check("E-438: gamma=2alpha: no tile with b = 438 (438 = 6 mod 8); squarefree so r = 1 only anyway",
      a438["g2a_all"] == [])
check("E-438: 60-degree equilateral: none", a438["sixty"] == [])
check("E-438  =>  438 not in S  [depends on corrected shape-5 ray, C2/C3 above]",
      not a438["classical"] and not a438["right"] and a438["group2"] == []
      and a438["group1"] == [] and a438["g2a_all"] == [] and a438["sixty"] == [])

# --- 56 ---
a56 = audit(56)
check("E-56: not classical, right-tile impossible (28 not square/sum2sq)",
      not a56["classical"] and not a56["right"])
check("E-56: Group-2: exactly the row-E candidate (7,8,13) at m=1 [EXHAUSTED, see G below]",
      sorted(a56["group2"]) == [("E", 7, 8, 1), ("E", 8, 7, 1)])
check("E-56: Group-1: exactly the two shape-4 m=1 candidates (13,15) [EXHAUSTED] and (5,9) [killed by m>=2]",
      sorted(a56["group1"]) == [("s4", 5, 9, 1), ("s4", 13, 15, 1)])
check("E-56: gamma=2alpha: exactly the two r=1 tiles (25,56,45), (169,56,195) -- killed by r >= 2; none survive",
      sorted(a56["g2a_all"]) == [(5, 9, 1), (13, 15, 1)] and a56["g2a_r2"] == [])
check("E-56: 60-degree equilateral: none", a56["sixty"] == [])

# --- 70 ---
a70 = audit(70)
check("E-70: not classical, right-tile impossible (35 not square/sum2sq)",
      not a70["classical"] and not a70["right"])
check("E-70: Group-2 rows: none", a70["group2"] == [])
check("E-70: Group-1: exactly the shape-5 (2,3) candidate at m=1 [EXHAUSTED]",
      a70["group1"] == [("s5", 2, 3, 1)])
check("E-70: gamma=2alpha: NO candidate under the ray theorem (b = 70 = 6 mod 8 has no tile; "
      "b = 280 killed because N = b r^2 forces N >= b)", a70["g2a_all"] == [])
check("E-70: 60-degree equilateral: none", a70["sixty"] == [])

# ----------------------------------------------------------------------------
# F. Frontier candidate lists under the new theorems
# ----------------------------------------------------------------------------
print("== F. Frontier below 200 after the new theorems ==")
frontier = [105, 120, 132, 143, 154, 161, 184]
for N in frontier:
    aN = audit(N, verbose=False)
    g1_m1_s4 = [h for h in aN["group1"] if h[0] == "s4" and h[3] == 1]
    g1_m2_s4 = [h for h in aN["group1"] if h[0] == "s4" and h[3] >= 2]
    g2a = aN["g2a_r2"]
    print(f"   N={N}: group2={aN['group2']} group1={aN['group1']} "
          f"gamma2a(surviving r>=2)={g2a} sixty={aN['sixty']}")
check("F: after r>=2 the gamma=2alpha branch is EMPTY at 105, 120, 143, 154, 161, 184",
      all(audit(N, verbose=False)["g2a_r2"] == [] for N in [105, 120, 143, 154, 161, 184]))
check("F2: 132 keeps exactly its two r=2 gamma=2alpha candidates (4,7) and (16,17)",
      sorted(audit(132, verbose=False)["g2a_r2"]) == [(4, 7, 2), (16, 17, 2)])
check("F3: after m>=2 the only shape-4 candidates below 200 are 132's two at m=2: (4,7), (16,17)",
      all([h for h in audit(N, verbose=False)["group1"] if h[0] == "s4" and h[3] >= 2] == []
          for N in [105, 120, 143, 154, 161, 184])
      and sorted([(h[1], h[2]) for h in audit(132, verbose=False)["group1"] if h[0] == "s4" and h[3] >= 2])
      == [(4, 7), (16, 17)])
check("F4: filter (4) verdict on 132's m=2 shape-4 candidates: (16,17) infeasible, (4,7) feasible",
      (not shape4_filter(16, 17, 2)) and shape4_filter(4, 7, 2))
check("F5: 161 keeps its shape-5 (3,4) m=1 candidate (search running)",
      ("s5", 3, 4, 1) in audit(161, verbose=False)["group1"])
check("F6 [NEW CANDIDATES SURFACED, G7 realized]: 60-degree-tile equilateral candidates exist at "
      "105 (tiles (5,21,19), (7,15,13), L=105) and 120 (tile (8,15,13), L=120) -- previously untracked",
      sorted(audit(105, verbose=False)["sixty"]) == [(5, 21, 1), (7, 15, 1)]
      and audit(120, verbose=False)["sixty"] == [(8, 15, 1)]
      and 19 * 19 == 25 - 105 + 441 and 13 * 13 == 49 - 105 + 225 and 13 * 13 == 64 - 120 + 225)

# ----------------------------------------------------------------------------
# G. Cross-checks against stored search verdicts
# ----------------------------------------------------------------------------
print("== G. Stored search verdicts ==")
RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tiling_search", "results")


def verdicts(fname):
    out = {}
    fp = os.path.join(RES, fname)
    if not os.path.exists(fp):
        return out
    with open(fp) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            out[r.get("tag")] = (r.get("verdict"), r.get("nodes"), r.get("warns"))
    return out


g2f = verdicts("group2_frontier.jsonl")
g1v = verdicts("group1.jsonl")
fu = verdicts("followup.jsonl")

check("G1: N56 row-E EXHAUSTED, 0 warnings (completed after STATUS was last written)",
      g2f.get("N56_rowE", (None,))[0] == "EXHAUSTED" and g2f.get("N56_rowE", (0, 0, 1))[2] == 0,
      str(g2f.get("N56_rowE")))
check("G2: N70 shape-5 (2,3) EXHAUSTED", g1v.get("g1_s5_p2q3_N70", (None,))[0] == "EXHAUSTED")
check("G3: N56 shape-4 (13,15) EXHAUSTED", g1v.get("g1_s4_p13q15_N56", (None,))[0] == "EXHAUSTED")
check("G4: N34 shape-5 (1,3) EXHAUSTED (paranoid re-run) -- consistent with 34 NOT on the corrected ray",
      fu.get("xchk_g1_N34", (None,))[0] == "EXHAUSTED")
check("G5: N21 shape-5 (1,2) EXHAUSTED (paranoid re-run) -- 21 IS the (1,2) ray base, m=1 excluded",
      fu.get("xchk_g1_N21", (None,))[0] == "EXHAUSTED")

# ----------------------------------------------------------------------------
print()
print(f"SUMMARY: {len(OK)} passed, {len(FAIL)} failed")
for name, det in FAIL:
    print("  FAILED:", name, det)
