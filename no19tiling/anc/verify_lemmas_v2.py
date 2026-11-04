#!/usr/bin/env python3
"""Exact checks of the algebra and arithmetic of the lemmas of version 2 of

  "No triangle can be cut into nineteen congruent triangles:
   the prime case of Erdos Problem 634"

Lemmas are referred to by the LaTeX labels of no19tiling.tex: lem:group2 ("Group-2
tiles"), lem:rowI ("Isosceles and equilateral targets"), lem:g1tile ("Group-1 tiles"),
lem:g1counts ("Group-1 count equations"), lem:g1residues ("Residues"), lem:shape4,
lem:shape5 (the shapes (alpha+beta, alpha+beta, alpha) and (alpha, alpha, alpha+2beta)),
lem:character ("Boundary character").

Run:    python3 verify_lemmas_v2.py [--tilings DIR]
   or:  uv run --with sympy python verify_lemmas_v2.py [--tilings DIR]

Requires Python >= 3.10 and SymPy.  All arithmetic is exact (SymPy expressions, Python
integers and Fractions); there is no floating point.  The proofs are in the paper; this
script checks their algebra and stress-tests their arithmetic claims.  Finite tests are
error detection, not proofs, except where marked as complete enumerations.

  1. Group-1 tile and target triangles (lem:g1tile, lem:g1counts, lem:shape4, lem:shape5):
     the side vectors are checked against the law of cosines with the exact
     cosines of all angles as polynomials in s = sin(alpha/2) = m/(2k), and the
     tile counts against Heron's formula.  Both are polynomial identities in m, k.
  2. Group-2 targets (lem:rowI and the four cases of lem:group2): same two checks on the
     rational parametrization of c^2 = a^2+ab+b^2 (an identity on a Zariski-dense
     subset of the conic).
  3. gcd (primitivity) claims over finite ranges.
  4. Residue claims of lem:g1residues: complete residue enumeration mod 8 and mod 3 (a
     proof of the residue facts), plus the primes p = 3 mod 4 below 5000 that the two
     Group-1 forms actually represent (shows the congruences are sharp).
  5. lem:shape4: brute-force enumeration of all base decompositions in the prime case
     for 0 < m < k <= 80.
  6. lem:shape5 (elementary part): prime counts force N = k^2 + t^2.
  7. Boundary characters (lem:character, lem:rowI, lem:shape5): tile and target boundary
     polynomials are recomputed from the turning-angle rule, the evaluation maps are
     checked symbolically, and the divisibility conclusions are stress-tested.
  8. Optional (needs --tilings DIR): the identity sum_t B(dt) = B(dT) and the predicted
     direct/reflected tile values on exact tilings stored as JSON files in DIR (or
     DIR/external): N = 63, 99, 189 (Group 1) and N = 88, 143, 77 (Group 2).  The
     tilings are not part of this folder.
  9. The three numerical examples quoted in the remarks of the paper.

Nothing here replaces the geometric arguments (boundary decomposition, angle counts,
the imported classification theorems), which are not checked by computation.
"""
from __future__ import annotations

import ast
import json
import math
import argparse
import sys
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

TILINGS_DIR: Path | None = None  # set by --tilings

FAILURES: list[str] = []


def check(cond: bool, label: str) -> None:
    if not cond:
        FAILURES.append(label)
        print(f"  FAIL  {label}")


def ok(label: str) -> None:
    print(f"  ok    {label}")


def heron16(x, y, z):
    """16 * area^2 of a triangle with sides x, y, z."""
    return sp.expand((x + y + z) * (-x + y + z) * (x - y + z) * (x + y - z))


def law_of_cosines_ok(sides, cosines) -> bool:
    """sides[i] is opposite the angle with cosine cosines[i]."""
    x, y, z = sides
    for (p, q, r), cp in (((x, y, z), cosines[0]), ((y, z, x), cosines[1]), ((z, x, y), cosines[2])):
        if sp.simplify(sp.together(p**2 - (q**2 + r**2 - 2 * q * r * cp))) != 0:
            return False
    return True


# ---------------------------------------------------------------------------
# 1. Group 1
# ---------------------------------------------------------------------------
m, k, j, t = sp.symbols("m k j t", positive=True)
th = sp.symbols("theta")


def group1_symbolic() -> None:
    print("\n[1] Group-1 side vectors and counts (Lemmas lem:g1tile, lem:g1counts, lem:shape4, lem:shape5)")
    # trig facts used in the proof of Lemma lem:g1tile: with theta = alpha/2,
    # alpha = 2 theta, beta = pi/2 - 3 theta, gamma = pi/2 + theta.
    alpha, beta, gamma = 2 * th, sp.pi / 2 - 3 * th, sp.pi / 2 + th
    check(sp.simplify(3 * alpha + 2 * beta - sp.pi) == 0, "3alpha+2beta=pi")
    check(sp.simplify(alpha + beta + gamma - sp.pi) == 0, "angle sum")
    # a/c = sin(2th)/cos(th) = 2 sin th ; b/c = cos(3th)/cos(th) = 1 - 4 sin^2 th
    r1 = sp.simplify(sp.expand_trig(sp.sin(alpha) - 2 * sp.sin(th) * sp.sin(gamma)))
    r2 = sp.simplify(sp.expand_trig(sp.sin(beta) - (1 - 4 * sp.sin(th) ** 2) * sp.sin(gamma)))
    check(r1 == 0 and r2 == 0, "a/c = 2 sin(theta), b/c = 1 - 4 sin^2(theta)")
    ok("law of sines ratios a/c = 2 sin(alpha/2), b/c = 1 - (a/c)^2")

    # exact cosines as polynomials in s = sin(theta)
    s = m / (2 * k)
    cos = {
        "alpha": 1 - 2 * s**2,                  # cos 2th
        "beta": 3 * s - 4 * s**3,               # cos(pi/2 - 3th) = sin 3th
        "gamma": -s,                            # cos(pi/2 + th)
        "2alpha": 1 - 8 * s**2 + 8 * s**4,      # cos 4th
        "alpha+beta": s,                        # cos(pi/2 - th)
        "3alpha": sp.expand(sp.chebyshevt(3, 1 - 2 * s**2)),  # cos 6th = T3(cos 2th)
        "2beta": -sp.expand(sp.chebyshevt(3, 1 - 2 * s**2)),  # 2beta = pi - 6th
        "alpha+2beta": -(1 - 8 * s**2 + 8 * s**4),            # pi - 4th
    }
    # spot-check the cosine table against sympy trig with a numeric-free identity
    s_sym = sp.sin(th)
    table_trig = {
        "alpha": sp.cos(alpha), "beta": sp.cos(beta), "gamma": sp.cos(gamma),
        "2alpha": sp.cos(2 * alpha), "alpha+beta": sp.cos(alpha + beta),
        "3alpha": sp.cos(3 * alpha), "2beta": sp.cos(2 * beta), "alpha+2beta": sp.cos(alpha + 2 * beta),
    }
    for name, expr in table_trig.items():
        poly_in_s = cos[name].subs(m, 2 * k * sp.Symbol("S")).subs(sp.Symbol("S"), s_sym)
        diff = sp.simplify(sp.expand_trig(expr - poly_in_s))
        check(diff == 0, f"cos({name}) as polynomial in sin(theta)")
    ok("cosine table of all Group-1 angles as polynomials in sin(alpha/2)")

    a, b, c = m * k, k**2 - m**2, k**2
    h, g = 2 * k**2 - m**2, 3 * k**2 - m**2
    check(law_of_cosines_ok((a, b, c), (cos["alpha"], cos["beta"], cos["gamma"])), "tile (mk, k^2-m^2, k^2)")
    ok("tile (mk, k^2-m^2, k^2) has angles (alpha, beta, gamma) with sin(alpha/2) = m/(2k)")

    tile16 = heron16(a, b, c)
    shapes = [
        # name, angles (opposite the listed sides), primitive side vector, scale, claimed N
        ("triquadratic (2a,b,a+b)", ("2alpha", "beta", "alpha+beta"), (m * h, k * b, k**3), j, j**2 * h),
        ("isosceles-beta (b,b,3a)", ("beta", "beta", "3alpha"), (k**3, k**3, m * g), j, j**2 * g),
        ("(a,2a,2b)", ("alpha", "2alpha", "2beta"), (k**4, k**2 * h, b * g), j, j**2 * h * g),
        ("shape 4 (a+b,a+b,a)", ("alpha+beta", "alpha+beta", "alpha"), (k, k, m), t, t**2 / b),
        ("shape 5 (a,a,a+2b)", ("alpha", "alpha", "alpha+2beta"), (k**2, k**2, h), t, t**2 * h / b),
    ]
    for name, angs, vec, scale, N in shapes:
        sides = tuple(scale * v for v in vec)
        lc = law_of_cosines_ok(sides, tuple(cos[x] for x in angs))
        her = sp.simplify(sp.together(heron16(*sides) - N**2 * tile16)) == 0
        check(lc, f"{name}: side vector (law of cosines)")
        check(her, f"{name}: count N = {N} (Heron)")
        if lc and her:
            ok(f"{name}: sides {scale}*{vec}, N = {sp.factor(N)}")


# ---------------------------------------------------------------------------
# 2. Group 2
# ---------------------------------------------------------------------------
S_, T_ = sp.symbols("s t", positive=True)
A2 = S_**2 - T_**2
B2 = T_ * (2 * S_ + T_)
C2 = S_**2 + S_ * T_ + T_**2


def cexp(n_alpha: int, n_beta: int, n_third: int):
    """(re, im) of exp(i(n_alpha*alpha + n_beta*beta + n_third*pi/3)) for the Group-2 tile."""
    ea = ((A2 + 2 * B2) / (2 * C2), sp.sqrt(3) * A2 / (2 * C2))
    eb = ((2 * A2 + B2) / (2 * C2), sp.sqrt(3) * B2 / (2 * C2))
    e3 = (sp.Rational(1, 2), sp.sqrt(3) / 2)

    def mul(u, v):
        return (sp.expand(u[0] * v[0] - u[1] * v[1]), sp.expand(u[0] * v[1] + u[1] * v[0]))

    def pw(u, n):
        r = (sp.Integer(1), sp.Integer(0))
        if n < 0:
            nrm = sp.simplify(u[0] ** 2 + u[1] ** 2)
            u = (u[0] / nrm, -u[1] / nrm)
            n = -n
        for _ in range(n):
            r = mul(r, u)
        return r

    r = mul(mul(pw(ea, n_alpha), pw(eb, n_beta)), pw(e3, n_third))
    return sp.simplify(r[0]), sp.simplify(r[1])


def group2_symbolic() -> None:
    print("\n[2] Group-2 side vectors and counts (Lemma lem:rowI and the four cases of lem:group2)")
    check(sp.expand(C2**2 - (A2**2 + A2 * B2 + B2**2)) == 0, "parametrization satisfies c^2=a^2+ab+b^2")
    a, b, c = A2, B2, C2
    cosof = lambda na, nb, n3: cexp(na, nb, n3)[0]
    # tile: angles alpha, beta, gamma = 2pi/3
    check(law_of_cosines_ok((a, b, c), (cosof(1, 0, 0), cosof(0, 1, 0), cosof(0, 0, 2))), "Group-2 tile")
    check(sp.simplify(cosof(1, 1, 0) - sp.Rational(1, 2)) == 0, "alpha+beta = pi/3")
    tile16 = heron16(a, b, c)
    mm = sp.symbols("mm", positive=True)
    U, V, W = a + 2 * b, 2 * a + b, a + b
    rows = [
        # name, angles as (n_alpha, n_beta, n_third), primitive vector, scale, claimed N
        ("row I (a,a,pi-2a)", ((1, 0, 0), (1, 0, 0), (-2, 0, 3)), (c, c, U), k, k**2 * U / b),
        ("row I swapped (b,b,pi-2b)", ((0, 1, 0), (0, 1, 0), (0, -2, 3)), (c, c, V), k, k**2 * V / a),
        ("lem:group2 case A (a,2a,3b)", ((1, 0, 0), (2, 0, 0), (0, 3, 0)), (c**2, c * U, 3 * b * W), mm, 3 * mm**2 * U * W),
        ("lem:group2 case B (a,2b,2a+b)", ((1, 0, 0), (0, 2, 0), (2, 1, 0)), (a * c, b * V, c * W), mm, mm**2 * V * W),
        ("lem:group2 case C (a,a+b,a+2b)", ((1, 0, 0), (1, 1, 0), (1, 2, 0)), (a, c, W), mm, mm**2 * W / b),
        ("lem:group2 case D (2a,2b,a+b)", ((2, 0, 0), (0, 2, 0), (1, 1, 0)), (a * U, b * V, c**2), mm, mm**2 * U * V),
    ]
    for name, angs, vec, scale, N in rows:
        sides = tuple(scale * v for v in vec)
        lc = law_of_cosines_ok(sides, tuple(cosof(*x) for x in angs))
        her = sp.simplify(sp.together(heron16(*sides) - N**2 * tile16)) == 0
        check(lc, f"{name}: side vector")
        check(her, f"{name}: count")
        if lc and her:
            ok(f"{name}: side vector and count N = scale^2 * {sp.factor(N / scale**2)}")
    # the sine-law scale ratios K_T/K quoted in lem:group2 (mc^2/a, mc, m, mc for A-D):
    # K_T/K = (side of T opposite alpha)/(a) when T has an alpha angle
    for name, ratio, side_opp_alpha in (("A", mm * c**2 / a, mm * c**2), ("B", mm * c, mm * a * c),
                                        ("C", mm, mm * a), ("D", mm * c, None)):
        if side_opp_alpha is not None:
            check(sp.simplify(side_opp_alpha / a - ratio) == 0, f"lem:group2 scale ratio case {name}")
    # case D has no alpha angle; use 2alpha: K_T sin 2alpha = mm a U and K sin 2alpha = a U / c
    check(sp.simplify((mm * a * U) / (a * U / c) - mm * c) == 0, "lem:group2 scale ratio case D")
    ok("lem:group2 scale ratios K_T/K = mc^2/a, mc, m, mc")


# ---------------------------------------------------------------------------
# 3. gcd claims
# ---------------------------------------------------------------------------
def primitive_group2_triples(bound: int):
    out = []
    for a in range(1, bound + 1):
        for b in range(1, bound + 1):
            if math.gcd(a, b) != 1:
                continue
            c2 = a * a + a * b + b * b
            c = math.isqrt(c2)
            if c * c == c2:
                out.append((a, b, c))
    return out


def gcd_checks() -> None:
    print("\n[3] gcd (primitivity) claims")
    K = 400
    n = 0
    for kk in range(2, K + 1):
        for mm in range(1, kk):
            if math.gcd(mm, kk) != 1:
                continue
            n += 1
            a, b, c = mm * kk, kk * kk - mm * mm, kk * kk
            h, g = 2 * kk * kk - mm * mm, 3 * kk * kk - mm * mm
            vecs = {
                "tile": (a, b, c), "triquadratic": (mm * h, kk * b, kk**3), "isosceles-beta": (kk**3, mm * g),
                "(a,2a,2b)": (kk**4, kk * kk * h, b * g), "shape4": (kk, mm), "shape5": (kk * kk, h),
            }
            for name, v in vecs.items():
                if math.gcd(*v) != 1:
                    check(False, f"gcd {name} (m,k)=({mm},{kk})")
            if math.gcd(h, b) != 1 or math.gcd(mm, b) != 1 or math.gcd(kk, b) != 1:
                check(False, f"gcd(h,b)=gcd(m,b)=gcd(k,b)=1 at ({mm},{kk})")
    ok(f"Group 1: all six vectors primitive and gcd(h,b)=gcd(m,b)=gcd(k,b)=1 for all {n} coprime 0<m<k<={K}")

    trip = primitive_group2_triples(1200)
    for a, b, c in trip:
        d = a - b
        if not (math.gcd(a, b) == math.gcd(a, c) == math.gcd(b, c) == 1):
            check(False, f"pairwise coprime {a,b,c}")
        if c % 3 == 0 or d % 3 == 0 or math.gcd(d, a * b) != 1:
            check(False, f"units mod 3ab {a,b,c}")
        if math.gcd(c, a + 2 * b) != 1 or math.gcd(c, 2 * a + b) != 1:
            check(False, f"row I primitive {a,b,c}")
        if min(a, b) < 2:
            check(False, f"a,b >= 2 {a,b,c}")
        for v in ((c * c, c * (a + 2 * b), 3 * b * (a + b)), (a * c, b * (2 * a + b), c * (a + b)),
                  (a, c, a + b), (a * (a + 2 * b), b * (2 * a + b), c * c)):
            if math.gcd(*v) != 1:
                check(False, f"lem:group2 vector {v}")
    ok(f"Group 2: {len(trip)} primitive triples with a,b <= 1200: pairwise coprime, 3 !| c, "
       f"d = a-b unit mod 3ab, a,b >= 2, gcd(c,a+2b)=gcd(c,2a+b)=1, lem:group2 vectors A-D primitive")


# ---------------------------------------------------------------------------
# 4. residues
# ---------------------------------------------------------------------------
def residue_checks() -> None:
    print("\n[4] Residues (Lemma lem:g1residues)")
    vals8 = {(2 * x * x - y * y) % 8 for x in range(8) for y in range(8) if (2 * x * x - y * y) % 2 == 1}
    check(vals8 == {1, 7}, "odd 2k^2-m^2 mod 8")
    vals3 = {(3 * x * x - y * y) % 3 for x in range(3) for y in range(3)}
    check(1 not in vals3, "3k^2-m^2 mod 3")
    ok(f"complete residue enumeration: odd 2k^2-m^2 mod 8 in {sorted(vals8)}; 3k^2-m^2 mod 3 in {sorted(vals3)}")
    P = 5000
    primes = [p for p in sp.primerange(5, P) if p % 4 == 3]
    rep_h, rep_g = set(), set()
    for kk in range(2, math.isqrt(P) + 2):
        for mm in range(1, kk):
            if math.gcd(mm, kk) != 1:
                continue
            for val, bucket in ((2 * kk * kk - mm * mm, rep_h), (3 * kk * kk - mm * mm, rep_g)):
                if val < P:
                    bucket.add(val)
    bad_h = [p for p in primes if p in rep_h and p % 8 != 7]
    bad_g = [p for p in primes if p in rep_g and p % 12 != 11]
    check(not bad_h and not bad_g, "representation congruences")
    miss_h = [p for p in primes if p % 8 == 7 and p not in rep_h]
    miss_g = [p for p in primes if p % 12 == 11 and p not in rep_g]
    p19 = [p for p in primes if p % 24 == 19]
    both = [p for p in p19 if p in rep_h or p in rep_g]
    check(not both, "p = 19 mod 24 represented by neither form")
    ok(f"primes p = 3 mod 4, 5 <= p < {P}: {len(primes)}; represented by 2k^2-m^2 (coprime 0<m<k): "
       f"{len([p for p in primes if p in rep_h])}, all = 7 mod 8, missing p = 7 mod 8: {miss_h}")
    ok(f"represented by 3k^2-m^2: {len([p for p in primes if p in rep_g])}, all = 11 mod 12, "
       f"missing p = 11 mod 12: {miss_g}")
    ok(f"{len(p19)} primes p = 19 mod 24 below {P} (19, 43, 67, ...): represented by neither form")


# ---------------------------------------------------------------------------
# 5. shape 4 base decompositions
# ---------------------------------------------------------------------------
def shape4_checks() -> None:
    print("\n[5] Lemma lem:shape4: base decompositions in the prime case")
    K = 80
    inst = 0
    examples = []
    for kk in range(2, K + 1):
        for mm in range(1, kk):
            if math.gcd(mm, kk) != 1:
                continue
            a, b, c = mm * kk, kk * kk - mm * mm, kk * kk
            for N in sp.primefactors(b):
                q, r = divmod(b, N)
                s = math.isqrt(q)
                if r or s * s != q:
                    continue
                tt = N * s           # t^2 = N b
                base = tt * mm
                inst += 1
                sols = []
                for C in range(base // c + 1):
                    for B in range((base - C * c) // b + 1):
                        rest = base - C * c - B * b
                        if rest % a == 0:
                            sols.append((rest // a, B, C))
                expected = [(0, mm // s, 0)] if mm % s == 0 else []
                if any(C > 0 for (_, _, C) in sols) or sols != expected:
                    check(False, f"lem:shape4 (m,k)=({mm},{kk}) N={N} s={s} sols={sols}")
                if len(examples) < 6:
                    examples.append(f"(m,k)=({mm},{kk}) N={N} t={tt} base={base}")
    ok(f"{inst} prime instances with k <= {K}: the base t*m = N*s*m has no decomposition with a c-edge "
       f"(only (A,B,C) = (0, m/s, 0) when s | m, none otherwise); e.g. " + "; ".join(examples))


# ---------------------------------------------------------------------------
# 6. shape 5 elementary part
# ---------------------------------------------------------------------------
def shape5_elementary() -> None:
    print("\n[6] Lemma lem:shape5, elementary part")
    K = 400
    hits = []
    for kk in range(2, K + 1):
        for mm in range(1, kk):
            if math.gcd(mm, kk) != 1:
                continue
            b, h = kk * kk - mm * mm, 2 * kk * kk - mm * mm
            tt = math.isqrt(b)
            if tt * tt == b and sp.isprime(h):
                hits.append((mm, kk, tt, h))
                if h != kk * kk + tt * tt or h % 4 != 1 or tt % b == 0:
                    check(False, f"lem:shape5 elementary {(mm, kk, tt, h)}")
    ok(f"{len(hits)} pairs with k <= {K} where t^2 = b and h prime; all have N = h = k^2 + t^2 = 1 mod 4 "
       f"and b !| t (excluded by the boundary-character part); first: {hits[:4]}")


# ---------------------------------------------------------------------------
# 7. boundary characters
# ---------------------------------------------------------------------------
z = sp.symbols("z")


def psi(ang, group):
    """Character of an angle given as integer pair. group 2: (j,n)=j*pi/3+n*alpha; group 1: (j,n)=j*pi+n*gamma."""
    jj, nn = ang
    return (-1) ** (jj % 2) * z**nn


def turning_value(lengths, angles, group):
    """ccw polygon: edge i runs from vertex i to i+1, angles[i] = interior angle at vertex i (integer pair).
    Direction of edge 0 is 0; edge i+1 = edge i + pi - angles[i+1]."""
    pi = (3, 0) if group == 2 else (1, 0)
    d = (0, 0)
    val = 0
    for i, L in enumerate(lengths):
        if i > 0:
            ai = angles[i]
            d = (d[0] + pi[0] - ai[0], d[1] + pi[1] - ai[1])
        val += L * psi(d, group)
    return sp.expand(val), d


def character_checks() -> None:
    print("\n[7] Boundary characters (Lemmas lem:character, lem:rowI, lem:shape5)")
    # ---- Group 2: alpha=(0,1), beta=(1,-1), gamma=(2,0), pi=(3,0)
    a, b, c = sp.symbols("a b c", positive=True)
    d = a - b
    al, be, ga = (0, 1), (1, -1), (2, 0)
    # direct ccw (A,B,C): edges AB=c, BC=a, CA=b; anchor = BC
    v, _ = turning_value([c, a, b], [al, be, ga], 2)
    # direction of BC = pi - beta
    anchor = psi((3 - be[0], -be[1]), 2)
    check(sp.simplify(v / anchor - (d + c / z)) == 0, "Group-2 direct tile value d + c z^-1")
    # reflected ccw (A,C,B): edges AC=b, CB=a, BA=c; anchor = CB, direction pi - gamma
    v, _ = turning_value([b, a, c], [al, ga, be], 2)
    anchor = psi((3 - ga[0], -ga[1]), 2)
    check(sp.simplify(v / anchor - (d + c * z)) == 0, "Group-2 reflected tile value d + c z")
    ok("Group-2 tile values: direct chi(a-edge)(d + c z^-1), reflected chi(a-edge)(d + c z)")
    # row I target ccw (X,Y,Z), angles alpha, alpha, pi-2alpha = (3,-2)
    kk = sp.symbols("k", positive=True)
    U = a + 2 * b
    v, _ = turning_value([kk * U, kk * c, kk * c], [al, al, (3, -2)], 2)
    check(sp.simplify(v - kk * (U - c / z - c * z)) == 0, "row I target polynomial")
    ok("row I target polynomial B(dT) = k(U - c z^-1 - c z) (base direction anchored)")
    # evaluation z -> -d/c
    rel = c**2 - (a**2 + a * b + b**2)
    w = -d / c
    expr = sp.together(d * (kk * (U - c / w - c * w)) - 3 * a**2 * kk)
    num = sp.expand(sp.numer(expr))
    check(sp.rem(num, rel, c) == 0, "d * eps(row I) = 3 a^2 k")
    gen2 = sp.together(d * (d + c / w) - (d**2 - c**2))
    check(sp.simplify(gen2) == 0 and sp.expand(d**2 - c**2 + 3 * a * b).subs(c**2, a**2 + a * b + b**2) == 0,
          "eps(d + c z^-1) = -3ab/d")
    check(sp.simplify(d + c * w) == 0, "eps(d + c z) = 0")
    ok("evaluation z -> -d c^-1: kills d+cz and d+cz^-1 (mod 3ab); d*eps(B(dT)) = 3a^2 k")
    # numeric: eps(row I) = 0 mod 3ab  iff  b | k
    trip = primitive_group2_triples(300)
    cnt = 0
    for A, B, C in trip:
        M = 3 * A * B
        D = A - B
        wz = (-D * pow(C, -1, M)) % M
        wzi = pow(wz, -1, M)
        assert (D + C * wz) % M == 0 and (D + C * wzi) % M == 0
        for kv in range(1, 2 * B + 1):
            e = (kv * ((A + 2 * B) - C * wz - C * wzi)) % M
            if (e == 0) != (kv % B == 0):
                check(False, f"row I eps criterion {(A, B, C)} k={kv}")
            cnt += 1
    ok(f"row I: eps(B(dT)) = 0 mod 3ab exactly when b | k ({cnt} cases, {len(trip)} triples a,b <= 300)")

    # ---- Group 1: alpha=(-1,2), beta=(2,-3), gamma=(0,1), pi=(1,0)
    mm_, kk_, tt_ = sp.symbols("m k t", positive=True)
    A1, B1, C1 = mm_ * kk_, kk_**2 - mm_**2, kk_**2
    al1, be1, ga1 = (-1, 2), (2, -3), (0, 1)
    Q = kk_ * z**2 + mm_ * z + kk_
    Qb = kk_ * z**2 - mm_ * z + kk_
    F = sp.expand(kk_**2 + (kk_**2 - mm_**2) * z**2 - mm_ * kk_ * z**3)
    G = sp.expand(kk_**2 * z**3 + (kk_**2 - mm_**2) * z - mm_ * kk_)
    check(sp.expand(F - (kk_ - mm_ * z) * Q) == 0 and sp.expand(G - (kk_ * z - mm_) * Q) == 0, "F,G factor")
    v, _ = turning_value([C1, A1, B1], [al1, be1, ga1], 1)
    anchor = psi((1 - be1[0], -be1[1]), 1)
    check(sp.simplify(v / anchor - (-F / z**3)) == 0, "Group-1 direct tile value")
    v, _ = turning_value([B1, A1, C1], [al1, ga1, be1], 1)
    anchor = psi((1 - ga1[0], -ga1[1]), 1)
    check(sp.simplify(v / anchor - (-G)) == 0, "Group-1 reflected tile value")
    ok("Group-1 tile values: direct -chi(a-edge) z^-3 (k-mz)Q, reflected -chi(a-edge)(kz-m)Q, Q = kz^2+mz+k")
    hh = 2 * kk_**2 - mm_**2
    v, _ = turning_value([tt_ * hh, tt_ * kk_**2, tt_ * kk_**2], [al1, al1, (3, -4)], 1)
    check(sp.simplify(v - tt_ * Q * Qb / z**2) == 0, "shape 5 target polynomial")
    ok("shape 5 target polynomial B(dT) = t(h + k^2 z^-2 + k^2 z^2) = t z^-2 Q Qbar")
    check(sp.simplify(Qb.subs(z, kk_ / mm_) - kk_**3 / mm_**2) == 0, "Qbar(k/m) = k^3/m^2")
    ok("Qbar(k m^-1) = k^3 m^-2 (a unit mod b)")
    cnt = 0
    for kv in range(2, 61):
        for mv in range(1, kv):
            if math.gcd(mv, kv) != 1:
                continue
            bv = kv * kv - mv * mv
            zz = kv * pow(mv, -1, bv) % bv
            zi = pow(zz, -1, bv)
            assert (kv - mv * zz) % bv == 0 and (kv * zz - mv) % bv == 0
            qb = (kv * zz * zz - mv * zz + kv) % bv
            for tv in range(1, 2 * bv + 1):
                if ((tv * qb) % bv == 0) != (tv % bv == 0):
                    check(False, f"lem:shape5 psi criterion {(mv, kv, tv)}")
                cnt += 1
    ok(f"shape 5: psi_b(t Qbar) = 0 mod b exactly when b | t ({cnt} cases, k <= 60)")


# ---------------------------------------------------------------------------
# 8. certificates
# ---------------------------------------------------------------------------
class Field:
    """Elements x + w*sqrt(-D) stored as (x, w) Fractions; geometric point (x, w*sqrt(D))."""

    def __init__(self, D):
        self.D = D

    def mul(self, u, v):
        return (u[0] * v[0] - self.D * u[1] * v[1], u[0] * v[1] + u[1] * v[0])

    def inv(self, u):
        n = u[0] * u[0] + self.D * u[1] * u[1]
        return (u[0] / n, -u[1] / n)


def frac_sqrt(q: Fr) -> Fr:
    n, d = q.numerator, q.denominator
    rn, rd = math.isqrt(n), math.isqrt(d)
    if rn * rn != n or rd * rd != d:
        raise ValueError(f"not a rational square: {q}")
    return Fr(rn, rd)


def load_tiling(path: Path):
    data = json.loads(path.read_text())
    til = data["tiling"]
    if isinstance(til, str):
        til = ast.literal_eval(til)
    tiles = [[(Fr(p[0]), Fr(p[1])) for p in tri] for tri in til]
    return data, tiles


def cert_checks() -> None:
    print("\n[8] Boundary-character identity on exact tilings (optional)")
    if TILINGS_DIR is None:
        print("  skipped: no --tilings DIR given (this section needs the tiling JSON files)")
        return
    cases = [
        ("N189_tiling.json", ("g1", 1, 2), "shape5"),
        ("external/N63_bonfioli.json", ("g1", 1, 2), None),
        ("external/N99_bonfioli.json", ("g1", 1, 2), None),
        ("N88_tiling.json", ("g2", 3, 5, 7), None),
        ("external/N143_bonfioli.json", ("g2", 3, 5, 7), None),
        ("x31_N77_trapezoid_tiling.json", ("g2", 3, 5, 7), None),
    ]
    for fname, tile, extra in cases:
        path = next((q for q in (TILINGS_DIR / fname, TILINGS_DIR / "external" / Path(fname).name, TILINGS_DIR / Path(fname).name) if q.exists()), TILINGS_DIR / fname)
        if not path.exists():
            print(f"  skip  {fname} (not found)")
            continue
        data, tiles = load_tiling(path)
        if tile[0] == "g1":
            p, q = tile[1], tile[2]
            D = 4 * q * q - p * p
            sides = {"a": p * q, "b": q * q - p * p, "c": q * q}
            omega = (Fr(-p, 2 * q), Fr(1, 2 * q))   # e^{i gamma}
            gen, order = (Fr(-1), Fr(0)), 2         # e^{i pi}
        else:
            a_, b_, c_ = tile[1], tile[2], tile[3]
            D = 3
            sides = {"a": a_, "b": b_, "c": c_}
            omega = (Fr(a_ + 2 * b_, 2 * c_), Fr(a_, 2 * c_))  # e^{i alpha}
            gen, order = (Fr(1, 2), Fr(1, 2)), 6                # e^{i pi/3}
        F_ = Field(D)
        table = {}
        g = (Fr(1), Fr(0))
        for jj in range(order):
            w_ = g
            for nn in range(0, 80):
                table.setdefault(w_, (jj, nn))
                w_ = F_.mul(w_, omega)
            w_ = g
            oi = F_.inv(omega)
            for nn in range(0, -80, -1):
                table.setdefault(w_, (jj, nn))
                w_ = F_.mul(w_, oi)
            g = F_.mul(g, gen)

        def chi_of(vec):
            L2 = vec[0] ** 2 + D * vec[1] ** 2
            L = frac_sqrt(L2)
            u = (vec[0] / L, vec[1] / L)
            jj, nn = table[u]
            return L, (-1) ** (jj % 2) * z**nn

        def cross(o, p1, p2):
            return (p1[0] - o[0]) * (p2[1] - o[1]) - (p1[1] - o[1]) * (p2[0] - o[0])

        total = 0
        nd = nr = 0
        okvals = True
        a_s, b_s, c_s = sides["a"], sides["b"], sides["c"]
        dpoly = None
        for tri in tiles:
            if cross(*tri) < 0:
                tri = [tri[0], tri[2], tri[1]]
            val = 0
            lens = []
            for i in range(3):
                P0, P1 = tri[i], tri[(i + 1) % 3]
                L, ch = chi_of((P1[0] - P0[0], P1[1] - P0[1]))
                val += L * ch
                lens.append(L)
            total += val
            # vertex i is opposite edge (i+1)->(i+2); its angle name from that edge length
            name = {sides["a"]: "A", sides["b"]: "B", sides["c"]: "C"}
            opp = [name[int(lens[(i + 1) % 3])] for i in range(3)]
            order_ccw = "".join(opp)
            direct = order_ccw in ("ABC", "BCA", "CAB")
            nd += direct
            nr += not direct
            # anchor: the a-edge, i.e. the edge opposite vertex A
            ia = opp.index("A")
            P0, P1 = tri[(ia + 1) % 3], tri[(ia + 2) % 3]
            _, chA = chi_of((P1[0] - P0[0], P1[1] - P0[1]))
            if tile[0] == "g2":
                dd = a_s - b_s
                expect = chA * (dd + c_s / z) if direct else chA * (dd + c_s * z)
            else:
                mm, kk = p, q
                Qz = kk * z**2 + mm * z + kk
                expect = -chA * z**-3 * (kk - mm * z) * Qz if direct else -chA * (kk * z - mm) * Qz
            if sp.simplify(val - expect) != 0:
                okvals = False
        # target boundary: convex hull, ccw, collinear points removed
        pts = sorted({p_ for tri in tiles for p_ in tri})
        lower, upper = [], []
        for p_ in pts:
            while len(lower) >= 2 and cross(lower[-2], lower[-1], p_) <= 0:
                lower.pop()
            lower.append(p_)
        for p_ in reversed(pts):
            while len(upper) >= 2 and cross(upper[-2], upper[-1], p_) <= 0:
                upper.pop()
            upper.append(p_)
        hull = lower[:-1] + upper[:-1]
        bT = 0
        side_lens = []
        for i in range(len(hull)):
            P0, P1 = hull[i], hull[(i + 1) % len(hull)]
            L, ch = chi_of((P1[0] - P0[0], P1[1] - P0[1]))
            bT += L * ch
            side_lens.append(L)
        ident = sp.expand(total - bT) == 0
        check(ident, f"{fname}: sum of tile values = B(dT)")
        check(okvals, f"{fname}: tile values match the direct/reflected formulas")
        msg = (f"{fname}: N={len(tiles)} ({nd} direct, {nr} reflected), target sides "
               f"{[str(x) for x in side_lens]}: sum_t B(dt) = B(dT) exactly; every tile value as predicted")
        if tile[0] == "g2":
            M = 3 * a_s * b_s
            dd = a_s - b_s
            wz = (-dd * pow(c_s, -1, M)) % M
            poly = sp.Poly(sp.expand(bT * z**200), z)
            ev = sum(int(cf) * pow(wz, e - 200, M) for (e,), cf in poly.terms()) % M
            check(ev == 0, f"{fname}: eps(B(dT)) = 0 mod 3ab")
            msg += f"; eps(B(dT)) = 0 mod {M}"
        if extra == "shape5":
            mm, kk = p, q
            bb, hh = kk * kk - mm * mm, 2 * kk * kk - mm * mm
            # sides t(k^2, k^2, h)
            tvals = {L / hh for L in side_lens if (L / hh) * kk * kk in side_lens} | \
                    {L / (kk * kk) for L in side_lens if (L / (kk * kk)) * hh in side_lens}
            tv = min(tvals)
            Qz = kk * z**2 + mm * z + kk
            Qbz = kk * z**2 - mm * z + kk
            quot = sp.simplify(bT / (tv * Qz * Qbz / z**2))
            unit = quot in {z**e for e in range(-40, 41)} | {-z**e for e in range(-40, 41)}
            check(unit and tv.denominator == 1 and int(tv) % bb == 0, f"{fname}: shape-5 conclusion")
            msg += f"; target polynomial = unit * t z^-2 Q Qbar with t={tv}, b={bb} | t"
        if ident and okvals:
            ok(msg)


# ---------------------------------------------------------------------------
# 9. the examples quoted in the remarks of the paper
# ---------------------------------------------------------------------------
def remark_examples() -> None:
    print("\n[9] Examples quoted in the remarks (count formula allows a prime; the geometric step excludes it)")
    # Lemma lem:shape4: (m,k) = (9,10), tile (90,19,100), T = 19*(10,10,9), N = t^2/b = 19
    mm, kk, tt = 9, 10, 19
    b = kk * kk - mm * mm
    check((mm * kk, b, kk * kk) == (90, 19, 100) and tt * tt % b == 0 and tt * tt // b == 19, "lem:shape4 example")
    base = tt * mm
    sols = [(A, B, C) for C in range(base // (kk * kk) + 1) for B in range(base // b + 1) for A in range(base // (mm * kk) + 1)
            if A * mm * kk + B * b + C * kk * kk == base]
    check(sols == [(0, 9, 0)], "lem:shape4 example: base = nine b-edges")
    ok(f"lem:shape4: tile (90,19,100), T = 19*(10,10,9), N = 19; base 171 decompositions {sols} (nine b-edges, no c-edge)")
    # Lemma lem:shape5: (m,k) = (3,5), tile (15,16,25), t = 4, T = 4*(25,25,41), N = t^2 h / b = 41
    mm, kk, tt = 3, 5, 4
    b, h = kk * kk - mm * mm, 2 * kk * kk - mm * mm
    check((mm * kk, b, kk * kk) == (15, 16, 25) and tt * tt * h % b == 0 and tt * tt * h // b == 41
          and sp.isprime(41) and tt % b != 0, "shape5 example")
    ok("lem:shape5: tile (15,16,25), T = 4*(25,25,41), N = 41 prime = 1 mod 4; excluded only by b | t (16 !| 4)")
    # Lemma lem:rowI: (a,b,c) = (39,16,49), k = 4, T = 4*(49,49,71), N = k^2 U / b = 71
    a, b, c, kv = 39, 16, 49, 4
    U = a + 2 * b
    check(c * c == a * a + a * b + b * b and math.gcd(math.gcd(a, b), c) == 1 and kv * kv * U % b == 0
          and kv * kv * U // b == 71 and sp.isprime(71) and 71 % 4 == 3 and kv % b != 0, "rowI example")
    M = 3 * a * b
    d = a - b
    wz = (-d * pow(c, -1, M)) % M
    ev = (kv * (U - c * pow(wz, -1, M) - c * wz)) % M
    check(ev != 0, "lem:rowI example: eps(B(dT)) != 0")
    ok(f"lem:rowI: tile (39,16,49), T = 4*(49,49,71), N = 71 prime = 3 mod 4; eps(B(dT)) = {ev} != 0 mod {M}, so excluded")


def main() -> int:
    global TILINGS_DIR
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--tilings", metavar="DIR", type=Path,
                    help="directory with exact tiling JSON files; enables the optional section 8")
    args = ap.parse_args()
    TILINGS_DIR = args.tilings
    if TILINGS_DIR is not None and not TILINGS_DIR.is_dir():
        ap.error(f"--tilings: not a directory: {TILINGS_DIR}")
    group1_symbolic()
    group2_symbolic()
    gcd_checks()
    residue_checks()
    shape4_checks()
    shape5_elementary()
    character_checks()
    cert_checks()
    remark_examples()
    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} check(s)")
        for f in FAILURES:
            print("  -", f)
        return 1
    print("ALL CHECKS PASSED (exact symbolic identities and finite arithmetic tests; "
          + ("tilings checked)" if TILINGS_DIR is not None else "tilings section skipped)"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
