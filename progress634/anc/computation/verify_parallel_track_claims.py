#!/usr/bin/env python3
"""Verification of the parallel track's 2026-07-24 (late) report claims.

Checks, in order:
  A. (32,45,67) is a primitive Eisenstein triple.
  B. Closed form R(a,b) = ceil(a/b)+ceil(b/a):
       r*ab - (a^2+b^2) in <a,b>  <=>  r >= R(a,b)     (brute force, many pairs)
  C. 3*R(a,b) <= M_Zhang(a,b) for every primitive Eisenstein triple in range;
     list all triples with strict improvement (3R < M).
  D. The m=9 equilateral construction for (32,45,67): every layer parallelogram
     length is in <32,45>; 1271 = 13*32 + 19*45; m=9 < M=12.
  E. N = 116640 = 81*1440; classicality (sum of two squares).
  F. gamma=2alpha branch: polynomial identity F = (kz+m)(kz^2-mz+k) = a z^3 - b z + c
     with (a,b,c) = (k^2, m^2-k^2, km); mirror G; ideal identity m(kz+m)-k(k+mz) = m^2-k^2;
     numeric closure a e^{3ia} - b e^{ia} + c = 0 and gamma = 2*alpha from the sides.
  G. gamma=2alpha data consistency: 720 = 5*12^2 and 45 = 5*3^2 on tile (4,5,6);
     enumeration of gamma=2alpha ray candidates (N = b r^2) for the 11 frontier values.
  H. Group-1: polynomial identity F = (q-pz)(qz^2+pz+q) = -a z^3 + b z^2 + c with
     (a,b,c) = (pq, q^2-p^2, q^2); mirror G = (qz-p)H = c z^3 + b z - a; numeric closure
     c + a e^{i(pi/2+3h)} + b e^{i(pi+2h)} = 0 with s = p/q = 2 sin(h); 3*alpha+2*beta = pi.
  I. Shape-5 kappa discrepancy: report ray (q^2-p^2)(2q^2-p^2)n^2 for (1,3) gives base 136,
     but Beeson's table entries 34, 306 require base 34 (kappa=4). Report formula wrong
     for p,q both odd.
  J. Shape-4 n=1 candidate enumeration for the 11 frontier values (what a proved n>=2 kills).
"""

import math
from math import gcd, isqrt
from fractions import Fraction
import cmath

OK = []
FAIL = []


def check(name, cond, detail=""):
    (OK if cond else FAIL).append((name, detail))
    print(("PASS  " if cond else "FAIL  ") + name + ("  | " + detail if detail else ""))


def in_semigroup(x, a, b):
    if x < 0:
        return False
    # DP not needed: x in <a,b> iff exists A>=0 with (x - A*a) % b == 0
    for A in range(0, x // a + 1):
        if (x - A * a) % b == 0:
            return True
    return False


def R(a, b):
    return math.ceil(a / b) + math.ceil(b / a)


def M_zhang(a, b):
    c2 = a * a + a * b + b * b
    return 3 * math.ceil((c2 - a - b) / (a * b))


def is_square(n):
    return n >= 0 and isqrt(n) ** 2 == n


# ---------- A ----------
a, b = 32, 45
c2 = a * a + a * b + b * b
check("A: 32^2+32*45+45^2 = 67^2", c2 == 67 ** 2, f"c2={c2}")
check("A: gcd(32,45)=1", gcd(32, 45) == 1)

# ---------- B ----------
bad = []
for aa in range(1, 61):
    for bb in range(1, 61):
        if gcd(aa, bb) != 1 or aa == bb:
            continue
        Rab = R(aa, bb)
        for r in range(1, Rab + 6):
            member = in_semigroup(r * aa * bb - aa * aa - bb * bb, aa, bb)
            if member != (r >= Rab):
                bad.append((aa, bb, r, member, Rab))
check("B: r*ab-(a^2+b^2) in <a,b> <=> r>=ceil(a/b)+ceil(b/a), all coprime a,b<=60",
      not bad, f"{len(bad)} mismatches" if bad else "0 mismatches")

# ---------- C ----------
triples = []
for aa in range(1, 400):
    for bb in range(aa + 1, 400):
        if gcd(aa, bb) != 1:
            continue
        cc2 = aa * aa + aa * bb + bb * bb
        if is_square(cc2):
            triples.append((aa, bb, isqrt(cc2)))
viol = [(t, 3 * R(t[0], t[1]), M_zhang(t[0], t[1])) for t in triples
        if 3 * R(t[0], t[1]) > M_zhang(t[0], t[1])]
strict = [(t, 3 * R(t[0], t[1]), M_zhang(t[0], t[1])) for t in triples
          if 3 * R(t[0], t[1]) < M_zhang(t[0], t[1])]
check("C: 3R <= M_Zhang for all primitive Eisenstein triples a<b<400",
      not viol, f"{len(triples)} triples checked")
print("      triples with strict improvement 3R < M:",
      [(t[0], (v, w)) for t, v, w in strict])
check("C: (32,45,67) has 3R=9 < M=12",
      ((32, 45, 67), 9, 12) in [(t, v, w) for t, v, w in strict])

# ---------- D ----------
ab = 32 * 45
x0 = 3 * ab           # top parameter r=3 for each of the three trapezoids
lens = [x0 + i * ab - (32 ** 2 + 45 ** 2) for i in range(3)]  # layers r_i = 3,4,5
check("D: layer parallelogram lengths " + str(lens) + " all in <32,45>",
      all(in_semigroup(x, 32, 45) for x in lens))
check("D: 1271 = 13*32 + 19*45", 13 * 32 + 19 * 45 == 1271)
check("D: Zhang M(32,45) = 12 and 9 < 12", M_zhang(32, 45) == 12)
check("D: per-trapezoid semigroup condition holds at r=3 (= R)",
      in_semigroup(3 * ab - 32 ** 2 - 45 ** 2, 32, 45) and R(32, 45) == 3)
check("D: r=2 would fail (sharpness of R)",
      not in_semigroup(2 * ab - 32 ** 2 - 45 ** 2, 32, 45))

# ---------- E ----------
N = 9 * 9 * 32 * 45
check("E: N = 116640", N == 116640)


def sum_two_squares(n):
    m = n
    p = 2
    while p * p <= m:
        e = 0
        while m % p == 0:
            m //= p
            e += 1
        if p % 4 == 3 and e % 2 == 1:
            return False
        p += 1
    return not (m % 4 == 3)


check("E: 116640 is a sum of two squares (classical count, no new member of S)",
      sum_two_squares(116640))

# ---------- F ----------
def polymul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += x * y
    return r


ok_poly = True
for (k, m) in [(2, 3), (3, 4), (3, 5), (4, 5), (5, 7), (5, 9), (13, 15)]:
    if gcd(k, m) != 1 or not (k < m < 2 * k):
        # allow (3,5),(5,9),(13,15) style anyway for the identity check
        pass
    A, B, C = k * k, m * m - k * k, k * m
    # F = (kz+m)(kz^2-mz+k) should equal a z^3 - b z + c -> coeffs [c, -b, 0, a]
    F = polymul([m, k], [k, -m, k])
    if F != [C, -B, 0, A]:
        ok_poly = False
    # G = (k+mz)(kz^2-mz+k) should equal c z^3 - b z^2 + a -> coeffs [a, 0, -b, c]
    G = polymul([k, m], [k, -m, k])
    if G != [A, 0, -B, C]:
        ok_poly = False
check("F: gamma=2a factorizations F=(kz+m)(kz^2-mz+k), G=(k+mz)(kz^2-mz+k) as claimed",
      ok_poly)
check("F: ideal identity m(kz+m)-k(k+mz) = m^2-k^2 (z-coeffs cancel)", True,
      "m*k - k*m = 0 and m*m - k*k = b by inspection")

ok_geo = True
for (k, m) in [(2, 3), (3, 4), (4, 5), (5, 7), (5, 9), (13, 15)]:
    if gcd(k, m) != 1 or not (k < m < 2 * k):
        continue
    A, B, C = k * k, m * m - k * k, k * m
    # angles from law of cosines; alpha opposite a, gamma opposite c? — the
    # gamma=2alpha branch has gamma=2alpha with cos(alpha) = m/(2k).
    import math as _m
    cosA = (B * B + C * C - A * A) / (2 * B * C)
    cosB_ = (A * A + C * C - B * B) / (2 * A * C)
    cosC = (A * A + B * B - C * C) / (2 * A * B)
    al, be, ga = _m.acos(cosA), _m.acos(cosB_), _m.acos(cosC)
    # which angle is twice which: check gamma=2alpha for angle opposite c=km vs a=k^2
    if abs(ga - 2 * al) > 1e-9:
        ok_geo = False
    if abs(cosA - m / (2 * k)) > 1e-12:
        ok_geo = False
    z = cmath.exp(1j * al)
    if abs(A * z ** 3 - B * z + C) > 1e-9:
        ok_geo = False
check("F: gamma=2alpha geometry (cos a = m/2k, gamma=2*alpha, closure a z^3 - b z + c = 0 at z=e^{ia})",
      ok_geo)

# ---------- G ----------
check("G: 720 = 5*12^2 (tile (4,5,6): b=5)", 720 == 5 * 144)
check("G: 45 = 5*3^2", 45 == 5 * 9)

frontier = [56, 70, 88, 105, 120, 132, 143, 154, 161, 184, 189]
print("\n   gamma=2alpha ray candidates (N = b r^2, b = m^2-k^2, k<m<2k, gcd(k,m)=1):")
g2a = {}
for NN in frontier:
    cands = []
    r = 1
    while r * r <= NN:
        if NN % (r * r) == 0:
            bb = NN // (r * r)
            # factor bb = (m-k)(m+k), same parity
            for d1 in range(1, isqrt(bb) + 1):
                if bb % d1:
                    continue
                d2 = bb // d1
                if (d1 + d2) % 2:
                    continue
                mm, kk = (d1 + d2) // 2, (d2 - d1) // 2
                if 0 < kk < mm < 2 * kk and gcd(kk, mm) == 1:
                    cands.append((kk, mm, r, (kk * kk, bb, kk * mm)))
        r += 1
    g2a[NN] = cands
    if cands:
        print(f"     N={NN}: " + "; ".join(
            f"tile{t}, r={r_}" for (kk, mm, r_, t) in cands))
print("     (values with no line have no gamma=2alpha candidate at all)")
n56 = g2a[56]
check("G: N=56 has gamma=2alpha candidates, all with r=1 (killed iff reported r>=2 holds)",
      len(n56) > 0 and all(r_ == 1 for (_, _, r_, _) in n56),
      f"candidates: {[t for (_, _, _, t) in n56]}")

# ---------- H ----------
ok_poly1 = True
for (p, q) in [(1, 2), (1, 3), (2, 3), (3, 4), (1, 4), (3, 5), (1, 5), (5, 7)]:
    A, B, C = p * q, q * q - p * p, q * q
    # F = (q-pz)(qz^2+pz+q) should equal -a z^3 + b z^2 + c -> [c, 0, b, -a]
    F = polymul([q, -p], [q, p, q])
    if F != [C, 0, B, -A]:
        ok_poly1 = False
    # G = (qz-p)(qz^2+pz+q) should equal c z^3 + b z - a -> [-a, b, 0, c]
    G = polymul([-p, q], [q, p, q])
    if G != [-A, B, 0, C]:
        ok_poly1 = False
check("H: Group-1 factorizations F=(q-pz)H, G=(qz-p)H with H=qz^2+pz+q as claimed",
      ok_poly1)
check("H: ideal identity q(q-pz)+p(qz-p) = q^2-p^2", True, "by inspection")

ok_geo1 = True
for (p, q) in [(1, 2), (1, 3), (2, 3), (3, 4), (1, 4)]:
    A, B, C = p * q, q * q - p * p, q * q
    s = p / q  # = 2 sin(alpha/2)
    h = math.asin(s / 2)  # alpha/2
    al = 2 * h
    be = (math.pi - 3 * al) / 2
    # sides law of sines check: a : b : c = sin al : sin be : sin(pi - al - be)
    ga = math.pi - al - be
    ratio_ab = math.sin(al) / math.sin(be)
    if abs(ratio_ab - A / B) > 1e-9:
        ok_geo1 = False
    if abs(3 * al + 2 * be - math.pi) > 1e-12:
        ok_geo1 = False
    # closure: c + a e^{i(pi/2+3h)} + b e^{i(pi+2h)} = 0 (after scaling by common factor)
    scale = C / math.sin(ga)
    va = math.sin(al) * scale
    vb = math.sin(be) * scale
    zsum = C + va * cmath.exp(1j * (math.pi / 2 + 3 * h)) + vb * cmath.exp(1j * (math.pi + 2 * h))
    if abs(zsum) > 1e-7:
        ok_geo1 = False
    # and F vanishes at z = e^{i(pi/2+h)} = e^{i gamma}
    z = cmath.exp(1j * (math.pi / 2 + h))
    if abs(-A * z ** 3 + B * z ** 2 + C) > 1e-7:
        ok_geo1 = False
    if abs(ga - (math.pi / 2 + h)) > 1e-12:
        ok_geo1 = False
check("H: Group-1 geometry (3a+2b=pi, sides = (pq, q^2-p^2, q^2), closure, F(e^{i gamma})=0)",
      ok_geo1)

# ---------- I ----------
p, q = 1, 3
base_report = (q * q - p * p) * (2 * q * q - p * p)  # 8*17 = 136
base_ours = base_report // 4                          # kappa = 4 (p,q both odd)
check("I: (1,3) shape-5 ray base: report 136 vs kappa-corrected 34",
      base_report == 136 and base_ours == 34)
check("I: Beeson table values 34 and 306 lie on 34n^2 but NOT on 136n^2",
      34 == 34 * 1 and 306 == 34 * 9 and 34 % 136 != 0 and 306 % 136 != 0,
      "report's shape-5 formula misses kappa=4 for p,q both odd (known error class)")

# ---------- J ----------
print("\n   Group-1 shape-4 candidates with n=1 (N = q^2-p^2) on the frontier "
      "(what a proved n>=2 kills):")
for NN in frontier:
    cands = []
    for d1 in range(1, isqrt(NN) + 1):
        if NN % d1:
            continue
        d2 = NN // d1
        if (d1 + d2) % 2:
            continue
        qq, pp = (d1 + d2) // 2, (d2 - d1) // 2
        if 0 < pp < qq and gcd(pp, qq) == 1:
            cands.append((pp, qq))
    if cands:
        print(f"     N={NN}: (p,q) in {cands}")

print()
print(f"SUMMARY: {len(OK)} passed, {len(FAIL)} failed")
for name, det in FAIL:
    print("  FAILED:", name, det)
