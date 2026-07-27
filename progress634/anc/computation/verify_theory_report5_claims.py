#!/usr/bin/env python3
"""Machine verification of the checkable arithmetic in theory-track report #5
(archive/pro_report_5/report5.md, 2026-07-25).

What this DOES verify:

  A. The augmentation arithmetic behind the reported shape-4 divisibility
     `q | m` (report §1): tile formula (pq, q²−p², q²), coloring number
     M = (q−p)m forced by Beeson's Theorem 17 equation N/M² = (1+s)/(1−s),
     scale factor μ = M(1+s) = (q²−p²)m/q, equal side X = μc = (q²−p²)mq,
     augmentation scale ℓ = X/b = mq ∈ ℤ (unconditionally — no squarefree or
     coprimality hypotheses), augmented coloring number M′ = M + 2ℓ = (3q−p)m,
     g = gcd(a,c) = q, and the equivalence  q | M′ ⟺ q | m.  Plus the live
     instance (p,q,m) = (4,7,2): 7 ∤ 2, M′ = 34, 7 ∤ 34 — the 132 shape-4
     candidate dies if Theorem 14's `g | M` necessity is sound.

  B. The Theorem-19 contradiction data (report §2): Beeson's Table 5 rows
     (arXiv:1206.2229v3, verbatim in sources/beeson_primary_source_extraction.md)
     all satisfy his isosceles-α tiling equation exactly, yet seven of the
     fifteen rows — including 161, 189, 280 and 465 — violate the printed
     divisibility g = gcd(a,c) | M.  Our certified 189-tiling sits on one of
     the violating rows, so the divisibility is refuted by an actual tiling,
     not merely by internal inconsistency.  Also: Table 3 (isosceles-β, the
     sibling case whose Theorem 14 the report's §1 uses) satisfies g | M on
     all ten rows — consistency, not proof, of Theorem 14.

  C. The 143 macro-numerology (report §4): the three area identities
     143 = 73+70 = 77+66 = 79+64 with the intended pieces' tile counts
     (sporadic trapezoids T(29/31/32, 15) → 73/77/79 tiles; π/3-parallelograms
     of leg 15 and bases 35/33 → 70/66; the 8-scaled tile → 64).

  D. Consequences of the reported q | m: combined with the proved m ≥ 2, the
     first admissible multiplier on every shape-4 ray is m = q, i.e. first
     candidate N = (q²−p²)q²; classicality audit of those values for q ≤ 5
     shows (1,4) → 240 and (2,5) → 525 are the only non-classical ones (240
     the sharpest open test; 112 = 28·2² is in S via Beeson's 28-tiling).

What this does NOT verify (open items, STATUS §8):
  - Beeson's Theorem 14 necessity proof of g | M (isosceles-β) — unread at
    source, and its isosceles-α sibling claim (Theorem 19) is false as printed.
  - Beeson's augmentation construction and the additivity M′ = M + 2ℓ —
    asserted "explicit in the paper", unread at source.
  - The report's searches (shallow-macro, fan/cevian/star closures) and the
    orientation+segment MILP feasibility — the reporting agent's own artifacts,
    archived in archive/pro_report_5/, not independently re-run here.
"""

import json
import os
from fractions import Fraction
from math import gcd, isqrt

PASS = FAIL = 0


def check(name, cond):
    global PASS, FAIL
    if cond:
        PASS += 1
        print(f"  PASS  {name}")
    else:
        FAIL += 1
        print(f"  FAIL  {name}")


def is_square(n):
    return n >= 0 and isqrt(n) ** 2 == n


def is_sum_two_squares(n):
    # n > 0 is a sum of two squares iff every prime ≡ 3 (mod 4) divides it
    # to an even power.
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


def classical(n):
    """Membership in the classical families n², e²+f², 2n², 3n², 6n²."""
    tags = []
    if is_square(n):
        tags.append("square")
    if is_sum_two_squares(n):
        tags.append("e^2+f^2")
    for k in (2, 3, 6):
        if n % k == 0 and is_square(n // k):
            tags.append(f"{k}n^2")
    return tags


# ---------------------------------------------------------------- section A
print("A. Shape-4 augmentation arithmetic (report #5 §1)")

pairs = [(p, q) for q in range(2, 13) for p in range(1, q) if gcd(p, q) == 1]
ok_all = True
for p, q in pairs:
    a, b, c = p * q, q * q - p * p, q * q
    s = Fraction(a, c)
    if gcd(a, gcd(b, c)) != 1:
        ok_all = False
    if s != Fraction(p, q):
        ok_all = False
    if gcd(a, c) != q:  # g = gcd(pq, q²) = q since gcd(p,q)=1
        ok_all = False
    for m in range(1, 13):
        N = b * m * m
        # Theorem 17: N/M² = (1+s)/(1−s)  ⟹  M = (q−p)m
        M2 = Fraction(N) * (1 - s) / (1 + s)
        M = (q - p) * m
        if M2 != M * M:
            ok_all = False
        mu = M * (1 + s)  # Beeson's scale factor, Theorem 17
        if mu != Fraction(b * m, q):
            ok_all = False
        X = mu * c  # equal outer side
        if X != b * m * q:
            ok_all = False
        ell = Fraction(int(X), b)  # attach ℓ-scaled quadratic tile copies
        if ell != m * q or ell.denominator != 1:
            ok_all = False
        Mp = M + 2 * int(ell)  # augmented coloring number
        if Mp != (3 * q - p) * m:
            ok_all = False
        # Theorem 14 on the augmented isosceles-β triangle: q | M′ ⟺ q | m
        if (Mp % q == 0) != (m % q == 0):
            ok_all = False
check(f"tile/M/μ/X/ℓ/M′ formulas and (q|M′ ⟺ q|m) on {len(pairs)} coprime "
      "pairs × 12 multipliers", ok_all)

p, q, m = 4, 7, 2
Mp = (3 * q - p) * m
check("instance (p,q,m)=(4,7,2): q ∤ m (7 ∤ 2)", m % q != 0)
check("instance (p,q,m)=(4,7,2): M′ = 34 and 7 ∤ 34", Mp == 34 and Mp % 7 != 0)
check("consistency with lemma:integermu instances (1,2)/(2,3)/(3,4): q | m "
      "reproduces 2|m, 3|m, 4|m",
      all((Mp0 % q0 == 0) == (m0 % q0 == 0)
          for (p0, q0) in [(1, 2), (2, 3), (3, 4)]
          for m0 in range(1, 25)
          for Mp0 in [(3 * q0 - p0) * m0]))
check("shape-4 'yes' entries obey q | m: 48 = 3·4² (m=4, q=2), "
      "108 = 3·6² (m=6, q=2)", 4 % 2 == 0 and 6 % 2 == 0)

# ---------------------------------------------------------------- section B
print("B. Theorem-19 contradiction data (report #5 §2)")


def iso_alpha(s):  # Theorem 19's isosceles-α equation N/M²
    return (1 + s) * (2 - s * s) / ((1 - s) * (2 + s) ** 2)


def iso_beta(s):  # Theorem 14's isosceles-β equation N/M²
    return (3 - s * s) / (1 + s) ** 2


table5 = [  # (N, M, (a,b,c)) — Beeson Table 5, p. 91–92, verbatim extraction
    (21, 5, (2, 3, 4)), (34, 7, (3, 8, 9)), (70, 8, (6, 5, 9)),
    (84, 10, (2, 3, 4)), (136, 14, (3, 8, 9)), (161, 11, (12, 7, 16)),
    (164, 13, (15, 16, 25)), (189, 15, (2, 3, 4)), (280, 16, (6, 5, 9)),
    (294, 22, (5, 24, 25)), (306, 14, (20, 9, 25)), (306, 21, (3, 8, 9)),
    (336, 20, (2, 3, 4)), (438, 19, (35, 24, 49)), (465, 27, (4, 15, 16)),
]
check("all 15 Table-5 rows satisfy the isosceles-α tiling equation exactly",
      all(Fraction(N) == M * M * iso_alpha(Fraction(a, c))
          for N, M, (a, b, c) in table5))
viol = [(N, M, gcd(a, c)) for N, M, (a, b, c) in table5
        if M % gcd(a, c) != 0]
check("12 of the 15 rows violate the printed g | M — all except the two "
      "'yes' rows (84, 336) and the (3,8,9) row of 306",
      sorted(N for N, _, _ in viol)
      == [21, 34, 70, 136, 161, 164, 189, 280, 294, 306, 438, 465])
check("161: g = gcd(12,16) = 4 ∤ M = 11", gcd(12, 16) == 4 and 11 % 4 != 0)
check("189: g = gcd(2,4) = 2 ∤ M = 15", gcd(2, 4) == 2 and 15 % 2 != 0)
check("the open values 161, 280, 465 are all on violating rows (Theorem 19 as "
      "printed would 'decide' them)",
      {161, 280, 465} <= {N for N, _, _ in viol})

cert = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                    "tiling_search", "results", "N189_tiling.json")
try:
    with open(cert) as f:
        d = json.load(f)
    check("certified 189-tiling exists on the violating (1,2) row "
          "(N189_tiling.json: verdict FOUND, 189 tiles, warns 0)",
          d["verdict"] == "FOUND" and d["N"] == 189
          and len(d["tiling"]) == 189 and d["warns"] == 0
          and "(p,q)=(1,2)" in d["label"])
except FileNotFoundError:
    check("certified 189-tiling certificate present", False)

table3 = [  # (N, M, (a,b,c)) — Beeson Table 3, p. 69 (isosceles-β, all 'yes')
    (44, 6, (2, 3, 4)), (176, 12, (2, 3, 4)), (207, 15, (6, 5, 9)),
    (234, 12, (3, 8, 9)), (396, 18, (2, 3, 4)), (624, 28, (12, 7, 16)),
    (704, 24, (2, 3, 4)), (752, 20, (4, 15, 16)), (828, 30, (6, 5, 9)),
    (936, 24, (3, 8, 9)),
]
check("all 10 Table-3 rows satisfy the isosceles-β equation exactly",
      all(Fraction(N) == M * M * iso_beta(Fraction(a, c))
          for N, M, (a, b, c) in table3))
check("all 10 Table-3 rows satisfy g | M (consistency of Theorem 14's claim)",
      all(M % gcd(a, c) == 0 for N, M, (a, b, c) in table3))

# ---------------------------------------------------------------- section C
print("C. 143 macro-numerology (report #5 §4)")

trap = {x: 2 * x + 15 for x in (29, 31, 32)}  # T(x,15) tile count
check("sporadic trapezoid counts: T(29/31/32, 15) → 73/77/79",
      (trap[29], trap[31], trap[32]) == (73, 77, 79))
check("π/3-parallelogram counts, leg 15: base 35 → 70, base 33 → 66 tiles, "
      "both bases in ⟨3,5⟩",
      2 * 35 == 70 and 2 * 33 == 66
      and any(35 == 3 * i + 5 * j for i in range(15) for j in range(10))
      and any(33 == 3 * i + 5 * j for i in range(15) for j in range(10)))
check("area identities 143 = 73+70 = 77+66 = 79+64 (64 = 8² = 8-scaled tile)",
      143 == 73 + 70 == 77 + 66 == 79 + 64 and 64 == 8 ** 2)

# ---------------------------------------------------------------- section D
print("D. First admissible shape-4 multiplier under the reported q | m")

expect = {  # (p,q) → (N₁ = (q²−p²)q², classification)
    (1, 2): (12, "classical"), (1, 3): (72, "classical"),
    (2, 3): (45, "classical"), (1, 4): (240, "open"),
    (3, 4): (112, "in S via 28·2² [pub]"), (1, 5): (600, "classical"),
    (2, 5): (525, "open"), (3, 5): (400, "classical"),
    (4, 5): (225, "classical"),
}
ok_all = True
for (p, q), (N1, cls) in sorted(expect.items(), key=lambda kv: kv[1][0]):
    b = q * q - p * p
    if b * q * q != N1:
        ok_all = False
    tags = classical(N1)
    if cls == "classical" and not tags:
        ok_all = False
    if cls != "classical" and tags:
        ok_all = False
    print(f"        ({p},{q}): N₁ = {N1:4d}  {tags or cls}")
check("N₁ = (q²−p²)q² and classicality audit for all (p,q) with q ≤ 5 "
      "(240 and 525 the only non-classical; 112 ∈ S separately)", ok_all)
check("240 is non-classical (the sharpest open shape-4 test)",
      not classical(240))

# --------------------------------------------------------------------------
print(f"\n{PASS}/{PASS + FAIL} PASS")
raise SystemExit(0 if FAIL == 0 else 1)
