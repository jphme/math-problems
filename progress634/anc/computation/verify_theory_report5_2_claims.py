#!/usr/bin/env python3
"""Machine verification of the checkable content of theory-track report #5.2
(archive/pro_report_5_2/, 2026-07-25 late evening) — written independently of
the report's own script (verify_erdos634_report5.py), with different
implementations (DP semigroup membership, symbolic angle vectors) and with the
geometric bookkeeping of every patch construction re-derived here rather than
assumed.

What this DOES verify:

  A. The *second, independent* derivation of the general shape-4 divisibility
     `q | m` (report §1) — the shape-1 route: attaching a (qm)-scaled tile to
     one equal side of the shape-4 target straightens the base vertex
     ((α+β)+γ = 3α+2β = π), turns the apex into 2α, and yields a shape-1
     target (2α, β, α+β); side bookkeeping (the merged base is pm(2q²−p²),
     the new side q³m), the count identity bm² + (qm)² = hm², h = 2q²−p²;
     Beeson's shape-1 iff (Thm 7, arXiv:1206.2229v3 [pub], audited in
     sources/beeson_primary_source_extraction.md with the printed "K does not
     divide M²" typo documented) has exact count set {q²hn²} for the tile
     (p,q) — re-derived from (M,K) = (pt,qt), K | M² ⟺ q | t — and is
     cross-checked against ALL EIGHT rows of his Table 1; comparison
     hm² = q²hn² forces q | m.  Instance (4,7,2): 7 ∤ 2 — 132's shape-4
     candidate is dead WITHOUT any unread import (unlike the report-#5
     Thm-14 route, whose two imports remain unread at source).

  B. The shape-4 → shape-5 transfer at m = qn (report §2): angle bookkeeping
     ((α+β)+γ = π straightens one base vertex, the other becomes α+2β, apex
     and new vertex both α → shape 5), side bookkeeping (glued side
     bpqn = a·bn), count identity q²bn² + (bn)² · b = b(2q²-p²)n² — landing
     exactly on the verified shape-5 ray at multiplier n.  Consequence
     checked: shape-4 (3,4) at m = 4 is N = 112, target (112,112,84), and a
     tiling + the 49-tile patch is a 161-tiling — the sole 161 candidate.

  C. The γ=2α r = 2 exclusion arithmetic (report §4): δ(u,v) = v for the
     corner chord (own routine, swept u < 24 — the report's script sweeps
     u < 50 with a different implementation; u < 24 covers both 132 tiles),
     the three residual lengths re-derived from patch side bookkeeping (BB:
     equal-side leftover u(v²−2u²); BC: base leftover v(v²−uv−u²); CC:
     2v(v²−uv−u²)), each either negative (overlap) or outside the edge
     semigroup ⟨u²,v²−u²,uv⟩; the general-proof identities swept u < 200
     ((v−u)b − vD = u³ etc.);
     containment of Beeson's no20 ((2,3), N = 20 [pub]); and the kill of
     BOTH 132 candidates (16,33,28) = (u,v) = (4,7) and (256,33,272) =
     (16,17) at r = 2.

  D. The 60°-equilateral exclusions at 105 (report §5): tile validity
     (c² = a²−ab+b²), δ = 3 resp. 4, the straight-multiset enumeration
     ({α+β+γ, 3γ} are the ONLY straight boundary multisets, and none
     contains α+α or β+β — swept exactly), the corner-orientation
     pigeonhole (all 8 corner configurations either put two b-patch ends on
     one side, overlapping since 2δb > 105, or leave every side mixed), and
     the mixed-side middle lengths 27 ∉ ⟨5,19,21⟩, 17 ∉ ⟨7,13,15⟩.

  E. The 120 forced-skeleton reduction (report §6): δ = 3 for (8,15,13),
     2δb = 90 < 120 (so the overlap argument does NOT apply — the two-b-end
     pattern instead dies by the unique decomposition 30 = 15+15 plus the
     α+α non-completability), uniqueness of both edge decompositions
     (30 → {(0,2,0)}, 51 → {(1,2,1)} exactly), and the remainder hexagon
     (51,39,51,39,51,39) with 120 − 3·3² = 93 tiles.

  F. The Group-2 row IV → row I and row IV → row III(b,a) transfers
     (report §7): full angle + side bookkeeping of both attachments (the
     merged side is bm(a+2b) = bmU for row I; count identities
     bW + b² = bU and bW + W² = UW; row I angles (α, α, α+3β) and sides
     bm(c,c,U) match the union exactly), and the concrete chains:
       IV(5,3;2)  N=96  (30,42,48) → I(5,3;2)  N=132  — 132's only candidate
       IV(8,7;1)  N=105          → I(8,7;1)  N=154  — 154's candidate
       IV(7,8;1)  N=120          → I(7,8;1)  N=184  — 184's candidate
       IV(16,5;1) N=105          → I(16,5;1) N=130  — classical (11²+3²)
     plus the row-III cascade values 330, 345, 352 with classicality audit.

  G. The revised frontier ledger: the candidate kill-list (two 60° at 105,
     two γ=2α at 132, shape-4 (4,7) at 132) and the surviving lists per
     value, matching report §7's table.

What this does NOT verify (the open audit items — STATUS §8):
  - Lemma 3.1's forced-corner-layer *induction* (the row-by-row growth of the
    δ-scaled corner patch).  Its angle-arithmetic hypotheses ARE verified
    here (sections C/D: endpoint sectors unique, equal-angle pairs not
    completable, straight multisets exact), and the boundary-partition
    facts it uses are standard; but the geometric assembly step ("the
    uniquely forced angle at every joint supplies the next row of 2k+1
    tiles") is a proof to audit, not an arithmetic identity.  It carries
    r ≥ 3, both 105 exclusions, and the 120 skeleton.
  - That the attachments in A/B/F produce *tilings* is immediate (a scaled
    tile carries its quadratic subdivision); the bookkeeping verified here
    is that the unions are the claimed targets.
"""

from fractions import Fraction as Fr
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


def in_semigroup(L, gens):
    """L ∈ ℕ₀·g1 + ℕ₀·g2 + ... — DP over reachable residues (independent of
    the report script's nested-loop implementation)."""
    if L < 0:
        return False
    reach = bytearray(L + 1)
    reach[0] = 1
    for g in gens:
        for x in range(g, L + 1):
            if reach[x - g]:
                reach[x] = 1
    return bool(reach[L])


def decompositions(L, gens):
    """All (n1,...,nk) with Σ ni·gi = L."""
    out = []

    def rec(i, rem, acc):
        if i == len(gens) - 1:
            if rem % gens[i] == 0:
                out.append(tuple(acc + [rem // gens[i]]))
            return
        for n in range(rem // gens[i] + 1):
            rec(i + 1, rem - n * gens[i], acc + [n])

    rec(0, L, [])
    return out


def is_square(n):
    return n >= 0 and isqrt(n) ** 2 == n


def is_sum_two_squares(n):
    return any(is_square(n - e * e) for e in range(isqrt(n) + 1))


def classical(n):
    return (is_square(n) or is_sum_two_squares(n)
            or (n % 2 == 0 and is_square(n // 2))
            or (n % 3 == 0 and is_square(n // 3))
            or (n % 6 == 0 and is_square(n // 6)))


# ---------------------------------------------------------------------------
# A. shape-1 route to q | m
# ---------------------------------------------------------------------------
def section_A():
    print("A. shape-4 q|m via the shape-1 patch (second, Thm-7-based route)")

    # Angle vectors (i, j) = iα + jβ in Group 1;  π = 3α + 2β,  γ = 2α + β.
    ALPHA, BETA, GAMMA, PI = (1, 0), (0, 1), (2, 1), (3, 2)
    add = lambda *v: tuple(map(sum, zip(*v)))
    # base vertex of shape-4 target (α+β) + tile γ  =  π  (vertex straightens)
    check("(α+β) + γ = π (base vertex straightens)",
          add(ALPHA, BETA, GAMMA) == PI)
    # apex α + tile α = 2α; tile's remaining vertex β; untouched vertex α+β
    check("union angles are (2α, β, α+β) — Beeson's shape 1",
          add(ALPHA, ALPHA) == (2, 0) and BETA == (0, 1)
          and add(ALPHA, BETA) == (1, 1))

    for q in range(2, 40):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            a, b, c = p * q, q * q - p * p, q * q
            h = 2 * q * q - p * p
            for m in range(1, 6):
                X, Y = b * q * m, b * p * m
                # glued side: the (qm)-scaled tile's b-side equals X exactly
                assert b * (q * m) == X
                # merged base = old base + tile a-side = pm·h; new side q³m
                assert Y + a * (q * m) == p * m * h
                assert c * (q * m) == q ** 3 * m
                # count identity
                assert b * m * m + (q * m) ** 2 == h * m * m
    check("side + count bookkeeping, all (p,q<40), m<6 (N' = hm²)", True)

    # Beeson's shape-1 exact count set for tile ratio s = p/q:
    # M² + N = 2K² with M/K = p/q  ⟹ (M,K) = (pt,qt), N = ht²;
    # Thm 7's condition K | M²  ⟺  qt | p²t²  ⟺  q | t   (gcd(p,q)=1).
    ok = True
    for q in range(2, 40):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            for t in range(1, 4 * q):
                M, K = p * t, q * t
                N = 2 * K * K - M * M
                assert N == (2 * q * q - p * p) * t * t
                ok &= ((M * M) % K == 0) == (t % q == 0)
    check("K | M² ⟺ q | t  ⟹  exact shape-1 set {q²hn²}", ok)

    # Cross-check against ALL EIGHT rows of Beeson's Table 1 (N ≤ 500):
    table1 = [(28, (2, 3, 4)), (112, (2, 3, 4)), (126, (6, 5, 9)),
              (153, (3, 8, 9)), (252, (2, 3, 4)), (368, (12, 7, 16)),
              (448, (2, 3, 4)), (496, (4, 15, 16))]
    ok = True
    for N, (a, b, c) in table1:
        g = gcd(a, c)
        p, q = a // g, isqrt(c)          # tile is (pq, q²−p², q²)
        assert (p * q, q * q - p * p, q * q) == (a, b, c)
        h = 2 * q * q - p * p
        ok &= N % (q * q * h) == 0 and is_square(N // (q * q * h))
    check("all 8 Table-1 rows are q²hn² (the iff's necessity side)", ok)

    # The comparison: hm² ∈ {q²hn²} ⟹ q | m; instance (4,7,2).
    p, q, m = 4, 7, 2
    h = 2 * q * q - p * p
    check("(4,7): h·2² = 132+64 = 196·? — not q²h·n² for any n "
          "(7 ∤ 2 ⟹ 132's shape-4 candidate dead)",
          not any(h * m * m == q * q * h * n * n for n in range(1, 10)))


# ---------------------------------------------------------------------------
# B. shape-4 → shape-5 transfer at m = qn
# ---------------------------------------------------------------------------
def section_B():
    print("B. shape-4 at m = qn  ⟹  shape-5 at n")
    ALPHA, BETA, GAMMA, PI = (1, 0), (0, 1), (2, 1), (3, 2)
    add = lambda *v: tuple(map(sum, zip(*v)))
    check("(α+β) + γ = π; (α+β) + β = α+2β; union = (α, α, α+2β) = shape 5",
          add(ALPHA, BETA, GAMMA) == PI
          and add(ALPHA, BETA, BETA) == (1, 2))
    for q in range(2, 40):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            a, b = p * q, q * q - p * p
            h = 2 * q * q - p * p
            for n in range(1, 6):
                # glued side: shape-4 base at m = qn is bpqn = a·(bn)
                assert b * p * (q * n) == a * (b * n)
                # count: shape-4 N + (bn)² = shape-5 ray at n
                assert b * (q * n) ** 2 + (b * n) ** 2 == b * h * n * n
    check("side + count bookkeeping, all (p,q<40), n<6 "
          "(lands on the verified shape-5 ray)", True)

    # the 161 route: (3,4) at m = q = 4
    p, q = 3, 4
    b, h = q * q - p * p, 2 * q * q - p * p
    m = q
    check("shape-4 (3,4) m=4: N = 112, target (112,112,84), tile (12,7,16)",
          b * m * m == 112 and (b * q * m, b * p * m) == (112, 84)
          and (p * q, b, q * q) == (12, 7, 16))
    check("112-tiling + 49-tile patch = 161-tiling (the sole 161 candidate)",
          112 + (b * 1) ** 2 == 161 and b * h == 161)


# ---------------------------------------------------------------------------
# C. γ=2α: r = 2 impossible
# ---------------------------------------------------------------------------
def section_C():
    print("C. γ=2α branch: δ = v and the three r = 2 orientation kills")

    # Angle arithmetic (basis α; π = 3α+β ⟹ β = π−3α, γ = 2α, α/π ∉ ℚ):
    # straight multisets iα+jβ+kγ = π ⟹ j = 1, i+2k = 3 ⟹ {3α+β, α+β+γ};
    # iα + jβ + kγ = π with β = π−3α, γ = 2α, α/π ∉ ℚ reduces exactly to
    # j = 1 and i + 2k = 3 (coefficient comparison in α and π):
    sols = [(i, j, k) for i in range(8) for j in range(8) for k in range(8)
            if j == 1 and i + 2 * k == 3]
    check("straight multisets are exactly {3α+β, α+β+γ} "
          "(no ββ, no γγ possible)", sorted(sols) == [(1, 1, 1), (3, 1, 0)])

    def in_two_gen(L, g1, g2):
        return L >= 0 and any((L - x * g1) % g2 == 0
                              for x in range(L // g1 + 1))

    ok_delta = ok_resid = True
    for u in range(2, 24):
        for v in range(u + 1, 2 * u):
            if gcd(u, v) != 1:
                continue
            a, b, c = u * u, v * v - u * u, u * v
            # δ = min d with d·a ∈ ⟨b, c⟩  (chord = a-side at an α corner)
            delta = next(d for d in range(1, 4 * v)
                         if in_two_gen(d * a, b, c))
            ok_delta &= delta == v
            # patch side bookkeeping at r = 2: base Y = 2vb, equal X = 2ub;
            # v-scaled patch puts (b on base, c on equal) [type B] or
            # (c on base, b on equal) [type C]; c·v = uv².
            L_BB_side = 2 * u * b - u * v * v          # equal-side leftover
            L_BC = 2 * v * b - v * b - u * v * v       # base leftover
            L_CC = 2 * v * b - 2 * u * v * v
            assert L_BB_side == u * (v * v - 2 * u * u)
            D = v * v - u * v - u * u
            assert L_BC == v * D and L_CC == 2 * v * D
            for L in (L_BB_side, L_BC, L_CC):
                ok_resid &= not in_semigroup(L, (a, b, c))
            # BB base is exactly filled: vb + vb = 2vb
            assert v * b + v * b == 2 * v * b
    check("δ(u,v) = v for all primitive u < 24", ok_delta)
    check("all three r=2 residuals negative or outside ⟨a,b,c⟩ (u < 24, "
          "incl. both 132 tiles)", ok_resid)

    ok_ids = True
    for u in range(2, 200):
        for v in range(u + 1, 2 * u):
            if gcd(u, v) != 1:
                continue
            b = v * v - u * u
            D = v * v - u * v - u * u
            L_CC = 2 * v * D
            ok_ids &= (v - u) * b - v * D == u ** 3
            w = v - u
            if 2 * w < u:
                ok_ids &= 2 * w * b - L_CC == 2 * u ** 3
            if 2 * w > u:
                ok_ids &= L_CC - (2 * v - 3 * u) * b == u * (v * v - 3 * u * u)
    check("general-proof identities ((v−u)b − vD = u³, CC cases; u < 200)",
          ok_ids)

    check("contains Beeson's no20 [pub]: (2,3) r=2 is N = 5·4 = 20",
          (2 * 2, 3 * 3 - 2 * 2, 2 * 3) == (4, 5, 6) and 5 * 4 == 20)
    check("132 kill #1: (16,33,28) = (u,v)=(4,7), r=2, N = 33·4 = 132",
          (16, 33, 28) == (4 * 4, 7 * 7 - 16, 4 * 7) and 33 * 4 == 132)
    check("132 kill #2: (256,33,272) = (u,v)=(16,17), r=2, N = 132",
          (256, 33, 272) == (16 * 16, 17 * 17 - 256, 16 * 17) and 33 * 4 == 132)
    # consistency with the branch's known positive: Herdt 720 = r 12 ≥ 3
    check("consistent with Herdt's 720 (r = 12 on (4,5,6)) and transport set",
          720 == 5 * 12 * 12 and all(r >= 3 for r in (12, 18, 27)))


# ---------------------------------------------------------------------------
# D. 60°-equilateral candidates at 105
# ---------------------------------------------------------------------------
def section_D():
    print("D. 60° tiles at 105: both candidates impossible")

    # Angle arithmetic (α+β = 2π/3, γ = π/3, α/π ∉ ℚ): straight multisets
    # iα+jβ+kγ = π  ⟹  i = j, 2j+k = 3  ⟹  {α+β+γ, 3γ}; neither contains
    # αα or ββ (i = j ≤ 1).
    sols = sorted((i, j, k) for i in range(8) for j in range(8)
                  for k in range(8) if i == j and 2 * j + k == 3)
    check("straight multisets are exactly {α+β+γ, 3γ}; αα/ββ impossible",
          sols == [(0, 0, 3), (1, 1, 1)])

    for (a, b, c), want_delta, want_mid in [((5, 21, 19), 3, 27),
                                            ((7, 15, 13), 4, 17)]:
        check(f"({a},{b},{c}): 60° tile (c² = a²−ab+b²)",
              c * c == a * a - a * b + b * b)
        delta = next(d for d in range(1, 50) if in_semigroup(d * c, (a, b)))
        check(f"({a},{b},{c}): δ = {want_delta}", delta == want_delta)
        L = 105
        check(f"({a},{b},{c}): two b-ends on one side overlap (2δb > 105)",
              2 * delta * b > L)
        # corner pigeonhole: each corner sends a to one adjacent side, b to
        # the other (2³ configurations); every configuration either has a
        # side with two b-ends (overlap) or all three sides mixed.
        all_ok = True
        for cfg in range(8):
            # sides 0,1,2; corner i sits between sides i and (i+1)%3
            ends = {s: [] for s in range(3)}
            for i in range(3):
                if (cfg >> i) & 1:
                    ends[i].append("a"); ends[(i + 1) % 3].append("b")
                else:
                    ends[i].append("b"); ends[(i + 1) % 3].append("a")
            twob = any(e.count("b") == 2 for e in ends.values())
            mixed = all(sorted(e) == ["a", "b"] for e in ends.values())
            all_ok &= twob or mixed
        check(f"({a},{b},{c}): all 8 corner configs → overlap or all-mixed",
              all_ok)
        mid = L - delta * (a + b)
        check(f"({a},{b},{c}): mixed-side middle = {want_mid}",
              mid == want_mid)
        check(f"({a},{b},{c}): {want_mid} ∉ ⟨{a},{c},{b}⟩ — contradiction",
              not in_semigroup(mid, (a, b, c)))


# ---------------------------------------------------------------------------
# E. the 120 candidate's forced skeleton
# ---------------------------------------------------------------------------
def section_E():
    print("E. 60° tile (8,15,13) at 120: forced cyclic skeleton")
    a, b, c = 8, 15, 13
    check("(8,15,13) is a 60° tile", c * c == a * a - a * b + b * b)
    delta = next(d for d in range(1, 50) if in_semigroup(d * c, (a, b)))
    check("δ = 3 (3c = 3a+b = 39)", delta == 3 and 3 * c == 3 * a + b)
    check("2δb = 90 < 120 — overlap argument does NOT close this one",
          2 * delta * b < 120)
    check("two-b-end side residual 30 decomposes ONLY as 15+15",
          decompositions(30, (a, b, c)) == [(0, 2, 0)])
    check("mixed-side middle 51 decomposes ONLY as {8,15,15,13}",
          decompositions(51, (a, b, c)) == [(1, 2, 1)])
    check("remainder hexagon (51,39,51,39,51,39), 120 − 3·9 = 93 tiles",
          120 - delta * (a + b) == 51 and delta * c == 39
          and 120 - 3 * delta ** 2 == 93)


# ---------------------------------------------------------------------------
# F. Group-2 row IV → row I / row III transfers
# ---------------------------------------------------------------------------
def section_F():
    print("F. Group-2 transfers: IV(a,b;m) ⟹ I(a,b;m) and III(b,a;m)")

    # Angle vectors (i, j) = iα + jπ in Group 2 (β = π/3 − α, γ = 2π/3):
    A = (1, Fr(0));  B = (-1, Fr(1, 3));  G = (0, Fr(2, 3));  PI = (0, Fr(1))
    add = lambda *v: (sum(x for x, _ in v), sum(y for _, y in v))
    # row IV angles (α, α+β, α+2β); glued side ka is opposite α, its ends
    # are the (α+β) and (α+2β) vertices; tile a-edge carries (β, γ).
    check("(α+β) + γ = π (row-IV vertex straightens)",
          add(A, B, G) == PI)
    check("(α+2β) + β = α+3β = π−2α (row-I apex)",
          add(A, B, B, B) == add(PI, (-2, Fr(0))))

    ok_sides = ok_counts = True
    for a in range(2, 45):
        for b in range(2, 45):
            c2 = a * a + a * b + b * b
            c = isqrt(c2)
            if c * c != c2 or gcd(gcd(a, b), c) != 1:
                continue
            U, V, W = a + 2 * b, 2 * a + b, a + b
            for m in range(1, 4):
                k = b * m
                # row IV sides k(a,c,W); N_IV = k²·(a+b)/b = bWm²
                assert k * k * (a + b) % b == 0
                assert k * k * (a + b) // b == b * W * m * m
                # attach (bm)-scaled tile on side ka = abm via its a-edge:
                # merged side = kW + (bm)·b = bm(a+2b) = bmU;
                ok_sides &= k * W + b * m * b == b * m * U
                # union sides bm(c,c,U) = row I at multiplier m; count:
                ok_counts &= b * W * m * m + (b * m) ** 2 == b * U * m * m
                # row III variant: attach (Wm)-scaled tile on side kW = bWm
                # via its b-edge; count lands on row III of the swapped tile:
                ok_counts &= b * W * m * m + (W * m) ** 2 == U * W * m * m
                assert (2 * b + a) * (b + a) == U * W  # = row III(b,a)
                # tile-copy variant: bW + a² = c²
                assert b * W + a * a == c * c
    check("merged-side identity kW + b²m = bmU (row-I sides bm(c,c,U))",
          ok_sides)
    check("count identities bW+b² = bU, bW+W² = UW, bW+a² = c² "
          "(all primitive 120° tiles a,b < 45)", ok_counts)

    # row-I angle/side sanity on the searcher's own N132 instance:
    a, b, c = 5, 3, 7
    U = a + 2 * b
    check("N132 = row I (5,3,7) k=6: sides (42,42,66) = 6·(7,7,11), "
          "N = 3·11·2² = 132", (6 * c, 6 * c, 6 * U) == (42, 42, 66)
          and b * U * 4 == 132)

    # the four concrete chains:
    chains = [((5, 3), 2, 96, 132), ((8, 7), 1, 105, 154),
              ((7, 8), 1, 120, 184), ((16, 5), 1, 105, 130)]
    for (a, b), m, n_iv, n_i in chains:
        W, U = a + b, a + 2 * b
        check(f"IV({a},{b};{m}) N={n_iv} ⟹ I({a},{b};{m}) N={n_i}",
              b * W * m * m == n_iv and b * U * m * m == n_i)
    check("N=96 target sides 6·(5,7,8) = (30,42,48)",
          (6 * 5, 6 * 7, 6 * 8) == (30, 42, 48))
    check("130 is classical (11²+3²) — that chain adds no frontier info",
          classical(130) and 130 == 121 + 9)
    # row-III cascade: IV(8,7;1)→III(7,8;1)=330, IV(7,8;1)→III(8,7;1)=345,
    # IV(5,3;2)→III(3,5;2)=352 = 88·2² (row III (3,5,7) already solved)
    check("row-III cascade counts 330/345/352",
          (2 * 7 + 8) * 15 == 330 and (2 * 8 + 7) * 15 == 345
          and (2 * 3 + 5) * 8 * 4 == 352)
    check("330, 345 non-classical (new members if 105/120 row-IV tile); "
          "352 = 88·2² already in S",
          not classical(330) and not classical(345) and 352 == 88 * 4)


# ---------------------------------------------------------------------------
# G. revised frontier ledger
# ---------------------------------------------------------------------------
def section_G():
    print("G. historical report-5.2 candidate ledger (before report #7)")
    killed = {
        105: ["60° (5,21,19)", "60° (7,15,13)"],
        132: ["shape-4 (4,7) m=2", "γ=2α (16,33,28) r=2",
              "γ=2α (256,33,272) r=2"],
    }
    alive = {
        105: ["row IV (8,7,13) m=1", "row IV (16,5,19) m=1"],
        120: ["row IV (7,8,13) m=1", "60° (8,15,13) [forced skeleton]"],
        132: ["row I (5,3,7) m=2"],
        143: ["row V (3,5,7) m=1"],
        154: ["row I (8,7,13) m=1"],
        161: ["shape 5 (3,4) n=1"],
        184: ["row I (7,8,13) m=1"],
    }
    check("132 has exactly ONE surviving candidate", len(alive[132]) == 1)
    check("105 is decided by its two row-IV searches alone",
          len(alive[105]) == 2 and len(killed[105]) == 2)
    check("historical report-5.2 list is 105,120,132,143,154,161,184 "
          "(not a check of the current frontier)",
          sorted(alive) == [105, 120, 132, 143, 154, 161, 184])
    for n in alive:
        print(f"  INFO N={n}: {len(alive[n])} historical candidate(s): "
              f"{'; '.join(alive[n])}")


def main():
    section_A()
    section_B()
    section_C()
    section_D()
    section_E()
    section_F()
    section_G()
    print(f"\n{PASS} PASS, {FAIL} FAIL")
    if FAIL:
        raise SystemExit(1)
    print("ALL REPORT-5.2 CHECKS PASSED (see header for what is NOT covered)")


if __name__ == "__main__":
    main()
