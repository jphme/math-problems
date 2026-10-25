# No19Tiling: Lean 4 formalization of the arithmetic of no19tiling

[![Lean](https://github.com/jphme/math-problems/actions/workflows/lean.yml/badge.svg)](https://github.com/jphme/math-problems/actions/workflows/lean.yml)

This Lake package formalizes, in Lean 4 with Mathlib, the integer arithmetic and the case analysis
of the paper *No triangle can be cut into nineteen congruent triangles: the prime case of Erdős
Problem 634* ([`../no19tiling.pdf`](../no19tiling.pdf), source [`../no19tiling.tex`](../no19tiling.tex)).
The paper's section "Verification" describes this development.

What is proved here, in one sentence: if a prime `N > 3` with `N ≡ 3 (mod 4)` admits one of the
outcomes that the imported theorems and the geometric lemmas of the paper provide for a tiling, then
a contradiction follows, with the Beeson–Roşu theorem (`thm:BR`) as an explicit hypothesis; for
`N ≡ 19 (mod 24)`, and so for `N = 19`, without that hypothesis. The geometry, the trigonometry and
the imported theorems are not formalized; they enter as hypotheses, listed in
[What is assumed and what is not formalized](#what-is-assumed-and-what-is-not-formalized).

The development contains no `sorry`, and every theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound` ([Axioms](#axioms)).

Paper results are cited below by name and LaTeX label (`\label{...}` in `no19tiling.tex`), not by
number. Lean doc comments use the same labels.

## Build

Toolchain `leanprover/lean4:v4.30.0` (pinned in `lean-toolchain`), Mathlib `v4.30.0` (pinned in
`lake-manifest.json`). Install [elan](https://github.com/leanprover/elan), then, in this directory:

```sh
lake exe cache get                     # downloads the prebuilt Mathlib
lake build                             # builds the seven No19Tiling modules
lake env lean No19Tiling/Axioms.lean   # prints the axioms of every theorem
```

Observed on 2026-10-25 on an Apple M5 Pro laptop, with the Mathlib cache already unpacked and
`.lake/build` deleted first: `lake build` took 9.2 s wall clock (each module 1–4 s); `/usr/bin/time
-l` reported a maximum resident set size of 2.2 GB, almost all of it shared, memory-mapped Mathlib
`.olean` files, and a peak memory footprint of 180 MB. The axiom check took 1.7 s (maximum resident
set size 2.1 GB, peak memory footprint 133 MB). The build output is 11 MB. The modules import
individual Mathlib files, not all of `Mathlib`. The GitHub Actions workflow of this repository builds
the package, checks that there is no `sorry`, and runs the axiom check.

## Files

| File | Content |
|---|---|
| `No19Tiling/Common.lean` | `Primitive3`, `SidesIntegral`, the scale lemma, sums of two squares mod 4, the structure `G2Triple` (primitive solution of `c^2 = a^2+ab+b^2`) with pairwise coprimality, `3 ∤ c` and the relabeling `swap` |
| `No19Tiling/Group2.lean` | Lemma `lem:group2`: the four side vectors, their primitivity, the four counts |
| `No19Tiling/Group1.lean` | the Group-1 tile `(mk, k^2-m^2, k^2)` (`G1Param`); Lemmas `lem:g1counts`, `lem:g1residues`, `lem:shape4` (arithmetic part), `lem:shape5` |
| `No19Tiling/Lattice.lean` | Appendix A, Lemmas `app:lattice` and `app:decomp`: the relation lattice of the Group-1 tile and the edge decompositions (facts (L1)–(L3)) used in the proof of the Group-1 scale-one cases |
| `No19Tiling/RowI.lean` | Lemma `lem:rowI`: the Laurent-polynomial evaluation for the isosceles target (part (a)) and the equilateral target (part (b)) |
| `No19Tiling/Assembly.lean` | the case analysis of Section `sec:proof`: `Outcome`, `reduction`, `main_theorem`, `main_theorem_19_mod_24`, `no_nineteen` |
| `No19Tiling/Axioms.lean` | `#print axioms` for every theorem listed below (not part of the library build) |
| `No19Tiling.lean` | root module |

## Conventions

* A Group-2 tile (angle `2π/3`) is a `G2Triple`: natural numbers `a, b, c` with `0 < a`, `0 < b`,
  `c^2 = a^2 + a*b + b^2` and `gcd(gcd(a, b), c) = 1` (a primitive triple in the sense of Lemma
  `lem:group2`). The other labeling of the two acute angles (`α ↔ β`) is `t.swap = (b, a, c)`.
  Every Group-2 statement is proved for an arbitrary `G2Triple`, so it holds for both labelings;
  `lem_group2_both_labelings` and `rowI_swap_not_prime` spell this out.
* A Group-1 tile (`3α + 2β = π`) is a `G1Param`: coprime natural numbers `0 < m < k`; the tile is
  `(mk, k^2-m^2, k^2)` as in Lemma `lem:g1tile`, with `h = 2k^2-m^2`, `g = 3k^2-m^2` and
  `b = k^2-m^2`. These are natural-number differences; because `m < k` they are the true
  differences (`G1Param.cast_h`, `G1Param.cast_g`, `G1Param.cast_b` state this in `ℤ`).
* An *edge decomposition* of a length `L` (Appendix A) is a triple of natural numbers `(p, q, r)`
  with `p (mk) + q b + r k^2 = L`: `p` a-edges, `q` b-edges and `r` c-edges partitioning a segment of
  length `L`.
* Boundary integrality, Lemma `lem:bdry`(c) (every side of the tiled triangle is an integer), enters
  as `SidesIntegral m x y z`: the rational numbers `m*x`, `m*y`, `m*z` are integers, where `m > 0`
  is the rational scale from the integer side vector `(x, y, z)` to the tiled triangle.
* Side vectors and tile counts are data taken from the paper; their derivation from the laws of
  sines and cosines and the area formula is not formalized. A count is stated over `ℚ`, and where
  the paper divides it is cleared of denominators: `N * b = m^2 (a+b)` for case C of Lemma
  `lem:group2`, `N * b = k^2 (a+2b)` for Lemma `lem:rowI`(a), `N * ab = L^2` for Lemma
  `lem:rowI`(b), `N * b = t^2` for Lemma `lem:shape4`, `N * b = t^2 h` for Lemma `lem:shape5`.

## Theorems and the paper statements they formalize

### Common.lean

| Lean | Statement | Paper |
|---|---|---|
| `scale_int_of_primitive3`, `scale_nat_of_primitive3` | if `(x,y,z)` is primitive and `m*x, m*y, m*z ∈ ℤ` for a rational `m`, then `m ∈ ℤ`; with `m > 0`, `m` is a positive natural number | proof of Lemma `lem:group2`, "The scale factor is an integer" (Bézout); reused in Lemmas `lem:rowI`, `lem:g1counts`, `lem:shape4`, `lem:shape5` |
| `G2Triple.coprime_ab`, `coprime_ac`, `coprime_bc` | `a, b, c` are pairwise coprime | proof of Lemma `lem:group2`, first paragraph |
| `G2Triple.not_three_dvd_c` | `3 ∤ c` | equation `eq:not3` |
| `sq_add_sq_mod_four` | `x^2 + y^2 ≢ 3 (mod 4)` | proof of Theorem `thm:main`, Step 2; Lemma `lem:shape5` |

### Group2.lean: Lemma `lem:group2`

| Lean | Statement |
|---|---|
| `primitive_A` … `primitive_D` | the side vectors A `(c^2, c(a+2b), 3b(a+b))`, B `(ac, b(2a+b), c(a+b))`, C `(a, c, a+b)`, D `(a(a+2b), b(2a+b), c^2)` of the table in the proof are primitive ("The vectors are primitive") |
| `countA_not_prime`, `countB_not_prime`, `countD_not_prime` | for every integer `m ≥ 1`, `3m^2(a+2b)(a+b)`, `m^2(2a+b)(a+b)`, `m^2(a+2b)(2a+b)` are not prime ("Conclusion") |
| `countC_not_prime` | if `N * b = m^2 (a+b)`, then `N` is not prime ("Conclusion", case C) |
| `lem_group2` | for each case `X ∈ {A, B, C, D}`: if `m > 0` is rational, `m · sideVec X` is integral and `N` satisfies the count of case `X` (`countEq`), then `N` is not prime |
| `lem_group2_both_labelings` | `lem_group2` for the triple and for its swap (the relabelings in the last sentence of the proof) |

### Group1.lean: Section `sec:group1`

| Lean | Statement | Paper |
|---|---|---|
| `tile_primitive` | `(mk, k^2-m^2, k^2)` is primitive | Lemma `lem:g1tile` (primitivity only) |
| `triVec_primitive`, `isoVec_primitive`, `shape2Vec_primitive` | `(mh, k(k^2-m^2), k^3)`, `(k^3, k^3, mg)`, `(k^4, k^2h, bg)` are primitive | Lemma `lem:g1counts`, proof |
| `eq_one_of_prime_sq_mul` | a prime `N = j^2 x` with `x ≥ 2` forces `j = 1` | Lemma `lem:g1residues`, proof |
| `two_sq_sub_sq_mod_eight` | for all integers `k, m`: an odd `2k^2-m^2` is `≡ 1` or `7 (mod 8)` | Lemma `lem:g1residues`(a) |
| `three_sq_sub_sq_mod_three` | for all integers `k, m`: `3k^2-m^2 ≢ 1 (mod 3)` | Lemma `lem:g1residues`(b) |
| `h_count_prime_mod8`, `g_count_prime_mod3` | a prime `j^2 h` is `≢ 3 (mod 8)`; a prime `j^2 g` is `≢ 1 (mod 3)` | Lemma `lem:g1residues`, "Consequently" |
| `triquadratic` | target `(2α, β, α+β)`, sides `j · (mh, k(k^2-m^2), k^3)` with rational `j > 0` and integral sides, `N = j^2 h` prime: then `j = 1`, `N = h`, `N ≢ 3 (mod 8)` | Lemma `lem:g1counts`(a) with Lemma `lem:g1residues` |
| `isoBeta` | target `(β, β, 3α)`, sides `j · (k^3, k^3, mg)`, `N = j^2 g` prime: then `j = 1`, `N = g`, `N ≢ 1 (mod 3)` | Lemma `lem:g1counts`(b) with Lemma `lem:g1residues` |
| `triquadratic_not_19_mod_24`, `isoBeta_not_19_mod_24` | a prime `j^2 h` or `j^2 g` is not `≡ 19 (mod 24)` | Lemma `lem:g1residues`, last sentence |
| `shape2_not_prime` | target `(α, 2α, 2β)`, sides `j · (k^4, k^2h, bg)`, `N = j^2hg`: `N` is not prime | Lemma `lem:g1counts`(c) with Lemma `lem:g1residues` |
| `shape4_prime_no_c_edge` | sides `t (k, k, m)`, `N b = t^2`, base `t m = A(mk) + Bb + Ck^2` with `A, B, C ≥ 0`: a prime `N` forces `C = 0` | Lemma `lem:shape4`, arithmetic part (equation `eq:base4`) |
| `shape4_not_prime`, `shape4_not_prime_rat` | the same with `C ≥ 1` as hypothesis (integer, resp. rational scale `t`): `N` is not prime | Lemma `lem:shape4` |
| `shape5_prime`, `shape5_not_3_mod_4`, `shape5_not_3_mod_4_rat` | target `(α, α, α+2β)`, sides `t (k^2, k^2, h)`, `N b = t^2 h`: a prime `N` equals `h = k^2 + t^2` with `t^2 = b`, hence `N ≢ 3 (mod 4)` | Lemma `lem:shape5` |
| `shape4Vec_primitive`, `shape5Vec_primitive` | `(k, k, m)` and `(k^2, k^2, h)` are primitive | proofs of Lemmas `lem:shape4`, `lem:shape5` |

Corollary `cor:g1prime` has no single Lean counterpart: it is the conjunction of `shape2_not_prime`,
`triquadratic`, `isoBeta`, `shape4_not_prime_rat` and `shape5_not_3_mod_4_rat`, and it is used in
that form inside `reduction`.

### Lattice.lean: Appendix A, Lemmas `app:lattice` and `app:decomp`

The tile is `(a, b, c) = (mk, k^2-m^2, k^2)` of a `G1Param`. These are the arithmetic facts of the
self-contained proof of the Group-1 scale-one cases, the targets `(β, β, 3α)` and `(2α, β, α+β)`
with `j = 1`; in the working notes they are facts (L1), (L2), (L3) and the leg step of the proof
for `(β, β, 3α)`. The lengths that occur are the legs `kc = k^3` and the base `m(b+2c) = mg` of
`(β, β, 3α)` (the entries of `isoVec`; `g_eq` gives `g = b + 2c`) and the side `m(b+c) = mh`
opposite `2α` of `(2α, β, α+β)` (the first entry of `triVec`; `h_eq` gives `h = b + c`). As in
`Group1.lean`, these side lengths are data from the paper; the geometric half of that proof (side
partitions, runs of `c`-edges, the pigeonhole on a side) is not formalized. The theorems of this
module stand alone: `reduction` and the main theorems do not use them.

| Lean | Statement | Paper |
|---|---|---|
| `lattice_iff` | for integers `x, y, z`: `x a + y b + z c = 0` iff `(x, y, z) = ξ (k, 0, -m) + η (m, k, -k)` for some integers `ξ, η` | Lemma `app:lattice` (L1) |
| `decomp_shift` | two integer triples with the same value `p a + q b + r c` differ by `ξ (k, 0, -m) + η (m, k, -k)` | Lemma `app:lattice`, the form in which the proof of Lemma `app:decomp` uses it |
| `decomp_a` | for `n < k`: `p a + q b + r c = n a` forces `(p, q, r) = (n, 0, 0)` | Lemma `app:decomp` (L2)(A) |
| `decomp_b` | for `n < k`: `p a + q b + r c = n b` forces `(p, q, r) = (0, n, 0)` | Lemma `app:decomp` (L2)(B) |
| `decomp_c_no_b` | for `n < k`: `p a + q b + r c = n c` forces `q = 0` | Lemma `app:decomp` (L2)(C) |
| `decomp_mb2c_lt_k` | `p a + q b + r c = m(b + 2c)` with `p ≥ 1` forces `r < k` | Lemma `app:decomp` (L3)(i) |
| `decomp_mbc` | `p a + q b + r c = m(b + c)` forces `(p, q, r) = (0, m, m)` or `(k, m, 0)` | Lemma `app:decomp` (L3)(ii) |
| `leg_no_b_edge` | `p a + q b + r c = k c` with `r ≥ 1` forces `q = 0` | Lemma `app:decomp`, (L2)(C) applied to `(k - r) c`: a leg of `(β, β, 3α)` carries no `b`-edge |
| `cast_b`, `g_eq` | `b = k^2 - m^2` in `ℤ`; `g = b + 2k^2` | auxiliary |

### RowI.lean: Lemma `lem:rowI`

The Laurent polynomial ring `ℤ[z, z⁻¹]` is Mathlib's `LaurentPolynomial ℤ`, with `z = T 1` and
`z⁻¹ = T (-1)`. Notation as in the proof of the lemma: `d = a - b`, `U = a + 2b`,
`I = (d + cz, d + cz⁻¹)`, and `ε : ℤ[z, z⁻¹] → ℤ/3abℤ` the ring homomorphism with `ε(z) = -d c⁻¹`.

| Lean | Statement | Paper |
|---|---|---|
| `norm_b_ne_one`, `two_le_b`, `two_le_a` | `b = 1` is impossible in `c^2 = a^2+ab+b^2`, so `a, b ≥ 2` | proof, "Arithmetic of the tile" |
| `not_three_dvd_d`, `isCoprime_c`, `isCoprime_d` | `3 ∤ a - b`; `c` and `d` are coprime to `3ab`, so units modulo `3ab` | proof, "Arithmetic of the tile" |
| `three_ab_mem` | `3ab ∈ I` | auxiliary, not used by the main theorems: the reason why `ℤ/3abℤ` is the natural target of `ε` |
| `eps_kills_ideal` | `I ≤ ker ε` (`ε` is `LaurentPolynomial.eval₂` at the unit `w = -d c⁻¹`) | proof, "Evaluation" |
| `coprime_c_U`, `rowI_primitive` | `gcd(c, a+2b) = 1`, so `(c, c, a+2b)` is primitive | proof of (a) |
| `d_mul_eps_rowI` | `d · ε(U - cz⁻¹ - cz) = 3a^2` in `ℤ/3abℤ` | proof of (a), identity `(a-b)(a+2b) + (a^2+ab+b^2) + (a-b)^2 = 3a^2` |
| `eps_rowIBoundary_eq_zero_iff` | `ε(k(U - cz⁻¹ - cz)) = 0 ↔ b ∣ k` | proof of (a) |
| `b_dvd_of_rowIBoundary_mem` | `k(U - cz⁻¹ - cz) ∈ I → b ∣ k` | proof of (a) |
| `rowI_not_prime_of_dvd` | `b ∣ k` and `N b = k^2(a+2b)` make `N` not prime | (a), "In particular" |
| `rowI_not_prime`, `rowI_not_prime_rat` | integer (resp. rational, with integral sides) scale `k`, `N b = k^2(a+2b)`, and the premise `RowIPremise`: `N` is not prime | (a) |
| `rowI_swap_not_prime` | base angles `β`: sides `k(c, c, 2a+b)`, `N a = k^2(2a+b)` | (a), relabeled statement |
| `ab_dvd_of_rowE`, `rowE_not_prime` | equilateral target of side `L`: `±3L z^e ∈ I → ab ∣ L`; with `N ab = L^2`, `N` is not prime | (b) |
| `exists_three_dvd_a_add_b` | `(7, 8, 13)` is a primitive triple with `3 ∣ a + b` | not in the paper (see [Notes](#notes-on-deviations-from-the-paper)) |

The target boundary polynomial is `rowIBoundary k = k · (U - c z⁻¹ - c z)`, the value
`B(∂T) = χ(θ₀) k (U - cz⁻¹ - cz)` of the proof of (a) without the unit factor `χ(θ₀)`. For the
equilateral target, `rowEBoundary L e = 3L z^e`, the value `B(∂T) = 3L χ(θ₀)` of the proof of (b)
with `χ(θ₀) = ±z^e`. Membership of these polynomials in `I` is the output of Lemma
`lem:character`(ii), which is geometric and enters as the hypotheses
`RowIPremise t k := rowIBoundary k ∈ I` and
`RowEPremise t L := ∃ e, 3L z^e ∈ I ∨ -3L z^e ∈ I`. The same evaluation appears as rows I and E of
the Laurent boundary quotient in
[progress634](https://github.com/jphme/math-problems/tree/main/progress634) (Theorem
`thm:laurent`, Corollary `cor:rows`, Appendix `app:rowalgebra`); the isomorphism
`ℤ[z,z⁻¹]/I ≅ ℤ/3abℤ` proved there is not needed and not formalized, only `I ≤ ker ε` is.

### Assembly.lean: Theorems `thm:main` and `thm:nineteen`

`Outcome Q N` is an inductive proposition with one constructor for each branch of the proof in
Section `sec:proof`, carrying the arithmetic data that the theorem or lemma handling that branch
provides. "Imported conclusion" means that the constructor carries the conclusion of an imported
theorem as stated there.

| Constructor | Branch (Section `sec:proof`) | Source of the data | Data carried |
|---|---|---|---|
| `reptile_sq`, `reptile_sum_sq`, `reptile_three_sq` | reptilings: Step 2, reached from Step 1b (line 1 of Theorem `thm:isoclass`), Step 3 and Step 4; `reptile_sq` also carries Step 1a(i) (equilateral tile) | Theorem `thm:reptile` (Snover–Waiveris–Williams); for Step 1a(i), Lemma `lem:bdry`(c) and the area | `N = M^2`, `N = M^2+K^2`, `N = 3M^2` |
| `equi_ii` | Step 1a(ii): equilateral `T`, tile `(π/6, π/6, 2π/3)` | elementary, in the proof: Lemma `lem:bdry`(a) and the area equation | `N = u^2 ∨ N = 3v^2` |
| `equi_iii` | Step 1a(iii): equilateral `T`, tile `(π/6, π/3, π/2)` | elementary, in the proof: Lemma `lem:bdry`(a) and the area equation | `N = 2n^2 ∨ N = 6n^2` |
| `equi_iv` | Step 1a(iv): equilateral `T`, tile `(α, β, π/3)` with `α/π` irrational | Theorem `thm:counts`(c) | `¬ N.Prime` (imported conclusion) |
| `equi_v` | Step 1a(v): equilateral `T`, tile `(α, β, 2π/3)` | Theorem `thm:rational`(a), Lemma `lem:rowI`(b) | side `L`, `N ab = L^2`, `RowEPremise` |
| `iso_right` | Step 1b, line 2 of Theorem `thm:isoclass` (right tile) | Theorem `thm:counts`(a) | `2 < N → ¬ N.Prime` (imported conclusion) |
| `iso_gamma2alpha` | Step 1b, line 3 (`γ = 2α`) | Theorem `thm:counts`(b) | `¬ Squarefree N` (imported conclusion) |
| `iso_rowI` | Step 1b, line 4 (`γ = 2π/3`; base angles `β` via `t.swap`) | Theorem `thm:rational`(a), Lemma `lem:rowI`(a) | rational `k > 0`, integral sides `k(c, c, a+2b)`, `N b = k^2(a+2b)`, `RowIPremise` |
| `g1_shape5` | Step 1b, line 5, target `(α, α, α+2β)` | Theorem `thm:rational`(b), Lemma `lem:shape5` | rational `t > 0`, integral sides `t(k^2, k^2, h)`, `N b = t^2 h` |
| `g1_isoBeta` | Step 1b, line 6, target `(β, β, 3α)` | Theorem `thm:rational`(b), Lemma `lem:g1counts`(b) | rational `j > 0`, integral sides `j(k^3, k^3, mg)`, `N = j^2 g`, `Q.IsoBeta P j N` |
| `g1_shape4` | Step 1b, line 7, target `(α+β, α+β, α)` | Theorem `thm:rational`(b), Lemma `lem:shape4` | rational `t > 0`, integral sides `t(k, k, m)`, `N b = t^2`, base `t m = A(mk) + Bb + Ck^2`, `1 ≤ C` |
| `g1_shape2` | Step 4, Group 1, target `(α, 2α, 2β)` | Theorem `thm:classification`(2), Theorem `thm:rational`(b), Lemma `lem:g1counts`(c) | rational `j > 0`, integral sides `j(k^4, k^2h, bg)`, `N = j^2hg` |
| `g1_triquad` | Step 4, Group 1, target `(2α, β, α+β)` | Theorem `thm:classification`(2), Theorem `thm:rational`(b), Lemma `lem:g1counts`(a) | rational `j > 0`, integral sides `j(mh, k(k^2-m^2), k^3)`, `N = j^2 h`, `Q.Triquad P j N` |
| `g2_scalene` | Step 4, Group 2, cases A–D, both labelings | Theorem `thm:classification`(3), Theorem `thm:rational`(a), Lemma `lem:group2` | case `X`, rational `m > 0`, integral sides `m · sideVec X`, `countEq` |

`Q : TilingPredicates` consists of two abstract predicates, `Q.IsoBeta P j N` and `Q.Triquad P j N`,
read as "the triangle with angles `(β, β, 3α)` (resp. `(2α, β, α+β)`) and sides `j` times the vector
above is tiled by `N` copies of the tile `P`". They are needed because Theorem `thm:BR` is a
statement about the existence of tilings, which the arithmetic data cannot express.

| Lean | Statement | Paper |
|---|---|---|
| `reduction` | if `N > 3` is prime, `N ≡ 3 (mod 4)` and `Outcome Q N`, then `Q.Triquad P 1 N` with `N = 2k^2-m^2 ≡ 7 (mod 8)`, or `Q.IsoBeta P 1 N` with `N = 3k^2-m^2 ≡ 11 (mod 12)`, for some `P` | Section `sec:proof`, Steps 1a–4, with Corollary `cor:g1prime` |
| `main_theorem` | assume `hBR37 : ∀ P N, ¬ Q.IsoBeta P 1 N` and `hBR41 : ∀ P N, ¬ Q.Triquad P 1 N`; if `N > 3` is prime, `N ≡ 3 (mod 4)` and `Outcome Q N`, then `False` | Theorem `thm:main`; the hypotheses are Theorem `thm:BR` (Beeson–Roşu, arXiv:2607.23453v3, Theorem 37 for the shape `(β, β, 3α)` and Theorem 41 for `(2α, β, α+β)`) |
| `main_theorem_19_mod_24` | if `N` is prime, `N ≡ 19 (mod 24)` and `Outcome Q N`, then `False`, for every `Q` | Theorem `thm:nineteen` |
| `no_nineteen` | `Outcome Q 19 → False`, for every `Q` | Theorem `thm:main`, case `p = 19` |

## What is assumed and what is not formalized

The main theorems take the following as hypotheses.

* `hO : Outcome Q N`, the statement that a tiling of a triangle by `N` congruent triangles falls into
  one of the branches above with the data listed there. This hypothesis carries everything that is
  not formalized:
  * the imported theorems of Section `sec:imports`: Theorems `thm:commensurable`, `thm:reptile`,
    `thm:classification`, `thm:isoclass`, `thm:equiclass`, `thm:rational` and `thm:counts`; the
    constructors `iso_right`, `iso_gamma2alpha` and `equi_iv` carry the conclusions of
    Theorem `thm:counts`(a), (b), (c) as stated in the cited papers;
  * the geometric lemmas of Section `sec:tools`: Lemma `lem:bdry` (boundary decomposition and
    integrality, carried as `SidesIntegral` and as the base decomposition in `g1_shape4`), Lemma
    `lem:irr`, and Lemma `lem:character` (carried as `RowIPremise` and `RowEPremise`);
  * the parametrization of Lemma `lem:g1tile`, the side vectors and area equations of Lemmas
    `lem:group2`, `lem:rowI`, `lem:g1counts`, `lem:shape4`, `lem:shape5`, the elementary irrationality
    arguments of Step 1a(ii) and (iii), and the angle sums of Step 3;
  * the angle count in the proof of Lemma `lem:shape4`, carried as the hypothesis `1 ≤ C` (the base
    of the target contains a `c`-edge). The angle count shows this for every tiling of that target,
    without using that `N` is prime.
* `hBR37`, `hBR41` in `main_theorem`: Theorem `thm:BR`. `main_theorem_19_mod_24` and `no_nineteen`
  do not use them.

The link between the predicates `Q` and actual tilings is part of the unformalized hypothesis `hO`.
Because `main_theorem_19_mod_24` and `no_nineteen` hold for every `Q`, they do not depend on how `Q`
is read. In `main_theorem`, `Q` must be read as the existence of the tiling for `hBR37` and `hBR41`
to be Theorem `thm:BR`.

Not formalized at all: Corollary `cor:primes` (its constructive half, the realizations of `2`, `3`
and the primes `p ≡ 1 (mod 4)`), and the remarks of the paper (the stronger statement `b ∣ t` for
the target of Lemma `lem:shape5`, which the main theorem does not need).

## Notes on deviations from the paper

* `3 ∤ c` (equation `eq:not3`) is proved by a finite check of the residues modulo 9 (`decide` on
  `ZMod 9`) instead of the paper's argument modulo 3 and 9; the statement is the same.
* Lemma `lem:g1residues`(a) is formalized as "a prime `j^2 h` is not `≡ 3 (mod 8)`", which together
  with `N ≡ 3 (mod 4)` gives the paper's `N ≡ 7 (mod 8)`; the residue statement itself
  (`two_sq_sub_sq_mod_eight`) is proved for all integers `k, m`, without coprimality.
* Lemma `lem:shape4` is split into its arithmetic part, which is formalized (`shape4_prime_no_c_edge`:
  a prime count forces a base without `c`-edges), and the angle count, which is the hypothesis
  `1 ≤ C`.
* In Lemma `lem:rowI` the unit factor `χ(θ₀)` of the target value is dropped (it does not change
  membership in `I`), and part (b) allows either sign `±3L z^e`.
* Lemma `app:decomp` (L2) is stated in the paper for `1 ≤ n < k`; `decomp_a`, `decomp_b` and
  `decomp_c_no_b` assume only `n < k` (for `n = 0` the statements also hold), which lets
  `leg_no_b_edge` apply (L2)(C) to `(k - r) c` without a separate case `r = k`.
* Step 1a(i) of the proof (equilateral tile) gives `N = (L/s)^2` directly; it is carried by the
  constructor `reptile_sq`, whose data is the same.
* `exists_three_dvd_a_add_b` documents a pitfall: `3 ∤ a + b` fails for primitive solutions of
  `c^2 = a^2+ab+b^2` (`(7, 8, 13)`), although it holds for the `60°` triples
  `c^2 = a^2-ab+b^2` of progress634 (Lemma `lem:g60-units`). The unit used for `ε` is `d = a - b`,
  and `3 ∤ a - b` is `not_three_dvd_d`, as in the paper.
* The development covers every branch of Section `sec:proof` with its own arithmetic; the only
  imported conclusions are those of Theorem `thm:counts` (in `iso_right`, `iso_gamma2alpha`,
  `equi_iv`) and Theorem `thm:BR` (in `main_theorem`).

## Axioms

`lake env lean No19Tiling/Axioms.lean` prints the axioms of 73 theorems. Output of 2026-10-25: all 73
report `[propext, Classical.choice, Quot.sound]`, except `G1Param.shape4Vec_primitive`,
`G1Param.cast_b` and `G1Param.g_eq`, which report `[propext, Quot.sound]`. Complete output:

```
'No19Tiling.scale_int_of_primitive3' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.scale_nat_of_primitive3' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.sq_add_sq_mod_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.coprime_ab' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.coprime_ac' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.coprime_bc' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.not_three_dvd_c' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.primitive_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.primitive_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.primitive_C' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.primitive_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.countA_not_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.countB_not_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.countC_not_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.countD_not_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.lem_group2' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.lem_group2_both_labelings' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.tile_primitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.triVec_primitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.isoVec_primitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.eq_one_of_prime_sq_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.two_sq_sub_sq_mod_eight' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.three_sq_sub_sq_mod_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.h_count_prime_mod8' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.g_count_prime_mod3' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.triquadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.isoBeta' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.triquadratic_not_19_mod_24' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.isoBeta_not_19_mod_24' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.shape2Vec_primitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.shape2_not_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.shape5_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.shape5_not_3_mod_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.shape4_prime_no_c_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.shape4_not_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.shape4Vec_primitive' depends on axioms: [propext, Quot.sound]
'No19Tiling.G1Param.shape4_not_prime_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.shape5Vec_primitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.shape5_not_3_mod_4_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.cast_b' depends on axioms: [propext, Quot.sound]
'No19Tiling.G1Param.g_eq' depends on axioms: [propext, Quot.sound]
'No19Tiling.G1Param.lattice_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.decomp_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.decomp_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.decomp_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.decomp_c_no_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.decomp_mb2c_lt_k' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.decomp_mbc' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G1Param.leg_no_b_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.norm_b_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.two_le_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.two_le_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.coprime_c_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.rowI_primitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.rowI_not_prime_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.three_ab_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.not_three_dvd_d' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.exists_three_dvd_a_add_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.isCoprime_c' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.isCoprime_d' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.eps_kills_ideal' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.d_mul_eps_rowI' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.eps_rowIBoundary_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.b_dvd_of_rowIBoundary_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.rowI_not_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.rowI_not_prime_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.rowI_swap_not_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.ab_dvd_of_rowE' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.G2Triple.rowE_not_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.main_theorem_19_mod_24' depends on axioms: [propext, Classical.choice, Quot.sound]
'No19Tiling.no_nineteen' depends on axioms: [propext, Classical.choice, Quot.sound]
```
