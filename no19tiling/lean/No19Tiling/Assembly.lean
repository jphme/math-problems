/-
Copyright (c) 2026 Jan Philipp Harries. All rights reserved.

Prop-level skeleton of the proof of Theorem `thm:main` of no19tiling.tex (Section `sec:proof`,
Steps 1a, 1b, 2, 3, 4) and of Theorem `thm:nineteen`.

`Outcome Q N` lists, for a tiling of some triangle by `N` congruent triangles, every branch of
the case analysis together with the arithmetic data that the cited theorem (or our own
geometric lemma) provides for that branch. That every tiling falls into one of these branches
is the content of the imported classification theorems and of the geometric lemmas; it is NOT
formalized here and enters the main theorems as the hypothesis `hO : Outcome Q N`.

The two Beeson–Roşu results (Theorem `thm:BR` of the paper = arXiv:2607.23453v3, Theorem 37:
no `j = 1` tiling of the isosceles-β triangle; Theorem 41: none of the triquadratic triangle) are
about the existence of
tilings, which the arithmetic cannot see. They are therefore stated about two abstract
predicates `Q.IsoBeta P j N` / `Q.Triquad P j N` ("the target with tile parameters `P` and scale
`j` is tiled by `N` tiles"), which the corresponding `Outcome` constructors carry, and enter
`main_theorem` as the named hypotheses `hBR37`, `hBR41`. `main_theorem_19_mod_24` does not use
them (it holds for arbitrary predicates).
-/
import No19Tiling.Group1
import No19Tiling.Group2
import No19Tiling.RowI
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic.NormNum.Prime

namespace No19Tiling

/-- Abstract existence predicates for the two Group-1 targets whose `j = 1` case is excluded
only by Beeson–Roşu. `IsoBeta P j N`: a triangle with angles `(β, β, 3α)` and sides
`j · (k^3, k^3, m(3k^2-m^2))` is tiled by `N` copies of the tile `(mk, k^2-m^2, k^2)`.
`Triquad P j N`: the same for angles `(2α, β, α+β)` and sides `j · (m(2k^2-m^2), k(k^2-m^2), k^3)`. -/
structure TilingPredicates where
  IsoBeta : G1Param → ℚ → ℕ → Prop
  Triquad : G1Param → ℚ → ℕ → Prop

/-- The branches of the case analysis of Section `sec:proof` for a tiling of a triangle `T` by
`N` congruent copies of a tile `R`, each with the arithmetic conclusion of the theorem or lemma
that handles it.
Notation as in the paper: Group-1 tile `(mk, k^2-m^2, k^2)` (`G1Param`), Group-2 tile
`(a, b, c)` with `c^2 = a^2+ab+b^2` (`G2Triple`). Labelings: Group-2 branches quantify over all
`G2Triple`s, so the relabeling `α ↔ β` is the instance `t.swap`. -/
inductive Outcome (Q : TilingPredicates) (N : ℕ) : Prop
  /-- Reptiling, `N = M^2` (Theorem `thm:reptile`, Snover–Waiveris–Williams). Reached from:
  scalene `T` with commensurable angles (Theorem `thm:commensurable`, Step 3), Theorem
  `thm:classification`(1) (Step 4), isosceles line 1 (Step 1b). Also carries Step 1a(i),
  equilateral tile: there `N = (L/s)^2` directly by Lemma `lem:bdry`(c). -/
  | reptile_sq (M : ℕ) (h : N = M ^ 2)
  /-- Reptiling, `N = M^2 + K^2` (same sources). -/
  | reptile_sum_sq (M K : ℕ) (h : N = M ^ 2 + K ^ 2)
  /-- Reptiling, `N = 3M^2` (same sources). -/
  | reptile_three_sq (M : ℕ) (h : N = 3 * M ^ 2)
  /-- Group 1, scalene target `(α, 2α, 2β)` (Theorem `thm:classification`(2), Step 4; Lemma
  `lem:g1counts`(c)): sides `j · (k^4, k^2 h, b g)`, `N = j^2 h g`. -/
  | g1_shape2 (P : G1Param) (j : ℚ) (hj : 0 < j)
      (hs : SidesIntegral j P.shape2Vec.1 P.shape2Vec.2.1 P.shape2Vec.2.2)
      (hN : (N : ℚ) = j ^ 2 * P.h * P.g)
  /-- Group 1, scalene triquadratic target `(2α, β, α+β)` (Theorem `thm:classification`(2),
  Step 4; Lemma `lem:g1counts`(a)): sides `j · triVec`, `N = j^2 (2k^2 - m^2)`, and the tiling
  exists. -/
  | g1_triquad (P : G1Param) (j : ℚ) (hj : 0 < j)
      (hs : SidesIntegral j P.triVec.1 P.triVec.2.1 P.triVec.2.2)
      (hN : (N : ℚ) = j ^ 2 * P.h) (htil : Q.Triquad P j N)
  /-- Isosceles line 6, target `(β, β, 3α)` (Theorem `thm:isoclass`, Step 1b; Lemma
  `lem:g1counts`(b)): sides `j · isoVec`, `N = j^2 (3k^2 - m^2)`, and the tiling exists. -/
  | g1_isoBeta (P : G1Param) (j : ℚ) (hj : 0 < j)
      (hs : SidesIntegral j P.isoVec.1 P.isoVec.2.1 P.isoVec.2.2)
      (hN : (N : ℚ) = j ^ 2 * P.g) (htil : Q.IsoBeta P j N)
  /-- Isosceles line 7, target `(α+β, α+β, α)` (Theorem `thm:isoclass`, Step 1b; Lemma
  `lem:shape4`): sides `t (k, k, m)`, `N b = t^2`, the base `t m` decomposes into `A` a-edges,
  `B` b-edges and `C ≥ 1` c-edges (Lemma `lem:bdry`(c); `C ≥ 1` is the angle count in the proof
  of Lemma `lem:shape4`, geometric). -/
  | g1_shape4 (P : G1Param) (t : ℚ) (ht : 0 < t) (hs : SidesIntegral t P.k P.k P.m)
      (A B C : ℕ) (hN : (N : ℚ) * P.b = t ^ 2)
      (hbase : t * P.m = A * (P.m * P.k) + B * P.b + C * P.k ^ 2) (hC : 1 ≤ C)
  /-- Isosceles line 5, target `(α, α, α+2β)` (Theorem `thm:isoclass`, Step 1b; Lemma
  `lem:shape5`): sides `t (k^2, k^2, h)`, `N b = t^2 h`. -/
  | g1_shape5 (P : G1Param) (t : ℚ) (ht : 0 < t) (hs : SidesIntegral t (P.k ^ 2) (P.k ^ 2) P.h)
      (hN : (N : ℚ) * P.b = t ^ 2 * P.h)
  /-- Group 2, scalene targets A–D (Theorem `thm:classification`(3), Step 4; Theorem
  `thm:rational`(a) for commensurable sides; Lemma `lem:group2`): rational scale `m`, integral
  sides, count formula of the case. -/
  | g2_scalene (t : G2Triple) (X : G2Triple.Case) (m : ℚ) (hm : 0 < m)
      (hs : SidesIntegral m (t.sideVec X).1 (t.sideVec X).2.1 (t.sideVec X).2.2)
      (hN : t.countEq m N X)
  /-- Isosceles line 2, right tile (Step 1b; Theorem `thm:counts`(a), Beeson, Iso-v8 Cor. 7.9:
  "Suppose isosceles triangle ABC is N-tiled by a right triangle and N > 2. Then N is not a
  prime."). Imported conclusion. -/
  | iso_right (h : 2 < N → ¬ N.Prime)
  /-- Isosceles line 3, `γ = 2α` (Step 1b; Theorem `thm:counts`(b), Beeson, Iso-v8 Thm 11.7:
  "N is not squarefree"). Imported conclusion. -/
  | iso_gamma2alpha (h : ¬ Squarefree N)
  /-- Isosceles line 4, `γ = 2π/3`, target `(α, α, π-2α)` (Step 1b; Lemma `lem:rowI`(a)):
  sides `k (c, c, a+2b)`, `N b = k^2 (a+2b)`, and the boundary premise (Lemma
  `lem:character`). The base-angle-β version is the instance `t.swap`. -/
  | iso_rowI (t : G2Triple) (k : ℚ) (hk : 0 < k)
      (hs : SidesIntegral k t.c t.c (t.a + 2 * t.b))
      (hN : (N : ℚ) * t.b = k ^ 2 * (t.a + 2 * t.b))
      (hprem : ∀ n : ℕ, (n : ℚ) = k → t.RowIPremise n)
  /-- Equilateral `T`, tile `(π/6, π/6, 2π/3)` (Step 1a(ii); elementary: `L = s(u + v√3)` by
  Lemma `lem:bdry`(a), and the area equation `N = u^2 + 3v^2 + 2uv√3` forces `uv = 0`):
  `N = u^2` or `N = 3 v^2`. -/
  | equi_ii (u v : ℕ) (h : N = u ^ 2 ∨ N = 3 * v ^ 2)
  /-- Equilateral `T`, tile `(π/6, π/3, π/2)` (Step 1a(iii); elementary: `L = s(u + v√3)`,
  `N = L^2/(2s^2)` forces `uv = 0` and `N = u^2/2` or `3v^2/2`, so `u` or `v` is even):
  `N = 2 n^2` or `N = 6 n^2`. -/
  | equi_iii (n : ℕ) (h : N = 2 * n ^ 2 ∨ N = 6 * n ^ 2)
  /-- Equilateral `T`, tile `(α, β, π/3)`, `α/π ∉ ℚ` (Step 1a(iv); Theorem `thm:counts`(c),
  Beeson, arXiv:1812.07014v3 Thm 3: "N is not prime"). Imported conclusion. -/
  | equi_iv (h : ¬ N.Prime)
  /-- Equilateral `T` of side `L`, tile `(α, β, 2π/3)` (Step 1a(v); Theorem `thm:rational`(a)
  for commensurable sides; Lemma `lem:rowI`(b)): `N ab = L^2` and the boundary premise. -/
  | equi_v (t : G2Triple) (L : ℕ) (hN : N * (t.a * t.b) = L ^ 2) (hprem : t.RowEPremise L)

/-- A prime is not a square. -/
theorem not_prime_sq (M : ℕ) : ¬ (M ^ 2).Prime := by
  intro hp
  rcases Nat.lt_or_ge M 2 with h | h
  · obtain rfl | rfl : M = 0 ∨ M = 1 := by omega
    · exact Nat.not_prime_zero (by simpa using hp)
    · exact Nat.not_prime_one (by simpa using hp)
  · rw [sq] at hp; exact Nat.not_prime_mul (by omega) (by omega) hp

/-- `c * M^2` with `c ≥ 2` prime forces `M = 1`. -/
theorem sq_eq_one_of_prime_mul_sq {c M N : ℕ} (hN : N = c * M ^ 2) (hp : N.Prime) : M ^ 2 = 1 := by
  rw [hN] at hp
  rcases Nat.prime_mul_iff.mp hp with h | h
  · exact h.2
  · exact absurd h.1 (not_prime_sq M)

/-- **Reduction theorem** (the case analysis of Section `sec:proof`, with Corollary `cor:g1prime`;
cf. Beeson–Roşu Cor. 8). If `N > 3` is a prime with `N ≡ 3 (mod 4)` and admits an outcome, then the
outcome is a `j = 1` triquadratic tiling with `N ≡ 7 (mod 8)` or a `j = 1` isosceles-β tiling
with `N ≡ 11 (mod 12)`. -/
theorem reduction (Q : TilingPredicates) {N : ℕ} (hp : N.Prime) (h4 : N % 4 = 3) (h3 : 3 < N)
    (hO : Outcome Q N) :
    (∃ P : G1Param, Q.Triquad P 1 N ∧ N = P.h ∧ N % 8 = 7) ∨
    (∃ P : G1Param, Q.IsoBeta P 1 N ∧ N = P.g ∧ N % 12 = 11) := by
  cases hO with
  | reptile_sq M h => exact absurd (h ▸ hp) (not_prime_sq M)
  | reptile_sum_sq M K h => exact absurd (h ▸ h4) (sq_add_sq_mod_four M K)
  | reptile_three_sq M h =>
    have := sq_eq_one_of_prime_mul_sq h hp; omega
  | g1_shape2 P j hj hs hN => exact absurd hp (P.shape2_not_prime hj hs hN)
  | g1_triquad P j hj hs hN htil =>
    obtain ⟨rfl, hNh, h8⟩ := P.triquadratic hj hs hN hp
    exact Or.inl ⟨P, htil, hNh, by omega⟩
  | g1_isoBeta P j hj hs hN htil =>
    obtain ⟨rfl, hNg, h3'⟩ := P.isoBeta hj hs hN hp
    have h3'' : N % 3 ≠ 0 := by
      intro h0
      have := (Nat.Prime.eq_one_or_self_of_dvd hp 3 (Nat.dvd_of_mod_eq_zero h0)); omega
    exact Or.inr ⟨P, htil, hNg, by omega⟩
  | g1_shape4 P t ht hs A B C hN hbase hC => exact absurd hp (P.shape4_not_prime_rat ht hs hN hbase hC)
  | g1_shape5 P t ht hs hN => exact absurd h4 (P.shape5_not_3_mod_4_rat ht hs hN hp)
  | g2_scalene t X m hm hs hN => exact absurd hp (t.lem_group2 X hm hs hN)
  | iso_right h => exact absurd hp (h (by omega))
  | iso_gamma2alpha h => exact absurd hp.prime.squarefree h
  | iso_rowI t k hk hs hN hprem => exact absurd hp (t.rowI_not_prime_rat hk hs hN hprem)
  | equi_ii u v h =>
    rcases h with h | h
    · exact absurd (h ▸ hp) (not_prime_sq u)
    · have := sq_eq_one_of_prime_mul_sq h hp; omega
  | equi_iii n h =>
    rcases h with h | h
    · have := sq_eq_one_of_prime_mul_sq h hp; omega
    · have h' : N = 2 * (3 * n ^ 2) := by rw [h]; ring
      rw [h'] at hp
      rcases Nat.prime_mul_iff.mp hp with ⟨-, h''⟩ | ⟨-, h''⟩ <;> omega
  | equi_iv h => exact absurd hp h
  | equi_v t L hN hprem => exact absurd hp (t.rowE_not_prime hN hprem)

/-- **Theorem `thm:main`, arithmetic skeleton.** Let `N > 3` be a prime with `N ≡ 3 (mod 4)`.
Assuming Theorem `thm:BR` (Beeson–Roşu Theorem 37, `hBR37`: no `j = 1` isosceles-β tiling;
Theorem 41, `hBR41`: no `j = 1` triquadratic tiling), no outcome of the case analysis has `N`
tiles. -/
theorem main_theorem (Q : TilingPredicates)
    (hBR37 : ∀ (P : G1Param) (N : ℕ), ¬ Q.IsoBeta P 1 N)
    (hBR41 : ∀ (P : G1Param) (N : ℕ), ¬ Q.Triquad P 1 N)
    {N : ℕ} (hp : N.Prime) (h4 : N % 4 = 3) (h3 : 3 < N) (hO : Outcome Q N) : False := by
  rcases reduction Q hp h4 h3 hO with ⟨P, h, -⟩ | ⟨P, h, -⟩
  · exact hBR41 P N h
  · exact hBR37 P N h

/-- **Theorem `thm:nineteen`, arithmetic skeleton: primes `p ≡ 19 (mod 24)`.** No outcome of the case
analysis has a prime number `N ≡ 19 (mod 24)` of tiles. No Beeson–Roşu hypothesis is used: the
predicates `Q` are arbitrary. -/
theorem main_theorem_19_mod_24 (Q : TilingPredicates) {N : ℕ} (hp : N.Prime) (h24 : N % 24 = 19)
    (hO : Outcome Q N) : False := by
  rcases reduction Q hp (by omega) (by omega) hO with ⟨P, -, -, h⟩ | ⟨P, -, -, h⟩ <;> omega

/-- The titular case: no outcome of the case analysis has `19` tiles. -/
theorem no_nineteen (Q : TilingPredicates) (hO : Outcome Q 19) : False :=
  main_theorem_19_mod_24 Q (by norm_num) (by norm_num) hO

end No19Tiling
