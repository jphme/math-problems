/-
Copyright (c) 2026 Jan Philipp Harries. All rights reserved.

The relation lattice of the Group-1 tile and the edge decompositions used in the proof of the
Group-1 scale-one cases (Appendix A of no19tiling.tex: Lemmas `app:lattice` and `app:decomp`).

The tile is `(a, b, c) = (mk, k^2 - m^2, k^2)` with coprime `0 < m < k` (`G1Param`). An *edge
decomposition* of a length `L` is a triple `(p, q, r)` of natural numbers with
`p a + q b + r c = L`: a segment of length `L` partitioned into `p` a-edges, `q` b-edges and
`r` c-edges.

* `lattice_iff` (Lemma `app:lattice`, fact (L1)): the integer relations `x a + y b + z c = 0`
  are exactly `ξ (k, 0, -m) + η (m, k, -k)`.
* `decomp_a`, `decomp_b`, `decomp_c_no_b` (Lemma `app:decomp`, fact (L2)): for `n < k` the only
  decomposition of `n a` is `(n, 0, 0)`, the only one of `n b` is `(0, n, 0)`, and no
  decomposition of `n c` contains a b-edge.
* `decomp_mb2c_lt_k`, `decomp_mbc` (Lemma `app:decomp`, fact (L3)): a decomposition of
  `m (b + 2c)` with an a-edge has fewer than `k` c-edges; the decompositions of `m (b + c)` are
  `(0, m, m)` and `(k, m, 0)`.
* `leg_no_b_edge`: a decomposition of `k c` with a c-edge has no b-edge (fact (L2)(C) applied to
  `(k - r) c`).

The lengths `k c`, `m (b + 2c)` and `m (b + c)` are the legs and base of the target
`(β, β, 3α)` and the side opposite `2α` of the target `(2α, β, α+β)`, at scale `j = 1`; with
`g = 3k^2 - m^2` and `h = 2k^2 - m^2` they are the entries `k^3`, `m g` of `isoVec` and `m h` of
`triVec` in `Group1.lean` (`g_eq`, `h_eq`). Those side vectors are data there and stay data here.
-/
import No19Tiling.Group1

namespace No19Tiling

namespace G1Param

variable (P : G1Param)

/-- `b = k^2 - m^2` is the true difference in `ℤ`. -/
theorem cast_b : (P.b : ℤ) = (P.k : ℤ) ^ 2 - (P.m : ℤ) ^ 2 := by
  have := P.msq_lt_ksq
  unfold b; rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- `g = 3k^2 - m^2 = b + 2c`. -/
theorem g_eq : P.g = P.b + 2 * P.k ^ 2 := by
  have := P.msq_lt_ksq; unfold g b; omega

/-- **Relation lattice** (Lemma `app:lattice`, fact (L1)). An integer triple `(x, y, z)`
satisfies `x a + y b + z c = 0` for the tile `(a, b, c) = (mk, k^2 - m^2, k^2)` if and only if
it is `ξ (k, 0, -m) + η (m, k, -k)` for integers `ξ, η`. -/
theorem lattice_iff (x y z : ℤ) :
    x * (P.m * P.k) + y * ((P.k : ℤ) ^ 2 - (P.m : ℤ) ^ 2) + z * (P.k : ℤ) ^ 2 = 0 ↔
      ∃ ξ η : ℤ, x = ξ * P.k + η * P.m ∧ y = η * P.k ∧ z = -ξ * P.m - η * P.k := by
  constructor
  · intro h
    have hk : (0 : ℤ) < P.k := by have := P.two_le_k; omega
    have hcop : IsCoprime (P.k : ℤ) (P.m : ℤ) := Nat.isCoprime_iff_coprime.mpr P.cop.symm
    -- reducing mod `k`: `k ∣ y m^2`, so `k ∣ y`
    have h1 : (P.k : ℤ) ∣ y * (P.m : ℤ) ^ 2 :=
      ⟨x * P.m + y * P.k + z * P.k, by linear_combination (-1 : ℤ) * h⟩
    obtain ⟨η, rfl⟩ := hcop.pow_right.dvd_of_dvd_mul_right h1
    -- subtracting `η (m, k, -k)`: `(x - η m) m = -(z + η k) k`
    have h2 : (x - η * P.m) * P.m = -(z + η * P.k) * P.k := by
      have h3 : ((x - η * P.m) * P.m + (z + η * P.k) * P.k) * P.k = 0 := by
        linear_combination h
      linear_combination (mul_eq_zero.mp h3).resolve_right hk.ne'
    obtain ⟨ξ, hξ⟩ : (P.k : ℤ) ∣ x - η * P.m :=
      hcop.dvd_of_dvd_mul_right ⟨-(z + η * P.k), by linear_combination h2⟩
    have h4 : (ξ * P.m + (z + η * P.k)) * P.k = 0 := by
      rw [hξ] at h2; linear_combination h2
    have h5 := (mul_eq_zero.mp h4).resolve_right hk.ne'
    exact ⟨ξ, η, by linear_combination hξ, by ring, by linear_combination h5⟩
  · rintro ⟨ξ, η, rfl, rfl, rfl⟩
    ring

/-- Two decompositions of the same length differ by an element of the relation lattice. -/
theorem decomp_shift {p q r p₀ q₀ r₀ : ℤ}
    (h : p * (P.m * P.k) + q * ((P.k : ℤ) ^ 2 - (P.m : ℤ) ^ 2) + r * (P.k : ℤ) ^ 2 =
      p₀ * (P.m * P.k) + q₀ * ((P.k : ℤ) ^ 2 - (P.m : ℤ) ^ 2) + r₀ * (P.k : ℤ) ^ 2) :
    ∃ ξ η : ℤ, p = p₀ + ξ * P.k + η * P.m ∧ q = q₀ + η * P.k ∧
      r = r₀ - ξ * P.m - η * P.k := by
  obtain ⟨ξ, η, h1, h2, h3⟩ :=
    (P.lattice_iff (p - p₀) (q - q₀) (r - r₀)).mp (by linear_combination h)
  exact ⟨ξ, η, by linear_combination h1, by linear_combination h2, by linear_combination h3⟩

/-- A natural-number decomposition, read in `ℤ`. -/
private theorem cast_decomp {p q r L : ℕ}
    (h : p * (P.m * P.k) + q * P.b + r * P.k ^ 2 = L) :
    (p : ℤ) * (P.m * P.k) + q * ((P.k : ℤ) ^ 2 - (P.m : ℤ) ^ 2) + r * (P.k : ℤ) ^ 2 = L := by
  rw [← P.cast_b]; exact_mod_cast h

/-- **(L2)(A)** (Lemma `app:decomp`). For `n < k`, the only decomposition of `n a` is
`(n, 0, 0)`. (The source states `1 ≤ n < k`; `n = 0` holds as well.) -/
theorem decomp_a {n p q r : ℕ} (hn : n < P.k)
    (h : p * (P.m * P.k) + q * P.b + r * P.k ^ 2 = n * (P.m * P.k)) :
    p = n ∧ q = 0 ∧ r = 0 := by
  have hz := P.cast_decomp h
  push_cast at hz
  obtain ⟨ξ, η, hp, hq, hr⟩ := P.decomp_shift (p := p) (q := q) (r := r)
    (p₀ := n) (q₀ := 0) (r₀ := 0)
    (by linear_combination hz)
  have hK : (0 : ℤ) < P.k := by have := P.two_le_k; omega
  have hM : (0 : ℤ) < P.m := by have := P.hm; omega
  have hMK : (P.m : ℤ) < P.k := by have := P.hmk; omega
  have hnK : (n : ℤ) < P.k := by omega
  have hp0 : (0 : ℤ) ≤ p := by positivity
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hη : 0 ≤ η := by
    by_contra! hc; nlinarith
  rcases hη.eq_or_lt with h0 | h1
  · subst h0
    have hξ1 : ξ ≤ 0 := by by_contra! hc; nlinarith
    have hξ2 : 0 ≤ ξ := by
      by_contra! hc
      have : ξ * P.k ≤ -1 * P.k := mul_le_mul_of_nonneg_right (by omega) hK.le
      linarith
    obtain rfl : ξ = 0 := le_antisymm hξ1 hξ2
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · exfalso
    -- `ξ ≤ -η - 1`, from `r ≥ 0`
    have hξ : ξ + η + 1 ≤ 0 := by
      by_contra! hc
      have : (-η) * (P.m : ℤ) ≤ ξ * P.m := mul_le_mul_of_nonneg_right (by omega) hM.le
      nlinarith [mul_pos h1 (sub_pos.mpr hMK)]
    have : (ξ + η + 1) * (P.k : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hξ hK.le
    nlinarith [mul_pos h1 (sub_pos.mpr hMK)]

/-- **(L2)(B)** (Lemma `app:decomp`). For `n < k`, the only decomposition of `n b` is
`(0, n, 0)`. (The source states `1 ≤ n < k`; `n = 0` holds as well.) -/
theorem decomp_b {n p q r : ℕ} (hn : n < P.k)
    (h : p * (P.m * P.k) + q * P.b + r * P.k ^ 2 = n * P.b) :
    p = 0 ∧ q = n ∧ r = 0 := by
  have hz := P.cast_decomp h
  push_cast at hz
  rw [P.cast_b] at hz
  obtain ⟨ξ, η, hp, hq, hr⟩ := P.decomp_shift (p := p) (q := q) (r := r)
    (p₀ := 0) (q₀ := n) (r₀ := 0)
    (by linear_combination hz)
  have hK : (0 : ℤ) < P.k := by have := P.two_le_k; omega
  have hM : (0 : ℤ) < P.m := by have := P.hm; omega
  have hMK : (P.m : ℤ) < P.k := by have := P.hmk; omega
  have hnK : (n : ℤ) < P.k := by omega
  have hp0 : (0 : ℤ) ≤ p := by positivity
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hη : 0 ≤ η := by
    by_contra! hc
    have : η * (P.k : ℤ) ≤ -1 * P.k := mul_le_mul_of_nonneg_right (by omega) hK.le
    linarith
  rcases hη.eq_or_lt with h0 | h1
  · subst h0
    have hξ1 : ξ ≤ 0 := by by_contra! hc; nlinarith
    have hξ2 : 0 ≤ ξ := by by_contra! hc; nlinarith
    obtain rfl : ξ = 0 := le_antisymm hξ1 hξ2
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · exfalso
    -- `p m = ξ m k + η m^2 ≤ -η k^2 + η m^2 < 0`
    have hξ : ξ * (P.m : ℤ) ≤ -η * P.k := by linarith
    have e1 : ξ * (P.m : ℤ) * P.k ≤ -η * P.k * P.k := mul_le_mul_of_nonneg_right hξ hK.le
    have e2 : (0 : ℤ) < η * ((P.k : ℤ) ^ 2 - (P.m : ℤ) ^ 2) :=
      mul_pos h1 (by nlinarith)
    have e3 : (0 : ℤ) ≤ (p : ℤ) * P.m := mul_nonneg hp0 hM.le
    rw [hp] at e3
    nlinarith

/-- **(L2)(C)** (Lemma `app:decomp`). For `n < k`, no decomposition of `n c` contains a
b-edge. -/
theorem decomp_c_no_b {n p q r : ℕ} (hn : n < P.k)
    (h : p * (P.m * P.k) + q * P.b + r * P.k ^ 2 = n * P.k ^ 2) : q = 0 := by
  have hz := P.cast_decomp h
  push_cast at hz
  obtain ⟨ξ, η, hp, hq, hr⟩ := P.decomp_shift (p := p) (q := q) (r := r)
    (p₀ := 0) (q₀ := 0) (r₀ := n)
    (by linear_combination hz)
  have hK : (0 : ℤ) < P.k := by have := P.two_le_k; omega
  have hM : (0 : ℤ) < P.m := by have := P.hm; omega
  have hMK : (P.m : ℤ) < P.k := by have := P.hmk; omega
  have hnK : (n : ℤ) < P.k := by omega
  have hp0 : (0 : ℤ) ≤ p := by positivity
  have hr0 : (0 : ℤ) ≤ r := by positivity
  by_contra hq1
  have hq1' : (1 : ℤ) ≤ q := by omega
  have h1 : 0 < η := by by_contra! hc; nlinarith
  -- `p ≥ 0` gives `ξ + η ≥ 1`
  have hξ : 1 ≤ ξ + η := by
    by_contra! hc
    have : (ξ + η) * (P.k : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) hK.le
    nlinarith [mul_pos h1 (sub_pos.mpr hMK)]
  -- then `r ≤ n - m - η (k - m) ≤ n - k < 0`
  have e1 : (0 : ℤ) ≤ (ξ + η - 1) * P.m := mul_nonneg (by omega) hM.le
  have e2 : (0 : ℤ) ≤ (η - 1) * (P.k - P.m) := mul_nonneg (by omega) (by omega)
  nlinarith

/-- **(L3)(i)** (Lemma `app:decomp`). Every decomposition of `m (b + 2c)` that contains an
a-edge has fewer than `k` c-edges. (`m (b + 2c) = m g` is the base of the target
`(β, β, 3α)` at scale `1`, `g_eq`.) -/
theorem decomp_mb2c_lt_k {p q r : ℕ} (hp : 1 ≤ p)
    (h : p * (P.m * P.k) + q * P.b + r * P.k ^ 2 = P.m * (P.b + 2 * P.k ^ 2)) :
    r < P.k := by
  have hz := P.cast_decomp h
  push_cast at hz
  rw [P.cast_b] at hz
  obtain ⟨ξ, η, hp', hq, hr⟩ := P.decomp_shift (p := p) (q := q) (r := r)
    (p₀ := 0) (q₀ := P.m) (r₀ := 2 * P.m)
    (by linear_combination hz)
  have hK : (0 : ℤ) < P.k := by have := P.two_le_k; omega
  have hM : (0 : ℤ) < P.m := by have := P.hm; omega
  have hMK : (P.m : ℤ) < P.k := by have := P.hmk; omega
  have hp1 : (1 : ℤ) ≤ p := by omega
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have hη : 0 ≤ η := by
    by_contra! hc
    have : η * (P.k : ℤ) ≤ -1 * P.k := mul_le_mul_of_nonneg_right (by omega) hK.le
    linarith
  -- `p ≥ 1` gives `ξ + η ≥ 1`
  have hξ : 1 ≤ ξ + η := by
    by_contra! hc
    have : (ξ + η) * (P.k : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) hK.le
    nlinarith [mul_nonneg hη (sub_pos.mpr hMK).le]
  -- then `r ≤ m - η (k - m) ≤ m < k`
  have e1 : (0 : ℤ) ≤ (ξ + η - 1) * P.m := mul_nonneg (by omega) hM.le
  have e2 : (0 : ℤ) ≤ η * (P.k - P.m) := mul_nonneg hη (by omega)
  have : (r : ℤ) < P.k := by nlinarith
  omega

/-- **(L3)(ii)** (Lemma `app:decomp`). The decompositions of `m (b + c)` are `(0, m, m)` and
`(k, m, 0)`. (`m (b + c) = m h` is the side opposite `2α` of the target `(2α, β, α+β)` at
scale `1`, `h_eq`.) -/
theorem decomp_mbc {p q r : ℕ}
    (h : p * (P.m * P.k) + q * P.b + r * P.k ^ 2 = P.m * (P.b + P.k ^ 2)) :
    (p = 0 ∧ q = P.m ∧ r = P.m) ∨ (p = P.k ∧ q = P.m ∧ r = 0) := by
  have hz := P.cast_decomp h
  push_cast at hz
  rw [P.cast_b] at hz
  obtain ⟨ξ, η, hp, hq, hr⟩ := P.decomp_shift (p := p) (q := q) (r := r)
    (p₀ := 0) (q₀ := P.m) (r₀ := P.m)
    (by linear_combination hz)
  have hK : (0 : ℤ) < P.k := by have := P.two_le_k; omega
  have hM : (0 : ℤ) < P.m := by have := P.hm; omega
  have hMK : (P.m : ℤ) < P.k := by have := P.hmk; omega
  have hp0 : (0 : ℤ) ≤ p := by positivity
  have hq0 : (0 : ℤ) ≤ q := by positivity
  have hr0 : (0 : ℤ) ≤ r := by positivity
  have hη : 0 ≤ η := by
    by_contra! hc
    have : η * (P.k : ℤ) ≤ -1 * P.k := mul_le_mul_of_nonneg_right (by omega) hK.le
    linarith
  rcases hη.eq_or_lt with h0 | h1
  · subst h0
    have hξ1 : 0 ≤ ξ := by by_contra! hc; nlinarith
    have hξ2 : ξ ≤ 1 := by by_contra! hc; nlinarith
    obtain rfl | rfl : ξ = 0 ∨ ξ = 1 := by omega
    · left; refine ⟨?_, ?_, ?_⟩ <;> omega
    · right; refine ⟨?_, ?_, ?_⟩ <;> omega
  · exfalso
    -- `p ≥ 0` gives `ξ + η ≥ 1`, then `r ≤ -η (k - m) < 0`
    have hξ : 1 ≤ ξ + η := by
      by_contra! hc
      have : (ξ + η) * (P.k : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) hK.le
      nlinarith [mul_pos h1 (sub_pos.mpr hMK)]
    have e1 : (0 : ℤ) ≤ (ξ + η - 1) * P.m := mul_nonneg (by omega) hM.le
    nlinarith [mul_pos h1 (sub_pos.mpr hMK)]

/-- **Legs** (proof of the scale-one case of the target `(β, β, 3α)`, step 1). A decomposition
of `k c` (a leg of that target at scale `1`, the entry `k^3` of `isoVec`) with at least one
c-edge has no b-edge: `(p, q, 0)` is a decomposition of `(k - r) c` with `k - r < k`, and
(L2)(C) applies. -/
theorem leg_no_b_edge {p q r : ℕ} (hr : 1 ≤ r)
    (h : p * (P.m * P.k) + q * P.b + r * P.k ^ 2 = P.k * P.k ^ 2) : q = 0 := by
  have hk2 : 0 < P.k ^ 2 := by have := P.two_le_k; positivity
  have hrk : r ≤ P.k := by
    apply Nat.le_of_mul_le_mul_right _ hk2
    calc r * P.k ^ 2 ≤ p * (P.m * P.k) + q * P.b + r * P.k ^ 2 := Nat.le_add_left _ _
      _ = P.k * P.k ^ 2 := h
  apply P.decomp_c_no_b (n := P.k - r) (p := p) (r := 0) (by omega)
  rw [Nat.sub_mul]
  omega

end G1Param

end No19Tiling
