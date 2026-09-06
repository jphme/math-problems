import PeaceableQueens.UpperBound.ProfileAlgebra
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-! Quantitative and asymptotic consequences for the explicit parity formula.
The analytic argument is independent of the certificate-backed queen theorem. -/

namespace PeaceableQueens.UpperBound

open Filter Asymptotics
open scoped Topology

/-- The two quantitative inequalities in paper `cor:asym`. -/
theorem H_bounds (q : ℕ) (hq : 0 < q) :
    kappa * (q : ℝ) ^ 2 - gamma * q - 1 / 4 ≤ (H q : ℝ) ∧
      H q ≤ ⌊kappa * (q : ℝ) ^ 2⌋₊ := by
  exact ⟨H_lower_s19 q hq, H_le_floor_s18 q hq⟩

/-- A convenient explicit linear error bound for positive half-orders. -/
theorem H_error_bound (q : ℕ) (hq : 0 < q) :
    ‖(H q : ℝ) - kappa * (q : ℝ) ^ 2‖ ≤ (q : ℝ) := by
  have hb := H_bounds q hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hk0 : 0 ≤ kappa * (q : ℝ) ^ 2 := mul_nonneg (le_of_lt (lt_trans (by norm_num) kappa_gt_half)) (sq_nonneg _)
  have hu : (H q : ℝ) ≤ kappa * (q : ℝ) ^ 2 :=
    (show (H q : ℝ) ≤ (⌊kappa * (q : ℝ) ^ 2⌋₊ : ℝ) by exact_mod_cast hb.2).trans (Nat.floor_le hk0)
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hu)]
  have hg := mul_le_mul_of_nonneg_right (le_of_lt gamma_lt_half) (show (0 : ℝ) ≤ q by positivity)
  linarith [hb.1]

/-- Paper `cor:asym`: the error in the quadratic formula is `O(n)` on even orders. -/
theorem H_asymptotic :
    (fun q : ℕ => (H q : ℝ) - (2 - Real.sqrt 3) / 2 * (2 * (q : ℝ)) ^ 2)
      =O[atTop] (fun q : ℕ => 2 * (q : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with q hq
  have he := H_error_bound q (by omega)
  have hid : (2 - Real.sqrt 3) / 2 * (2 * (q : ℝ)) ^ 2 = kappa * (q : ℝ) ^ 2 := by
    unfold kappa
    ring
  rw [hid, one_mul]
  calc
    _ ≤ (q : ℝ) := he
    _ ≤ ‖2 * (q : ℝ)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * q)]
      nlinarith [Nat.cast_nonneg (α := ℝ) q]

/-- Paper `cor:asym`: the limiting queen density along the even subsequence. -/
theorem H_density_limit :
    Tendsto (fun q : ℕ => (H q : ℝ) / (2 * (q : ℝ)) ^ 2)
      atTop (𝓝 ((2 - Real.sqrt 3) / 2)) := by
  have herror : Tendsto (fun q : ℕ => kappa - (H q : ℝ) / (q : ℝ) ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    · filter_upwards [eventually_ge_atTop 1] with q hq
      have hb := (H_bounds q (by omega)).2
      have hk0 : 0 ≤ kappa * (q : ℝ) ^ 2 := mul_nonneg (le_of_lt (lt_trans (by norm_num) kappa_gt_half)) (sq_nonneg _)
      have hu : (H q : ℝ) ≤ kappa * (q : ℝ) ^ 2 :=
        (show (H q : ℝ) ≤ (⌊kappa * (q : ℝ) ^ 2⌋₊ : ℝ) by exact_mod_cast hb).trans (Nat.floor_le hk0)
      have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by
        exact sq_pos_of_pos (by exact_mod_cast (show 0 < q by omega))
      exact sub_nonneg.mpr ((div_le_iff₀ hq2).mpr hu)
    · filter_upwards [eventually_ge_atTop 1] with q hq
      have he := H_error_bound q (by omega)
      have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have he' : kappa * (q : ℝ) ^ 2 - (H q : ℝ) ≤ (q : ℝ) := by
        have := neg_le_abs ((H q : ℝ) - kappa * (q : ℝ) ^ 2)
        rw [Real.norm_eq_abs] at he
        linarith
      have hd := (div_le_div_iff_of_pos_right (sq_pos_of_pos hqR)).mpr he'
      calc
        kappa - (H q : ℝ) / (q : ℝ) ^ 2 =
            (kappa * (q : ℝ) ^ 2 - H q) / (q : ℝ) ^ 2 := by
          field_simp [ne_of_gt hqR]
        _ ≤ (q : ℝ) / (q : ℝ) ^ 2 := hd
        _ = 1 / (q : ℝ) := by field_simp [ne_of_gt hqR]
  have hratio : Tendsto (fun q : ℕ => (H q : ℝ) / (q : ℝ) ^ 2) atTop (𝓝 kappa) := by
    convert (tendsto_const_nhds (x := kappa)).sub herror using 1 <;> simp
  have hd := hratio.div_const (4 : ℝ)
  have hc : kappa / 4 = (2 - Real.sqrt 3) / 2 := by
    unfold kappa
    ring
  rw [hc] at hd
  convert hd using 1
  ext q
  simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring

#print axioms H_asymptotic
#print axioms H_density_limit

end PeaceableQueens.UpperBound
