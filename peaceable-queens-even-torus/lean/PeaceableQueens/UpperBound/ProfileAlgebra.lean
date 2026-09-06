import PeaceableQueens.Defs
import Mathlib.Analysis.Real.Sqrt

/-!
# Profile algebra for the even-torus upper bound

This module starts the certificate-independent analytic part of the upper
bound.  It records the exact profile identities S16 over `ℝ` and the natural-
to-rational coercion needed to connect the existing definition of `H` to the
later exact certificate calculations.
-/

namespace PeaceableQueens.UpperBound

/-- The two normalized profile identities in S16 (`eq:XYid` in the paper). -/
theorem profile_identities
    (q r0 r1 c0 c1 : ℝ) (hq : q ≠ 0) :
    let X := r0 * c1 + r1 * c0
    let Y := (q - r0) * (q - c0) + (q - r1) * (q - c1)
    let rho := (r0 + r1) / q
    let chi := (c0 + c1) / q
    let z := ((r0 - r1) * (c0 - c1)) / q ^ 2
    (X - Y) / q ^ 2 = rho + chi - 2 - z ∧
      (X + Y) / q ^ 2 = 2 - rho - chi + rho * chi := by
  dsimp
  constructor <;> field_simp [hq] <;> ring

/-- The cross term in S16 is bounded by the product of the two profile sums. -/
theorem profile_cross_term_abs_le
    (q r0 r1 c0 c1 : ℝ) (hq : 0 < q)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) :
    |((r0 - r1) * (c0 - c1)) / q ^ 2| ≤
      ((r0 + r1) / q) * ((c0 + c1) / q) := by
  have hr : |r0 - r1| ≤ r0 + r1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hc : |c0 - c1| ≤ c0 + c1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hmul : |r0 - r1| * |c0 - c1| ≤ (r0 + r1) * (c0 + c1) :=
    mul_le_mul hr hc (abs_nonneg _) (by positivity)
  calc
    |((r0 - r1) * (c0 - c1)) / q ^ 2| =
        |r0 - r1| * |c0 - c1| / q ^ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg q)]
    _ ≤ (r0 + r1) * (c0 + c1) / q ^ 2 :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hq)).mpr hmul
    _ = ((r0 + r1) / q) * ((c0 + c1) / q) := by
      field_simp [ne_of_gt hq]

/-- Casting an admissible natural-valued white profile to `ℚ` agrees with
ordinary rational subtraction. -/
theorem cast_profileWhite
    (q r0 r1 c0 c1 : ℕ)
    (hr0 : r0 ≤ q) (hr1 : r1 ≤ q) (hc0 : c0 ≤ q) (hc1 : c1 ≤ q) :
    (profileWhite q r0 r1 c0 c1 : ℚ) =
      ((q : ℚ) - r0) * ((q : ℚ) - c0) +
        ((q : ℚ) - r1) * ((q : ℚ) - c1) := by
  unfold profileWhite
  push_cast [Nat.cast_sub hr0, Nat.cast_sub hr1, Nat.cast_sub hc0, Nat.cast_sub hc1]
  ring

/-- Casting a natural-valued black profile to `ℚ` preserves its polynomial
form. -/
theorem cast_profileBlack (r0 r1 c0 c1 : ℕ) :
    (profileBlack r0 r1 c0 c1 : ℚ) =
      (r0 : ℚ) * c1 + (r1 : ℚ) * c0 := by
  simp [profileBlack]

/-! ## Continuous constants and the `X ≥ Y` chamber -/

noncomputable section

def kappa : ℝ := 4 - 2 * Real.sqrt 3
def gamma : ℝ := 1 - 1 / Real.sqrt 3

lemma sqrt_three_pos : 0 < Real.sqrt 3 := by positivity

lemma sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num

lemma sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  nlinarith [sqrt_three_sq]

lemma sqrt_three_lt_seven_fourths : Real.sqrt 3 < (7 : ℝ) / 4 := by
  nlinarith [sqrt_three_sq]

lemma sqrt_three_lt_693_400 : Real.sqrt 3 < (693 : ℝ) / 400 := by
  nlinarith [sqrt_three_sq]

lemma kappa_gt_half : (1 : ℝ) / 2 < kappa := by
  unfold kappa
  linarith [sqrt_three_lt_seven_fourths]

/-- Paper `lem:escape`, first comparison: `κ - 527/1000 > 1/125`. -/
lemma kappa_escape_margin : (1 : ℝ) / 125 < kappa - 527 / 1000 := by
  unfold kappa
  linarith [sqrt_three_lt_693_400]

/-- Paper `lem:escape`, second comparison: `γ < 1/2`. -/
lemma gamma_lt_half : gamma < (1 : ℝ) / 2 := by
  unfold gamma
  have hrecip : (1 : ℝ) / 2 < 1 / Real.sqrt 3 :=
    (div_lt_div_iff₀ (by norm_num) sqrt_three_pos).mpr (by
      nlinarith [sqrt_three_sq])
  linarith

/-- AM--GM in the exact form used by S17(c). -/
lemma two_sqrt_mul_le_add (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  rw [Real.sqrt_mul hx]
  nlinarith [two_mul_le_add_sq (Real.sqrt x) (Real.sqrt y),
    Real.sq_sqrt hx, Real.sq_sqrt hy]

/-- The quadratic core of S17(c). -/
lemma sqrt_product_le_two_sub_sqrt_three
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 1) (hy1 : y ≤ 1)
    (hchamber : 2 * x + 2 * y - x * y ≤ 1) :
    Real.sqrt (x * y) ≤ 2 - Real.sqrt 3 := by
  let w := Real.sqrt (x * y)
  have hp : 0 ≤ x * y := mul_nonneg hx hy
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hwsq : w ^ 2 = x * y := Real.sq_sqrt hp
  have hprod_le_one : x * y ≤ 1 := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hy1)]
  have hw1 : w ≤ 1 := by nlinarith
  have hamgm : 4 * w ≤ 2 * x + 2 * y := by
    have h := two_sqrt_mul_le_add x y hx hy
    dsimp [w]
    linarith
  have hquad : 4 * w - w ^ 2 ≤ 1 := by linarith
  have ht0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  by_contra hnot
  have hlt : 2 - Real.sqrt 3 < w := lt_of_not_ge hnot
  nlinarith [sqrt_three_sq]

/-- The numerical upper estimate in the `X ≥ Y` chamber of S17(c). -/
lemma one_add_product_div_two_le_kappa
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 1) (hy1 : y ≤ 1)
    (hchamber : 2 * x + 2 * y - x * y ≤ 1) :
    (1 + x * y) / 2 ≤ kappa := by
  let w := Real.sqrt (x * y)
  have hp : 0 ≤ x * y := mul_nonneg hx hy
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hwsq : w ^ 2 = x * y := Real.sq_sqrt hp
  have hw : w ≤ 2 - Real.sqrt 3 :=
    sqrt_product_le_two_sub_sqrt_three x y hx hy hx1 hy1 hchamber
  have hroot0 : 0 ≤ 2 - Real.sqrt 3 := by
    linarith [sqrt_three_lt_two]
  have hsq : w ^ 2 ≤ (2 - Real.sqrt 3) ^ 2 :=
    (sq_le_sq₀ hw0 hroot0).mpr hw
  unfold kappa
  nlinarith [sqrt_three_sq]

/-- Rearranging S16 and the lower cross-term bound produces the chamber
inequality needed by `one_add_product_div_two_le_kappa`. -/
lemma chamber_ineq_of_cross_term
    (rho chi xi eta z : ℝ)
    (hxi : xi = 1 - rho) (heta : eta = 1 - chi)
    (hzlower : -rho * chi ≤ z) (horder : z ≤ rho + chi - 2) :
    2 * xi + 2 * eta - xi * eta ≤ 1 := by
  rw [hxi, heta]
  nlinarith

/-- The `X ≥ Y` chamber estimate used both in S17(c) and in the local S53
baseline: the average capacity is at most `κ q²`. -/
lemma profile_average_le_kappa_of_black_ge_white
    (q r0 r1 c0 c1 : ℝ) (hq : 0 < q)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hrsum : r0 + r1 ≤ q) (hcsum : c0 + c1 ≤ q)
    (horder : (q - r0) * (q - c0) + (q - r1) * (q - c1) ≤
      r0 * c1 + r1 * c0) :
    (r0 * c1 + r1 * c0 +
      ((q - r0) * (q - c0) + (q - r1) * (q - c1))) / 2 ≤
        kappa * q ^ 2 := by
  let X := r0 * c1 + r1 * c0
  let Y := (q - r0) * (q - c0) + (q - r1) * (q - c1)
  let rho := (r0 + r1) / q
  let chi := (c0 + c1) / q
  let xi := 1 - rho
  let eta := 1 - chi
  let z := ((r0 - r1) * (c0 - c1)) / q ^ 2
  have hid := profile_identities q r0 r1 c0 c1 (ne_of_gt hq)
  have hminus : (X - Y) / q ^ 2 = rho + chi - 2 - z := by
    simpa only [X, Y, rho, chi, z] using hid.1
  have hplus : (X + Y) / q ^ 2 = 1 + xi * eta := by
    rw [show (X + Y) / q ^ 2 = 2 - rho - chi + rho * chi by
      simpa only [X, Y, rho, chi] using hid.2]
    dsimp [xi, eta]
    ring
  have hcross := profile_cross_term_abs_le q r0 r1 c0 c1 hq hr0 hr1 hc0 hc1
  change |z| ≤ rho * chi at hcross
  have hxi0 : 0 ≤ xi := by
    dsimp [xi, rho]
    apply sub_nonneg.mpr
    rw [div_le_iff₀ hq]
    simpa using hrsum
  have hxi1 : xi ≤ 1 := by
    dsimp [xi, rho]
    have : 0 ≤ (r0 + r1) / q := div_nonneg (by linarith) (le_of_lt hq)
    linarith
  have heta0 : 0 ≤ eta := by
    dsimp [eta, chi]
    apply sub_nonneg.mpr
    rw [div_le_iff₀ hq]
    simpa using hcsum
  have heta1 : eta ≤ 1 := by
    dsimp [eta, chi]
    have : 0 ≤ (c0 + c1) / q := div_nonneg (by linarith) (le_of_lt hq)
    linarith
  have hdiff : 0 ≤ rho + chi - 2 - z := by
    have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
    have hXY : Y ≤ X := by simpa only [X, Y] using horder
    have : 0 ≤ (X - Y) / q ^ 2 :=
      div_nonneg (sub_nonneg.mpr hXY) (le_of_lt hq2)
    rwa [hminus] at this
  have hzlower : -rho * chi ≤ z := by
    have h := neg_abs_le z
    linarith
  have hzorder : z ≤ rho + chi - 2 := by linarith
  have hchamber := chamber_ineq_of_cross_term rho chi xi eta z (by rfl) (by rfl)
    hzlower hzorder
  have havg : (1 + xi * eta) / 2 ≤ kappa :=
    one_add_product_div_two_le_kappa xi eta hxi0 heta0 hxi1 heta1 hchamber
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
  have hsum : X + Y ≤ 2 * (kappa * q ^ 2) := by
    have hsum' : (X + Y) / q ^ 2 ≤ 2 * kappa := by
      rw [hplus]
      nlinarith
    have h := (div_le_iff₀ hq2).mp hsum'
    nlinarith
  dsimp [X, Y] at hsum ⊢
  linarith

/-- The purely numerical second inequality in S20(c). -/
lemma escape_quadratic_pos {q : ℝ} (hq : 64 ≤ q) :
    0 < q ^ 2 / 125 - q / 2 - 1 / 4 := by
  nlinarith [sq_nonneg (q - 64)]

/-- S20(c), factored so that S19 can supply its lower bound as one premise. -/
lemma escape_from_continuous_lower
    {q h : ℝ} (hq : 64 ≤ q)
    (hlower : kappa * q ^ 2 - gamma * q - 1 / 4 ≤ h) :
    0 < h - (527 : ℝ) / 1000 * q ^ 2 := by
  have hq0 : 0 ≤ q := by linarith
  have hmargin := kappa_escape_margin
  have hgamma := gamma_lt_half
  have hquad := escape_quadratic_pos hq
  have hmarginq : q / 125 < (kappa - 527 / 1000) * q := by
    nlinarith [mul_lt_mul_of_pos_right hmargin (by linarith : 0 < q)]
  have hgammaq : gamma * q ≤ q / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hgamma) hq0]
  nlinarith

lemma sqrt_three_gt_one_s17 : 1 < Real.sqrt 3 := by
  apply (sq_lt_sq₀ (by norm_num) (le_of_lt sqrt_three_pos)).mp
  norm_num [sqrt_three_sq]

/-- The complementary-product estimate used by the `X ≤ Y` subcase of S17.
If `xy` lies past the plaid threshold, then the complementary rectangle is
strictly below `κ`. -/
lemma one_sub_mul_one_sub_lt_kappa_of_product_gt_s17
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 1) (hy1 : y ≤ 1)
    (hprod : (2 - Real.sqrt 3) ^ 2 < x * y) :
    (1 - x) * (1 - y) < kappa := by
  let w := Real.sqrt (x * y)
  have hp : 0 ≤ x * y := mul_nonneg hx hy
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hwsq : w ^ 2 = x * y := Real.sq_sqrt hp
  have hxy_le_one : x * y ≤ 1 := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hy1)]
  have hw1 : w ≤ 1 := by nlinarith
  have hthreshold0 : 0 ≤ 2 - Real.sqrt 3 := by
    linarith [sqrt_three_lt_two]
  have hw_threshold : 2 - Real.sqrt 3 < w := by
    apply (sq_lt_sq₀ hthreshold0 hw0).mp
    nlinarith
  have hamgm : 2 * w ≤ x + y := by
    simpa [w] using two_sqrt_mul_le_add x y hx hy
  have hcomp : (1 - x) * (1 - y) ≤ (1 - w) ^ 2 := by
    nlinarith
  have hsub0 : 0 ≤ 1 - w := by linarith
  have hsqrt_sub0 : 0 ≤ Real.sqrt 3 - 1 := by
    linarith [sqrt_three_gt_one_s17]
  have hsq : (1 - w) ^ 2 < (Real.sqrt 3 - 1) ^ 2 :=
    (sq_lt_sq₀ hsub0 hsqrt_sub0).mpr (by linarith)
  unfold kappa
  nlinarith [sqrt_three_sq]

/-- The `X ≤ Y` branch of S17 after reduction to the nonnegative-sum
chamber (`r₀+r₁≤q`, `c₀+c₁≤q`). -/
lemma profile_black_le_kappa_of_white_ge_black_s17
    (q r0 r1 c0 c1 : ℝ) (hq : 0 < q)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hrsum : r0 + r1 ≤ q) (hcsum : c0 + c1 ≤ q)
    (horder : r0 * c1 + r1 * c0 ≤
      (q - r0) * (q - c0) + (q - r1) * (q - c1)) :
    r0 * c1 + r1 * c0 ≤ kappa * q ^ 2 := by
  let X := r0 * c1 + r1 * c0
  let Y := (q - r0) * (q - c0) + (q - r1) * (q - c1)
  let rho := (r0 + r1) / q
  let chi := (c0 + c1) / q
  let xi := 1 - rho
  let eta := 1 - chi
  have hid := profile_identities q r0 r1 c0 c1 (ne_of_gt hq)
  have hplus : (X + Y) / q ^ 2 = 1 + xi * eta := by
    rw [show (X + Y) / q ^ 2 = 2 - rho - chi + rho * chi by
      simpa only [X, Y, rho, chi] using hid.2]
    dsimp [xi, eta]
    ring
  have hxi0 : 0 ≤ xi := by
    dsimp [xi, rho]
    apply sub_nonneg.mpr
    rw [div_le_iff₀ hq]
    simpa using hrsum
  have hxi1 : xi ≤ 1 := by
    dsimp [xi, rho]
    have : 0 ≤ (r0 + r1) / q := div_nonneg (by linarith) (le_of_lt hq)
    linarith
  have heta0 : 0 ≤ eta := by
    dsimp [eta, chi]
    apply sub_nonneg.mpr
    rw [div_le_iff₀ hq]
    simpa using hcsum
  have heta1 : eta ≤ 1 := by
    dsimp [eta, chi]
    have : 0 ≤ (c0 + c1) / q := div_nonneg (by linarith) (le_of_lt hq)
    linarith
  have hXle_product : X ≤ (r0 + r1) * (c0 + c1) := by
    dsimp [X]
    nlinarith [mul_nonneg hr0 hc0, mul_nonneg hr1 hc1]
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
  have hproduct_eq : (r0 + r1) * (c0 + c1) = rho * chi * q ^ 2 := by
    dsimp [rho, chi]
    field_simp [ne_of_gt hq]
  by_contra hnot
  have hXgt : kappa * q ^ 2 < X := lt_of_not_ge hnot
  have hXY : X ≤ Y := by simpa only [X, Y] using horder
  have hsum_gt : 2 * kappa < (X + Y) / q ^ 2 := by
    apply (lt_div_iff₀ hq2).mpr
    nlinarith
  have hxi_eta_gt : (2 - Real.sqrt 3) ^ 2 < xi * eta := by
    rw [hplus] at hsum_gt
    unfold kappa at hsum_gt
    nlinarith [sqrt_three_sq]
  have hcomp := one_sub_mul_one_sub_lt_kappa_of_product_gt_s17
    xi eta hxi0 heta0 hxi1 heta1 hxi_eta_gt
  have hrhochi : rho * chi < kappa := by
    simpa [xi, eta] using hcomp
  have hXlt : X < kappa * q ^ 2 := by
    calc
      X ≤ (r0 + r1) * (c0 + c1) := hXle_product
      _ = rho * chi * q ^ 2 := hproduct_eq
      _ < kappa * q ^ 2 := mul_lt_mul_of_pos_right hrhochi hq2
  exact (not_lt_of_ge (le_of_lt hXgt)) hXlt

/-- The mixed-sum branch of S17: the normalized product is nonpositive, so
the average is at most `q²/2`. -/
lemma profile_min_le_kappa_of_mixed_sums_s17
    (q r0 r1 c0 c1 : ℝ) (hq : 0 < q)
    (hrsum : r0 + r1 ≤ q) (hcsum : q ≤ c0 + c1) :
    min (r0 * c1 + r1 * c0)
      ((q - r0) * (q - c0) + (q - r1) * (q - c1)) ≤ kappa * q ^ 2 := by
  let X := r0 * c1 + r1 * c0
  let Y := (q - r0) * (q - c0) + (q - r1) * (q - c1)
  let rho := (r0 + r1) / q
  let chi := (c0 + c1) / q
  let xi := 1 - rho
  let eta := 1 - chi
  have hid := profile_identities q r0 r1 c0 c1 (ne_of_gt hq)
  have hplus : (X + Y) / q ^ 2 = 1 + xi * eta := by
    rw [show (X + Y) / q ^ 2 = 2 - rho - chi + rho * chi by
      simpa only [X, Y, rho, chi] using hid.2]
    dsimp [xi, eta]
    ring
  have hxi : 0 ≤ xi := by
    dsimp [xi, rho]
    apply sub_nonneg.mpr
    rw [div_le_iff₀ hq]
    simpa using hrsum
  have heta : eta ≤ 0 := by
    dsimp [eta, chi]
    apply sub_nonpos.mpr
    rw [le_div_iff₀ hq]
    simpa using hcsum
  have hprod : xi * eta ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hxi heta
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq
  have hsum : X + Y ≤ q ^ 2 := by
    have hs : (X + Y) / q ^ 2 ≤ 1 := by
      rw [hplus]
      linarith
    have := (div_le_iff₀ hq2).mp hs
    nlinarith
  have havg : (X + Y) / 2 ≤ q ^ 2 / 2 := by
    linarith
  have hminavg : min X Y ≤ (X + Y) / 2 := by
    have hleft : min X Y ≤ X := min_le_left _ _
    have hright : min X Y ≤ Y := min_le_right _ _
    linarith
  have hk : q ^ 2 / 2 ≤ kappa * q ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right (le_of_lt kappa_gt_half) (le_of_lt hq2)]
  dsimp [X, Y] at hminavg ⊢
  linarith

/-- The two ordering subcases when both normalized sums are at most one. -/
lemma profile_min_le_kappa_of_sums_le_s17
    (q r0 r1 c0 c1 : ℝ) (hq : 0 < q)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hrsum : r0 + r1 ≤ q) (hcsum : c0 + c1 ≤ q) :
    min (r0 * c1 + r1 * c0)
      ((q - r0) * (q - c0) + (q - r1) * (q - c1)) ≤ kappa * q ^ 2 := by
  let X := r0 * c1 + r1 * c0
  let Y := (q - r0) * (q - c0) + (q - r1) * (q - c1)
  rcases le_total X Y with hXY | hYX
  · have hX := profile_black_le_kappa_of_white_ge_black_s17 q r0 r1 c0 c1
      hq hr0 hr1 hc0 hc1 hrsum hcsum (by simpa only [X, Y] using hXY)
    change min X Y ≤ kappa * q ^ 2
    rw [min_eq_left hXY]
    exact hX
  · have havg := profile_average_le_kappa_of_black_ge_white q r0 r1 c0 c1
      hq hr0 hr1 hc0 hc1 hrsum hcsum (by simpa only [X, Y] using hYX)
    have hminavg : min X Y ≤ (X + Y) / 2 := by
      have hleft : min X Y ≤ X := min_le_left _ _
      have hright : min X Y ≤ Y := min_le_right _ _
      linarith
    change min X Y ≤ kappa * q ^ 2
    linarith

/-- Full continuous upper bound (paper `lem:Hupper`, real part): every box
profile has smaller capacity at most `κ q²`. -/
lemma profile_min_le_kappa_s17
    (q r0 r1 c0 c1 : ℝ) (hq : 0 < q)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hr0q : r0 ≤ q) (hr1q : r1 ≤ q) (hc0q : c0 ≤ q) (hc1q : c1 ≤ q) :
    min (r0 * c1 + r1 * c0)
      ((q - r0) * (q - c0) + (q - r1) * (q - c1)) ≤ kappa * q ^ 2 := by
  rcases le_total (r0 + r1) q with hrsum | hrsum
  · rcases le_total (c0 + c1) q with hcsum | hcsum
    · exact profile_min_le_kappa_of_sums_le_s17 q r0 r1 c0 c1
        hq hr0 hr1 hc0 hc1 hrsum hcsum
    · exact profile_min_le_kappa_of_mixed_sums_s17 q r0 r1 c0 c1
        hq hrsum hcsum
  · rcases le_total (c0 + c1) q with hcsum | hcsum
    · have hswap := profile_min_le_kappa_of_mixed_sums_s17 q c0 c1 r0 r1
        hq hcsum hrsum
      convert hswap using 1
      all_goals ring
    · have hcomp := profile_min_le_kappa_of_sums_le_s17
        q (q - r0) (q - r1) (q - c1) (q - c0) hq
        (sub_nonneg.mpr hr0q) (sub_nonneg.mpr hr1q)
        (sub_nonneg.mpr hc1q) (sub_nonneg.mpr hc0q)
        (by linarith) (by linarith)
      rw [min_comm]
      convert hcomp using 1
      all_goals ring

end


lemma profile_min_le_floor_s18
    (q r0 r1 c0 c1 : ℕ)
    (hq : 0 < q)
    (hr0 : r0 ≤ q) (hr1 : r1 ≤ q) (hc0 : c0 ≤ q) (hc1 : c1 ≤ q) :
    min (profileBlack r0 r1 c0 c1) (profileWhite q r0 r1 c0 c1) ≤
      ⌊kappa * (q : ℝ) ^ 2⌋₊ := by
  apply Nat.le_floor
  have hcont := profile_min_le_kappa_s17
    (q : ℝ) (r0 : ℝ) (r1 : ℝ) (c0 : ℝ) (c1 : ℝ)
    (by exact_mod_cast hq)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast hr0) (by exact_mod_cast hr1)
    (by exact_mod_cast hc0) (by exact_mod_cast hc1)
  rw [Nat.cast_min]
  · change min (↑(profileBlack r0 r1 c0 c1) : ℝ)
      (↑(profileWhite q r0 r1 c0 c1) : ℝ) ≤ _
    rw [show (profileBlack r0 r1 c0 c1 : ℝ) = (r0 : ℝ) * c1 + (r1 : ℝ) * c0 by
      simp [profileBlack]]
    rw [show (profileWhite q r0 r1 c0 c1 : ℝ) =
      ((q : ℝ) - r0) * ((q : ℝ) - c0) +
        ((q : ℝ) - r1) * ((q : ℝ) - c1) by
      simp only [profileWhite, Nat.cast_add, Nat.cast_mul,
        Nat.cast_sub hr0, Nat.cast_sub hr1, Nat.cast_sub hc0, Nat.cast_sub hc1]]
    exact hcont

/-- Paper `lem:Hupper`, integer consequence (S18): `H(2q) ≤ ⌊κq²⌋`. -/
theorem H_le_floor_s18 (q : ℕ) (hq : 0 < q) :
    H q ≤ ⌊kappa * (q : ℝ) ^ 2⌋₊ := by
  apply H_le
  intro r0 r1 c0 c1 hr0 hr1 hc0 hc1
  exact profile_min_le_floor_s18 q r0 r1 c0 c1 hq hr0 hr1 hc0 hc1

#print axioms profile_min_le_floor_s18
#print axioms H_le_floor_s18

lemma profileWhite_floorceil_eq (q P : ℕ) (hP : P ≤ 2*q) :
    profileWhite q 0 (P / 2) ((P + 1) / 2) 0 = 2*q^2 - q*P := by
  unfold profileWhite
  have hhalf : P / 2 ≤ q := by omega
  have hceil : (P + 1) / 2 ≤ q := by omega
  have hsum : P / 2 + (P + 1) / 2 = P := by omega
  have hsumq : (q - (P + 1) / 2) + (q - P / 2) = 2*q - P := by omega
  calc
    (q - 0) * (q - (P + 1) / 2) +
        (q - P / 2) * (q - 0) =
      q * (q - (P + 1) / 2) + q * (q - P / 2) := by simp [Nat.mul_comm]
    _ = q * ((q - (P + 1) / 2) + (q - P / 2)) := by rw [Nat.mul_add]
    _ = q * (2*q - P) := by rw [hsumq]
    _ = 2*q^2 - q*P := by rw [Nat.mul_sub_left_distrib]; ring

lemma H_ge_profile_floorceil (q P : ℕ) (hP : P ≤ 2*q) :
    min ((P / 2) * ((P + 1) / 2)) (2*q^2 - q*P) ≤ H q := by
  rw [← profileWhite_floorceil_eq q P hP]
  convert le_H (q := q) (r0 := 0) (r1 := P / 2) (c0 := (P+1)/2) (c1 := 0)
    (by omega) (by omega) (by omega) (by omega) using 1 <;>
      simp [profileBlack]

lemma floorceil_mul_eq_floor_sq (P : ℕ) :
    (P / 2) * ((P + 1) / 2) = P^2 / 4 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' P
  · rw [show (2 * k + 1) / 2 = k by omega]
    rw [show (2 * k) ^ 2 = k * (k * 4) by ring]
    rw [Nat.mul_div_assoc k (by exact ⟨k, by ring⟩ : 4 ∣ k * 4)]
    simp
  · rw [show (2 * k + 1) / 2 = k by omega]
    rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    symm
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith

lemma H_ge_profile_floor_sq (q P : ℕ) (hP : P ≤ 2*q) :
    min (P^2 / 4) (2*q^2 - q*P) ≤ H q := by
  simpa [floorceil_mul_eq_floor_sq P] using H_ge_profile_floorceil q P hP

#print axioms H_ge_profile_floorceil
#print axioms H_ge_profile_floor_sq

lemma floor_sq_cast_lower (P : ℕ) :
    (P : ℝ)^2 / 4 - 1/4 ≤ (P^2 / 4 : ℕ) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' P
  · have hdiv : (2*k)^2 / 4 = k*k := by
      rw [show (2*k)^2 = k * (k*4) by ring]
      rw [Nat.mul_div_assoc k (by exact ⟨k, by ring⟩ : 4 ∣ k * 4)]
      simp
    rw [hdiv]
    norm_num
    nlinarith
  · have hdiv : (2*k+1)^2 / 4 = k*(k+1) := by
      apply Nat.div_eq_of_lt_le
      · nlinarith
      · nlinarith
    rw [hdiv]
    norm_num
    nlinarith

lemma profile_value_P_lower (q P : ℕ) (hP : P ≤ 2*q) :
    min ((P^2 / 4 : ℕ)) (2*q^2 - q*P) ≤ H q :=
  H_ge_profile_floor_sq q P hP

/-- Paper `lem:Hlower` (S19): `κq² - γq - 1/4 ≤ H(2q)` for every `q ≥ 1`, from the
profiles `(0, ⌊P/2⌋, ⌈P/2⌉, 0)` at `P = ⌊2sq⌋` and `P = ⌊2sq⌋ + 1`. -/
lemma H_lower_s19 (q : ℕ) (hq : 0 < q) :
    kappa * (q : ℝ)^2 - gamma * (q : ℝ) - 1/4 ≤ (H q : ℝ) := by
  let s : ℝ := Real.sqrt 3 - 1
  let x : ℝ := 2 * s * (q : ℝ)
  let m : ℕ := ⌊x⌋₊
  have hs0 : 0 ≤ s := by
    dsimp [s]
    nlinarith [sqrt_three_gt_one_s17]
  have hs1 : s < 1 := by
    dsimp [s]
    nlinarith [sqrt_three_lt_two]
  have hk : kappa = s^2 := by
    dsimp [kappa, s]
    nlinarith [sqrt_three_sq]
  have hk2 : kappa = 2 * (1 - s) := by
    dsimp [kappa, s]
    ring
  have hg : gamma = s / (1 + s) := by
    dsimp [gamma, s]
    field_simp [ne_of_gt sqrt_three_pos]
    ring
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqR0 : 0 ≤ (q : ℝ) := le_of_lt hqR
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxlt : x < (2*q : ℕ) := by
    dsimp [x]
    norm_num
    nlinarith [hs1]
  have hmle : (m : ℝ) ≤ x := by
    dsimp [m]
    exact Nat.floor_le hx0
  have hm_lt : m < 2*q := by
    apply (Nat.floor_lt hx0).mpr
    exact hxlt
  have hm1 : m + 1 ≤ 2*q := by omega
  have hdelta0 : 0 ≤ x - (m : ℝ) := by linarith
  have hdelta1 : x - (m : ℝ) < 1 := by
    have := Nat.lt_floor_add_one x
    linarith
  have hmval : (↑(min (m^2 / 4) (2*q^2 - q*m) : ℕ) : ℝ) ≤ (H q : ℝ) := by
    exact_mod_cast profile_value_P_lower q m hm_lt.le
  have hmval' : min ((m^2 / 4 : ℕ) : ℝ) ((2*q^2 - q*m : ℕ) : ℝ) ≤ (H q : ℝ) := by
    simpa only [Nat.cast_min] using hmval
  have hm_lower : kappa * (q : ℝ)^2 - s * (q : ℝ) * (x - (m : ℝ)) - 1/4 ≤
      (H q : ℝ) := by
    apply le_trans ?_ hmval'
    apply le_min
    · have hfloor := floor_sq_cast_lower m
      have hsq : 0 ≤ ((m : ℝ) - x)^2 := sq_nonneg _
      rw [hk]
      dsimp [x] at hsq ⊢
      norm_num at hsq ⊢
      nlinarith
    · rw [Nat.cast_sub]
      · rw [Nat.cast_mul, Nat.cast_pow]
        norm_num [Nat.cast_mul, Nat.cast_pow]
        rw [hk2]
        dsimp [x] at *
        nlinarith
      · nlinarith [show m ≤ 2*q from hm_lt.le]
  have hmpval : (↑(min ((m+1)^2 / 4) (2*q^2 - q*(m+1)) : ℕ) : ℝ) ≤
      (H q : ℝ) := by
    exact_mod_cast profile_value_P_lower q (m+1) hm1
  have hmpval' : min (((m+1)^2 / 4 : ℕ) : ℝ)
      (((2*q^2 - q*(m+1) : ℕ) : ℝ)) ≤ (H q : ℝ) := by
    simpa only [Nat.cast_min] using hmpval
  have hmp_lower : kappa * (q : ℝ)^2 - (q : ℝ) * (1 - (x - (m : ℝ))) - 1/4 ≤
      (H q : ℝ) := by
    apply le_trans ?_ hmpval'
    apply le_min
    · have hfloor := floor_sq_cast_lower (m+1)
      norm_num [Nat.cast_pow] at hfloor
      have hsq : 0 ≤ (((m+1 : ℕ) : ℝ) - x)^2 := sq_nonneg _
      rw [hk]
      dsimp [x] at hsq ⊢
      norm_num at hsq ⊢
      nlinarith
    · rw [Nat.cast_sub]
      · rw [Nat.cast_mul, Nat.cast_pow]
        norm_num [Nat.cast_mul, Nat.cast_pow]
        rw [hk2]
        dsimp [x] at *
        nlinarith
      · nlinarith [show m+1 ≤ 2*q from hm1]
  have hden : 0 < 1 + s := by linarith
  by_cases hcase : s * (x - (m : ℝ)) ≤ 1 - (x - (m : ℝ))
  · have hbound : s * (x - (m : ℝ)) ≤ gamma := by
      rw [hg]
      apply (le_div_iff₀ hden).2
      have ht : (1+s) * (x - (m : ℝ)) ≤ 1 := by
        nlinarith only [hcase]
      nlinarith [mul_le_mul_of_nonneg_left ht hs0]
    have hmul := mul_le_mul_of_nonneg_right hbound hqR0
    nlinarith only [hm_lower, hmul]
  · have hbound : 1 - (x - (m : ℝ)) ≤ gamma := by
      rw [hg]
      apply (le_div_iff₀ hden).2
      have hcase' : 1 - (x - (m : ℝ)) < s * (x - (m : ℝ)) := lt_of_not_ge hcase
      have ht : 1 ≤ (1+s) * (x - (m : ℝ)) := by
        nlinarith only [hcase']
      nlinarith only [ht]
    have hmul := mul_le_mul_of_nonneg_right hbound hqR0
    nlinarith only [hmp_lower, hmul]

/-- Paper `lem:escape` (S20): `527/1000·q² < H(2q)` for every `q ≥ 64`. -/
theorem H_escape_s20 (q : ℕ) (hq : 64 ≤ q) :
    0 < (H q : ℝ) - (527 : ℝ) / 1000 * (q : ℝ) ^ 2 := by
  have hqpos : 0 < q := by omega
  apply escape_from_continuous_lower (q := (q : ℝ)) (h := (H q : ℝ))
  · exact_mod_cast hq
  · exact H_lower_s19 q hqpos

#print axioms profile_identities
#print axioms profile_cross_term_abs_le
#print axioms profile_average_le_kappa_of_black_ge_white
#print axioms escape_from_continuous_lower
#print axioms profile_min_le_kappa_s17
#print axioms H_lower_s19
#print axioms H_escape_s20

end PeaceableQueens.UpperBound
