import PeaceableQueens.UpperBound.LargeOrderConfiguration
import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.ProfileAlgebra

namespace PeaceableQueens.UpperBound.LargeOrderFinish

open ConfigurationBridge ConfigurationMoments MomentModel
open LargeOrderAlgebra LargeOrderAlgebra.Local
open LargeOrderConfiguration SupportCuts

/-- Paper `def:N` in count form (S43): the eight inequalities of the plaid
neighbourhood `N` on the unnormalized outer counts. -/
def InLargeOrderNeighborhood (cfg : Configuration n) : Prop :=
  10 * outerCount cfg ⟨.row, 0⟩ ≤ n ∧
  10 * outerCount cfg ⟨.column, 0⟩ ≤ n ∧
  10 * outerCount cfg ⟨.diagonal, 1⟩ ≤ n ∧
  10 * outerCount cfg ⟨.antidiagonal, 1⟩ ≤ n ∧
  3 * n ≤ 5 * outerCount cfg ⟨.row, 1⟩ ∧
  8 * outerCount cfg ⟨.row, 1⟩ ≤ 7 * n ∧
  3 * n ≤ 5 * outerCount cfg ⟨.column, 1⟩ ∧
  8 * outerCount cfg ⟨.column, 1⟩ ≤ 7 * n

lemma local_neighborhood_transport (cfg : Configuration n) (h : InLargeOrderNeighborhood cfg) :
    (localOfConfiguration cfg).u ≤ (localOfConfiguration cfg).q / 10 ∧
    (localOfConfiguration cfg).v ≤ (localOfConfiguration cfg).q / 10 ∧
    (localOfConfiguration cfg).e ≤ (localOfConfiguration cfg).q / 10 ∧
    (localOfConfiguration cfg).f ≤ (localOfConfiguration cfg).q / 10 ∧
    3 * (localOfConfiguration cfg).q / 5 ≤ (localOfConfiguration cfg).R ∧
    (localOfConfiguration cfg).R ≤ 7 * (localOfConfiguration cfg).q / 8 ∧
    3 * (localOfConfiguration cfg).q / 5 ≤ (localOfConfiguration cfg).C ∧
    (localOfConfiguration cfg).C ≤ 7 * (localOfConfiguration cfg).q / 8 := by
  rcases h with ⟨hu, hv, he, hf, hRlo, hRhi, hClo, hChi⟩
  have huQ : (10 : ℚ) * outerCount cfg ⟨.row, 0⟩ ≤ n := by exact_mod_cast hu
  have hvQ : (10 : ℚ) * outerCount cfg ⟨.column, 0⟩ ≤ n := by exact_mod_cast hv
  have heQ : (10 : ℚ) * outerCount cfg ⟨.diagonal, 1⟩ ≤ n := by exact_mod_cast he
  have hfQ : (10 : ℚ) * outerCount cfg ⟨.antidiagonal, 1⟩ ≤ n := by exact_mod_cast hf
  have hRloQ : (3 : ℚ) * n ≤ 5 * outerCount cfg ⟨.row, 1⟩ := by exact_mod_cast hRlo
  have hRhiQ : (8 : ℚ) * outerCount cfg ⟨.row, 1⟩ ≤ 7 * n := by exact_mod_cast hRhi
  have hCloQ : (3 : ℚ) * n ≤ 5 * outerCount cfg ⟨.column, 1⟩ := by exact_mod_cast hClo
  have hChiQ : (8 : ℚ) * outerCount cfg ⟨.column, 1⟩ ≤ 7 * n := by exact_mod_cast hChi
  dsimp [localOfConfiguration]
  norm_num at *
  constructor
  · linarith [huQ]
  constructor
  · linarith [hvQ]
  constructor
  · linarith [heQ]
  constructor
  · linarith [hfQ]
  constructor
  · linarith [hRloQ]
  constructor
  · linarith [hRhiQ]
  constructor
  · linarith [hCloQ]
  · linarith [hChiQ]

lemma local_cut609_scaled (d : Local) (hq : d.q ≠ 0) :
    cut609Local (d.u / d.q) (d.R / d.q) (d.v / d.q) (d.C / d.q)
      (d.g / d.q) (d.e / d.q) (d.h / d.q) (d.f / d.q) = d.FB / d.q ^ 2 := by
  dsimp [cut609Local, FB, X, beta, zeta, Q, sigma]
  field_simp
  ring

lemma local_cut559_scaled (d : Local) (hq : d.q ≠ 0) :
    cut559Local (d.u / d.q) (d.R / d.q) (d.v / d.q) (d.C / d.q)
      (d.g / d.q) (d.e / d.q) (d.h / d.q) (d.f / d.q) = d.FW / d.q ^ 2 := by
  dsimp [cut559Local, FW, Y, alpha, delta, Q, sigma, m]
  field_simp
  ring

lemma local_profile_eq (cfg : Configuration n) (hq : 0 < n) :
    normalizedProfile cfg =
      localProfile ((localOfConfiguration cfg).u / n) ((localOfConfiguration cfg).R / n)
        ((localOfConfiguration cfg).v / n) ((localOfConfiguration cfg).C / n)
        ((localOfConfiguration cfg).g / n) ((localOfConfiguration cfg).e / n)
        ((localOfConfiguration cfg).h / n) ((localOfConfiguration cfg).f / n) := by
  have hle (c : OuterCoord) : outerCount cfg c ≤ n := outerCount_le cfg hq c
  funext c
  cases c with
  | mk family parity =>
    cases family <;> fin_cases parity <;>
      simp [normalizedProfile_eq_div, localProfile, localOfConfiguration]
    all_goals norm_num
    all_goals field_simp
    all_goals ring

/-- Paper `lem:cuts`, equation `eq:FB`: the individual black count. -/
lemma cut609_configuration_black (cfg : Configuration n) [NeZero (2 * n)] (hq : 0 < n) :
    (cfg.blackCells.card : ℚ) ≤ (localOfConfiguration cfg).FB := by
  have hcut := cut609_black_bound cfg hq
  have htotal := configurationWeights_blackTotal cfg
  have hprof := local_profile_eq cfg hq
  have hlocal := cut609_rhs_local
    ((localOfConfiguration cfg).u / n) ((localOfConfiguration cfg).R / n)
    ((localOfConfiguration cfg).v / n) ((localOfConfiguration cfg).C / n)
    ((localOfConfiguration cfg).g / n) ((localOfConfiguration cfg).e / n)
    ((localOfConfiguration cfg).h / n) ((localOfConfiguration cfg).f / n)
  have hscale := local_cut609_scaled (localOfConfiguration cfg) (by
    change (n : ℚ) ≠ 0
    exact_mod_cast Nat.ne_of_gt hq)
  have hdq : (localOfConfiguration cfg).q = (n : ℚ) := rfl
  rw [hdq] at hscale
  rw [htotal, hprof, hlocal, hscale] at hcut
  have hq2 : (0 : ℚ) < (n : ℚ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hq)
  have hmul := (div_le_div_iff₀ hq2 hq2).mp hcut
  nlinarith
/-- Paper `lem:cuts`, equation `eq:FW`: the individual white count. -/
lemma cut559_configuration_white (cfg : Configuration n) [NeZero (2 * n)] (hq : 0 < n) :
    (cfg.whiteCells.card : ℚ) ≤ (localOfConfiguration cfg).FW := by
  have hcut := cut559_white_bound cfg hq
  have htotal := configurationWeights_whiteTotal cfg
  have hprof := local_profile_eq cfg hq
  have hlocal := cut559_rhs_local
    ((localOfConfiguration cfg).u / n) ((localOfConfiguration cfg).R / n)
    ((localOfConfiguration cfg).v / n) ((localOfConfiguration cfg).C / n)
    ((localOfConfiguration cfg).g / n) ((localOfConfiguration cfg).e / n)
    ((localOfConfiguration cfg).h / n) ((localOfConfiguration cfg).f / n)
  have hscale := local_cut559_scaled (localOfConfiguration cfg) (by
    change (n : ℚ) ≠ 0
    exact_mod_cast Nat.ne_of_gt hq)
  have hdq : (localOfConfiguration cfg).q = (n : ℚ) := rfl
  rw [hdq] at hscale
  rw [htotal, hprof, hlocal, hscale] at hcut
  have hq2 : (0 : ℚ) < (n : ℚ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hq)
  have hmul := (div_le_div_iff₀ hq2 hq2).mp hcut
  nlinarith

/-- S41's minimum consequences, retained for the finishing interface. -/
lemma cut609_configuration_scaled (cfg : Configuration n) [NeZero (2 * n)] (hq : 0 < n) :
    (min cfg.blackCells.card cfg.whiteCells.card : ℚ) ≤ (localOfConfiguration cfg).FB := by
  exact le_trans (b := (cfg.blackCells.card : ℚ))
    (by exact_mod_cast min_le_left cfg.blackCells.card cfg.whiteCells.card)
    (cut609_configuration_black cfg hq)

lemma cut559_configuration_scaled (cfg : Configuration n) [NeZero (2 * n)] (hq : 0 < n) :
    (min cfg.blackCells.card cfg.whiteCells.card : ℚ) ≤ (localOfConfiguration cfg).FW := by
  exact le_trans (b := (cfg.whiteCells.card : ℚ))
    (by exact_mod_cast min_le_right cfg.blackCells.card cfg.whiteCells.card)
    (cut559_configuration_white cfg hq)

/-- S42.1: the exchanged column-parity profile is admissible for `H`. -/
lemma local_min_le_H (cfg : Configuration n) (hq : 0 < n) :
    min (localOfConfiguration cfg).X (localOfConfiguration cfg).Y ≤ (H n : ℚ) := by
  let u := outerCount cfg ⟨.row, 0⟩
  let R := outerCount cfg ⟨.row, 1⟩
  let v := outerCount cfg ⟨.column, 0⟩
  let C := outerCount cfg ⟨.column, 1⟩
  have hu : u ≤ n := outerCount_le cfg hq ⟨.row, 0⟩
  have hR : R ≤ n := outerCount_le cfg hq ⟨.row, 1⟩
  have hv : v ≤ n := outerCount_le cfg hq ⟨.column, 0⟩
  have hC : C ≤ n := outerCount_le cfg hq ⟨.column, 1⟩
  have hH := le_H (q := n) (r0 := u) (r1 := R) (c0 := C) (c1 := v) hu hR hC hv
  have hHq : (min (profileBlack u R C v) (profileWhite n u R C v) : ℚ) ≤ H n := by
    exact_mod_cast hH
  simpa [u, R, v, C, localOfConfiguration, X, Y, profileBlack, profileWhite,
    Nat.cast_sub hu, Nat.cast_sub hR, Nat.cast_sub hv, Nat.cast_sub hC] using hHq

/-- S48(c), in the unscaled local variables: the four white losses average to
`3 δ L / 4`. -/
def switchLoss (d : Local) (x y : ℚ) : ℚ :=
  x * (d.q - d.C) + y * (d.q - d.R)

lemma switch_losses_average (d : Local) :
    (switchLoss d d.e (2 * d.f) + switchLoss d (2 * d.e) d.f +
      switchLoss d d.f (2 * d.e) + switchLoss d (2 * d.f) d.e) / 4 =
      3 * d.delta * d.L / 4 := by
  dsimp [switchLoss, delta, L, sigma]
  ring

lemma some_switch_loss_le_average (d : Local) :
    switchLoss d d.e (2 * d.f) ≤ 3 * d.delta * d.L / 4 ∨
      switchLoss d (2 * d.e) d.f ≤ 3 * d.delta * d.L / 4 ∨
      switchLoss d d.f (2 * d.e) ≤ 3 * d.delta * d.L / 4 ∨
      switchLoss d (2 * d.f) d.e ≤ 3 * d.delta * d.L / 4 := by
  rw [← switch_losses_average]
  by_contra h
  push_neg at h
  nlinarith

/-- The capacity comparison behind S50 once one of S48's four profiles has
been chosen. -/
lemma switched_profile_dominates_cuts (d : Local) (x y : ℚ)
    (hxy : x * y = 2 * d.e * d.f)
    (hFB : d.FB ≤ d.X + 2 * d.e * d.f)
    (huy : 0 ≤ d.u * y) (hvx : 0 ≤ d.v * x)
    (haff : d.Q ≤ d.delta * (d.L / 4 - d.m))
    (hloss : switchLoss d x y ≤ 3 * d.delta * d.L / 4) :
    min d.FB d.FW ≤
      min (d.X + d.u * y + d.v * x + x * y) (d.Y - switchLoss d x y) := by
  have hwhite : d.FW ≤ d.Y - switchLoss d x y := by
    dsimp [FW, alpha, switchLoss, delta, L, sigma, m] at haff hloss ⊢
    linarith
  have hblack : d.FB ≤ d.X + d.u * y + d.v * x + x * y := by
    rw [hxy]
    linarith
  exact min_le_min hblack hwhite

/-- S50's averaging choice, with the profile-to-`H` step deliberately kept as
an interface premise.  This is the exact algebraic part independent of the
remaining natural-coordinate transport. -/
lemma s50_switch_exists (d : Local) (hnonneg : d.Nonnegative)
    (hFB : d.FB ≤ d.X + 2 * d.e * d.f)
    (haff : d.Q ≤ d.delta * (d.L / 4 - d.m)) :
    ∃ x y : ℚ, ((x = d.e ∧ y = 2 * d.f) ∨ (x = 2 * d.e ∧ y = d.f) ∨
      (x = d.f ∧ y = 2 * d.e) ∨ (x = 2 * d.f ∧ y = d.e)) ∧ min d.FB d.FW ≤
      min (d.X + d.u * y + d.v * x + x * y) (d.Y - switchLoss d x y) := by
  rcases hnonneg with ⟨hu, hR, hv, hC, he, hf, hg, hh⟩
  rcases some_switch_loss_le_average d with h | h | h | h
  · refine ⟨d.e, 2 * d.f, Or.inl ⟨rfl, rfl⟩, ?_⟩
    apply switched_profile_dominates_cuts d d.e (2 * d.f) (by ring) hFB
      (mul_nonneg hu (by positivity)) (mul_nonneg hv he) haff h
  · refine ⟨2 * d.e, d.f, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
    apply switched_profile_dominates_cuts d (2 * d.e) d.f (by ring) hFB
      (mul_nonneg hu hf) (mul_nonneg hv (by positivity)) haff h
  · refine ⟨d.f, 2 * d.e, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_⟩
    apply switched_profile_dominates_cuts d d.f (2 * d.e) (by ring) hFB
      (mul_nonneg hu (by positivity)) (mul_nonneg hv hf) haff h
  · refine ⟨2 * d.f, d.e, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_⟩
    apply switched_profile_dominates_cuts d (2 * d.f) d.e (by ring) hFB
      (mul_nonneg hu he) (mul_nonneg hv (by positivity)) haff h

/-- The direct `H` interface for each switched S48 profile. -/
lemma nat_switched_profile_le_H (n u R v C x y : ℕ)
    (hu : u + x ≤ n) (hR : R ≤ n) (hC : C ≤ n) (hv : v + y ≤ n) :
    min (((u + x : ℕ) : ℚ) * (v + y) + R * C)
      (((n : ℚ) - (u + x)) * (n - C) + (n - R) * (n - (v + y))) ≤ H n := by
  have h := le_H (q := n) (r0 := u + x) (r1 := R) (c0 := C) (c1 := v + y)
    hu hR hC hv
  have hq : (min (profileBlack (u + x) R C (v + y))
      (profileWhite n (u + x) R C (v + y)) : ℚ) ≤ H n := by
    exact_mod_cast h
  simpa [profileBlack, profileWhite, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub hu, Nat.cast_sub hR, Nat.cast_sub hC, Nat.cast_sub hv] using hq

lemma switched_coordinate_bounds (n u v e f : ℕ)
    (hu : 10 * u ≤ n) (hv : 10 * v ≤ n)
    (he : 10 * e ≤ n) (hf : 10 * f ≤ n) :
    u + e ≤ n ∧ v + 2 * f ≤ n ∧ u + 2 * e ≤ n ∧ v + f ≤ n ∧
      u + f ≤ n ∧ v + 2 * e ≤ n ∧ u + 2 * f ≤ n ∧ v + e ≤ n := by
  omega

/-- The four concrete S48 profiles are all admissible witnesses for `H`. -/
lemma configuration_switched_profiles_H (cfg : Configuration n)
    (hq : 0 < n) (hN : InLargeOrderNeighborhood cfg) :
    let d := localOfConfiguration cfg
    min (d.X + d.u * (2 * d.f) + d.v * d.e + d.e * (2 * d.f))
        (d.Y - switchLoss d d.e (2 * d.f)) ≤ H n ∧
    min (d.X + d.u * d.f + d.v * (2 * d.e) + (2 * d.e) * d.f)
        (d.Y - switchLoss d (2 * d.e) d.f) ≤ H n ∧
    min (d.X + d.u * (2 * d.e) + d.v * d.f + d.f * (2 * d.e))
        (d.Y - switchLoss d d.f (2 * d.e)) ≤ H n ∧
    min (d.X + d.u * d.e + d.v * (2 * d.f) + (2 * d.f) * d.e)
        (d.Y - switchLoss d (2 * d.f) d.e) ≤ H n := by
  dsimp
  rcases hN with ⟨hu, hv, he, hf, hRlo, hRhi, hClo, hChi⟩
  have hR := outerCount_le cfg hq ⟨.row, 1⟩
  have hC := outerCount_le cfg hq ⟨.column, 1⟩
  have hb := switched_coordinate_bounds n
    (outerCount cfg ⟨.row, 0⟩) (outerCount cfg ⟨.column, 0⟩)
    (outerCount cfg ⟨.diagonal, 1⟩) (outerCount cfg ⟨.antidiagonal, 1⟩) hu hv he hf
  rcases hb with ⟨hue, hv2f, hu2e, hvf, huf, hv2e, hu2f, hve⟩
  constructor
  · have h := nat_switched_profile_le_H n
      (outerCount cfg ⟨.row, 0⟩) (outerCount cfg ⟨.row, 1⟩)
      (outerCount cfg ⟨.column, 0⟩) (outerCount cfg ⟨.column, 1⟩)
      (outerCount cfg ⟨.diagonal, 1⟩) (2 * outerCount cfg ⟨.antidiagonal, 1⟩)
      hue hR hC hv2f
    have h' := h
    simp [localOfConfiguration, Local.X, Local.Y, switchLoss] at h'
    apply min_le_iff.mpr
    rcases h' with h' | h'
    · left
      simp only [localOfConfiguration, Local.X]
      convert h' using 1 <;> ring

    · right
      simp only [localOfConfiguration, Local.Y, switchLoss]
      convert h' using 1 <;> ring
  constructor
  · have h := nat_switched_profile_le_H n
      (outerCount cfg ⟨.row, 0⟩) (outerCount cfg ⟨.row, 1⟩)
      (outerCount cfg ⟨.column, 0⟩) (outerCount cfg ⟨.column, 1⟩)
      (2 * outerCount cfg ⟨.diagonal, 1⟩) (outerCount cfg ⟨.antidiagonal, 1⟩)
      hu2e hR hC hvf
    have h' := h
    simp [localOfConfiguration, Local.X, Local.Y, switchLoss] at h'
    apply min_le_iff.mpr
    rcases h' with h' | h'
    · left
      simp only [localOfConfiguration, Local.X]
      convert h' using 1 <;> ring
    · right
      simp only [localOfConfiguration, Local.Y, switchLoss]
      convert h' using 1 <;> ring
  constructor
  · have h := nat_switched_profile_le_H n
      (outerCount cfg ⟨.row, 0⟩) (outerCount cfg ⟨.row, 1⟩)
      (outerCount cfg ⟨.column, 0⟩) (outerCount cfg ⟨.column, 1⟩)
      (outerCount cfg ⟨.antidiagonal, 1⟩) (2 * outerCount cfg ⟨.diagonal, 1⟩)
      huf hR hC hv2e
    have h' := h
    simp [localOfConfiguration, Local.X, Local.Y, switchLoss] at h'
    apply min_le_iff.mpr
    rcases h' with h' | h'
    · left
      simp only [localOfConfiguration, Local.X]
      convert h' using 1 <;> ring
    · right
      simp only [localOfConfiguration, Local.Y, switchLoss]
      convert h' using 1 <;> ring
  · have h := nat_switched_profile_le_H n
      (outerCount cfg ⟨.row, 0⟩) (outerCount cfg ⟨.row, 1⟩)
      (outerCount cfg ⟨.column, 0⟩) (outerCount cfg ⟨.column, 1⟩)
      (2 * outerCount cfg ⟨.antidiagonal, 1⟩) (outerCount cfg ⟨.diagonal, 1⟩)
      hu2f hR hC hve
    have h' := h
    simp [localOfConfiguration, Local.X, Local.Y, switchLoss] at h'
    apply min_le_iff.mpr
    rcases h' with h' | h'
    · left
      simp only [localOfConfiguration, Local.X]
      convert h' using 1 <;> ring
    · right
      simp only [localOfConfiguration, Local.Y, switchLoss]
      convert h' using 1 <;> ring

/-- S53, isolated from the configuration transport: the plaid neighbourhood
forces the same continuous average bound as the balanced chamber. -/
lemma s53_average_le_kappa (q u R v C : ℝ) (hq : 0 < q)
    (hu : 0 ≤ u) (hR : 0 ≤ R) (hv : 0 ≤ v) (hC : 0 ≤ C)
    (huN : u ≤ q / 10) (hvN : v ≤ q / 10)
    (hRN : R ≤ 7 * q / 8) (hCN : C ≤ 7 * q / 8)
    (horder : (q - u) * (q - C) + (q - R) * (q - v) ≤ u * v + R * C) :
    (u * v + R * C + ((q - u) * (q - C) + (q - R) * (q - v))) / 2 ≤
      kappa * q ^ 2 := by
  apply profile_average_le_kappa_of_black_ge_white q u R C v hq hu hR hC hv
  · linarith
  · linarith
  · simpa [add_comm, add_left_comm, add_assoc] using horder

lemma s54_numeric (q : ℝ) (hq : 130 ≤ q) :
    gamma * q + 9 / 4 ≤ 11 / 25 * q := by
  have hs : 0 < Real.sqrt 3 := sqrt_three_pos
  have hrecip : (1501 : ℝ) / 2600 < 1 / Real.sqrt 3 := by
    apply (lt_div_iff₀ hs).mpr
    nlinarith [sqrt_three_sq]
  have hcoef : 0 ≤ 1 / Real.sqrt 3 - 14 / 25 := by
    nlinarith
  have hq0 : 0 ≤ q - 130 := by linarith
  have hprod := mul_nonneg hcoef hq0
  unfold gamma
  nlinarith

/-- S54 after S52, S53, and S19 have supplied their respective bounds. -/
lemma s54_finish (d : Local) (n : ℕ) (hnlarge : 130 ≤ n)
    (hq : d.q = n) (hpenalty : min d.FB d.FW ≤
      (d.X + d.Y) / 2 - (d.beta - 2))
    (haverage : ((d.X + d.Y) / 2 : ℝ) ≤ (kappa * (n : ℝ) ^ 2))
    (hbeta : (11 : ℚ) / 25 * d.q ≤ d.beta)
    (hH : kappa * (n : ℝ) ^ 2 - gamma * n - 1 / 4 ≤ (H n : ℝ)) :
    min (d.FB : ℝ) (d.FW : ℝ) ≤ (H n : ℝ) := by
  have hnum := s54_numeric (n : ℝ) (by exact_mod_cast hnlarge)
  have hqR : (d.q : ℝ) = n := by exact_mod_cast hq
  have hpR : (min d.FB d.FW : ℝ) ≤
      ((d.X + d.Y) / 2 - (d.beta - 2) : ℚ) := by exact_mod_cast hpenalty
  have hbR : (11 : ℝ) / 25 * (d.q : ℝ) ≤ d.beta := by
    calc
      (11 : ℝ) / 25 * (d.q : ℝ) = ((11 / 25 * d.q : ℚ) : ℝ) := by
        norm_num
      _ ≤ d.beta := by exact_mod_cast hbeta
  norm_num at hpR hbR
  rw [hqR] at hbR
  have hmargin : gamma * n + 1 / 4 ≤ (d.beta : ℝ) - 2 := by
    nlinarith [hnum, hbR]
  rcases hpR with hpR | hpR
  · apply min_le_iff.mpr
    left
    nlinarith
  · apply min_le_iff.mpr
    right
    nlinarith

/-- S51's integrality step, attached to the actual configuration defects. -/
lemma configuration_zeta_ge_two (cfg : Configuration n) (hq : 0 < n)
    (hcore : (localOfConfiguration cfg).Core)
    (hlarge : (localOfConfiguration cfg).alpha * (localOfConfiguration cfg).delta <
      (localOfConfiguration cfg).Q) :
    (2 : ℚ) ≤ (localOfConfiguration cfg).zeta := by
  have hnonneg := localOfConfiguration_nonnegative cfg hq
  have hqQ : (0 : ℚ) < (localOfConfiguration cfg).q := by
    change (0 : ℚ) < n
    exact_mod_cast hq
  have hgh := gh_pos_of_Q_gt_alpha_delta (localOfConfiguration cfg) hqQ hnonneg hcore hlarge
  have hd0 := outerCount_le cfg hq ⟨.diagonal, 0⟩
  have ha0 := outerCount_le cfg hq ⟨.antidiagonal, 0⟩
  have hg0 : (0 : ℚ) ≤ (n : ℚ) - outerCount cfg ⟨.diagonal, 0⟩ := by
    exact sub_nonneg.mpr (by exact_mod_cast hd0)
  have hh0 : (0 : ℚ) ≤ (n : ℚ) - outerCount cfg ⟨.antidiagonal, 0⟩ := by
    exact sub_nonneg.mpr (by exact_mod_cast ha0)
  have hgpos : 0 < (n : ℚ) - outerCount cfg ⟨.diagonal, 0⟩ := by
    dsimp [localOfConfiguration] at hgh
    nlinarith
  have hhpos : 0 < (n : ℚ) - outerCount cfg ⟨.antidiagonal, 0⟩ := by
    dsimp [localOfConfiguration] at hgh
    nlinarith
  rw [← Nat.cast_sub hd0] at hgpos
  rw [← Nat.cast_sub ha0] at hhpos
  have hgnat : 0 < n - outerCount cfg ⟨.diagonal, 0⟩ := by exact_mod_cast hgpos
  have hhnat : 0 < n - outerCount cfg ⟨.antidiagonal, 0⟩ := by exact_mod_cast hhpos
  have hz := zeta_ge_two_of_natural_defects
    (n - outerCount cfg ⟨.diagonal, 0⟩) (n - outerCount cfg ⟨.antidiagonal, 0⟩)
    (Nat.mul_pos hgnat hhnat)
  rw [Nat.cast_sub hd0, Nat.cast_sub ha0] at hz
  simpa [localOfConfiguration, Local.zeta] using hz

/-- Paper `prop:caseA` and `prop:caseB` (S42--S54) assembled on a genuine
large-order configuration in the checked core and plaid neighbourhood: the
minimum of the two cut bounds is at most `H(2q)`.  Case A (`X ≤ Y`) does not
use `130 ≤ n`; only case B does. -/
lemma configuration_local_finish (cfg : Configuration n) (hq : 0 < n)
    (hnlarge : 130 ≤ n) (hN : InLargeOrderNeighborhood cfg)
    (hcore : LeafChecks.InCore (flatProfile cfg)) :
    min (localOfConfiguration cfg).FB (localOfConfiguration cfg).FW ≤ (H n : ℚ) := by
  let d := localOfConfiguration cfg
  have hdq : d.q = (n : ℚ) := by rfl
  have hdqpos : 0 < d.q := by
    rw [hdq]
    exact_mod_cast hq
  have hnonneg : d.Nonnegative := localOfConfiguration_nonnegative cfg hq
  have hcore' : d.Core := localOfConfiguration_core cfg hq hcore
  have hbasic := d.basic hdqpos hcore'
  have hbeta : 11 / 25 * d.q ≤ d.beta := hbasic.2.1
  have hdelta : d.delta < d.alpha := hbasic.2.2.1
  have hzeta : d.zeta < d.beta := hbasic.2.2.2
  have hXY : min d.X d.Y ≤ (H n : ℚ) := local_min_le_H cfg hq
  by_cases horder : d.X ≤ d.Y
  · by_cases hsmall : d.Q ≤ d.beta * d.zeta
    · calc
        min d.FB d.FW ≤ d.FB := min_le_left _ _
        _ ≤ d.X := by dsimp [Local.FB]; linarith
        _ = min d.X d.Y := (min_eq_left horder).symm
        _ ≤ (H n : ℚ) := hXY
    · have hlarge : d.beta * d.zeta < d.Q := lt_of_not_ge hsmall
      have hzeta0 : 0 ≤ d.zeta := by
        rcases hnonneg with ⟨hu, hR, hv, hC, he, hf, hg, hh⟩
        dsimp [Local.zeta]
        linarith
      have hgh := d.two_gh_le_q_zeta_over_fifty hnonneg hcore'
      have hbetazeta : d.q * d.zeta / 50 ≤ d.beta * d.zeta := by
        have hq0 : 0 ≤ d.q := le_of_lt hdqpos
        have hqz0 : 0 ≤ d.q * d.zeta := mul_nonneg hq0 hzeta0
        have hmul := mul_le_mul_of_nonneg_right hbeta hzeta0
        norm_num at hmul ⊢
        nlinarith
      have hFB : d.FB ≤ d.X + 2 * d.e * d.f :=
        d.FB_le_X_add_two_ef (hgh.trans hbetazeta)
      have haff := d.large_defect_affordable hdqpos hnonneg hcore' hlarge
      rcases s50_switch_exists d hnonneg hFB haff with ⟨x, y, hchoice, hdom⟩
      rcases configuration_switched_profiles_H cfg hq hN with ⟨hp1, hp2, hp3, hp4⟩
      rcases hchoice with hchoice | hchoice | hchoice | hchoice
      · rcases hchoice with ⟨rfl, rfl⟩
        exact hdom.trans hp1
      · rcases hchoice with ⟨rfl, rfl⟩
        exact hdom.trans hp2
      · rcases hchoice with ⟨rfl, rfl⟩
        exact hdom.trans hp3
      · rcases hchoice with ⟨rfl, rfl⟩
        exact hdom.trans hp4
  · have horder' : d.Y ≤ d.X := le_of_not_ge horder
    by_cases hsmall : d.Q ≤ d.alpha * d.delta
    · calc
        min d.FB d.FW ≤ d.FW := min_le_right _ _
        _ ≤ d.Y := by dsimp [Local.FW]; linarith
        _ = min d.X d.Y := (min_eq_right horder').symm
        _ ≤ (H n : ℚ) := hXY
    · have hlarge : d.alpha * d.delta < d.Q := lt_of_not_ge hsmall
      have hzeta2 : (2 : ℚ) ≤ d.zeta :=
        configuration_zeta_ge_two cfg hq hcore' hlarge
      have hq130 : (130 : ℚ) ≤ d.q := by
        rw [hdq]
        exact_mod_cast hnlarge
      have hzetaUpper : d.zeta ≤ 1 / 25 * d.q := hcore'.2.2.2.2
      have hgap : (2 : ℚ) ≤ d.beta - d.zeta := by
        norm_num at hbeta hzetaUpper ⊢
        linarith
      have hpenalty := d.min_FB_FW_le_average_sub_beta_minus_two hnonneg
        (le_of_lt hdelta) (le_of_lt hzeta) hzeta2 hgap
      rcases hnonneg with ⟨hu, hR, hv, hC, he, hf, hg, hh⟩
      rcases local_neighborhood_transport cfg hN with
        ⟨huN, hvN, heN, hfN, hRlo, hRhi, hClo, hChi⟩
      have hdqR : (d.q : ℝ) = (n : ℝ) := by exact_mod_cast hdq
      have hqR : (0 : ℝ) < d.q := by exact_mod_cast hdqpos
      have huR : (0 : ℝ) ≤ d.u := by exact_mod_cast hu
      have hRR : (0 : ℝ) ≤ d.R := by exact_mod_cast hR
      have hvR : (0 : ℝ) ≤ d.v := by exact_mod_cast hv
      have hCR : (0 : ℝ) ≤ d.C := by exact_mod_cast hC
      have huNR : (d.u : ℝ) ≤ d.q / 10 := by exact_mod_cast huN
      have hvNR : (d.v : ℝ) ≤ d.q / 10 := by exact_mod_cast hvN
      have hRhiR : (d.R : ℝ) ≤ 7 * d.q / 8 := by exact_mod_cast hRhi
      have hChiR : (d.C : ℝ) ≤ 7 * d.q / 8 := by exact_mod_cast hChi
      have horderR :
          ((d.q : ℝ) - d.u) * ((d.q : ℝ) - d.C) +
              ((d.q : ℝ) - d.R) * ((d.q : ℝ) - d.v) ≤
            (d.u : ℝ) * d.v + (d.R : ℝ) * d.C := by
        change d.Y ≤ d.X at horder'
        exact_mod_cast horder'
      have haverage' := s53_average_le_kappa (d.q : ℝ) d.u d.R d.v d.C hqR
        huR hRR hvR hCR huNR hvNR hRhiR hChiR horderR
      have haverage : ((d.X + d.Y) / 2 : ℝ) ≤ kappa * (n : ℝ) ^ 2 := by
        rw [← hdqR]
        simpa [Local.X, Local.Y] using haverage'
      have hH := H_lower_s19 n hq
      have hfinish := s54_finish d n hnlarge hdq hpenalty haverage hbeta hH
      exact_mod_cast hfinish

/-- Paper `thm:q130` in configuration form: the two checked support cuts
(`lem:cuts`) attach the local S42--S54 estimate to the actual black/white cell
cardinalities. -/
lemma configuration_finish (cfg : Configuration n) [NeZero (2 * n)] (hq : 0 < n)
    (hnlarge : 130 ≤ n) (hN : InLargeOrderNeighborhood cfg)
    (hcore : LeafChecks.InCore (flatProfile cfg)) :
    min cfg.blackCells.card cfg.whiteCells.card ≤ H n := by
  have h609 := cut609_configuration_scaled cfg hq
  have h559 := cut559_configuration_scaled cfg hq
  have hlocal := configuration_local_finish cfg hq hnlarge hN hcore
  have hcardsQ : (min cfg.blackCells.card cfg.whiteCells.card : ℚ) ≤
      min (localOfConfiguration cfg).FB (localOfConfiguration cfg).FW :=
    le_min h609 h559
  have hQ : (min cfg.blackCells.card cfg.whiteCells.card : ℚ) ≤ (H n : ℚ) :=
    hcardsQ.trans hlocal
  exact_mod_cast hQ

end PeaceableQueens.UpperBound.LargeOrderFinish

#print axioms PeaceableQueens.UpperBound.LargeOrderFinish.cut609_configuration_scaled
#print axioms PeaceableQueens.UpperBound.LargeOrderFinish.cut559_configuration_scaled
#print axioms PeaceableQueens.UpperBound.LargeOrderFinish.local_min_le_H
#print axioms PeaceableQueens.UpperBound.LargeOrderFinish.s50_switch_exists
#print axioms PeaceableQueens.UpperBound.LargeOrderFinish.s53_average_le_kappa
#print axioms PeaceableQueens.UpperBound.LargeOrderFinish.s54_finish
#print axioms PeaceableQueens.UpperBound.LargeOrderFinish.configuration_local_finish
#print axioms PeaceableQueens.UpperBound.LargeOrderFinish.configuration_finish
