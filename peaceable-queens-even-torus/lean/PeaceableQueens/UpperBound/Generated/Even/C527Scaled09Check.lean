import PeaceableQueens.UpperBound.Generated.Even.C527Scaled09Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_09_00_values : List Bool := [accepted_450]
theorem batch_09_00_ok : batch_09_00_values.all id = true := by decide

def batch_09_01_values : List Bool := [accepted_453]
theorem batch_09_01_ok : batch_09_01_values.all id = true := by decide

def batch_09_02_values : List Bool := [accepted_454]
theorem batch_09_02_ok : batch_09_02_values.all id = true := by decide

def batch_09_03_values : List Bool := [accepted_455]
theorem batch_09_03_ok : batch_09_03_values.all id = true := by decide

def batch_09_04_values : List Bool := [accepted_457]
theorem batch_09_04_ok : batch_09_04_values.all id = true := by decide

def batch_09_05_values : List Bool := [accepted_459]
theorem batch_09_05_ok : batch_09_05_values.all id = true := by decide

def batch_09_06_values : List Bool := [accepted_461]
theorem batch_09_06_ok : batch_09_06_values.all id = true := by decide

def batch_09_07_values : List Bool := [accepted_463]
theorem batch_09_07_ok : batch_09_07_values.all id = true := by decide

def batch_09_08_values : List Bool := [accepted_464]
theorem batch_09_08_ok : batch_09_08_values.all id = true := by decide

def batch_09_09_values : List Bool := [accepted_467]
theorem batch_09_09_ok : batch_09_09_values.all id = true := by decide

def batch_09_10_values : List Bool := [accepted_469]
theorem batch_09_10_ok : batch_09_10_values.all id = true := by decide

def batch_09_11_values : List Bool := [accepted_471]
theorem batch_09_11_ok : batch_09_11_values.all id = true := by decide

def batch_09_12_values : List Bool := [accepted_472]
theorem batch_09_12_ok : batch_09_12_values.all id = true := by decide

def batch_09_13_values : List Bool := [accepted_473]
theorem batch_09_13_ok : batch_09_13_values.all id = true := by decide

def batch_09_14_values : List Bool := [accepted_477]
theorem batch_09_14_ok : batch_09_14_values.all id = true := by decide

def batch_09_15_values : List Bool := [accepted_478]
theorem batch_09_15_ok : batch_09_15_values.all id = true := by decide

def batch_09_16_values : List Bool := [accepted_479]
theorem batch_09_16_ok : batch_09_16_values.all id = true := by decide

def batch_09_17_values : List Bool := [accepted_481]
theorem batch_09_17_ok : batch_09_17_values.all id = true := by decide

def batch_09_18_values : List Bool := [accepted_483]
theorem batch_09_18_ok : batch_09_18_values.all id = true := by decide

def batch_09_19_values : List Bool := [accepted_486]
theorem batch_09_19_ok : batch_09_19_values.all id = true := by decide

def batch_09_20_values : List Bool := [accepted_487]
theorem batch_09_20_ok : batch_09_20_values.all id = true := by decide

def batch_09_21_values : List Bool := [accepted_488]
theorem batch_09_21_ok : batch_09_21_values.all id = true := by decide

theorem leaf_450_ok : checkAt 527 1000 box_450 cert_450 = true := by
  have h := List.all_eq_true.mp batch_09_00_ok accepted_450 (by simp [batch_09_00_values])
  exact h
theorem leaf_450_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_450.profileLo box_450.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_450_ok
theorem branch_box_450_nonnegative : ∀ j, 0 ≤ branch_box_450.lower j ∧ 0 ≤ branch_box_450.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_450, Box.profileLo, Box.profileHi, box_450]
theorem leaf_450_BranchSafe : CertificateConsequences.BranchSafe branch_box_450 := by
  left; refine ⟨branch_box_450_nonnegative, ?_⟩
  intro z hz; exact leaf_450_sound hz

theorem leaf_453_ok : checkAt 527 1000 box_453 cert_453 = true := by
  have h := List.all_eq_true.mp batch_09_01_ok accepted_453 (by simp [batch_09_01_values])
  exact h
theorem leaf_453_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_453.profileLo box_453.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_453_ok
theorem branch_box_453_nonnegative : ∀ j, 0 ≤ branch_box_453.lower j ∧ 0 ≤ branch_box_453.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_453, Box.profileLo, Box.profileHi, box_453]
theorem leaf_453_BranchSafe : CertificateConsequences.BranchSafe branch_box_453 := by
  left; refine ⟨branch_box_453_nonnegative, ?_⟩
  intro z hz; exact leaf_453_sound hz

theorem leaf_454_ok : checkAt 527 1000 box_454 cert_454 = true := by
  have h := List.all_eq_true.mp batch_09_02_ok accepted_454 (by simp [batch_09_02_values])
  exact h
theorem leaf_454_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_454.profileLo box_454.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_454_ok
theorem branch_box_454_nonnegative : ∀ j, 0 ≤ branch_box_454.lower j ∧ 0 ≤ branch_box_454.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_454, Box.profileLo, Box.profileHi, box_454]
theorem leaf_454_BranchSafe : CertificateConsequences.BranchSafe branch_box_454 := by
  left; refine ⟨branch_box_454_nonnegative, ?_⟩
  intro z hz; exact leaf_454_sound hz

theorem leaf_455_ok : checkAt 527 1000 box_455 cert_455 = true := by
  have h := List.all_eq_true.mp batch_09_03_ok accepted_455 (by simp [batch_09_03_values])
  exact h
theorem leaf_455_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_455.profileLo box_455.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_455_ok
theorem branch_box_455_nonnegative : ∀ j, 0 ≤ branch_box_455.lower j ∧ 0 ≤ branch_box_455.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_455, Box.profileLo, Box.profileHi, box_455]
theorem leaf_455_BranchSafe : CertificateConsequences.BranchSafe branch_box_455 := by
  left; refine ⟨branch_box_455_nonnegative, ?_⟩
  intro z hz; exact leaf_455_sound hz

theorem leaf_457_ok : checkAt 527 1000 box_457 cert_457 = true := by
  have h := List.all_eq_true.mp batch_09_04_ok accepted_457 (by simp [batch_09_04_values])
  exact h
theorem leaf_457_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_457.profileLo box_457.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_457_ok
theorem branch_box_457_nonnegative : ∀ j, 0 ≤ branch_box_457.lower j ∧ 0 ≤ branch_box_457.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_457, Box.profileLo, Box.profileHi, box_457]
theorem leaf_457_BranchSafe : CertificateConsequences.BranchSafe branch_box_457 := by
  left; refine ⟨branch_box_457_nonnegative, ?_⟩
  intro z hz; exact leaf_457_sound hz

theorem leaf_459_ok : checkAt 527 1000 box_459 cert_459 = true := by
  have h := List.all_eq_true.mp batch_09_05_ok accepted_459 (by simp [batch_09_05_values])
  exact h
theorem leaf_459_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_459.profileLo box_459.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_459_ok
theorem branch_box_459_nonnegative : ∀ j, 0 ≤ branch_box_459.lower j ∧ 0 ≤ branch_box_459.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_459, Box.profileLo, Box.profileHi, box_459]
theorem leaf_459_BranchSafe : CertificateConsequences.BranchSafe branch_box_459 := by
  left; refine ⟨branch_box_459_nonnegative, ?_⟩
  intro z hz; exact leaf_459_sound hz

theorem leaf_461_ok : checkAt 527 1000 box_461 cert_461 = true := by
  have h := List.all_eq_true.mp batch_09_06_ok accepted_461 (by simp [batch_09_06_values])
  exact h
theorem leaf_461_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_461.profileLo box_461.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_461_ok
theorem branch_box_461_nonnegative : ∀ j, 0 ≤ branch_box_461.lower j ∧ 0 ≤ branch_box_461.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_461, Box.profileLo, Box.profileHi, box_461]
theorem leaf_461_BranchSafe : CertificateConsequences.BranchSafe branch_box_461 := by
  left; refine ⟨branch_box_461_nonnegative, ?_⟩
  intro z hz; exact leaf_461_sound hz

theorem leaf_463_ok : checkAt 527 1000 box_463 cert_463 = true := by
  have h := List.all_eq_true.mp batch_09_07_ok accepted_463 (by simp [batch_09_07_values])
  exact h
theorem leaf_463_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_463.profileLo box_463.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_463_ok
theorem branch_box_463_nonnegative : ∀ j, 0 ≤ branch_box_463.lower j ∧ 0 ≤ branch_box_463.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_463, Box.profileLo, Box.profileHi, box_463]
theorem leaf_463_BranchSafe : CertificateConsequences.BranchSafe branch_box_463 := by
  left; refine ⟨branch_box_463_nonnegative, ?_⟩
  intro z hz; exact leaf_463_sound hz

theorem leaf_464_ok : checkAt 527 1000 box_464 cert_464 = true := by
  have h := List.all_eq_true.mp batch_09_08_ok accepted_464 (by simp [batch_09_08_values])
  exact h
theorem leaf_464_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_464.profileLo box_464.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_464_ok
theorem branch_box_464_nonnegative : ∀ j, 0 ≤ branch_box_464.lower j ∧ 0 ≤ branch_box_464.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_464, Box.profileLo, Box.profileHi, box_464]
theorem leaf_464_BranchSafe : CertificateConsequences.BranchSafe branch_box_464 := by
  left; refine ⟨branch_box_464_nonnegative, ?_⟩
  intro z hz; exact leaf_464_sound hz

theorem leaf_467_ok : checkAt 527 1000 box_467 cert_467 = true := by
  have h := List.all_eq_true.mp batch_09_09_ok accepted_467 (by simp [batch_09_09_values])
  exact h
theorem leaf_467_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_467.profileLo box_467.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_467_ok
theorem branch_box_467_nonnegative : ∀ j, 0 ≤ branch_box_467.lower j ∧ 0 ≤ branch_box_467.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_467, Box.profileLo, Box.profileHi, box_467]
theorem leaf_467_BranchSafe : CertificateConsequences.BranchSafe branch_box_467 := by
  left; refine ⟨branch_box_467_nonnegative, ?_⟩
  intro z hz; exact leaf_467_sound hz

theorem leaf_469_ok : checkAt 527 1000 box_469 cert_469 = true := by
  have h := List.all_eq_true.mp batch_09_10_ok accepted_469 (by simp [batch_09_10_values])
  exact h
theorem leaf_469_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_469.profileLo box_469.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_469_ok
theorem branch_box_469_nonnegative : ∀ j, 0 ≤ branch_box_469.lower j ∧ 0 ≤ branch_box_469.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_469, Box.profileLo, Box.profileHi, box_469]
theorem leaf_469_BranchSafe : CertificateConsequences.BranchSafe branch_box_469 := by
  left; refine ⟨branch_box_469_nonnegative, ?_⟩
  intro z hz; exact leaf_469_sound hz

theorem leaf_471_ok : checkAt 527 1000 box_471 cert_471 = true := by
  have h := List.all_eq_true.mp batch_09_11_ok accepted_471 (by simp [batch_09_11_values])
  exact h
theorem leaf_471_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_471.profileLo box_471.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_471_ok
theorem branch_box_471_nonnegative : ∀ j, 0 ≤ branch_box_471.lower j ∧ 0 ≤ branch_box_471.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_471, Box.profileLo, Box.profileHi, box_471]
theorem leaf_471_BranchSafe : CertificateConsequences.BranchSafe branch_box_471 := by
  left; refine ⟨branch_box_471_nonnegative, ?_⟩
  intro z hz; exact leaf_471_sound hz

theorem leaf_472_ok : checkAt 527 1000 box_472 cert_472 = true := by
  have h := List.all_eq_true.mp batch_09_12_ok accepted_472 (by simp [batch_09_12_values])
  exact h
theorem leaf_472_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_472.profileLo box_472.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_472_ok
theorem branch_box_472_nonnegative : ∀ j, 0 ≤ branch_box_472.lower j ∧ 0 ≤ branch_box_472.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_472, Box.profileLo, Box.profileHi, box_472]
theorem leaf_472_BranchSafe : CertificateConsequences.BranchSafe branch_box_472 := by
  left; refine ⟨branch_box_472_nonnegative, ?_⟩
  intro z hz; exact leaf_472_sound hz

theorem leaf_473_ok : checkAt 527 1000 box_473 cert_473 = true := by
  have h := List.all_eq_true.mp batch_09_13_ok accepted_473 (by simp [batch_09_13_values])
  exact h
theorem leaf_473_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_473.profileLo box_473.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_473_ok
theorem branch_box_473_nonnegative : ∀ j, 0 ≤ branch_box_473.lower j ∧ 0 ≤ branch_box_473.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_473, Box.profileLo, Box.profileHi, box_473]
theorem leaf_473_BranchSafe : CertificateConsequences.BranchSafe branch_box_473 := by
  left; refine ⟨branch_box_473_nonnegative, ?_⟩
  intro z hz; exact leaf_473_sound hz

theorem leaf_477_ok : checkAt 527 1000 box_477 cert_477 = true := by
  have h := List.all_eq_true.mp batch_09_14_ok accepted_477 (by simp [batch_09_14_values])
  exact h
theorem leaf_477_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_477.profileLo box_477.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_477_ok
theorem branch_box_477_nonnegative : ∀ j, 0 ≤ branch_box_477.lower j ∧ 0 ≤ branch_box_477.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_477, Box.profileLo, Box.profileHi, box_477]
theorem leaf_477_BranchSafe : CertificateConsequences.BranchSafe branch_box_477 := by
  left; refine ⟨branch_box_477_nonnegative, ?_⟩
  intro z hz; exact leaf_477_sound hz

theorem leaf_478_ok : checkAt 527 1000 box_478 cert_478 = true := by
  have h := List.all_eq_true.mp batch_09_15_ok accepted_478 (by simp [batch_09_15_values])
  exact h
theorem leaf_478_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_478.profileLo box_478.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_478_ok
theorem branch_box_478_nonnegative : ∀ j, 0 ≤ branch_box_478.lower j ∧ 0 ≤ branch_box_478.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_478, Box.profileLo, Box.profileHi, box_478]
theorem leaf_478_BranchSafe : CertificateConsequences.BranchSafe branch_box_478 := by
  left; refine ⟨branch_box_478_nonnegative, ?_⟩
  intro z hz; exact leaf_478_sound hz

theorem leaf_479_ok : checkAt 527 1000 box_479 cert_479 = true := by
  have h := List.all_eq_true.mp batch_09_16_ok accepted_479 (by simp [batch_09_16_values])
  exact h
theorem leaf_479_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_479.profileLo box_479.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_479_ok
theorem branch_box_479_nonnegative : ∀ j, 0 ≤ branch_box_479.lower j ∧ 0 ≤ branch_box_479.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_479, Box.profileLo, Box.profileHi, box_479]
theorem leaf_479_BranchSafe : CertificateConsequences.BranchSafe branch_box_479 := by
  left; refine ⟨branch_box_479_nonnegative, ?_⟩
  intro z hz; exact leaf_479_sound hz

theorem leaf_481_ok : checkAt 527 1000 box_481 cert_481 = true := by
  have h := List.all_eq_true.mp batch_09_17_ok accepted_481 (by simp [batch_09_17_values])
  exact h
theorem leaf_481_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_481.profileLo box_481.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_481_ok
theorem branch_box_481_nonnegative : ∀ j, 0 ≤ branch_box_481.lower j ∧ 0 ≤ branch_box_481.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_481, Box.profileLo, Box.profileHi, box_481]
theorem leaf_481_BranchSafe : CertificateConsequences.BranchSafe branch_box_481 := by
  left; refine ⟨branch_box_481_nonnegative, ?_⟩
  intro z hz; exact leaf_481_sound hz

theorem leaf_483_ok : checkAt 527 1000 box_483 cert_483 = true := by
  have h := List.all_eq_true.mp batch_09_18_ok accepted_483 (by simp [batch_09_18_values])
  exact h
theorem leaf_483_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_483.profileLo box_483.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_483_ok
theorem branch_box_483_nonnegative : ∀ j, 0 ≤ branch_box_483.lower j ∧ 0 ≤ branch_box_483.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_483, Box.profileLo, Box.profileHi, box_483]
theorem leaf_483_BranchSafe : CertificateConsequences.BranchSafe branch_box_483 := by
  left; refine ⟨branch_box_483_nonnegative, ?_⟩
  intro z hz; exact leaf_483_sound hz

theorem leaf_486_ok : checkAt 527 1000 box_486 cert_486 = true := by
  have h := List.all_eq_true.mp batch_09_19_ok accepted_486 (by simp [batch_09_19_values])
  exact h
theorem leaf_486_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_486.profileLo box_486.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_486_ok
theorem branch_box_486_nonnegative : ∀ j, 0 ≤ branch_box_486.lower j ∧ 0 ≤ branch_box_486.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_486, Box.profileLo, Box.profileHi, box_486]
theorem leaf_486_BranchSafe : CertificateConsequences.BranchSafe branch_box_486 := by
  left; refine ⟨branch_box_486_nonnegative, ?_⟩
  intro z hz; exact leaf_486_sound hz

theorem leaf_487_ok : checkAt 527 1000 box_487 cert_487 = true := by
  have h := List.all_eq_true.mp batch_09_20_ok accepted_487 (by simp [batch_09_20_values])
  exact h
theorem leaf_487_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_487.profileLo box_487.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_487_ok
theorem branch_box_487_nonnegative : ∀ j, 0 ≤ branch_box_487.lower j ∧ 0 ≤ branch_box_487.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_487, Box.profileLo, Box.profileHi, box_487]
theorem leaf_487_BranchSafe : CertificateConsequences.BranchSafe branch_box_487 := by
  left; refine ⟨branch_box_487_nonnegative, ?_⟩
  intro z hz; exact leaf_487_sound hz

theorem leaf_488_ok : checkAt 527 1000 box_488 cert_488 = true := by
  have h := List.all_eq_true.mp batch_09_21_ok accepted_488 (by simp [batch_09_21_values])
  exact h
theorem leaf_488_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_488.profileLo box_488.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_488_ok
theorem branch_box_488_nonnegative : ∀ j, 0 ≤ branch_box_488.lower j ∧ 0 ≤ branch_box_488.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_488, Box.profileLo, Box.profileHi, box_488]
theorem leaf_488_BranchSafe : CertificateConsequences.BranchSafe branch_box_488 := by
  left; refine ⟨branch_box_488_nonnegative, ?_⟩
  intro z hz; exact leaf_488_sound hz

#print axioms batch_09_00_ok
#print axioms leaf_450_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
