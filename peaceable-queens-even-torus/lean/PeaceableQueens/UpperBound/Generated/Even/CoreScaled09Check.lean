import PeaceableQueens.UpperBound.Generated.Even.CoreScaled09Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_09_00_values : List Bool := [accepted_454]
theorem batch_09_00_ok : batch_09_00_values.all id = true := by decide

def batch_09_01_values : List Bool := [accepted_456]
theorem batch_09_01_ok : batch_09_01_values.all id = true := by decide

def batch_09_02_values : List Bool := [accepted_460]
theorem batch_09_02_ok : batch_09_02_values.all id = true := by decide

def batch_09_03_values : List Bool := [accepted_462]
theorem batch_09_03_ok : batch_09_03_values.all id = true := by decide

def batch_09_04_values : List Bool := [accepted_470]
theorem batch_09_04_ok : batch_09_04_values.all id = true := by decide

def batch_09_05_values : List Bool := [accepted_472]
theorem batch_09_05_ok : batch_09_05_values.all id = true := by decide

def batch_09_06_values : List Bool := [accepted_474]
theorem batch_09_06_ok : batch_09_06_values.all id = true := by decide

def batch_09_07_values : List Bool := [accepted_476]
theorem batch_09_07_ok : batch_09_07_values.all id = true := by decide

def batch_09_08_values : List Bool := [accepted_478]
theorem batch_09_08_ok : batch_09_08_values.all id = true := by decide

def batch_09_09_values : List Bool := [accepted_479]
theorem batch_09_09_ok : batch_09_09_values.all id = true := by decide

def batch_09_10_values : List Bool := [accepted_481]
theorem batch_09_10_ok : batch_09_10_values.all id = true := by decide

def batch_09_11_values : List Bool := [accepted_488]
theorem batch_09_11_ok : batch_09_11_values.all id = true := by decide

def batch_09_12_values : List Bool := [accepted_490]
theorem batch_09_12_ok : batch_09_12_values.all id = true := by decide

def batch_09_13_values : List Bool := [accepted_491]
theorem batch_09_13_ok : batch_09_13_values.all id = true := by decide

def batch_09_14_values : List Bool := [accepted_493]
theorem batch_09_14_ok : batch_09_14_values.all id = true := by decide

def batch_09_15_values : List Bool := [accepted_497]
theorem batch_09_15_ok : batch_09_15_values.all id = true := by decide

theorem leaf_454_ok : checkAt 527 1000 box_454 cert_454 = true := by
  have h := List.all_eq_true.mp batch_09_00_ok accepted_454 (by simp [batch_09_00_values])
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

theorem leaf_456_ok : checkAt 527 1000 box_456 cert_456 = true := by
  have h := List.all_eq_true.mp batch_09_01_ok accepted_456 (by simp [batch_09_01_values])
  exact h
theorem leaf_456_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_456.profileLo box_456.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_456_ok
theorem branch_box_456_nonnegative : ∀ j, 0 ≤ branch_box_456.lower j ∧ 0 ≤ branch_box_456.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_456, Box.profileLo, Box.profileHi, box_456]
theorem leaf_456_BranchSafe : CertificateConsequences.BranchSafe branch_box_456 := by
  left; refine ⟨branch_box_456_nonnegative, ?_⟩
  intro z hz; exact leaf_456_sound hz

theorem leaf_460_ok : checkAt 527 1000 box_460 cert_460 = true := by
  have h := List.all_eq_true.mp batch_09_02_ok accepted_460 (by simp [batch_09_02_values])
  exact h
theorem leaf_460_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_460.profileLo box_460.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_460_ok
theorem branch_box_460_nonnegative : ∀ j, 0 ≤ branch_box_460.lower j ∧ 0 ≤ branch_box_460.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_460, Box.profileLo, Box.profileHi, box_460]
theorem leaf_460_BranchSafe : CertificateConsequences.BranchSafe branch_box_460 := by
  left; refine ⟨branch_box_460_nonnegative, ?_⟩
  intro z hz; exact leaf_460_sound hz

theorem leaf_462_ok : checkAt 527 1000 box_462 cert_462 = true := by
  have h := List.all_eq_true.mp batch_09_03_ok accepted_462 (by simp [batch_09_03_values])
  exact h
theorem leaf_462_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_462.profileLo box_462.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_462_ok
theorem branch_box_462_nonnegative : ∀ j, 0 ≤ branch_box_462.lower j ∧ 0 ≤ branch_box_462.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_462, Box.profileLo, Box.profileHi, box_462]
theorem leaf_462_BranchSafe : CertificateConsequences.BranchSafe branch_box_462 := by
  left; refine ⟨branch_box_462_nonnegative, ?_⟩
  intro z hz; exact leaf_462_sound hz

theorem leaf_470_ok : checkAt 527 1000 box_470 cert_470 = true := by
  have h := List.all_eq_true.mp batch_09_04_ok accepted_470 (by simp [batch_09_04_values])
  exact h
theorem leaf_470_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_470.profileLo box_470.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_470_ok
theorem branch_box_470_nonnegative : ∀ j, 0 ≤ branch_box_470.lower j ∧ 0 ≤ branch_box_470.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_470, Box.profileLo, Box.profileHi, box_470]
theorem leaf_470_BranchSafe : CertificateConsequences.BranchSafe branch_box_470 := by
  left; refine ⟨branch_box_470_nonnegative, ?_⟩
  intro z hz; exact leaf_470_sound hz

theorem leaf_472_ok : checkAt 527 1000 box_472 cert_472 = true := by
  have h := List.all_eq_true.mp batch_09_05_ok accepted_472 (by simp [batch_09_05_values])
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

theorem leaf_474_ok : checkAt 527 1000 box_474 cert_474 = true := by
  have h := List.all_eq_true.mp batch_09_06_ok accepted_474 (by simp [batch_09_06_values])
  exact h
theorem leaf_474_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_474.profileLo box_474.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_474_ok
theorem branch_box_474_nonnegative : ∀ j, 0 ≤ branch_box_474.lower j ∧ 0 ≤ branch_box_474.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_474, Box.profileLo, Box.profileHi, box_474]
theorem leaf_474_BranchSafe : CertificateConsequences.BranchSafe branch_box_474 := by
  left; refine ⟨branch_box_474_nonnegative, ?_⟩
  intro z hz; exact leaf_474_sound hz

theorem leaf_476_ok : checkAt 527 1000 box_476 cert_476 = true := by
  have h := List.all_eq_true.mp batch_09_07_ok accepted_476 (by simp [batch_09_07_values])
  exact h
theorem leaf_476_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_476.profileLo box_476.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_476_ok
theorem branch_box_476_nonnegative : ∀ j, 0 ≤ branch_box_476.lower j ∧ 0 ≤ branch_box_476.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_476, Box.profileLo, Box.profileHi, box_476]
theorem leaf_476_BranchSafe : CertificateConsequences.BranchSafe branch_box_476 := by
  left; refine ⟨branch_box_476_nonnegative, ?_⟩
  intro z hz; exact leaf_476_sound hz

theorem leaf_478_ok : checkAt 527 1000 box_478 cert_478 = true := by
  have h := List.all_eq_true.mp batch_09_08_ok accepted_478 (by simp [batch_09_08_values])
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
  have h := List.all_eq_true.mp batch_09_09_ok accepted_479 (by simp [batch_09_09_values])
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
  have h := List.all_eq_true.mp batch_09_10_ok accepted_481 (by simp [batch_09_10_values])
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

theorem leaf_488_ok : checkAt 527 1000 box_488 cert_488 = true := by
  have h := List.all_eq_true.mp batch_09_11_ok accepted_488 (by simp [batch_09_11_values])
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

theorem leaf_490_ok : checkAt 527 1000 box_490 cert_490 = true := by
  have h := List.all_eq_true.mp batch_09_12_ok accepted_490 (by simp [batch_09_12_values])
  exact h
theorem leaf_490_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_490.profileLo box_490.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_490_ok
theorem branch_box_490_nonnegative : ∀ j, 0 ≤ branch_box_490.lower j ∧ 0 ≤ branch_box_490.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_490, Box.profileLo, Box.profileHi, box_490]
theorem leaf_490_BranchSafe : CertificateConsequences.BranchSafe branch_box_490 := by
  left; refine ⟨branch_box_490_nonnegative, ?_⟩
  intro z hz; exact leaf_490_sound hz

theorem leaf_491_ok : checkAt 527 1000 box_491 cert_491 = true := by
  have h := List.all_eq_true.mp batch_09_13_ok accepted_491 (by simp [batch_09_13_values])
  exact h
theorem leaf_491_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_491.profileLo box_491.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_491_ok
theorem branch_box_491_nonnegative : ∀ j, 0 ≤ branch_box_491.lower j ∧ 0 ≤ branch_box_491.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_491, Box.profileLo, Box.profileHi, box_491]
theorem leaf_491_BranchSafe : CertificateConsequences.BranchSafe branch_box_491 := by
  left; refine ⟨branch_box_491_nonnegative, ?_⟩
  intro z hz; exact leaf_491_sound hz

theorem leaf_493_ok : checkAt 527 1000 box_493 cert_493 = true := by
  have h := List.all_eq_true.mp batch_09_14_ok accepted_493 (by simp [batch_09_14_values])
  exact h
theorem leaf_493_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_493.profileLo box_493.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_493_ok
theorem branch_box_493_nonnegative : ∀ j, 0 ≤ branch_box_493.lower j ∧ 0 ≤ branch_box_493.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_493, Box.profileLo, Box.profileHi, box_493]
theorem leaf_493_BranchSafe : CertificateConsequences.BranchSafe branch_box_493 := by
  left; refine ⟨branch_box_493_nonnegative, ?_⟩
  intro z hz; exact leaf_493_sound hz

theorem leaf_497_ok : checkAt 527 1000 box_497 cert_497 = true := by
  have h := List.all_eq_true.mp batch_09_15_ok accepted_497 (by simp [batch_09_15_values])
  exact h
theorem leaf_497_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_497.profileLo box_497.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_497_ok
theorem branch_box_497_nonnegative : ∀ j, 0 ≤ branch_box_497.lower j ∧ 0 ≤ branch_box_497.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_497, Box.profileLo, Box.profileHi, box_497]
theorem leaf_497_BranchSafe : CertificateConsequences.BranchSafe branch_box_497 := by
  left; refine ⟨branch_box_497_nonnegative, ?_⟩
  intro z hz; exact leaf_497_sound hz

#print axioms batch_09_00_ok
#print axioms leaf_454_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
