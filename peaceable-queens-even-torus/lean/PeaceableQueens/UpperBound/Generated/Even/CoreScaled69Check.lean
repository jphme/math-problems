import PeaceableQueens.UpperBound.Generated.Even.CoreScaled69Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_69_00_values : List Bool := [accepted_3454]
theorem batch_69_00_ok : batch_69_00_values.all id = true := by decide

def batch_69_01_values : List Bool := [accepted_3455]
theorem batch_69_01_ok : batch_69_01_values.all id = true := by decide

def batch_69_02_values : List Bool := [accepted_3457]
theorem batch_69_02_ok : batch_69_02_values.all id = true := by decide

def batch_69_03_values : List Bool := [accepted_3459]
theorem batch_69_03_ok : batch_69_03_values.all id = true := by decide

def batch_69_04_values : List Bool := [accepted_3462]
theorem batch_69_04_ok : batch_69_04_values.all id = true := by decide

def batch_69_05_values : List Bool := [accepted_3463]
theorem batch_69_05_ok : batch_69_05_values.all id = true := by decide

def batch_69_06_values : List Bool := [accepted_3465]
theorem batch_69_06_ok : batch_69_06_values.all id = true := by decide

def batch_69_07_values : List Bool := [accepted_3467]
theorem batch_69_07_ok : batch_69_07_values.all id = true := by decide

def batch_69_08_values : List Bool := [accepted_3474]
theorem batch_69_08_ok : batch_69_08_values.all id = true := by decide

def batch_69_09_values : List Bool := [accepted_3478]
theorem batch_69_09_ok : batch_69_09_values.all id = true := by decide

def batch_69_10_values : List Bool := [accepted_3480]
theorem batch_69_10_ok : batch_69_10_values.all id = true := by decide

def batch_69_11_values : List Bool := [accepted_3482]
theorem batch_69_11_ok : batch_69_11_values.all id = true := by decide

def batch_69_12_values : List Bool := [accepted_3484]
theorem batch_69_12_ok : batch_69_12_values.all id = true := by decide

def batch_69_13_values : List Bool := [accepted_3488]
theorem batch_69_13_ok : batch_69_13_values.all id = true := by decide

def batch_69_14_values : List Bool := [accepted_3491]
theorem batch_69_14_ok : batch_69_14_values.all id = true := by decide

def batch_69_15_values : List Bool := [accepted_3496]
theorem batch_69_15_ok : batch_69_15_values.all id = true := by decide

def batch_69_16_values : List Bool := [accepted_3497]
theorem batch_69_16_ok : batch_69_16_values.all id = true := by decide

theorem leaf_3454_ok : checkAt 527 1000 box_3454 cert_3454 = true := by
  have h := List.all_eq_true.mp batch_69_00_ok accepted_3454 (by simp [batch_69_00_values])
  exact h
theorem leaf_3454_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3454.profileLo box_3454.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3454_ok
theorem branch_box_3454_nonnegative : ∀ j, 0 ≤ branch_box_3454.lower j ∧ 0 ≤ branch_box_3454.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3454, Box.profileLo, Box.profileHi, box_3454]
theorem leaf_3454_BranchSafe : CertificateConsequences.BranchSafe branch_box_3454 := by
  left; refine ⟨branch_box_3454_nonnegative, ?_⟩
  intro z hz; exact leaf_3454_sound hz

theorem leaf_3455_ok : checkAt 527 1000 box_3455 cert_3455 = true := by
  have h := List.all_eq_true.mp batch_69_01_ok accepted_3455 (by simp [batch_69_01_values])
  exact h
theorem leaf_3455_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3455.profileLo box_3455.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3455_ok
theorem branch_box_3455_nonnegative : ∀ j, 0 ≤ branch_box_3455.lower j ∧ 0 ≤ branch_box_3455.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3455, Box.profileLo, Box.profileHi, box_3455]
theorem leaf_3455_BranchSafe : CertificateConsequences.BranchSafe branch_box_3455 := by
  left; refine ⟨branch_box_3455_nonnegative, ?_⟩
  intro z hz; exact leaf_3455_sound hz

theorem leaf_3457_ok : checkAt 527 1000 box_3457 cert_3457 = true := by
  have h := List.all_eq_true.mp batch_69_02_ok accepted_3457 (by simp [batch_69_02_values])
  exact h
theorem leaf_3457_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3457.profileLo box_3457.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3457_ok
theorem branch_box_3457_nonnegative : ∀ j, 0 ≤ branch_box_3457.lower j ∧ 0 ≤ branch_box_3457.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3457, Box.profileLo, Box.profileHi, box_3457]
theorem leaf_3457_BranchSafe : CertificateConsequences.BranchSafe branch_box_3457 := by
  left; refine ⟨branch_box_3457_nonnegative, ?_⟩
  intro z hz; exact leaf_3457_sound hz

theorem leaf_3459_ok : checkAt 527 1000 box_3459 cert_3459 = true := by
  have h := List.all_eq_true.mp batch_69_03_ok accepted_3459 (by simp [batch_69_03_values])
  exact h
theorem leaf_3459_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3459.profileLo box_3459.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3459_ok
theorem branch_box_3459_nonnegative : ∀ j, 0 ≤ branch_box_3459.lower j ∧ 0 ≤ branch_box_3459.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3459, Box.profileLo, Box.profileHi, box_3459]
theorem leaf_3459_BranchSafe : CertificateConsequences.BranchSafe branch_box_3459 := by
  left; refine ⟨branch_box_3459_nonnegative, ?_⟩
  intro z hz; exact leaf_3459_sound hz

theorem leaf_3462_ok : checkAt 527 1000 box_3462 cert_3462 = true := by
  have h := List.all_eq_true.mp batch_69_04_ok accepted_3462 (by simp [batch_69_04_values])
  exact h
theorem leaf_3462_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3462.profileLo box_3462.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3462_ok
theorem branch_box_3462_nonnegative : ∀ j, 0 ≤ branch_box_3462.lower j ∧ 0 ≤ branch_box_3462.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3462, Box.profileLo, Box.profileHi, box_3462]
theorem leaf_3462_BranchSafe : CertificateConsequences.BranchSafe branch_box_3462 := by
  left; refine ⟨branch_box_3462_nonnegative, ?_⟩
  intro z hz; exact leaf_3462_sound hz

theorem leaf_3463_ok : checkAt 527 1000 box_3463 cert_3463 = true := by
  have h := List.all_eq_true.mp batch_69_05_ok accepted_3463 (by simp [batch_69_05_values])
  exact h
theorem leaf_3463_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3463.profileLo box_3463.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3463_ok
theorem branch_box_3463_nonnegative : ∀ j, 0 ≤ branch_box_3463.lower j ∧ 0 ≤ branch_box_3463.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3463, Box.profileLo, Box.profileHi, box_3463]
theorem leaf_3463_BranchSafe : CertificateConsequences.BranchSafe branch_box_3463 := by
  left; refine ⟨branch_box_3463_nonnegative, ?_⟩
  intro z hz; exact leaf_3463_sound hz

theorem leaf_3465_ok : checkAt 527 1000 box_3465 cert_3465 = true := by
  have h := List.all_eq_true.mp batch_69_06_ok accepted_3465 (by simp [batch_69_06_values])
  exact h
theorem leaf_3465_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3465.profileLo box_3465.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3465_ok
theorem branch_box_3465_nonnegative : ∀ j, 0 ≤ branch_box_3465.lower j ∧ 0 ≤ branch_box_3465.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3465, Box.profileLo, Box.profileHi, box_3465]
theorem leaf_3465_BranchSafe : CertificateConsequences.BranchSafe branch_box_3465 := by
  left; refine ⟨branch_box_3465_nonnegative, ?_⟩
  intro z hz; exact leaf_3465_sound hz

theorem leaf_3467_ok : checkAt 527 1000 box_3467 cert_3467 = true := by
  have h := List.all_eq_true.mp batch_69_07_ok accepted_3467 (by simp [batch_69_07_values])
  exact h
theorem leaf_3467_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3467.profileLo box_3467.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3467_ok
theorem branch_box_3467_nonnegative : ∀ j, 0 ≤ branch_box_3467.lower j ∧ 0 ≤ branch_box_3467.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3467, Box.profileLo, Box.profileHi, box_3467]
theorem leaf_3467_BranchSafe : CertificateConsequences.BranchSafe branch_box_3467 := by
  left; refine ⟨branch_box_3467_nonnegative, ?_⟩
  intro z hz; exact leaf_3467_sound hz

theorem leaf_3474_ok : checkAt 527 1000 box_3474 cert_3474 = true := by
  have h := List.all_eq_true.mp batch_69_08_ok accepted_3474 (by simp [batch_69_08_values])
  exact h
theorem leaf_3474_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3474.profileLo box_3474.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3474_ok
theorem branch_box_3474_nonnegative : ∀ j, 0 ≤ branch_box_3474.lower j ∧ 0 ≤ branch_box_3474.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3474, Box.profileLo, Box.profileHi, box_3474]
theorem leaf_3474_BranchSafe : CertificateConsequences.BranchSafe branch_box_3474 := by
  left; refine ⟨branch_box_3474_nonnegative, ?_⟩
  intro z hz; exact leaf_3474_sound hz

theorem leaf_3478_ok : checkAt 527 1000 box_3478 cert_3478 = true := by
  have h := List.all_eq_true.mp batch_69_09_ok accepted_3478 (by simp [batch_69_09_values])
  exact h
theorem leaf_3478_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3478.profileLo box_3478.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3478_ok
theorem branch_box_3478_nonnegative : ∀ j, 0 ≤ branch_box_3478.lower j ∧ 0 ≤ branch_box_3478.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3478, Box.profileLo, Box.profileHi, box_3478]
theorem leaf_3478_BranchSafe : CertificateConsequences.BranchSafe branch_box_3478 := by
  left; refine ⟨branch_box_3478_nonnegative, ?_⟩
  intro z hz; exact leaf_3478_sound hz

theorem leaf_3480_ok : checkAt 527 1000 box_3480 cert_3480 = true := by
  have h := List.all_eq_true.mp batch_69_10_ok accepted_3480 (by simp [batch_69_10_values])
  exact h
theorem leaf_3480_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3480.profileLo box_3480.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3480_ok
theorem branch_box_3480_nonnegative : ∀ j, 0 ≤ branch_box_3480.lower j ∧ 0 ≤ branch_box_3480.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3480, Box.profileLo, Box.profileHi, box_3480]
theorem leaf_3480_BranchSafe : CertificateConsequences.BranchSafe branch_box_3480 := by
  left; refine ⟨branch_box_3480_nonnegative, ?_⟩
  intro z hz; exact leaf_3480_sound hz

theorem leaf_3482_ok : checkAt 527 1000 box_3482 cert_3482 = true := by
  have h := List.all_eq_true.mp batch_69_11_ok accepted_3482 (by simp [batch_69_11_values])
  exact h
theorem leaf_3482_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3482.profileLo box_3482.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3482_ok
theorem branch_box_3482_nonnegative : ∀ j, 0 ≤ branch_box_3482.lower j ∧ 0 ≤ branch_box_3482.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3482, Box.profileLo, Box.profileHi, box_3482]
theorem leaf_3482_BranchSafe : CertificateConsequences.BranchSafe branch_box_3482 := by
  left; refine ⟨branch_box_3482_nonnegative, ?_⟩
  intro z hz; exact leaf_3482_sound hz

theorem leaf_3484_ok : checkAt 527 1000 box_3484 cert_3484 = true := by
  have h := List.all_eq_true.mp batch_69_12_ok accepted_3484 (by simp [batch_69_12_values])
  exact h
theorem leaf_3484_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3484.profileLo box_3484.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3484_ok
theorem branch_box_3484_nonnegative : ∀ j, 0 ≤ branch_box_3484.lower j ∧ 0 ≤ branch_box_3484.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3484, Box.profileLo, Box.profileHi, box_3484]
theorem leaf_3484_BranchSafe : CertificateConsequences.BranchSafe branch_box_3484 := by
  left; refine ⟨branch_box_3484_nonnegative, ?_⟩
  intro z hz; exact leaf_3484_sound hz

theorem leaf_3488_ok : checkAt 527 1000 box_3488 cert_3488 = true := by
  have h := List.all_eq_true.mp batch_69_13_ok accepted_3488 (by simp [batch_69_13_values])
  exact h
theorem leaf_3488_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3488.profileLo box_3488.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3488_ok
theorem branch_box_3488_nonnegative : ∀ j, 0 ≤ branch_box_3488.lower j ∧ 0 ≤ branch_box_3488.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3488, Box.profileLo, Box.profileHi, box_3488]
theorem leaf_3488_BranchSafe : CertificateConsequences.BranchSafe branch_box_3488 := by
  left; refine ⟨branch_box_3488_nonnegative, ?_⟩
  intro z hz; exact leaf_3488_sound hz

theorem leaf_3491_ok : checkAt 527 1000 box_3491 cert_3491 = true := by
  have h := List.all_eq_true.mp batch_69_14_ok accepted_3491 (by simp [batch_69_14_values])
  exact h
theorem leaf_3491_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3491.profileLo box_3491.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3491_ok
theorem branch_box_3491_nonnegative : ∀ j, 0 ≤ branch_box_3491.lower j ∧ 0 ≤ branch_box_3491.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3491, Box.profileLo, Box.profileHi, box_3491]
theorem leaf_3491_BranchSafe : CertificateConsequences.BranchSafe branch_box_3491 := by
  left; refine ⟨branch_box_3491_nonnegative, ?_⟩
  intro z hz; exact leaf_3491_sound hz

theorem leaf_3496_ok : checkAt 527 1000 box_3496 cert_3496 = true := by
  have h := List.all_eq_true.mp batch_69_15_ok accepted_3496 (by simp [batch_69_15_values])
  exact h
theorem leaf_3496_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3496.profileLo box_3496.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3496_ok
theorem branch_box_3496_nonnegative : ∀ j, 0 ≤ branch_box_3496.lower j ∧ 0 ≤ branch_box_3496.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3496, Box.profileLo, Box.profileHi, box_3496]
theorem leaf_3496_BranchSafe : CertificateConsequences.BranchSafe branch_box_3496 := by
  left; refine ⟨branch_box_3496_nonnegative, ?_⟩
  intro z hz; exact leaf_3496_sound hz

theorem leaf_3497_ok : checkAt 527 1000 box_3497 cert_3497 = true := by
  have h := List.all_eq_true.mp batch_69_16_ok accepted_3497 (by simp [batch_69_16_values])
  exact h
theorem leaf_3497_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3497.profileLo box_3497.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3497_ok
theorem branch_box_3497_nonnegative : ∀ j, 0 ≤ branch_box_3497.lower j ∧ 0 ≤ branch_box_3497.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3497, Box.profileLo, Box.profileHi, box_3497]
theorem leaf_3497_BranchSafe : CertificateConsequences.BranchSafe branch_box_3497 := by
  left; refine ⟨branch_box_3497_nonnegative, ?_⟩
  intro z hz; exact leaf_3497_sound hz

#print axioms batch_69_00_ok
#print axioms leaf_3454_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
