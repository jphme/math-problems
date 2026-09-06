import PeaceableQueens.UpperBound.Generated.Even.CoreScaled71Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_71_00_values : List Bool := [accepted_3550]
theorem batch_71_00_ok : batch_71_00_values.all id = true := by decide

def batch_71_01_values : List Bool := [accepted_3552]
theorem batch_71_01_ok : batch_71_01_values.all id = true := by decide

def batch_71_02_values : List Bool := [accepted_3553]
theorem batch_71_02_ok : batch_71_02_values.all id = true := by decide

def batch_71_03_values : List Bool := [accepted_3555]
theorem batch_71_03_ok : batch_71_03_values.all id = true := by decide

def batch_71_04_values : List Bool := [accepted_3557]
theorem batch_71_04_ok : batch_71_04_values.all id = true := by decide

def batch_71_05_values : List Bool := [accepted_3566]
theorem batch_71_05_ok : batch_71_05_values.all id = true := by decide

def batch_71_06_values : List Bool := [accepted_3568]
theorem batch_71_06_ok : batch_71_06_values.all id = true := by decide

def batch_71_07_values : List Bool := [accepted_3570]
theorem batch_71_07_ok : batch_71_07_values.all id = true := by decide

def batch_71_08_values : List Bool := [accepted_3572]
theorem batch_71_08_ok : batch_71_08_values.all id = true := by decide

def batch_71_09_values : List Bool := [accepted_3578]
theorem batch_71_09_ok : batch_71_09_values.all id = true := by decide

def batch_71_10_values : List Bool := [accepted_3580]
theorem batch_71_10_ok : batch_71_10_values.all id = true := by decide

def batch_71_11_values : List Bool := [accepted_3582]
theorem batch_71_11_ok : batch_71_11_values.all id = true := by decide

def batch_71_12_values : List Bool := [accepted_3584]
theorem batch_71_12_ok : batch_71_12_values.all id = true := by decide

def batch_71_13_values : List Bool := [accepted_3586]
theorem batch_71_13_ok : batch_71_13_values.all id = true := by decide

def batch_71_14_values : List Bool := [accepted_3588]
theorem batch_71_14_ok : batch_71_14_values.all id = true := by decide

def batch_71_15_values : List Bool := [accepted_3589]
theorem batch_71_15_ok : batch_71_15_values.all id = true := by decide

def batch_71_16_values : List Bool := [accepted_3596]
theorem batch_71_16_ok : batch_71_16_values.all id = true := by decide

def batch_71_17_values : List Bool := [accepted_3598]
theorem batch_71_17_ok : batch_71_17_values.all id = true := by decide

theorem leaf_3550_ok : checkAt 527 1000 box_3550 cert_3550 = true := by
  have h := List.all_eq_true.mp batch_71_00_ok accepted_3550 (by simp [batch_71_00_values])
  exact h
theorem leaf_3550_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3550.profileLo box_3550.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3550_ok
theorem branch_box_3550_nonnegative : ∀ j, 0 ≤ branch_box_3550.lower j ∧ 0 ≤ branch_box_3550.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3550, Box.profileLo, Box.profileHi, box_3550]
theorem leaf_3550_BranchSafe : CertificateConsequences.BranchSafe branch_box_3550 := by
  left; refine ⟨branch_box_3550_nonnegative, ?_⟩
  intro z hz; exact leaf_3550_sound hz

theorem leaf_3552_ok : checkAt 527 1000 box_3552 cert_3552 = true := by
  have h := List.all_eq_true.mp batch_71_01_ok accepted_3552 (by simp [batch_71_01_values])
  exact h
theorem leaf_3552_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3552.profileLo box_3552.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3552_ok
theorem branch_box_3552_nonnegative : ∀ j, 0 ≤ branch_box_3552.lower j ∧ 0 ≤ branch_box_3552.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3552, Box.profileLo, Box.profileHi, box_3552]
theorem leaf_3552_BranchSafe : CertificateConsequences.BranchSafe branch_box_3552 := by
  left; refine ⟨branch_box_3552_nonnegative, ?_⟩
  intro z hz; exact leaf_3552_sound hz

theorem leaf_3553_ok : checkAt 527 1000 box_3553 cert_3553 = true := by
  have h := List.all_eq_true.mp batch_71_02_ok accepted_3553 (by simp [batch_71_02_values])
  exact h
theorem leaf_3553_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3553.profileLo box_3553.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3553_ok
theorem branch_box_3553_nonnegative : ∀ j, 0 ≤ branch_box_3553.lower j ∧ 0 ≤ branch_box_3553.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3553, Box.profileLo, Box.profileHi, box_3553]
theorem leaf_3553_BranchSafe : CertificateConsequences.BranchSafe branch_box_3553 := by
  left; refine ⟨branch_box_3553_nonnegative, ?_⟩
  intro z hz; exact leaf_3553_sound hz

theorem leaf_3555_ok : checkAt 527 1000 box_3555 cert_3555 = true := by
  have h := List.all_eq_true.mp batch_71_03_ok accepted_3555 (by simp [batch_71_03_values])
  exact h
theorem leaf_3555_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3555.profileLo box_3555.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3555_ok
theorem branch_box_3555_nonnegative : ∀ j, 0 ≤ branch_box_3555.lower j ∧ 0 ≤ branch_box_3555.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3555, Box.profileLo, Box.profileHi, box_3555]
theorem leaf_3555_BranchSafe : CertificateConsequences.BranchSafe branch_box_3555 := by
  left; refine ⟨branch_box_3555_nonnegative, ?_⟩
  intro z hz; exact leaf_3555_sound hz

theorem leaf_3557_ok : checkAt 527 1000 box_3557 cert_3557 = true := by
  have h := List.all_eq_true.mp batch_71_04_ok accepted_3557 (by simp [batch_71_04_values])
  exact h
theorem leaf_3557_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3557.profileLo box_3557.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3557_ok
theorem branch_box_3557_nonnegative : ∀ j, 0 ≤ branch_box_3557.lower j ∧ 0 ≤ branch_box_3557.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3557, Box.profileLo, Box.profileHi, box_3557]
theorem leaf_3557_BranchSafe : CertificateConsequences.BranchSafe branch_box_3557 := by
  left; refine ⟨branch_box_3557_nonnegative, ?_⟩
  intro z hz; exact leaf_3557_sound hz

theorem leaf_3566_ok : checkAt 527 1000 box_3566 cert_3566 = true := by
  have h := List.all_eq_true.mp batch_71_05_ok accepted_3566 (by simp [batch_71_05_values])
  exact h
theorem leaf_3566_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3566.profileLo box_3566.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3566_ok
theorem branch_box_3566_nonnegative : ∀ j, 0 ≤ branch_box_3566.lower j ∧ 0 ≤ branch_box_3566.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3566, Box.profileLo, Box.profileHi, box_3566]
theorem leaf_3566_BranchSafe : CertificateConsequences.BranchSafe branch_box_3566 := by
  left; refine ⟨branch_box_3566_nonnegative, ?_⟩
  intro z hz; exact leaf_3566_sound hz

theorem leaf_3568_ok : checkAt 527 1000 box_3568 cert_3568 = true := by
  have h := List.all_eq_true.mp batch_71_06_ok accepted_3568 (by simp [batch_71_06_values])
  exact h
theorem leaf_3568_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3568.profileLo box_3568.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3568_ok
theorem branch_box_3568_nonnegative : ∀ j, 0 ≤ branch_box_3568.lower j ∧ 0 ≤ branch_box_3568.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3568, Box.profileLo, Box.profileHi, box_3568]
theorem leaf_3568_BranchSafe : CertificateConsequences.BranchSafe branch_box_3568 := by
  left; refine ⟨branch_box_3568_nonnegative, ?_⟩
  intro z hz; exact leaf_3568_sound hz

theorem leaf_3570_ok : checkAt 527 1000 box_3570 cert_3570 = true := by
  have h := List.all_eq_true.mp batch_71_07_ok accepted_3570 (by simp [batch_71_07_values])
  exact h
theorem leaf_3570_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3570.profileLo box_3570.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3570_ok
theorem branch_box_3570_nonnegative : ∀ j, 0 ≤ branch_box_3570.lower j ∧ 0 ≤ branch_box_3570.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3570, Box.profileLo, Box.profileHi, box_3570]
theorem leaf_3570_BranchSafe : CertificateConsequences.BranchSafe branch_box_3570 := by
  left; refine ⟨branch_box_3570_nonnegative, ?_⟩
  intro z hz; exact leaf_3570_sound hz

theorem leaf_3572_ok : checkAt 527 1000 box_3572 cert_3572 = true := by
  have h := List.all_eq_true.mp batch_71_08_ok accepted_3572 (by simp [batch_71_08_values])
  exact h
theorem leaf_3572_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3572.profileLo box_3572.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3572_ok
theorem branch_box_3572_nonnegative : ∀ j, 0 ≤ branch_box_3572.lower j ∧ 0 ≤ branch_box_3572.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3572, Box.profileLo, Box.profileHi, box_3572]
theorem leaf_3572_BranchSafe : CertificateConsequences.BranchSafe branch_box_3572 := by
  left; refine ⟨branch_box_3572_nonnegative, ?_⟩
  intro z hz; exact leaf_3572_sound hz

theorem leaf_3578_ok : checkAt 527 1000 box_3578 cert_3578 = true := by
  have h := List.all_eq_true.mp batch_71_09_ok accepted_3578 (by simp [batch_71_09_values])
  exact h
theorem leaf_3578_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3578.profileLo box_3578.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3578_ok
theorem branch_box_3578_nonnegative : ∀ j, 0 ≤ branch_box_3578.lower j ∧ 0 ≤ branch_box_3578.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3578, Box.profileLo, Box.profileHi, box_3578]
theorem leaf_3578_BranchSafe : CertificateConsequences.BranchSafe branch_box_3578 := by
  left; refine ⟨branch_box_3578_nonnegative, ?_⟩
  intro z hz; exact leaf_3578_sound hz

theorem leaf_3580_ok : checkAt 527 1000 box_3580 cert_3580 = true := by
  have h := List.all_eq_true.mp batch_71_10_ok accepted_3580 (by simp [batch_71_10_values])
  exact h
theorem leaf_3580_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3580.profileLo box_3580.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3580_ok
theorem branch_box_3580_nonnegative : ∀ j, 0 ≤ branch_box_3580.lower j ∧ 0 ≤ branch_box_3580.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3580, Box.profileLo, Box.profileHi, box_3580]
theorem leaf_3580_BranchSafe : CertificateConsequences.BranchSafe branch_box_3580 := by
  left; refine ⟨branch_box_3580_nonnegative, ?_⟩
  intro z hz; exact leaf_3580_sound hz

theorem leaf_3582_ok : checkAt 527 1000 box_3582 cert_3582 = true := by
  have h := List.all_eq_true.mp batch_71_11_ok accepted_3582 (by simp [batch_71_11_values])
  exact h
theorem leaf_3582_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3582.profileLo box_3582.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3582_ok
theorem branch_box_3582_nonnegative : ∀ j, 0 ≤ branch_box_3582.lower j ∧ 0 ≤ branch_box_3582.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3582, Box.profileLo, Box.profileHi, box_3582]
theorem leaf_3582_BranchSafe : CertificateConsequences.BranchSafe branch_box_3582 := by
  left; refine ⟨branch_box_3582_nonnegative, ?_⟩
  intro z hz; exact leaf_3582_sound hz

theorem leaf_3584_ok : checkAt 527 1000 box_3584 cert_3584 = true := by
  have h := List.all_eq_true.mp batch_71_12_ok accepted_3584 (by simp [batch_71_12_values])
  exact h
theorem leaf_3584_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3584.profileLo box_3584.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3584_ok
theorem branch_box_3584_nonnegative : ∀ j, 0 ≤ branch_box_3584.lower j ∧ 0 ≤ branch_box_3584.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3584, Box.profileLo, Box.profileHi, box_3584]
theorem leaf_3584_BranchSafe : CertificateConsequences.BranchSafe branch_box_3584 := by
  left; refine ⟨branch_box_3584_nonnegative, ?_⟩
  intro z hz; exact leaf_3584_sound hz

theorem leaf_3586_ok : checkAt 527 1000 box_3586 cert_3586 = true := by
  have h := List.all_eq_true.mp batch_71_13_ok accepted_3586 (by simp [batch_71_13_values])
  exact h
theorem leaf_3586_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3586.profileLo box_3586.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3586_ok
theorem branch_box_3586_nonnegative : ∀ j, 0 ≤ branch_box_3586.lower j ∧ 0 ≤ branch_box_3586.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3586, Box.profileLo, Box.profileHi, box_3586]
theorem leaf_3586_BranchSafe : CertificateConsequences.BranchSafe branch_box_3586 := by
  left; refine ⟨branch_box_3586_nonnegative, ?_⟩
  intro z hz; exact leaf_3586_sound hz

theorem leaf_3588_ok : checkAt 527 1000 box_3588 cert_3588 = true := by
  have h := List.all_eq_true.mp batch_71_14_ok accepted_3588 (by simp [batch_71_14_values])
  exact h
theorem leaf_3588_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3588.profileLo box_3588.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3588_ok
theorem branch_box_3588_nonnegative : ∀ j, 0 ≤ branch_box_3588.lower j ∧ 0 ≤ branch_box_3588.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3588, Box.profileLo, Box.profileHi, box_3588]
theorem leaf_3588_BranchSafe : CertificateConsequences.BranchSafe branch_box_3588 := by
  left; refine ⟨branch_box_3588_nonnegative, ?_⟩
  intro z hz; exact leaf_3588_sound hz

theorem leaf_3589_ok : checkAt 527 1000 box_3589 cert_3589 = true := by
  have h := List.all_eq_true.mp batch_71_15_ok accepted_3589 (by simp [batch_71_15_values])
  exact h
theorem leaf_3589_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3589.profileLo box_3589.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3589_ok
theorem branch_box_3589_nonnegative : ∀ j, 0 ≤ branch_box_3589.lower j ∧ 0 ≤ branch_box_3589.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3589, Box.profileLo, Box.profileHi, box_3589]
theorem leaf_3589_BranchSafe : CertificateConsequences.BranchSafe branch_box_3589 := by
  left; refine ⟨branch_box_3589_nonnegative, ?_⟩
  intro z hz; exact leaf_3589_sound hz

theorem leaf_3596_ok : checkAt 527 1000 box_3596 cert_3596 = true := by
  have h := List.all_eq_true.mp batch_71_16_ok accepted_3596 (by simp [batch_71_16_values])
  exact h
theorem leaf_3596_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3596.profileLo box_3596.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3596_ok
theorem branch_box_3596_nonnegative : ∀ j, 0 ≤ branch_box_3596.lower j ∧ 0 ≤ branch_box_3596.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3596, Box.profileLo, Box.profileHi, box_3596]
theorem leaf_3596_BranchSafe : CertificateConsequences.BranchSafe branch_box_3596 := by
  left; refine ⟨branch_box_3596_nonnegative, ?_⟩
  intro z hz; exact leaf_3596_sound hz

theorem leaf_3598_ok : checkAt 527 1000 box_3598 cert_3598 = true := by
  have h := List.all_eq_true.mp batch_71_17_ok accepted_3598 (by simp [batch_71_17_values])
  exact h
theorem leaf_3598_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3598.profileLo box_3598.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3598_ok
theorem branch_box_3598_nonnegative : ∀ j, 0 ≤ branch_box_3598.lower j ∧ 0 ≤ branch_box_3598.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3598, Box.profileLo, Box.profileHi, box_3598]
theorem leaf_3598_BranchSafe : CertificateConsequences.BranchSafe branch_box_3598 := by
  left; refine ⟨branch_box_3598_nonnegative, ?_⟩
  intro z hz; exact leaf_3598_sound hz

#print axioms batch_71_00_ok
#print axioms leaf_3550_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
