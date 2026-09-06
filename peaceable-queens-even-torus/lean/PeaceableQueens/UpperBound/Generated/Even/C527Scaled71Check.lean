import PeaceableQueens.UpperBound.Generated.Even.C527Scaled71Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_71_00_values : List Bool := [accepted_3550]
theorem batch_71_00_ok : batch_71_00_values.all id = true := by decide

def batch_71_01_values : List Bool := [accepted_3551]
theorem batch_71_01_ok : batch_71_01_values.all id = true := by decide

def batch_71_02_values : List Bool := [accepted_3552]
theorem batch_71_02_ok : batch_71_02_values.all id = true := by decide

def batch_71_03_values : List Bool := [accepted_3567]
theorem batch_71_03_ok : batch_71_03_values.all id = true := by decide

def batch_71_04_values : List Bool := [accepted_3569]
theorem batch_71_04_ok : batch_71_04_values.all id = true := by decide

def batch_71_05_values : List Bool := [accepted_3571]
theorem batch_71_05_ok : batch_71_05_values.all id = true := by decide

def batch_71_06_values : List Bool := [accepted_3573]
theorem batch_71_06_ok : batch_71_06_values.all id = true := by decide

def batch_71_07_values : List Bool := [accepted_3574]
theorem batch_71_07_ok : batch_71_07_values.all id = true := by decide

def batch_71_08_values : List Bool := [accepted_3575]
theorem batch_71_08_ok : batch_71_08_values.all id = true := by decide

def batch_71_09_values : List Bool := [accepted_3577]
theorem batch_71_09_ok : batch_71_09_values.all id = true := by decide

def batch_71_10_values : List Bool := [accepted_3580]
theorem batch_71_10_ok : batch_71_10_values.all id = true := by decide

def batch_71_11_values : List Bool := [accepted_3581]
theorem batch_71_11_ok : batch_71_11_values.all id = true := by decide

def batch_71_12_values : List Bool := [accepted_3582]
theorem batch_71_12_ok : batch_71_12_values.all id = true := by decide

def batch_71_13_values : List Bool := [accepted_3583]
theorem batch_71_13_ok : batch_71_13_values.all id = true := by decide

def batch_71_14_values : List Bool := [accepted_3587]
theorem batch_71_14_ok : batch_71_14_values.all id = true := by decide

def batch_71_15_values : List Bool := [accepted_3588]
theorem batch_71_15_ok : batch_71_15_values.all id = true := by decide

def batch_71_16_values : List Bool := [accepted_3589]
theorem batch_71_16_ok : batch_71_16_values.all id = true := by decide

def batch_71_17_values : List Bool := [accepted_3591]
theorem batch_71_17_ok : batch_71_17_values.all id = true := by decide

def batch_71_18_values : List Bool := [accepted_3592]
theorem batch_71_18_ok : batch_71_18_values.all id = true := by decide

def batch_71_19_values : List Bool := [accepted_3595]
theorem batch_71_19_ok : batch_71_19_values.all id = true := by decide

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

theorem leaf_3551_ok : checkAt 527 1000 box_3551 cert_3551 = true := by
  have h := List.all_eq_true.mp batch_71_01_ok accepted_3551 (by simp [batch_71_01_values])
  exact h
theorem leaf_3551_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3551.profileLo box_3551.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3551_ok
theorem branch_box_3551_nonnegative : ∀ j, 0 ≤ branch_box_3551.lower j ∧ 0 ≤ branch_box_3551.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3551, Box.profileLo, Box.profileHi, box_3551]
theorem leaf_3551_BranchSafe : CertificateConsequences.BranchSafe branch_box_3551 := by
  left; refine ⟨branch_box_3551_nonnegative, ?_⟩
  intro z hz; exact leaf_3551_sound hz

theorem leaf_3552_ok : checkAt 527 1000 box_3552 cert_3552 = true := by
  have h := List.all_eq_true.mp batch_71_02_ok accepted_3552 (by simp [batch_71_02_values])
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

theorem leaf_3567_ok : checkAt 527 1000 box_3567 cert_3567 = true := by
  have h := List.all_eq_true.mp batch_71_03_ok accepted_3567 (by simp [batch_71_03_values])
  exact h
theorem leaf_3567_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3567.profileLo box_3567.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3567_ok
theorem branch_box_3567_nonnegative : ∀ j, 0 ≤ branch_box_3567.lower j ∧ 0 ≤ branch_box_3567.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3567, Box.profileLo, Box.profileHi, box_3567]
theorem leaf_3567_BranchSafe : CertificateConsequences.BranchSafe branch_box_3567 := by
  left; refine ⟨branch_box_3567_nonnegative, ?_⟩
  intro z hz; exact leaf_3567_sound hz

theorem leaf_3569_ok : checkAt 527 1000 box_3569 cert_3569 = true := by
  have h := List.all_eq_true.mp batch_71_04_ok accepted_3569 (by simp [batch_71_04_values])
  exact h
theorem leaf_3569_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3569.profileLo box_3569.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3569_ok
theorem branch_box_3569_nonnegative : ∀ j, 0 ≤ branch_box_3569.lower j ∧ 0 ≤ branch_box_3569.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3569, Box.profileLo, Box.profileHi, box_3569]
theorem leaf_3569_BranchSafe : CertificateConsequences.BranchSafe branch_box_3569 := by
  left; refine ⟨branch_box_3569_nonnegative, ?_⟩
  intro z hz; exact leaf_3569_sound hz

theorem leaf_3571_ok : checkAt 527 1000 box_3571 cert_3571 = true := by
  have h := List.all_eq_true.mp batch_71_05_ok accepted_3571 (by simp [batch_71_05_values])
  exact h
theorem leaf_3571_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3571.profileLo box_3571.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3571_ok
theorem branch_box_3571_nonnegative : ∀ j, 0 ≤ branch_box_3571.lower j ∧ 0 ≤ branch_box_3571.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3571, Box.profileLo, Box.profileHi, box_3571]
theorem leaf_3571_BranchSafe : CertificateConsequences.BranchSafe branch_box_3571 := by
  left; refine ⟨branch_box_3571_nonnegative, ?_⟩
  intro z hz; exact leaf_3571_sound hz

theorem leaf_3573_ok : checkAt 527 1000 box_3573 cert_3573 = true := by
  have h := List.all_eq_true.mp batch_71_06_ok accepted_3573 (by simp [batch_71_06_values])
  exact h
theorem leaf_3573_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3573.profileLo box_3573.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3573_ok
theorem branch_box_3573_nonnegative : ∀ j, 0 ≤ branch_box_3573.lower j ∧ 0 ≤ branch_box_3573.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3573, Box.profileLo, Box.profileHi, box_3573]
theorem leaf_3573_BranchSafe : CertificateConsequences.BranchSafe branch_box_3573 := by
  left; refine ⟨branch_box_3573_nonnegative, ?_⟩
  intro z hz; exact leaf_3573_sound hz

theorem leaf_3574_ok : checkAt 527 1000 box_3574 cert_3574 = true := by
  have h := List.all_eq_true.mp batch_71_07_ok accepted_3574 (by simp [batch_71_07_values])
  exact h
theorem leaf_3574_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3574.profileLo box_3574.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3574_ok
theorem branch_box_3574_nonnegative : ∀ j, 0 ≤ branch_box_3574.lower j ∧ 0 ≤ branch_box_3574.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3574, Box.profileLo, Box.profileHi, box_3574]
theorem leaf_3574_BranchSafe : CertificateConsequences.BranchSafe branch_box_3574 := by
  left; refine ⟨branch_box_3574_nonnegative, ?_⟩
  intro z hz; exact leaf_3574_sound hz

theorem leaf_3575_ok : checkAt 527 1000 box_3575 cert_3575 = true := by
  have h := List.all_eq_true.mp batch_71_08_ok accepted_3575 (by simp [batch_71_08_values])
  exact h
theorem leaf_3575_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3575.profileLo box_3575.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3575_ok
theorem branch_box_3575_nonnegative : ∀ j, 0 ≤ branch_box_3575.lower j ∧ 0 ≤ branch_box_3575.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3575, Box.profileLo, Box.profileHi, box_3575]
theorem leaf_3575_BranchSafe : CertificateConsequences.BranchSafe branch_box_3575 := by
  left; refine ⟨branch_box_3575_nonnegative, ?_⟩
  intro z hz; exact leaf_3575_sound hz

theorem leaf_3577_ok : checkAt 527 1000 box_3577 cert_3577 = true := by
  have h := List.all_eq_true.mp batch_71_09_ok accepted_3577 (by simp [batch_71_09_values])
  exact h
theorem leaf_3577_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3577.profileLo box_3577.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3577_ok
theorem branch_box_3577_nonnegative : ∀ j, 0 ≤ branch_box_3577.lower j ∧ 0 ≤ branch_box_3577.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3577, Box.profileLo, Box.profileHi, box_3577]
theorem leaf_3577_BranchSafe : CertificateConsequences.BranchSafe branch_box_3577 := by
  left; refine ⟨branch_box_3577_nonnegative, ?_⟩
  intro z hz; exact leaf_3577_sound hz

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

theorem leaf_3581_ok : checkAt 527 1000 box_3581 cert_3581 = true := by
  have h := List.all_eq_true.mp batch_71_11_ok accepted_3581 (by simp [batch_71_11_values])
  exact h
theorem leaf_3581_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3581.profileLo box_3581.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3581_ok
theorem branch_box_3581_nonnegative : ∀ j, 0 ≤ branch_box_3581.lower j ∧ 0 ≤ branch_box_3581.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3581, Box.profileLo, Box.profileHi, box_3581]
theorem leaf_3581_BranchSafe : CertificateConsequences.BranchSafe branch_box_3581 := by
  left; refine ⟨branch_box_3581_nonnegative, ?_⟩
  intro z hz; exact leaf_3581_sound hz

theorem leaf_3582_ok : checkAt 527 1000 box_3582 cert_3582 = true := by
  have h := List.all_eq_true.mp batch_71_12_ok accepted_3582 (by simp [batch_71_12_values])
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

theorem leaf_3583_ok : checkAt 527 1000 box_3583 cert_3583 = true := by
  have h := List.all_eq_true.mp batch_71_13_ok accepted_3583 (by simp [batch_71_13_values])
  exact h
theorem leaf_3583_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3583.profileLo box_3583.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3583_ok
theorem branch_box_3583_nonnegative : ∀ j, 0 ≤ branch_box_3583.lower j ∧ 0 ≤ branch_box_3583.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3583, Box.profileLo, Box.profileHi, box_3583]
theorem leaf_3583_BranchSafe : CertificateConsequences.BranchSafe branch_box_3583 := by
  left; refine ⟨branch_box_3583_nonnegative, ?_⟩
  intro z hz; exact leaf_3583_sound hz

theorem leaf_3587_ok : checkAt 527 1000 box_3587 cert_3587 = true := by
  have h := List.all_eq_true.mp batch_71_14_ok accepted_3587 (by simp [batch_71_14_values])
  exact h
theorem leaf_3587_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3587.profileLo box_3587.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3587_ok
theorem branch_box_3587_nonnegative : ∀ j, 0 ≤ branch_box_3587.lower j ∧ 0 ≤ branch_box_3587.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3587, Box.profileLo, Box.profileHi, box_3587]
theorem leaf_3587_BranchSafe : CertificateConsequences.BranchSafe branch_box_3587 := by
  left; refine ⟨branch_box_3587_nonnegative, ?_⟩
  intro z hz; exact leaf_3587_sound hz

theorem leaf_3588_ok : checkAt 527 1000 box_3588 cert_3588 = true := by
  have h := List.all_eq_true.mp batch_71_15_ok accepted_3588 (by simp [batch_71_15_values])
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
  have h := List.all_eq_true.mp batch_71_16_ok accepted_3589 (by simp [batch_71_16_values])
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

theorem leaf_3591_ok : checkAt 527 1000 box_3591 cert_3591 = true := by
  have h := List.all_eq_true.mp batch_71_17_ok accepted_3591 (by simp [batch_71_17_values])
  exact h
theorem leaf_3591_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3591.profileLo box_3591.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3591_ok
theorem branch_box_3591_nonnegative : ∀ j, 0 ≤ branch_box_3591.lower j ∧ 0 ≤ branch_box_3591.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3591, Box.profileLo, Box.profileHi, box_3591]
theorem leaf_3591_BranchSafe : CertificateConsequences.BranchSafe branch_box_3591 := by
  left; refine ⟨branch_box_3591_nonnegative, ?_⟩
  intro z hz; exact leaf_3591_sound hz

theorem leaf_3592_ok : checkAt 527 1000 box_3592 cert_3592 = true := by
  have h := List.all_eq_true.mp batch_71_18_ok accepted_3592 (by simp [batch_71_18_values])
  exact h
theorem leaf_3592_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3592.profileLo box_3592.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3592_ok
theorem branch_box_3592_nonnegative : ∀ j, 0 ≤ branch_box_3592.lower j ∧ 0 ≤ branch_box_3592.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3592, Box.profileLo, Box.profileHi, box_3592]
theorem leaf_3592_BranchSafe : CertificateConsequences.BranchSafe branch_box_3592 := by
  left; refine ⟨branch_box_3592_nonnegative, ?_⟩
  intro z hz; exact leaf_3592_sound hz

theorem leaf_3595_ok : checkAt 527 1000 box_3595 cert_3595 = true := by
  have h := List.all_eq_true.mp batch_71_19_ok accepted_3595 (by simp [batch_71_19_values])
  exact h
theorem leaf_3595_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3595.profileLo box_3595.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3595_ok
theorem branch_box_3595_nonnegative : ∀ j, 0 ≤ branch_box_3595.lower j ∧ 0 ≤ branch_box_3595.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3595, Box.profileLo, Box.profileHi, box_3595]
theorem leaf_3595_BranchSafe : CertificateConsequences.BranchSafe branch_box_3595 := by
  left; refine ⟨branch_box_3595_nonnegative, ?_⟩
  intro z hz; exact leaf_3595_sound hz

#print axioms batch_71_00_ok
#print axioms leaf_3550_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
