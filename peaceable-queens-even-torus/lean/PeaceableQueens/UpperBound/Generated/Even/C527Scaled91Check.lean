import PeaceableQueens.UpperBound.Generated.Even.C527Scaled91Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_91_00_values : List Bool := [accepted_4552]
theorem batch_91_00_ok : batch_91_00_values.all id = true := by decide

def batch_91_01_values : List Bool := [accepted_4553]
theorem batch_91_01_ok : batch_91_01_values.all id = true := by decide

def batch_91_02_values : List Bool := [accepted_4554]
theorem batch_91_02_ok : batch_91_02_values.all id = true := by decide

def batch_91_03_values : List Bool := [accepted_4559]
theorem batch_91_03_ok : batch_91_03_values.all id = true := by decide

def batch_91_04_values : List Bool := [accepted_4560]
theorem batch_91_04_ok : batch_91_04_values.all id = true := by decide

def batch_91_05_values : List Bool := [accepted_4563]
theorem batch_91_05_ok : batch_91_05_values.all id = true := by decide

def batch_91_06_values : List Bool := [accepted_4564]
theorem batch_91_06_ok : batch_91_06_values.all id = true := by decide

def batch_91_07_values : List Bool := [accepted_4565]
theorem batch_91_07_ok : batch_91_07_values.all id = true := by decide

def batch_91_08_values : List Bool := [accepted_4566]
theorem batch_91_08_ok : batch_91_08_values.all id = true := by decide

def batch_91_09_values : List Bool := [accepted_4567]
theorem batch_91_09_ok : batch_91_09_values.all id = true := by decide

def batch_91_10_values : List Bool := [accepted_4569]
theorem batch_91_10_ok : batch_91_10_values.all id = true := by decide

def batch_91_11_values : List Bool := [accepted_4570]
theorem batch_91_11_ok : batch_91_11_values.all id = true := by decide

def batch_91_12_values : List Bool := [accepted_4591]
theorem batch_91_12_ok : batch_91_12_values.all id = true := by decide

def batch_91_13_values : List Bool := [accepted_4593]
theorem batch_91_13_ok : batch_91_13_values.all id = true := by decide

def batch_91_14_values : List Bool := [accepted_4595]
theorem batch_91_14_ok : batch_91_14_values.all id = true := by decide

def batch_91_15_values : List Bool := [accepted_4597]
theorem batch_91_15_ok : batch_91_15_values.all id = true := by decide

def batch_91_16_values : List Bool := [accepted_4599]
theorem batch_91_16_ok : batch_91_16_values.all id = true := by decide

theorem leaf_4552_ok : checkAt 527 1000 box_4552 cert_4552 = true := by
  have h := List.all_eq_true.mp batch_91_00_ok accepted_4552 (by simp [batch_91_00_values])
  exact h
theorem leaf_4552_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4552.profileLo box_4552.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4552_ok
theorem branch_box_4552_nonnegative : ∀ j, 0 ≤ branch_box_4552.lower j ∧ 0 ≤ branch_box_4552.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4552, Box.profileLo, Box.profileHi, box_4552]
theorem leaf_4552_BranchSafe : CertificateConsequences.BranchSafe branch_box_4552 := by
  left; refine ⟨branch_box_4552_nonnegative, ?_⟩
  intro z hz; exact leaf_4552_sound hz

theorem leaf_4553_ok : checkAt 527 1000 box_4553 cert_4553 = true := by
  have h := List.all_eq_true.mp batch_91_01_ok accepted_4553 (by simp [batch_91_01_values])
  exact h
theorem leaf_4553_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4553.profileLo box_4553.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4553_ok
theorem branch_box_4553_nonnegative : ∀ j, 0 ≤ branch_box_4553.lower j ∧ 0 ≤ branch_box_4553.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4553, Box.profileLo, Box.profileHi, box_4553]
theorem leaf_4553_BranchSafe : CertificateConsequences.BranchSafe branch_box_4553 := by
  left; refine ⟨branch_box_4553_nonnegative, ?_⟩
  intro z hz; exact leaf_4553_sound hz

theorem leaf_4554_ok : checkAt 527 1000 box_4554 cert_4554 = true := by
  have h := List.all_eq_true.mp batch_91_02_ok accepted_4554 (by simp [batch_91_02_values])
  exact h
theorem leaf_4554_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4554.profileLo box_4554.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4554_ok
theorem branch_box_4554_nonnegative : ∀ j, 0 ≤ branch_box_4554.lower j ∧ 0 ≤ branch_box_4554.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4554, Box.profileLo, Box.profileHi, box_4554]
theorem leaf_4554_BranchSafe : CertificateConsequences.BranchSafe branch_box_4554 := by
  left; refine ⟨branch_box_4554_nonnegative, ?_⟩
  intro z hz; exact leaf_4554_sound hz

theorem leaf_4559_ok : checkAt 527 1000 box_4559 cert_4559 = true := by
  have h := List.all_eq_true.mp batch_91_03_ok accepted_4559 (by simp [batch_91_03_values])
  exact h
theorem leaf_4559_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4559.profileLo box_4559.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4559_ok
theorem branch_box_4559_nonnegative : ∀ j, 0 ≤ branch_box_4559.lower j ∧ 0 ≤ branch_box_4559.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4559, Box.profileLo, Box.profileHi, box_4559]
theorem leaf_4559_BranchSafe : CertificateConsequences.BranchSafe branch_box_4559 := by
  left; refine ⟨branch_box_4559_nonnegative, ?_⟩
  intro z hz; exact leaf_4559_sound hz

theorem leaf_4560_ok : checkAt 527 1000 box_4560 cert_4560 = true := by
  have h := List.all_eq_true.mp batch_91_04_ok accepted_4560 (by simp [batch_91_04_values])
  exact h
theorem leaf_4560_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4560.profileLo box_4560.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4560_ok
theorem branch_box_4560_nonnegative : ∀ j, 0 ≤ branch_box_4560.lower j ∧ 0 ≤ branch_box_4560.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4560, Box.profileLo, Box.profileHi, box_4560]
theorem leaf_4560_BranchSafe : CertificateConsequences.BranchSafe branch_box_4560 := by
  left; refine ⟨branch_box_4560_nonnegative, ?_⟩
  intro z hz; exact leaf_4560_sound hz

theorem leaf_4563_ok : checkAt 527 1000 box_4563 cert_4563 = true := by
  have h := List.all_eq_true.mp batch_91_05_ok accepted_4563 (by simp [batch_91_05_values])
  exact h
theorem leaf_4563_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4563.profileLo box_4563.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4563_ok
theorem branch_box_4563_nonnegative : ∀ j, 0 ≤ branch_box_4563.lower j ∧ 0 ≤ branch_box_4563.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4563, Box.profileLo, Box.profileHi, box_4563]
theorem leaf_4563_BranchSafe : CertificateConsequences.BranchSafe branch_box_4563 := by
  left; refine ⟨branch_box_4563_nonnegative, ?_⟩
  intro z hz; exact leaf_4563_sound hz

theorem leaf_4564_ok : checkAt 527 1000 box_4564 cert_4564 = true := by
  have h := List.all_eq_true.mp batch_91_06_ok accepted_4564 (by simp [batch_91_06_values])
  exact h
theorem leaf_4564_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4564.profileLo box_4564.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4564_ok
theorem branch_box_4564_nonnegative : ∀ j, 0 ≤ branch_box_4564.lower j ∧ 0 ≤ branch_box_4564.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4564, Box.profileLo, Box.profileHi, box_4564]
theorem leaf_4564_BranchSafe : CertificateConsequences.BranchSafe branch_box_4564 := by
  left; refine ⟨branch_box_4564_nonnegative, ?_⟩
  intro z hz; exact leaf_4564_sound hz

theorem leaf_4565_ok : checkAt 527 1000 box_4565 cert_4565 = true := by
  have h := List.all_eq_true.mp batch_91_07_ok accepted_4565 (by simp [batch_91_07_values])
  exact h
theorem leaf_4565_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4565.profileLo box_4565.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4565_ok
theorem branch_box_4565_nonnegative : ∀ j, 0 ≤ branch_box_4565.lower j ∧ 0 ≤ branch_box_4565.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4565, Box.profileLo, Box.profileHi, box_4565]
theorem leaf_4565_BranchSafe : CertificateConsequences.BranchSafe branch_box_4565 := by
  left; refine ⟨branch_box_4565_nonnegative, ?_⟩
  intro z hz; exact leaf_4565_sound hz

theorem leaf_4566_ok : checkAt 527 1000 box_4566 cert_4566 = true := by
  have h := List.all_eq_true.mp batch_91_08_ok accepted_4566 (by simp [batch_91_08_values])
  exact h
theorem leaf_4566_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4566.profileLo box_4566.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4566_ok
theorem branch_box_4566_nonnegative : ∀ j, 0 ≤ branch_box_4566.lower j ∧ 0 ≤ branch_box_4566.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4566, Box.profileLo, Box.profileHi, box_4566]
theorem leaf_4566_BranchSafe : CertificateConsequences.BranchSafe branch_box_4566 := by
  left; refine ⟨branch_box_4566_nonnegative, ?_⟩
  intro z hz; exact leaf_4566_sound hz

theorem leaf_4567_ok : checkAt 527 1000 box_4567 cert_4567 = true := by
  have h := List.all_eq_true.mp batch_91_09_ok accepted_4567 (by simp [batch_91_09_values])
  exact h
theorem leaf_4567_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4567.profileLo box_4567.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4567_ok
theorem branch_box_4567_nonnegative : ∀ j, 0 ≤ branch_box_4567.lower j ∧ 0 ≤ branch_box_4567.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4567, Box.profileLo, Box.profileHi, box_4567]
theorem leaf_4567_BranchSafe : CertificateConsequences.BranchSafe branch_box_4567 := by
  left; refine ⟨branch_box_4567_nonnegative, ?_⟩
  intro z hz; exact leaf_4567_sound hz

theorem leaf_4569_ok : checkAt 527 1000 box_4569 cert_4569 = true := by
  have h := List.all_eq_true.mp batch_91_10_ok accepted_4569 (by simp [batch_91_10_values])
  exact h
theorem leaf_4569_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4569.profileLo box_4569.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4569_ok
theorem branch_box_4569_nonnegative : ∀ j, 0 ≤ branch_box_4569.lower j ∧ 0 ≤ branch_box_4569.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4569, Box.profileLo, Box.profileHi, box_4569]
theorem leaf_4569_BranchSafe : CertificateConsequences.BranchSafe branch_box_4569 := by
  left; refine ⟨branch_box_4569_nonnegative, ?_⟩
  intro z hz; exact leaf_4569_sound hz

theorem leaf_4570_ok : checkAt 527 1000 box_4570 cert_4570 = true := by
  have h := List.all_eq_true.mp batch_91_11_ok accepted_4570 (by simp [batch_91_11_values])
  exact h
theorem leaf_4570_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4570.profileLo box_4570.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4570_ok
theorem branch_box_4570_nonnegative : ∀ j, 0 ≤ branch_box_4570.lower j ∧ 0 ≤ branch_box_4570.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4570, Box.profileLo, Box.profileHi, box_4570]
theorem leaf_4570_BranchSafe : CertificateConsequences.BranchSafe branch_box_4570 := by
  left; refine ⟨branch_box_4570_nonnegative, ?_⟩
  intro z hz; exact leaf_4570_sound hz

theorem leaf_4591_ok : checkAt 527 1000 box_4591 cert_4591 = true := by
  have h := List.all_eq_true.mp batch_91_12_ok accepted_4591 (by simp [batch_91_12_values])
  exact h
theorem leaf_4591_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4591.profileLo box_4591.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4591_ok
theorem branch_box_4591_nonnegative : ∀ j, 0 ≤ branch_box_4591.lower j ∧ 0 ≤ branch_box_4591.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4591, Box.profileLo, Box.profileHi, box_4591]
theorem leaf_4591_BranchSafe : CertificateConsequences.BranchSafe branch_box_4591 := by
  left; refine ⟨branch_box_4591_nonnegative, ?_⟩
  intro z hz; exact leaf_4591_sound hz

theorem leaf_4593_ok : checkAt 527 1000 box_4593 cert_4593 = true := by
  have h := List.all_eq_true.mp batch_91_13_ok accepted_4593 (by simp [batch_91_13_values])
  exact h
theorem leaf_4593_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4593.profileLo box_4593.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4593_ok
theorem branch_box_4593_nonnegative : ∀ j, 0 ≤ branch_box_4593.lower j ∧ 0 ≤ branch_box_4593.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4593, Box.profileLo, Box.profileHi, box_4593]
theorem leaf_4593_BranchSafe : CertificateConsequences.BranchSafe branch_box_4593 := by
  left; refine ⟨branch_box_4593_nonnegative, ?_⟩
  intro z hz; exact leaf_4593_sound hz

theorem leaf_4595_ok : checkAt 527 1000 box_4595 cert_4595 = true := by
  have h := List.all_eq_true.mp batch_91_14_ok accepted_4595 (by simp [batch_91_14_values])
  exact h
theorem leaf_4595_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4595.profileLo box_4595.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4595_ok
theorem branch_box_4595_nonnegative : ∀ j, 0 ≤ branch_box_4595.lower j ∧ 0 ≤ branch_box_4595.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4595, Box.profileLo, Box.profileHi, box_4595]
theorem leaf_4595_BranchSafe : CertificateConsequences.BranchSafe branch_box_4595 := by
  left; refine ⟨branch_box_4595_nonnegative, ?_⟩
  intro z hz; exact leaf_4595_sound hz

theorem leaf_4597_ok : checkAt 527 1000 box_4597 cert_4597 = true := by
  have h := List.all_eq_true.mp batch_91_15_ok accepted_4597 (by simp [batch_91_15_values])
  exact h
theorem leaf_4597_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4597.profileLo box_4597.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4597_ok
theorem branch_box_4597_nonnegative : ∀ j, 0 ≤ branch_box_4597.lower j ∧ 0 ≤ branch_box_4597.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4597, Box.profileLo, Box.profileHi, box_4597]
theorem leaf_4597_BranchSafe : CertificateConsequences.BranchSafe branch_box_4597 := by
  left; refine ⟨branch_box_4597_nonnegative, ?_⟩
  intro z hz; exact leaf_4597_sound hz

theorem leaf_4599_ok : checkAt 527 1000 box_4599 cert_4599 = true := by
  have h := List.all_eq_true.mp batch_91_16_ok accepted_4599 (by simp [batch_91_16_values])
  exact h
theorem leaf_4599_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4599.profileLo box_4599.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4599_ok
theorem branch_box_4599_nonnegative : ∀ j, 0 ≤ branch_box_4599.lower j ∧ 0 ≤ branch_box_4599.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4599, Box.profileLo, Box.profileHi, box_4599]
theorem leaf_4599_BranchSafe : CertificateConsequences.BranchSafe branch_box_4599 := by
  left; refine ⟨branch_box_4599_nonnegative, ?_⟩
  intro z hz; exact leaf_4599_sound hz

#print axioms batch_91_00_ok
#print axioms leaf_4552_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
