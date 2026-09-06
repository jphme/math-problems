import PeaceableQueens.UpperBound.Generated.Even.C527Scaled111Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_111_00_values : List Bool := [accepted_5551]
theorem batch_111_00_ok : batch_111_00_values.all id = true := by decide

def batch_111_01_values : List Bool := [accepted_5552]
theorem batch_111_01_ok : batch_111_01_values.all id = true := by decide

def batch_111_02_values : List Bool := [accepted_5555]
theorem batch_111_02_ok : batch_111_02_values.all id = true := by decide

def batch_111_03_values : List Bool := [accepted_5556]
theorem batch_111_03_ok : batch_111_03_values.all id = true := by decide

def batch_111_04_values : List Bool := [accepted_5557]
theorem batch_111_04_ok : batch_111_04_values.all id = true := by decide

def batch_111_05_values : List Bool := [accepted_5558]
theorem batch_111_05_ok : batch_111_05_values.all id = true := by decide

def batch_111_06_values : List Bool := [accepted_5563]
theorem batch_111_06_ok : batch_111_06_values.all id = true := by decide

def batch_111_07_values : List Bool := [accepted_5564]
theorem batch_111_07_ok : batch_111_07_values.all id = true := by decide

def batch_111_08_values : List Bool := [accepted_5565]
theorem batch_111_08_ok : batch_111_08_values.all id = true := by decide

def batch_111_09_values : List Bool := [accepted_5566]
theorem batch_111_09_ok : batch_111_09_values.all id = true := by decide

def batch_111_10_values : List Bool := [accepted_5569]
theorem batch_111_10_ok : batch_111_10_values.all id = true := by decide

def batch_111_11_values : List Bool := [accepted_5573]
theorem batch_111_11_ok : batch_111_11_values.all id = true := by decide

def batch_111_12_values : List Bool := [accepted_5574]
theorem batch_111_12_ok : batch_111_12_values.all id = true := by decide

def batch_111_13_values : List Bool := [accepted_5576]
theorem batch_111_13_ok : batch_111_13_values.all id = true := by decide

def batch_111_14_values : List Bool := [accepted_5577]
theorem batch_111_14_ok : batch_111_14_values.all id = true := by decide

def batch_111_15_values : List Bool := [accepted_5578]
theorem batch_111_15_ok : batch_111_15_values.all id = true := by decide

def batch_111_16_values : List Bool := [accepted_5581]
theorem batch_111_16_ok : batch_111_16_values.all id = true := by decide

def batch_111_17_values : List Bool := [accepted_5582]
theorem batch_111_17_ok : batch_111_17_values.all id = true := by decide

def batch_111_18_values : List Bool := [accepted_5585]
theorem batch_111_18_ok : batch_111_18_values.all id = true := by decide

def batch_111_19_values : List Bool := [accepted_5586]
theorem batch_111_19_ok : batch_111_19_values.all id = true := by decide

def batch_111_20_values : List Bool := [accepted_5587]
theorem batch_111_20_ok : batch_111_20_values.all id = true := by decide

def batch_111_21_values : List Bool := [accepted_5590]
theorem batch_111_21_ok : batch_111_21_values.all id = true := by decide

def batch_111_22_values : List Bool := [accepted_5591]
theorem batch_111_22_ok : batch_111_22_values.all id = true := by decide

def batch_111_23_values : List Bool := [accepted_5592]
theorem batch_111_23_ok : batch_111_23_values.all id = true := by decide

def batch_111_24_values : List Bool := [accepted_5598]
theorem batch_111_24_ok : batch_111_24_values.all id = true := by decide

def batch_111_25_values : List Bool := [accepted_5599]
theorem batch_111_25_ok : batch_111_25_values.all id = true := by decide

theorem leaf_5551_ok : checkAt 527 1000 box_5551 cert_5551 = true := by
  have h := List.all_eq_true.mp batch_111_00_ok accepted_5551 (by simp [batch_111_00_values])
  exact h
theorem leaf_5551_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5551.profileLo box_5551.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5551_ok
theorem branch_box_5551_nonnegative : ∀ j, 0 ≤ branch_box_5551.lower j ∧ 0 ≤ branch_box_5551.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5551, Box.profileLo, Box.profileHi, box_5551]
theorem leaf_5551_BranchSafe : CertificateConsequences.BranchSafe branch_box_5551 := by
  left; refine ⟨branch_box_5551_nonnegative, ?_⟩
  intro z hz; exact leaf_5551_sound hz

theorem leaf_5552_ok : checkAt 527 1000 box_5552 cert_5552 = true := by
  have h := List.all_eq_true.mp batch_111_01_ok accepted_5552 (by simp [batch_111_01_values])
  exact h
theorem leaf_5552_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5552.profileLo box_5552.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5552_ok
theorem branch_box_5552_nonnegative : ∀ j, 0 ≤ branch_box_5552.lower j ∧ 0 ≤ branch_box_5552.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5552, Box.profileLo, Box.profileHi, box_5552]
theorem leaf_5552_BranchSafe : CertificateConsequences.BranchSafe branch_box_5552 := by
  left; refine ⟨branch_box_5552_nonnegative, ?_⟩
  intro z hz; exact leaf_5552_sound hz

theorem leaf_5555_ok : checkAt 527 1000 box_5555 cert_5555 = true := by
  have h := List.all_eq_true.mp batch_111_02_ok accepted_5555 (by simp [batch_111_02_values])
  exact h
theorem leaf_5555_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5555.profileLo box_5555.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5555_ok
theorem branch_box_5555_nonnegative : ∀ j, 0 ≤ branch_box_5555.lower j ∧ 0 ≤ branch_box_5555.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5555, Box.profileLo, Box.profileHi, box_5555]
theorem leaf_5555_BranchSafe : CertificateConsequences.BranchSafe branch_box_5555 := by
  left; refine ⟨branch_box_5555_nonnegative, ?_⟩
  intro z hz; exact leaf_5555_sound hz

theorem leaf_5556_ok : checkAt 527 1000 box_5556 cert_5556 = true := by
  have h := List.all_eq_true.mp batch_111_03_ok accepted_5556 (by simp [batch_111_03_values])
  exact h
theorem leaf_5556_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5556.profileLo box_5556.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5556_ok
theorem branch_box_5556_nonnegative : ∀ j, 0 ≤ branch_box_5556.lower j ∧ 0 ≤ branch_box_5556.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5556, Box.profileLo, Box.profileHi, box_5556]
theorem leaf_5556_BranchSafe : CertificateConsequences.BranchSafe branch_box_5556 := by
  left; refine ⟨branch_box_5556_nonnegative, ?_⟩
  intro z hz; exact leaf_5556_sound hz

theorem leaf_5557_ok : checkAt 527 1000 box_5557 cert_5557 = true := by
  have h := List.all_eq_true.mp batch_111_04_ok accepted_5557 (by simp [batch_111_04_values])
  exact h
theorem leaf_5557_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5557.profileLo box_5557.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5557_ok
theorem branch_box_5557_nonnegative : ∀ j, 0 ≤ branch_box_5557.lower j ∧ 0 ≤ branch_box_5557.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5557, Box.profileLo, Box.profileHi, box_5557]
theorem leaf_5557_BranchSafe : CertificateConsequences.BranchSafe branch_box_5557 := by
  left; refine ⟨branch_box_5557_nonnegative, ?_⟩
  intro z hz; exact leaf_5557_sound hz

theorem leaf_5558_ok : checkAt 527 1000 box_5558 cert_5558 = true := by
  have h := List.all_eq_true.mp batch_111_05_ok accepted_5558 (by simp [batch_111_05_values])
  exact h
theorem leaf_5558_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5558.profileLo box_5558.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5558_ok
theorem branch_box_5558_nonnegative : ∀ j, 0 ≤ branch_box_5558.lower j ∧ 0 ≤ branch_box_5558.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5558, Box.profileLo, Box.profileHi, box_5558]
theorem leaf_5558_BranchSafe : CertificateConsequences.BranchSafe branch_box_5558 := by
  left; refine ⟨branch_box_5558_nonnegative, ?_⟩
  intro z hz; exact leaf_5558_sound hz

theorem leaf_5563_ok : checkAt 527 1000 box_5563 cert_5563 = true := by
  have h := List.all_eq_true.mp batch_111_06_ok accepted_5563 (by simp [batch_111_06_values])
  exact h
theorem leaf_5563_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5563.profileLo box_5563.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5563_ok
theorem branch_box_5563_nonnegative : ∀ j, 0 ≤ branch_box_5563.lower j ∧ 0 ≤ branch_box_5563.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5563, Box.profileLo, Box.profileHi, box_5563]
theorem leaf_5563_BranchSafe : CertificateConsequences.BranchSafe branch_box_5563 := by
  left; refine ⟨branch_box_5563_nonnegative, ?_⟩
  intro z hz; exact leaf_5563_sound hz

theorem leaf_5564_ok : checkAt 527 1000 box_5564 cert_5564 = true := by
  have h := List.all_eq_true.mp batch_111_07_ok accepted_5564 (by simp [batch_111_07_values])
  exact h
theorem leaf_5564_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5564.profileLo box_5564.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5564_ok
theorem branch_box_5564_nonnegative : ∀ j, 0 ≤ branch_box_5564.lower j ∧ 0 ≤ branch_box_5564.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5564, Box.profileLo, Box.profileHi, box_5564]
theorem leaf_5564_BranchSafe : CertificateConsequences.BranchSafe branch_box_5564 := by
  left; refine ⟨branch_box_5564_nonnegative, ?_⟩
  intro z hz; exact leaf_5564_sound hz

theorem leaf_5565_ok : checkAt 527 1000 box_5565 cert_5565 = true := by
  have h := List.all_eq_true.mp batch_111_08_ok accepted_5565 (by simp [batch_111_08_values])
  exact h
theorem leaf_5565_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5565.profileLo box_5565.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5565_ok
theorem branch_box_5565_nonnegative : ∀ j, 0 ≤ branch_box_5565.lower j ∧ 0 ≤ branch_box_5565.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5565, Box.profileLo, Box.profileHi, box_5565]
theorem leaf_5565_BranchSafe : CertificateConsequences.BranchSafe branch_box_5565 := by
  left; refine ⟨branch_box_5565_nonnegative, ?_⟩
  intro z hz; exact leaf_5565_sound hz

theorem leaf_5566_ok : checkAt 527 1000 box_5566 cert_5566 = true := by
  have h := List.all_eq_true.mp batch_111_09_ok accepted_5566 (by simp [batch_111_09_values])
  exact h
theorem leaf_5566_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5566.profileLo box_5566.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5566_ok
theorem branch_box_5566_nonnegative : ∀ j, 0 ≤ branch_box_5566.lower j ∧ 0 ≤ branch_box_5566.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5566, Box.profileLo, Box.profileHi, box_5566]
theorem leaf_5566_BranchSafe : CertificateConsequences.BranchSafe branch_box_5566 := by
  left; refine ⟨branch_box_5566_nonnegative, ?_⟩
  intro z hz; exact leaf_5566_sound hz

theorem leaf_5569_ok : checkAt 527 1000 box_5569 cert_5569 = true := by
  have h := List.all_eq_true.mp batch_111_10_ok accepted_5569 (by simp [batch_111_10_values])
  exact h
theorem leaf_5569_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5569.profileLo box_5569.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5569_ok
theorem branch_box_5569_nonnegative : ∀ j, 0 ≤ branch_box_5569.lower j ∧ 0 ≤ branch_box_5569.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5569, Box.profileLo, Box.profileHi, box_5569]
theorem leaf_5569_BranchSafe : CertificateConsequences.BranchSafe branch_box_5569 := by
  left; refine ⟨branch_box_5569_nonnegative, ?_⟩
  intro z hz; exact leaf_5569_sound hz

theorem leaf_5573_ok : checkAt 527 1000 box_5573 cert_5573 = true := by
  have h := List.all_eq_true.mp batch_111_11_ok accepted_5573 (by simp [batch_111_11_values])
  exact h
theorem leaf_5573_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5573.profileLo box_5573.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5573_ok
theorem branch_box_5573_nonnegative : ∀ j, 0 ≤ branch_box_5573.lower j ∧ 0 ≤ branch_box_5573.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5573, Box.profileLo, Box.profileHi, box_5573]
theorem leaf_5573_BranchSafe : CertificateConsequences.BranchSafe branch_box_5573 := by
  left; refine ⟨branch_box_5573_nonnegative, ?_⟩
  intro z hz; exact leaf_5573_sound hz

theorem leaf_5574_ok : checkAt 527 1000 box_5574 cert_5574 = true := by
  have h := List.all_eq_true.mp batch_111_12_ok accepted_5574 (by simp [batch_111_12_values])
  exact h
theorem leaf_5574_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5574.profileLo box_5574.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5574_ok
theorem branch_box_5574_nonnegative : ∀ j, 0 ≤ branch_box_5574.lower j ∧ 0 ≤ branch_box_5574.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5574, Box.profileLo, Box.profileHi, box_5574]
theorem leaf_5574_BranchSafe : CertificateConsequences.BranchSafe branch_box_5574 := by
  left; refine ⟨branch_box_5574_nonnegative, ?_⟩
  intro z hz; exact leaf_5574_sound hz

theorem leaf_5576_ok : checkAt 527 1000 box_5576 cert_5576 = true := by
  have h := List.all_eq_true.mp batch_111_13_ok accepted_5576 (by simp [batch_111_13_values])
  exact h
theorem leaf_5576_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5576.profileLo box_5576.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5576_ok
theorem branch_box_5576_nonnegative : ∀ j, 0 ≤ branch_box_5576.lower j ∧ 0 ≤ branch_box_5576.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5576, Box.profileLo, Box.profileHi, box_5576]
theorem leaf_5576_BranchSafe : CertificateConsequences.BranchSafe branch_box_5576 := by
  left; refine ⟨branch_box_5576_nonnegative, ?_⟩
  intro z hz; exact leaf_5576_sound hz

theorem leaf_5577_ok : checkAt 527 1000 box_5577 cert_5577 = true := by
  have h := List.all_eq_true.mp batch_111_14_ok accepted_5577 (by simp [batch_111_14_values])
  exact h
theorem leaf_5577_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5577.profileLo box_5577.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5577_ok
theorem branch_box_5577_nonnegative : ∀ j, 0 ≤ branch_box_5577.lower j ∧ 0 ≤ branch_box_5577.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5577, Box.profileLo, Box.profileHi, box_5577]
theorem leaf_5577_BranchSafe : CertificateConsequences.BranchSafe branch_box_5577 := by
  left; refine ⟨branch_box_5577_nonnegative, ?_⟩
  intro z hz; exact leaf_5577_sound hz

theorem leaf_5578_ok : checkAt 527 1000 box_5578 cert_5578 = true := by
  have h := List.all_eq_true.mp batch_111_15_ok accepted_5578 (by simp [batch_111_15_values])
  exact h
theorem leaf_5578_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5578.profileLo box_5578.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5578_ok
theorem branch_box_5578_nonnegative : ∀ j, 0 ≤ branch_box_5578.lower j ∧ 0 ≤ branch_box_5578.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5578, Box.profileLo, Box.profileHi, box_5578]
theorem leaf_5578_BranchSafe : CertificateConsequences.BranchSafe branch_box_5578 := by
  left; refine ⟨branch_box_5578_nonnegative, ?_⟩
  intro z hz; exact leaf_5578_sound hz

theorem leaf_5581_ok : checkAt 527 1000 box_5581 cert_5581 = true := by
  have h := List.all_eq_true.mp batch_111_16_ok accepted_5581 (by simp [batch_111_16_values])
  exact h
theorem leaf_5581_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5581.profileLo box_5581.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5581_ok
theorem branch_box_5581_nonnegative : ∀ j, 0 ≤ branch_box_5581.lower j ∧ 0 ≤ branch_box_5581.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5581, Box.profileLo, Box.profileHi, box_5581]
theorem leaf_5581_BranchSafe : CertificateConsequences.BranchSafe branch_box_5581 := by
  left; refine ⟨branch_box_5581_nonnegative, ?_⟩
  intro z hz; exact leaf_5581_sound hz

theorem leaf_5582_ok : checkAt 527 1000 box_5582 cert_5582 = true := by
  have h := List.all_eq_true.mp batch_111_17_ok accepted_5582 (by simp [batch_111_17_values])
  exact h
theorem leaf_5582_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5582.profileLo box_5582.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5582_ok
theorem branch_box_5582_nonnegative : ∀ j, 0 ≤ branch_box_5582.lower j ∧ 0 ≤ branch_box_5582.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5582, Box.profileLo, Box.profileHi, box_5582]
theorem leaf_5582_BranchSafe : CertificateConsequences.BranchSafe branch_box_5582 := by
  left; refine ⟨branch_box_5582_nonnegative, ?_⟩
  intro z hz; exact leaf_5582_sound hz

theorem leaf_5585_ok : checkAt 527 1000 box_5585 cert_5585 = true := by
  have h := List.all_eq_true.mp batch_111_18_ok accepted_5585 (by simp [batch_111_18_values])
  exact h
theorem leaf_5585_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5585.profileLo box_5585.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5585_ok
theorem branch_box_5585_nonnegative : ∀ j, 0 ≤ branch_box_5585.lower j ∧ 0 ≤ branch_box_5585.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5585, Box.profileLo, Box.profileHi, box_5585]
theorem leaf_5585_BranchSafe : CertificateConsequences.BranchSafe branch_box_5585 := by
  left; refine ⟨branch_box_5585_nonnegative, ?_⟩
  intro z hz; exact leaf_5585_sound hz

theorem leaf_5586_ok : checkAt 527 1000 box_5586 cert_5586 = true := by
  have h := List.all_eq_true.mp batch_111_19_ok accepted_5586 (by simp [batch_111_19_values])
  exact h
theorem leaf_5586_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5586.profileLo box_5586.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5586_ok
theorem branch_box_5586_nonnegative : ∀ j, 0 ≤ branch_box_5586.lower j ∧ 0 ≤ branch_box_5586.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5586, Box.profileLo, Box.profileHi, box_5586]
theorem leaf_5586_BranchSafe : CertificateConsequences.BranchSafe branch_box_5586 := by
  left; refine ⟨branch_box_5586_nonnegative, ?_⟩
  intro z hz; exact leaf_5586_sound hz

theorem leaf_5587_ok : checkAt 527 1000 box_5587 cert_5587 = true := by
  have h := List.all_eq_true.mp batch_111_20_ok accepted_5587 (by simp [batch_111_20_values])
  exact h
theorem leaf_5587_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5587.profileLo box_5587.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5587_ok
theorem branch_box_5587_nonnegative : ∀ j, 0 ≤ branch_box_5587.lower j ∧ 0 ≤ branch_box_5587.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5587, Box.profileLo, Box.profileHi, box_5587]
theorem leaf_5587_BranchSafe : CertificateConsequences.BranchSafe branch_box_5587 := by
  left; refine ⟨branch_box_5587_nonnegative, ?_⟩
  intro z hz; exact leaf_5587_sound hz

theorem leaf_5590_ok : checkAt 527 1000 box_5590 cert_5590 = true := by
  have h := List.all_eq_true.mp batch_111_21_ok accepted_5590 (by simp [batch_111_21_values])
  exact h
theorem leaf_5590_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5590.profileLo box_5590.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5590_ok
theorem branch_box_5590_nonnegative : ∀ j, 0 ≤ branch_box_5590.lower j ∧ 0 ≤ branch_box_5590.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5590, Box.profileLo, Box.profileHi, box_5590]
theorem leaf_5590_BranchSafe : CertificateConsequences.BranchSafe branch_box_5590 := by
  left; refine ⟨branch_box_5590_nonnegative, ?_⟩
  intro z hz; exact leaf_5590_sound hz

theorem leaf_5591_ok : checkAt 527 1000 box_5591 cert_5591 = true := by
  have h := List.all_eq_true.mp batch_111_22_ok accepted_5591 (by simp [batch_111_22_values])
  exact h
theorem leaf_5591_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5591.profileLo box_5591.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5591_ok
theorem branch_box_5591_nonnegative : ∀ j, 0 ≤ branch_box_5591.lower j ∧ 0 ≤ branch_box_5591.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5591, Box.profileLo, Box.profileHi, box_5591]
theorem leaf_5591_BranchSafe : CertificateConsequences.BranchSafe branch_box_5591 := by
  left; refine ⟨branch_box_5591_nonnegative, ?_⟩
  intro z hz; exact leaf_5591_sound hz

theorem leaf_5592_ok : checkAt 527 1000 box_5592 cert_5592 = true := by
  have h := List.all_eq_true.mp batch_111_23_ok accepted_5592 (by simp [batch_111_23_values])
  exact h
theorem leaf_5592_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5592.profileLo box_5592.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5592_ok
theorem branch_box_5592_nonnegative : ∀ j, 0 ≤ branch_box_5592.lower j ∧ 0 ≤ branch_box_5592.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5592, Box.profileLo, Box.profileHi, box_5592]
theorem leaf_5592_BranchSafe : CertificateConsequences.BranchSafe branch_box_5592 := by
  left; refine ⟨branch_box_5592_nonnegative, ?_⟩
  intro z hz; exact leaf_5592_sound hz

theorem leaf_5598_ok : checkAt 527 1000 box_5598 cert_5598 = true := by
  have h := List.all_eq_true.mp batch_111_24_ok accepted_5598 (by simp [batch_111_24_values])
  exact h
theorem leaf_5598_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5598.profileLo box_5598.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5598_ok
theorem branch_box_5598_nonnegative : ∀ j, 0 ≤ branch_box_5598.lower j ∧ 0 ≤ branch_box_5598.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5598, Box.profileLo, Box.profileHi, box_5598]
theorem leaf_5598_BranchSafe : CertificateConsequences.BranchSafe branch_box_5598 := by
  left; refine ⟨branch_box_5598_nonnegative, ?_⟩
  intro z hz; exact leaf_5598_sound hz

theorem leaf_5599_ok : checkAt 527 1000 box_5599 cert_5599 = true := by
  have h := List.all_eq_true.mp batch_111_25_ok accepted_5599 (by simp [batch_111_25_values])
  exact h
theorem leaf_5599_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5599.profileLo box_5599.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5599_ok
theorem branch_box_5599_nonnegative : ∀ j, 0 ≤ branch_box_5599.lower j ∧ 0 ≤ branch_box_5599.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5599, Box.profileLo, Box.profileHi, box_5599]
theorem leaf_5599_BranchSafe : CertificateConsequences.BranchSafe branch_box_5599 := by
  left; refine ⟨branch_box_5599_nonnegative, ?_⟩
  intro z hz; exact leaf_5599_sound hz

#print axioms batch_111_00_ok
#print axioms leaf_5551_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
