import PeaceableQueens.UpperBound.Generated.Even.C527Scaled131Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_131_00_values : List Bool := [accepted_6552]
theorem batch_131_00_ok : batch_131_00_values.all id = true := by decide

def batch_131_01_values : List Bool := [accepted_6553]
theorem batch_131_01_ok : batch_131_01_values.all id = true := by decide

def batch_131_02_values : List Bool := [accepted_6554]
theorem batch_131_02_ok : batch_131_02_values.all id = true := by decide

def batch_131_03_values : List Bool := [accepted_6557]
theorem batch_131_03_ok : batch_131_03_values.all id = true := by decide

def batch_131_04_values : List Bool := [accepted_6559]
theorem batch_131_04_ok : batch_131_04_values.all id = true := by decide

def batch_131_05_values : List Bool := [accepted_6565]
theorem batch_131_05_ok : batch_131_05_values.all id = true := by decide

def batch_131_06_values : List Bool := [accepted_6576]
theorem batch_131_06_ok : batch_131_06_values.all id = true := by decide

def batch_131_07_values : List Bool := [accepted_6578]
theorem batch_131_07_ok : batch_131_07_values.all id = true := by decide

def batch_131_08_values : List Bool := [accepted_6581]
theorem batch_131_08_ok : batch_131_08_values.all id = true := by decide

def batch_131_09_values : List Bool := [accepted_6583]
theorem batch_131_09_ok : batch_131_09_values.all id = true := by decide

def batch_131_10_values : List Bool := [accepted_6585]
theorem batch_131_10_ok : batch_131_10_values.all id = true := by decide

def batch_131_11_values : List Bool := [accepted_6587]
theorem batch_131_11_ok : batch_131_11_values.all id = true := by decide

def batch_131_12_values : List Bool := [accepted_6588]
theorem batch_131_12_ok : batch_131_12_values.all id = true := by decide

def batch_131_13_values : List Bool := [accepted_6595]
theorem batch_131_13_ok : batch_131_13_values.all id = true := by decide

def batch_131_14_values : List Bool := [accepted_6597]
theorem batch_131_14_ok : batch_131_14_values.all id = true := by decide

def batch_131_15_values : List Bool := [accepted_6598]
theorem batch_131_15_ok : batch_131_15_values.all id = true := by decide

theorem leaf_6552_ok : checkAt 527 1000 box_6552 cert_6552 = true := by
  have h := List.all_eq_true.mp batch_131_00_ok accepted_6552 (by simp [batch_131_00_values])
  exact h
theorem leaf_6552_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6552.profileLo box_6552.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6552_ok
theorem branch_box_6552_nonnegative : ∀ j, 0 ≤ branch_box_6552.lower j ∧ 0 ≤ branch_box_6552.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6552, Box.profileLo, Box.profileHi, box_6552]
theorem leaf_6552_BranchSafe : CertificateConsequences.BranchSafe branch_box_6552 := by
  left; refine ⟨branch_box_6552_nonnegative, ?_⟩
  intro z hz; exact leaf_6552_sound hz

theorem leaf_6553_ok : checkAt 527 1000 box_6553 cert_6553 = true := by
  have h := List.all_eq_true.mp batch_131_01_ok accepted_6553 (by simp [batch_131_01_values])
  exact h
theorem leaf_6553_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6553.profileLo box_6553.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6553_ok
theorem branch_box_6553_nonnegative : ∀ j, 0 ≤ branch_box_6553.lower j ∧ 0 ≤ branch_box_6553.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6553, Box.profileLo, Box.profileHi, box_6553]
theorem leaf_6553_BranchSafe : CertificateConsequences.BranchSafe branch_box_6553 := by
  left; refine ⟨branch_box_6553_nonnegative, ?_⟩
  intro z hz; exact leaf_6553_sound hz

theorem leaf_6554_ok : checkAt 527 1000 box_6554 cert_6554 = true := by
  have h := List.all_eq_true.mp batch_131_02_ok accepted_6554 (by simp [batch_131_02_values])
  exact h
theorem leaf_6554_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6554.profileLo box_6554.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6554_ok
theorem branch_box_6554_nonnegative : ∀ j, 0 ≤ branch_box_6554.lower j ∧ 0 ≤ branch_box_6554.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6554, Box.profileLo, Box.profileHi, box_6554]
theorem leaf_6554_BranchSafe : CertificateConsequences.BranchSafe branch_box_6554 := by
  left; refine ⟨branch_box_6554_nonnegative, ?_⟩
  intro z hz; exact leaf_6554_sound hz

theorem leaf_6557_ok : checkAt 527 1000 box_6557 cert_6557 = true := by
  have h := List.all_eq_true.mp batch_131_03_ok accepted_6557 (by simp [batch_131_03_values])
  exact h
theorem leaf_6557_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6557.profileLo box_6557.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6557_ok
theorem branch_box_6557_nonnegative : ∀ j, 0 ≤ branch_box_6557.lower j ∧ 0 ≤ branch_box_6557.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6557, Box.profileLo, Box.profileHi, box_6557]
theorem leaf_6557_BranchSafe : CertificateConsequences.BranchSafe branch_box_6557 := by
  left; refine ⟨branch_box_6557_nonnegative, ?_⟩
  intro z hz; exact leaf_6557_sound hz

theorem leaf_6559_ok : checkAt 527 1000 box_6559 cert_6559 = true := by
  have h := List.all_eq_true.mp batch_131_04_ok accepted_6559 (by simp [batch_131_04_values])
  exact h
theorem leaf_6559_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6559.profileLo box_6559.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6559_ok
theorem branch_box_6559_nonnegative : ∀ j, 0 ≤ branch_box_6559.lower j ∧ 0 ≤ branch_box_6559.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6559, Box.profileLo, Box.profileHi, box_6559]
theorem leaf_6559_BranchSafe : CertificateConsequences.BranchSafe branch_box_6559 := by
  left; refine ⟨branch_box_6559_nonnegative, ?_⟩
  intro z hz; exact leaf_6559_sound hz

theorem leaf_6565_ok : checkAt 527 1000 box_6565 cert_6565 = true := by
  have h := List.all_eq_true.mp batch_131_05_ok accepted_6565 (by simp [batch_131_05_values])
  exact h
theorem leaf_6565_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6565.profileLo box_6565.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6565_ok
theorem branch_box_6565_nonnegative : ∀ j, 0 ≤ branch_box_6565.lower j ∧ 0 ≤ branch_box_6565.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6565, Box.profileLo, Box.profileHi, box_6565]
theorem leaf_6565_BranchSafe : CertificateConsequences.BranchSafe branch_box_6565 := by
  left; refine ⟨branch_box_6565_nonnegative, ?_⟩
  intro z hz; exact leaf_6565_sound hz

theorem leaf_6576_ok : checkAt 527 1000 box_6576 cert_6576 = true := by
  have h := List.all_eq_true.mp batch_131_06_ok accepted_6576 (by simp [batch_131_06_values])
  exact h
theorem leaf_6576_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6576.profileLo box_6576.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6576_ok
theorem branch_box_6576_nonnegative : ∀ j, 0 ≤ branch_box_6576.lower j ∧ 0 ≤ branch_box_6576.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6576, Box.profileLo, Box.profileHi, box_6576]
theorem leaf_6576_BranchSafe : CertificateConsequences.BranchSafe branch_box_6576 := by
  left; refine ⟨branch_box_6576_nonnegative, ?_⟩
  intro z hz; exact leaf_6576_sound hz

theorem leaf_6578_ok : checkAt 527 1000 box_6578 cert_6578 = true := by
  have h := List.all_eq_true.mp batch_131_07_ok accepted_6578 (by simp [batch_131_07_values])
  exact h
theorem leaf_6578_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6578.profileLo box_6578.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6578_ok
theorem branch_box_6578_nonnegative : ∀ j, 0 ≤ branch_box_6578.lower j ∧ 0 ≤ branch_box_6578.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6578, Box.profileLo, Box.profileHi, box_6578]
theorem leaf_6578_BranchSafe : CertificateConsequences.BranchSafe branch_box_6578 := by
  left; refine ⟨branch_box_6578_nonnegative, ?_⟩
  intro z hz; exact leaf_6578_sound hz

theorem leaf_6581_ok : checkAt 527 1000 box_6581 cert_6581 = true := by
  have h := List.all_eq_true.mp batch_131_08_ok accepted_6581 (by simp [batch_131_08_values])
  exact h
theorem leaf_6581_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6581.profileLo box_6581.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6581_ok
theorem branch_box_6581_nonnegative : ∀ j, 0 ≤ branch_box_6581.lower j ∧ 0 ≤ branch_box_6581.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6581, Box.profileLo, Box.profileHi, box_6581]
theorem leaf_6581_BranchSafe : CertificateConsequences.BranchSafe branch_box_6581 := by
  left; refine ⟨branch_box_6581_nonnegative, ?_⟩
  intro z hz; exact leaf_6581_sound hz

theorem leaf_6583_ok : checkAt 527 1000 box_6583 cert_6583 = true := by
  have h := List.all_eq_true.mp batch_131_09_ok accepted_6583 (by simp [batch_131_09_values])
  exact h
theorem leaf_6583_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6583.profileLo box_6583.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6583_ok
theorem branch_box_6583_nonnegative : ∀ j, 0 ≤ branch_box_6583.lower j ∧ 0 ≤ branch_box_6583.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6583, Box.profileLo, Box.profileHi, box_6583]
theorem leaf_6583_BranchSafe : CertificateConsequences.BranchSafe branch_box_6583 := by
  left; refine ⟨branch_box_6583_nonnegative, ?_⟩
  intro z hz; exact leaf_6583_sound hz

theorem leaf_6585_ok : checkAt 527 1000 box_6585 cert_6585 = true := by
  have h := List.all_eq_true.mp batch_131_10_ok accepted_6585 (by simp [batch_131_10_values])
  exact h
theorem leaf_6585_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6585.profileLo box_6585.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6585_ok
theorem branch_box_6585_nonnegative : ∀ j, 0 ≤ branch_box_6585.lower j ∧ 0 ≤ branch_box_6585.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6585, Box.profileLo, Box.profileHi, box_6585]
theorem leaf_6585_BranchSafe : CertificateConsequences.BranchSafe branch_box_6585 := by
  left; refine ⟨branch_box_6585_nonnegative, ?_⟩
  intro z hz; exact leaf_6585_sound hz

theorem leaf_6587_ok : checkAt 527 1000 box_6587 cert_6587 = true := by
  have h := List.all_eq_true.mp batch_131_11_ok accepted_6587 (by simp [batch_131_11_values])
  exact h
theorem leaf_6587_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6587.profileLo box_6587.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6587_ok
theorem branch_box_6587_nonnegative : ∀ j, 0 ≤ branch_box_6587.lower j ∧ 0 ≤ branch_box_6587.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6587, Box.profileLo, Box.profileHi, box_6587]
theorem leaf_6587_BranchSafe : CertificateConsequences.BranchSafe branch_box_6587 := by
  left; refine ⟨branch_box_6587_nonnegative, ?_⟩
  intro z hz; exact leaf_6587_sound hz

theorem leaf_6588_ok : checkAt 527 1000 box_6588 cert_6588 = true := by
  have h := List.all_eq_true.mp batch_131_12_ok accepted_6588 (by simp [batch_131_12_values])
  exact h
theorem leaf_6588_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6588.profileLo box_6588.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6588_ok
theorem branch_box_6588_nonnegative : ∀ j, 0 ≤ branch_box_6588.lower j ∧ 0 ≤ branch_box_6588.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6588, Box.profileLo, Box.profileHi, box_6588]
theorem leaf_6588_BranchSafe : CertificateConsequences.BranchSafe branch_box_6588 := by
  left; refine ⟨branch_box_6588_nonnegative, ?_⟩
  intro z hz; exact leaf_6588_sound hz

theorem leaf_6595_ok : checkAt 527 1000 box_6595 cert_6595 = true := by
  have h := List.all_eq_true.mp batch_131_13_ok accepted_6595 (by simp [batch_131_13_values])
  exact h
theorem leaf_6595_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6595.profileLo box_6595.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6595_ok
theorem branch_box_6595_nonnegative : ∀ j, 0 ≤ branch_box_6595.lower j ∧ 0 ≤ branch_box_6595.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6595, Box.profileLo, Box.profileHi, box_6595]
theorem leaf_6595_BranchSafe : CertificateConsequences.BranchSafe branch_box_6595 := by
  left; refine ⟨branch_box_6595_nonnegative, ?_⟩
  intro z hz; exact leaf_6595_sound hz

theorem leaf_6597_ok : checkAt 527 1000 box_6597 cert_6597 = true := by
  have h := List.all_eq_true.mp batch_131_14_ok accepted_6597 (by simp [batch_131_14_values])
  exact h
theorem leaf_6597_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6597.profileLo box_6597.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6597_ok
theorem branch_box_6597_nonnegative : ∀ j, 0 ≤ branch_box_6597.lower j ∧ 0 ≤ branch_box_6597.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6597, Box.profileLo, Box.profileHi, box_6597]
theorem leaf_6597_BranchSafe : CertificateConsequences.BranchSafe branch_box_6597 := by
  left; refine ⟨branch_box_6597_nonnegative, ?_⟩
  intro z hz; exact leaf_6597_sound hz

theorem leaf_6598_ok : checkAt 527 1000 box_6598 cert_6598 = true := by
  have h := List.all_eq_true.mp batch_131_15_ok accepted_6598 (by simp [batch_131_15_values])
  exact h
theorem leaf_6598_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6598.profileLo box_6598.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6598_ok
theorem branch_box_6598_nonnegative : ∀ j, 0 ≤ branch_box_6598.lower j ∧ 0 ≤ branch_box_6598.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6598, Box.profileLo, Box.profileHi, box_6598]
theorem leaf_6598_BranchSafe : CertificateConsequences.BranchSafe branch_box_6598 := by
  left; refine ⟨branch_box_6598_nonnegative, ?_⟩
  intro z hz; exact leaf_6598_sound hz

#print axioms batch_131_00_ok
#print axioms leaf_6552_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
