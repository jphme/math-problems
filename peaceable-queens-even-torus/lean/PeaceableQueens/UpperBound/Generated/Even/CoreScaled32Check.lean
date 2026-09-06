import PeaceableQueens.UpperBound.Generated.Even.CoreScaled32Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_32_00_values : List Bool := [accepted_1605]
theorem batch_32_00_ok : batch_32_00_values.all id = true := by decide

def batch_32_01_values : List Bool := [accepted_1607]
theorem batch_32_01_ok : batch_32_01_values.all id = true := by decide

def batch_32_02_values : List Bool := [accepted_1609]
theorem batch_32_02_ok : batch_32_02_values.all id = true := by decide

def batch_32_03_values : List Bool := [accepted_1611]
theorem batch_32_03_ok : batch_32_03_values.all id = true := by decide

def batch_32_04_values : List Bool := [accepted_1617]
theorem batch_32_04_ok : batch_32_04_values.all id = true := by decide

def batch_32_05_values : List Bool := [accepted_1619]
theorem batch_32_05_ok : batch_32_05_values.all id = true := by decide

def batch_32_06_values : List Bool := [accepted_1626]
theorem batch_32_06_ok : batch_32_06_values.all id = true := by decide

def batch_32_07_values : List Bool := [accepted_1628]
theorem batch_32_07_ok : batch_32_07_values.all id = true := by decide

def batch_32_08_values : List Bool := [accepted_1629]
theorem batch_32_08_ok : batch_32_08_values.all id = true := by decide

def batch_32_09_values : List Bool := [accepted_1631]
theorem batch_32_09_ok : batch_32_09_values.all id = true := by decide

def batch_32_10_values : List Bool := [accepted_1635]
theorem batch_32_10_ok : batch_32_10_values.all id = true := by decide

def batch_32_11_values : List Bool := [accepted_1638]
theorem batch_32_11_ok : batch_32_11_values.all id = true := by decide

def batch_32_12_values : List Bool := [accepted_1640]
theorem batch_32_12_ok : batch_32_12_values.all id = true := by decide

def batch_32_13_values : List Bool := [accepted_1641]
theorem batch_32_13_ok : batch_32_13_values.all id = true := by decide

def batch_32_14_values : List Bool := [accepted_1643]
theorem batch_32_14_ok : batch_32_14_values.all id = true := by decide

def batch_32_15_values : List Bool := [accepted_1645]
theorem batch_32_15_ok : batch_32_15_values.all id = true := by decide

theorem leaf_1605_ok : checkAt 527 1000 box_1605 cert_1605 = true := by
  have h := List.all_eq_true.mp batch_32_00_ok accepted_1605 (by simp [batch_32_00_values])
  exact h
theorem leaf_1605_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1605.profileLo box_1605.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1605_ok
theorem branch_box_1605_nonnegative : ∀ j, 0 ≤ branch_box_1605.lower j ∧ 0 ≤ branch_box_1605.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1605, Box.profileLo, Box.profileHi, box_1605]
theorem leaf_1605_BranchSafe : CertificateConsequences.BranchSafe branch_box_1605 := by
  left; refine ⟨branch_box_1605_nonnegative, ?_⟩
  intro z hz; exact leaf_1605_sound hz

theorem leaf_1607_ok : checkAt 527 1000 box_1607 cert_1607 = true := by
  have h := List.all_eq_true.mp batch_32_01_ok accepted_1607 (by simp [batch_32_01_values])
  exact h
theorem leaf_1607_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1607.profileLo box_1607.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1607_ok
theorem branch_box_1607_nonnegative : ∀ j, 0 ≤ branch_box_1607.lower j ∧ 0 ≤ branch_box_1607.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1607, Box.profileLo, Box.profileHi, box_1607]
theorem leaf_1607_BranchSafe : CertificateConsequences.BranchSafe branch_box_1607 := by
  left; refine ⟨branch_box_1607_nonnegative, ?_⟩
  intro z hz; exact leaf_1607_sound hz

theorem leaf_1609_ok : checkAt 527 1000 box_1609 cert_1609 = true := by
  have h := List.all_eq_true.mp batch_32_02_ok accepted_1609 (by simp [batch_32_02_values])
  exact h
theorem leaf_1609_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1609.profileLo box_1609.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1609_ok
theorem branch_box_1609_nonnegative : ∀ j, 0 ≤ branch_box_1609.lower j ∧ 0 ≤ branch_box_1609.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1609, Box.profileLo, Box.profileHi, box_1609]
theorem leaf_1609_BranchSafe : CertificateConsequences.BranchSafe branch_box_1609 := by
  left; refine ⟨branch_box_1609_nonnegative, ?_⟩
  intro z hz; exact leaf_1609_sound hz

theorem leaf_1611_ok : checkAt 527 1000 box_1611 cert_1611 = true := by
  have h := List.all_eq_true.mp batch_32_03_ok accepted_1611 (by simp [batch_32_03_values])
  exact h
theorem leaf_1611_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1611.profileLo box_1611.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1611_ok
theorem branch_box_1611_nonnegative : ∀ j, 0 ≤ branch_box_1611.lower j ∧ 0 ≤ branch_box_1611.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1611, Box.profileLo, Box.profileHi, box_1611]
theorem leaf_1611_BranchSafe : CertificateConsequences.BranchSafe branch_box_1611 := by
  left; refine ⟨branch_box_1611_nonnegative, ?_⟩
  intro z hz; exact leaf_1611_sound hz

theorem leaf_1617_ok : checkAt 527 1000 box_1617 cert_1617 = true := by
  have h := List.all_eq_true.mp batch_32_04_ok accepted_1617 (by simp [batch_32_04_values])
  exact h
theorem leaf_1617_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1617.profileLo box_1617.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1617_ok
theorem branch_box_1617_nonnegative : ∀ j, 0 ≤ branch_box_1617.lower j ∧ 0 ≤ branch_box_1617.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1617, Box.profileLo, Box.profileHi, box_1617]
theorem leaf_1617_BranchSafe : CertificateConsequences.BranchSafe branch_box_1617 := by
  left; refine ⟨branch_box_1617_nonnegative, ?_⟩
  intro z hz; exact leaf_1617_sound hz

theorem leaf_1619_ok : checkAt 527 1000 box_1619 cert_1619 = true := by
  have h := List.all_eq_true.mp batch_32_05_ok accepted_1619 (by simp [batch_32_05_values])
  exact h
theorem leaf_1619_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1619.profileLo box_1619.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1619_ok
theorem branch_box_1619_nonnegative : ∀ j, 0 ≤ branch_box_1619.lower j ∧ 0 ≤ branch_box_1619.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1619, Box.profileLo, Box.profileHi, box_1619]
theorem leaf_1619_BranchSafe : CertificateConsequences.BranchSafe branch_box_1619 := by
  left; refine ⟨branch_box_1619_nonnegative, ?_⟩
  intro z hz; exact leaf_1619_sound hz

theorem leaf_1626_ok : checkAt 527 1000 box_1626 cert_1626 = true := by
  have h := List.all_eq_true.mp batch_32_06_ok accepted_1626 (by simp [batch_32_06_values])
  exact h
theorem leaf_1626_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1626.profileLo box_1626.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1626_ok
theorem branch_box_1626_nonnegative : ∀ j, 0 ≤ branch_box_1626.lower j ∧ 0 ≤ branch_box_1626.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1626, Box.profileLo, Box.profileHi, box_1626]
theorem leaf_1626_BranchSafe : CertificateConsequences.BranchSafe branch_box_1626 := by
  left; refine ⟨branch_box_1626_nonnegative, ?_⟩
  intro z hz; exact leaf_1626_sound hz

theorem leaf_1628_ok : checkAt 527 1000 box_1628 cert_1628 = true := by
  have h := List.all_eq_true.mp batch_32_07_ok accepted_1628 (by simp [batch_32_07_values])
  exact h
theorem leaf_1628_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1628.profileLo box_1628.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1628_ok
theorem branch_box_1628_nonnegative : ∀ j, 0 ≤ branch_box_1628.lower j ∧ 0 ≤ branch_box_1628.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1628, Box.profileLo, Box.profileHi, box_1628]
theorem leaf_1628_BranchSafe : CertificateConsequences.BranchSafe branch_box_1628 := by
  left; refine ⟨branch_box_1628_nonnegative, ?_⟩
  intro z hz; exact leaf_1628_sound hz

theorem leaf_1629_ok : checkAt 527 1000 box_1629 cert_1629 = true := by
  have h := List.all_eq_true.mp batch_32_08_ok accepted_1629 (by simp [batch_32_08_values])
  exact h
theorem leaf_1629_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1629.profileLo box_1629.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1629_ok
theorem branch_box_1629_nonnegative : ∀ j, 0 ≤ branch_box_1629.lower j ∧ 0 ≤ branch_box_1629.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1629, Box.profileLo, Box.profileHi, box_1629]
theorem leaf_1629_BranchSafe : CertificateConsequences.BranchSafe branch_box_1629 := by
  left; refine ⟨branch_box_1629_nonnegative, ?_⟩
  intro z hz; exact leaf_1629_sound hz

theorem leaf_1631_ok : checkAt 527 1000 box_1631 cert_1631 = true := by
  have h := List.all_eq_true.mp batch_32_09_ok accepted_1631 (by simp [batch_32_09_values])
  exact h
theorem leaf_1631_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1631.profileLo box_1631.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1631_ok
theorem branch_box_1631_nonnegative : ∀ j, 0 ≤ branch_box_1631.lower j ∧ 0 ≤ branch_box_1631.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1631, Box.profileLo, Box.profileHi, box_1631]
theorem leaf_1631_BranchSafe : CertificateConsequences.BranchSafe branch_box_1631 := by
  left; refine ⟨branch_box_1631_nonnegative, ?_⟩
  intro z hz; exact leaf_1631_sound hz

theorem leaf_1635_ok : checkAt 527 1000 box_1635 cert_1635 = true := by
  have h := List.all_eq_true.mp batch_32_10_ok accepted_1635 (by simp [batch_32_10_values])
  exact h
theorem leaf_1635_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1635.profileLo box_1635.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1635_ok
theorem branch_box_1635_nonnegative : ∀ j, 0 ≤ branch_box_1635.lower j ∧ 0 ≤ branch_box_1635.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1635, Box.profileLo, Box.profileHi, box_1635]
theorem leaf_1635_BranchSafe : CertificateConsequences.BranchSafe branch_box_1635 := by
  left; refine ⟨branch_box_1635_nonnegative, ?_⟩
  intro z hz; exact leaf_1635_sound hz

theorem leaf_1638_ok : checkAt 527 1000 box_1638 cert_1638 = true := by
  have h := List.all_eq_true.mp batch_32_11_ok accepted_1638 (by simp [batch_32_11_values])
  exact h
theorem leaf_1638_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1638.profileLo box_1638.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1638_ok
theorem branch_box_1638_nonnegative : ∀ j, 0 ≤ branch_box_1638.lower j ∧ 0 ≤ branch_box_1638.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1638, Box.profileLo, Box.profileHi, box_1638]
theorem leaf_1638_BranchSafe : CertificateConsequences.BranchSafe branch_box_1638 := by
  left; refine ⟨branch_box_1638_nonnegative, ?_⟩
  intro z hz; exact leaf_1638_sound hz

theorem leaf_1640_ok : checkAt 527 1000 box_1640 cert_1640 = true := by
  have h := List.all_eq_true.mp batch_32_12_ok accepted_1640 (by simp [batch_32_12_values])
  exact h
theorem leaf_1640_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1640.profileLo box_1640.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1640_ok
theorem branch_box_1640_nonnegative : ∀ j, 0 ≤ branch_box_1640.lower j ∧ 0 ≤ branch_box_1640.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1640, Box.profileLo, Box.profileHi, box_1640]
theorem leaf_1640_BranchSafe : CertificateConsequences.BranchSafe branch_box_1640 := by
  left; refine ⟨branch_box_1640_nonnegative, ?_⟩
  intro z hz; exact leaf_1640_sound hz

theorem leaf_1641_ok : checkAt 527 1000 box_1641 cert_1641 = true := by
  have h := List.all_eq_true.mp batch_32_13_ok accepted_1641 (by simp [batch_32_13_values])
  exact h
theorem leaf_1641_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1641.profileLo box_1641.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1641_ok
theorem branch_box_1641_nonnegative : ∀ j, 0 ≤ branch_box_1641.lower j ∧ 0 ≤ branch_box_1641.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1641, Box.profileLo, Box.profileHi, box_1641]
theorem leaf_1641_BranchSafe : CertificateConsequences.BranchSafe branch_box_1641 := by
  left; refine ⟨branch_box_1641_nonnegative, ?_⟩
  intro z hz; exact leaf_1641_sound hz

theorem leaf_1643_ok : checkAt 527 1000 box_1643 cert_1643 = true := by
  have h := List.all_eq_true.mp batch_32_14_ok accepted_1643 (by simp [batch_32_14_values])
  exact h
theorem leaf_1643_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1643.profileLo box_1643.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1643_ok
theorem branch_box_1643_nonnegative : ∀ j, 0 ≤ branch_box_1643.lower j ∧ 0 ≤ branch_box_1643.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1643, Box.profileLo, Box.profileHi, box_1643]
theorem leaf_1643_BranchSafe : CertificateConsequences.BranchSafe branch_box_1643 := by
  left; refine ⟨branch_box_1643_nonnegative, ?_⟩
  intro z hz; exact leaf_1643_sound hz

theorem leaf_1645_ok : checkAt 527 1000 box_1645 cert_1645 = true := by
  have h := List.all_eq_true.mp batch_32_15_ok accepted_1645 (by simp [batch_32_15_values])
  exact h
theorem leaf_1645_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1645.profileLo box_1645.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1645_ok
theorem branch_box_1645_nonnegative : ∀ j, 0 ≤ branch_box_1645.lower j ∧ 0 ≤ branch_box_1645.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1645, Box.profileLo, Box.profileHi, box_1645]
theorem leaf_1645_BranchSafe : CertificateConsequences.BranchSafe branch_box_1645 := by
  left; refine ⟨branch_box_1645_nonnegative, ?_⟩
  intro z hz; exact leaf_1645_sound hz

#print axioms batch_32_00_ok
#print axioms leaf_1605_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
