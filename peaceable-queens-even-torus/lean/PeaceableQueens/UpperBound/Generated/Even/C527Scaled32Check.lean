import PeaceableQueens.UpperBound.Generated.Even.C527Scaled32Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_32_00_values : List Bool := [accepted_1600]
theorem batch_32_00_ok : batch_32_00_values.all id = true := by decide

def batch_32_01_values : List Bool := [accepted_1606]
theorem batch_32_01_ok : batch_32_01_values.all id = true := by decide

def batch_32_02_values : List Bool := [accepted_1607]
theorem batch_32_02_ok : batch_32_02_values.all id = true := by decide

def batch_32_03_values : List Bool := [accepted_1608]
theorem batch_32_03_ok : batch_32_03_values.all id = true := by decide

def batch_32_04_values : List Bool := [accepted_1611]
theorem batch_32_04_ok : batch_32_04_values.all id = true := by decide

def batch_32_05_values : List Bool := [accepted_1612]
theorem batch_32_05_ok : batch_32_05_values.all id = true := by decide

def batch_32_06_values : List Bool := [accepted_1614]
theorem batch_32_06_ok : batch_32_06_values.all id = true := by decide

def batch_32_07_values : List Bool := [accepted_1616]
theorem batch_32_07_ok : batch_32_07_values.all id = true := by decide

def batch_32_08_values : List Bool := [accepted_1617]
theorem batch_32_08_ok : batch_32_08_values.all id = true := by decide

def batch_32_09_values : List Bool := [accepted_1619]
theorem batch_32_09_ok : batch_32_09_values.all id = true := by decide

def batch_32_10_values : List Bool := [accepted_1620]
theorem batch_32_10_ok : batch_32_10_values.all id = true := by decide

def batch_32_11_values : List Bool := [accepted_1623]
theorem batch_32_11_ok : batch_32_11_values.all id = true := by decide

def batch_32_12_values : List Bool := [accepted_1624]
theorem batch_32_12_ok : batch_32_12_values.all id = true := by decide

def batch_32_13_values : List Bool := [accepted_1625]
theorem batch_32_13_ok : batch_32_13_values.all id = true := by decide

def batch_32_14_values : List Bool := [accepted_1628]
theorem batch_32_14_ok : batch_32_14_values.all id = true := by decide

def batch_32_15_values : List Bool := [accepted_1631]
theorem batch_32_15_ok : batch_32_15_values.all id = true := by decide

def batch_32_16_values : List Bool := [accepted_1632]
theorem batch_32_16_ok : batch_32_16_values.all id = true := by decide

def batch_32_17_values : List Bool := [accepted_1634]
theorem batch_32_17_ok : batch_32_17_values.all id = true := by decide

def batch_32_18_values : List Bool := [accepted_1635]
theorem batch_32_18_ok : batch_32_18_values.all id = true := by decide

def batch_32_19_values : List Bool := [accepted_1637]
theorem batch_32_19_ok : batch_32_19_values.all id = true := by decide

def batch_32_20_values : List Bool := [accepted_1638]
theorem batch_32_20_ok : batch_32_20_values.all id = true := by decide

def batch_32_21_values : List Bool := [accepted_1646]
theorem batch_32_21_ok : batch_32_21_values.all id = true := by decide

def batch_32_22_values : List Bool := [accepted_1649]
theorem batch_32_22_ok : batch_32_22_values.all id = true := by decide

theorem leaf_1600_ok : checkAt 527 1000 box_1600 cert_1600 = true := by
  have h := List.all_eq_true.mp batch_32_00_ok accepted_1600 (by simp [batch_32_00_values])
  exact h
theorem leaf_1600_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1600.profileLo box_1600.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1600_ok
theorem branch_box_1600_nonnegative : ∀ j, 0 ≤ branch_box_1600.lower j ∧ 0 ≤ branch_box_1600.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1600, Box.profileLo, Box.profileHi, box_1600]
theorem leaf_1600_BranchSafe : CertificateConsequences.BranchSafe branch_box_1600 := by
  left; refine ⟨branch_box_1600_nonnegative, ?_⟩
  intro z hz; exact leaf_1600_sound hz

theorem leaf_1606_ok : checkAt 527 1000 box_1606 cert_1606 = true := by
  have h := List.all_eq_true.mp batch_32_01_ok accepted_1606 (by simp [batch_32_01_values])
  exact h
theorem leaf_1606_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1606.profileLo box_1606.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1606_ok
theorem branch_box_1606_nonnegative : ∀ j, 0 ≤ branch_box_1606.lower j ∧ 0 ≤ branch_box_1606.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1606, Box.profileLo, Box.profileHi, box_1606]
theorem leaf_1606_BranchSafe : CertificateConsequences.BranchSafe branch_box_1606 := by
  left; refine ⟨branch_box_1606_nonnegative, ?_⟩
  intro z hz; exact leaf_1606_sound hz

theorem leaf_1607_ok : checkAt 527 1000 box_1607 cert_1607 = true := by
  have h := List.all_eq_true.mp batch_32_02_ok accepted_1607 (by simp [batch_32_02_values])
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

theorem leaf_1608_ok : checkAt 527 1000 box_1608 cert_1608 = true := by
  have h := List.all_eq_true.mp batch_32_03_ok accepted_1608 (by simp [batch_32_03_values])
  exact h
theorem leaf_1608_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1608.profileLo box_1608.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1608_ok
theorem branch_box_1608_nonnegative : ∀ j, 0 ≤ branch_box_1608.lower j ∧ 0 ≤ branch_box_1608.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1608, Box.profileLo, Box.profileHi, box_1608]
theorem leaf_1608_BranchSafe : CertificateConsequences.BranchSafe branch_box_1608 := by
  left; refine ⟨branch_box_1608_nonnegative, ?_⟩
  intro z hz; exact leaf_1608_sound hz

theorem leaf_1611_ok : checkAt 527 1000 box_1611 cert_1611 = true := by
  have h := List.all_eq_true.mp batch_32_04_ok accepted_1611 (by simp [batch_32_04_values])
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

theorem leaf_1612_ok : checkAt 527 1000 box_1612 cert_1612 = true := by
  have h := List.all_eq_true.mp batch_32_05_ok accepted_1612 (by simp [batch_32_05_values])
  exact h
theorem leaf_1612_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1612.profileLo box_1612.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1612_ok
theorem branch_box_1612_nonnegative : ∀ j, 0 ≤ branch_box_1612.lower j ∧ 0 ≤ branch_box_1612.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1612, Box.profileLo, Box.profileHi, box_1612]
theorem leaf_1612_BranchSafe : CertificateConsequences.BranchSafe branch_box_1612 := by
  left; refine ⟨branch_box_1612_nonnegative, ?_⟩
  intro z hz; exact leaf_1612_sound hz

theorem leaf_1614_ok : checkAt 527 1000 box_1614 cert_1614 = true := by
  have h := List.all_eq_true.mp batch_32_06_ok accepted_1614 (by simp [batch_32_06_values])
  exact h
theorem leaf_1614_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1614.profileLo box_1614.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1614_ok
theorem branch_box_1614_nonnegative : ∀ j, 0 ≤ branch_box_1614.lower j ∧ 0 ≤ branch_box_1614.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1614, Box.profileLo, Box.profileHi, box_1614]
theorem leaf_1614_BranchSafe : CertificateConsequences.BranchSafe branch_box_1614 := by
  left; refine ⟨branch_box_1614_nonnegative, ?_⟩
  intro z hz; exact leaf_1614_sound hz

theorem leaf_1616_ok : checkAt 527 1000 box_1616 cert_1616 = true := by
  have h := List.all_eq_true.mp batch_32_07_ok accepted_1616 (by simp [batch_32_07_values])
  exact h
theorem leaf_1616_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1616.profileLo box_1616.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1616_ok
theorem branch_box_1616_nonnegative : ∀ j, 0 ≤ branch_box_1616.lower j ∧ 0 ≤ branch_box_1616.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1616, Box.profileLo, Box.profileHi, box_1616]
theorem leaf_1616_BranchSafe : CertificateConsequences.BranchSafe branch_box_1616 := by
  left; refine ⟨branch_box_1616_nonnegative, ?_⟩
  intro z hz; exact leaf_1616_sound hz

theorem leaf_1617_ok : checkAt 527 1000 box_1617 cert_1617 = true := by
  have h := List.all_eq_true.mp batch_32_08_ok accepted_1617 (by simp [batch_32_08_values])
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
  have h := List.all_eq_true.mp batch_32_09_ok accepted_1619 (by simp [batch_32_09_values])
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

theorem leaf_1620_ok : checkAt 527 1000 box_1620 cert_1620 = true := by
  have h := List.all_eq_true.mp batch_32_10_ok accepted_1620 (by simp [batch_32_10_values])
  exact h
theorem leaf_1620_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1620.profileLo box_1620.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1620_ok
theorem branch_box_1620_nonnegative : ∀ j, 0 ≤ branch_box_1620.lower j ∧ 0 ≤ branch_box_1620.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1620, Box.profileLo, Box.profileHi, box_1620]
theorem leaf_1620_BranchSafe : CertificateConsequences.BranchSafe branch_box_1620 := by
  left; refine ⟨branch_box_1620_nonnegative, ?_⟩
  intro z hz; exact leaf_1620_sound hz

theorem leaf_1623_ok : checkAt 527 1000 box_1623 cert_1623 = true := by
  have h := List.all_eq_true.mp batch_32_11_ok accepted_1623 (by simp [batch_32_11_values])
  exact h
theorem leaf_1623_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1623.profileLo box_1623.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1623_ok
theorem branch_box_1623_nonnegative : ∀ j, 0 ≤ branch_box_1623.lower j ∧ 0 ≤ branch_box_1623.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1623, Box.profileLo, Box.profileHi, box_1623]
theorem leaf_1623_BranchSafe : CertificateConsequences.BranchSafe branch_box_1623 := by
  left; refine ⟨branch_box_1623_nonnegative, ?_⟩
  intro z hz; exact leaf_1623_sound hz

theorem leaf_1624_ok : checkAt 527 1000 box_1624 cert_1624 = true := by
  have h := List.all_eq_true.mp batch_32_12_ok accepted_1624 (by simp [batch_32_12_values])
  exact h
theorem leaf_1624_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1624.profileLo box_1624.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1624_ok
theorem branch_box_1624_nonnegative : ∀ j, 0 ≤ branch_box_1624.lower j ∧ 0 ≤ branch_box_1624.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1624, Box.profileLo, Box.profileHi, box_1624]
theorem leaf_1624_BranchSafe : CertificateConsequences.BranchSafe branch_box_1624 := by
  left; refine ⟨branch_box_1624_nonnegative, ?_⟩
  intro z hz; exact leaf_1624_sound hz

theorem leaf_1625_ok : checkAt 527 1000 box_1625 cert_1625 = true := by
  have h := List.all_eq_true.mp batch_32_13_ok accepted_1625 (by simp [batch_32_13_values])
  exact h
theorem leaf_1625_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1625.profileLo box_1625.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1625_ok
theorem branch_box_1625_nonnegative : ∀ j, 0 ≤ branch_box_1625.lower j ∧ 0 ≤ branch_box_1625.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1625, Box.profileLo, Box.profileHi, box_1625]
theorem leaf_1625_BranchSafe : CertificateConsequences.BranchSafe branch_box_1625 := by
  left; refine ⟨branch_box_1625_nonnegative, ?_⟩
  intro z hz; exact leaf_1625_sound hz

theorem leaf_1628_ok : checkAt 527 1000 box_1628 cert_1628 = true := by
  have h := List.all_eq_true.mp batch_32_14_ok accepted_1628 (by simp [batch_32_14_values])
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

theorem leaf_1631_ok : checkAt 527 1000 box_1631 cert_1631 = true := by
  have h := List.all_eq_true.mp batch_32_15_ok accepted_1631 (by simp [batch_32_15_values])
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

theorem leaf_1632_ok : checkAt 527 1000 box_1632 cert_1632 = true := by
  have h := List.all_eq_true.mp batch_32_16_ok accepted_1632 (by simp [batch_32_16_values])
  exact h
theorem leaf_1632_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1632.profileLo box_1632.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1632_ok
theorem branch_box_1632_nonnegative : ∀ j, 0 ≤ branch_box_1632.lower j ∧ 0 ≤ branch_box_1632.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1632, Box.profileLo, Box.profileHi, box_1632]
theorem leaf_1632_BranchSafe : CertificateConsequences.BranchSafe branch_box_1632 := by
  left; refine ⟨branch_box_1632_nonnegative, ?_⟩
  intro z hz; exact leaf_1632_sound hz

theorem leaf_1634_ok : checkAt 527 1000 box_1634 cert_1634 = true := by
  have h := List.all_eq_true.mp batch_32_17_ok accepted_1634 (by simp [batch_32_17_values])
  exact h
theorem leaf_1634_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1634.profileLo box_1634.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1634_ok
theorem branch_box_1634_nonnegative : ∀ j, 0 ≤ branch_box_1634.lower j ∧ 0 ≤ branch_box_1634.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1634, Box.profileLo, Box.profileHi, box_1634]
theorem leaf_1634_BranchSafe : CertificateConsequences.BranchSafe branch_box_1634 := by
  left; refine ⟨branch_box_1634_nonnegative, ?_⟩
  intro z hz; exact leaf_1634_sound hz

theorem leaf_1635_ok : checkAt 527 1000 box_1635 cert_1635 = true := by
  have h := List.all_eq_true.mp batch_32_18_ok accepted_1635 (by simp [batch_32_18_values])
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

theorem leaf_1637_ok : checkAt 527 1000 box_1637 cert_1637 = true := by
  have h := List.all_eq_true.mp batch_32_19_ok accepted_1637 (by simp [batch_32_19_values])
  exact h
theorem leaf_1637_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1637.profileLo box_1637.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1637_ok
theorem branch_box_1637_nonnegative : ∀ j, 0 ≤ branch_box_1637.lower j ∧ 0 ≤ branch_box_1637.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1637, Box.profileLo, Box.profileHi, box_1637]
theorem leaf_1637_BranchSafe : CertificateConsequences.BranchSafe branch_box_1637 := by
  left; refine ⟨branch_box_1637_nonnegative, ?_⟩
  intro z hz; exact leaf_1637_sound hz

theorem leaf_1638_ok : checkAt 527 1000 box_1638 cert_1638 = true := by
  have h := List.all_eq_true.mp batch_32_20_ok accepted_1638 (by simp [batch_32_20_values])
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

theorem leaf_1646_ok : checkAt 527 1000 box_1646 cert_1646 = true := by
  have h := List.all_eq_true.mp batch_32_21_ok accepted_1646 (by simp [batch_32_21_values])
  exact h
theorem leaf_1646_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1646.profileLo box_1646.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1646_ok
theorem branch_box_1646_nonnegative : ∀ j, 0 ≤ branch_box_1646.lower j ∧ 0 ≤ branch_box_1646.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1646, Box.profileLo, Box.profileHi, box_1646]
theorem leaf_1646_BranchSafe : CertificateConsequences.BranchSafe branch_box_1646 := by
  left; refine ⟨branch_box_1646_nonnegative, ?_⟩
  intro z hz; exact leaf_1646_sound hz

theorem leaf_1649_ok : checkAt 527 1000 box_1649 cert_1649 = true := by
  have h := List.all_eq_true.mp batch_32_22_ok accepted_1649 (by simp [batch_32_22_values])
  exact h
theorem leaf_1649_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1649.profileLo box_1649.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1649_ok
theorem branch_box_1649_nonnegative : ∀ j, 0 ≤ branch_box_1649.lower j ∧ 0 ≤ branch_box_1649.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1649, Box.profileLo, Box.profileHi, box_1649]
theorem leaf_1649_BranchSafe : CertificateConsequences.BranchSafe branch_box_1649 := by
  left; refine ⟨branch_box_1649_nonnegative, ?_⟩
  intro z hz; exact leaf_1649_sound hz

#print axioms batch_32_00_ok
#print axioms leaf_1600_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
