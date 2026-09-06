import PeaceableQueens.UpperBound.Generated.Even.C527Scaled33Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_33_00_values : List Bool := [accepted_1650]
theorem batch_33_00_ok : batch_33_00_values.all id = true := by decide

def batch_33_01_values : List Bool := [accepted_1651]
theorem batch_33_01_ok : batch_33_01_values.all id = true := by decide

def batch_33_02_values : List Bool := [accepted_1652]
theorem batch_33_02_ok : batch_33_02_values.all id = true := by decide

def batch_33_03_values : List Bool := [accepted_1654]
theorem batch_33_03_ok : batch_33_03_values.all id = true := by decide

def batch_33_04_values : List Bool := [accepted_1655]
theorem batch_33_04_ok : batch_33_04_values.all id = true := by decide

def batch_33_05_values : List Bool := [accepted_1656]
theorem batch_33_05_ok : batch_33_05_values.all id = true := by decide

def batch_33_06_values : List Bool := [accepted_1663]
theorem batch_33_06_ok : batch_33_06_values.all id = true := by decide

def batch_33_07_values : List Bool := [accepted_1664]
theorem batch_33_07_ok : batch_33_07_values.all id = true := by decide

def batch_33_08_values : List Bool := [accepted_1665]
theorem batch_33_08_ok : batch_33_08_values.all id = true := by decide

def batch_33_09_values : List Bool := [accepted_1666]
theorem batch_33_09_ok : batch_33_09_values.all id = true := by decide

def batch_33_10_values : List Bool := [accepted_1671]
theorem batch_33_10_ok : batch_33_10_values.all id = true := by decide

def batch_33_11_values : List Bool := [accepted_1673]
theorem batch_33_11_ok : batch_33_11_values.all id = true := by decide

def batch_33_12_values : List Bool := [accepted_1674]
theorem batch_33_12_ok : batch_33_12_values.all id = true := by decide

def batch_33_13_values : List Bool := [accepted_1675]
theorem batch_33_13_ok : batch_33_13_values.all id = true := by decide

def batch_33_14_values : List Bool := [accepted_1677]
theorem batch_33_14_ok : batch_33_14_values.all id = true := by decide

def batch_33_15_values : List Bool := [accepted_1678]
theorem batch_33_15_ok : batch_33_15_values.all id = true := by decide

def batch_33_16_values : List Bool := [accepted_1683]
theorem batch_33_16_ok : batch_33_16_values.all id = true := by decide

def batch_33_17_values : List Bool := [accepted_1684]
theorem batch_33_17_ok : batch_33_17_values.all id = true := by decide

def batch_33_18_values : List Bool := [accepted_1686]
theorem batch_33_18_ok : batch_33_18_values.all id = true := by decide

def batch_33_19_values : List Bool := [accepted_1689]
theorem batch_33_19_ok : batch_33_19_values.all id = true := by decide

def batch_33_20_values : List Bool := [accepted_1690]
theorem batch_33_20_ok : batch_33_20_values.all id = true := by decide

def batch_33_21_values : List Bool := [accepted_1691]
theorem batch_33_21_ok : batch_33_21_values.all id = true := by decide

def batch_33_22_values : List Bool := [accepted_1692]
theorem batch_33_22_ok : batch_33_22_values.all id = true := by decide

def batch_33_23_values : List Bool := [accepted_1697]
theorem batch_33_23_ok : batch_33_23_values.all id = true := by decide

def batch_33_24_values : List Bool := [accepted_1698]
theorem batch_33_24_ok : batch_33_24_values.all id = true := by decide

def batch_33_25_values : List Bool := [accepted_1699]
theorem batch_33_25_ok : batch_33_25_values.all id = true := by decide

theorem leaf_1650_ok : checkAt 527 1000 box_1650 cert_1650 = true := by
  have h := List.all_eq_true.mp batch_33_00_ok accepted_1650 (by simp [batch_33_00_values])
  exact h
theorem leaf_1650_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1650.profileLo box_1650.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1650_ok
theorem branch_box_1650_nonnegative : ∀ j, 0 ≤ branch_box_1650.lower j ∧ 0 ≤ branch_box_1650.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1650, Box.profileLo, Box.profileHi, box_1650]
theorem leaf_1650_BranchSafe : CertificateConsequences.BranchSafe branch_box_1650 := by
  left; refine ⟨branch_box_1650_nonnegative, ?_⟩
  intro z hz; exact leaf_1650_sound hz

theorem leaf_1651_ok : checkAt 527 1000 box_1651 cert_1651 = true := by
  have h := List.all_eq_true.mp batch_33_01_ok accepted_1651 (by simp [batch_33_01_values])
  exact h
theorem leaf_1651_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1651.profileLo box_1651.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1651_ok
theorem branch_box_1651_nonnegative : ∀ j, 0 ≤ branch_box_1651.lower j ∧ 0 ≤ branch_box_1651.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1651, Box.profileLo, Box.profileHi, box_1651]
theorem leaf_1651_BranchSafe : CertificateConsequences.BranchSafe branch_box_1651 := by
  left; refine ⟨branch_box_1651_nonnegative, ?_⟩
  intro z hz; exact leaf_1651_sound hz

theorem leaf_1652_ok : checkAt 527 1000 box_1652 cert_1652 = true := by
  have h := List.all_eq_true.mp batch_33_02_ok accepted_1652 (by simp [batch_33_02_values])
  exact h
theorem leaf_1652_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1652.profileLo box_1652.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1652_ok
theorem branch_box_1652_nonnegative : ∀ j, 0 ≤ branch_box_1652.lower j ∧ 0 ≤ branch_box_1652.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1652, Box.profileLo, Box.profileHi, box_1652]
theorem leaf_1652_BranchSafe : CertificateConsequences.BranchSafe branch_box_1652 := by
  left; refine ⟨branch_box_1652_nonnegative, ?_⟩
  intro z hz; exact leaf_1652_sound hz

theorem leaf_1654_ok : checkAt 527 1000 box_1654 cert_1654 = true := by
  have h := List.all_eq_true.mp batch_33_03_ok accepted_1654 (by simp [batch_33_03_values])
  exact h
theorem leaf_1654_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1654.profileLo box_1654.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1654_ok
theorem branch_box_1654_nonnegative : ∀ j, 0 ≤ branch_box_1654.lower j ∧ 0 ≤ branch_box_1654.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1654, Box.profileLo, Box.profileHi, box_1654]
theorem leaf_1654_BranchSafe : CertificateConsequences.BranchSafe branch_box_1654 := by
  left; refine ⟨branch_box_1654_nonnegative, ?_⟩
  intro z hz; exact leaf_1654_sound hz

theorem leaf_1655_ok : checkAt 527 1000 box_1655 cert_1655 = true := by
  have h := List.all_eq_true.mp batch_33_04_ok accepted_1655 (by simp [batch_33_04_values])
  exact h
theorem leaf_1655_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1655.profileLo box_1655.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1655_ok
theorem branch_box_1655_nonnegative : ∀ j, 0 ≤ branch_box_1655.lower j ∧ 0 ≤ branch_box_1655.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1655, Box.profileLo, Box.profileHi, box_1655]
theorem leaf_1655_BranchSafe : CertificateConsequences.BranchSafe branch_box_1655 := by
  left; refine ⟨branch_box_1655_nonnegative, ?_⟩
  intro z hz; exact leaf_1655_sound hz

theorem leaf_1656_ok : checkAt 527 1000 box_1656 cert_1656 = true := by
  have h := List.all_eq_true.mp batch_33_05_ok accepted_1656 (by simp [batch_33_05_values])
  exact h
theorem leaf_1656_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1656.profileLo box_1656.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1656_ok
theorem branch_box_1656_nonnegative : ∀ j, 0 ≤ branch_box_1656.lower j ∧ 0 ≤ branch_box_1656.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1656, Box.profileLo, Box.profileHi, box_1656]
theorem leaf_1656_BranchSafe : CertificateConsequences.BranchSafe branch_box_1656 := by
  left; refine ⟨branch_box_1656_nonnegative, ?_⟩
  intro z hz; exact leaf_1656_sound hz

theorem leaf_1663_ok : checkAt 527 1000 box_1663 cert_1663 = true := by
  have h := List.all_eq_true.mp batch_33_06_ok accepted_1663 (by simp [batch_33_06_values])
  exact h
theorem leaf_1663_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1663.profileLo box_1663.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1663_ok
theorem branch_box_1663_nonnegative : ∀ j, 0 ≤ branch_box_1663.lower j ∧ 0 ≤ branch_box_1663.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1663, Box.profileLo, Box.profileHi, box_1663]
theorem leaf_1663_BranchSafe : CertificateConsequences.BranchSafe branch_box_1663 := by
  left; refine ⟨branch_box_1663_nonnegative, ?_⟩
  intro z hz; exact leaf_1663_sound hz

theorem leaf_1664_ok : checkAt 527 1000 box_1664 cert_1664 = true := by
  have h := List.all_eq_true.mp batch_33_07_ok accepted_1664 (by simp [batch_33_07_values])
  exact h
theorem leaf_1664_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1664.profileLo box_1664.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1664_ok
theorem branch_box_1664_nonnegative : ∀ j, 0 ≤ branch_box_1664.lower j ∧ 0 ≤ branch_box_1664.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1664, Box.profileLo, Box.profileHi, box_1664]
theorem leaf_1664_BranchSafe : CertificateConsequences.BranchSafe branch_box_1664 := by
  left; refine ⟨branch_box_1664_nonnegative, ?_⟩
  intro z hz; exact leaf_1664_sound hz

theorem leaf_1665_ok : checkAt 527 1000 box_1665 cert_1665 = true := by
  have h := List.all_eq_true.mp batch_33_08_ok accepted_1665 (by simp [batch_33_08_values])
  exact h
theorem leaf_1665_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1665.profileLo box_1665.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1665_ok
theorem branch_box_1665_nonnegative : ∀ j, 0 ≤ branch_box_1665.lower j ∧ 0 ≤ branch_box_1665.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1665, Box.profileLo, Box.profileHi, box_1665]
theorem leaf_1665_BranchSafe : CertificateConsequences.BranchSafe branch_box_1665 := by
  left; refine ⟨branch_box_1665_nonnegative, ?_⟩
  intro z hz; exact leaf_1665_sound hz

theorem leaf_1666_ok : checkAt 527 1000 box_1666 cert_1666 = true := by
  have h := List.all_eq_true.mp batch_33_09_ok accepted_1666 (by simp [batch_33_09_values])
  exact h
theorem leaf_1666_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1666.profileLo box_1666.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1666_ok
theorem branch_box_1666_nonnegative : ∀ j, 0 ≤ branch_box_1666.lower j ∧ 0 ≤ branch_box_1666.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1666, Box.profileLo, Box.profileHi, box_1666]
theorem leaf_1666_BranchSafe : CertificateConsequences.BranchSafe branch_box_1666 := by
  left; refine ⟨branch_box_1666_nonnegative, ?_⟩
  intro z hz; exact leaf_1666_sound hz

theorem leaf_1671_ok : checkAt 527 1000 box_1671 cert_1671 = true := by
  have h := List.all_eq_true.mp batch_33_10_ok accepted_1671 (by simp [batch_33_10_values])
  exact h
theorem leaf_1671_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1671.profileLo box_1671.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1671_ok
theorem branch_box_1671_nonnegative : ∀ j, 0 ≤ branch_box_1671.lower j ∧ 0 ≤ branch_box_1671.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1671, Box.profileLo, Box.profileHi, box_1671]
theorem leaf_1671_BranchSafe : CertificateConsequences.BranchSafe branch_box_1671 := by
  left; refine ⟨branch_box_1671_nonnegative, ?_⟩
  intro z hz; exact leaf_1671_sound hz

theorem leaf_1673_ok : checkAt 527 1000 box_1673 cert_1673 = true := by
  have h := List.all_eq_true.mp batch_33_11_ok accepted_1673 (by simp [batch_33_11_values])
  exact h
theorem leaf_1673_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1673.profileLo box_1673.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1673_ok
theorem branch_box_1673_nonnegative : ∀ j, 0 ≤ branch_box_1673.lower j ∧ 0 ≤ branch_box_1673.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1673, Box.profileLo, Box.profileHi, box_1673]
theorem leaf_1673_BranchSafe : CertificateConsequences.BranchSafe branch_box_1673 := by
  left; refine ⟨branch_box_1673_nonnegative, ?_⟩
  intro z hz; exact leaf_1673_sound hz

theorem leaf_1674_ok : checkAt 527 1000 box_1674 cert_1674 = true := by
  have h := List.all_eq_true.mp batch_33_12_ok accepted_1674 (by simp [batch_33_12_values])
  exact h
theorem leaf_1674_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1674.profileLo box_1674.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1674_ok
theorem branch_box_1674_nonnegative : ∀ j, 0 ≤ branch_box_1674.lower j ∧ 0 ≤ branch_box_1674.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1674, Box.profileLo, Box.profileHi, box_1674]
theorem leaf_1674_BranchSafe : CertificateConsequences.BranchSafe branch_box_1674 := by
  left; refine ⟨branch_box_1674_nonnegative, ?_⟩
  intro z hz; exact leaf_1674_sound hz

theorem leaf_1675_ok : checkAt 527 1000 box_1675 cert_1675 = true := by
  have h := List.all_eq_true.mp batch_33_13_ok accepted_1675 (by simp [batch_33_13_values])
  exact h
theorem leaf_1675_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1675.profileLo box_1675.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1675_ok
theorem branch_box_1675_nonnegative : ∀ j, 0 ≤ branch_box_1675.lower j ∧ 0 ≤ branch_box_1675.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1675, Box.profileLo, Box.profileHi, box_1675]
theorem leaf_1675_BranchSafe : CertificateConsequences.BranchSafe branch_box_1675 := by
  left; refine ⟨branch_box_1675_nonnegative, ?_⟩
  intro z hz; exact leaf_1675_sound hz

theorem leaf_1677_ok : checkAt 527 1000 box_1677 cert_1677 = true := by
  have h := List.all_eq_true.mp batch_33_14_ok accepted_1677 (by simp [batch_33_14_values])
  exact h
theorem leaf_1677_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1677.profileLo box_1677.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1677_ok
theorem branch_box_1677_nonnegative : ∀ j, 0 ≤ branch_box_1677.lower j ∧ 0 ≤ branch_box_1677.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1677, Box.profileLo, Box.profileHi, box_1677]
theorem leaf_1677_BranchSafe : CertificateConsequences.BranchSafe branch_box_1677 := by
  left; refine ⟨branch_box_1677_nonnegative, ?_⟩
  intro z hz; exact leaf_1677_sound hz

theorem leaf_1678_ok : checkAt 527 1000 box_1678 cert_1678 = true := by
  have h := List.all_eq_true.mp batch_33_15_ok accepted_1678 (by simp [batch_33_15_values])
  exact h
theorem leaf_1678_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1678.profileLo box_1678.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1678_ok
theorem branch_box_1678_nonnegative : ∀ j, 0 ≤ branch_box_1678.lower j ∧ 0 ≤ branch_box_1678.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1678, Box.profileLo, Box.profileHi, box_1678]
theorem leaf_1678_BranchSafe : CertificateConsequences.BranchSafe branch_box_1678 := by
  left; refine ⟨branch_box_1678_nonnegative, ?_⟩
  intro z hz; exact leaf_1678_sound hz

theorem leaf_1683_ok : checkAt 527 1000 box_1683 cert_1683 = true := by
  have h := List.all_eq_true.mp batch_33_16_ok accepted_1683 (by simp [batch_33_16_values])
  exact h
theorem leaf_1683_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1683.profileLo box_1683.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1683_ok
theorem branch_box_1683_nonnegative : ∀ j, 0 ≤ branch_box_1683.lower j ∧ 0 ≤ branch_box_1683.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1683, Box.profileLo, Box.profileHi, box_1683]
theorem leaf_1683_BranchSafe : CertificateConsequences.BranchSafe branch_box_1683 := by
  left; refine ⟨branch_box_1683_nonnegative, ?_⟩
  intro z hz; exact leaf_1683_sound hz

theorem leaf_1684_ok : checkAt 527 1000 box_1684 cert_1684 = true := by
  have h := List.all_eq_true.mp batch_33_17_ok accepted_1684 (by simp [batch_33_17_values])
  exact h
theorem leaf_1684_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1684.profileLo box_1684.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1684_ok
theorem branch_box_1684_nonnegative : ∀ j, 0 ≤ branch_box_1684.lower j ∧ 0 ≤ branch_box_1684.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1684, Box.profileLo, Box.profileHi, box_1684]
theorem leaf_1684_BranchSafe : CertificateConsequences.BranchSafe branch_box_1684 := by
  left; refine ⟨branch_box_1684_nonnegative, ?_⟩
  intro z hz; exact leaf_1684_sound hz

theorem leaf_1686_ok : checkAt 527 1000 box_1686 cert_1686 = true := by
  have h := List.all_eq_true.mp batch_33_18_ok accepted_1686 (by simp [batch_33_18_values])
  exact h
theorem leaf_1686_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1686.profileLo box_1686.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1686_ok
theorem branch_box_1686_nonnegative : ∀ j, 0 ≤ branch_box_1686.lower j ∧ 0 ≤ branch_box_1686.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1686, Box.profileLo, Box.profileHi, box_1686]
theorem leaf_1686_BranchSafe : CertificateConsequences.BranchSafe branch_box_1686 := by
  left; refine ⟨branch_box_1686_nonnegative, ?_⟩
  intro z hz; exact leaf_1686_sound hz

theorem leaf_1689_ok : checkAt 527 1000 box_1689 cert_1689 = true := by
  have h := List.all_eq_true.mp batch_33_19_ok accepted_1689 (by simp [batch_33_19_values])
  exact h
theorem leaf_1689_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1689.profileLo box_1689.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1689_ok
theorem branch_box_1689_nonnegative : ∀ j, 0 ≤ branch_box_1689.lower j ∧ 0 ≤ branch_box_1689.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1689, Box.profileLo, Box.profileHi, box_1689]
theorem leaf_1689_BranchSafe : CertificateConsequences.BranchSafe branch_box_1689 := by
  left; refine ⟨branch_box_1689_nonnegative, ?_⟩
  intro z hz; exact leaf_1689_sound hz

theorem leaf_1690_ok : checkAt 527 1000 box_1690 cert_1690 = true := by
  have h := List.all_eq_true.mp batch_33_20_ok accepted_1690 (by simp [batch_33_20_values])
  exact h
theorem leaf_1690_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1690.profileLo box_1690.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1690_ok
theorem branch_box_1690_nonnegative : ∀ j, 0 ≤ branch_box_1690.lower j ∧ 0 ≤ branch_box_1690.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1690, Box.profileLo, Box.profileHi, box_1690]
theorem leaf_1690_BranchSafe : CertificateConsequences.BranchSafe branch_box_1690 := by
  left; refine ⟨branch_box_1690_nonnegative, ?_⟩
  intro z hz; exact leaf_1690_sound hz

theorem leaf_1691_ok : checkAt 527 1000 box_1691 cert_1691 = true := by
  have h := List.all_eq_true.mp batch_33_21_ok accepted_1691 (by simp [batch_33_21_values])
  exact h
theorem leaf_1691_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1691.profileLo box_1691.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1691_ok
theorem branch_box_1691_nonnegative : ∀ j, 0 ≤ branch_box_1691.lower j ∧ 0 ≤ branch_box_1691.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1691, Box.profileLo, Box.profileHi, box_1691]
theorem leaf_1691_BranchSafe : CertificateConsequences.BranchSafe branch_box_1691 := by
  left; refine ⟨branch_box_1691_nonnegative, ?_⟩
  intro z hz; exact leaf_1691_sound hz

theorem leaf_1692_ok : checkAt 527 1000 box_1692 cert_1692 = true := by
  have h := List.all_eq_true.mp batch_33_22_ok accepted_1692 (by simp [batch_33_22_values])
  exact h
theorem leaf_1692_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1692.profileLo box_1692.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1692_ok
theorem branch_box_1692_nonnegative : ∀ j, 0 ≤ branch_box_1692.lower j ∧ 0 ≤ branch_box_1692.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1692, Box.profileLo, Box.profileHi, box_1692]
theorem leaf_1692_BranchSafe : CertificateConsequences.BranchSafe branch_box_1692 := by
  left; refine ⟨branch_box_1692_nonnegative, ?_⟩
  intro z hz; exact leaf_1692_sound hz

theorem leaf_1697_ok : checkAt 527 1000 box_1697 cert_1697 = true := by
  have h := List.all_eq_true.mp batch_33_23_ok accepted_1697 (by simp [batch_33_23_values])
  exact h
theorem leaf_1697_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1697.profileLo box_1697.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1697_ok
theorem branch_box_1697_nonnegative : ∀ j, 0 ≤ branch_box_1697.lower j ∧ 0 ≤ branch_box_1697.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1697, Box.profileLo, Box.profileHi, box_1697]
theorem leaf_1697_BranchSafe : CertificateConsequences.BranchSafe branch_box_1697 := by
  left; refine ⟨branch_box_1697_nonnegative, ?_⟩
  intro z hz; exact leaf_1697_sound hz

theorem leaf_1698_ok : checkAt 527 1000 box_1698 cert_1698 = true := by
  have h := List.all_eq_true.mp batch_33_24_ok accepted_1698 (by simp [batch_33_24_values])
  exact h
theorem leaf_1698_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1698.profileLo box_1698.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1698_ok
theorem branch_box_1698_nonnegative : ∀ j, 0 ≤ branch_box_1698.lower j ∧ 0 ≤ branch_box_1698.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1698, Box.profileLo, Box.profileHi, box_1698]
theorem leaf_1698_BranchSafe : CertificateConsequences.BranchSafe branch_box_1698 := by
  left; refine ⟨branch_box_1698_nonnegative, ?_⟩
  intro z hz; exact leaf_1698_sound hz

theorem leaf_1699_ok : checkAt 527 1000 box_1699 cert_1699 = true := by
  have h := List.all_eq_true.mp batch_33_25_ok accepted_1699 (by simp [batch_33_25_values])
  exact h
theorem leaf_1699_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1699.profileLo box_1699.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1699_ok
theorem branch_box_1699_nonnegative : ∀ j, 0 ≤ branch_box_1699.lower j ∧ 0 ≤ branch_box_1699.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1699, Box.profileLo, Box.profileHi, box_1699]
theorem leaf_1699_BranchSafe : CertificateConsequences.BranchSafe branch_box_1699 := by
  left; refine ⟨branch_box_1699_nonnegative, ?_⟩
  intro z hz; exact leaf_1699_sound hz

#print axioms batch_33_00_ok
#print axioms leaf_1650_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
