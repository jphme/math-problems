import PeaceableQueens.UpperBound.Generated.Even.CoreScaled33Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_33_00_values : List Bool := [accepted_1650]
theorem batch_33_00_ok : batch_33_00_values.all id = true := by decide

def batch_33_01_values : List Bool := [accepted_1656]
theorem batch_33_01_ok : batch_33_01_values.all id = true := by decide

def batch_33_02_values : List Bool := [accepted_1657]
theorem batch_33_02_ok : batch_33_02_values.all id = true := by decide

def batch_33_03_values : List Bool := [accepted_1659]
theorem batch_33_03_ok : batch_33_03_values.all id = true := by decide

def batch_33_04_values : List Bool := [accepted_1661]
theorem batch_33_04_ok : batch_33_04_values.all id = true := by decide

def batch_33_05_values : List Bool := [accepted_1668]
theorem batch_33_05_ok : batch_33_05_values.all id = true := by decide

def batch_33_06_values : List Bool := [accepted_1670]
theorem batch_33_06_ok : batch_33_06_values.all id = true := by decide

def batch_33_07_values : List Bool := [accepted_1672]
theorem batch_33_07_ok : batch_33_07_values.all id = true := by decide

def batch_33_08_values : List Bool := [accepted_1673]
theorem batch_33_08_ok : batch_33_08_values.all id = true := by decide

def batch_33_09_values : List Bool := [accepted_1675]
theorem batch_33_09_ok : batch_33_09_values.all id = true := by decide

def batch_33_10_values : List Bool := [accepted_1677]
theorem batch_33_10_ok : batch_33_10_values.all id = true := by decide

def batch_33_11_values : List Bool := [accepted_1680]
theorem batch_33_11_ok : batch_33_11_values.all id = true := by decide

def batch_33_12_values : List Bool := [accepted_1682]
theorem batch_33_12_ok : batch_33_12_values.all id = true := by decide

def batch_33_13_values : List Bool := [accepted_1684]
theorem batch_33_13_ok : batch_33_13_values.all id = true := by decide

def batch_33_14_values : List Bool := [accepted_1686]
theorem batch_33_14_ok : batch_33_14_values.all id = true := by decide

def batch_33_15_values : List Bool := [accepted_1690]
theorem batch_33_15_ok : batch_33_15_values.all id = true := by decide

def batch_33_16_values : List Bool := [accepted_1691]
theorem batch_33_16_ok : batch_33_16_values.all id = true := by decide

def batch_33_17_values : List Bool := [accepted_1696]
theorem batch_33_17_ok : batch_33_17_values.all id = true := by decide

def batch_33_18_values : List Bool := [accepted_1698]
theorem batch_33_18_ok : batch_33_18_values.all id = true := by decide

def batch_33_19_values : List Bool := [accepted_1699]
theorem batch_33_19_ok : batch_33_19_values.all id = true := by decide

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

theorem leaf_1656_ok : checkAt 527 1000 box_1656 cert_1656 = true := by
  have h := List.all_eq_true.mp batch_33_01_ok accepted_1656 (by simp [batch_33_01_values])
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

theorem leaf_1657_ok : checkAt 527 1000 box_1657 cert_1657 = true := by
  have h := List.all_eq_true.mp batch_33_02_ok accepted_1657 (by simp [batch_33_02_values])
  exact h
theorem leaf_1657_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1657.profileLo box_1657.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1657_ok
theorem branch_box_1657_nonnegative : ∀ j, 0 ≤ branch_box_1657.lower j ∧ 0 ≤ branch_box_1657.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1657, Box.profileLo, Box.profileHi, box_1657]
theorem leaf_1657_BranchSafe : CertificateConsequences.BranchSafe branch_box_1657 := by
  left; refine ⟨branch_box_1657_nonnegative, ?_⟩
  intro z hz; exact leaf_1657_sound hz

theorem leaf_1659_ok : checkAt 527 1000 box_1659 cert_1659 = true := by
  have h := List.all_eq_true.mp batch_33_03_ok accepted_1659 (by simp [batch_33_03_values])
  exact h
theorem leaf_1659_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1659.profileLo box_1659.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1659_ok
theorem branch_box_1659_nonnegative : ∀ j, 0 ≤ branch_box_1659.lower j ∧ 0 ≤ branch_box_1659.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1659, Box.profileLo, Box.profileHi, box_1659]
theorem leaf_1659_BranchSafe : CertificateConsequences.BranchSafe branch_box_1659 := by
  left; refine ⟨branch_box_1659_nonnegative, ?_⟩
  intro z hz; exact leaf_1659_sound hz

theorem leaf_1661_ok : checkAt 527 1000 box_1661 cert_1661 = true := by
  have h := List.all_eq_true.mp batch_33_04_ok accepted_1661 (by simp [batch_33_04_values])
  exact h
theorem leaf_1661_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1661.profileLo box_1661.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1661_ok
theorem branch_box_1661_nonnegative : ∀ j, 0 ≤ branch_box_1661.lower j ∧ 0 ≤ branch_box_1661.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1661, Box.profileLo, Box.profileHi, box_1661]
theorem leaf_1661_BranchSafe : CertificateConsequences.BranchSafe branch_box_1661 := by
  left; refine ⟨branch_box_1661_nonnegative, ?_⟩
  intro z hz; exact leaf_1661_sound hz

theorem leaf_1668_ok : checkAt 527 1000 box_1668 cert_1668 = true := by
  have h := List.all_eq_true.mp batch_33_05_ok accepted_1668 (by simp [batch_33_05_values])
  exact h
theorem leaf_1668_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1668.profileLo box_1668.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1668_ok
theorem branch_box_1668_nonnegative : ∀ j, 0 ≤ branch_box_1668.lower j ∧ 0 ≤ branch_box_1668.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1668, Box.profileLo, Box.profileHi, box_1668]
theorem leaf_1668_BranchSafe : CertificateConsequences.BranchSafe branch_box_1668 := by
  left; refine ⟨branch_box_1668_nonnegative, ?_⟩
  intro z hz; exact leaf_1668_sound hz

theorem leaf_1670_ok : checkAt 527 1000 box_1670 cert_1670 = true := by
  have h := List.all_eq_true.mp batch_33_06_ok accepted_1670 (by simp [batch_33_06_values])
  exact h
theorem leaf_1670_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1670.profileLo box_1670.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1670_ok
theorem branch_box_1670_nonnegative : ∀ j, 0 ≤ branch_box_1670.lower j ∧ 0 ≤ branch_box_1670.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1670, Box.profileLo, Box.profileHi, box_1670]
theorem leaf_1670_BranchSafe : CertificateConsequences.BranchSafe branch_box_1670 := by
  left; refine ⟨branch_box_1670_nonnegative, ?_⟩
  intro z hz; exact leaf_1670_sound hz

theorem leaf_1672_ok : checkAt 527 1000 box_1672 cert_1672 = true := by
  have h := List.all_eq_true.mp batch_33_07_ok accepted_1672 (by simp [batch_33_07_values])
  exact h
theorem leaf_1672_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1672.profileLo box_1672.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1672_ok
theorem branch_box_1672_nonnegative : ∀ j, 0 ≤ branch_box_1672.lower j ∧ 0 ≤ branch_box_1672.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1672, Box.profileLo, Box.profileHi, box_1672]
theorem leaf_1672_BranchSafe : CertificateConsequences.BranchSafe branch_box_1672 := by
  left; refine ⟨branch_box_1672_nonnegative, ?_⟩
  intro z hz; exact leaf_1672_sound hz

theorem leaf_1673_ok : checkAt 527 1000 box_1673 cert_1673 = true := by
  have h := List.all_eq_true.mp batch_33_08_ok accepted_1673 (by simp [batch_33_08_values])
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

theorem leaf_1675_ok : checkAt 527 1000 box_1675 cert_1675 = true := by
  have h := List.all_eq_true.mp batch_33_09_ok accepted_1675 (by simp [batch_33_09_values])
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
  have h := List.all_eq_true.mp batch_33_10_ok accepted_1677 (by simp [batch_33_10_values])
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

theorem leaf_1680_ok : checkAt 527 1000 box_1680 cert_1680 = true := by
  have h := List.all_eq_true.mp batch_33_11_ok accepted_1680 (by simp [batch_33_11_values])
  exact h
theorem leaf_1680_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1680.profileLo box_1680.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1680_ok
theorem branch_box_1680_nonnegative : ∀ j, 0 ≤ branch_box_1680.lower j ∧ 0 ≤ branch_box_1680.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1680, Box.profileLo, Box.profileHi, box_1680]
theorem leaf_1680_BranchSafe : CertificateConsequences.BranchSafe branch_box_1680 := by
  left; refine ⟨branch_box_1680_nonnegative, ?_⟩
  intro z hz; exact leaf_1680_sound hz

theorem leaf_1682_ok : checkAt 527 1000 box_1682 cert_1682 = true := by
  have h := List.all_eq_true.mp batch_33_12_ok accepted_1682 (by simp [batch_33_12_values])
  exact h
theorem leaf_1682_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1682.profileLo box_1682.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1682_ok
theorem branch_box_1682_nonnegative : ∀ j, 0 ≤ branch_box_1682.lower j ∧ 0 ≤ branch_box_1682.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1682, Box.profileLo, Box.profileHi, box_1682]
theorem leaf_1682_BranchSafe : CertificateConsequences.BranchSafe branch_box_1682 := by
  left; refine ⟨branch_box_1682_nonnegative, ?_⟩
  intro z hz; exact leaf_1682_sound hz

theorem leaf_1684_ok : checkAt 527 1000 box_1684 cert_1684 = true := by
  have h := List.all_eq_true.mp batch_33_13_ok accepted_1684 (by simp [batch_33_13_values])
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
  have h := List.all_eq_true.mp batch_33_14_ok accepted_1686 (by simp [batch_33_14_values])
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

theorem leaf_1690_ok : checkAt 527 1000 box_1690 cert_1690 = true := by
  have h := List.all_eq_true.mp batch_33_15_ok accepted_1690 (by simp [batch_33_15_values])
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
  have h := List.all_eq_true.mp batch_33_16_ok accepted_1691 (by simp [batch_33_16_values])
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

theorem leaf_1696_ok : checkAt 527 1000 box_1696 cert_1696 = true := by
  have h := List.all_eq_true.mp batch_33_17_ok accepted_1696 (by simp [batch_33_17_values])
  exact h
theorem leaf_1696_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1696.profileLo box_1696.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1696_ok
theorem branch_box_1696_nonnegative : ∀ j, 0 ≤ branch_box_1696.lower j ∧ 0 ≤ branch_box_1696.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1696, Box.profileLo, Box.profileHi, box_1696]
theorem leaf_1696_BranchSafe : CertificateConsequences.BranchSafe branch_box_1696 := by
  left; refine ⟨branch_box_1696_nonnegative, ?_⟩
  intro z hz; exact leaf_1696_sound hz

theorem leaf_1698_ok : checkAt 527 1000 box_1698 cert_1698 = true := by
  have h := List.all_eq_true.mp batch_33_18_ok accepted_1698 (by simp [batch_33_18_values])
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
  have h := List.all_eq_true.mp batch_33_19_ok accepted_1699 (by simp [batch_33_19_values])
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
end PeaceableQueens.UpperBound.Generated.Even.Core
