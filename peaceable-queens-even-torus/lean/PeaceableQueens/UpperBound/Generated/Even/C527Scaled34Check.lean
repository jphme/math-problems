import PeaceableQueens.UpperBound.Generated.Even.C527Scaled34Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_34_00_values : List Bool := [accepted_1700]
theorem batch_34_00_ok : batch_34_00_values.all id = true := by decide

def batch_34_01_values : List Bool := [accepted_1706]
theorem batch_34_01_ok : batch_34_01_values.all id = true := by decide

def batch_34_02_values : List Bool := [accepted_1707]
theorem batch_34_02_ok : batch_34_02_values.all id = true := by decide

def batch_34_03_values : List Bool := [accepted_1708]
theorem batch_34_03_ok : batch_34_03_values.all id = true := by decide

def batch_34_04_values : List Bool := [accepted_1711]
theorem batch_34_04_ok : batch_34_04_values.all id = true := by decide

def batch_34_05_values : List Bool := [accepted_1712]
theorem batch_34_05_ok : batch_34_05_values.all id = true := by decide

def batch_34_06_values : List Bool := [accepted_1713]
theorem batch_34_06_ok : batch_34_06_values.all id = true := by decide

def batch_34_07_values : List Bool := [accepted_1716]
theorem batch_34_07_ok : batch_34_07_values.all id = true := by decide

def batch_34_08_values : List Bool := [accepted_1718]
theorem batch_34_08_ok : batch_34_08_values.all id = true := by decide

def batch_34_09_values : List Bool := [accepted_1719]
theorem batch_34_09_ok : batch_34_09_values.all id = true := by decide

def batch_34_10_values : List Bool := [accepted_1720]
theorem batch_34_10_ok : batch_34_10_values.all id = true := by decide

def batch_34_11_values : List Bool := [accepted_1725]
theorem batch_34_11_ok : batch_34_11_values.all id = true := by decide

def batch_34_12_values : List Bool := [accepted_1726]
theorem batch_34_12_ok : batch_34_12_values.all id = true := by decide

def batch_34_13_values : List Bool := [accepted_1727]
theorem batch_34_13_ok : batch_34_13_values.all id = true := by decide

def batch_34_14_values : List Bool := [accepted_1728]
theorem batch_34_14_ok : batch_34_14_values.all id = true := by decide

def batch_34_15_values : List Bool := [accepted_1735]
theorem batch_34_15_ok : batch_34_15_values.all id = true := by decide

def batch_34_16_values : List Bool := [accepted_1736]
theorem batch_34_16_ok : batch_34_16_values.all id = true := by decide

def batch_34_17_values : List Bool := [accepted_1737]
theorem batch_34_17_ok : batch_34_17_values.all id = true := by decide

def batch_34_18_values : List Bool := [accepted_1738]
theorem batch_34_18_ok : batch_34_18_values.all id = true := by decide

def batch_34_19_values : List Bool := [accepted_1740]
theorem batch_34_19_ok : batch_34_19_values.all id = true := by decide

def batch_34_20_values : List Bool := [accepted_1741]
theorem batch_34_20_ok : batch_34_20_values.all id = true := by decide

def batch_34_21_values : List Bool := [accepted_1742]
theorem batch_34_21_ok : batch_34_21_values.all id = true := by decide

def batch_34_22_values : List Bool := [accepted_1749]
theorem batch_34_22_ok : batch_34_22_values.all id = true := by decide

theorem leaf_1700_ok : checkAt 527 1000 box_1700 cert_1700 = true := by
  have h := List.all_eq_true.mp batch_34_00_ok accepted_1700 (by simp [batch_34_00_values])
  exact h
theorem leaf_1700_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1700.profileLo box_1700.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1700_ok
theorem branch_box_1700_nonnegative : ∀ j, 0 ≤ branch_box_1700.lower j ∧ 0 ≤ branch_box_1700.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1700, Box.profileLo, Box.profileHi, box_1700]
theorem leaf_1700_BranchSafe : CertificateConsequences.BranchSafe branch_box_1700 := by
  left; refine ⟨branch_box_1700_nonnegative, ?_⟩
  intro z hz; exact leaf_1700_sound hz

theorem leaf_1706_ok : checkAt 527 1000 box_1706 cert_1706 = true := by
  have h := List.all_eq_true.mp batch_34_01_ok accepted_1706 (by simp [batch_34_01_values])
  exact h
theorem leaf_1706_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1706.profileLo box_1706.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1706_ok
theorem branch_box_1706_nonnegative : ∀ j, 0 ≤ branch_box_1706.lower j ∧ 0 ≤ branch_box_1706.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1706, Box.profileLo, Box.profileHi, box_1706]
theorem leaf_1706_BranchSafe : CertificateConsequences.BranchSafe branch_box_1706 := by
  left; refine ⟨branch_box_1706_nonnegative, ?_⟩
  intro z hz; exact leaf_1706_sound hz

theorem leaf_1707_ok : checkAt 527 1000 box_1707 cert_1707 = true := by
  have h := List.all_eq_true.mp batch_34_02_ok accepted_1707 (by simp [batch_34_02_values])
  exact h
theorem leaf_1707_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1707.profileLo box_1707.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1707_ok
theorem branch_box_1707_nonnegative : ∀ j, 0 ≤ branch_box_1707.lower j ∧ 0 ≤ branch_box_1707.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1707, Box.profileLo, Box.profileHi, box_1707]
theorem leaf_1707_BranchSafe : CertificateConsequences.BranchSafe branch_box_1707 := by
  left; refine ⟨branch_box_1707_nonnegative, ?_⟩
  intro z hz; exact leaf_1707_sound hz

theorem leaf_1708_ok : checkAt 527 1000 box_1708 cert_1708 = true := by
  have h := List.all_eq_true.mp batch_34_03_ok accepted_1708 (by simp [batch_34_03_values])
  exact h
theorem leaf_1708_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1708.profileLo box_1708.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1708_ok
theorem branch_box_1708_nonnegative : ∀ j, 0 ≤ branch_box_1708.lower j ∧ 0 ≤ branch_box_1708.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1708, Box.profileLo, Box.profileHi, box_1708]
theorem leaf_1708_BranchSafe : CertificateConsequences.BranchSafe branch_box_1708 := by
  left; refine ⟨branch_box_1708_nonnegative, ?_⟩
  intro z hz; exact leaf_1708_sound hz

theorem leaf_1711_ok : checkAt 527 1000 box_1711 cert_1711 = true := by
  have h := List.all_eq_true.mp batch_34_04_ok accepted_1711 (by simp [batch_34_04_values])
  exact h
theorem leaf_1711_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1711.profileLo box_1711.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1711_ok
theorem branch_box_1711_nonnegative : ∀ j, 0 ≤ branch_box_1711.lower j ∧ 0 ≤ branch_box_1711.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1711, Box.profileLo, Box.profileHi, box_1711]
theorem leaf_1711_BranchSafe : CertificateConsequences.BranchSafe branch_box_1711 := by
  left; refine ⟨branch_box_1711_nonnegative, ?_⟩
  intro z hz; exact leaf_1711_sound hz

theorem leaf_1712_ok : checkAt 527 1000 box_1712 cert_1712 = true := by
  have h := List.all_eq_true.mp batch_34_05_ok accepted_1712 (by simp [batch_34_05_values])
  exact h
theorem leaf_1712_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1712.profileLo box_1712.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1712_ok
theorem branch_box_1712_nonnegative : ∀ j, 0 ≤ branch_box_1712.lower j ∧ 0 ≤ branch_box_1712.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1712, Box.profileLo, Box.profileHi, box_1712]
theorem leaf_1712_BranchSafe : CertificateConsequences.BranchSafe branch_box_1712 := by
  left; refine ⟨branch_box_1712_nonnegative, ?_⟩
  intro z hz; exact leaf_1712_sound hz

theorem leaf_1713_ok : checkAt 527 1000 box_1713 cert_1713 = true := by
  have h := List.all_eq_true.mp batch_34_06_ok accepted_1713 (by simp [batch_34_06_values])
  exact h
theorem leaf_1713_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1713.profileLo box_1713.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1713_ok
theorem branch_box_1713_nonnegative : ∀ j, 0 ≤ branch_box_1713.lower j ∧ 0 ≤ branch_box_1713.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1713, Box.profileLo, Box.profileHi, box_1713]
theorem leaf_1713_BranchSafe : CertificateConsequences.BranchSafe branch_box_1713 := by
  left; refine ⟨branch_box_1713_nonnegative, ?_⟩
  intro z hz; exact leaf_1713_sound hz

theorem leaf_1716_ok : checkAt 527 1000 box_1716 cert_1716 = true := by
  have h := List.all_eq_true.mp batch_34_07_ok accepted_1716 (by simp [batch_34_07_values])
  exact h
theorem leaf_1716_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1716.profileLo box_1716.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1716_ok
theorem branch_box_1716_nonnegative : ∀ j, 0 ≤ branch_box_1716.lower j ∧ 0 ≤ branch_box_1716.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1716, Box.profileLo, Box.profileHi, box_1716]
theorem leaf_1716_BranchSafe : CertificateConsequences.BranchSafe branch_box_1716 := by
  left; refine ⟨branch_box_1716_nonnegative, ?_⟩
  intro z hz; exact leaf_1716_sound hz

theorem leaf_1718_ok : checkAt 527 1000 box_1718 cert_1718 = true := by
  have h := List.all_eq_true.mp batch_34_08_ok accepted_1718 (by simp [batch_34_08_values])
  exact h
theorem leaf_1718_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1718.profileLo box_1718.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1718_ok
theorem branch_box_1718_nonnegative : ∀ j, 0 ≤ branch_box_1718.lower j ∧ 0 ≤ branch_box_1718.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1718, Box.profileLo, Box.profileHi, box_1718]
theorem leaf_1718_BranchSafe : CertificateConsequences.BranchSafe branch_box_1718 := by
  left; refine ⟨branch_box_1718_nonnegative, ?_⟩
  intro z hz; exact leaf_1718_sound hz

theorem leaf_1719_ok : checkAt 527 1000 box_1719 cert_1719 = true := by
  have h := List.all_eq_true.mp batch_34_09_ok accepted_1719 (by simp [batch_34_09_values])
  exact h
theorem leaf_1719_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1719.profileLo box_1719.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1719_ok
theorem branch_box_1719_nonnegative : ∀ j, 0 ≤ branch_box_1719.lower j ∧ 0 ≤ branch_box_1719.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1719, Box.profileLo, Box.profileHi, box_1719]
theorem leaf_1719_BranchSafe : CertificateConsequences.BranchSafe branch_box_1719 := by
  left; refine ⟨branch_box_1719_nonnegative, ?_⟩
  intro z hz; exact leaf_1719_sound hz

theorem leaf_1720_ok : checkAt 527 1000 box_1720 cert_1720 = true := by
  have h := List.all_eq_true.mp batch_34_10_ok accepted_1720 (by simp [batch_34_10_values])
  exact h
theorem leaf_1720_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1720.profileLo box_1720.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1720_ok
theorem branch_box_1720_nonnegative : ∀ j, 0 ≤ branch_box_1720.lower j ∧ 0 ≤ branch_box_1720.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1720, Box.profileLo, Box.profileHi, box_1720]
theorem leaf_1720_BranchSafe : CertificateConsequences.BranchSafe branch_box_1720 := by
  left; refine ⟨branch_box_1720_nonnegative, ?_⟩
  intro z hz; exact leaf_1720_sound hz

theorem leaf_1725_ok : checkAt 527 1000 box_1725 cert_1725 = true := by
  have h := List.all_eq_true.mp batch_34_11_ok accepted_1725 (by simp [batch_34_11_values])
  exact h
theorem leaf_1725_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1725.profileLo box_1725.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1725_ok
theorem branch_box_1725_nonnegative : ∀ j, 0 ≤ branch_box_1725.lower j ∧ 0 ≤ branch_box_1725.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1725, Box.profileLo, Box.profileHi, box_1725]
theorem leaf_1725_BranchSafe : CertificateConsequences.BranchSafe branch_box_1725 := by
  left; refine ⟨branch_box_1725_nonnegative, ?_⟩
  intro z hz; exact leaf_1725_sound hz

theorem leaf_1726_ok : checkAt 527 1000 box_1726 cert_1726 = true := by
  have h := List.all_eq_true.mp batch_34_12_ok accepted_1726 (by simp [batch_34_12_values])
  exact h
theorem leaf_1726_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1726.profileLo box_1726.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1726_ok
theorem branch_box_1726_nonnegative : ∀ j, 0 ≤ branch_box_1726.lower j ∧ 0 ≤ branch_box_1726.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1726, Box.profileLo, Box.profileHi, box_1726]
theorem leaf_1726_BranchSafe : CertificateConsequences.BranchSafe branch_box_1726 := by
  left; refine ⟨branch_box_1726_nonnegative, ?_⟩
  intro z hz; exact leaf_1726_sound hz

theorem leaf_1727_ok : checkAt 527 1000 box_1727 cert_1727 = true := by
  have h := List.all_eq_true.mp batch_34_13_ok accepted_1727 (by simp [batch_34_13_values])
  exact h
theorem leaf_1727_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1727.profileLo box_1727.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1727_ok
theorem branch_box_1727_nonnegative : ∀ j, 0 ≤ branch_box_1727.lower j ∧ 0 ≤ branch_box_1727.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1727, Box.profileLo, Box.profileHi, box_1727]
theorem leaf_1727_BranchSafe : CertificateConsequences.BranchSafe branch_box_1727 := by
  left; refine ⟨branch_box_1727_nonnegative, ?_⟩
  intro z hz; exact leaf_1727_sound hz

theorem leaf_1728_ok : checkAt 527 1000 box_1728 cert_1728 = true := by
  have h := List.all_eq_true.mp batch_34_14_ok accepted_1728 (by simp [batch_34_14_values])
  exact h
theorem leaf_1728_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1728.profileLo box_1728.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1728_ok
theorem branch_box_1728_nonnegative : ∀ j, 0 ≤ branch_box_1728.lower j ∧ 0 ≤ branch_box_1728.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1728, Box.profileLo, Box.profileHi, box_1728]
theorem leaf_1728_BranchSafe : CertificateConsequences.BranchSafe branch_box_1728 := by
  left; refine ⟨branch_box_1728_nonnegative, ?_⟩
  intro z hz; exact leaf_1728_sound hz

theorem leaf_1735_ok : checkAt 527 1000 box_1735 cert_1735 = true := by
  have h := List.all_eq_true.mp batch_34_15_ok accepted_1735 (by simp [batch_34_15_values])
  exact h
theorem leaf_1735_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1735.profileLo box_1735.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1735_ok
theorem branch_box_1735_nonnegative : ∀ j, 0 ≤ branch_box_1735.lower j ∧ 0 ≤ branch_box_1735.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1735, Box.profileLo, Box.profileHi, box_1735]
theorem leaf_1735_BranchSafe : CertificateConsequences.BranchSafe branch_box_1735 := by
  left; refine ⟨branch_box_1735_nonnegative, ?_⟩
  intro z hz; exact leaf_1735_sound hz

theorem leaf_1736_ok : checkAt 527 1000 box_1736 cert_1736 = true := by
  have h := List.all_eq_true.mp batch_34_16_ok accepted_1736 (by simp [batch_34_16_values])
  exact h
theorem leaf_1736_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1736.profileLo box_1736.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1736_ok
theorem branch_box_1736_nonnegative : ∀ j, 0 ≤ branch_box_1736.lower j ∧ 0 ≤ branch_box_1736.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1736, Box.profileLo, Box.profileHi, box_1736]
theorem leaf_1736_BranchSafe : CertificateConsequences.BranchSafe branch_box_1736 := by
  left; refine ⟨branch_box_1736_nonnegative, ?_⟩
  intro z hz; exact leaf_1736_sound hz

theorem leaf_1737_ok : checkAt 527 1000 box_1737 cert_1737 = true := by
  have h := List.all_eq_true.mp batch_34_17_ok accepted_1737 (by simp [batch_34_17_values])
  exact h
theorem leaf_1737_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1737.profileLo box_1737.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1737_ok
theorem branch_box_1737_nonnegative : ∀ j, 0 ≤ branch_box_1737.lower j ∧ 0 ≤ branch_box_1737.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1737, Box.profileLo, Box.profileHi, box_1737]
theorem leaf_1737_BranchSafe : CertificateConsequences.BranchSafe branch_box_1737 := by
  left; refine ⟨branch_box_1737_nonnegative, ?_⟩
  intro z hz; exact leaf_1737_sound hz

theorem leaf_1738_ok : checkAt 527 1000 box_1738 cert_1738 = true := by
  have h := List.all_eq_true.mp batch_34_18_ok accepted_1738 (by simp [batch_34_18_values])
  exact h
theorem leaf_1738_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1738.profileLo box_1738.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1738_ok
theorem branch_box_1738_nonnegative : ∀ j, 0 ≤ branch_box_1738.lower j ∧ 0 ≤ branch_box_1738.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1738, Box.profileLo, Box.profileHi, box_1738]
theorem leaf_1738_BranchSafe : CertificateConsequences.BranchSafe branch_box_1738 := by
  left; refine ⟨branch_box_1738_nonnegative, ?_⟩
  intro z hz; exact leaf_1738_sound hz

theorem leaf_1740_ok : checkAt 527 1000 box_1740 cert_1740 = true := by
  have h := List.all_eq_true.mp batch_34_19_ok accepted_1740 (by simp [batch_34_19_values])
  exact h
theorem leaf_1740_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1740.profileLo box_1740.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1740_ok
theorem branch_box_1740_nonnegative : ∀ j, 0 ≤ branch_box_1740.lower j ∧ 0 ≤ branch_box_1740.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1740, Box.profileLo, Box.profileHi, box_1740]
theorem leaf_1740_BranchSafe : CertificateConsequences.BranchSafe branch_box_1740 := by
  left; refine ⟨branch_box_1740_nonnegative, ?_⟩
  intro z hz; exact leaf_1740_sound hz

theorem leaf_1741_ok : checkAt 527 1000 box_1741 cert_1741 = true := by
  have h := List.all_eq_true.mp batch_34_20_ok accepted_1741 (by simp [batch_34_20_values])
  exact h
theorem leaf_1741_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1741.profileLo box_1741.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1741_ok
theorem branch_box_1741_nonnegative : ∀ j, 0 ≤ branch_box_1741.lower j ∧ 0 ≤ branch_box_1741.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1741, Box.profileLo, Box.profileHi, box_1741]
theorem leaf_1741_BranchSafe : CertificateConsequences.BranchSafe branch_box_1741 := by
  left; refine ⟨branch_box_1741_nonnegative, ?_⟩
  intro z hz; exact leaf_1741_sound hz

theorem leaf_1742_ok : checkAt 527 1000 box_1742 cert_1742 = true := by
  have h := List.all_eq_true.mp batch_34_21_ok accepted_1742 (by simp [batch_34_21_values])
  exact h
theorem leaf_1742_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1742.profileLo box_1742.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1742_ok
theorem branch_box_1742_nonnegative : ∀ j, 0 ≤ branch_box_1742.lower j ∧ 0 ≤ branch_box_1742.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1742, Box.profileLo, Box.profileHi, box_1742]
theorem leaf_1742_BranchSafe : CertificateConsequences.BranchSafe branch_box_1742 := by
  left; refine ⟨branch_box_1742_nonnegative, ?_⟩
  intro z hz; exact leaf_1742_sound hz

theorem leaf_1749_ok : checkAt 527 1000 box_1749 cert_1749 = true := by
  have h := List.all_eq_true.mp batch_34_22_ok accepted_1749 (by simp [batch_34_22_values])
  exact h
theorem leaf_1749_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1749.profileLo box_1749.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1749_ok
theorem branch_box_1749_nonnegative : ∀ j, 0 ≤ branch_box_1749.lower j ∧ 0 ≤ branch_box_1749.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1749, Box.profileLo, Box.profileHi, box_1749]
theorem leaf_1749_BranchSafe : CertificateConsequences.BranchSafe branch_box_1749 := by
  left; refine ⟨branch_box_1749_nonnegative, ?_⟩
  intro z hz; exact leaf_1749_sound hz

#print axioms batch_34_00_ok
#print axioms leaf_1700_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
