import PeaceableQueens.UpperBound.Generated.Even.CoreScaled36Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_36_00_values : List Bool := [accepted_1801]
theorem batch_36_00_ok : batch_36_00_values.all id = true := by decide

def batch_36_01_values : List Bool := [accepted_1803]
theorem batch_36_01_ok : batch_36_01_values.all id = true := by decide

def batch_36_02_values : List Bool := [accepted_1806]
theorem batch_36_02_ok : batch_36_02_values.all id = true := by decide

def batch_36_03_values : List Bool := [accepted_1808]
theorem batch_36_03_ok : batch_36_03_values.all id = true := by decide

def batch_36_04_values : List Bool := [accepted_1810]
theorem batch_36_04_ok : batch_36_04_values.all id = true := by decide

def batch_36_05_values : List Bool := [accepted_1811]
theorem batch_36_05_ok : batch_36_05_values.all id = true := by decide

def batch_36_06_values : List Bool := [accepted_1814]
theorem batch_36_06_ok : batch_36_06_values.all id = true := by decide

def batch_36_07_values : List Bool := [accepted_1816]
theorem batch_36_07_ok : batch_36_07_values.all id = true := by decide

def batch_36_08_values : List Bool := [accepted_1818]
theorem batch_36_08_ok : batch_36_08_values.all id = true := by decide

def batch_36_09_values : List Bool := [accepted_1819]
theorem batch_36_09_ok : batch_36_09_values.all id = true := by decide

def batch_36_10_values : List Bool := [accepted_1821]
theorem batch_36_10_ok : batch_36_10_values.all id = true := by decide

def batch_36_11_values : List Bool := [accepted_1825]
theorem batch_36_11_ok : batch_36_11_values.all id = true := by decide

def batch_36_12_values : List Bool := [accepted_1830]
theorem batch_36_12_ok : batch_36_12_values.all id = true := by decide

def batch_36_13_values : List Bool := [accepted_1831]
theorem batch_36_13_ok : batch_36_13_values.all id = true := by decide

def batch_36_14_values : List Bool := [accepted_1833]
theorem batch_36_14_ok : batch_36_14_values.all id = true := by decide

def batch_36_15_values : List Bool := [accepted_1835]
theorem batch_36_15_ok : batch_36_15_values.all id = true := by decide

def batch_36_16_values : List Bool := [accepted_1840]
theorem batch_36_16_ok : batch_36_16_values.all id = true := by decide

def batch_36_17_values : List Bool := [accepted_1841]
theorem batch_36_17_ok : batch_36_17_values.all id = true := by decide

def batch_36_18_values : List Bool := [accepted_1843]
theorem batch_36_18_ok : batch_36_18_values.all id = true := by decide

def batch_36_19_values : List Bool := [accepted_1845]
theorem batch_36_19_ok : batch_36_19_values.all id = true := by decide

def batch_36_20_values : List Bool := [accepted_1848]
theorem batch_36_20_ok : batch_36_20_values.all id = true := by decide

def batch_36_21_values : List Bool := [accepted_1849]
theorem batch_36_21_ok : batch_36_21_values.all id = true := by decide

theorem leaf_1801_ok : checkAt 527 1000 box_1801 cert_1801 = true := by
  have h := List.all_eq_true.mp batch_36_00_ok accepted_1801 (by simp [batch_36_00_values])
  exact h
theorem leaf_1801_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1801.profileLo box_1801.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1801_ok
theorem branch_box_1801_nonnegative : ∀ j, 0 ≤ branch_box_1801.lower j ∧ 0 ≤ branch_box_1801.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1801, Box.profileLo, Box.profileHi, box_1801]
theorem leaf_1801_BranchSafe : CertificateConsequences.BranchSafe branch_box_1801 := by
  left; refine ⟨branch_box_1801_nonnegative, ?_⟩
  intro z hz; exact leaf_1801_sound hz

theorem leaf_1803_ok : checkAt 527 1000 box_1803 cert_1803 = true := by
  have h := List.all_eq_true.mp batch_36_01_ok accepted_1803 (by simp [batch_36_01_values])
  exact h
theorem leaf_1803_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1803.profileLo box_1803.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1803_ok
theorem branch_box_1803_nonnegative : ∀ j, 0 ≤ branch_box_1803.lower j ∧ 0 ≤ branch_box_1803.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1803, Box.profileLo, Box.profileHi, box_1803]
theorem leaf_1803_BranchSafe : CertificateConsequences.BranchSafe branch_box_1803 := by
  left; refine ⟨branch_box_1803_nonnegative, ?_⟩
  intro z hz; exact leaf_1803_sound hz

theorem leaf_1806_ok : checkAt 527 1000 box_1806 cert_1806 = true := by
  have h := List.all_eq_true.mp batch_36_02_ok accepted_1806 (by simp [batch_36_02_values])
  exact h
theorem leaf_1806_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1806.profileLo box_1806.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1806_ok
theorem branch_box_1806_nonnegative : ∀ j, 0 ≤ branch_box_1806.lower j ∧ 0 ≤ branch_box_1806.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1806, Box.profileLo, Box.profileHi, box_1806]
theorem leaf_1806_BranchSafe : CertificateConsequences.BranchSafe branch_box_1806 := by
  left; refine ⟨branch_box_1806_nonnegative, ?_⟩
  intro z hz; exact leaf_1806_sound hz

theorem leaf_1808_ok : checkAt 527 1000 box_1808 cert_1808 = true := by
  have h := List.all_eq_true.mp batch_36_03_ok accepted_1808 (by simp [batch_36_03_values])
  exact h
theorem leaf_1808_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1808.profileLo box_1808.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1808_ok
theorem branch_box_1808_nonnegative : ∀ j, 0 ≤ branch_box_1808.lower j ∧ 0 ≤ branch_box_1808.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1808, Box.profileLo, Box.profileHi, box_1808]
theorem leaf_1808_BranchSafe : CertificateConsequences.BranchSafe branch_box_1808 := by
  left; refine ⟨branch_box_1808_nonnegative, ?_⟩
  intro z hz; exact leaf_1808_sound hz

theorem leaf_1810_ok : checkAt 527 1000 box_1810 cert_1810 = true := by
  have h := List.all_eq_true.mp batch_36_04_ok accepted_1810 (by simp [batch_36_04_values])
  exact h
theorem leaf_1810_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1810.profileLo box_1810.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1810_ok
theorem branch_box_1810_nonnegative : ∀ j, 0 ≤ branch_box_1810.lower j ∧ 0 ≤ branch_box_1810.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1810, Box.profileLo, Box.profileHi, box_1810]
theorem leaf_1810_BranchSafe : CertificateConsequences.BranchSafe branch_box_1810 := by
  left; refine ⟨branch_box_1810_nonnegative, ?_⟩
  intro z hz; exact leaf_1810_sound hz

theorem leaf_1811_ok : checkAt 527 1000 box_1811 cert_1811 = true := by
  have h := List.all_eq_true.mp batch_36_05_ok accepted_1811 (by simp [batch_36_05_values])
  exact h
theorem leaf_1811_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1811.profileLo box_1811.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1811_ok
theorem branch_box_1811_nonnegative : ∀ j, 0 ≤ branch_box_1811.lower j ∧ 0 ≤ branch_box_1811.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1811, Box.profileLo, Box.profileHi, box_1811]
theorem leaf_1811_BranchSafe : CertificateConsequences.BranchSafe branch_box_1811 := by
  left; refine ⟨branch_box_1811_nonnegative, ?_⟩
  intro z hz; exact leaf_1811_sound hz

theorem leaf_1814_ok : checkAt 527 1000 box_1814 cert_1814 = true := by
  have h := List.all_eq_true.mp batch_36_06_ok accepted_1814 (by simp [batch_36_06_values])
  exact h
theorem leaf_1814_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1814.profileLo box_1814.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1814_ok
theorem branch_box_1814_nonnegative : ∀ j, 0 ≤ branch_box_1814.lower j ∧ 0 ≤ branch_box_1814.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1814, Box.profileLo, Box.profileHi, box_1814]
theorem leaf_1814_BranchSafe : CertificateConsequences.BranchSafe branch_box_1814 := by
  left; refine ⟨branch_box_1814_nonnegative, ?_⟩
  intro z hz; exact leaf_1814_sound hz

theorem leaf_1816_ok : checkAt 527 1000 box_1816 cert_1816 = true := by
  have h := List.all_eq_true.mp batch_36_07_ok accepted_1816 (by simp [batch_36_07_values])
  exact h
theorem leaf_1816_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1816.profileLo box_1816.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1816_ok
theorem branch_box_1816_nonnegative : ∀ j, 0 ≤ branch_box_1816.lower j ∧ 0 ≤ branch_box_1816.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1816, Box.profileLo, Box.profileHi, box_1816]
theorem leaf_1816_BranchSafe : CertificateConsequences.BranchSafe branch_box_1816 := by
  left; refine ⟨branch_box_1816_nonnegative, ?_⟩
  intro z hz; exact leaf_1816_sound hz

theorem leaf_1818_ok : checkAt 527 1000 box_1818 cert_1818 = true := by
  have h := List.all_eq_true.mp batch_36_08_ok accepted_1818 (by simp [batch_36_08_values])
  exact h
theorem leaf_1818_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1818.profileLo box_1818.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1818_ok
theorem branch_box_1818_nonnegative : ∀ j, 0 ≤ branch_box_1818.lower j ∧ 0 ≤ branch_box_1818.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1818, Box.profileLo, Box.profileHi, box_1818]
theorem leaf_1818_BranchSafe : CertificateConsequences.BranchSafe branch_box_1818 := by
  left; refine ⟨branch_box_1818_nonnegative, ?_⟩
  intro z hz; exact leaf_1818_sound hz

theorem leaf_1819_ok : checkAt 527 1000 box_1819 cert_1819 = true := by
  have h := List.all_eq_true.mp batch_36_09_ok accepted_1819 (by simp [batch_36_09_values])
  exact h
theorem leaf_1819_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1819.profileLo box_1819.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1819_ok
theorem branch_box_1819_nonnegative : ∀ j, 0 ≤ branch_box_1819.lower j ∧ 0 ≤ branch_box_1819.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1819, Box.profileLo, Box.profileHi, box_1819]
theorem leaf_1819_BranchSafe : CertificateConsequences.BranchSafe branch_box_1819 := by
  left; refine ⟨branch_box_1819_nonnegative, ?_⟩
  intro z hz; exact leaf_1819_sound hz

theorem leaf_1821_ok : checkAt 527 1000 box_1821 cert_1821 = true := by
  have h := List.all_eq_true.mp batch_36_10_ok accepted_1821 (by simp [batch_36_10_values])
  exact h
theorem leaf_1821_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1821.profileLo box_1821.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1821_ok
theorem branch_box_1821_nonnegative : ∀ j, 0 ≤ branch_box_1821.lower j ∧ 0 ≤ branch_box_1821.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1821, Box.profileLo, Box.profileHi, box_1821]
theorem leaf_1821_BranchSafe : CertificateConsequences.BranchSafe branch_box_1821 := by
  left; refine ⟨branch_box_1821_nonnegative, ?_⟩
  intro z hz; exact leaf_1821_sound hz

theorem leaf_1825_ok : checkAt 527 1000 box_1825 cert_1825 = true := by
  have h := List.all_eq_true.mp batch_36_11_ok accepted_1825 (by simp [batch_36_11_values])
  exact h
theorem leaf_1825_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1825.profileLo box_1825.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1825_ok
theorem branch_box_1825_nonnegative : ∀ j, 0 ≤ branch_box_1825.lower j ∧ 0 ≤ branch_box_1825.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1825, Box.profileLo, Box.profileHi, box_1825]
theorem leaf_1825_BranchSafe : CertificateConsequences.BranchSafe branch_box_1825 := by
  left; refine ⟨branch_box_1825_nonnegative, ?_⟩
  intro z hz; exact leaf_1825_sound hz

theorem leaf_1830_ok : checkAt 527 1000 box_1830 cert_1830 = true := by
  have h := List.all_eq_true.mp batch_36_12_ok accepted_1830 (by simp [batch_36_12_values])
  exact h
theorem leaf_1830_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1830.profileLo box_1830.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1830_ok
theorem branch_box_1830_nonnegative : ∀ j, 0 ≤ branch_box_1830.lower j ∧ 0 ≤ branch_box_1830.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1830, Box.profileLo, Box.profileHi, box_1830]
theorem leaf_1830_BranchSafe : CertificateConsequences.BranchSafe branch_box_1830 := by
  left; refine ⟨branch_box_1830_nonnegative, ?_⟩
  intro z hz; exact leaf_1830_sound hz

theorem leaf_1831_ok : checkAt 527 1000 box_1831 cert_1831 = true := by
  have h := List.all_eq_true.mp batch_36_13_ok accepted_1831 (by simp [batch_36_13_values])
  exact h
theorem leaf_1831_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1831.profileLo box_1831.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1831_ok
theorem branch_box_1831_nonnegative : ∀ j, 0 ≤ branch_box_1831.lower j ∧ 0 ≤ branch_box_1831.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1831, Box.profileLo, Box.profileHi, box_1831]
theorem leaf_1831_BranchSafe : CertificateConsequences.BranchSafe branch_box_1831 := by
  left; refine ⟨branch_box_1831_nonnegative, ?_⟩
  intro z hz; exact leaf_1831_sound hz

theorem leaf_1833_ok : checkAt 527 1000 box_1833 cert_1833 = true := by
  have h := List.all_eq_true.mp batch_36_14_ok accepted_1833 (by simp [batch_36_14_values])
  exact h
theorem leaf_1833_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1833.profileLo box_1833.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1833_ok
theorem branch_box_1833_nonnegative : ∀ j, 0 ≤ branch_box_1833.lower j ∧ 0 ≤ branch_box_1833.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1833, Box.profileLo, Box.profileHi, box_1833]
theorem leaf_1833_BranchSafe : CertificateConsequences.BranchSafe branch_box_1833 := by
  left; refine ⟨branch_box_1833_nonnegative, ?_⟩
  intro z hz; exact leaf_1833_sound hz

theorem leaf_1835_ok : checkAt 527 1000 box_1835 cert_1835 = true := by
  have h := List.all_eq_true.mp batch_36_15_ok accepted_1835 (by simp [batch_36_15_values])
  exact h
theorem leaf_1835_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1835.profileLo box_1835.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1835_ok
theorem branch_box_1835_nonnegative : ∀ j, 0 ≤ branch_box_1835.lower j ∧ 0 ≤ branch_box_1835.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1835, Box.profileLo, Box.profileHi, box_1835]
theorem leaf_1835_BranchSafe : CertificateConsequences.BranchSafe branch_box_1835 := by
  left; refine ⟨branch_box_1835_nonnegative, ?_⟩
  intro z hz; exact leaf_1835_sound hz

theorem leaf_1840_ok : checkAt 527 1000 box_1840 cert_1840 = true := by
  have h := List.all_eq_true.mp batch_36_16_ok accepted_1840 (by simp [batch_36_16_values])
  exact h
theorem leaf_1840_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1840.profileLo box_1840.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1840_ok
theorem branch_box_1840_nonnegative : ∀ j, 0 ≤ branch_box_1840.lower j ∧ 0 ≤ branch_box_1840.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1840, Box.profileLo, Box.profileHi, box_1840]
theorem leaf_1840_BranchSafe : CertificateConsequences.BranchSafe branch_box_1840 := by
  left; refine ⟨branch_box_1840_nonnegative, ?_⟩
  intro z hz; exact leaf_1840_sound hz

theorem leaf_1841_ok : checkAt 527 1000 box_1841 cert_1841 = true := by
  have h := List.all_eq_true.mp batch_36_17_ok accepted_1841 (by simp [batch_36_17_values])
  exact h
theorem leaf_1841_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1841.profileLo box_1841.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1841_ok
theorem branch_box_1841_nonnegative : ∀ j, 0 ≤ branch_box_1841.lower j ∧ 0 ≤ branch_box_1841.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1841, Box.profileLo, Box.profileHi, box_1841]
theorem leaf_1841_BranchSafe : CertificateConsequences.BranchSafe branch_box_1841 := by
  left; refine ⟨branch_box_1841_nonnegative, ?_⟩
  intro z hz; exact leaf_1841_sound hz

theorem leaf_1843_ok : checkAt 527 1000 box_1843 cert_1843 = true := by
  have h := List.all_eq_true.mp batch_36_18_ok accepted_1843 (by simp [batch_36_18_values])
  exact h
theorem leaf_1843_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1843.profileLo box_1843.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1843_ok
theorem branch_box_1843_nonnegative : ∀ j, 0 ≤ branch_box_1843.lower j ∧ 0 ≤ branch_box_1843.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1843, Box.profileLo, Box.profileHi, box_1843]
theorem leaf_1843_BranchSafe : CertificateConsequences.BranchSafe branch_box_1843 := by
  left; refine ⟨branch_box_1843_nonnegative, ?_⟩
  intro z hz; exact leaf_1843_sound hz

theorem leaf_1845_ok : checkAt 527 1000 box_1845 cert_1845 = true := by
  have h := List.all_eq_true.mp batch_36_19_ok accepted_1845 (by simp [batch_36_19_values])
  exact h
theorem leaf_1845_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1845.profileLo box_1845.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1845_ok
theorem branch_box_1845_nonnegative : ∀ j, 0 ≤ branch_box_1845.lower j ∧ 0 ≤ branch_box_1845.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1845, Box.profileLo, Box.profileHi, box_1845]
theorem leaf_1845_BranchSafe : CertificateConsequences.BranchSafe branch_box_1845 := by
  left; refine ⟨branch_box_1845_nonnegative, ?_⟩
  intro z hz; exact leaf_1845_sound hz

theorem leaf_1848_ok : checkAt 527 1000 box_1848 cert_1848 = true := by
  have h := List.all_eq_true.mp batch_36_20_ok accepted_1848 (by simp [batch_36_20_values])
  exact h
theorem leaf_1848_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1848.profileLo box_1848.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1848_ok
theorem branch_box_1848_nonnegative : ∀ j, 0 ≤ branch_box_1848.lower j ∧ 0 ≤ branch_box_1848.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1848, Box.profileLo, Box.profileHi, box_1848]
theorem leaf_1848_BranchSafe : CertificateConsequences.BranchSafe branch_box_1848 := by
  left; refine ⟨branch_box_1848_nonnegative, ?_⟩
  intro z hz; exact leaf_1848_sound hz

theorem leaf_1849_ok : checkAt 527 1000 box_1849 cert_1849 = true := by
  have h := List.all_eq_true.mp batch_36_21_ok accepted_1849 (by simp [batch_36_21_values])
  exact h
theorem leaf_1849_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1849.profileLo box_1849.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1849_ok
theorem branch_box_1849_nonnegative : ∀ j, 0 ≤ branch_box_1849.lower j ∧ 0 ≤ branch_box_1849.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1849, Box.profileLo, Box.profileHi, box_1849]
theorem leaf_1849_BranchSafe : CertificateConsequences.BranchSafe branch_box_1849 := by
  left; refine ⟨branch_box_1849_nonnegative, ?_⟩
  intro z hz; exact leaf_1849_sound hz

#print axioms batch_36_00_ok
#print axioms leaf_1801_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
