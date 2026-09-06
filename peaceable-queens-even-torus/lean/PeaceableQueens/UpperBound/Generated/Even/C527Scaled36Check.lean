import PeaceableQueens.UpperBound.Generated.Even.C527Scaled36Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_36_00_values : List Bool := [accepted_1805]
theorem batch_36_00_ok : batch_36_00_values.all id = true := by decide

def batch_36_01_values : List Bool := [accepted_1807]
theorem batch_36_01_ok : batch_36_01_values.all id = true := by decide

def batch_36_02_values : List Bool := [accepted_1808]
theorem batch_36_02_ok : batch_36_02_values.all id = true := by decide

def batch_36_03_values : List Bool := [accepted_1809]
theorem batch_36_03_ok : batch_36_03_values.all id = true := by decide

def batch_36_04_values : List Bool := [accepted_1810]
theorem batch_36_04_ok : batch_36_04_values.all id = true := by decide

def batch_36_05_values : List Bool := [accepted_1812]
theorem batch_36_05_ok : batch_36_05_values.all id = true := by decide

def batch_36_06_values : List Bool := [accepted_1813]
theorem batch_36_06_ok : batch_36_06_values.all id = true := by decide

def batch_36_07_values : List Bool := [accepted_1814]
theorem batch_36_07_ok : batch_36_07_values.all id = true := by decide

def batch_36_08_values : List Bool := [accepted_1817]
theorem batch_36_08_ok : batch_36_08_values.all id = true := by decide

def batch_36_09_values : List Bool := [accepted_1818]
theorem batch_36_09_ok : batch_36_09_values.all id = true := by decide

def batch_36_10_values : List Bool := [accepted_1821]
theorem batch_36_10_ok : batch_36_10_values.all id = true := by decide

def batch_36_11_values : List Bool := [accepted_1822]
theorem batch_36_11_ok : batch_36_11_values.all id = true := by decide

def batch_36_12_values : List Bool := [accepted_1823]
theorem batch_36_12_ok : batch_36_12_values.all id = true := by decide

def batch_36_13_values : List Bool := [accepted_1824]
theorem batch_36_13_ok : batch_36_13_values.all id = true := by decide

def batch_36_14_values : List Bool := [accepted_1829]
theorem batch_36_14_ok : batch_36_14_values.all id = true := by decide

def batch_36_15_values : List Bool := [accepted_1830]
theorem batch_36_15_ok : batch_36_15_values.all id = true := by decide

def batch_36_16_values : List Bool := [accepted_1833]
theorem batch_36_16_ok : batch_36_16_values.all id = true := by decide

def batch_36_17_values : List Bool := [accepted_1835]
theorem batch_36_17_ok : batch_36_17_values.all id = true := by decide

def batch_36_18_values : List Bool := [accepted_1836]
theorem batch_36_18_ok : batch_36_18_values.all id = true := by decide

def batch_36_19_values : List Bool := [accepted_1837]
theorem batch_36_19_ok : batch_36_19_values.all id = true := by decide

def batch_36_20_values : List Bool := [accepted_1838]
theorem batch_36_20_ok : batch_36_20_values.all id = true := by decide

def batch_36_21_values : List Bool := [accepted_1841]
theorem batch_36_21_ok : batch_36_21_values.all id = true := by decide

def batch_36_22_values : List Bool := [accepted_1842]
theorem batch_36_22_ok : batch_36_22_values.all id = true := by decide

def batch_36_23_values : List Bool := [accepted_1843]
theorem batch_36_23_ok : batch_36_23_values.all id = true := by decide

def batch_36_24_values : List Bool := [accepted_1845]
theorem batch_36_24_ok : batch_36_24_values.all id = true := by decide

def batch_36_25_values : List Bool := [accepted_1846]
theorem batch_36_25_ok : batch_36_25_values.all id = true := by decide

def batch_36_26_values : List Bool := [accepted_1847]
theorem batch_36_26_ok : batch_36_26_values.all id = true := by decide

def batch_36_27_values : List Bool := [accepted_1849]
theorem batch_36_27_ok : batch_36_27_values.all id = true := by decide

theorem leaf_1805_ok : checkAt 527 1000 box_1805 cert_1805 = true := by
  have h := List.all_eq_true.mp batch_36_00_ok accepted_1805 (by simp [batch_36_00_values])
  exact h
theorem leaf_1805_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1805.profileLo box_1805.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1805_ok
theorem branch_box_1805_nonnegative : ∀ j, 0 ≤ branch_box_1805.lower j ∧ 0 ≤ branch_box_1805.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1805, Box.profileLo, Box.profileHi, box_1805]
theorem leaf_1805_BranchSafe : CertificateConsequences.BranchSafe branch_box_1805 := by
  left; refine ⟨branch_box_1805_nonnegative, ?_⟩
  intro z hz; exact leaf_1805_sound hz

theorem leaf_1807_ok : checkAt 527 1000 box_1807 cert_1807 = true := by
  have h := List.all_eq_true.mp batch_36_01_ok accepted_1807 (by simp [batch_36_01_values])
  exact h
theorem leaf_1807_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1807.profileLo box_1807.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1807_ok
theorem branch_box_1807_nonnegative : ∀ j, 0 ≤ branch_box_1807.lower j ∧ 0 ≤ branch_box_1807.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1807, Box.profileLo, Box.profileHi, box_1807]
theorem leaf_1807_BranchSafe : CertificateConsequences.BranchSafe branch_box_1807 := by
  left; refine ⟨branch_box_1807_nonnegative, ?_⟩
  intro z hz; exact leaf_1807_sound hz

theorem leaf_1808_ok : checkAt 527 1000 box_1808 cert_1808 = true := by
  have h := List.all_eq_true.mp batch_36_02_ok accepted_1808 (by simp [batch_36_02_values])
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

theorem leaf_1809_ok : checkAt 527 1000 box_1809 cert_1809 = true := by
  have h := List.all_eq_true.mp batch_36_03_ok accepted_1809 (by simp [batch_36_03_values])
  exact h
theorem leaf_1809_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1809.profileLo box_1809.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1809_ok
theorem branch_box_1809_nonnegative : ∀ j, 0 ≤ branch_box_1809.lower j ∧ 0 ≤ branch_box_1809.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1809, Box.profileLo, Box.profileHi, box_1809]
theorem leaf_1809_BranchSafe : CertificateConsequences.BranchSafe branch_box_1809 := by
  left; refine ⟨branch_box_1809_nonnegative, ?_⟩
  intro z hz; exact leaf_1809_sound hz

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

theorem leaf_1812_ok : checkAt 527 1000 box_1812 cert_1812 = true := by
  have h := List.all_eq_true.mp batch_36_05_ok accepted_1812 (by simp [batch_36_05_values])
  exact h
theorem leaf_1812_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1812.profileLo box_1812.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1812_ok
theorem branch_box_1812_nonnegative : ∀ j, 0 ≤ branch_box_1812.lower j ∧ 0 ≤ branch_box_1812.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1812, Box.profileLo, Box.profileHi, box_1812]
theorem leaf_1812_BranchSafe : CertificateConsequences.BranchSafe branch_box_1812 := by
  left; refine ⟨branch_box_1812_nonnegative, ?_⟩
  intro z hz; exact leaf_1812_sound hz

theorem leaf_1813_ok : checkAt 527 1000 box_1813 cert_1813 = true := by
  have h := List.all_eq_true.mp batch_36_06_ok accepted_1813 (by simp [batch_36_06_values])
  exact h
theorem leaf_1813_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1813.profileLo box_1813.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1813_ok
theorem branch_box_1813_nonnegative : ∀ j, 0 ≤ branch_box_1813.lower j ∧ 0 ≤ branch_box_1813.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1813, Box.profileLo, Box.profileHi, box_1813]
theorem leaf_1813_BranchSafe : CertificateConsequences.BranchSafe branch_box_1813 := by
  left; refine ⟨branch_box_1813_nonnegative, ?_⟩
  intro z hz; exact leaf_1813_sound hz

theorem leaf_1814_ok : checkAt 527 1000 box_1814 cert_1814 = true := by
  have h := List.all_eq_true.mp batch_36_07_ok accepted_1814 (by simp [batch_36_07_values])
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

theorem leaf_1817_ok : checkAt 527 1000 box_1817 cert_1817 = true := by
  have h := List.all_eq_true.mp batch_36_08_ok accepted_1817 (by simp [batch_36_08_values])
  exact h
theorem leaf_1817_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1817.profileLo box_1817.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1817_ok
theorem branch_box_1817_nonnegative : ∀ j, 0 ≤ branch_box_1817.lower j ∧ 0 ≤ branch_box_1817.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1817, Box.profileLo, Box.profileHi, box_1817]
theorem leaf_1817_BranchSafe : CertificateConsequences.BranchSafe branch_box_1817 := by
  left; refine ⟨branch_box_1817_nonnegative, ?_⟩
  intro z hz; exact leaf_1817_sound hz

theorem leaf_1818_ok : checkAt 527 1000 box_1818 cert_1818 = true := by
  have h := List.all_eq_true.mp batch_36_09_ok accepted_1818 (by simp [batch_36_09_values])
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

theorem leaf_1822_ok : checkAt 527 1000 box_1822 cert_1822 = true := by
  have h := List.all_eq_true.mp batch_36_11_ok accepted_1822 (by simp [batch_36_11_values])
  exact h
theorem leaf_1822_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1822.profileLo box_1822.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1822_ok
theorem branch_box_1822_nonnegative : ∀ j, 0 ≤ branch_box_1822.lower j ∧ 0 ≤ branch_box_1822.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1822, Box.profileLo, Box.profileHi, box_1822]
theorem leaf_1822_BranchSafe : CertificateConsequences.BranchSafe branch_box_1822 := by
  left; refine ⟨branch_box_1822_nonnegative, ?_⟩
  intro z hz; exact leaf_1822_sound hz

theorem leaf_1823_ok : checkAt 527 1000 box_1823 cert_1823 = true := by
  have h := List.all_eq_true.mp batch_36_12_ok accepted_1823 (by simp [batch_36_12_values])
  exact h
theorem leaf_1823_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1823.profileLo box_1823.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1823_ok
theorem branch_box_1823_nonnegative : ∀ j, 0 ≤ branch_box_1823.lower j ∧ 0 ≤ branch_box_1823.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1823, Box.profileLo, Box.profileHi, box_1823]
theorem leaf_1823_BranchSafe : CertificateConsequences.BranchSafe branch_box_1823 := by
  left; refine ⟨branch_box_1823_nonnegative, ?_⟩
  intro z hz; exact leaf_1823_sound hz

theorem leaf_1824_ok : checkAt 527 1000 box_1824 cert_1824 = true := by
  have h := List.all_eq_true.mp batch_36_13_ok accepted_1824 (by simp [batch_36_13_values])
  exact h
theorem leaf_1824_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1824.profileLo box_1824.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1824_ok
theorem branch_box_1824_nonnegative : ∀ j, 0 ≤ branch_box_1824.lower j ∧ 0 ≤ branch_box_1824.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1824, Box.profileLo, Box.profileHi, box_1824]
theorem leaf_1824_BranchSafe : CertificateConsequences.BranchSafe branch_box_1824 := by
  left; refine ⟨branch_box_1824_nonnegative, ?_⟩
  intro z hz; exact leaf_1824_sound hz

theorem leaf_1829_ok : checkAt 527 1000 box_1829 cert_1829 = true := by
  have h := List.all_eq_true.mp batch_36_14_ok accepted_1829 (by simp [batch_36_14_values])
  exact h
theorem leaf_1829_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1829.profileLo box_1829.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1829_ok
theorem branch_box_1829_nonnegative : ∀ j, 0 ≤ branch_box_1829.lower j ∧ 0 ≤ branch_box_1829.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1829, Box.profileLo, Box.profileHi, box_1829]
theorem leaf_1829_BranchSafe : CertificateConsequences.BranchSafe branch_box_1829 := by
  left; refine ⟨branch_box_1829_nonnegative, ?_⟩
  intro z hz; exact leaf_1829_sound hz

theorem leaf_1830_ok : checkAt 527 1000 box_1830 cert_1830 = true := by
  have h := List.all_eq_true.mp batch_36_15_ok accepted_1830 (by simp [batch_36_15_values])
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

theorem leaf_1833_ok : checkAt 527 1000 box_1833 cert_1833 = true := by
  have h := List.all_eq_true.mp batch_36_16_ok accepted_1833 (by simp [batch_36_16_values])
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
  have h := List.all_eq_true.mp batch_36_17_ok accepted_1835 (by simp [batch_36_17_values])
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

theorem leaf_1836_ok : checkAt 527 1000 box_1836 cert_1836 = true := by
  have h := List.all_eq_true.mp batch_36_18_ok accepted_1836 (by simp [batch_36_18_values])
  exact h
theorem leaf_1836_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1836.profileLo box_1836.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1836_ok
theorem branch_box_1836_nonnegative : ∀ j, 0 ≤ branch_box_1836.lower j ∧ 0 ≤ branch_box_1836.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1836, Box.profileLo, Box.profileHi, box_1836]
theorem leaf_1836_BranchSafe : CertificateConsequences.BranchSafe branch_box_1836 := by
  left; refine ⟨branch_box_1836_nonnegative, ?_⟩
  intro z hz; exact leaf_1836_sound hz

theorem leaf_1837_ok : checkAt 527 1000 box_1837 cert_1837 = true := by
  have h := List.all_eq_true.mp batch_36_19_ok accepted_1837 (by simp [batch_36_19_values])
  exact h
theorem leaf_1837_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1837.profileLo box_1837.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1837_ok
theorem branch_box_1837_nonnegative : ∀ j, 0 ≤ branch_box_1837.lower j ∧ 0 ≤ branch_box_1837.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1837, Box.profileLo, Box.profileHi, box_1837]
theorem leaf_1837_BranchSafe : CertificateConsequences.BranchSafe branch_box_1837 := by
  left; refine ⟨branch_box_1837_nonnegative, ?_⟩
  intro z hz; exact leaf_1837_sound hz

theorem leaf_1838_ok : checkAt 527 1000 box_1838 cert_1838 = true := by
  have h := List.all_eq_true.mp batch_36_20_ok accepted_1838 (by simp [batch_36_20_values])
  exact h
theorem leaf_1838_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1838.profileLo box_1838.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1838_ok
theorem branch_box_1838_nonnegative : ∀ j, 0 ≤ branch_box_1838.lower j ∧ 0 ≤ branch_box_1838.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1838, Box.profileLo, Box.profileHi, box_1838]
theorem leaf_1838_BranchSafe : CertificateConsequences.BranchSafe branch_box_1838 := by
  left; refine ⟨branch_box_1838_nonnegative, ?_⟩
  intro z hz; exact leaf_1838_sound hz

theorem leaf_1841_ok : checkAt 527 1000 box_1841 cert_1841 = true := by
  have h := List.all_eq_true.mp batch_36_21_ok accepted_1841 (by simp [batch_36_21_values])
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

theorem leaf_1842_ok : checkAt 527 1000 box_1842 cert_1842 = true := by
  have h := List.all_eq_true.mp batch_36_22_ok accepted_1842 (by simp [batch_36_22_values])
  exact h
theorem leaf_1842_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1842.profileLo box_1842.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1842_ok
theorem branch_box_1842_nonnegative : ∀ j, 0 ≤ branch_box_1842.lower j ∧ 0 ≤ branch_box_1842.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1842, Box.profileLo, Box.profileHi, box_1842]
theorem leaf_1842_BranchSafe : CertificateConsequences.BranchSafe branch_box_1842 := by
  left; refine ⟨branch_box_1842_nonnegative, ?_⟩
  intro z hz; exact leaf_1842_sound hz

theorem leaf_1843_ok : checkAt 527 1000 box_1843 cert_1843 = true := by
  have h := List.all_eq_true.mp batch_36_23_ok accepted_1843 (by simp [batch_36_23_values])
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
  have h := List.all_eq_true.mp batch_36_24_ok accepted_1845 (by simp [batch_36_24_values])
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

theorem leaf_1846_ok : checkAt 527 1000 box_1846 cert_1846 = true := by
  have h := List.all_eq_true.mp batch_36_25_ok accepted_1846 (by simp [batch_36_25_values])
  exact h
theorem leaf_1846_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1846.profileLo box_1846.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1846_ok
theorem branch_box_1846_nonnegative : ∀ j, 0 ≤ branch_box_1846.lower j ∧ 0 ≤ branch_box_1846.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1846, Box.profileLo, Box.profileHi, box_1846]
theorem leaf_1846_BranchSafe : CertificateConsequences.BranchSafe branch_box_1846 := by
  left; refine ⟨branch_box_1846_nonnegative, ?_⟩
  intro z hz; exact leaf_1846_sound hz

theorem leaf_1847_ok : checkAt 527 1000 box_1847 cert_1847 = true := by
  have h := List.all_eq_true.mp batch_36_26_ok accepted_1847 (by simp [batch_36_26_values])
  exact h
theorem leaf_1847_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1847.profileLo box_1847.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1847_ok
theorem branch_box_1847_nonnegative : ∀ j, 0 ≤ branch_box_1847.lower j ∧ 0 ≤ branch_box_1847.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1847, Box.profileLo, Box.profileHi, box_1847]
theorem leaf_1847_BranchSafe : CertificateConsequences.BranchSafe branch_box_1847 := by
  left; refine ⟨branch_box_1847_nonnegative, ?_⟩
  intro z hz; exact leaf_1847_sound hz

theorem leaf_1849_ok : checkAt 527 1000 box_1849 cert_1849 = true := by
  have h := List.all_eq_true.mp batch_36_27_ok accepted_1849 (by simp [batch_36_27_values])
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
#print axioms leaf_1805_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
