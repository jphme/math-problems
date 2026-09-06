import PeaceableQueens.UpperBound.Generated.Even.C527Scaled37Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_37_00_values : List Bool := [accepted_1850]
theorem batch_37_00_ok : batch_37_00_values.all id = true := by decide

def batch_37_01_values : List Bool := [accepted_1851]
theorem batch_37_01_ok : batch_37_01_values.all id = true := by decide

def batch_37_02_values : List Bool := [accepted_1854]
theorem batch_37_02_ok : batch_37_02_values.all id = true := by decide

def batch_37_03_values : List Bool := [accepted_1857]
theorem batch_37_03_ok : batch_37_03_values.all id = true := by decide

def batch_37_04_values : List Bool := [accepted_1858]
theorem batch_37_04_ok : batch_37_04_values.all id = true := by decide

def batch_37_05_values : List Bool := [accepted_1860]
theorem batch_37_05_ok : batch_37_05_values.all id = true := by decide

def batch_37_06_values : List Bool := [accepted_1861]
theorem batch_37_06_ok : batch_37_06_values.all id = true := by decide

def batch_37_07_values : List Bool := [accepted_1863]
theorem batch_37_07_ok : batch_37_07_values.all id = true := by decide

def batch_37_08_values : List Bool := [accepted_1864]
theorem batch_37_08_ok : batch_37_08_values.all id = true := by decide

def batch_37_09_values : List Bool := [accepted_1867]
theorem batch_37_09_ok : batch_37_09_values.all id = true := by decide

def batch_37_10_values : List Bool := [accepted_1868]
theorem batch_37_10_ok : batch_37_10_values.all id = true := by decide

def batch_37_11_values : List Bool := [accepted_1873]
theorem batch_37_11_ok : batch_37_11_values.all id = true := by decide

def batch_37_12_values : List Bool := [accepted_1874]
theorem batch_37_12_ok : batch_37_12_values.all id = true := by decide

def batch_37_13_values : List Bool := [accepted_1877]
theorem batch_37_13_ok : batch_37_13_values.all id = true := by decide

def batch_37_14_values : List Bool := [accepted_1878]
theorem batch_37_14_ok : batch_37_14_values.all id = true := by decide

def batch_37_15_values : List Bool := [accepted_1879]
theorem batch_37_15_ok : batch_37_15_values.all id = true := by decide

def batch_37_16_values : List Bool := [accepted_1880]
theorem batch_37_16_ok : batch_37_16_values.all id = true := by decide

def batch_37_17_values : List Bool := [accepted_1884]
theorem batch_37_17_ok : batch_37_17_values.all id = true := by decide

def batch_37_18_values : List Bool := [accepted_1885]
theorem batch_37_18_ok : batch_37_18_values.all id = true := by decide

def batch_37_19_values : List Bool := [accepted_1888]
theorem batch_37_19_ok : batch_37_19_values.all id = true := by decide

def batch_37_20_values : List Bool := [accepted_1889]
theorem batch_37_20_ok : batch_37_20_values.all id = true := by decide

def batch_37_21_values : List Bool := [accepted_1890]
theorem batch_37_21_ok : batch_37_21_values.all id = true := by decide

def batch_37_22_values : List Bool := [accepted_1893]
theorem batch_37_22_ok : batch_37_22_values.all id = true := by decide

def batch_37_23_values : List Bool := [accepted_1895]
theorem batch_37_23_ok : batch_37_23_values.all id = true := by decide

def batch_37_24_values : List Bool := [accepted_1897]
theorem batch_37_24_ok : batch_37_24_values.all id = true := by decide

def batch_37_25_values : List Bool := [accepted_1898]
theorem batch_37_25_ok : batch_37_25_values.all id = true := by decide

def batch_37_26_values : List Bool := [accepted_1899]
theorem batch_37_26_ok : batch_37_26_values.all id = true := by decide

theorem leaf_1850_ok : checkAt 527 1000 box_1850 cert_1850 = true := by
  have h := List.all_eq_true.mp batch_37_00_ok accepted_1850 (by simp [batch_37_00_values])
  exact h
theorem leaf_1850_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1850.profileLo box_1850.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1850_ok
theorem branch_box_1850_nonnegative : ∀ j, 0 ≤ branch_box_1850.lower j ∧ 0 ≤ branch_box_1850.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1850, Box.profileLo, Box.profileHi, box_1850]
theorem leaf_1850_BranchSafe : CertificateConsequences.BranchSafe branch_box_1850 := by
  left; refine ⟨branch_box_1850_nonnegative, ?_⟩
  intro z hz; exact leaf_1850_sound hz

theorem leaf_1851_ok : checkAt 527 1000 box_1851 cert_1851 = true := by
  have h := List.all_eq_true.mp batch_37_01_ok accepted_1851 (by simp [batch_37_01_values])
  exact h
theorem leaf_1851_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1851.profileLo box_1851.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1851_ok
theorem branch_box_1851_nonnegative : ∀ j, 0 ≤ branch_box_1851.lower j ∧ 0 ≤ branch_box_1851.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1851, Box.profileLo, Box.profileHi, box_1851]
theorem leaf_1851_BranchSafe : CertificateConsequences.BranchSafe branch_box_1851 := by
  left; refine ⟨branch_box_1851_nonnegative, ?_⟩
  intro z hz; exact leaf_1851_sound hz

theorem leaf_1854_ok : checkAt 527 1000 box_1854 cert_1854 = true := by
  have h := List.all_eq_true.mp batch_37_02_ok accepted_1854 (by simp [batch_37_02_values])
  exact h
theorem leaf_1854_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1854.profileLo box_1854.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1854_ok
theorem branch_box_1854_nonnegative : ∀ j, 0 ≤ branch_box_1854.lower j ∧ 0 ≤ branch_box_1854.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1854, Box.profileLo, Box.profileHi, box_1854]
theorem leaf_1854_BranchSafe : CertificateConsequences.BranchSafe branch_box_1854 := by
  left; refine ⟨branch_box_1854_nonnegative, ?_⟩
  intro z hz; exact leaf_1854_sound hz

theorem leaf_1857_ok : checkAt 527 1000 box_1857 cert_1857 = true := by
  have h := List.all_eq_true.mp batch_37_03_ok accepted_1857 (by simp [batch_37_03_values])
  exact h
theorem leaf_1857_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1857.profileLo box_1857.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1857_ok
theorem branch_box_1857_nonnegative : ∀ j, 0 ≤ branch_box_1857.lower j ∧ 0 ≤ branch_box_1857.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1857, Box.profileLo, Box.profileHi, box_1857]
theorem leaf_1857_BranchSafe : CertificateConsequences.BranchSafe branch_box_1857 := by
  left; refine ⟨branch_box_1857_nonnegative, ?_⟩
  intro z hz; exact leaf_1857_sound hz

theorem leaf_1858_ok : checkAt 527 1000 box_1858 cert_1858 = true := by
  have h := List.all_eq_true.mp batch_37_04_ok accepted_1858 (by simp [batch_37_04_values])
  exact h
theorem leaf_1858_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1858.profileLo box_1858.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1858_ok
theorem branch_box_1858_nonnegative : ∀ j, 0 ≤ branch_box_1858.lower j ∧ 0 ≤ branch_box_1858.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1858, Box.profileLo, Box.profileHi, box_1858]
theorem leaf_1858_BranchSafe : CertificateConsequences.BranchSafe branch_box_1858 := by
  left; refine ⟨branch_box_1858_nonnegative, ?_⟩
  intro z hz; exact leaf_1858_sound hz

theorem leaf_1860_ok : checkAt 527 1000 box_1860 cert_1860 = true := by
  have h := List.all_eq_true.mp batch_37_05_ok accepted_1860 (by simp [batch_37_05_values])
  exact h
theorem leaf_1860_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1860.profileLo box_1860.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1860_ok
theorem branch_box_1860_nonnegative : ∀ j, 0 ≤ branch_box_1860.lower j ∧ 0 ≤ branch_box_1860.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1860, Box.profileLo, Box.profileHi, box_1860]
theorem leaf_1860_BranchSafe : CertificateConsequences.BranchSafe branch_box_1860 := by
  left; refine ⟨branch_box_1860_nonnegative, ?_⟩
  intro z hz; exact leaf_1860_sound hz

theorem leaf_1861_ok : checkAt 527 1000 box_1861 cert_1861 = true := by
  have h := List.all_eq_true.mp batch_37_06_ok accepted_1861 (by simp [batch_37_06_values])
  exact h
theorem leaf_1861_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1861.profileLo box_1861.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1861_ok
theorem branch_box_1861_nonnegative : ∀ j, 0 ≤ branch_box_1861.lower j ∧ 0 ≤ branch_box_1861.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1861, Box.profileLo, Box.profileHi, box_1861]
theorem leaf_1861_BranchSafe : CertificateConsequences.BranchSafe branch_box_1861 := by
  left; refine ⟨branch_box_1861_nonnegative, ?_⟩
  intro z hz; exact leaf_1861_sound hz

theorem leaf_1863_ok : checkAt 527 1000 box_1863 cert_1863 = true := by
  have h := List.all_eq_true.mp batch_37_07_ok accepted_1863 (by simp [batch_37_07_values])
  exact h
theorem leaf_1863_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1863.profileLo box_1863.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1863_ok
theorem branch_box_1863_nonnegative : ∀ j, 0 ≤ branch_box_1863.lower j ∧ 0 ≤ branch_box_1863.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1863, Box.profileLo, Box.profileHi, box_1863]
theorem leaf_1863_BranchSafe : CertificateConsequences.BranchSafe branch_box_1863 := by
  left; refine ⟨branch_box_1863_nonnegative, ?_⟩
  intro z hz; exact leaf_1863_sound hz

theorem leaf_1864_ok : checkAt 527 1000 box_1864 cert_1864 = true := by
  have h := List.all_eq_true.mp batch_37_08_ok accepted_1864 (by simp [batch_37_08_values])
  exact h
theorem leaf_1864_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1864.profileLo box_1864.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1864_ok
theorem branch_box_1864_nonnegative : ∀ j, 0 ≤ branch_box_1864.lower j ∧ 0 ≤ branch_box_1864.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1864, Box.profileLo, Box.profileHi, box_1864]
theorem leaf_1864_BranchSafe : CertificateConsequences.BranchSafe branch_box_1864 := by
  left; refine ⟨branch_box_1864_nonnegative, ?_⟩
  intro z hz; exact leaf_1864_sound hz

theorem leaf_1867_ok : checkAt 527 1000 box_1867 cert_1867 = true := by
  have h := List.all_eq_true.mp batch_37_09_ok accepted_1867 (by simp [batch_37_09_values])
  exact h
theorem leaf_1867_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1867.profileLo box_1867.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1867_ok
theorem branch_box_1867_nonnegative : ∀ j, 0 ≤ branch_box_1867.lower j ∧ 0 ≤ branch_box_1867.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1867, Box.profileLo, Box.profileHi, box_1867]
theorem leaf_1867_BranchSafe : CertificateConsequences.BranchSafe branch_box_1867 := by
  left; refine ⟨branch_box_1867_nonnegative, ?_⟩
  intro z hz; exact leaf_1867_sound hz

theorem leaf_1868_ok : checkAt 527 1000 box_1868 cert_1868 = true := by
  have h := List.all_eq_true.mp batch_37_10_ok accepted_1868 (by simp [batch_37_10_values])
  exact h
theorem leaf_1868_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1868.profileLo box_1868.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1868_ok
theorem branch_box_1868_nonnegative : ∀ j, 0 ≤ branch_box_1868.lower j ∧ 0 ≤ branch_box_1868.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1868, Box.profileLo, Box.profileHi, box_1868]
theorem leaf_1868_BranchSafe : CertificateConsequences.BranchSafe branch_box_1868 := by
  left; refine ⟨branch_box_1868_nonnegative, ?_⟩
  intro z hz; exact leaf_1868_sound hz

theorem leaf_1873_ok : checkAt 527 1000 box_1873 cert_1873 = true := by
  have h := List.all_eq_true.mp batch_37_11_ok accepted_1873 (by simp [batch_37_11_values])
  exact h
theorem leaf_1873_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1873.profileLo box_1873.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1873_ok
theorem branch_box_1873_nonnegative : ∀ j, 0 ≤ branch_box_1873.lower j ∧ 0 ≤ branch_box_1873.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1873, Box.profileLo, Box.profileHi, box_1873]
theorem leaf_1873_BranchSafe : CertificateConsequences.BranchSafe branch_box_1873 := by
  left; refine ⟨branch_box_1873_nonnegative, ?_⟩
  intro z hz; exact leaf_1873_sound hz

theorem leaf_1874_ok : checkAt 527 1000 box_1874 cert_1874 = true := by
  have h := List.all_eq_true.mp batch_37_12_ok accepted_1874 (by simp [batch_37_12_values])
  exact h
theorem leaf_1874_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1874.profileLo box_1874.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1874_ok
theorem branch_box_1874_nonnegative : ∀ j, 0 ≤ branch_box_1874.lower j ∧ 0 ≤ branch_box_1874.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1874, Box.profileLo, Box.profileHi, box_1874]
theorem leaf_1874_BranchSafe : CertificateConsequences.BranchSafe branch_box_1874 := by
  left; refine ⟨branch_box_1874_nonnegative, ?_⟩
  intro z hz; exact leaf_1874_sound hz

theorem leaf_1877_ok : checkAt 527 1000 box_1877 cert_1877 = true := by
  have h := List.all_eq_true.mp batch_37_13_ok accepted_1877 (by simp [batch_37_13_values])
  exact h
theorem leaf_1877_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1877.profileLo box_1877.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1877_ok
theorem branch_box_1877_nonnegative : ∀ j, 0 ≤ branch_box_1877.lower j ∧ 0 ≤ branch_box_1877.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1877, Box.profileLo, Box.profileHi, box_1877]
theorem leaf_1877_BranchSafe : CertificateConsequences.BranchSafe branch_box_1877 := by
  left; refine ⟨branch_box_1877_nonnegative, ?_⟩
  intro z hz; exact leaf_1877_sound hz

theorem leaf_1878_ok : checkAt 527 1000 box_1878 cert_1878 = true := by
  have h := List.all_eq_true.mp batch_37_14_ok accepted_1878 (by simp [batch_37_14_values])
  exact h
theorem leaf_1878_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1878.profileLo box_1878.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1878_ok
theorem branch_box_1878_nonnegative : ∀ j, 0 ≤ branch_box_1878.lower j ∧ 0 ≤ branch_box_1878.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1878, Box.profileLo, Box.profileHi, box_1878]
theorem leaf_1878_BranchSafe : CertificateConsequences.BranchSafe branch_box_1878 := by
  left; refine ⟨branch_box_1878_nonnegative, ?_⟩
  intro z hz; exact leaf_1878_sound hz

theorem leaf_1879_ok : checkAt 527 1000 box_1879 cert_1879 = true := by
  have h := List.all_eq_true.mp batch_37_15_ok accepted_1879 (by simp [batch_37_15_values])
  exact h
theorem leaf_1879_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1879.profileLo box_1879.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1879_ok
theorem branch_box_1879_nonnegative : ∀ j, 0 ≤ branch_box_1879.lower j ∧ 0 ≤ branch_box_1879.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1879, Box.profileLo, Box.profileHi, box_1879]
theorem leaf_1879_BranchSafe : CertificateConsequences.BranchSafe branch_box_1879 := by
  left; refine ⟨branch_box_1879_nonnegative, ?_⟩
  intro z hz; exact leaf_1879_sound hz

theorem leaf_1880_ok : checkAt 527 1000 box_1880 cert_1880 = true := by
  have h := List.all_eq_true.mp batch_37_16_ok accepted_1880 (by simp [batch_37_16_values])
  exact h
theorem leaf_1880_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1880.profileLo box_1880.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1880_ok
theorem branch_box_1880_nonnegative : ∀ j, 0 ≤ branch_box_1880.lower j ∧ 0 ≤ branch_box_1880.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1880, Box.profileLo, Box.profileHi, box_1880]
theorem leaf_1880_BranchSafe : CertificateConsequences.BranchSafe branch_box_1880 := by
  left; refine ⟨branch_box_1880_nonnegative, ?_⟩
  intro z hz; exact leaf_1880_sound hz

theorem leaf_1884_ok : checkAt 527 1000 box_1884 cert_1884 = true := by
  have h := List.all_eq_true.mp batch_37_17_ok accepted_1884 (by simp [batch_37_17_values])
  exact h
theorem leaf_1884_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1884.profileLo box_1884.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1884_ok
theorem branch_box_1884_nonnegative : ∀ j, 0 ≤ branch_box_1884.lower j ∧ 0 ≤ branch_box_1884.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1884, Box.profileLo, Box.profileHi, box_1884]
theorem leaf_1884_BranchSafe : CertificateConsequences.BranchSafe branch_box_1884 := by
  left; refine ⟨branch_box_1884_nonnegative, ?_⟩
  intro z hz; exact leaf_1884_sound hz

theorem leaf_1885_ok : checkAt 527 1000 box_1885 cert_1885 = true := by
  have h := List.all_eq_true.mp batch_37_18_ok accepted_1885 (by simp [batch_37_18_values])
  exact h
theorem leaf_1885_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1885.profileLo box_1885.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1885_ok
theorem branch_box_1885_nonnegative : ∀ j, 0 ≤ branch_box_1885.lower j ∧ 0 ≤ branch_box_1885.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1885, Box.profileLo, Box.profileHi, box_1885]
theorem leaf_1885_BranchSafe : CertificateConsequences.BranchSafe branch_box_1885 := by
  left; refine ⟨branch_box_1885_nonnegative, ?_⟩
  intro z hz; exact leaf_1885_sound hz

theorem leaf_1888_ok : checkAt 527 1000 box_1888 cert_1888 = true := by
  have h := List.all_eq_true.mp batch_37_19_ok accepted_1888 (by simp [batch_37_19_values])
  exact h
theorem leaf_1888_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1888.profileLo box_1888.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1888_ok
theorem branch_box_1888_nonnegative : ∀ j, 0 ≤ branch_box_1888.lower j ∧ 0 ≤ branch_box_1888.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1888, Box.profileLo, Box.profileHi, box_1888]
theorem leaf_1888_BranchSafe : CertificateConsequences.BranchSafe branch_box_1888 := by
  left; refine ⟨branch_box_1888_nonnegative, ?_⟩
  intro z hz; exact leaf_1888_sound hz

theorem leaf_1889_ok : checkAt 527 1000 box_1889 cert_1889 = true := by
  have h := List.all_eq_true.mp batch_37_20_ok accepted_1889 (by simp [batch_37_20_values])
  exact h
theorem leaf_1889_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1889.profileLo box_1889.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1889_ok
theorem branch_box_1889_nonnegative : ∀ j, 0 ≤ branch_box_1889.lower j ∧ 0 ≤ branch_box_1889.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1889, Box.profileLo, Box.profileHi, box_1889]
theorem leaf_1889_BranchSafe : CertificateConsequences.BranchSafe branch_box_1889 := by
  left; refine ⟨branch_box_1889_nonnegative, ?_⟩
  intro z hz; exact leaf_1889_sound hz

theorem leaf_1890_ok : checkAt 527 1000 box_1890 cert_1890 = true := by
  have h := List.all_eq_true.mp batch_37_21_ok accepted_1890 (by simp [batch_37_21_values])
  exact h
theorem leaf_1890_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1890.profileLo box_1890.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1890_ok
theorem branch_box_1890_nonnegative : ∀ j, 0 ≤ branch_box_1890.lower j ∧ 0 ≤ branch_box_1890.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1890, Box.profileLo, Box.profileHi, box_1890]
theorem leaf_1890_BranchSafe : CertificateConsequences.BranchSafe branch_box_1890 := by
  left; refine ⟨branch_box_1890_nonnegative, ?_⟩
  intro z hz; exact leaf_1890_sound hz

theorem leaf_1893_ok : checkAt 527 1000 box_1893 cert_1893 = true := by
  have h := List.all_eq_true.mp batch_37_22_ok accepted_1893 (by simp [batch_37_22_values])
  exact h
theorem leaf_1893_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1893.profileLo box_1893.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1893_ok
theorem branch_box_1893_nonnegative : ∀ j, 0 ≤ branch_box_1893.lower j ∧ 0 ≤ branch_box_1893.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1893, Box.profileLo, Box.profileHi, box_1893]
theorem leaf_1893_BranchSafe : CertificateConsequences.BranchSafe branch_box_1893 := by
  left; refine ⟨branch_box_1893_nonnegative, ?_⟩
  intro z hz; exact leaf_1893_sound hz

theorem leaf_1895_ok : checkAt 527 1000 box_1895 cert_1895 = true := by
  have h := List.all_eq_true.mp batch_37_23_ok accepted_1895 (by simp [batch_37_23_values])
  exact h
theorem leaf_1895_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1895.profileLo box_1895.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1895_ok
theorem branch_box_1895_nonnegative : ∀ j, 0 ≤ branch_box_1895.lower j ∧ 0 ≤ branch_box_1895.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1895, Box.profileLo, Box.profileHi, box_1895]
theorem leaf_1895_BranchSafe : CertificateConsequences.BranchSafe branch_box_1895 := by
  left; refine ⟨branch_box_1895_nonnegative, ?_⟩
  intro z hz; exact leaf_1895_sound hz

theorem leaf_1897_ok : checkAt 527 1000 box_1897 cert_1897 = true := by
  have h := List.all_eq_true.mp batch_37_24_ok accepted_1897 (by simp [batch_37_24_values])
  exact h
theorem leaf_1897_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1897.profileLo box_1897.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1897_ok
theorem branch_box_1897_nonnegative : ∀ j, 0 ≤ branch_box_1897.lower j ∧ 0 ≤ branch_box_1897.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1897, Box.profileLo, Box.profileHi, box_1897]
theorem leaf_1897_BranchSafe : CertificateConsequences.BranchSafe branch_box_1897 := by
  left; refine ⟨branch_box_1897_nonnegative, ?_⟩
  intro z hz; exact leaf_1897_sound hz

theorem leaf_1898_ok : checkAt 527 1000 box_1898 cert_1898 = true := by
  have h := List.all_eq_true.mp batch_37_25_ok accepted_1898 (by simp [batch_37_25_values])
  exact h
theorem leaf_1898_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1898.profileLo box_1898.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1898_ok
theorem branch_box_1898_nonnegative : ∀ j, 0 ≤ branch_box_1898.lower j ∧ 0 ≤ branch_box_1898.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1898, Box.profileLo, Box.profileHi, box_1898]
theorem leaf_1898_BranchSafe : CertificateConsequences.BranchSafe branch_box_1898 := by
  left; refine ⟨branch_box_1898_nonnegative, ?_⟩
  intro z hz; exact leaf_1898_sound hz

theorem leaf_1899_ok : checkAt 527 1000 box_1899 cert_1899 = true := by
  have h := List.all_eq_true.mp batch_37_26_ok accepted_1899 (by simp [batch_37_26_values])
  exact h
theorem leaf_1899_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1899.profileLo box_1899.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1899_ok
theorem branch_box_1899_nonnegative : ∀ j, 0 ≤ branch_box_1899.lower j ∧ 0 ≤ branch_box_1899.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1899, Box.profileLo, Box.profileHi, box_1899]
theorem leaf_1899_BranchSafe : CertificateConsequences.BranchSafe branch_box_1899 := by
  left; refine ⟨branch_box_1899_nonnegative, ?_⟩
  intro z hz; exact leaf_1899_sound hz

#print axioms batch_37_00_ok
#print axioms leaf_1850_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
