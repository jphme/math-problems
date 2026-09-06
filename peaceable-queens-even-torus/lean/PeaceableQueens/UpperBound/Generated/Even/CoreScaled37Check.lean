import PeaceableQueens.UpperBound.Generated.Even.CoreScaled37Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_37_00_values : List Bool := [accepted_1851]
theorem batch_37_00_ok : batch_37_00_values.all id = true := by decide

def batch_37_01_values : List Bool := [accepted_1853]
theorem batch_37_01_ok : batch_37_01_values.all id = true := by decide

def batch_37_02_values : List Bool := [accepted_1856]
theorem batch_37_02_ok : batch_37_02_values.all id = true := by decide

def batch_37_03_values : List Bool := [accepted_1858]
theorem batch_37_03_ok : batch_37_03_values.all id = true := by decide

def batch_37_04_values : List Bool := [accepted_1864]
theorem batch_37_04_ok : batch_37_04_values.all id = true := by decide

def batch_37_05_values : List Bool := [accepted_1865]
theorem batch_37_05_ok : batch_37_05_values.all id = true := by decide

def batch_37_06_values : List Bool := [accepted_1867]
theorem batch_37_06_ok : batch_37_06_values.all id = true := by decide

def batch_37_07_values : List Bool := [accepted_1869]
theorem batch_37_07_ok : batch_37_07_values.all id = true := by decide

def batch_37_08_values : List Bool := [accepted_1874]
theorem batch_37_08_ok : batch_37_08_values.all id = true := by decide

def batch_37_09_values : List Bool := [accepted_1875]
theorem batch_37_09_ok : batch_37_09_values.all id = true := by decide

def batch_37_10_values : List Bool := [accepted_1877]
theorem batch_37_10_ok : batch_37_10_values.all id = true := by decide

def batch_37_11_values : List Bool := [accepted_1879]
theorem batch_37_11_ok : batch_37_11_values.all id = true := by decide

def batch_37_12_values : List Bool := [accepted_1882]
theorem batch_37_12_ok : batch_37_12_values.all id = true := by decide

def batch_37_13_values : List Bool := [accepted_1883]
theorem batch_37_13_ok : batch_37_13_values.all id = true := by decide

def batch_37_14_values : List Bool := [accepted_1885]
theorem batch_37_14_ok : batch_37_14_values.all id = true := by decide

def batch_37_15_values : List Bool := [accepted_1887]
theorem batch_37_15_ok : batch_37_15_values.all id = true := by decide

def batch_37_16_values : List Bool := [accepted_1894]
theorem batch_37_16_ok : batch_37_16_values.all id = true := by decide

def batch_37_17_values : List Bool := [accepted_1896]
theorem batch_37_17_ok : batch_37_17_values.all id = true := by decide

def batch_37_18_values : List Bool := [accepted_1898]
theorem batch_37_18_ok : batch_37_18_values.all id = true := by decide

theorem leaf_1851_ok : checkAt 527 1000 box_1851 cert_1851 = true := by
  have h := List.all_eq_true.mp batch_37_00_ok accepted_1851 (by simp [batch_37_00_values])
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

theorem leaf_1853_ok : checkAt 527 1000 box_1853 cert_1853 = true := by
  have h := List.all_eq_true.mp batch_37_01_ok accepted_1853 (by simp [batch_37_01_values])
  exact h
theorem leaf_1853_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1853.profileLo box_1853.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1853_ok
theorem branch_box_1853_nonnegative : ∀ j, 0 ≤ branch_box_1853.lower j ∧ 0 ≤ branch_box_1853.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1853, Box.profileLo, Box.profileHi, box_1853]
theorem leaf_1853_BranchSafe : CertificateConsequences.BranchSafe branch_box_1853 := by
  left; refine ⟨branch_box_1853_nonnegative, ?_⟩
  intro z hz; exact leaf_1853_sound hz

theorem leaf_1856_ok : checkAt 527 1000 box_1856 cert_1856 = true := by
  have h := List.all_eq_true.mp batch_37_02_ok accepted_1856 (by simp [batch_37_02_values])
  exact h
theorem leaf_1856_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1856.profileLo box_1856.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1856_ok
theorem branch_box_1856_nonnegative : ∀ j, 0 ≤ branch_box_1856.lower j ∧ 0 ≤ branch_box_1856.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1856, Box.profileLo, Box.profileHi, box_1856]
theorem leaf_1856_BranchSafe : CertificateConsequences.BranchSafe branch_box_1856 := by
  left; refine ⟨branch_box_1856_nonnegative, ?_⟩
  intro z hz; exact leaf_1856_sound hz

theorem leaf_1858_ok : checkAt 527 1000 box_1858 cert_1858 = true := by
  have h := List.all_eq_true.mp batch_37_03_ok accepted_1858 (by simp [batch_37_03_values])
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

theorem leaf_1864_ok : checkAt 527 1000 box_1864 cert_1864 = true := by
  have h := List.all_eq_true.mp batch_37_04_ok accepted_1864 (by simp [batch_37_04_values])
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

theorem leaf_1865_ok : checkAt 527 1000 box_1865 cert_1865 = true := by
  have h := List.all_eq_true.mp batch_37_05_ok accepted_1865 (by simp [batch_37_05_values])
  exact h
theorem leaf_1865_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1865.profileLo box_1865.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1865_ok
theorem branch_box_1865_nonnegative : ∀ j, 0 ≤ branch_box_1865.lower j ∧ 0 ≤ branch_box_1865.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1865, Box.profileLo, Box.profileHi, box_1865]
theorem leaf_1865_BranchSafe : CertificateConsequences.BranchSafe branch_box_1865 := by
  left; refine ⟨branch_box_1865_nonnegative, ?_⟩
  intro z hz; exact leaf_1865_sound hz

theorem leaf_1867_ok : checkAt 527 1000 box_1867 cert_1867 = true := by
  have h := List.all_eq_true.mp batch_37_06_ok accepted_1867 (by simp [batch_37_06_values])
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

theorem leaf_1869_ok : checkAt 527 1000 box_1869 cert_1869 = true := by
  have h := List.all_eq_true.mp batch_37_07_ok accepted_1869 (by simp [batch_37_07_values])
  exact h
theorem leaf_1869_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1869.profileLo box_1869.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1869_ok
theorem branch_box_1869_nonnegative : ∀ j, 0 ≤ branch_box_1869.lower j ∧ 0 ≤ branch_box_1869.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1869, Box.profileLo, Box.profileHi, box_1869]
theorem leaf_1869_BranchSafe : CertificateConsequences.BranchSafe branch_box_1869 := by
  left; refine ⟨branch_box_1869_nonnegative, ?_⟩
  intro z hz; exact leaf_1869_sound hz

theorem leaf_1874_ok : checkAt 527 1000 box_1874 cert_1874 = true := by
  have h := List.all_eq_true.mp batch_37_08_ok accepted_1874 (by simp [batch_37_08_values])
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

theorem leaf_1875_ok : checkAt 527 1000 box_1875 cert_1875 = true := by
  have h := List.all_eq_true.mp batch_37_09_ok accepted_1875 (by simp [batch_37_09_values])
  exact h
theorem leaf_1875_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1875.profileLo box_1875.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1875_ok
theorem branch_box_1875_nonnegative : ∀ j, 0 ≤ branch_box_1875.lower j ∧ 0 ≤ branch_box_1875.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1875, Box.profileLo, Box.profileHi, box_1875]
theorem leaf_1875_BranchSafe : CertificateConsequences.BranchSafe branch_box_1875 := by
  left; refine ⟨branch_box_1875_nonnegative, ?_⟩
  intro z hz; exact leaf_1875_sound hz

theorem leaf_1877_ok : checkAt 527 1000 box_1877 cert_1877 = true := by
  have h := List.all_eq_true.mp batch_37_10_ok accepted_1877 (by simp [batch_37_10_values])
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

theorem leaf_1879_ok : checkAt 527 1000 box_1879 cert_1879 = true := by
  have h := List.all_eq_true.mp batch_37_11_ok accepted_1879 (by simp [batch_37_11_values])
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

theorem leaf_1882_ok : checkAt 527 1000 box_1882 cert_1882 = true := by
  have h := List.all_eq_true.mp batch_37_12_ok accepted_1882 (by simp [batch_37_12_values])
  exact h
theorem leaf_1882_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1882.profileLo box_1882.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1882_ok
theorem branch_box_1882_nonnegative : ∀ j, 0 ≤ branch_box_1882.lower j ∧ 0 ≤ branch_box_1882.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1882, Box.profileLo, Box.profileHi, box_1882]
theorem leaf_1882_BranchSafe : CertificateConsequences.BranchSafe branch_box_1882 := by
  left; refine ⟨branch_box_1882_nonnegative, ?_⟩
  intro z hz; exact leaf_1882_sound hz

theorem leaf_1883_ok : checkAt 527 1000 box_1883 cert_1883 = true := by
  have h := List.all_eq_true.mp batch_37_13_ok accepted_1883 (by simp [batch_37_13_values])
  exact h
theorem leaf_1883_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1883.profileLo box_1883.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1883_ok
theorem branch_box_1883_nonnegative : ∀ j, 0 ≤ branch_box_1883.lower j ∧ 0 ≤ branch_box_1883.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1883, Box.profileLo, Box.profileHi, box_1883]
theorem leaf_1883_BranchSafe : CertificateConsequences.BranchSafe branch_box_1883 := by
  left; refine ⟨branch_box_1883_nonnegative, ?_⟩
  intro z hz; exact leaf_1883_sound hz

theorem leaf_1885_ok : checkAt 527 1000 box_1885 cert_1885 = true := by
  have h := List.all_eq_true.mp batch_37_14_ok accepted_1885 (by simp [batch_37_14_values])
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

theorem leaf_1887_ok : checkAt 527 1000 box_1887 cert_1887 = true := by
  have h := List.all_eq_true.mp batch_37_15_ok accepted_1887 (by simp [batch_37_15_values])
  exact h
theorem leaf_1887_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1887.profileLo box_1887.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1887_ok
theorem branch_box_1887_nonnegative : ∀ j, 0 ≤ branch_box_1887.lower j ∧ 0 ≤ branch_box_1887.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1887, Box.profileLo, Box.profileHi, box_1887]
theorem leaf_1887_BranchSafe : CertificateConsequences.BranchSafe branch_box_1887 := by
  left; refine ⟨branch_box_1887_nonnegative, ?_⟩
  intro z hz; exact leaf_1887_sound hz

theorem leaf_1894_ok : checkAt 527 1000 box_1894 cert_1894 = true := by
  have h := List.all_eq_true.mp batch_37_16_ok accepted_1894 (by simp [batch_37_16_values])
  exact h
theorem leaf_1894_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1894.profileLo box_1894.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1894_ok
theorem branch_box_1894_nonnegative : ∀ j, 0 ≤ branch_box_1894.lower j ∧ 0 ≤ branch_box_1894.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1894, Box.profileLo, Box.profileHi, box_1894]
theorem leaf_1894_BranchSafe : CertificateConsequences.BranchSafe branch_box_1894 := by
  left; refine ⟨branch_box_1894_nonnegative, ?_⟩
  intro z hz; exact leaf_1894_sound hz

theorem leaf_1896_ok : checkAt 527 1000 box_1896 cert_1896 = true := by
  have h := List.all_eq_true.mp batch_37_17_ok accepted_1896 (by simp [batch_37_17_values])
  exact h
theorem leaf_1896_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1896.profileLo box_1896.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1896_ok
theorem branch_box_1896_nonnegative : ∀ j, 0 ≤ branch_box_1896.lower j ∧ 0 ≤ branch_box_1896.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1896, Box.profileLo, Box.profileHi, box_1896]
theorem leaf_1896_BranchSafe : CertificateConsequences.BranchSafe branch_box_1896 := by
  left; refine ⟨branch_box_1896_nonnegative, ?_⟩
  intro z hz; exact leaf_1896_sound hz

theorem leaf_1898_ok : checkAt 527 1000 box_1898 cert_1898 = true := by
  have h := List.all_eq_true.mp batch_37_18_ok accepted_1898 (by simp [batch_37_18_values])
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

#print axioms batch_37_00_ok
#print axioms leaf_1851_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
