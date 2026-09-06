import PeaceableQueens.UpperBound.Generated.Even.CoreScaled38Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_38_00_values : List Bool := [accepted_1900]
theorem batch_38_00_ok : batch_38_00_values.all id = true := by decide

def batch_38_01_values : List Bool := [accepted_1902]
theorem batch_38_01_ok : batch_38_01_values.all id = true := by decide

def batch_38_02_values : List Bool := [accepted_1906]
theorem batch_38_02_ok : batch_38_02_values.all id = true := by decide

def batch_38_03_values : List Bool := [accepted_1907]
theorem batch_38_03_ok : batch_38_03_values.all id = true := by decide

def batch_38_04_values : List Bool := [accepted_1912]
theorem batch_38_04_ok : batch_38_04_values.all id = true := by decide

def batch_38_05_values : List Bool := [accepted_1913]
theorem batch_38_05_ok : batch_38_05_values.all id = true := by decide

def batch_38_06_values : List Bool := [accepted_1916]
theorem batch_38_06_ok : batch_38_06_values.all id = true := by decide

def batch_38_07_values : List Bool := [accepted_1917]
theorem batch_38_07_ok : batch_38_07_values.all id = true := by decide

def batch_38_08_values : List Bool := [accepted_1922]
theorem batch_38_08_ok : batch_38_08_values.all id = true := by decide

def batch_38_09_values : List Bool := [accepted_1924]
theorem batch_38_09_ok : batch_38_09_values.all id = true := by decide

def batch_38_10_values : List Bool := [accepted_1926]
theorem batch_38_10_ok : batch_38_10_values.all id = true := by decide

def batch_38_11_values : List Bool := [accepted_1928]
theorem batch_38_11_ok : batch_38_11_values.all id = true := by decide

def batch_38_12_values : List Bool := [accepted_1932]
theorem batch_38_12_ok : batch_38_12_values.all id = true := by decide

def batch_38_13_values : List Bool := [accepted_1937]
theorem batch_38_13_ok : batch_38_13_values.all id = true := by decide

def batch_38_14_values : List Bool := [accepted_1944]
theorem batch_38_14_ok : batch_38_14_values.all id = true := by decide

def batch_38_15_values : List Bool := [accepted_1945]
theorem batch_38_15_ok : batch_38_15_values.all id = true := by decide

def batch_38_16_values : List Bool := [accepted_1947]
theorem batch_38_16_ok : batch_38_16_values.all id = true := by decide

def batch_38_17_values : List Bool := [accepted_1949]
theorem batch_38_17_ok : batch_38_17_values.all id = true := by decide

theorem leaf_1900_ok : checkAt 527 1000 box_1900 cert_1900 = true := by
  have h := List.all_eq_true.mp batch_38_00_ok accepted_1900 (by simp [batch_38_00_values])
  exact h
theorem leaf_1900_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1900.profileLo box_1900.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1900_ok
theorem branch_box_1900_nonnegative : ∀ j, 0 ≤ branch_box_1900.lower j ∧ 0 ≤ branch_box_1900.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1900, Box.profileLo, Box.profileHi, box_1900]
theorem leaf_1900_BranchSafe : CertificateConsequences.BranchSafe branch_box_1900 := by
  left; refine ⟨branch_box_1900_nonnegative, ?_⟩
  intro z hz; exact leaf_1900_sound hz

theorem leaf_1902_ok : checkAt 527 1000 box_1902 cert_1902 = true := by
  have h := List.all_eq_true.mp batch_38_01_ok accepted_1902 (by simp [batch_38_01_values])
  exact h
theorem leaf_1902_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1902.profileLo box_1902.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1902_ok
theorem branch_box_1902_nonnegative : ∀ j, 0 ≤ branch_box_1902.lower j ∧ 0 ≤ branch_box_1902.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1902, Box.profileLo, Box.profileHi, box_1902]
theorem leaf_1902_BranchSafe : CertificateConsequences.BranchSafe branch_box_1902 := by
  left; refine ⟨branch_box_1902_nonnegative, ?_⟩
  intro z hz; exact leaf_1902_sound hz

theorem leaf_1906_ok : checkAt 527 1000 box_1906 cert_1906 = true := by
  have h := List.all_eq_true.mp batch_38_02_ok accepted_1906 (by simp [batch_38_02_values])
  exact h
theorem leaf_1906_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1906.profileLo box_1906.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1906_ok
theorem branch_box_1906_nonnegative : ∀ j, 0 ≤ branch_box_1906.lower j ∧ 0 ≤ branch_box_1906.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1906, Box.profileLo, Box.profileHi, box_1906]
theorem leaf_1906_BranchSafe : CertificateConsequences.BranchSafe branch_box_1906 := by
  left; refine ⟨branch_box_1906_nonnegative, ?_⟩
  intro z hz; exact leaf_1906_sound hz

theorem leaf_1907_ok : checkAt 527 1000 box_1907 cert_1907 = true := by
  have h := List.all_eq_true.mp batch_38_03_ok accepted_1907 (by simp [batch_38_03_values])
  exact h
theorem leaf_1907_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1907.profileLo box_1907.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1907_ok
theorem branch_box_1907_nonnegative : ∀ j, 0 ≤ branch_box_1907.lower j ∧ 0 ≤ branch_box_1907.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1907, Box.profileLo, Box.profileHi, box_1907]
theorem leaf_1907_BranchSafe : CertificateConsequences.BranchSafe branch_box_1907 := by
  left; refine ⟨branch_box_1907_nonnegative, ?_⟩
  intro z hz; exact leaf_1907_sound hz

theorem leaf_1912_ok : checkAt 527 1000 box_1912 cert_1912 = true := by
  have h := List.all_eq_true.mp batch_38_04_ok accepted_1912 (by simp [batch_38_04_values])
  exact h
theorem leaf_1912_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1912.profileLo box_1912.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1912_ok
theorem branch_box_1912_nonnegative : ∀ j, 0 ≤ branch_box_1912.lower j ∧ 0 ≤ branch_box_1912.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1912, Box.profileLo, Box.profileHi, box_1912]
theorem leaf_1912_BranchSafe : CertificateConsequences.BranchSafe branch_box_1912 := by
  left; refine ⟨branch_box_1912_nonnegative, ?_⟩
  intro z hz; exact leaf_1912_sound hz

theorem leaf_1913_ok : checkAt 527 1000 box_1913 cert_1913 = true := by
  have h := List.all_eq_true.mp batch_38_05_ok accepted_1913 (by simp [batch_38_05_values])
  exact h
theorem leaf_1913_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1913.profileLo box_1913.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1913_ok
theorem branch_box_1913_nonnegative : ∀ j, 0 ≤ branch_box_1913.lower j ∧ 0 ≤ branch_box_1913.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1913, Box.profileLo, Box.profileHi, box_1913]
theorem leaf_1913_BranchSafe : CertificateConsequences.BranchSafe branch_box_1913 := by
  left; refine ⟨branch_box_1913_nonnegative, ?_⟩
  intro z hz; exact leaf_1913_sound hz

theorem leaf_1916_ok : checkAt 527 1000 box_1916 cert_1916 = true := by
  have h := List.all_eq_true.mp batch_38_06_ok accepted_1916 (by simp [batch_38_06_values])
  exact h
theorem leaf_1916_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1916.profileLo box_1916.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1916_ok
theorem branch_box_1916_nonnegative : ∀ j, 0 ≤ branch_box_1916.lower j ∧ 0 ≤ branch_box_1916.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1916, Box.profileLo, Box.profileHi, box_1916]
theorem leaf_1916_BranchSafe : CertificateConsequences.BranchSafe branch_box_1916 := by
  left; refine ⟨branch_box_1916_nonnegative, ?_⟩
  intro z hz; exact leaf_1916_sound hz

theorem leaf_1917_ok : checkAt 527 1000 box_1917 cert_1917 = true := by
  have h := List.all_eq_true.mp batch_38_07_ok accepted_1917 (by simp [batch_38_07_values])
  exact h
theorem leaf_1917_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1917.profileLo box_1917.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1917_ok
theorem branch_box_1917_nonnegative : ∀ j, 0 ≤ branch_box_1917.lower j ∧ 0 ≤ branch_box_1917.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1917, Box.profileLo, Box.profileHi, box_1917]
theorem leaf_1917_BranchSafe : CertificateConsequences.BranchSafe branch_box_1917 := by
  left; refine ⟨branch_box_1917_nonnegative, ?_⟩
  intro z hz; exact leaf_1917_sound hz

theorem leaf_1922_ok : checkAt 527 1000 box_1922 cert_1922 = true := by
  have h := List.all_eq_true.mp batch_38_08_ok accepted_1922 (by simp [batch_38_08_values])
  exact h
theorem leaf_1922_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1922.profileLo box_1922.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1922_ok
theorem branch_box_1922_nonnegative : ∀ j, 0 ≤ branch_box_1922.lower j ∧ 0 ≤ branch_box_1922.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1922, Box.profileLo, Box.profileHi, box_1922]
theorem leaf_1922_BranchSafe : CertificateConsequences.BranchSafe branch_box_1922 := by
  left; refine ⟨branch_box_1922_nonnegative, ?_⟩
  intro z hz; exact leaf_1922_sound hz

theorem leaf_1924_ok : checkAt 527 1000 box_1924 cert_1924 = true := by
  have h := List.all_eq_true.mp batch_38_09_ok accepted_1924 (by simp [batch_38_09_values])
  exact h
theorem leaf_1924_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1924.profileLo box_1924.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1924_ok
theorem branch_box_1924_nonnegative : ∀ j, 0 ≤ branch_box_1924.lower j ∧ 0 ≤ branch_box_1924.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1924, Box.profileLo, Box.profileHi, box_1924]
theorem leaf_1924_BranchSafe : CertificateConsequences.BranchSafe branch_box_1924 := by
  left; refine ⟨branch_box_1924_nonnegative, ?_⟩
  intro z hz; exact leaf_1924_sound hz

theorem leaf_1926_ok : checkAt 527 1000 box_1926 cert_1926 = true := by
  have h := List.all_eq_true.mp batch_38_10_ok accepted_1926 (by simp [batch_38_10_values])
  exact h
theorem leaf_1926_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1926.profileLo box_1926.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1926_ok
theorem branch_box_1926_nonnegative : ∀ j, 0 ≤ branch_box_1926.lower j ∧ 0 ≤ branch_box_1926.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1926, Box.profileLo, Box.profileHi, box_1926]
theorem leaf_1926_BranchSafe : CertificateConsequences.BranchSafe branch_box_1926 := by
  left; refine ⟨branch_box_1926_nonnegative, ?_⟩
  intro z hz; exact leaf_1926_sound hz

theorem leaf_1928_ok : checkAt 527 1000 box_1928 cert_1928 = true := by
  have h := List.all_eq_true.mp batch_38_11_ok accepted_1928 (by simp [batch_38_11_values])
  exact h
theorem leaf_1928_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1928.profileLo box_1928.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1928_ok
theorem branch_box_1928_nonnegative : ∀ j, 0 ≤ branch_box_1928.lower j ∧ 0 ≤ branch_box_1928.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1928, Box.profileLo, Box.profileHi, box_1928]
theorem leaf_1928_BranchSafe : CertificateConsequences.BranchSafe branch_box_1928 := by
  left; refine ⟨branch_box_1928_nonnegative, ?_⟩
  intro z hz; exact leaf_1928_sound hz

theorem leaf_1932_ok : checkAt 527 1000 box_1932 cert_1932 = true := by
  have h := List.all_eq_true.mp batch_38_12_ok accepted_1932 (by simp [batch_38_12_values])
  exact h
theorem leaf_1932_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1932.profileLo box_1932.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1932_ok
theorem branch_box_1932_nonnegative : ∀ j, 0 ≤ branch_box_1932.lower j ∧ 0 ≤ branch_box_1932.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1932, Box.profileLo, Box.profileHi, box_1932]
theorem leaf_1932_BranchSafe : CertificateConsequences.BranchSafe branch_box_1932 := by
  left; refine ⟨branch_box_1932_nonnegative, ?_⟩
  intro z hz; exact leaf_1932_sound hz

theorem leaf_1937_ok : checkAt 527 1000 box_1937 cert_1937 = true := by
  have h := List.all_eq_true.mp batch_38_13_ok accepted_1937 (by simp [batch_38_13_values])
  exact h
theorem leaf_1937_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1937.profileLo box_1937.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1937_ok
theorem branch_box_1937_nonnegative : ∀ j, 0 ≤ branch_box_1937.lower j ∧ 0 ≤ branch_box_1937.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1937, Box.profileLo, Box.profileHi, box_1937]
theorem leaf_1937_BranchSafe : CertificateConsequences.BranchSafe branch_box_1937 := by
  left; refine ⟨branch_box_1937_nonnegative, ?_⟩
  intro z hz; exact leaf_1937_sound hz

theorem leaf_1944_ok : checkAt 527 1000 box_1944 cert_1944 = true := by
  have h := List.all_eq_true.mp batch_38_14_ok accepted_1944 (by simp [batch_38_14_values])
  exact h
theorem leaf_1944_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1944.profileLo box_1944.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1944_ok
theorem branch_box_1944_nonnegative : ∀ j, 0 ≤ branch_box_1944.lower j ∧ 0 ≤ branch_box_1944.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1944, Box.profileLo, Box.profileHi, box_1944]
theorem leaf_1944_BranchSafe : CertificateConsequences.BranchSafe branch_box_1944 := by
  left; refine ⟨branch_box_1944_nonnegative, ?_⟩
  intro z hz; exact leaf_1944_sound hz

theorem leaf_1945_ok : checkAt 527 1000 box_1945 cert_1945 = true := by
  have h := List.all_eq_true.mp batch_38_15_ok accepted_1945 (by simp [batch_38_15_values])
  exact h
theorem leaf_1945_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1945.profileLo box_1945.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1945_ok
theorem branch_box_1945_nonnegative : ∀ j, 0 ≤ branch_box_1945.lower j ∧ 0 ≤ branch_box_1945.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1945, Box.profileLo, Box.profileHi, box_1945]
theorem leaf_1945_BranchSafe : CertificateConsequences.BranchSafe branch_box_1945 := by
  left; refine ⟨branch_box_1945_nonnegative, ?_⟩
  intro z hz; exact leaf_1945_sound hz

theorem leaf_1947_ok : checkAt 527 1000 box_1947 cert_1947 = true := by
  have h := List.all_eq_true.mp batch_38_16_ok accepted_1947 (by simp [batch_38_16_values])
  exact h
theorem leaf_1947_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1947.profileLo box_1947.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1947_ok
theorem branch_box_1947_nonnegative : ∀ j, 0 ≤ branch_box_1947.lower j ∧ 0 ≤ branch_box_1947.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1947, Box.profileLo, Box.profileHi, box_1947]
theorem leaf_1947_BranchSafe : CertificateConsequences.BranchSafe branch_box_1947 := by
  left; refine ⟨branch_box_1947_nonnegative, ?_⟩
  intro z hz; exact leaf_1947_sound hz

theorem leaf_1949_ok : checkAt 527 1000 box_1949 cert_1949 = true := by
  have h := List.all_eq_true.mp batch_38_17_ok accepted_1949 (by simp [batch_38_17_values])
  exact h
theorem leaf_1949_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1949.profileLo box_1949.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1949_ok
theorem branch_box_1949_nonnegative : ∀ j, 0 ≤ branch_box_1949.lower j ∧ 0 ≤ branch_box_1949.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1949, Box.profileLo, Box.profileHi, box_1949]
theorem leaf_1949_BranchSafe : CertificateConsequences.BranchSafe branch_box_1949 := by
  left; refine ⟨branch_box_1949_nonnegative, ?_⟩
  intro z hz; exact leaf_1949_sound hz

#print axioms batch_38_00_ok
#print axioms leaf_1900_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
