import PeaceableQueens.UpperBound.Generated.Even.C527Scaled38Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_38_00_values : List Bool := [accepted_1900]
theorem batch_38_00_ok : batch_38_00_values.all id = true := by decide

def batch_38_01_values : List Bool := [accepted_1903]
theorem batch_38_01_ok : batch_38_01_values.all id = true := by decide

def batch_38_02_values : List Bool := [accepted_1905]
theorem batch_38_02_ok : batch_38_02_values.all id = true := by decide

def batch_38_03_values : List Bool := [accepted_1906]
theorem batch_38_03_ok : batch_38_03_values.all id = true := by decide

def batch_38_04_values : List Bool := [accepted_1909]
theorem batch_38_04_ok : batch_38_04_values.all id = true := by decide

def batch_38_05_values : List Bool := [accepted_1910]
theorem batch_38_05_ok : batch_38_05_values.all id = true := by decide

def batch_38_06_values : List Bool := [accepted_1914]
theorem batch_38_06_ok : batch_38_06_values.all id = true := by decide

def batch_38_07_values : List Bool := [accepted_1915]
theorem batch_38_07_ok : batch_38_07_values.all id = true := by decide

def batch_38_08_values : List Bool := [accepted_1916]
theorem batch_38_08_ok : batch_38_08_values.all id = true := by decide

def batch_38_09_values : List Bool := [accepted_1918]
theorem batch_38_09_ok : batch_38_09_values.all id = true := by decide

def batch_38_10_values : List Bool := [accepted_1919]
theorem batch_38_10_ok : batch_38_10_values.all id = true := by decide

def batch_38_11_values : List Bool := [accepted_1920]
theorem batch_38_11_ok : batch_38_11_values.all id = true := by decide

def batch_38_12_values : List Bool := [accepted_1935]
theorem batch_38_12_ok : batch_38_12_values.all id = true := by decide

def batch_38_13_values : List Bool := [accepted_1936]
theorem batch_38_13_ok : batch_38_13_values.all id = true := by decide

def batch_38_14_values : List Bool := [accepted_1937]
theorem batch_38_14_ok : batch_38_14_values.all id = true := by decide

def batch_38_15_values : List Bool := [accepted_1938]
theorem batch_38_15_ok : batch_38_15_values.all id = true := by decide

def batch_38_16_values : List Bool := [accepted_1941]
theorem batch_38_16_ok : batch_38_16_values.all id = true := by decide

def batch_38_17_values : List Bool := [accepted_1942]
theorem batch_38_17_ok : batch_38_17_values.all id = true := by decide

def batch_38_18_values : List Bool := [accepted_1943]
theorem batch_38_18_ok : batch_38_18_values.all id = true := by decide

def batch_38_19_values : List Bool := [accepted_1945]
theorem batch_38_19_ok : batch_38_19_values.all id = true := by decide

def batch_38_20_values : List Bool := [accepted_1946]
theorem batch_38_20_ok : batch_38_20_values.all id = true := by decide

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

theorem leaf_1903_ok : checkAt 527 1000 box_1903 cert_1903 = true := by
  have h := List.all_eq_true.mp batch_38_01_ok accepted_1903 (by simp [batch_38_01_values])
  exact h
theorem leaf_1903_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1903.profileLo box_1903.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1903_ok
theorem branch_box_1903_nonnegative : ∀ j, 0 ≤ branch_box_1903.lower j ∧ 0 ≤ branch_box_1903.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1903, Box.profileLo, Box.profileHi, box_1903]
theorem leaf_1903_BranchSafe : CertificateConsequences.BranchSafe branch_box_1903 := by
  left; refine ⟨branch_box_1903_nonnegative, ?_⟩
  intro z hz; exact leaf_1903_sound hz

theorem leaf_1905_ok : checkAt 527 1000 box_1905 cert_1905 = true := by
  have h := List.all_eq_true.mp batch_38_02_ok accepted_1905 (by simp [batch_38_02_values])
  exact h
theorem leaf_1905_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1905.profileLo box_1905.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1905_ok
theorem branch_box_1905_nonnegative : ∀ j, 0 ≤ branch_box_1905.lower j ∧ 0 ≤ branch_box_1905.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1905, Box.profileLo, Box.profileHi, box_1905]
theorem leaf_1905_BranchSafe : CertificateConsequences.BranchSafe branch_box_1905 := by
  left; refine ⟨branch_box_1905_nonnegative, ?_⟩
  intro z hz; exact leaf_1905_sound hz

theorem leaf_1906_ok : checkAt 527 1000 box_1906 cert_1906 = true := by
  have h := List.all_eq_true.mp batch_38_03_ok accepted_1906 (by simp [batch_38_03_values])
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

theorem leaf_1909_ok : checkAt 527 1000 box_1909 cert_1909 = true := by
  have h := List.all_eq_true.mp batch_38_04_ok accepted_1909 (by simp [batch_38_04_values])
  exact h
theorem leaf_1909_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1909.profileLo box_1909.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1909_ok
theorem branch_box_1909_nonnegative : ∀ j, 0 ≤ branch_box_1909.lower j ∧ 0 ≤ branch_box_1909.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1909, Box.profileLo, Box.profileHi, box_1909]
theorem leaf_1909_BranchSafe : CertificateConsequences.BranchSafe branch_box_1909 := by
  left; refine ⟨branch_box_1909_nonnegative, ?_⟩
  intro z hz; exact leaf_1909_sound hz

theorem leaf_1910_ok : checkAt 527 1000 box_1910 cert_1910 = true := by
  have h := List.all_eq_true.mp batch_38_05_ok accepted_1910 (by simp [batch_38_05_values])
  exact h
theorem leaf_1910_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1910.profileLo box_1910.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1910_ok
theorem branch_box_1910_nonnegative : ∀ j, 0 ≤ branch_box_1910.lower j ∧ 0 ≤ branch_box_1910.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1910, Box.profileLo, Box.profileHi, box_1910]
theorem leaf_1910_BranchSafe : CertificateConsequences.BranchSafe branch_box_1910 := by
  left; refine ⟨branch_box_1910_nonnegative, ?_⟩
  intro z hz; exact leaf_1910_sound hz

theorem leaf_1914_ok : checkAt 527 1000 box_1914 cert_1914 = true := by
  have h := List.all_eq_true.mp batch_38_06_ok accepted_1914 (by simp [batch_38_06_values])
  exact h
theorem leaf_1914_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1914.profileLo box_1914.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1914_ok
theorem branch_box_1914_nonnegative : ∀ j, 0 ≤ branch_box_1914.lower j ∧ 0 ≤ branch_box_1914.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1914, Box.profileLo, Box.profileHi, box_1914]
theorem leaf_1914_BranchSafe : CertificateConsequences.BranchSafe branch_box_1914 := by
  left; refine ⟨branch_box_1914_nonnegative, ?_⟩
  intro z hz; exact leaf_1914_sound hz

theorem leaf_1915_ok : checkAt 527 1000 box_1915 cert_1915 = true := by
  have h := List.all_eq_true.mp batch_38_07_ok accepted_1915 (by simp [batch_38_07_values])
  exact h
theorem leaf_1915_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1915.profileLo box_1915.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1915_ok
theorem branch_box_1915_nonnegative : ∀ j, 0 ≤ branch_box_1915.lower j ∧ 0 ≤ branch_box_1915.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1915, Box.profileLo, Box.profileHi, box_1915]
theorem leaf_1915_BranchSafe : CertificateConsequences.BranchSafe branch_box_1915 := by
  left; refine ⟨branch_box_1915_nonnegative, ?_⟩
  intro z hz; exact leaf_1915_sound hz

theorem leaf_1916_ok : checkAt 527 1000 box_1916 cert_1916 = true := by
  have h := List.all_eq_true.mp batch_38_08_ok accepted_1916 (by simp [batch_38_08_values])
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

theorem leaf_1918_ok : checkAt 527 1000 box_1918 cert_1918 = true := by
  have h := List.all_eq_true.mp batch_38_09_ok accepted_1918 (by simp [batch_38_09_values])
  exact h
theorem leaf_1918_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1918.profileLo box_1918.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1918_ok
theorem branch_box_1918_nonnegative : ∀ j, 0 ≤ branch_box_1918.lower j ∧ 0 ≤ branch_box_1918.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1918, Box.profileLo, Box.profileHi, box_1918]
theorem leaf_1918_BranchSafe : CertificateConsequences.BranchSafe branch_box_1918 := by
  left; refine ⟨branch_box_1918_nonnegative, ?_⟩
  intro z hz; exact leaf_1918_sound hz

theorem leaf_1919_ok : checkAt 527 1000 box_1919 cert_1919 = true := by
  have h := List.all_eq_true.mp batch_38_10_ok accepted_1919 (by simp [batch_38_10_values])
  exact h
theorem leaf_1919_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1919.profileLo box_1919.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1919_ok
theorem branch_box_1919_nonnegative : ∀ j, 0 ≤ branch_box_1919.lower j ∧ 0 ≤ branch_box_1919.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1919, Box.profileLo, Box.profileHi, box_1919]
theorem leaf_1919_BranchSafe : CertificateConsequences.BranchSafe branch_box_1919 := by
  left; refine ⟨branch_box_1919_nonnegative, ?_⟩
  intro z hz; exact leaf_1919_sound hz

theorem leaf_1920_ok : checkAt 527 1000 box_1920 cert_1920 = true := by
  have h := List.all_eq_true.mp batch_38_11_ok accepted_1920 (by simp [batch_38_11_values])
  exact h
theorem leaf_1920_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1920.profileLo box_1920.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1920_ok
theorem branch_box_1920_nonnegative : ∀ j, 0 ≤ branch_box_1920.lower j ∧ 0 ≤ branch_box_1920.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1920, Box.profileLo, Box.profileHi, box_1920]
theorem leaf_1920_BranchSafe : CertificateConsequences.BranchSafe branch_box_1920 := by
  left; refine ⟨branch_box_1920_nonnegative, ?_⟩
  intro z hz; exact leaf_1920_sound hz

theorem leaf_1935_ok : checkAt 527 1000 box_1935 cert_1935 = true := by
  have h := List.all_eq_true.mp batch_38_12_ok accepted_1935 (by simp [batch_38_12_values])
  exact h
theorem leaf_1935_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1935.profileLo box_1935.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1935_ok
theorem branch_box_1935_nonnegative : ∀ j, 0 ≤ branch_box_1935.lower j ∧ 0 ≤ branch_box_1935.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1935, Box.profileLo, Box.profileHi, box_1935]
theorem leaf_1935_BranchSafe : CertificateConsequences.BranchSafe branch_box_1935 := by
  left; refine ⟨branch_box_1935_nonnegative, ?_⟩
  intro z hz; exact leaf_1935_sound hz

theorem leaf_1936_ok : checkAt 527 1000 box_1936 cert_1936 = true := by
  have h := List.all_eq_true.mp batch_38_13_ok accepted_1936 (by simp [batch_38_13_values])
  exact h
theorem leaf_1936_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1936.profileLo box_1936.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1936_ok
theorem branch_box_1936_nonnegative : ∀ j, 0 ≤ branch_box_1936.lower j ∧ 0 ≤ branch_box_1936.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1936, Box.profileLo, Box.profileHi, box_1936]
theorem leaf_1936_BranchSafe : CertificateConsequences.BranchSafe branch_box_1936 := by
  left; refine ⟨branch_box_1936_nonnegative, ?_⟩
  intro z hz; exact leaf_1936_sound hz

theorem leaf_1937_ok : checkAt 527 1000 box_1937 cert_1937 = true := by
  have h := List.all_eq_true.mp batch_38_14_ok accepted_1937 (by simp [batch_38_14_values])
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

theorem leaf_1938_ok : checkAt 527 1000 box_1938 cert_1938 = true := by
  have h := List.all_eq_true.mp batch_38_15_ok accepted_1938 (by simp [batch_38_15_values])
  exact h
theorem leaf_1938_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1938.profileLo box_1938.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1938_ok
theorem branch_box_1938_nonnegative : ∀ j, 0 ≤ branch_box_1938.lower j ∧ 0 ≤ branch_box_1938.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1938, Box.profileLo, Box.profileHi, box_1938]
theorem leaf_1938_BranchSafe : CertificateConsequences.BranchSafe branch_box_1938 := by
  left; refine ⟨branch_box_1938_nonnegative, ?_⟩
  intro z hz; exact leaf_1938_sound hz

theorem leaf_1941_ok : checkAt 527 1000 box_1941 cert_1941 = true := by
  have h := List.all_eq_true.mp batch_38_16_ok accepted_1941 (by simp [batch_38_16_values])
  exact h
theorem leaf_1941_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1941.profileLo box_1941.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1941_ok
theorem branch_box_1941_nonnegative : ∀ j, 0 ≤ branch_box_1941.lower j ∧ 0 ≤ branch_box_1941.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1941, Box.profileLo, Box.profileHi, box_1941]
theorem leaf_1941_BranchSafe : CertificateConsequences.BranchSafe branch_box_1941 := by
  left; refine ⟨branch_box_1941_nonnegative, ?_⟩
  intro z hz; exact leaf_1941_sound hz

theorem leaf_1942_ok : checkAt 527 1000 box_1942 cert_1942 = true := by
  have h := List.all_eq_true.mp batch_38_17_ok accepted_1942 (by simp [batch_38_17_values])
  exact h
theorem leaf_1942_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1942.profileLo box_1942.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1942_ok
theorem branch_box_1942_nonnegative : ∀ j, 0 ≤ branch_box_1942.lower j ∧ 0 ≤ branch_box_1942.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1942, Box.profileLo, Box.profileHi, box_1942]
theorem leaf_1942_BranchSafe : CertificateConsequences.BranchSafe branch_box_1942 := by
  left; refine ⟨branch_box_1942_nonnegative, ?_⟩
  intro z hz; exact leaf_1942_sound hz

theorem leaf_1943_ok : checkAt 527 1000 box_1943 cert_1943 = true := by
  have h := List.all_eq_true.mp batch_38_18_ok accepted_1943 (by simp [batch_38_18_values])
  exact h
theorem leaf_1943_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1943.profileLo box_1943.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1943_ok
theorem branch_box_1943_nonnegative : ∀ j, 0 ≤ branch_box_1943.lower j ∧ 0 ≤ branch_box_1943.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1943, Box.profileLo, Box.profileHi, box_1943]
theorem leaf_1943_BranchSafe : CertificateConsequences.BranchSafe branch_box_1943 := by
  left; refine ⟨branch_box_1943_nonnegative, ?_⟩
  intro z hz; exact leaf_1943_sound hz

theorem leaf_1945_ok : checkAt 527 1000 box_1945 cert_1945 = true := by
  have h := List.all_eq_true.mp batch_38_19_ok accepted_1945 (by simp [batch_38_19_values])
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

theorem leaf_1946_ok : checkAt 527 1000 box_1946 cert_1946 = true := by
  have h := List.all_eq_true.mp batch_38_20_ok accepted_1946 (by simp [batch_38_20_values])
  exact h
theorem leaf_1946_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1946.profileLo box_1946.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1946_ok
theorem branch_box_1946_nonnegative : ∀ j, 0 ≤ branch_box_1946.lower j ∧ 0 ≤ branch_box_1946.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1946, Box.profileLo, Box.profileHi, box_1946]
theorem leaf_1946_BranchSafe : CertificateConsequences.BranchSafe branch_box_1946 := by
  left; refine ⟨branch_box_1946_nonnegative, ?_⟩
  intro z hz; exact leaf_1946_sound hz

#print axioms batch_38_00_ok
#print axioms leaf_1900_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
