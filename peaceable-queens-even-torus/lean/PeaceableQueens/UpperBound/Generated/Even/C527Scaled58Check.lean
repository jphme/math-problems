import PeaceableQueens.UpperBound.Generated.Even.C527Scaled58Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_58_00_values : List Bool := [accepted_2902]
theorem batch_58_00_ok : batch_58_00_values.all id = true := by decide

def batch_58_01_values : List Bool := [accepted_2903]
theorem batch_58_01_ok : batch_58_01_values.all id = true := by decide

def batch_58_02_values : List Bool := [accepted_2904]
theorem batch_58_02_ok : batch_58_02_values.all id = true := by decide

def batch_58_03_values : List Bool := [accepted_2912]
theorem batch_58_03_ok : batch_58_03_values.all id = true := by decide

def batch_58_04_values : List Bool := [accepted_2913]
theorem batch_58_04_ok : batch_58_04_values.all id = true := by decide

def batch_58_05_values : List Bool := [accepted_2914]
theorem batch_58_05_ok : batch_58_05_values.all id = true := by decide

def batch_58_06_values : List Bool := [accepted_2915]
theorem batch_58_06_ok : batch_58_06_values.all id = true := by decide

def batch_58_07_values : List Bool := [accepted_2917]
theorem batch_58_07_ok : batch_58_07_values.all id = true := by decide

def batch_58_08_values : List Bool := [accepted_2918]
theorem batch_58_08_ok : batch_58_08_values.all id = true := by decide

def batch_58_09_values : List Bool := [accepted_2921]
theorem batch_58_09_ok : batch_58_09_values.all id = true := by decide

def batch_58_10_values : List Bool := [accepted_2922]
theorem batch_58_10_ok : batch_58_10_values.all id = true := by decide

def batch_58_11_values : List Bool := [accepted_2923]
theorem batch_58_11_ok : batch_58_11_values.all id = true := by decide

def batch_58_12_values : List Bool := [accepted_2925]
theorem batch_58_12_ok : batch_58_12_values.all id = true := by decide

def batch_58_13_values : List Bool := [accepted_2926]
theorem batch_58_13_ok : batch_58_13_values.all id = true := by decide

def batch_58_14_values : List Bool := [accepted_2927]
theorem batch_58_14_ok : batch_58_14_values.all id = true := by decide

def batch_58_15_values : List Bool := [accepted_2928]
theorem batch_58_15_ok : batch_58_15_values.all id = true := by decide

def batch_58_16_values : List Bool := [accepted_2931]
theorem batch_58_16_ok : batch_58_16_values.all id = true := by decide

def batch_58_17_values : List Bool := [accepted_2933]
theorem batch_58_17_ok : batch_58_17_values.all id = true := by decide

def batch_58_18_values : List Bool := [accepted_2934]
theorem batch_58_18_ok : batch_58_18_values.all id = true := by decide

def batch_58_19_values : List Bool := [accepted_2937]
theorem batch_58_19_ok : batch_58_19_values.all id = true := by decide

def batch_58_20_values : List Bool := [accepted_2938]
theorem batch_58_20_ok : batch_58_20_values.all id = true := by decide

def batch_58_21_values : List Bool := [accepted_2939]
theorem batch_58_21_ok : batch_58_21_values.all id = true := by decide

def batch_58_22_values : List Bool := [accepted_2941]
theorem batch_58_22_ok : batch_58_22_values.all id = true := by decide

def batch_58_23_values : List Bool := [accepted_2942]
theorem batch_58_23_ok : batch_58_23_values.all id = true := by decide

theorem leaf_2902_ok : checkAt 527 1000 box_2902 cert_2902 = true := by
  have h := List.all_eq_true.mp batch_58_00_ok accepted_2902 (by simp [batch_58_00_values])
  exact h
theorem leaf_2902_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2902.profileLo box_2902.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2902_ok
theorem branch_box_2902_nonnegative : ∀ j, 0 ≤ branch_box_2902.lower j ∧ 0 ≤ branch_box_2902.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2902, Box.profileLo, Box.profileHi, box_2902]
theorem leaf_2902_BranchSafe : CertificateConsequences.BranchSafe branch_box_2902 := by
  left; refine ⟨branch_box_2902_nonnegative, ?_⟩
  intro z hz; exact leaf_2902_sound hz

theorem leaf_2903_ok : checkAt 527 1000 box_2903 cert_2903 = true := by
  have h := List.all_eq_true.mp batch_58_01_ok accepted_2903 (by simp [batch_58_01_values])
  exact h
theorem leaf_2903_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2903.profileLo box_2903.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2903_ok
theorem branch_box_2903_nonnegative : ∀ j, 0 ≤ branch_box_2903.lower j ∧ 0 ≤ branch_box_2903.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2903, Box.profileLo, Box.profileHi, box_2903]
theorem leaf_2903_BranchSafe : CertificateConsequences.BranchSafe branch_box_2903 := by
  left; refine ⟨branch_box_2903_nonnegative, ?_⟩
  intro z hz; exact leaf_2903_sound hz

theorem leaf_2904_ok : checkAt 527 1000 box_2904 cert_2904 = true := by
  have h := List.all_eq_true.mp batch_58_02_ok accepted_2904 (by simp [batch_58_02_values])
  exact h
theorem leaf_2904_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2904.profileLo box_2904.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2904_ok
theorem branch_box_2904_nonnegative : ∀ j, 0 ≤ branch_box_2904.lower j ∧ 0 ≤ branch_box_2904.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2904, Box.profileLo, Box.profileHi, box_2904]
theorem leaf_2904_BranchSafe : CertificateConsequences.BranchSafe branch_box_2904 := by
  left; refine ⟨branch_box_2904_nonnegative, ?_⟩
  intro z hz; exact leaf_2904_sound hz

theorem leaf_2912_ok : checkAt 527 1000 box_2912 cert_2912 = true := by
  have h := List.all_eq_true.mp batch_58_03_ok accepted_2912 (by simp [batch_58_03_values])
  exact h
theorem leaf_2912_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2912.profileLo box_2912.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2912_ok
theorem branch_box_2912_nonnegative : ∀ j, 0 ≤ branch_box_2912.lower j ∧ 0 ≤ branch_box_2912.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2912, Box.profileLo, Box.profileHi, box_2912]
theorem leaf_2912_BranchSafe : CertificateConsequences.BranchSafe branch_box_2912 := by
  left; refine ⟨branch_box_2912_nonnegative, ?_⟩
  intro z hz; exact leaf_2912_sound hz

theorem leaf_2913_ok : checkAt 527 1000 box_2913 cert_2913 = true := by
  have h := List.all_eq_true.mp batch_58_04_ok accepted_2913 (by simp [batch_58_04_values])
  exact h
theorem leaf_2913_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2913.profileLo box_2913.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2913_ok
theorem branch_box_2913_nonnegative : ∀ j, 0 ≤ branch_box_2913.lower j ∧ 0 ≤ branch_box_2913.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2913, Box.profileLo, Box.profileHi, box_2913]
theorem leaf_2913_BranchSafe : CertificateConsequences.BranchSafe branch_box_2913 := by
  left; refine ⟨branch_box_2913_nonnegative, ?_⟩
  intro z hz; exact leaf_2913_sound hz

theorem leaf_2914_ok : checkAt 527 1000 box_2914 cert_2914 = true := by
  have h := List.all_eq_true.mp batch_58_05_ok accepted_2914 (by simp [batch_58_05_values])
  exact h
theorem leaf_2914_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2914.profileLo box_2914.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2914_ok
theorem branch_box_2914_nonnegative : ∀ j, 0 ≤ branch_box_2914.lower j ∧ 0 ≤ branch_box_2914.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2914, Box.profileLo, Box.profileHi, box_2914]
theorem leaf_2914_BranchSafe : CertificateConsequences.BranchSafe branch_box_2914 := by
  left; refine ⟨branch_box_2914_nonnegative, ?_⟩
  intro z hz; exact leaf_2914_sound hz

theorem leaf_2915_ok : checkAt 527 1000 box_2915 cert_2915 = true := by
  have h := List.all_eq_true.mp batch_58_06_ok accepted_2915 (by simp [batch_58_06_values])
  exact h
theorem leaf_2915_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2915.profileLo box_2915.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2915_ok
theorem branch_box_2915_nonnegative : ∀ j, 0 ≤ branch_box_2915.lower j ∧ 0 ≤ branch_box_2915.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2915, Box.profileLo, Box.profileHi, box_2915]
theorem leaf_2915_BranchSafe : CertificateConsequences.BranchSafe branch_box_2915 := by
  left; refine ⟨branch_box_2915_nonnegative, ?_⟩
  intro z hz; exact leaf_2915_sound hz

theorem leaf_2917_ok : checkAt 527 1000 box_2917 cert_2917 = true := by
  have h := List.all_eq_true.mp batch_58_07_ok accepted_2917 (by simp [batch_58_07_values])
  exact h
theorem leaf_2917_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2917.profileLo box_2917.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2917_ok
theorem branch_box_2917_nonnegative : ∀ j, 0 ≤ branch_box_2917.lower j ∧ 0 ≤ branch_box_2917.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2917, Box.profileLo, Box.profileHi, box_2917]
theorem leaf_2917_BranchSafe : CertificateConsequences.BranchSafe branch_box_2917 := by
  left; refine ⟨branch_box_2917_nonnegative, ?_⟩
  intro z hz; exact leaf_2917_sound hz

theorem leaf_2918_ok : checkAt 527 1000 box_2918 cert_2918 = true := by
  have h := List.all_eq_true.mp batch_58_08_ok accepted_2918 (by simp [batch_58_08_values])
  exact h
theorem leaf_2918_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2918.profileLo box_2918.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2918_ok
theorem branch_box_2918_nonnegative : ∀ j, 0 ≤ branch_box_2918.lower j ∧ 0 ≤ branch_box_2918.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2918, Box.profileLo, Box.profileHi, box_2918]
theorem leaf_2918_BranchSafe : CertificateConsequences.BranchSafe branch_box_2918 := by
  left; refine ⟨branch_box_2918_nonnegative, ?_⟩
  intro z hz; exact leaf_2918_sound hz

theorem leaf_2921_ok : checkAt 527 1000 box_2921 cert_2921 = true := by
  have h := List.all_eq_true.mp batch_58_09_ok accepted_2921 (by simp [batch_58_09_values])
  exact h
theorem leaf_2921_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2921.profileLo box_2921.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2921_ok
theorem branch_box_2921_nonnegative : ∀ j, 0 ≤ branch_box_2921.lower j ∧ 0 ≤ branch_box_2921.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2921, Box.profileLo, Box.profileHi, box_2921]
theorem leaf_2921_BranchSafe : CertificateConsequences.BranchSafe branch_box_2921 := by
  left; refine ⟨branch_box_2921_nonnegative, ?_⟩
  intro z hz; exact leaf_2921_sound hz

theorem leaf_2922_ok : checkAt 527 1000 box_2922 cert_2922 = true := by
  have h := List.all_eq_true.mp batch_58_10_ok accepted_2922 (by simp [batch_58_10_values])
  exact h
theorem leaf_2922_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2922.profileLo box_2922.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2922_ok
theorem branch_box_2922_nonnegative : ∀ j, 0 ≤ branch_box_2922.lower j ∧ 0 ≤ branch_box_2922.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2922, Box.profileLo, Box.profileHi, box_2922]
theorem leaf_2922_BranchSafe : CertificateConsequences.BranchSafe branch_box_2922 := by
  left; refine ⟨branch_box_2922_nonnegative, ?_⟩
  intro z hz; exact leaf_2922_sound hz

theorem leaf_2923_ok : checkAt 527 1000 box_2923 cert_2923 = true := by
  have h := List.all_eq_true.mp batch_58_11_ok accepted_2923 (by simp [batch_58_11_values])
  exact h
theorem leaf_2923_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2923.profileLo box_2923.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2923_ok
theorem branch_box_2923_nonnegative : ∀ j, 0 ≤ branch_box_2923.lower j ∧ 0 ≤ branch_box_2923.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2923, Box.profileLo, Box.profileHi, box_2923]
theorem leaf_2923_BranchSafe : CertificateConsequences.BranchSafe branch_box_2923 := by
  left; refine ⟨branch_box_2923_nonnegative, ?_⟩
  intro z hz; exact leaf_2923_sound hz

theorem leaf_2925_ok : checkAt 527 1000 box_2925 cert_2925 = true := by
  have h := List.all_eq_true.mp batch_58_12_ok accepted_2925 (by simp [batch_58_12_values])
  exact h
theorem leaf_2925_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2925.profileLo box_2925.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2925_ok
theorem branch_box_2925_nonnegative : ∀ j, 0 ≤ branch_box_2925.lower j ∧ 0 ≤ branch_box_2925.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2925, Box.profileLo, Box.profileHi, box_2925]
theorem leaf_2925_BranchSafe : CertificateConsequences.BranchSafe branch_box_2925 := by
  left; refine ⟨branch_box_2925_nonnegative, ?_⟩
  intro z hz; exact leaf_2925_sound hz

theorem leaf_2926_ok : checkAt 527 1000 box_2926 cert_2926 = true := by
  have h := List.all_eq_true.mp batch_58_13_ok accepted_2926 (by simp [batch_58_13_values])
  exact h
theorem leaf_2926_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2926.profileLo box_2926.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2926_ok
theorem branch_box_2926_nonnegative : ∀ j, 0 ≤ branch_box_2926.lower j ∧ 0 ≤ branch_box_2926.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2926, Box.profileLo, Box.profileHi, box_2926]
theorem leaf_2926_BranchSafe : CertificateConsequences.BranchSafe branch_box_2926 := by
  left; refine ⟨branch_box_2926_nonnegative, ?_⟩
  intro z hz; exact leaf_2926_sound hz

theorem leaf_2927_ok : checkAt 527 1000 box_2927 cert_2927 = true := by
  have h := List.all_eq_true.mp batch_58_14_ok accepted_2927 (by simp [batch_58_14_values])
  exact h
theorem leaf_2927_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2927.profileLo box_2927.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2927_ok
theorem branch_box_2927_nonnegative : ∀ j, 0 ≤ branch_box_2927.lower j ∧ 0 ≤ branch_box_2927.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2927, Box.profileLo, Box.profileHi, box_2927]
theorem leaf_2927_BranchSafe : CertificateConsequences.BranchSafe branch_box_2927 := by
  left; refine ⟨branch_box_2927_nonnegative, ?_⟩
  intro z hz; exact leaf_2927_sound hz

theorem leaf_2928_ok : checkAt 527 1000 box_2928 cert_2928 = true := by
  have h := List.all_eq_true.mp batch_58_15_ok accepted_2928 (by simp [batch_58_15_values])
  exact h
theorem leaf_2928_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2928.profileLo box_2928.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2928_ok
theorem branch_box_2928_nonnegative : ∀ j, 0 ≤ branch_box_2928.lower j ∧ 0 ≤ branch_box_2928.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2928, Box.profileLo, Box.profileHi, box_2928]
theorem leaf_2928_BranchSafe : CertificateConsequences.BranchSafe branch_box_2928 := by
  left; refine ⟨branch_box_2928_nonnegative, ?_⟩
  intro z hz; exact leaf_2928_sound hz

theorem leaf_2931_ok : checkAt 527 1000 box_2931 cert_2931 = true := by
  have h := List.all_eq_true.mp batch_58_16_ok accepted_2931 (by simp [batch_58_16_values])
  exact h
theorem leaf_2931_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2931.profileLo box_2931.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2931_ok
theorem branch_box_2931_nonnegative : ∀ j, 0 ≤ branch_box_2931.lower j ∧ 0 ≤ branch_box_2931.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2931, Box.profileLo, Box.profileHi, box_2931]
theorem leaf_2931_BranchSafe : CertificateConsequences.BranchSafe branch_box_2931 := by
  left; refine ⟨branch_box_2931_nonnegative, ?_⟩
  intro z hz; exact leaf_2931_sound hz

theorem leaf_2933_ok : checkAt 527 1000 box_2933 cert_2933 = true := by
  have h := List.all_eq_true.mp batch_58_17_ok accepted_2933 (by simp [batch_58_17_values])
  exact h
theorem leaf_2933_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2933.profileLo box_2933.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2933_ok
theorem branch_box_2933_nonnegative : ∀ j, 0 ≤ branch_box_2933.lower j ∧ 0 ≤ branch_box_2933.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2933, Box.profileLo, Box.profileHi, box_2933]
theorem leaf_2933_BranchSafe : CertificateConsequences.BranchSafe branch_box_2933 := by
  left; refine ⟨branch_box_2933_nonnegative, ?_⟩
  intro z hz; exact leaf_2933_sound hz

theorem leaf_2934_ok : checkAt 527 1000 box_2934 cert_2934 = true := by
  have h := List.all_eq_true.mp batch_58_18_ok accepted_2934 (by simp [batch_58_18_values])
  exact h
theorem leaf_2934_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2934.profileLo box_2934.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2934_ok
theorem branch_box_2934_nonnegative : ∀ j, 0 ≤ branch_box_2934.lower j ∧ 0 ≤ branch_box_2934.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2934, Box.profileLo, Box.profileHi, box_2934]
theorem leaf_2934_BranchSafe : CertificateConsequences.BranchSafe branch_box_2934 := by
  left; refine ⟨branch_box_2934_nonnegative, ?_⟩
  intro z hz; exact leaf_2934_sound hz

theorem leaf_2937_ok : checkAt 527 1000 box_2937 cert_2937 = true := by
  have h := List.all_eq_true.mp batch_58_19_ok accepted_2937 (by simp [batch_58_19_values])
  exact h
theorem leaf_2937_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2937.profileLo box_2937.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2937_ok
theorem branch_box_2937_nonnegative : ∀ j, 0 ≤ branch_box_2937.lower j ∧ 0 ≤ branch_box_2937.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2937, Box.profileLo, Box.profileHi, box_2937]
theorem leaf_2937_BranchSafe : CertificateConsequences.BranchSafe branch_box_2937 := by
  left; refine ⟨branch_box_2937_nonnegative, ?_⟩
  intro z hz; exact leaf_2937_sound hz

theorem leaf_2938_ok : checkAt 527 1000 box_2938 cert_2938 = true := by
  have h := List.all_eq_true.mp batch_58_20_ok accepted_2938 (by simp [batch_58_20_values])
  exact h
theorem leaf_2938_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2938.profileLo box_2938.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2938_ok
theorem branch_box_2938_nonnegative : ∀ j, 0 ≤ branch_box_2938.lower j ∧ 0 ≤ branch_box_2938.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2938, Box.profileLo, Box.profileHi, box_2938]
theorem leaf_2938_BranchSafe : CertificateConsequences.BranchSafe branch_box_2938 := by
  left; refine ⟨branch_box_2938_nonnegative, ?_⟩
  intro z hz; exact leaf_2938_sound hz

theorem leaf_2939_ok : checkAt 527 1000 box_2939 cert_2939 = true := by
  have h := List.all_eq_true.mp batch_58_21_ok accepted_2939 (by simp [batch_58_21_values])
  exact h
theorem leaf_2939_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2939.profileLo box_2939.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2939_ok
theorem branch_box_2939_nonnegative : ∀ j, 0 ≤ branch_box_2939.lower j ∧ 0 ≤ branch_box_2939.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2939, Box.profileLo, Box.profileHi, box_2939]
theorem leaf_2939_BranchSafe : CertificateConsequences.BranchSafe branch_box_2939 := by
  left; refine ⟨branch_box_2939_nonnegative, ?_⟩
  intro z hz; exact leaf_2939_sound hz

theorem leaf_2941_ok : checkAt 527 1000 box_2941 cert_2941 = true := by
  have h := List.all_eq_true.mp batch_58_22_ok accepted_2941 (by simp [batch_58_22_values])
  exact h
theorem leaf_2941_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2941.profileLo box_2941.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2941_ok
theorem branch_box_2941_nonnegative : ∀ j, 0 ≤ branch_box_2941.lower j ∧ 0 ≤ branch_box_2941.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2941, Box.profileLo, Box.profileHi, box_2941]
theorem leaf_2941_BranchSafe : CertificateConsequences.BranchSafe branch_box_2941 := by
  left; refine ⟨branch_box_2941_nonnegative, ?_⟩
  intro z hz; exact leaf_2941_sound hz

theorem leaf_2942_ok : checkAt 527 1000 box_2942 cert_2942 = true := by
  have h := List.all_eq_true.mp batch_58_23_ok accepted_2942 (by simp [batch_58_23_values])
  exact h
theorem leaf_2942_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2942.profileLo box_2942.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2942_ok
theorem branch_box_2942_nonnegative : ∀ j, 0 ≤ branch_box_2942.lower j ∧ 0 ≤ branch_box_2942.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2942, Box.profileLo, Box.profileHi, box_2942]
theorem leaf_2942_BranchSafe : CertificateConsequences.BranchSafe branch_box_2942 := by
  left; refine ⟨branch_box_2942_nonnegative, ?_⟩
  intro z hz; exact leaf_2942_sound hz

#print axioms batch_58_00_ok
#print axioms leaf_2902_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
