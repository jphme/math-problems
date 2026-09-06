import PeaceableQueens.UpperBound.Generated.Even.CoreScaled58Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_58_00_values : List Bool := [accepted_2900]
theorem batch_58_00_ok : batch_58_00_values.all id = true := by decide

def batch_58_01_values : List Bool := [accepted_2902]
theorem batch_58_01_ok : batch_58_01_values.all id = true := by decide

def batch_58_02_values : List Bool := [accepted_2904]
theorem batch_58_02_ok : batch_58_02_values.all id = true := by decide

def batch_58_03_values : List Bool := [accepted_2906]
theorem batch_58_03_ok : batch_58_03_values.all id = true := by decide

def batch_58_04_values : List Bool := [accepted_2908]
theorem batch_58_04_ok : batch_58_04_values.all id = true := by decide

def batch_58_05_values : List Bool := [accepted_2909]
theorem batch_58_05_ok : batch_58_05_values.all id = true := by decide

def batch_58_06_values : List Bool := [accepted_2912]
theorem batch_58_06_ok : batch_58_06_values.all id = true := by decide

def batch_58_07_values : List Bool := [accepted_2914]
theorem batch_58_07_ok : batch_58_07_values.all id = true := by decide

def batch_58_08_values : List Bool := [accepted_2916]
theorem batch_58_08_ok : batch_58_08_values.all id = true := by decide

def batch_58_09_values : List Bool := [accepted_2918]
theorem batch_58_09_ok : batch_58_09_values.all id = true := by decide

def batch_58_10_values : List Bool := [accepted_2920]
theorem batch_58_10_ok : batch_58_10_values.all id = true := by decide

def batch_58_11_values : List Bool := [accepted_2922]
theorem batch_58_11_ok : batch_58_11_values.all id = true := by decide

def batch_58_12_values : List Bool := [accepted_2923]
theorem batch_58_12_ok : batch_58_12_values.all id = true := by decide

def batch_58_13_values : List Bool := [accepted_2926]
theorem batch_58_13_ok : batch_58_13_values.all id = true := by decide

def batch_58_14_values : List Bool := [accepted_2928]
theorem batch_58_14_ok : batch_58_14_values.all id = true := by decide

def batch_58_15_values : List Bool := [accepted_2930]
theorem batch_58_15_ok : batch_58_15_values.all id = true := by decide

def batch_58_16_values : List Bool := [accepted_2932]
theorem batch_58_16_ok : batch_58_16_values.all id = true := by decide

def batch_58_17_values : List Bool := [accepted_2934]
theorem batch_58_17_ok : batch_58_17_values.all id = true := by decide

def batch_58_18_values : List Bool := [accepted_2936]
theorem batch_58_18_ok : batch_58_18_values.all id = true := by decide

def batch_58_19_values : List Bool := [accepted_2937]
theorem batch_58_19_ok : batch_58_19_values.all id = true := by decide

def batch_58_20_values : List Bool := [accepted_2940]
theorem batch_58_20_ok : batch_58_20_values.all id = true := by decide

def batch_58_21_values : List Bool := [accepted_2942]
theorem batch_58_21_ok : batch_58_21_values.all id = true := by decide

def batch_58_22_values : List Bool := [accepted_2944]
theorem batch_58_22_ok : batch_58_22_values.all id = true := by decide

def batch_58_23_values : List Bool := [accepted_2948]
theorem batch_58_23_ok : batch_58_23_values.all id = true := by decide

theorem leaf_2900_ok : checkAt 527 1000 box_2900 cert_2900 = true := by
  have h := List.all_eq_true.mp batch_58_00_ok accepted_2900 (by simp [batch_58_00_values])
  exact h
theorem leaf_2900_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2900.profileLo box_2900.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2900_ok
theorem branch_box_2900_nonnegative : ∀ j, 0 ≤ branch_box_2900.lower j ∧ 0 ≤ branch_box_2900.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2900, Box.profileLo, Box.profileHi, box_2900]
theorem leaf_2900_BranchSafe : CertificateConsequences.BranchSafe branch_box_2900 := by
  left; refine ⟨branch_box_2900_nonnegative, ?_⟩
  intro z hz; exact leaf_2900_sound hz

theorem leaf_2902_ok : checkAt 527 1000 box_2902 cert_2902 = true := by
  have h := List.all_eq_true.mp batch_58_01_ok accepted_2902 (by simp [batch_58_01_values])
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

theorem leaf_2906_ok : checkAt 527 1000 box_2906 cert_2906 = true := by
  have h := List.all_eq_true.mp batch_58_03_ok accepted_2906 (by simp [batch_58_03_values])
  exact h
theorem leaf_2906_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2906.profileLo box_2906.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2906_ok
theorem branch_box_2906_nonnegative : ∀ j, 0 ≤ branch_box_2906.lower j ∧ 0 ≤ branch_box_2906.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2906, Box.profileLo, Box.profileHi, box_2906]
theorem leaf_2906_BranchSafe : CertificateConsequences.BranchSafe branch_box_2906 := by
  left; refine ⟨branch_box_2906_nonnegative, ?_⟩
  intro z hz; exact leaf_2906_sound hz

theorem leaf_2908_ok : checkAt 527 1000 box_2908 cert_2908 = true := by
  have h := List.all_eq_true.mp batch_58_04_ok accepted_2908 (by simp [batch_58_04_values])
  exact h
theorem leaf_2908_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2908.profileLo box_2908.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2908_ok
theorem branch_box_2908_nonnegative : ∀ j, 0 ≤ branch_box_2908.lower j ∧ 0 ≤ branch_box_2908.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2908, Box.profileLo, Box.profileHi, box_2908]
theorem leaf_2908_BranchSafe : CertificateConsequences.BranchSafe branch_box_2908 := by
  left; refine ⟨branch_box_2908_nonnegative, ?_⟩
  intro z hz; exact leaf_2908_sound hz

theorem leaf_2909_ok : checkAt 527 1000 box_2909 cert_2909 = true := by
  have h := List.all_eq_true.mp batch_58_05_ok accepted_2909 (by simp [batch_58_05_values])
  exact h
theorem leaf_2909_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2909.profileLo box_2909.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2909_ok
theorem branch_box_2909_nonnegative : ∀ j, 0 ≤ branch_box_2909.lower j ∧ 0 ≤ branch_box_2909.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2909, Box.profileLo, Box.profileHi, box_2909]
theorem leaf_2909_BranchSafe : CertificateConsequences.BranchSafe branch_box_2909 := by
  left; refine ⟨branch_box_2909_nonnegative, ?_⟩
  intro z hz; exact leaf_2909_sound hz

theorem leaf_2912_ok : checkAt 527 1000 box_2912 cert_2912 = true := by
  have h := List.all_eq_true.mp batch_58_06_ok accepted_2912 (by simp [batch_58_06_values])
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

theorem leaf_2914_ok : checkAt 527 1000 box_2914 cert_2914 = true := by
  have h := List.all_eq_true.mp batch_58_07_ok accepted_2914 (by simp [batch_58_07_values])
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

theorem leaf_2916_ok : checkAt 527 1000 box_2916 cert_2916 = true := by
  have h := List.all_eq_true.mp batch_58_08_ok accepted_2916 (by simp [batch_58_08_values])
  exact h
theorem leaf_2916_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2916.profileLo box_2916.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2916_ok
theorem branch_box_2916_nonnegative : ∀ j, 0 ≤ branch_box_2916.lower j ∧ 0 ≤ branch_box_2916.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2916, Box.profileLo, Box.profileHi, box_2916]
theorem leaf_2916_BranchSafe : CertificateConsequences.BranchSafe branch_box_2916 := by
  left; refine ⟨branch_box_2916_nonnegative, ?_⟩
  intro z hz; exact leaf_2916_sound hz

theorem leaf_2918_ok : checkAt 527 1000 box_2918 cert_2918 = true := by
  have h := List.all_eq_true.mp batch_58_09_ok accepted_2918 (by simp [batch_58_09_values])
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

theorem leaf_2920_ok : checkAt 527 1000 box_2920 cert_2920 = true := by
  have h := List.all_eq_true.mp batch_58_10_ok accepted_2920 (by simp [batch_58_10_values])
  exact h
theorem leaf_2920_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2920.profileLo box_2920.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2920_ok
theorem branch_box_2920_nonnegative : ∀ j, 0 ≤ branch_box_2920.lower j ∧ 0 ≤ branch_box_2920.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2920, Box.profileLo, Box.profileHi, box_2920]
theorem leaf_2920_BranchSafe : CertificateConsequences.BranchSafe branch_box_2920 := by
  left; refine ⟨branch_box_2920_nonnegative, ?_⟩
  intro z hz; exact leaf_2920_sound hz

theorem leaf_2922_ok : checkAt 527 1000 box_2922 cert_2922 = true := by
  have h := List.all_eq_true.mp batch_58_11_ok accepted_2922 (by simp [batch_58_11_values])
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
  have h := List.all_eq_true.mp batch_58_12_ok accepted_2923 (by simp [batch_58_12_values])
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

theorem leaf_2928_ok : checkAt 527 1000 box_2928 cert_2928 = true := by
  have h := List.all_eq_true.mp batch_58_14_ok accepted_2928 (by simp [batch_58_14_values])
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

theorem leaf_2930_ok : checkAt 527 1000 box_2930 cert_2930 = true := by
  have h := List.all_eq_true.mp batch_58_15_ok accepted_2930 (by simp [batch_58_15_values])
  exact h
theorem leaf_2930_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2930.profileLo box_2930.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2930_ok
theorem branch_box_2930_nonnegative : ∀ j, 0 ≤ branch_box_2930.lower j ∧ 0 ≤ branch_box_2930.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2930, Box.profileLo, Box.profileHi, box_2930]
theorem leaf_2930_BranchSafe : CertificateConsequences.BranchSafe branch_box_2930 := by
  left; refine ⟨branch_box_2930_nonnegative, ?_⟩
  intro z hz; exact leaf_2930_sound hz

theorem leaf_2932_ok : checkAt 527 1000 box_2932 cert_2932 = true := by
  have h := List.all_eq_true.mp batch_58_16_ok accepted_2932 (by simp [batch_58_16_values])
  exact h
theorem leaf_2932_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2932.profileLo box_2932.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2932_ok
theorem branch_box_2932_nonnegative : ∀ j, 0 ≤ branch_box_2932.lower j ∧ 0 ≤ branch_box_2932.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2932, Box.profileLo, Box.profileHi, box_2932]
theorem leaf_2932_BranchSafe : CertificateConsequences.BranchSafe branch_box_2932 := by
  left; refine ⟨branch_box_2932_nonnegative, ?_⟩
  intro z hz; exact leaf_2932_sound hz

theorem leaf_2934_ok : checkAt 527 1000 box_2934 cert_2934 = true := by
  have h := List.all_eq_true.mp batch_58_17_ok accepted_2934 (by simp [batch_58_17_values])
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

theorem leaf_2936_ok : checkAt 527 1000 box_2936 cert_2936 = true := by
  have h := List.all_eq_true.mp batch_58_18_ok accepted_2936 (by simp [batch_58_18_values])
  exact h
theorem leaf_2936_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2936.profileLo box_2936.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2936_ok
theorem branch_box_2936_nonnegative : ∀ j, 0 ≤ branch_box_2936.lower j ∧ 0 ≤ branch_box_2936.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2936, Box.profileLo, Box.profileHi, box_2936]
theorem leaf_2936_BranchSafe : CertificateConsequences.BranchSafe branch_box_2936 := by
  left; refine ⟨branch_box_2936_nonnegative, ?_⟩
  intro z hz; exact leaf_2936_sound hz

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

theorem leaf_2940_ok : checkAt 527 1000 box_2940 cert_2940 = true := by
  have h := List.all_eq_true.mp batch_58_20_ok accepted_2940 (by simp [batch_58_20_values])
  exact h
theorem leaf_2940_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2940.profileLo box_2940.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2940_ok
theorem branch_box_2940_nonnegative : ∀ j, 0 ≤ branch_box_2940.lower j ∧ 0 ≤ branch_box_2940.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2940, Box.profileLo, Box.profileHi, box_2940]
theorem leaf_2940_BranchSafe : CertificateConsequences.BranchSafe branch_box_2940 := by
  left; refine ⟨branch_box_2940_nonnegative, ?_⟩
  intro z hz; exact leaf_2940_sound hz

theorem leaf_2942_ok : checkAt 527 1000 box_2942 cert_2942 = true := by
  have h := List.all_eq_true.mp batch_58_21_ok accepted_2942 (by simp [batch_58_21_values])
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

theorem leaf_2944_ok : checkAt 527 1000 box_2944 cert_2944 = true := by
  have h := List.all_eq_true.mp batch_58_22_ok accepted_2944 (by simp [batch_58_22_values])
  exact h
theorem leaf_2944_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2944.profileLo box_2944.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2944_ok
theorem branch_box_2944_nonnegative : ∀ j, 0 ≤ branch_box_2944.lower j ∧ 0 ≤ branch_box_2944.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2944, Box.profileLo, Box.profileHi, box_2944]
theorem leaf_2944_BranchSafe : CertificateConsequences.BranchSafe branch_box_2944 := by
  left; refine ⟨branch_box_2944_nonnegative, ?_⟩
  intro z hz; exact leaf_2944_sound hz

theorem leaf_2948_ok : checkAt 527 1000 box_2948 cert_2948 = true := by
  have h := List.all_eq_true.mp batch_58_23_ok accepted_2948 (by simp [batch_58_23_values])
  exact h
theorem leaf_2948_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2948.profileLo box_2948.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2948_ok
theorem branch_box_2948_nonnegative : ∀ j, 0 ≤ branch_box_2948.lower j ∧ 0 ≤ branch_box_2948.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2948, Box.profileLo, Box.profileHi, box_2948]
theorem leaf_2948_BranchSafe : CertificateConsequences.BranchSafe branch_box_2948 := by
  left; refine ⟨branch_box_2948_nonnegative, ?_⟩
  intro z hz; exact leaf_2948_sound hz

#print axioms batch_58_00_ok
#print axioms leaf_2900_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
