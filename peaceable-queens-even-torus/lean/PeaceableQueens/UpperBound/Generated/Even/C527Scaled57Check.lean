import PeaceableQueens.UpperBound.Generated.Even.C527Scaled57Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_57_00_values : List Bool := [accepted_2855]
theorem batch_57_00_ok : batch_57_00_values.all id = true := by decide

def batch_57_01_values : List Bool := [accepted_2857]
theorem batch_57_01_ok : batch_57_01_values.all id = true := by decide

def batch_57_02_values : List Bool := [accepted_2859]
theorem batch_57_02_ok : batch_57_02_values.all id = true := by decide

def batch_57_03_values : List Bool := [accepted_2860]
theorem batch_57_03_ok : batch_57_03_values.all id = true := by decide

def batch_57_04_values : List Bool := [accepted_2863]
theorem batch_57_04_ok : batch_57_04_values.all id = true := by decide

def batch_57_05_values : List Bool := [accepted_2864]
theorem batch_57_05_ok : batch_57_05_values.all id = true := by decide

def batch_57_06_values : List Bool := [accepted_2866]
theorem batch_57_06_ok : batch_57_06_values.all id = true := by decide

def batch_57_07_values : List Bool := [accepted_2867]
theorem batch_57_07_ok : batch_57_07_values.all id = true := by decide

def batch_57_08_values : List Bool := [accepted_2868]
theorem batch_57_08_ok : batch_57_08_values.all id = true := by decide

def batch_57_09_values : List Bool := [accepted_2873]
theorem batch_57_09_ok : batch_57_09_values.all id = true := by decide

def batch_57_10_values : List Bool := [accepted_2874]
theorem batch_57_10_ok : batch_57_10_values.all id = true := by decide

def batch_57_11_values : List Bool := [accepted_2880]
theorem batch_57_11_ok : batch_57_11_values.all id = true := by decide

def batch_57_12_values : List Bool := [accepted_2881]
theorem batch_57_12_ok : batch_57_12_values.all id = true := by decide

def batch_57_13_values : List Bool := [accepted_2882]
theorem batch_57_13_ok : batch_57_13_values.all id = true := by decide

def batch_57_14_values : List Bool := [accepted_2887]
theorem batch_57_14_ok : batch_57_14_values.all id = true := by decide

def batch_57_15_values : List Bool := [accepted_2889]
theorem batch_57_15_ok : batch_57_15_values.all id = true := by decide

def batch_57_16_values : List Bool := [accepted_2890]
theorem batch_57_16_ok : batch_57_16_values.all id = true := by decide

def batch_57_17_values : List Bool := [accepted_2891]
theorem batch_57_17_ok : batch_57_17_values.all id = true := by decide

def batch_57_18_values : List Bool := [accepted_2893]
theorem batch_57_18_ok : batch_57_18_values.all id = true := by decide

def batch_57_19_values : List Bool := [accepted_2894]
theorem batch_57_19_ok : batch_57_19_values.all id = true := by decide

def batch_57_20_values : List Bool := [accepted_2895]
theorem batch_57_20_ok : batch_57_20_values.all id = true := by decide

def batch_57_21_values : List Bool := [accepted_2896]
theorem batch_57_21_ok : batch_57_21_values.all id = true := by decide

def batch_57_22_values : List Bool := [accepted_2897]
theorem batch_57_22_ok : batch_57_22_values.all id = true := by decide

def batch_57_23_values : List Bool := [accepted_2898]
theorem batch_57_23_ok : batch_57_23_values.all id = true := by decide

theorem leaf_2855_ok : checkAt 527 1000 box_2855 cert_2855 = true := by
  have h := List.all_eq_true.mp batch_57_00_ok accepted_2855 (by simp [batch_57_00_values])
  exact h
theorem leaf_2855_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2855.profileLo box_2855.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2855_ok
theorem branch_box_2855_nonnegative : ∀ j, 0 ≤ branch_box_2855.lower j ∧ 0 ≤ branch_box_2855.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2855, Box.profileLo, Box.profileHi, box_2855]
theorem leaf_2855_BranchSafe : CertificateConsequences.BranchSafe branch_box_2855 := by
  left; refine ⟨branch_box_2855_nonnegative, ?_⟩
  intro z hz; exact leaf_2855_sound hz

theorem leaf_2857_ok : checkAt 527 1000 box_2857 cert_2857 = true := by
  have h := List.all_eq_true.mp batch_57_01_ok accepted_2857 (by simp [batch_57_01_values])
  exact h
theorem leaf_2857_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2857.profileLo box_2857.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2857_ok
theorem branch_box_2857_nonnegative : ∀ j, 0 ≤ branch_box_2857.lower j ∧ 0 ≤ branch_box_2857.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2857, Box.profileLo, Box.profileHi, box_2857]
theorem leaf_2857_BranchSafe : CertificateConsequences.BranchSafe branch_box_2857 := by
  left; refine ⟨branch_box_2857_nonnegative, ?_⟩
  intro z hz; exact leaf_2857_sound hz

theorem leaf_2859_ok : checkAt 527 1000 box_2859 cert_2859 = true := by
  have h := List.all_eq_true.mp batch_57_02_ok accepted_2859 (by simp [batch_57_02_values])
  exact h
theorem leaf_2859_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2859.profileLo box_2859.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2859_ok
theorem branch_box_2859_nonnegative : ∀ j, 0 ≤ branch_box_2859.lower j ∧ 0 ≤ branch_box_2859.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2859, Box.profileLo, Box.profileHi, box_2859]
theorem leaf_2859_BranchSafe : CertificateConsequences.BranchSafe branch_box_2859 := by
  left; refine ⟨branch_box_2859_nonnegative, ?_⟩
  intro z hz; exact leaf_2859_sound hz

theorem leaf_2860_ok : checkAt 527 1000 box_2860 cert_2860 = true := by
  have h := List.all_eq_true.mp batch_57_03_ok accepted_2860 (by simp [batch_57_03_values])
  exact h
theorem leaf_2860_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2860.profileLo box_2860.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2860_ok
theorem branch_box_2860_nonnegative : ∀ j, 0 ≤ branch_box_2860.lower j ∧ 0 ≤ branch_box_2860.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2860, Box.profileLo, Box.profileHi, box_2860]
theorem leaf_2860_BranchSafe : CertificateConsequences.BranchSafe branch_box_2860 := by
  left; refine ⟨branch_box_2860_nonnegative, ?_⟩
  intro z hz; exact leaf_2860_sound hz

theorem leaf_2863_ok : checkAt 527 1000 box_2863 cert_2863 = true := by
  have h := List.all_eq_true.mp batch_57_04_ok accepted_2863 (by simp [batch_57_04_values])
  exact h
theorem leaf_2863_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2863.profileLo box_2863.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2863_ok
theorem branch_box_2863_nonnegative : ∀ j, 0 ≤ branch_box_2863.lower j ∧ 0 ≤ branch_box_2863.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2863, Box.profileLo, Box.profileHi, box_2863]
theorem leaf_2863_BranchSafe : CertificateConsequences.BranchSafe branch_box_2863 := by
  left; refine ⟨branch_box_2863_nonnegative, ?_⟩
  intro z hz; exact leaf_2863_sound hz

theorem leaf_2864_ok : checkAt 527 1000 box_2864 cert_2864 = true := by
  have h := List.all_eq_true.mp batch_57_05_ok accepted_2864 (by simp [batch_57_05_values])
  exact h
theorem leaf_2864_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2864.profileLo box_2864.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2864_ok
theorem branch_box_2864_nonnegative : ∀ j, 0 ≤ branch_box_2864.lower j ∧ 0 ≤ branch_box_2864.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2864, Box.profileLo, Box.profileHi, box_2864]
theorem leaf_2864_BranchSafe : CertificateConsequences.BranchSafe branch_box_2864 := by
  left; refine ⟨branch_box_2864_nonnegative, ?_⟩
  intro z hz; exact leaf_2864_sound hz

theorem leaf_2866_ok : checkAt 527 1000 box_2866 cert_2866 = true := by
  have h := List.all_eq_true.mp batch_57_06_ok accepted_2866 (by simp [batch_57_06_values])
  exact h
theorem leaf_2866_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2866.profileLo box_2866.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2866_ok
theorem branch_box_2866_nonnegative : ∀ j, 0 ≤ branch_box_2866.lower j ∧ 0 ≤ branch_box_2866.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2866, Box.profileLo, Box.profileHi, box_2866]
theorem leaf_2866_BranchSafe : CertificateConsequences.BranchSafe branch_box_2866 := by
  left; refine ⟨branch_box_2866_nonnegative, ?_⟩
  intro z hz; exact leaf_2866_sound hz

theorem leaf_2867_ok : checkAt 527 1000 box_2867 cert_2867 = true := by
  have h := List.all_eq_true.mp batch_57_07_ok accepted_2867 (by simp [batch_57_07_values])
  exact h
theorem leaf_2867_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2867.profileLo box_2867.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2867_ok
theorem branch_box_2867_nonnegative : ∀ j, 0 ≤ branch_box_2867.lower j ∧ 0 ≤ branch_box_2867.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2867, Box.profileLo, Box.profileHi, box_2867]
theorem leaf_2867_BranchSafe : CertificateConsequences.BranchSafe branch_box_2867 := by
  left; refine ⟨branch_box_2867_nonnegative, ?_⟩
  intro z hz; exact leaf_2867_sound hz

theorem leaf_2868_ok : checkAt 527 1000 box_2868 cert_2868 = true := by
  have h := List.all_eq_true.mp batch_57_08_ok accepted_2868 (by simp [batch_57_08_values])
  exact h
theorem leaf_2868_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2868.profileLo box_2868.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2868_ok
theorem branch_box_2868_nonnegative : ∀ j, 0 ≤ branch_box_2868.lower j ∧ 0 ≤ branch_box_2868.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2868, Box.profileLo, Box.profileHi, box_2868]
theorem leaf_2868_BranchSafe : CertificateConsequences.BranchSafe branch_box_2868 := by
  left; refine ⟨branch_box_2868_nonnegative, ?_⟩
  intro z hz; exact leaf_2868_sound hz

theorem leaf_2873_ok : checkAt 527 1000 box_2873 cert_2873 = true := by
  have h := List.all_eq_true.mp batch_57_09_ok accepted_2873 (by simp [batch_57_09_values])
  exact h
theorem leaf_2873_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2873.profileLo box_2873.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2873_ok
theorem branch_box_2873_nonnegative : ∀ j, 0 ≤ branch_box_2873.lower j ∧ 0 ≤ branch_box_2873.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2873, Box.profileLo, Box.profileHi, box_2873]
theorem leaf_2873_BranchSafe : CertificateConsequences.BranchSafe branch_box_2873 := by
  left; refine ⟨branch_box_2873_nonnegative, ?_⟩
  intro z hz; exact leaf_2873_sound hz

theorem leaf_2874_ok : checkAt 527 1000 box_2874 cert_2874 = true := by
  have h := List.all_eq_true.mp batch_57_10_ok accepted_2874 (by simp [batch_57_10_values])
  exact h
theorem leaf_2874_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2874.profileLo box_2874.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2874_ok
theorem branch_box_2874_nonnegative : ∀ j, 0 ≤ branch_box_2874.lower j ∧ 0 ≤ branch_box_2874.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2874, Box.profileLo, Box.profileHi, box_2874]
theorem leaf_2874_BranchSafe : CertificateConsequences.BranchSafe branch_box_2874 := by
  left; refine ⟨branch_box_2874_nonnegative, ?_⟩
  intro z hz; exact leaf_2874_sound hz

theorem leaf_2880_ok : checkAt 527 1000 box_2880 cert_2880 = true := by
  have h := List.all_eq_true.mp batch_57_11_ok accepted_2880 (by simp [batch_57_11_values])
  exact h
theorem leaf_2880_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2880.profileLo box_2880.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2880_ok
theorem branch_box_2880_nonnegative : ∀ j, 0 ≤ branch_box_2880.lower j ∧ 0 ≤ branch_box_2880.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2880, Box.profileLo, Box.profileHi, box_2880]
theorem leaf_2880_BranchSafe : CertificateConsequences.BranchSafe branch_box_2880 := by
  left; refine ⟨branch_box_2880_nonnegative, ?_⟩
  intro z hz; exact leaf_2880_sound hz

theorem leaf_2881_ok : checkAt 527 1000 box_2881 cert_2881 = true := by
  have h := List.all_eq_true.mp batch_57_12_ok accepted_2881 (by simp [batch_57_12_values])
  exact h
theorem leaf_2881_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2881.profileLo box_2881.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2881_ok
theorem branch_box_2881_nonnegative : ∀ j, 0 ≤ branch_box_2881.lower j ∧ 0 ≤ branch_box_2881.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2881, Box.profileLo, Box.profileHi, box_2881]
theorem leaf_2881_BranchSafe : CertificateConsequences.BranchSafe branch_box_2881 := by
  left; refine ⟨branch_box_2881_nonnegative, ?_⟩
  intro z hz; exact leaf_2881_sound hz

theorem leaf_2882_ok : checkAt 527 1000 box_2882 cert_2882 = true := by
  have h := List.all_eq_true.mp batch_57_13_ok accepted_2882 (by simp [batch_57_13_values])
  exact h
theorem leaf_2882_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2882.profileLo box_2882.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2882_ok
theorem branch_box_2882_nonnegative : ∀ j, 0 ≤ branch_box_2882.lower j ∧ 0 ≤ branch_box_2882.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2882, Box.profileLo, Box.profileHi, box_2882]
theorem leaf_2882_BranchSafe : CertificateConsequences.BranchSafe branch_box_2882 := by
  left; refine ⟨branch_box_2882_nonnegative, ?_⟩
  intro z hz; exact leaf_2882_sound hz

theorem leaf_2887_ok : checkAt 527 1000 box_2887 cert_2887 = true := by
  have h := List.all_eq_true.mp batch_57_14_ok accepted_2887 (by simp [batch_57_14_values])
  exact h
theorem leaf_2887_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2887.profileLo box_2887.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2887_ok
theorem branch_box_2887_nonnegative : ∀ j, 0 ≤ branch_box_2887.lower j ∧ 0 ≤ branch_box_2887.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2887, Box.profileLo, Box.profileHi, box_2887]
theorem leaf_2887_BranchSafe : CertificateConsequences.BranchSafe branch_box_2887 := by
  left; refine ⟨branch_box_2887_nonnegative, ?_⟩
  intro z hz; exact leaf_2887_sound hz

theorem leaf_2889_ok : checkAt 527 1000 box_2889 cert_2889 = true := by
  have h := List.all_eq_true.mp batch_57_15_ok accepted_2889 (by simp [batch_57_15_values])
  exact h
theorem leaf_2889_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2889.profileLo box_2889.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2889_ok
theorem branch_box_2889_nonnegative : ∀ j, 0 ≤ branch_box_2889.lower j ∧ 0 ≤ branch_box_2889.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2889, Box.profileLo, Box.profileHi, box_2889]
theorem leaf_2889_BranchSafe : CertificateConsequences.BranchSafe branch_box_2889 := by
  left; refine ⟨branch_box_2889_nonnegative, ?_⟩
  intro z hz; exact leaf_2889_sound hz

theorem leaf_2890_ok : checkAt 527 1000 box_2890 cert_2890 = true := by
  have h := List.all_eq_true.mp batch_57_16_ok accepted_2890 (by simp [batch_57_16_values])
  exact h
theorem leaf_2890_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2890.profileLo box_2890.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2890_ok
theorem branch_box_2890_nonnegative : ∀ j, 0 ≤ branch_box_2890.lower j ∧ 0 ≤ branch_box_2890.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2890, Box.profileLo, Box.profileHi, box_2890]
theorem leaf_2890_BranchSafe : CertificateConsequences.BranchSafe branch_box_2890 := by
  left; refine ⟨branch_box_2890_nonnegative, ?_⟩
  intro z hz; exact leaf_2890_sound hz

theorem leaf_2891_ok : checkAt 527 1000 box_2891 cert_2891 = true := by
  have h := List.all_eq_true.mp batch_57_17_ok accepted_2891 (by simp [batch_57_17_values])
  exact h
theorem leaf_2891_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2891.profileLo box_2891.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2891_ok
theorem branch_box_2891_nonnegative : ∀ j, 0 ≤ branch_box_2891.lower j ∧ 0 ≤ branch_box_2891.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2891, Box.profileLo, Box.profileHi, box_2891]
theorem leaf_2891_BranchSafe : CertificateConsequences.BranchSafe branch_box_2891 := by
  left; refine ⟨branch_box_2891_nonnegative, ?_⟩
  intro z hz; exact leaf_2891_sound hz

theorem leaf_2893_ok : checkAt 527 1000 box_2893 cert_2893 = true := by
  have h := List.all_eq_true.mp batch_57_18_ok accepted_2893 (by simp [batch_57_18_values])
  exact h
theorem leaf_2893_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2893.profileLo box_2893.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2893_ok
theorem branch_box_2893_nonnegative : ∀ j, 0 ≤ branch_box_2893.lower j ∧ 0 ≤ branch_box_2893.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2893, Box.profileLo, Box.profileHi, box_2893]
theorem leaf_2893_BranchSafe : CertificateConsequences.BranchSafe branch_box_2893 := by
  left; refine ⟨branch_box_2893_nonnegative, ?_⟩
  intro z hz; exact leaf_2893_sound hz

theorem leaf_2894_ok : checkAt 527 1000 box_2894 cert_2894 = true := by
  have h := List.all_eq_true.mp batch_57_19_ok accepted_2894 (by simp [batch_57_19_values])
  exact h
theorem leaf_2894_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2894.profileLo box_2894.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2894_ok
theorem branch_box_2894_nonnegative : ∀ j, 0 ≤ branch_box_2894.lower j ∧ 0 ≤ branch_box_2894.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2894, Box.profileLo, Box.profileHi, box_2894]
theorem leaf_2894_BranchSafe : CertificateConsequences.BranchSafe branch_box_2894 := by
  left; refine ⟨branch_box_2894_nonnegative, ?_⟩
  intro z hz; exact leaf_2894_sound hz

theorem leaf_2895_ok : checkAt 527 1000 box_2895 cert_2895 = true := by
  have h := List.all_eq_true.mp batch_57_20_ok accepted_2895 (by simp [batch_57_20_values])
  exact h
theorem leaf_2895_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2895.profileLo box_2895.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2895_ok
theorem branch_box_2895_nonnegative : ∀ j, 0 ≤ branch_box_2895.lower j ∧ 0 ≤ branch_box_2895.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2895, Box.profileLo, Box.profileHi, box_2895]
theorem leaf_2895_BranchSafe : CertificateConsequences.BranchSafe branch_box_2895 := by
  left; refine ⟨branch_box_2895_nonnegative, ?_⟩
  intro z hz; exact leaf_2895_sound hz

theorem leaf_2896_ok : checkAt 527 1000 box_2896 cert_2896 = true := by
  have h := List.all_eq_true.mp batch_57_21_ok accepted_2896 (by simp [batch_57_21_values])
  exact h
theorem leaf_2896_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2896.profileLo box_2896.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2896_ok
theorem branch_box_2896_nonnegative : ∀ j, 0 ≤ branch_box_2896.lower j ∧ 0 ≤ branch_box_2896.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2896, Box.profileLo, Box.profileHi, box_2896]
theorem leaf_2896_BranchSafe : CertificateConsequences.BranchSafe branch_box_2896 := by
  left; refine ⟨branch_box_2896_nonnegative, ?_⟩
  intro z hz; exact leaf_2896_sound hz

theorem leaf_2897_ok : checkAt 527 1000 box_2897 cert_2897 = true := by
  have h := List.all_eq_true.mp batch_57_22_ok accepted_2897 (by simp [batch_57_22_values])
  exact h
theorem leaf_2897_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2897.profileLo box_2897.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2897_ok
theorem branch_box_2897_nonnegative : ∀ j, 0 ≤ branch_box_2897.lower j ∧ 0 ≤ branch_box_2897.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2897, Box.profileLo, Box.profileHi, box_2897]
theorem leaf_2897_BranchSafe : CertificateConsequences.BranchSafe branch_box_2897 := by
  left; refine ⟨branch_box_2897_nonnegative, ?_⟩
  intro z hz; exact leaf_2897_sound hz

theorem leaf_2898_ok : checkAt 527 1000 box_2898 cert_2898 = true := by
  have h := List.all_eq_true.mp batch_57_23_ok accepted_2898 (by simp [batch_57_23_values])
  exact h
theorem leaf_2898_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2898.profileLo box_2898.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2898_ok
theorem branch_box_2898_nonnegative : ∀ j, 0 ≤ branch_box_2898.lower j ∧ 0 ≤ branch_box_2898.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2898, Box.profileLo, Box.profileHi, box_2898]
theorem leaf_2898_BranchSafe : CertificateConsequences.BranchSafe branch_box_2898 := by
  left; refine ⟨branch_box_2898_nonnegative, ?_⟩
  intro z hz; exact leaf_2898_sound hz

#print axioms batch_57_00_ok
#print axioms leaf_2855_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
