import PeaceableQueens.UpperBound.Generated.Even.C527Scaled56Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_56_00_values : List Bool := [accepted_2807]
theorem batch_56_00_ok : batch_56_00_values.all id = true := by decide

def batch_56_01_values : List Bool := [accepted_2808]
theorem batch_56_01_ok : batch_56_01_values.all id = true := by decide

def batch_56_02_values : List Bool := [accepted_2809]
theorem batch_56_02_ok : batch_56_02_values.all id = true := by decide

def batch_56_03_values : List Bool := [accepted_2810]
theorem batch_56_03_ok : batch_56_03_values.all id = true := by decide

def batch_56_04_values : List Bool := [accepted_2813]
theorem batch_56_04_ok : batch_56_04_values.all id = true := by decide

def batch_56_05_values : List Bool := [accepted_2814]
theorem batch_56_05_ok : batch_56_05_values.all id = true := by decide

def batch_56_06_values : List Bool := [accepted_2815]
theorem batch_56_06_ok : batch_56_06_values.all id = true := by decide

def batch_56_07_values : List Bool := [accepted_2817]
theorem batch_56_07_ok : batch_56_07_values.all id = true := by decide

def batch_56_08_values : List Bool := [accepted_2819]
theorem batch_56_08_ok : batch_56_08_values.all id = true := by decide

def batch_56_09_values : List Bool := [accepted_2820]
theorem batch_56_09_ok : batch_56_09_values.all id = true := by decide

def batch_56_10_values : List Bool := [accepted_2823]
theorem batch_56_10_ok : batch_56_10_values.all id = true := by decide

def batch_56_11_values : List Bool := [accepted_2825]
theorem batch_56_11_ok : batch_56_11_values.all id = true := by decide

def batch_56_12_values : List Bool := [accepted_2826]
theorem batch_56_12_ok : batch_56_12_values.all id = true := by decide

def batch_56_13_values : List Bool := [accepted_2829]
theorem batch_56_13_ok : batch_56_13_values.all id = true := by decide

def batch_56_14_values : List Bool := [accepted_2830]
theorem batch_56_14_ok : batch_56_14_values.all id = true := by decide

def batch_56_15_values : List Bool := [accepted_2831]
theorem batch_56_15_ok : batch_56_15_values.all id = true := by decide

def batch_56_16_values : List Bool := [accepted_2833]
theorem batch_56_16_ok : batch_56_16_values.all id = true := by decide

def batch_56_17_values : List Bool := [accepted_2836]
theorem batch_56_17_ok : batch_56_17_values.all id = true := by decide

def batch_56_18_values : List Bool := [accepted_2837]
theorem batch_56_18_ok : batch_56_18_values.all id = true := by decide

def batch_56_19_values : List Bool := [accepted_2838]
theorem batch_56_19_ok : batch_56_19_values.all id = true := by decide

def batch_56_20_values : List Bool := [accepted_2841]
theorem batch_56_20_ok : batch_56_20_values.all id = true := by decide

def batch_56_21_values : List Bool := [accepted_2842]
theorem batch_56_21_ok : batch_56_21_values.all id = true := by decide

def batch_56_22_values : List Bool := [accepted_2845]
theorem batch_56_22_ok : batch_56_22_values.all id = true := by decide

def batch_56_23_values : List Bool := [accepted_2846]
theorem batch_56_23_ok : batch_56_23_values.all id = true := by decide

def batch_56_24_values : List Bool := [accepted_2847]
theorem batch_56_24_ok : batch_56_24_values.all id = true := by decide

def batch_56_25_values : List Bool := [accepted_2848]
theorem batch_56_25_ok : batch_56_25_values.all id = true := by decide

theorem leaf_2807_ok : checkAt 527 1000 box_2807 cert_2807 = true := by
  have h := List.all_eq_true.mp batch_56_00_ok accepted_2807 (by simp [batch_56_00_values])
  exact h
theorem leaf_2807_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2807.profileLo box_2807.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2807_ok
theorem branch_box_2807_nonnegative : ∀ j, 0 ≤ branch_box_2807.lower j ∧ 0 ≤ branch_box_2807.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2807, Box.profileLo, Box.profileHi, box_2807]
theorem leaf_2807_BranchSafe : CertificateConsequences.BranchSafe branch_box_2807 := by
  left; refine ⟨branch_box_2807_nonnegative, ?_⟩
  intro z hz; exact leaf_2807_sound hz

theorem leaf_2808_ok : checkAt 527 1000 box_2808 cert_2808 = true := by
  have h := List.all_eq_true.mp batch_56_01_ok accepted_2808 (by simp [batch_56_01_values])
  exact h
theorem leaf_2808_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2808.profileLo box_2808.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2808_ok
theorem branch_box_2808_nonnegative : ∀ j, 0 ≤ branch_box_2808.lower j ∧ 0 ≤ branch_box_2808.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2808, Box.profileLo, Box.profileHi, box_2808]
theorem leaf_2808_BranchSafe : CertificateConsequences.BranchSafe branch_box_2808 := by
  left; refine ⟨branch_box_2808_nonnegative, ?_⟩
  intro z hz; exact leaf_2808_sound hz

theorem leaf_2809_ok : checkAt 527 1000 box_2809 cert_2809 = true := by
  have h := List.all_eq_true.mp batch_56_02_ok accepted_2809 (by simp [batch_56_02_values])
  exact h
theorem leaf_2809_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2809.profileLo box_2809.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2809_ok
theorem branch_box_2809_nonnegative : ∀ j, 0 ≤ branch_box_2809.lower j ∧ 0 ≤ branch_box_2809.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2809, Box.profileLo, Box.profileHi, box_2809]
theorem leaf_2809_BranchSafe : CertificateConsequences.BranchSafe branch_box_2809 := by
  left; refine ⟨branch_box_2809_nonnegative, ?_⟩
  intro z hz; exact leaf_2809_sound hz

theorem leaf_2810_ok : checkAt 527 1000 box_2810 cert_2810 = true := by
  have h := List.all_eq_true.mp batch_56_03_ok accepted_2810 (by simp [batch_56_03_values])
  exact h
theorem leaf_2810_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2810.profileLo box_2810.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2810_ok
theorem branch_box_2810_nonnegative : ∀ j, 0 ≤ branch_box_2810.lower j ∧ 0 ≤ branch_box_2810.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2810, Box.profileLo, Box.profileHi, box_2810]
theorem leaf_2810_BranchSafe : CertificateConsequences.BranchSafe branch_box_2810 := by
  left; refine ⟨branch_box_2810_nonnegative, ?_⟩
  intro z hz; exact leaf_2810_sound hz

theorem leaf_2813_ok : checkAt 527 1000 box_2813 cert_2813 = true := by
  have h := List.all_eq_true.mp batch_56_04_ok accepted_2813 (by simp [batch_56_04_values])
  exact h
theorem leaf_2813_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2813.profileLo box_2813.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2813_ok
theorem branch_box_2813_nonnegative : ∀ j, 0 ≤ branch_box_2813.lower j ∧ 0 ≤ branch_box_2813.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2813, Box.profileLo, Box.profileHi, box_2813]
theorem leaf_2813_BranchSafe : CertificateConsequences.BranchSafe branch_box_2813 := by
  left; refine ⟨branch_box_2813_nonnegative, ?_⟩
  intro z hz; exact leaf_2813_sound hz

theorem leaf_2814_ok : checkAt 527 1000 box_2814 cert_2814 = true := by
  have h := List.all_eq_true.mp batch_56_05_ok accepted_2814 (by simp [batch_56_05_values])
  exact h
theorem leaf_2814_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2814.profileLo box_2814.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2814_ok
theorem branch_box_2814_nonnegative : ∀ j, 0 ≤ branch_box_2814.lower j ∧ 0 ≤ branch_box_2814.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2814, Box.profileLo, Box.profileHi, box_2814]
theorem leaf_2814_BranchSafe : CertificateConsequences.BranchSafe branch_box_2814 := by
  left; refine ⟨branch_box_2814_nonnegative, ?_⟩
  intro z hz; exact leaf_2814_sound hz

theorem leaf_2815_ok : checkAt 527 1000 box_2815 cert_2815 = true := by
  have h := List.all_eq_true.mp batch_56_06_ok accepted_2815 (by simp [batch_56_06_values])
  exact h
theorem leaf_2815_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2815.profileLo box_2815.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2815_ok
theorem branch_box_2815_nonnegative : ∀ j, 0 ≤ branch_box_2815.lower j ∧ 0 ≤ branch_box_2815.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2815, Box.profileLo, Box.profileHi, box_2815]
theorem leaf_2815_BranchSafe : CertificateConsequences.BranchSafe branch_box_2815 := by
  left; refine ⟨branch_box_2815_nonnegative, ?_⟩
  intro z hz; exact leaf_2815_sound hz

theorem leaf_2817_ok : checkAt 527 1000 box_2817 cert_2817 = true := by
  have h := List.all_eq_true.mp batch_56_07_ok accepted_2817 (by simp [batch_56_07_values])
  exact h
theorem leaf_2817_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2817.profileLo box_2817.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2817_ok
theorem branch_box_2817_nonnegative : ∀ j, 0 ≤ branch_box_2817.lower j ∧ 0 ≤ branch_box_2817.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2817, Box.profileLo, Box.profileHi, box_2817]
theorem leaf_2817_BranchSafe : CertificateConsequences.BranchSafe branch_box_2817 := by
  left; refine ⟨branch_box_2817_nonnegative, ?_⟩
  intro z hz; exact leaf_2817_sound hz

theorem leaf_2819_ok : checkAt 527 1000 box_2819 cert_2819 = true := by
  have h := List.all_eq_true.mp batch_56_08_ok accepted_2819 (by simp [batch_56_08_values])
  exact h
theorem leaf_2819_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2819.profileLo box_2819.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2819_ok
theorem branch_box_2819_nonnegative : ∀ j, 0 ≤ branch_box_2819.lower j ∧ 0 ≤ branch_box_2819.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2819, Box.profileLo, Box.profileHi, box_2819]
theorem leaf_2819_BranchSafe : CertificateConsequences.BranchSafe branch_box_2819 := by
  left; refine ⟨branch_box_2819_nonnegative, ?_⟩
  intro z hz; exact leaf_2819_sound hz

theorem leaf_2820_ok : checkAt 527 1000 box_2820 cert_2820 = true := by
  have h := List.all_eq_true.mp batch_56_09_ok accepted_2820 (by simp [batch_56_09_values])
  exact h
theorem leaf_2820_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2820.profileLo box_2820.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2820_ok
theorem branch_box_2820_nonnegative : ∀ j, 0 ≤ branch_box_2820.lower j ∧ 0 ≤ branch_box_2820.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2820, Box.profileLo, Box.profileHi, box_2820]
theorem leaf_2820_BranchSafe : CertificateConsequences.BranchSafe branch_box_2820 := by
  left; refine ⟨branch_box_2820_nonnegative, ?_⟩
  intro z hz; exact leaf_2820_sound hz

theorem leaf_2823_ok : checkAt 527 1000 box_2823 cert_2823 = true := by
  have h := List.all_eq_true.mp batch_56_10_ok accepted_2823 (by simp [batch_56_10_values])
  exact h
theorem leaf_2823_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2823.profileLo box_2823.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2823_ok
theorem branch_box_2823_nonnegative : ∀ j, 0 ≤ branch_box_2823.lower j ∧ 0 ≤ branch_box_2823.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2823, Box.profileLo, Box.profileHi, box_2823]
theorem leaf_2823_BranchSafe : CertificateConsequences.BranchSafe branch_box_2823 := by
  left; refine ⟨branch_box_2823_nonnegative, ?_⟩
  intro z hz; exact leaf_2823_sound hz

theorem leaf_2825_ok : checkAt 527 1000 box_2825 cert_2825 = true := by
  have h := List.all_eq_true.mp batch_56_11_ok accepted_2825 (by simp [batch_56_11_values])
  exact h
theorem leaf_2825_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2825.profileLo box_2825.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2825_ok
theorem branch_box_2825_nonnegative : ∀ j, 0 ≤ branch_box_2825.lower j ∧ 0 ≤ branch_box_2825.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2825, Box.profileLo, Box.profileHi, box_2825]
theorem leaf_2825_BranchSafe : CertificateConsequences.BranchSafe branch_box_2825 := by
  left; refine ⟨branch_box_2825_nonnegative, ?_⟩
  intro z hz; exact leaf_2825_sound hz

theorem leaf_2826_ok : checkAt 527 1000 box_2826 cert_2826 = true := by
  have h := List.all_eq_true.mp batch_56_12_ok accepted_2826 (by simp [batch_56_12_values])
  exact h
theorem leaf_2826_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2826.profileLo box_2826.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2826_ok
theorem branch_box_2826_nonnegative : ∀ j, 0 ≤ branch_box_2826.lower j ∧ 0 ≤ branch_box_2826.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2826, Box.profileLo, Box.profileHi, box_2826]
theorem leaf_2826_BranchSafe : CertificateConsequences.BranchSafe branch_box_2826 := by
  left; refine ⟨branch_box_2826_nonnegative, ?_⟩
  intro z hz; exact leaf_2826_sound hz

theorem leaf_2829_ok : checkAt 527 1000 box_2829 cert_2829 = true := by
  have h := List.all_eq_true.mp batch_56_13_ok accepted_2829 (by simp [batch_56_13_values])
  exact h
theorem leaf_2829_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2829.profileLo box_2829.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2829_ok
theorem branch_box_2829_nonnegative : ∀ j, 0 ≤ branch_box_2829.lower j ∧ 0 ≤ branch_box_2829.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2829, Box.profileLo, Box.profileHi, box_2829]
theorem leaf_2829_BranchSafe : CertificateConsequences.BranchSafe branch_box_2829 := by
  left; refine ⟨branch_box_2829_nonnegative, ?_⟩
  intro z hz; exact leaf_2829_sound hz

theorem leaf_2830_ok : checkAt 527 1000 box_2830 cert_2830 = true := by
  have h := List.all_eq_true.mp batch_56_14_ok accepted_2830 (by simp [batch_56_14_values])
  exact h
theorem leaf_2830_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2830.profileLo box_2830.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2830_ok
theorem branch_box_2830_nonnegative : ∀ j, 0 ≤ branch_box_2830.lower j ∧ 0 ≤ branch_box_2830.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2830, Box.profileLo, Box.profileHi, box_2830]
theorem leaf_2830_BranchSafe : CertificateConsequences.BranchSafe branch_box_2830 := by
  left; refine ⟨branch_box_2830_nonnegative, ?_⟩
  intro z hz; exact leaf_2830_sound hz

theorem leaf_2831_ok : checkAt 527 1000 box_2831 cert_2831 = true := by
  have h := List.all_eq_true.mp batch_56_15_ok accepted_2831 (by simp [batch_56_15_values])
  exact h
theorem leaf_2831_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2831.profileLo box_2831.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2831_ok
theorem branch_box_2831_nonnegative : ∀ j, 0 ≤ branch_box_2831.lower j ∧ 0 ≤ branch_box_2831.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2831, Box.profileLo, Box.profileHi, box_2831]
theorem leaf_2831_BranchSafe : CertificateConsequences.BranchSafe branch_box_2831 := by
  left; refine ⟨branch_box_2831_nonnegative, ?_⟩
  intro z hz; exact leaf_2831_sound hz

theorem leaf_2833_ok : checkAt 527 1000 box_2833 cert_2833 = true := by
  have h := List.all_eq_true.mp batch_56_16_ok accepted_2833 (by simp [batch_56_16_values])
  exact h
theorem leaf_2833_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2833.profileLo box_2833.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2833_ok
theorem branch_box_2833_nonnegative : ∀ j, 0 ≤ branch_box_2833.lower j ∧ 0 ≤ branch_box_2833.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2833, Box.profileLo, Box.profileHi, box_2833]
theorem leaf_2833_BranchSafe : CertificateConsequences.BranchSafe branch_box_2833 := by
  left; refine ⟨branch_box_2833_nonnegative, ?_⟩
  intro z hz; exact leaf_2833_sound hz

theorem leaf_2836_ok : checkAt 527 1000 box_2836 cert_2836 = true := by
  have h := List.all_eq_true.mp batch_56_17_ok accepted_2836 (by simp [batch_56_17_values])
  exact h
theorem leaf_2836_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2836.profileLo box_2836.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2836_ok
theorem branch_box_2836_nonnegative : ∀ j, 0 ≤ branch_box_2836.lower j ∧ 0 ≤ branch_box_2836.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2836, Box.profileLo, Box.profileHi, box_2836]
theorem leaf_2836_BranchSafe : CertificateConsequences.BranchSafe branch_box_2836 := by
  left; refine ⟨branch_box_2836_nonnegative, ?_⟩
  intro z hz; exact leaf_2836_sound hz

theorem leaf_2837_ok : checkAt 527 1000 box_2837 cert_2837 = true := by
  have h := List.all_eq_true.mp batch_56_18_ok accepted_2837 (by simp [batch_56_18_values])
  exact h
theorem leaf_2837_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2837.profileLo box_2837.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2837_ok
theorem branch_box_2837_nonnegative : ∀ j, 0 ≤ branch_box_2837.lower j ∧ 0 ≤ branch_box_2837.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2837, Box.profileLo, Box.profileHi, box_2837]
theorem leaf_2837_BranchSafe : CertificateConsequences.BranchSafe branch_box_2837 := by
  left; refine ⟨branch_box_2837_nonnegative, ?_⟩
  intro z hz; exact leaf_2837_sound hz

theorem leaf_2838_ok : checkAt 527 1000 box_2838 cert_2838 = true := by
  have h := List.all_eq_true.mp batch_56_19_ok accepted_2838 (by simp [batch_56_19_values])
  exact h
theorem leaf_2838_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2838.profileLo box_2838.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2838_ok
theorem branch_box_2838_nonnegative : ∀ j, 0 ≤ branch_box_2838.lower j ∧ 0 ≤ branch_box_2838.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2838, Box.profileLo, Box.profileHi, box_2838]
theorem leaf_2838_BranchSafe : CertificateConsequences.BranchSafe branch_box_2838 := by
  left; refine ⟨branch_box_2838_nonnegative, ?_⟩
  intro z hz; exact leaf_2838_sound hz

theorem leaf_2841_ok : checkAt 527 1000 box_2841 cert_2841 = true := by
  have h := List.all_eq_true.mp batch_56_20_ok accepted_2841 (by simp [batch_56_20_values])
  exact h
theorem leaf_2841_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2841.profileLo box_2841.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2841_ok
theorem branch_box_2841_nonnegative : ∀ j, 0 ≤ branch_box_2841.lower j ∧ 0 ≤ branch_box_2841.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2841, Box.profileLo, Box.profileHi, box_2841]
theorem leaf_2841_BranchSafe : CertificateConsequences.BranchSafe branch_box_2841 := by
  left; refine ⟨branch_box_2841_nonnegative, ?_⟩
  intro z hz; exact leaf_2841_sound hz

theorem leaf_2842_ok : checkAt 527 1000 box_2842 cert_2842 = true := by
  have h := List.all_eq_true.mp batch_56_21_ok accepted_2842 (by simp [batch_56_21_values])
  exact h
theorem leaf_2842_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2842.profileLo box_2842.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2842_ok
theorem branch_box_2842_nonnegative : ∀ j, 0 ≤ branch_box_2842.lower j ∧ 0 ≤ branch_box_2842.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2842, Box.profileLo, Box.profileHi, box_2842]
theorem leaf_2842_BranchSafe : CertificateConsequences.BranchSafe branch_box_2842 := by
  left; refine ⟨branch_box_2842_nonnegative, ?_⟩
  intro z hz; exact leaf_2842_sound hz

theorem leaf_2845_ok : checkAt 527 1000 box_2845 cert_2845 = true := by
  have h := List.all_eq_true.mp batch_56_22_ok accepted_2845 (by simp [batch_56_22_values])
  exact h
theorem leaf_2845_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2845.profileLo box_2845.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2845_ok
theorem branch_box_2845_nonnegative : ∀ j, 0 ≤ branch_box_2845.lower j ∧ 0 ≤ branch_box_2845.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2845, Box.profileLo, Box.profileHi, box_2845]
theorem leaf_2845_BranchSafe : CertificateConsequences.BranchSafe branch_box_2845 := by
  left; refine ⟨branch_box_2845_nonnegative, ?_⟩
  intro z hz; exact leaf_2845_sound hz

theorem leaf_2846_ok : checkAt 527 1000 box_2846 cert_2846 = true := by
  have h := List.all_eq_true.mp batch_56_23_ok accepted_2846 (by simp [batch_56_23_values])
  exact h
theorem leaf_2846_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2846.profileLo box_2846.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2846_ok
theorem branch_box_2846_nonnegative : ∀ j, 0 ≤ branch_box_2846.lower j ∧ 0 ≤ branch_box_2846.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2846, Box.profileLo, Box.profileHi, box_2846]
theorem leaf_2846_BranchSafe : CertificateConsequences.BranchSafe branch_box_2846 := by
  left; refine ⟨branch_box_2846_nonnegative, ?_⟩
  intro z hz; exact leaf_2846_sound hz

theorem leaf_2847_ok : checkAt 527 1000 box_2847 cert_2847 = true := by
  have h := List.all_eq_true.mp batch_56_24_ok accepted_2847 (by simp [batch_56_24_values])
  exact h
theorem leaf_2847_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2847.profileLo box_2847.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2847_ok
theorem branch_box_2847_nonnegative : ∀ j, 0 ≤ branch_box_2847.lower j ∧ 0 ≤ branch_box_2847.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2847, Box.profileLo, Box.profileHi, box_2847]
theorem leaf_2847_BranchSafe : CertificateConsequences.BranchSafe branch_box_2847 := by
  left; refine ⟨branch_box_2847_nonnegative, ?_⟩
  intro z hz; exact leaf_2847_sound hz

theorem leaf_2848_ok : checkAt 527 1000 box_2848 cert_2848 = true := by
  have h := List.all_eq_true.mp batch_56_25_ok accepted_2848 (by simp [batch_56_25_values])
  exact h
theorem leaf_2848_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2848.profileLo box_2848.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2848_ok
theorem branch_box_2848_nonnegative : ∀ j, 0 ≤ branch_box_2848.lower j ∧ 0 ≤ branch_box_2848.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2848, Box.profileLo, Box.profileHi, box_2848]
theorem leaf_2848_BranchSafe : CertificateConsequences.BranchSafe branch_box_2848 := by
  left; refine ⟨branch_box_2848_nonnegative, ?_⟩
  intro z hz; exact leaf_2848_sound hz

#print axioms batch_56_00_ok
#print axioms leaf_2807_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
