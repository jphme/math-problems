import PeaceableQueens.UpperBound.Generated.Even.CoreScaled76Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_76_00_values : List Bool := [accepted_3800]
theorem batch_76_00_ok : batch_76_00_values.all id = true := by decide

def batch_76_01_values : List Bool := [accepted_3806]
theorem batch_76_01_ok : batch_76_01_values.all id = true := by decide

def batch_76_02_values : List Bool := [accepted_3807]
theorem batch_76_02_ok : batch_76_02_values.all id = true := by decide

def batch_76_03_values : List Bool := [accepted_3809]
theorem batch_76_03_ok : batch_76_03_values.all id = true := by decide

def batch_76_04_values : List Bool := [accepted_3812]
theorem batch_76_04_ok : batch_76_04_values.all id = true := by decide

def batch_76_05_values : List Bool := [accepted_3813]
theorem batch_76_05_ok : batch_76_05_values.all id = true := by decide

def batch_76_06_values : List Bool := [accepted_3816]
theorem batch_76_06_ok : batch_76_06_values.all id = true := by decide

def batch_76_07_values : List Bool := [accepted_3820]
theorem batch_76_07_ok : batch_76_07_values.all id = true := by decide

def batch_76_08_values : List Bool := [accepted_3824]
theorem batch_76_08_ok : batch_76_08_values.all id = true := by decide

def batch_76_09_values : List Bool := [accepted_3826]
theorem batch_76_09_ok : batch_76_09_values.all id = true := by decide

def batch_76_10_values : List Bool := [accepted_3828]
theorem batch_76_10_ok : batch_76_10_values.all id = true := by decide

def batch_76_11_values : List Bool := [accepted_3831]
theorem batch_76_11_ok : batch_76_11_values.all id = true := by decide

def batch_76_12_values : List Bool := [accepted_3834]
theorem batch_76_12_ok : batch_76_12_values.all id = true := by decide

def batch_76_13_values : List Bool := [accepted_3836]
theorem batch_76_13_ok : batch_76_13_values.all id = true := by decide

def batch_76_14_values : List Bool := [accepted_3838]
theorem batch_76_14_ok : batch_76_14_values.all id = true := by decide

def batch_76_15_values : List Bool := [accepted_3840]
theorem batch_76_15_ok : batch_76_15_values.all id = true := by decide

def batch_76_16_values : List Bool := [accepted_3842]
theorem batch_76_16_ok : batch_76_16_values.all id = true := by decide

def batch_76_17_values : List Bool := [accepted_3844]
theorem batch_76_17_ok : batch_76_17_values.all id = true := by decide

def batch_76_18_values : List Bool := [accepted_3845]
theorem batch_76_18_ok : batch_76_18_values.all id = true := by decide

def batch_76_19_values : List Bool := [accepted_3847]
theorem batch_76_19_ok : batch_76_19_values.all id = true := by decide

theorem leaf_3800_ok : checkAt 527 1000 box_3800 cert_3800 = true := by
  have h := List.all_eq_true.mp batch_76_00_ok accepted_3800 (by simp [batch_76_00_values])
  exact h
theorem leaf_3800_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3800.profileLo box_3800.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3800_ok
theorem branch_box_3800_nonnegative : ∀ j, 0 ≤ branch_box_3800.lower j ∧ 0 ≤ branch_box_3800.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3800, Box.profileLo, Box.profileHi, box_3800]
theorem leaf_3800_BranchSafe : CertificateConsequences.BranchSafe branch_box_3800 := by
  left; refine ⟨branch_box_3800_nonnegative, ?_⟩
  intro z hz; exact leaf_3800_sound hz

theorem leaf_3806_ok : checkAt 527 1000 box_3806 cert_3806 = true := by
  have h := List.all_eq_true.mp batch_76_01_ok accepted_3806 (by simp [batch_76_01_values])
  exact h
theorem leaf_3806_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3806.profileLo box_3806.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3806_ok
theorem branch_box_3806_nonnegative : ∀ j, 0 ≤ branch_box_3806.lower j ∧ 0 ≤ branch_box_3806.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3806, Box.profileLo, Box.profileHi, box_3806]
theorem leaf_3806_BranchSafe : CertificateConsequences.BranchSafe branch_box_3806 := by
  left; refine ⟨branch_box_3806_nonnegative, ?_⟩
  intro z hz; exact leaf_3806_sound hz

theorem leaf_3807_ok : checkAt 527 1000 box_3807 cert_3807 = true := by
  have h := List.all_eq_true.mp batch_76_02_ok accepted_3807 (by simp [batch_76_02_values])
  exact h
theorem leaf_3807_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3807.profileLo box_3807.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3807_ok
theorem branch_box_3807_nonnegative : ∀ j, 0 ≤ branch_box_3807.lower j ∧ 0 ≤ branch_box_3807.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3807, Box.profileLo, Box.profileHi, box_3807]
theorem leaf_3807_BranchSafe : CertificateConsequences.BranchSafe branch_box_3807 := by
  left; refine ⟨branch_box_3807_nonnegative, ?_⟩
  intro z hz; exact leaf_3807_sound hz

theorem leaf_3809_ok : checkAt 527 1000 box_3809 cert_3809 = true := by
  have h := List.all_eq_true.mp batch_76_03_ok accepted_3809 (by simp [batch_76_03_values])
  exact h
theorem leaf_3809_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3809.profileLo box_3809.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3809_ok
theorem branch_box_3809_nonnegative : ∀ j, 0 ≤ branch_box_3809.lower j ∧ 0 ≤ branch_box_3809.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3809, Box.profileLo, Box.profileHi, box_3809]
theorem leaf_3809_BranchSafe : CertificateConsequences.BranchSafe branch_box_3809 := by
  left; refine ⟨branch_box_3809_nonnegative, ?_⟩
  intro z hz; exact leaf_3809_sound hz

theorem leaf_3812_ok : checkAt 527 1000 box_3812 cert_3812 = true := by
  have h := List.all_eq_true.mp batch_76_04_ok accepted_3812 (by simp [batch_76_04_values])
  exact h
theorem leaf_3812_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3812.profileLo box_3812.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3812_ok
theorem branch_box_3812_nonnegative : ∀ j, 0 ≤ branch_box_3812.lower j ∧ 0 ≤ branch_box_3812.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3812, Box.profileLo, Box.profileHi, box_3812]
theorem leaf_3812_BranchSafe : CertificateConsequences.BranchSafe branch_box_3812 := by
  left; refine ⟨branch_box_3812_nonnegative, ?_⟩
  intro z hz; exact leaf_3812_sound hz

theorem leaf_3813_ok : checkAt 527 1000 box_3813 cert_3813 = true := by
  have h := List.all_eq_true.mp batch_76_05_ok accepted_3813 (by simp [batch_76_05_values])
  exact h
theorem leaf_3813_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3813.profileLo box_3813.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3813_ok
theorem branch_box_3813_nonnegative : ∀ j, 0 ≤ branch_box_3813.lower j ∧ 0 ≤ branch_box_3813.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3813, Box.profileLo, Box.profileHi, box_3813]
theorem leaf_3813_BranchSafe : CertificateConsequences.BranchSafe branch_box_3813 := by
  left; refine ⟨branch_box_3813_nonnegative, ?_⟩
  intro z hz; exact leaf_3813_sound hz

theorem leaf_3816_ok : checkAt 527 1000 box_3816 cert_3816 = true := by
  have h := List.all_eq_true.mp batch_76_06_ok accepted_3816 (by simp [batch_76_06_values])
  exact h
theorem leaf_3816_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3816.profileLo box_3816.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3816_ok
theorem branch_box_3816_nonnegative : ∀ j, 0 ≤ branch_box_3816.lower j ∧ 0 ≤ branch_box_3816.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3816, Box.profileLo, Box.profileHi, box_3816]
theorem leaf_3816_BranchSafe : CertificateConsequences.BranchSafe branch_box_3816 := by
  left; refine ⟨branch_box_3816_nonnegative, ?_⟩
  intro z hz; exact leaf_3816_sound hz

theorem leaf_3820_ok : checkAt 527 1000 box_3820 cert_3820 = true := by
  have h := List.all_eq_true.mp batch_76_07_ok accepted_3820 (by simp [batch_76_07_values])
  exact h
theorem leaf_3820_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3820.profileLo box_3820.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3820_ok
theorem branch_box_3820_nonnegative : ∀ j, 0 ≤ branch_box_3820.lower j ∧ 0 ≤ branch_box_3820.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3820, Box.profileLo, Box.profileHi, box_3820]
theorem leaf_3820_BranchSafe : CertificateConsequences.BranchSafe branch_box_3820 := by
  left; refine ⟨branch_box_3820_nonnegative, ?_⟩
  intro z hz; exact leaf_3820_sound hz

theorem leaf_3824_ok : checkAt 527 1000 box_3824 cert_3824 = true := by
  have h := List.all_eq_true.mp batch_76_08_ok accepted_3824 (by simp [batch_76_08_values])
  exact h
theorem leaf_3824_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3824.profileLo box_3824.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3824_ok
theorem branch_box_3824_nonnegative : ∀ j, 0 ≤ branch_box_3824.lower j ∧ 0 ≤ branch_box_3824.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3824, Box.profileLo, Box.profileHi, box_3824]
theorem leaf_3824_BranchSafe : CertificateConsequences.BranchSafe branch_box_3824 := by
  left; refine ⟨branch_box_3824_nonnegative, ?_⟩
  intro z hz; exact leaf_3824_sound hz

theorem leaf_3826_ok : checkAt 527 1000 box_3826 cert_3826 = true := by
  have h := List.all_eq_true.mp batch_76_09_ok accepted_3826 (by simp [batch_76_09_values])
  exact h
theorem leaf_3826_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3826.profileLo box_3826.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3826_ok
theorem branch_box_3826_nonnegative : ∀ j, 0 ≤ branch_box_3826.lower j ∧ 0 ≤ branch_box_3826.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3826, Box.profileLo, Box.profileHi, box_3826]
theorem leaf_3826_BranchSafe : CertificateConsequences.BranchSafe branch_box_3826 := by
  left; refine ⟨branch_box_3826_nonnegative, ?_⟩
  intro z hz; exact leaf_3826_sound hz

theorem leaf_3828_ok : checkAt 527 1000 box_3828 cert_3828 = true := by
  have h := List.all_eq_true.mp batch_76_10_ok accepted_3828 (by simp [batch_76_10_values])
  exact h
theorem leaf_3828_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3828.profileLo box_3828.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3828_ok
theorem branch_box_3828_nonnegative : ∀ j, 0 ≤ branch_box_3828.lower j ∧ 0 ≤ branch_box_3828.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3828, Box.profileLo, Box.profileHi, box_3828]
theorem leaf_3828_BranchSafe : CertificateConsequences.BranchSafe branch_box_3828 := by
  left; refine ⟨branch_box_3828_nonnegative, ?_⟩
  intro z hz; exact leaf_3828_sound hz

theorem leaf_3831_ok : checkAt 527 1000 box_3831 cert_3831 = true := by
  have h := List.all_eq_true.mp batch_76_11_ok accepted_3831 (by simp [batch_76_11_values])
  exact h
theorem leaf_3831_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3831.profileLo box_3831.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3831_ok
theorem branch_box_3831_nonnegative : ∀ j, 0 ≤ branch_box_3831.lower j ∧ 0 ≤ branch_box_3831.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3831, Box.profileLo, Box.profileHi, box_3831]
theorem leaf_3831_BranchSafe : CertificateConsequences.BranchSafe branch_box_3831 := by
  left; refine ⟨branch_box_3831_nonnegative, ?_⟩
  intro z hz; exact leaf_3831_sound hz

theorem leaf_3834_ok : checkAt 527 1000 box_3834 cert_3834 = true := by
  have h := List.all_eq_true.mp batch_76_12_ok accepted_3834 (by simp [batch_76_12_values])
  exact h
theorem leaf_3834_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3834.profileLo box_3834.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3834_ok
theorem branch_box_3834_nonnegative : ∀ j, 0 ≤ branch_box_3834.lower j ∧ 0 ≤ branch_box_3834.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3834, Box.profileLo, Box.profileHi, box_3834]
theorem leaf_3834_BranchSafe : CertificateConsequences.BranchSafe branch_box_3834 := by
  left; refine ⟨branch_box_3834_nonnegative, ?_⟩
  intro z hz; exact leaf_3834_sound hz

theorem leaf_3836_ok : checkAt 527 1000 box_3836 cert_3836 = true := by
  have h := List.all_eq_true.mp batch_76_13_ok accepted_3836 (by simp [batch_76_13_values])
  exact h
theorem leaf_3836_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3836.profileLo box_3836.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3836_ok
theorem branch_box_3836_nonnegative : ∀ j, 0 ≤ branch_box_3836.lower j ∧ 0 ≤ branch_box_3836.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3836, Box.profileLo, Box.profileHi, box_3836]
theorem leaf_3836_BranchSafe : CertificateConsequences.BranchSafe branch_box_3836 := by
  left; refine ⟨branch_box_3836_nonnegative, ?_⟩
  intro z hz; exact leaf_3836_sound hz

theorem leaf_3838_ok : checkAt 527 1000 box_3838 cert_3838 = true := by
  have h := List.all_eq_true.mp batch_76_14_ok accepted_3838 (by simp [batch_76_14_values])
  exact h
theorem leaf_3838_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3838.profileLo box_3838.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3838_ok
theorem branch_box_3838_nonnegative : ∀ j, 0 ≤ branch_box_3838.lower j ∧ 0 ≤ branch_box_3838.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3838, Box.profileLo, Box.profileHi, box_3838]
theorem leaf_3838_BranchSafe : CertificateConsequences.BranchSafe branch_box_3838 := by
  left; refine ⟨branch_box_3838_nonnegative, ?_⟩
  intro z hz; exact leaf_3838_sound hz

theorem leaf_3840_ok : checkAt 527 1000 box_3840 cert_3840 = true := by
  have h := List.all_eq_true.mp batch_76_15_ok accepted_3840 (by simp [batch_76_15_values])
  exact h
theorem leaf_3840_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3840.profileLo box_3840.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3840_ok
theorem branch_box_3840_nonnegative : ∀ j, 0 ≤ branch_box_3840.lower j ∧ 0 ≤ branch_box_3840.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3840, Box.profileLo, Box.profileHi, box_3840]
theorem leaf_3840_BranchSafe : CertificateConsequences.BranchSafe branch_box_3840 := by
  left; refine ⟨branch_box_3840_nonnegative, ?_⟩
  intro z hz; exact leaf_3840_sound hz

theorem leaf_3842_ok : checkAt 527 1000 box_3842 cert_3842 = true := by
  have h := List.all_eq_true.mp batch_76_16_ok accepted_3842 (by simp [batch_76_16_values])
  exact h
theorem leaf_3842_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3842.profileLo box_3842.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3842_ok
theorem branch_box_3842_nonnegative : ∀ j, 0 ≤ branch_box_3842.lower j ∧ 0 ≤ branch_box_3842.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3842, Box.profileLo, Box.profileHi, box_3842]
theorem leaf_3842_BranchSafe : CertificateConsequences.BranchSafe branch_box_3842 := by
  left; refine ⟨branch_box_3842_nonnegative, ?_⟩
  intro z hz; exact leaf_3842_sound hz

theorem leaf_3844_ok : checkAt 527 1000 box_3844 cert_3844 = true := by
  have h := List.all_eq_true.mp batch_76_17_ok accepted_3844 (by simp [batch_76_17_values])
  exact h
theorem leaf_3844_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3844.profileLo box_3844.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3844_ok
theorem branch_box_3844_nonnegative : ∀ j, 0 ≤ branch_box_3844.lower j ∧ 0 ≤ branch_box_3844.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3844, Box.profileLo, Box.profileHi, box_3844]
theorem leaf_3844_BranchSafe : CertificateConsequences.BranchSafe branch_box_3844 := by
  left; refine ⟨branch_box_3844_nonnegative, ?_⟩
  intro z hz; exact leaf_3844_sound hz

theorem leaf_3845_ok : checkAt 527 1000 box_3845 cert_3845 = true := by
  have h := List.all_eq_true.mp batch_76_18_ok accepted_3845 (by simp [batch_76_18_values])
  exact h
theorem leaf_3845_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3845.profileLo box_3845.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3845_ok
theorem branch_box_3845_nonnegative : ∀ j, 0 ≤ branch_box_3845.lower j ∧ 0 ≤ branch_box_3845.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3845, Box.profileLo, Box.profileHi, box_3845]
theorem leaf_3845_BranchSafe : CertificateConsequences.BranchSafe branch_box_3845 := by
  left; refine ⟨branch_box_3845_nonnegative, ?_⟩
  intro z hz; exact leaf_3845_sound hz

theorem leaf_3847_ok : checkAt 527 1000 box_3847 cert_3847 = true := by
  have h := List.all_eq_true.mp batch_76_19_ok accepted_3847 (by simp [batch_76_19_values])
  exact h
theorem leaf_3847_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3847.profileLo box_3847.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3847_ok
theorem branch_box_3847_nonnegative : ∀ j, 0 ≤ branch_box_3847.lower j ∧ 0 ≤ branch_box_3847.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3847, Box.profileLo, Box.profileHi, box_3847]
theorem leaf_3847_BranchSafe : CertificateConsequences.BranchSafe branch_box_3847 := by
  left; refine ⟨branch_box_3847_nonnegative, ?_⟩
  intro z hz; exact leaf_3847_sound hz

#print axioms batch_76_00_ok
#print axioms leaf_3800_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
