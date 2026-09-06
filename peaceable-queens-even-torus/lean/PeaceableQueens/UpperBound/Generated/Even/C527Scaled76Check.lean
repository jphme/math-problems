import PeaceableQueens.UpperBound.Generated.Even.C527Scaled76Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_76_00_values : List Bool := [accepted_3801]
theorem batch_76_00_ok : batch_76_00_values.all id = true := by decide

def batch_76_01_values : List Bool := [accepted_3802]
theorem batch_76_01_ok : batch_76_01_values.all id = true := by decide

def batch_76_02_values : List Bool := [accepted_3805]
theorem batch_76_02_ok : batch_76_02_values.all id = true := by decide

def batch_76_03_values : List Bool := [accepted_3807]
theorem batch_76_03_ok : batch_76_03_values.all id = true := by decide

def batch_76_04_values : List Bool := [accepted_3809]
theorem batch_76_04_ok : batch_76_04_values.all id = true := by decide

def batch_76_05_values : List Bool := [accepted_3810]
theorem batch_76_05_ok : batch_76_05_values.all id = true := by decide

def batch_76_06_values : List Bool := [accepted_3811]
theorem batch_76_06_ok : batch_76_06_values.all id = true := by decide

def batch_76_07_values : List Bool := [accepted_3813]
theorem batch_76_07_ok : batch_76_07_values.all id = true := by decide

def batch_76_08_values : List Bool := [accepted_3814]
theorem batch_76_08_ok : batch_76_08_values.all id = true := by decide

def batch_76_09_values : List Bool := [accepted_3817]
theorem batch_76_09_ok : batch_76_09_values.all id = true := by decide

def batch_76_10_values : List Bool := [accepted_3819]
theorem batch_76_10_ok : batch_76_10_values.all id = true := by decide

def batch_76_11_values : List Bool := [accepted_3820]
theorem batch_76_11_ok : batch_76_11_values.all id = true := by decide

def batch_76_12_values : List Bool := [accepted_3823]
theorem batch_76_12_ok : batch_76_12_values.all id = true := by decide

def batch_76_13_values : List Bool := [accepted_3825]
theorem batch_76_13_ok : batch_76_13_values.all id = true := by decide

def batch_76_14_values : List Bool := [accepted_3826]
theorem batch_76_14_ok : batch_76_14_values.all id = true := by decide

def batch_76_15_values : List Bool := [accepted_3827]
theorem batch_76_15_ok : batch_76_15_values.all id = true := by decide

def batch_76_16_values : List Bool := [accepted_3829]
theorem batch_76_16_ok : batch_76_16_values.all id = true := by decide

def batch_76_17_values : List Bool := [accepted_3830]
theorem batch_76_17_ok : batch_76_17_values.all id = true := by decide

def batch_76_18_values : List Bool := [accepted_3843]
theorem batch_76_18_ok : batch_76_18_values.all id = true := by decide

def batch_76_19_values : List Bool := [accepted_3845]
theorem batch_76_19_ok : batch_76_19_values.all id = true := by decide

def batch_76_20_values : List Bool := [accepted_3846]
theorem batch_76_20_ok : batch_76_20_values.all id = true := by decide

def batch_76_21_values : List Bool := [accepted_3847]
theorem batch_76_21_ok : batch_76_21_values.all id = true := by decide

def batch_76_22_values : List Bool := [accepted_3848]
theorem batch_76_22_ok : batch_76_22_values.all id = true := by decide

theorem leaf_3801_ok : checkAt 527 1000 box_3801 cert_3801 = true := by
  have h := List.all_eq_true.mp batch_76_00_ok accepted_3801 (by simp [batch_76_00_values])
  exact h
theorem leaf_3801_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3801.profileLo box_3801.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3801_ok
theorem branch_box_3801_nonnegative : ∀ j, 0 ≤ branch_box_3801.lower j ∧ 0 ≤ branch_box_3801.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3801, Box.profileLo, Box.profileHi, box_3801]
theorem leaf_3801_BranchSafe : CertificateConsequences.BranchSafe branch_box_3801 := by
  left; refine ⟨branch_box_3801_nonnegative, ?_⟩
  intro z hz; exact leaf_3801_sound hz

theorem leaf_3802_ok : checkAt 527 1000 box_3802 cert_3802 = true := by
  have h := List.all_eq_true.mp batch_76_01_ok accepted_3802 (by simp [batch_76_01_values])
  exact h
theorem leaf_3802_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3802.profileLo box_3802.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3802_ok
theorem branch_box_3802_nonnegative : ∀ j, 0 ≤ branch_box_3802.lower j ∧ 0 ≤ branch_box_3802.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3802, Box.profileLo, Box.profileHi, box_3802]
theorem leaf_3802_BranchSafe : CertificateConsequences.BranchSafe branch_box_3802 := by
  left; refine ⟨branch_box_3802_nonnegative, ?_⟩
  intro z hz; exact leaf_3802_sound hz

theorem leaf_3805_ok : checkAt 527 1000 box_3805 cert_3805 = true := by
  have h := List.all_eq_true.mp batch_76_02_ok accepted_3805 (by simp [batch_76_02_values])
  exact h
theorem leaf_3805_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3805.profileLo box_3805.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3805_ok
theorem branch_box_3805_nonnegative : ∀ j, 0 ≤ branch_box_3805.lower j ∧ 0 ≤ branch_box_3805.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3805, Box.profileLo, Box.profileHi, box_3805]
theorem leaf_3805_BranchSafe : CertificateConsequences.BranchSafe branch_box_3805 := by
  left; refine ⟨branch_box_3805_nonnegative, ?_⟩
  intro z hz; exact leaf_3805_sound hz

theorem leaf_3807_ok : checkAt 527 1000 box_3807 cert_3807 = true := by
  have h := List.all_eq_true.mp batch_76_03_ok accepted_3807 (by simp [batch_76_03_values])
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
  have h := List.all_eq_true.mp batch_76_04_ok accepted_3809 (by simp [batch_76_04_values])
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

theorem leaf_3810_ok : checkAt 527 1000 box_3810 cert_3810 = true := by
  have h := List.all_eq_true.mp batch_76_05_ok accepted_3810 (by simp [batch_76_05_values])
  exact h
theorem leaf_3810_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3810.profileLo box_3810.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3810_ok
theorem branch_box_3810_nonnegative : ∀ j, 0 ≤ branch_box_3810.lower j ∧ 0 ≤ branch_box_3810.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3810, Box.profileLo, Box.profileHi, box_3810]
theorem leaf_3810_BranchSafe : CertificateConsequences.BranchSafe branch_box_3810 := by
  left; refine ⟨branch_box_3810_nonnegative, ?_⟩
  intro z hz; exact leaf_3810_sound hz

theorem leaf_3811_ok : checkAt 527 1000 box_3811 cert_3811 = true := by
  have h := List.all_eq_true.mp batch_76_06_ok accepted_3811 (by simp [batch_76_06_values])
  exact h
theorem leaf_3811_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3811.profileLo box_3811.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3811_ok
theorem branch_box_3811_nonnegative : ∀ j, 0 ≤ branch_box_3811.lower j ∧ 0 ≤ branch_box_3811.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3811, Box.profileLo, Box.profileHi, box_3811]
theorem leaf_3811_BranchSafe : CertificateConsequences.BranchSafe branch_box_3811 := by
  left; refine ⟨branch_box_3811_nonnegative, ?_⟩
  intro z hz; exact leaf_3811_sound hz

theorem leaf_3813_ok : checkAt 527 1000 box_3813 cert_3813 = true := by
  have h := List.all_eq_true.mp batch_76_07_ok accepted_3813 (by simp [batch_76_07_values])
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

theorem leaf_3814_ok : checkAt 527 1000 box_3814 cert_3814 = true := by
  have h := List.all_eq_true.mp batch_76_08_ok accepted_3814 (by simp [batch_76_08_values])
  exact h
theorem leaf_3814_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3814.profileLo box_3814.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3814_ok
theorem branch_box_3814_nonnegative : ∀ j, 0 ≤ branch_box_3814.lower j ∧ 0 ≤ branch_box_3814.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3814, Box.profileLo, Box.profileHi, box_3814]
theorem leaf_3814_BranchSafe : CertificateConsequences.BranchSafe branch_box_3814 := by
  left; refine ⟨branch_box_3814_nonnegative, ?_⟩
  intro z hz; exact leaf_3814_sound hz

theorem leaf_3817_ok : checkAt 527 1000 box_3817 cert_3817 = true := by
  have h := List.all_eq_true.mp batch_76_09_ok accepted_3817 (by simp [batch_76_09_values])
  exact h
theorem leaf_3817_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3817.profileLo box_3817.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3817_ok
theorem branch_box_3817_nonnegative : ∀ j, 0 ≤ branch_box_3817.lower j ∧ 0 ≤ branch_box_3817.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3817, Box.profileLo, Box.profileHi, box_3817]
theorem leaf_3817_BranchSafe : CertificateConsequences.BranchSafe branch_box_3817 := by
  left; refine ⟨branch_box_3817_nonnegative, ?_⟩
  intro z hz; exact leaf_3817_sound hz

theorem leaf_3819_ok : checkAt 527 1000 box_3819 cert_3819 = true := by
  have h := List.all_eq_true.mp batch_76_10_ok accepted_3819 (by simp [batch_76_10_values])
  exact h
theorem leaf_3819_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3819.profileLo box_3819.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3819_ok
theorem branch_box_3819_nonnegative : ∀ j, 0 ≤ branch_box_3819.lower j ∧ 0 ≤ branch_box_3819.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3819, Box.profileLo, Box.profileHi, box_3819]
theorem leaf_3819_BranchSafe : CertificateConsequences.BranchSafe branch_box_3819 := by
  left; refine ⟨branch_box_3819_nonnegative, ?_⟩
  intro z hz; exact leaf_3819_sound hz

theorem leaf_3820_ok : checkAt 527 1000 box_3820 cert_3820 = true := by
  have h := List.all_eq_true.mp batch_76_11_ok accepted_3820 (by simp [batch_76_11_values])
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

theorem leaf_3823_ok : checkAt 527 1000 box_3823 cert_3823 = true := by
  have h := List.all_eq_true.mp batch_76_12_ok accepted_3823 (by simp [batch_76_12_values])
  exact h
theorem leaf_3823_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3823.profileLo box_3823.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3823_ok
theorem branch_box_3823_nonnegative : ∀ j, 0 ≤ branch_box_3823.lower j ∧ 0 ≤ branch_box_3823.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3823, Box.profileLo, Box.profileHi, box_3823]
theorem leaf_3823_BranchSafe : CertificateConsequences.BranchSafe branch_box_3823 := by
  left; refine ⟨branch_box_3823_nonnegative, ?_⟩
  intro z hz; exact leaf_3823_sound hz

theorem leaf_3825_ok : checkAt 527 1000 box_3825 cert_3825 = true := by
  have h := List.all_eq_true.mp batch_76_13_ok accepted_3825 (by simp [batch_76_13_values])
  exact h
theorem leaf_3825_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3825.profileLo box_3825.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3825_ok
theorem branch_box_3825_nonnegative : ∀ j, 0 ≤ branch_box_3825.lower j ∧ 0 ≤ branch_box_3825.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3825, Box.profileLo, Box.profileHi, box_3825]
theorem leaf_3825_BranchSafe : CertificateConsequences.BranchSafe branch_box_3825 := by
  left; refine ⟨branch_box_3825_nonnegative, ?_⟩
  intro z hz; exact leaf_3825_sound hz

theorem leaf_3826_ok : checkAt 527 1000 box_3826 cert_3826 = true := by
  have h := List.all_eq_true.mp batch_76_14_ok accepted_3826 (by simp [batch_76_14_values])
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

theorem leaf_3827_ok : checkAt 527 1000 box_3827 cert_3827 = true := by
  have h := List.all_eq_true.mp batch_76_15_ok accepted_3827 (by simp [batch_76_15_values])
  exact h
theorem leaf_3827_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3827.profileLo box_3827.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3827_ok
theorem branch_box_3827_nonnegative : ∀ j, 0 ≤ branch_box_3827.lower j ∧ 0 ≤ branch_box_3827.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3827, Box.profileLo, Box.profileHi, box_3827]
theorem leaf_3827_BranchSafe : CertificateConsequences.BranchSafe branch_box_3827 := by
  left; refine ⟨branch_box_3827_nonnegative, ?_⟩
  intro z hz; exact leaf_3827_sound hz

theorem leaf_3829_ok : checkAt 527 1000 box_3829 cert_3829 = true := by
  have h := List.all_eq_true.mp batch_76_16_ok accepted_3829 (by simp [batch_76_16_values])
  exact h
theorem leaf_3829_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3829.profileLo box_3829.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3829_ok
theorem branch_box_3829_nonnegative : ∀ j, 0 ≤ branch_box_3829.lower j ∧ 0 ≤ branch_box_3829.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3829, Box.profileLo, Box.profileHi, box_3829]
theorem leaf_3829_BranchSafe : CertificateConsequences.BranchSafe branch_box_3829 := by
  left; refine ⟨branch_box_3829_nonnegative, ?_⟩
  intro z hz; exact leaf_3829_sound hz

theorem leaf_3830_ok : checkAt 527 1000 box_3830 cert_3830 = true := by
  have h := List.all_eq_true.mp batch_76_17_ok accepted_3830 (by simp [batch_76_17_values])
  exact h
theorem leaf_3830_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3830.profileLo box_3830.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3830_ok
theorem branch_box_3830_nonnegative : ∀ j, 0 ≤ branch_box_3830.lower j ∧ 0 ≤ branch_box_3830.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3830, Box.profileLo, Box.profileHi, box_3830]
theorem leaf_3830_BranchSafe : CertificateConsequences.BranchSafe branch_box_3830 := by
  left; refine ⟨branch_box_3830_nonnegative, ?_⟩
  intro z hz; exact leaf_3830_sound hz

theorem leaf_3843_ok : checkAt 527 1000 box_3843 cert_3843 = true := by
  have h := List.all_eq_true.mp batch_76_18_ok accepted_3843 (by simp [batch_76_18_values])
  exact h
theorem leaf_3843_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3843.profileLo box_3843.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3843_ok
theorem branch_box_3843_nonnegative : ∀ j, 0 ≤ branch_box_3843.lower j ∧ 0 ≤ branch_box_3843.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3843, Box.profileLo, Box.profileHi, box_3843]
theorem leaf_3843_BranchSafe : CertificateConsequences.BranchSafe branch_box_3843 := by
  left; refine ⟨branch_box_3843_nonnegative, ?_⟩
  intro z hz; exact leaf_3843_sound hz

theorem leaf_3845_ok : checkAt 527 1000 box_3845 cert_3845 = true := by
  have h := List.all_eq_true.mp batch_76_19_ok accepted_3845 (by simp [batch_76_19_values])
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

theorem leaf_3846_ok : checkAt 527 1000 box_3846 cert_3846 = true := by
  have h := List.all_eq_true.mp batch_76_20_ok accepted_3846 (by simp [batch_76_20_values])
  exact h
theorem leaf_3846_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3846.profileLo box_3846.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3846_ok
theorem branch_box_3846_nonnegative : ∀ j, 0 ≤ branch_box_3846.lower j ∧ 0 ≤ branch_box_3846.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3846, Box.profileLo, Box.profileHi, box_3846]
theorem leaf_3846_BranchSafe : CertificateConsequences.BranchSafe branch_box_3846 := by
  left; refine ⟨branch_box_3846_nonnegative, ?_⟩
  intro z hz; exact leaf_3846_sound hz

theorem leaf_3847_ok : checkAt 527 1000 box_3847 cert_3847 = true := by
  have h := List.all_eq_true.mp batch_76_21_ok accepted_3847 (by simp [batch_76_21_values])
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

theorem leaf_3848_ok : checkAt 527 1000 box_3848 cert_3848 = true := by
  have h := List.all_eq_true.mp batch_76_22_ok accepted_3848 (by simp [batch_76_22_values])
  exact h
theorem leaf_3848_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3848.profileLo box_3848.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3848_ok
theorem branch_box_3848_nonnegative : ∀ j, 0 ≤ branch_box_3848.lower j ∧ 0 ≤ branch_box_3848.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3848, Box.profileLo, Box.profileHi, box_3848]
theorem leaf_3848_BranchSafe : CertificateConsequences.BranchSafe branch_box_3848 := by
  left; refine ⟨branch_box_3848_nonnegative, ?_⟩
  intro z hz; exact leaf_3848_sound hz

#print axioms batch_76_00_ok
#print axioms leaf_3801_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
