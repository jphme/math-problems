import PeaceableQueens.UpperBound.Generated.Even.C527Scaled96Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_96_00_values : List Bool := [accepted_4800]
theorem batch_96_00_ok : batch_96_00_values.all id = true := by decide

def batch_96_01_values : List Bool := [accepted_4801]
theorem batch_96_01_ok : batch_96_01_values.all id = true := by decide

def batch_96_02_values : List Bool := [accepted_4803]
theorem batch_96_02_ok : batch_96_02_values.all id = true := by decide

def batch_96_03_values : List Bool := [accepted_4804]
theorem batch_96_03_ok : batch_96_03_values.all id = true := by decide

def batch_96_04_values : List Bool := [accepted_4805]
theorem batch_96_04_ok : batch_96_04_values.all id = true := by decide

def batch_96_05_values : List Bool := [accepted_4806]
theorem batch_96_05_ok : batch_96_05_values.all id = true := by decide

def batch_96_06_values : List Bool := [accepted_4808]
theorem batch_96_06_ok : batch_96_06_values.all id = true := by decide

def batch_96_07_values : List Bool := [accepted_4818]
theorem batch_96_07_ok : batch_96_07_values.all id = true := by decide

def batch_96_08_values : List Bool := [accepted_4819]
theorem batch_96_08_ok : batch_96_08_values.all id = true := by decide

def batch_96_09_values : List Bool := [accepted_4821]
theorem batch_96_09_ok : batch_96_09_values.all id = true := by decide

def batch_96_10_values : List Bool := [accepted_4822]
theorem batch_96_10_ok : batch_96_10_values.all id = true := by decide

def batch_96_11_values : List Bool := [accepted_4825]
theorem batch_96_11_ok : batch_96_11_values.all id = true := by decide

def batch_96_12_values : List Bool := [accepted_4826]
theorem batch_96_12_ok : batch_96_12_values.all id = true := by decide

def batch_96_13_values : List Bool := [accepted_4827]
theorem batch_96_13_ok : batch_96_13_values.all id = true := by decide

def batch_96_14_values : List Bool := [accepted_4829]
theorem batch_96_14_ok : batch_96_14_values.all id = true := by decide

def batch_96_15_values : List Bool := [accepted_4831]
theorem batch_96_15_ok : batch_96_15_values.all id = true := by decide

def batch_96_16_values : List Bool := [accepted_4835]
theorem batch_96_16_ok : batch_96_16_values.all id = true := by decide

def batch_96_17_values : List Bool := [accepted_4836]
theorem batch_96_17_ok : batch_96_17_values.all id = true := by decide

def batch_96_18_values : List Bool := [accepted_4841]
theorem batch_96_18_ok : batch_96_18_values.all id = true := by decide

def batch_96_19_values : List Bool := [accepted_4843]
theorem batch_96_19_ok : batch_96_19_values.all id = true := by decide

def batch_96_20_values : List Bool := [accepted_4844]
theorem batch_96_20_ok : batch_96_20_values.all id = true := by decide

def batch_96_21_values : List Bool := [accepted_4847]
theorem batch_96_21_ok : batch_96_21_values.all id = true := by decide

def batch_96_22_values : List Bool := [accepted_4848]
theorem batch_96_22_ok : batch_96_22_values.all id = true := by decide

theorem leaf_4800_ok : checkAt 527 1000 box_4800 cert_4800 = true := by
  have h := List.all_eq_true.mp batch_96_00_ok accepted_4800 (by simp [batch_96_00_values])
  exact h
theorem leaf_4800_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4800.profileLo box_4800.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4800_ok
theorem branch_box_4800_nonnegative : ∀ j, 0 ≤ branch_box_4800.lower j ∧ 0 ≤ branch_box_4800.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4800, Box.profileLo, Box.profileHi, box_4800]
theorem leaf_4800_BranchSafe : CertificateConsequences.BranchSafe branch_box_4800 := by
  left; refine ⟨branch_box_4800_nonnegative, ?_⟩
  intro z hz; exact leaf_4800_sound hz

theorem leaf_4801_ok : checkAt 527 1000 box_4801 cert_4801 = true := by
  have h := List.all_eq_true.mp batch_96_01_ok accepted_4801 (by simp [batch_96_01_values])
  exact h
theorem leaf_4801_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4801.profileLo box_4801.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4801_ok
theorem branch_box_4801_nonnegative : ∀ j, 0 ≤ branch_box_4801.lower j ∧ 0 ≤ branch_box_4801.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4801, Box.profileLo, Box.profileHi, box_4801]
theorem leaf_4801_BranchSafe : CertificateConsequences.BranchSafe branch_box_4801 := by
  left; refine ⟨branch_box_4801_nonnegative, ?_⟩
  intro z hz; exact leaf_4801_sound hz

theorem leaf_4803_ok : checkAt 527 1000 box_4803 cert_4803 = true := by
  have h := List.all_eq_true.mp batch_96_02_ok accepted_4803 (by simp [batch_96_02_values])
  exact h
theorem leaf_4803_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4803.profileLo box_4803.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4803_ok
theorem branch_box_4803_nonnegative : ∀ j, 0 ≤ branch_box_4803.lower j ∧ 0 ≤ branch_box_4803.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4803, Box.profileLo, Box.profileHi, box_4803]
theorem leaf_4803_BranchSafe : CertificateConsequences.BranchSafe branch_box_4803 := by
  left; refine ⟨branch_box_4803_nonnegative, ?_⟩
  intro z hz; exact leaf_4803_sound hz

theorem leaf_4804_ok : checkAt 527 1000 box_4804 cert_4804 = true := by
  have h := List.all_eq_true.mp batch_96_03_ok accepted_4804 (by simp [batch_96_03_values])
  exact h
theorem leaf_4804_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4804.profileLo box_4804.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4804_ok
theorem branch_box_4804_nonnegative : ∀ j, 0 ≤ branch_box_4804.lower j ∧ 0 ≤ branch_box_4804.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4804, Box.profileLo, Box.profileHi, box_4804]
theorem leaf_4804_BranchSafe : CertificateConsequences.BranchSafe branch_box_4804 := by
  left; refine ⟨branch_box_4804_nonnegative, ?_⟩
  intro z hz; exact leaf_4804_sound hz

theorem leaf_4805_ok : checkAt 527 1000 box_4805 cert_4805 = true := by
  have h := List.all_eq_true.mp batch_96_04_ok accepted_4805 (by simp [batch_96_04_values])
  exact h
theorem leaf_4805_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4805.profileLo box_4805.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4805_ok
theorem branch_box_4805_nonnegative : ∀ j, 0 ≤ branch_box_4805.lower j ∧ 0 ≤ branch_box_4805.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4805, Box.profileLo, Box.profileHi, box_4805]
theorem leaf_4805_BranchSafe : CertificateConsequences.BranchSafe branch_box_4805 := by
  left; refine ⟨branch_box_4805_nonnegative, ?_⟩
  intro z hz; exact leaf_4805_sound hz

theorem leaf_4806_ok : checkAt 527 1000 box_4806 cert_4806 = true := by
  have h := List.all_eq_true.mp batch_96_05_ok accepted_4806 (by simp [batch_96_05_values])
  exact h
theorem leaf_4806_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4806.profileLo box_4806.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4806_ok
theorem branch_box_4806_nonnegative : ∀ j, 0 ≤ branch_box_4806.lower j ∧ 0 ≤ branch_box_4806.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4806, Box.profileLo, Box.profileHi, box_4806]
theorem leaf_4806_BranchSafe : CertificateConsequences.BranchSafe branch_box_4806 := by
  left; refine ⟨branch_box_4806_nonnegative, ?_⟩
  intro z hz; exact leaf_4806_sound hz

theorem leaf_4808_ok : checkAt 527 1000 box_4808 cert_4808 = true := by
  have h := List.all_eq_true.mp batch_96_06_ok accepted_4808 (by simp [batch_96_06_values])
  exact h
theorem leaf_4808_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4808.profileLo box_4808.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4808_ok
theorem branch_box_4808_nonnegative : ∀ j, 0 ≤ branch_box_4808.lower j ∧ 0 ≤ branch_box_4808.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4808, Box.profileLo, Box.profileHi, box_4808]
theorem leaf_4808_BranchSafe : CertificateConsequences.BranchSafe branch_box_4808 := by
  left; refine ⟨branch_box_4808_nonnegative, ?_⟩
  intro z hz; exact leaf_4808_sound hz

theorem leaf_4818_ok : checkAt 527 1000 box_4818 cert_4818 = true := by
  have h := List.all_eq_true.mp batch_96_07_ok accepted_4818 (by simp [batch_96_07_values])
  exact h
theorem leaf_4818_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4818.profileLo box_4818.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4818_ok
theorem branch_box_4818_nonnegative : ∀ j, 0 ≤ branch_box_4818.lower j ∧ 0 ≤ branch_box_4818.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4818, Box.profileLo, Box.profileHi, box_4818]
theorem leaf_4818_BranchSafe : CertificateConsequences.BranchSafe branch_box_4818 := by
  left; refine ⟨branch_box_4818_nonnegative, ?_⟩
  intro z hz; exact leaf_4818_sound hz

theorem leaf_4819_ok : checkAt 527 1000 box_4819 cert_4819 = true := by
  have h := List.all_eq_true.mp batch_96_08_ok accepted_4819 (by simp [batch_96_08_values])
  exact h
theorem leaf_4819_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4819.profileLo box_4819.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4819_ok
theorem branch_box_4819_nonnegative : ∀ j, 0 ≤ branch_box_4819.lower j ∧ 0 ≤ branch_box_4819.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4819, Box.profileLo, Box.profileHi, box_4819]
theorem leaf_4819_BranchSafe : CertificateConsequences.BranchSafe branch_box_4819 := by
  left; refine ⟨branch_box_4819_nonnegative, ?_⟩
  intro z hz; exact leaf_4819_sound hz

theorem leaf_4821_ok : checkAt 527 1000 box_4821 cert_4821 = true := by
  have h := List.all_eq_true.mp batch_96_09_ok accepted_4821 (by simp [batch_96_09_values])
  exact h
theorem leaf_4821_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4821.profileLo box_4821.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4821_ok
theorem branch_box_4821_nonnegative : ∀ j, 0 ≤ branch_box_4821.lower j ∧ 0 ≤ branch_box_4821.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4821, Box.profileLo, Box.profileHi, box_4821]
theorem leaf_4821_BranchSafe : CertificateConsequences.BranchSafe branch_box_4821 := by
  left; refine ⟨branch_box_4821_nonnegative, ?_⟩
  intro z hz; exact leaf_4821_sound hz

theorem leaf_4822_ok : checkAt 527 1000 box_4822 cert_4822 = true := by
  have h := List.all_eq_true.mp batch_96_10_ok accepted_4822 (by simp [batch_96_10_values])
  exact h
theorem leaf_4822_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4822.profileLo box_4822.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4822_ok
theorem branch_box_4822_nonnegative : ∀ j, 0 ≤ branch_box_4822.lower j ∧ 0 ≤ branch_box_4822.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4822, Box.profileLo, Box.profileHi, box_4822]
theorem leaf_4822_BranchSafe : CertificateConsequences.BranchSafe branch_box_4822 := by
  left; refine ⟨branch_box_4822_nonnegative, ?_⟩
  intro z hz; exact leaf_4822_sound hz

theorem leaf_4825_ok : checkAt 527 1000 box_4825 cert_4825 = true := by
  have h := List.all_eq_true.mp batch_96_11_ok accepted_4825 (by simp [batch_96_11_values])
  exact h
theorem leaf_4825_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4825.profileLo box_4825.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4825_ok
theorem branch_box_4825_nonnegative : ∀ j, 0 ≤ branch_box_4825.lower j ∧ 0 ≤ branch_box_4825.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4825, Box.profileLo, Box.profileHi, box_4825]
theorem leaf_4825_BranchSafe : CertificateConsequences.BranchSafe branch_box_4825 := by
  left; refine ⟨branch_box_4825_nonnegative, ?_⟩
  intro z hz; exact leaf_4825_sound hz

theorem leaf_4826_ok : checkAt 527 1000 box_4826 cert_4826 = true := by
  have h := List.all_eq_true.mp batch_96_12_ok accepted_4826 (by simp [batch_96_12_values])
  exact h
theorem leaf_4826_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4826.profileLo box_4826.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4826_ok
theorem branch_box_4826_nonnegative : ∀ j, 0 ≤ branch_box_4826.lower j ∧ 0 ≤ branch_box_4826.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4826, Box.profileLo, Box.profileHi, box_4826]
theorem leaf_4826_BranchSafe : CertificateConsequences.BranchSafe branch_box_4826 := by
  left; refine ⟨branch_box_4826_nonnegative, ?_⟩
  intro z hz; exact leaf_4826_sound hz

theorem leaf_4827_ok : checkAt 527 1000 box_4827 cert_4827 = true := by
  have h := List.all_eq_true.mp batch_96_13_ok accepted_4827 (by simp [batch_96_13_values])
  exact h
theorem leaf_4827_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4827.profileLo box_4827.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4827_ok
theorem branch_box_4827_nonnegative : ∀ j, 0 ≤ branch_box_4827.lower j ∧ 0 ≤ branch_box_4827.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4827, Box.profileLo, Box.profileHi, box_4827]
theorem leaf_4827_BranchSafe : CertificateConsequences.BranchSafe branch_box_4827 := by
  left; refine ⟨branch_box_4827_nonnegative, ?_⟩
  intro z hz; exact leaf_4827_sound hz

theorem leaf_4829_ok : checkAt 527 1000 box_4829 cert_4829 = true := by
  have h := List.all_eq_true.mp batch_96_14_ok accepted_4829 (by simp [batch_96_14_values])
  exact h
theorem leaf_4829_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4829.profileLo box_4829.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4829_ok
theorem branch_box_4829_nonnegative : ∀ j, 0 ≤ branch_box_4829.lower j ∧ 0 ≤ branch_box_4829.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4829, Box.profileLo, Box.profileHi, box_4829]
theorem leaf_4829_BranchSafe : CertificateConsequences.BranchSafe branch_box_4829 := by
  left; refine ⟨branch_box_4829_nonnegative, ?_⟩
  intro z hz; exact leaf_4829_sound hz

theorem leaf_4831_ok : checkAt 527 1000 box_4831 cert_4831 = true := by
  have h := List.all_eq_true.mp batch_96_15_ok accepted_4831 (by simp [batch_96_15_values])
  exact h
theorem leaf_4831_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4831.profileLo box_4831.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4831_ok
theorem branch_box_4831_nonnegative : ∀ j, 0 ≤ branch_box_4831.lower j ∧ 0 ≤ branch_box_4831.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4831, Box.profileLo, Box.profileHi, box_4831]
theorem leaf_4831_BranchSafe : CertificateConsequences.BranchSafe branch_box_4831 := by
  left; refine ⟨branch_box_4831_nonnegative, ?_⟩
  intro z hz; exact leaf_4831_sound hz

theorem leaf_4835_ok : checkAt 527 1000 box_4835 cert_4835 = true := by
  have h := List.all_eq_true.mp batch_96_16_ok accepted_4835 (by simp [batch_96_16_values])
  exact h
theorem leaf_4835_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4835.profileLo box_4835.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4835_ok
theorem branch_box_4835_nonnegative : ∀ j, 0 ≤ branch_box_4835.lower j ∧ 0 ≤ branch_box_4835.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4835, Box.profileLo, Box.profileHi, box_4835]
theorem leaf_4835_BranchSafe : CertificateConsequences.BranchSafe branch_box_4835 := by
  left; refine ⟨branch_box_4835_nonnegative, ?_⟩
  intro z hz; exact leaf_4835_sound hz

theorem leaf_4836_ok : checkAt 527 1000 box_4836 cert_4836 = true := by
  have h := List.all_eq_true.mp batch_96_17_ok accepted_4836 (by simp [batch_96_17_values])
  exact h
theorem leaf_4836_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4836.profileLo box_4836.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4836_ok
theorem branch_box_4836_nonnegative : ∀ j, 0 ≤ branch_box_4836.lower j ∧ 0 ≤ branch_box_4836.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4836, Box.profileLo, Box.profileHi, box_4836]
theorem leaf_4836_BranchSafe : CertificateConsequences.BranchSafe branch_box_4836 := by
  left; refine ⟨branch_box_4836_nonnegative, ?_⟩
  intro z hz; exact leaf_4836_sound hz

theorem leaf_4841_ok : checkAt 527 1000 box_4841 cert_4841 = true := by
  have h := List.all_eq_true.mp batch_96_18_ok accepted_4841 (by simp [batch_96_18_values])
  exact h
theorem leaf_4841_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4841.profileLo box_4841.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4841_ok
theorem branch_box_4841_nonnegative : ∀ j, 0 ≤ branch_box_4841.lower j ∧ 0 ≤ branch_box_4841.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4841, Box.profileLo, Box.profileHi, box_4841]
theorem leaf_4841_BranchSafe : CertificateConsequences.BranchSafe branch_box_4841 := by
  left; refine ⟨branch_box_4841_nonnegative, ?_⟩
  intro z hz; exact leaf_4841_sound hz

theorem leaf_4843_ok : checkAt 527 1000 box_4843 cert_4843 = true := by
  have h := List.all_eq_true.mp batch_96_19_ok accepted_4843 (by simp [batch_96_19_values])
  exact h
theorem leaf_4843_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4843.profileLo box_4843.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4843_ok
theorem branch_box_4843_nonnegative : ∀ j, 0 ≤ branch_box_4843.lower j ∧ 0 ≤ branch_box_4843.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4843, Box.profileLo, Box.profileHi, box_4843]
theorem leaf_4843_BranchSafe : CertificateConsequences.BranchSafe branch_box_4843 := by
  left; refine ⟨branch_box_4843_nonnegative, ?_⟩
  intro z hz; exact leaf_4843_sound hz

theorem leaf_4844_ok : checkAt 527 1000 box_4844 cert_4844 = true := by
  have h := List.all_eq_true.mp batch_96_20_ok accepted_4844 (by simp [batch_96_20_values])
  exact h
theorem leaf_4844_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4844.profileLo box_4844.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4844_ok
theorem branch_box_4844_nonnegative : ∀ j, 0 ≤ branch_box_4844.lower j ∧ 0 ≤ branch_box_4844.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4844, Box.profileLo, Box.profileHi, box_4844]
theorem leaf_4844_BranchSafe : CertificateConsequences.BranchSafe branch_box_4844 := by
  left; refine ⟨branch_box_4844_nonnegative, ?_⟩
  intro z hz; exact leaf_4844_sound hz

theorem leaf_4847_ok : checkAt 527 1000 box_4847 cert_4847 = true := by
  have h := List.all_eq_true.mp batch_96_21_ok accepted_4847 (by simp [batch_96_21_values])
  exact h
theorem leaf_4847_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4847.profileLo box_4847.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4847_ok
theorem branch_box_4847_nonnegative : ∀ j, 0 ≤ branch_box_4847.lower j ∧ 0 ≤ branch_box_4847.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4847, Box.profileLo, Box.profileHi, box_4847]
theorem leaf_4847_BranchSafe : CertificateConsequences.BranchSafe branch_box_4847 := by
  left; refine ⟨branch_box_4847_nonnegative, ?_⟩
  intro z hz; exact leaf_4847_sound hz

theorem leaf_4848_ok : checkAt 527 1000 box_4848 cert_4848 = true := by
  have h := List.all_eq_true.mp batch_96_22_ok accepted_4848 (by simp [batch_96_22_values])
  exact h
theorem leaf_4848_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4848.profileLo box_4848.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4848_ok
theorem branch_box_4848_nonnegative : ∀ j, 0 ≤ branch_box_4848.lower j ∧ 0 ≤ branch_box_4848.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4848, Box.profileLo, Box.profileHi, box_4848]
theorem leaf_4848_BranchSafe : CertificateConsequences.BranchSafe branch_box_4848 := by
  left; refine ⟨branch_box_4848_nonnegative, ?_⟩
  intro z hz; exact leaf_4848_sound hz

#print axioms batch_96_00_ok
#print axioms leaf_4800_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
