import PeaceableQueens.UpperBound.Generated.Even.C527Scaled136Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_136_00_values : List Bool := [accepted_6800]
theorem batch_136_00_ok : batch_136_00_values.all id = true := by decide

def batch_136_01_values : List Bool := [accepted_6807]
theorem batch_136_01_ok : batch_136_01_values.all id = true := by decide

def batch_136_02_values : List Bool := [accepted_6808]
theorem batch_136_02_ok : batch_136_02_values.all id = true := by decide

def batch_136_03_values : List Bool := [accepted_6811]
theorem batch_136_03_ok : batch_136_03_values.all id = true := by decide

def batch_136_04_values : List Bool := [accepted_6812]
theorem batch_136_04_ok : batch_136_04_values.all id = true := by decide

def batch_136_05_values : List Bool := [accepted_6818]
theorem batch_136_05_ok : batch_136_05_values.all id = true := by decide

def batch_136_06_values : List Bool := [accepted_6819]
theorem batch_136_06_ok : batch_136_06_values.all id = true := by decide

def batch_136_07_values : List Bool := [accepted_6820]
theorem batch_136_07_ok : batch_136_07_values.all id = true := by decide

def batch_136_08_values : List Bool := [accepted_6823]
theorem batch_136_08_ok : batch_136_08_values.all id = true := by decide

def batch_136_09_values : List Bool := [accepted_6825]
theorem batch_136_09_ok : batch_136_09_values.all id = true := by decide

def batch_136_10_values : List Bool := [accepted_6826]
theorem batch_136_10_ok : batch_136_10_values.all id = true := by decide

def batch_136_11_values : List Bool := [accepted_6827]
theorem batch_136_11_ok : batch_136_11_values.all id = true := by decide

def batch_136_12_values : List Bool := [accepted_6828]
theorem batch_136_12_ok : batch_136_12_values.all id = true := by decide

def batch_136_13_values : List Bool := [accepted_6829]
theorem batch_136_13_ok : batch_136_13_values.all id = true := by decide

def batch_136_14_values : List Bool := [accepted_6830]
theorem batch_136_14_ok : batch_136_14_values.all id = true := by decide

def batch_136_15_values : List Bool := [accepted_6835]
theorem batch_136_15_ok : batch_136_15_values.all id = true := by decide

def batch_136_16_values : List Bool := [accepted_6837]
theorem batch_136_16_ok : batch_136_16_values.all id = true := by decide

def batch_136_17_values : List Bool := [accepted_6838]
theorem batch_136_17_ok : batch_136_17_values.all id = true := by decide

def batch_136_18_values : List Bool := [accepted_6839]
theorem batch_136_18_ok : batch_136_18_values.all id = true := by decide

def batch_136_19_values : List Bool := [accepted_6840]
theorem batch_136_19_ok : batch_136_19_values.all id = true := by decide

def batch_136_20_values : List Bool := [accepted_6843]
theorem batch_136_20_ok : batch_136_20_values.all id = true := by decide

def batch_136_21_values : List Bool := [accepted_6845]
theorem batch_136_21_ok : batch_136_21_values.all id = true := by decide

def batch_136_22_values : List Bool := [accepted_6846]
theorem batch_136_22_ok : batch_136_22_values.all id = true := by decide

def batch_136_23_values : List Bool := [accepted_6849]
theorem batch_136_23_ok : batch_136_23_values.all id = true := by decide

theorem leaf_6800_ok : checkAt 527 1000 box_6800 cert_6800 = true := by
  have h := List.all_eq_true.mp batch_136_00_ok accepted_6800 (by simp [batch_136_00_values])
  exact h
theorem leaf_6800_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6800.profileLo box_6800.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6800_ok
theorem branch_box_6800_nonnegative : ∀ j, 0 ≤ branch_box_6800.lower j ∧ 0 ≤ branch_box_6800.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6800, Box.profileLo, Box.profileHi, box_6800]
theorem leaf_6800_BranchSafe : CertificateConsequences.BranchSafe branch_box_6800 := by
  left; refine ⟨branch_box_6800_nonnegative, ?_⟩
  intro z hz; exact leaf_6800_sound hz

theorem leaf_6807_ok : checkAt 527 1000 box_6807 cert_6807 = true := by
  have h := List.all_eq_true.mp batch_136_01_ok accepted_6807 (by simp [batch_136_01_values])
  exact h
theorem leaf_6807_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6807.profileLo box_6807.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6807_ok
theorem branch_box_6807_nonnegative : ∀ j, 0 ≤ branch_box_6807.lower j ∧ 0 ≤ branch_box_6807.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6807, Box.profileLo, Box.profileHi, box_6807]
theorem leaf_6807_BranchSafe : CertificateConsequences.BranchSafe branch_box_6807 := by
  left; refine ⟨branch_box_6807_nonnegative, ?_⟩
  intro z hz; exact leaf_6807_sound hz

theorem leaf_6808_ok : checkAt 527 1000 box_6808 cert_6808 = true := by
  have h := List.all_eq_true.mp batch_136_02_ok accepted_6808 (by simp [batch_136_02_values])
  exact h
theorem leaf_6808_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6808.profileLo box_6808.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6808_ok
theorem branch_box_6808_nonnegative : ∀ j, 0 ≤ branch_box_6808.lower j ∧ 0 ≤ branch_box_6808.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6808, Box.profileLo, Box.profileHi, box_6808]
theorem leaf_6808_BranchSafe : CertificateConsequences.BranchSafe branch_box_6808 := by
  left; refine ⟨branch_box_6808_nonnegative, ?_⟩
  intro z hz; exact leaf_6808_sound hz

theorem leaf_6811_ok : checkAt 527 1000 box_6811 cert_6811 = true := by
  have h := List.all_eq_true.mp batch_136_03_ok accepted_6811 (by simp [batch_136_03_values])
  exact h
theorem leaf_6811_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6811.profileLo box_6811.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6811_ok
theorem branch_box_6811_nonnegative : ∀ j, 0 ≤ branch_box_6811.lower j ∧ 0 ≤ branch_box_6811.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6811, Box.profileLo, Box.profileHi, box_6811]
theorem leaf_6811_BranchSafe : CertificateConsequences.BranchSafe branch_box_6811 := by
  left; refine ⟨branch_box_6811_nonnegative, ?_⟩
  intro z hz; exact leaf_6811_sound hz

theorem leaf_6812_ok : checkAt 527 1000 box_6812 cert_6812 = true := by
  have h := List.all_eq_true.mp batch_136_04_ok accepted_6812 (by simp [batch_136_04_values])
  exact h
theorem leaf_6812_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6812.profileLo box_6812.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6812_ok
theorem branch_box_6812_nonnegative : ∀ j, 0 ≤ branch_box_6812.lower j ∧ 0 ≤ branch_box_6812.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6812, Box.profileLo, Box.profileHi, box_6812]
theorem leaf_6812_BranchSafe : CertificateConsequences.BranchSafe branch_box_6812 := by
  left; refine ⟨branch_box_6812_nonnegative, ?_⟩
  intro z hz; exact leaf_6812_sound hz

theorem leaf_6818_ok : checkAt 527 1000 box_6818 cert_6818 = true := by
  have h := List.all_eq_true.mp batch_136_05_ok accepted_6818 (by simp [batch_136_05_values])
  exact h
theorem leaf_6818_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6818.profileLo box_6818.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6818_ok
theorem branch_box_6818_nonnegative : ∀ j, 0 ≤ branch_box_6818.lower j ∧ 0 ≤ branch_box_6818.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6818, Box.profileLo, Box.profileHi, box_6818]
theorem leaf_6818_BranchSafe : CertificateConsequences.BranchSafe branch_box_6818 := by
  left; refine ⟨branch_box_6818_nonnegative, ?_⟩
  intro z hz; exact leaf_6818_sound hz

theorem leaf_6819_ok : checkAt 527 1000 box_6819 cert_6819 = true := by
  have h := List.all_eq_true.mp batch_136_06_ok accepted_6819 (by simp [batch_136_06_values])
  exact h
theorem leaf_6819_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6819.profileLo box_6819.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6819_ok
theorem branch_box_6819_nonnegative : ∀ j, 0 ≤ branch_box_6819.lower j ∧ 0 ≤ branch_box_6819.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6819, Box.profileLo, Box.profileHi, box_6819]
theorem leaf_6819_BranchSafe : CertificateConsequences.BranchSafe branch_box_6819 := by
  left; refine ⟨branch_box_6819_nonnegative, ?_⟩
  intro z hz; exact leaf_6819_sound hz

theorem leaf_6820_ok : checkAt 527 1000 box_6820 cert_6820 = true := by
  have h := List.all_eq_true.mp batch_136_07_ok accepted_6820 (by simp [batch_136_07_values])
  exact h
theorem leaf_6820_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6820.profileLo box_6820.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6820_ok
theorem branch_box_6820_nonnegative : ∀ j, 0 ≤ branch_box_6820.lower j ∧ 0 ≤ branch_box_6820.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6820, Box.profileLo, Box.profileHi, box_6820]
theorem leaf_6820_BranchSafe : CertificateConsequences.BranchSafe branch_box_6820 := by
  left; refine ⟨branch_box_6820_nonnegative, ?_⟩
  intro z hz; exact leaf_6820_sound hz

theorem leaf_6823_ok : checkAt 527 1000 box_6823 cert_6823 = true := by
  have h := List.all_eq_true.mp batch_136_08_ok accepted_6823 (by simp [batch_136_08_values])
  exact h
theorem leaf_6823_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6823.profileLo box_6823.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6823_ok
theorem branch_box_6823_nonnegative : ∀ j, 0 ≤ branch_box_6823.lower j ∧ 0 ≤ branch_box_6823.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6823, Box.profileLo, Box.profileHi, box_6823]
theorem leaf_6823_BranchSafe : CertificateConsequences.BranchSafe branch_box_6823 := by
  left; refine ⟨branch_box_6823_nonnegative, ?_⟩
  intro z hz; exact leaf_6823_sound hz

theorem leaf_6825_ok : checkAt 527 1000 box_6825 cert_6825 = true := by
  have h := List.all_eq_true.mp batch_136_09_ok accepted_6825 (by simp [batch_136_09_values])
  exact h
theorem leaf_6825_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6825.profileLo box_6825.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6825_ok
theorem branch_box_6825_nonnegative : ∀ j, 0 ≤ branch_box_6825.lower j ∧ 0 ≤ branch_box_6825.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6825, Box.profileLo, Box.profileHi, box_6825]
theorem leaf_6825_BranchSafe : CertificateConsequences.BranchSafe branch_box_6825 := by
  left; refine ⟨branch_box_6825_nonnegative, ?_⟩
  intro z hz; exact leaf_6825_sound hz

theorem leaf_6826_ok : checkAt 527 1000 box_6826 cert_6826 = true := by
  have h := List.all_eq_true.mp batch_136_10_ok accepted_6826 (by simp [batch_136_10_values])
  exact h
theorem leaf_6826_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6826.profileLo box_6826.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6826_ok
theorem branch_box_6826_nonnegative : ∀ j, 0 ≤ branch_box_6826.lower j ∧ 0 ≤ branch_box_6826.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6826, Box.profileLo, Box.profileHi, box_6826]
theorem leaf_6826_BranchSafe : CertificateConsequences.BranchSafe branch_box_6826 := by
  left; refine ⟨branch_box_6826_nonnegative, ?_⟩
  intro z hz; exact leaf_6826_sound hz

theorem leaf_6827_ok : checkAt 527 1000 box_6827 cert_6827 = true := by
  have h := List.all_eq_true.mp batch_136_11_ok accepted_6827 (by simp [batch_136_11_values])
  exact h
theorem leaf_6827_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6827.profileLo box_6827.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6827_ok
theorem branch_box_6827_nonnegative : ∀ j, 0 ≤ branch_box_6827.lower j ∧ 0 ≤ branch_box_6827.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6827, Box.profileLo, Box.profileHi, box_6827]
theorem leaf_6827_BranchSafe : CertificateConsequences.BranchSafe branch_box_6827 := by
  left; refine ⟨branch_box_6827_nonnegative, ?_⟩
  intro z hz; exact leaf_6827_sound hz

theorem leaf_6828_ok : checkAt 527 1000 box_6828 cert_6828 = true := by
  have h := List.all_eq_true.mp batch_136_12_ok accepted_6828 (by simp [batch_136_12_values])
  exact h
theorem leaf_6828_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6828.profileLo box_6828.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6828_ok
theorem branch_box_6828_nonnegative : ∀ j, 0 ≤ branch_box_6828.lower j ∧ 0 ≤ branch_box_6828.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6828, Box.profileLo, Box.profileHi, box_6828]
theorem leaf_6828_BranchSafe : CertificateConsequences.BranchSafe branch_box_6828 := by
  left; refine ⟨branch_box_6828_nonnegative, ?_⟩
  intro z hz; exact leaf_6828_sound hz

theorem leaf_6829_ok : checkAt 527 1000 box_6829 cert_6829 = true := by
  have h := List.all_eq_true.mp batch_136_13_ok accepted_6829 (by simp [batch_136_13_values])
  exact h
theorem leaf_6829_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6829.profileLo box_6829.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6829_ok
theorem branch_box_6829_nonnegative : ∀ j, 0 ≤ branch_box_6829.lower j ∧ 0 ≤ branch_box_6829.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6829, Box.profileLo, Box.profileHi, box_6829]
theorem leaf_6829_BranchSafe : CertificateConsequences.BranchSafe branch_box_6829 := by
  left; refine ⟨branch_box_6829_nonnegative, ?_⟩
  intro z hz; exact leaf_6829_sound hz

theorem leaf_6830_ok : checkAt 527 1000 box_6830 cert_6830 = true := by
  have h := List.all_eq_true.mp batch_136_14_ok accepted_6830 (by simp [batch_136_14_values])
  exact h
theorem leaf_6830_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6830.profileLo box_6830.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6830_ok
theorem branch_box_6830_nonnegative : ∀ j, 0 ≤ branch_box_6830.lower j ∧ 0 ≤ branch_box_6830.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6830, Box.profileLo, Box.profileHi, box_6830]
theorem leaf_6830_BranchSafe : CertificateConsequences.BranchSafe branch_box_6830 := by
  left; refine ⟨branch_box_6830_nonnegative, ?_⟩
  intro z hz; exact leaf_6830_sound hz

theorem leaf_6835_ok : checkAt 527 1000 box_6835 cert_6835 = true := by
  have h := List.all_eq_true.mp batch_136_15_ok accepted_6835 (by simp [batch_136_15_values])
  exact h
theorem leaf_6835_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6835.profileLo box_6835.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6835_ok
theorem branch_box_6835_nonnegative : ∀ j, 0 ≤ branch_box_6835.lower j ∧ 0 ≤ branch_box_6835.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6835, Box.profileLo, Box.profileHi, box_6835]
theorem leaf_6835_BranchSafe : CertificateConsequences.BranchSafe branch_box_6835 := by
  left; refine ⟨branch_box_6835_nonnegative, ?_⟩
  intro z hz; exact leaf_6835_sound hz

theorem leaf_6837_ok : checkAt 527 1000 box_6837 cert_6837 = true := by
  have h := List.all_eq_true.mp batch_136_16_ok accepted_6837 (by simp [batch_136_16_values])
  exact h
theorem leaf_6837_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6837.profileLo box_6837.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6837_ok
theorem branch_box_6837_nonnegative : ∀ j, 0 ≤ branch_box_6837.lower j ∧ 0 ≤ branch_box_6837.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6837, Box.profileLo, Box.profileHi, box_6837]
theorem leaf_6837_BranchSafe : CertificateConsequences.BranchSafe branch_box_6837 := by
  left; refine ⟨branch_box_6837_nonnegative, ?_⟩
  intro z hz; exact leaf_6837_sound hz

theorem leaf_6838_ok : checkAt 527 1000 box_6838 cert_6838 = true := by
  have h := List.all_eq_true.mp batch_136_17_ok accepted_6838 (by simp [batch_136_17_values])
  exact h
theorem leaf_6838_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6838.profileLo box_6838.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6838_ok
theorem branch_box_6838_nonnegative : ∀ j, 0 ≤ branch_box_6838.lower j ∧ 0 ≤ branch_box_6838.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6838, Box.profileLo, Box.profileHi, box_6838]
theorem leaf_6838_BranchSafe : CertificateConsequences.BranchSafe branch_box_6838 := by
  left; refine ⟨branch_box_6838_nonnegative, ?_⟩
  intro z hz; exact leaf_6838_sound hz

theorem leaf_6839_ok : checkAt 527 1000 box_6839 cert_6839 = true := by
  have h := List.all_eq_true.mp batch_136_18_ok accepted_6839 (by simp [batch_136_18_values])
  exact h
theorem leaf_6839_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6839.profileLo box_6839.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6839_ok
theorem branch_box_6839_nonnegative : ∀ j, 0 ≤ branch_box_6839.lower j ∧ 0 ≤ branch_box_6839.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6839, Box.profileLo, Box.profileHi, box_6839]
theorem leaf_6839_BranchSafe : CertificateConsequences.BranchSafe branch_box_6839 := by
  left; refine ⟨branch_box_6839_nonnegative, ?_⟩
  intro z hz; exact leaf_6839_sound hz

theorem leaf_6840_ok : checkAt 527 1000 box_6840 cert_6840 = true := by
  have h := List.all_eq_true.mp batch_136_19_ok accepted_6840 (by simp [batch_136_19_values])
  exact h
theorem leaf_6840_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6840.profileLo box_6840.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6840_ok
theorem branch_box_6840_nonnegative : ∀ j, 0 ≤ branch_box_6840.lower j ∧ 0 ≤ branch_box_6840.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6840, Box.profileLo, Box.profileHi, box_6840]
theorem leaf_6840_BranchSafe : CertificateConsequences.BranchSafe branch_box_6840 := by
  left; refine ⟨branch_box_6840_nonnegative, ?_⟩
  intro z hz; exact leaf_6840_sound hz

theorem leaf_6843_ok : checkAt 527 1000 box_6843 cert_6843 = true := by
  have h := List.all_eq_true.mp batch_136_20_ok accepted_6843 (by simp [batch_136_20_values])
  exact h
theorem leaf_6843_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6843.profileLo box_6843.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6843_ok
theorem branch_box_6843_nonnegative : ∀ j, 0 ≤ branch_box_6843.lower j ∧ 0 ≤ branch_box_6843.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6843, Box.profileLo, Box.profileHi, box_6843]
theorem leaf_6843_BranchSafe : CertificateConsequences.BranchSafe branch_box_6843 := by
  left; refine ⟨branch_box_6843_nonnegative, ?_⟩
  intro z hz; exact leaf_6843_sound hz

theorem leaf_6845_ok : checkAt 527 1000 box_6845 cert_6845 = true := by
  have h := List.all_eq_true.mp batch_136_21_ok accepted_6845 (by simp [batch_136_21_values])
  exact h
theorem leaf_6845_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6845.profileLo box_6845.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6845_ok
theorem branch_box_6845_nonnegative : ∀ j, 0 ≤ branch_box_6845.lower j ∧ 0 ≤ branch_box_6845.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6845, Box.profileLo, Box.profileHi, box_6845]
theorem leaf_6845_BranchSafe : CertificateConsequences.BranchSafe branch_box_6845 := by
  left; refine ⟨branch_box_6845_nonnegative, ?_⟩
  intro z hz; exact leaf_6845_sound hz

theorem leaf_6846_ok : checkAt 527 1000 box_6846 cert_6846 = true := by
  have h := List.all_eq_true.mp batch_136_22_ok accepted_6846 (by simp [batch_136_22_values])
  exact h
theorem leaf_6846_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6846.profileLo box_6846.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6846_ok
theorem branch_box_6846_nonnegative : ∀ j, 0 ≤ branch_box_6846.lower j ∧ 0 ≤ branch_box_6846.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6846, Box.profileLo, Box.profileHi, box_6846]
theorem leaf_6846_BranchSafe : CertificateConsequences.BranchSafe branch_box_6846 := by
  left; refine ⟨branch_box_6846_nonnegative, ?_⟩
  intro z hz; exact leaf_6846_sound hz

theorem leaf_6849_ok : checkAt 527 1000 box_6849 cert_6849 = true := by
  have h := List.all_eq_true.mp batch_136_23_ok accepted_6849 (by simp [batch_136_23_values])
  exact h
theorem leaf_6849_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6849.profileLo box_6849.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6849_ok
theorem branch_box_6849_nonnegative : ∀ j, 0 ≤ branch_box_6849.lower j ∧ 0 ≤ branch_box_6849.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6849, Box.profileLo, Box.profileHi, box_6849]
theorem leaf_6849_BranchSafe : CertificateConsequences.BranchSafe branch_box_6849 := by
  left; refine ⟨branch_box_6849_nonnegative, ?_⟩
  intro z hz; exact leaf_6849_sound hz

#print axioms batch_136_00_ok
#print axioms leaf_6800_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
