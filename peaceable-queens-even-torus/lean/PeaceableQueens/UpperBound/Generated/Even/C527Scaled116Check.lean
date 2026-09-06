import PeaceableQueens.UpperBound.Generated.Even.C527Scaled116Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_116_00_values : List Bool := [accepted_5801]
theorem batch_116_00_ok : batch_116_00_values.all id = true := by decide

def batch_116_01_values : List Bool := [accepted_5803]
theorem batch_116_01_ok : batch_116_01_values.all id = true := by decide

def batch_116_02_values : List Bool := [accepted_5804]
theorem batch_116_02_ok : batch_116_02_values.all id = true := by decide

def batch_116_03_values : List Bool := [accepted_5809]
theorem batch_116_03_ok : batch_116_03_values.all id = true := by decide

def batch_116_04_values : List Bool := [accepted_5810]
theorem batch_116_04_ok : batch_116_04_values.all id = true := by decide

def batch_116_05_values : List Bool := [accepted_5811]
theorem batch_116_05_ok : batch_116_05_values.all id = true := by decide

def batch_116_06_values : List Bool := [accepted_5812]
theorem batch_116_06_ok : batch_116_06_values.all id = true := by decide

def batch_116_07_values : List Bool := [accepted_5815]
theorem batch_116_07_ok : batch_116_07_values.all id = true := by decide

def batch_116_08_values : List Bool := [accepted_5816]
theorem batch_116_08_ok : batch_116_08_values.all id = true := by decide

def batch_116_09_values : List Bool := [accepted_5818]
theorem batch_116_09_ok : batch_116_09_values.all id = true := by decide

def batch_116_10_values : List Bool := [accepted_5821]
theorem batch_116_10_ok : batch_116_10_values.all id = true := by decide

def batch_116_11_values : List Bool := [accepted_5822]
theorem batch_116_11_ok : batch_116_11_values.all id = true := by decide

def batch_116_12_values : List Bool := [accepted_5824]
theorem batch_116_12_ok : batch_116_12_values.all id = true := by decide

def batch_116_13_values : List Bool := [accepted_5825]
theorem batch_116_13_ok : batch_116_13_values.all id = true := by decide

def batch_116_14_values : List Bool := [accepted_5826]
theorem batch_116_14_ok : batch_116_14_values.all id = true := by decide

def batch_116_15_values : List Bool := [accepted_5833]
theorem batch_116_15_ok : batch_116_15_values.all id = true := by decide

def batch_116_16_values : List Bool := [accepted_5835]
theorem batch_116_16_ok : batch_116_16_values.all id = true := by decide

def batch_116_17_values : List Bool := [accepted_5837]
theorem batch_116_17_ok : batch_116_17_values.all id = true := by decide

def batch_116_18_values : List Bool := [accepted_5838]
theorem batch_116_18_ok : batch_116_18_values.all id = true := by decide

def batch_116_19_values : List Bool := [accepted_5839]
theorem batch_116_19_ok : batch_116_19_values.all id = true := by decide

def batch_116_20_values : List Bool := [accepted_5841]
theorem batch_116_20_ok : batch_116_20_values.all id = true := by decide

def batch_116_21_values : List Bool := [accepted_5842]
theorem batch_116_21_ok : batch_116_21_values.all id = true := by decide

def batch_116_22_values : List Bool := [accepted_5843]
theorem batch_116_22_ok : batch_116_22_values.all id = true := by decide

def batch_116_23_values : List Bool := [accepted_5845]
theorem batch_116_23_ok : batch_116_23_values.all id = true := by decide

def batch_116_24_values : List Bool := [accepted_5848]
theorem batch_116_24_ok : batch_116_24_values.all id = true := by decide

def batch_116_25_values : List Bool := [accepted_5849]
theorem batch_116_25_ok : batch_116_25_values.all id = true := by decide

theorem leaf_5801_ok : checkAt 527 1000 box_5801 cert_5801 = true := by
  have h := List.all_eq_true.mp batch_116_00_ok accepted_5801 (by simp [batch_116_00_values])
  exact h
theorem leaf_5801_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5801.profileLo box_5801.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5801_ok
theorem branch_box_5801_nonnegative : ∀ j, 0 ≤ branch_box_5801.lower j ∧ 0 ≤ branch_box_5801.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5801, Box.profileLo, Box.profileHi, box_5801]
theorem leaf_5801_BranchSafe : CertificateConsequences.BranchSafe branch_box_5801 := by
  left; refine ⟨branch_box_5801_nonnegative, ?_⟩
  intro z hz; exact leaf_5801_sound hz

theorem leaf_5803_ok : checkAt 527 1000 box_5803 cert_5803 = true := by
  have h := List.all_eq_true.mp batch_116_01_ok accepted_5803 (by simp [batch_116_01_values])
  exact h
theorem leaf_5803_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5803.profileLo box_5803.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5803_ok
theorem branch_box_5803_nonnegative : ∀ j, 0 ≤ branch_box_5803.lower j ∧ 0 ≤ branch_box_5803.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5803, Box.profileLo, Box.profileHi, box_5803]
theorem leaf_5803_BranchSafe : CertificateConsequences.BranchSafe branch_box_5803 := by
  left; refine ⟨branch_box_5803_nonnegative, ?_⟩
  intro z hz; exact leaf_5803_sound hz

theorem leaf_5804_ok : checkAt 527 1000 box_5804 cert_5804 = true := by
  have h := List.all_eq_true.mp batch_116_02_ok accepted_5804 (by simp [batch_116_02_values])
  exact h
theorem leaf_5804_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5804.profileLo box_5804.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5804_ok
theorem branch_box_5804_nonnegative : ∀ j, 0 ≤ branch_box_5804.lower j ∧ 0 ≤ branch_box_5804.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5804, Box.profileLo, Box.profileHi, box_5804]
theorem leaf_5804_BranchSafe : CertificateConsequences.BranchSafe branch_box_5804 := by
  left; refine ⟨branch_box_5804_nonnegative, ?_⟩
  intro z hz; exact leaf_5804_sound hz

theorem leaf_5809_ok : checkAt 527 1000 box_5809 cert_5809 = true := by
  have h := List.all_eq_true.mp batch_116_03_ok accepted_5809 (by simp [batch_116_03_values])
  exact h
theorem leaf_5809_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5809.profileLo box_5809.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5809_ok
theorem branch_box_5809_nonnegative : ∀ j, 0 ≤ branch_box_5809.lower j ∧ 0 ≤ branch_box_5809.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5809, Box.profileLo, Box.profileHi, box_5809]
theorem leaf_5809_BranchSafe : CertificateConsequences.BranchSafe branch_box_5809 := by
  left; refine ⟨branch_box_5809_nonnegative, ?_⟩
  intro z hz; exact leaf_5809_sound hz

theorem leaf_5810_ok : checkAt 527 1000 box_5810 cert_5810 = true := by
  have h := List.all_eq_true.mp batch_116_04_ok accepted_5810 (by simp [batch_116_04_values])
  exact h
theorem leaf_5810_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5810.profileLo box_5810.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5810_ok
theorem branch_box_5810_nonnegative : ∀ j, 0 ≤ branch_box_5810.lower j ∧ 0 ≤ branch_box_5810.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5810, Box.profileLo, Box.profileHi, box_5810]
theorem leaf_5810_BranchSafe : CertificateConsequences.BranchSafe branch_box_5810 := by
  left; refine ⟨branch_box_5810_nonnegative, ?_⟩
  intro z hz; exact leaf_5810_sound hz

theorem leaf_5811_ok : checkAt 527 1000 box_5811 cert_5811 = true := by
  have h := List.all_eq_true.mp batch_116_05_ok accepted_5811 (by simp [batch_116_05_values])
  exact h
theorem leaf_5811_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5811.profileLo box_5811.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5811_ok
theorem branch_box_5811_nonnegative : ∀ j, 0 ≤ branch_box_5811.lower j ∧ 0 ≤ branch_box_5811.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5811, Box.profileLo, Box.profileHi, box_5811]
theorem leaf_5811_BranchSafe : CertificateConsequences.BranchSafe branch_box_5811 := by
  left; refine ⟨branch_box_5811_nonnegative, ?_⟩
  intro z hz; exact leaf_5811_sound hz

theorem leaf_5812_ok : checkAt 527 1000 box_5812 cert_5812 = true := by
  have h := List.all_eq_true.mp batch_116_06_ok accepted_5812 (by simp [batch_116_06_values])
  exact h
theorem leaf_5812_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5812.profileLo box_5812.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5812_ok
theorem branch_box_5812_nonnegative : ∀ j, 0 ≤ branch_box_5812.lower j ∧ 0 ≤ branch_box_5812.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5812, Box.profileLo, Box.profileHi, box_5812]
theorem leaf_5812_BranchSafe : CertificateConsequences.BranchSafe branch_box_5812 := by
  left; refine ⟨branch_box_5812_nonnegative, ?_⟩
  intro z hz; exact leaf_5812_sound hz

theorem leaf_5815_ok : checkAt 527 1000 box_5815 cert_5815 = true := by
  have h := List.all_eq_true.mp batch_116_07_ok accepted_5815 (by simp [batch_116_07_values])
  exact h
theorem leaf_5815_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5815.profileLo box_5815.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5815_ok
theorem branch_box_5815_nonnegative : ∀ j, 0 ≤ branch_box_5815.lower j ∧ 0 ≤ branch_box_5815.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5815, Box.profileLo, Box.profileHi, box_5815]
theorem leaf_5815_BranchSafe : CertificateConsequences.BranchSafe branch_box_5815 := by
  left; refine ⟨branch_box_5815_nonnegative, ?_⟩
  intro z hz; exact leaf_5815_sound hz

theorem leaf_5816_ok : checkAt 527 1000 box_5816 cert_5816 = true := by
  have h := List.all_eq_true.mp batch_116_08_ok accepted_5816 (by simp [batch_116_08_values])
  exact h
theorem leaf_5816_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5816.profileLo box_5816.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5816_ok
theorem branch_box_5816_nonnegative : ∀ j, 0 ≤ branch_box_5816.lower j ∧ 0 ≤ branch_box_5816.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5816, Box.profileLo, Box.profileHi, box_5816]
theorem leaf_5816_BranchSafe : CertificateConsequences.BranchSafe branch_box_5816 := by
  left; refine ⟨branch_box_5816_nonnegative, ?_⟩
  intro z hz; exact leaf_5816_sound hz

theorem leaf_5818_ok : checkAt 527 1000 box_5818 cert_5818 = true := by
  have h := List.all_eq_true.mp batch_116_09_ok accepted_5818 (by simp [batch_116_09_values])
  exact h
theorem leaf_5818_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5818.profileLo box_5818.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5818_ok
theorem branch_box_5818_nonnegative : ∀ j, 0 ≤ branch_box_5818.lower j ∧ 0 ≤ branch_box_5818.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5818, Box.profileLo, Box.profileHi, box_5818]
theorem leaf_5818_BranchSafe : CertificateConsequences.BranchSafe branch_box_5818 := by
  left; refine ⟨branch_box_5818_nonnegative, ?_⟩
  intro z hz; exact leaf_5818_sound hz

theorem leaf_5821_ok : checkAt 527 1000 box_5821 cert_5821 = true := by
  have h := List.all_eq_true.mp batch_116_10_ok accepted_5821 (by simp [batch_116_10_values])
  exact h
theorem leaf_5821_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5821.profileLo box_5821.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5821_ok
theorem branch_box_5821_nonnegative : ∀ j, 0 ≤ branch_box_5821.lower j ∧ 0 ≤ branch_box_5821.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5821, Box.profileLo, Box.profileHi, box_5821]
theorem leaf_5821_BranchSafe : CertificateConsequences.BranchSafe branch_box_5821 := by
  left; refine ⟨branch_box_5821_nonnegative, ?_⟩
  intro z hz; exact leaf_5821_sound hz

theorem leaf_5822_ok : checkAt 527 1000 box_5822 cert_5822 = true := by
  have h := List.all_eq_true.mp batch_116_11_ok accepted_5822 (by simp [batch_116_11_values])
  exact h
theorem leaf_5822_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5822.profileLo box_5822.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5822_ok
theorem branch_box_5822_nonnegative : ∀ j, 0 ≤ branch_box_5822.lower j ∧ 0 ≤ branch_box_5822.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5822, Box.profileLo, Box.profileHi, box_5822]
theorem leaf_5822_BranchSafe : CertificateConsequences.BranchSafe branch_box_5822 := by
  left; refine ⟨branch_box_5822_nonnegative, ?_⟩
  intro z hz; exact leaf_5822_sound hz

theorem leaf_5824_ok : checkAt 527 1000 box_5824 cert_5824 = true := by
  have h := List.all_eq_true.mp batch_116_12_ok accepted_5824 (by simp [batch_116_12_values])
  exact h
theorem leaf_5824_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5824.profileLo box_5824.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5824_ok
theorem branch_box_5824_nonnegative : ∀ j, 0 ≤ branch_box_5824.lower j ∧ 0 ≤ branch_box_5824.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5824, Box.profileLo, Box.profileHi, box_5824]
theorem leaf_5824_BranchSafe : CertificateConsequences.BranchSafe branch_box_5824 := by
  left; refine ⟨branch_box_5824_nonnegative, ?_⟩
  intro z hz; exact leaf_5824_sound hz

theorem leaf_5825_ok : checkAt 527 1000 box_5825 cert_5825 = true := by
  have h := List.all_eq_true.mp batch_116_13_ok accepted_5825 (by simp [batch_116_13_values])
  exact h
theorem leaf_5825_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5825.profileLo box_5825.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5825_ok
theorem branch_box_5825_nonnegative : ∀ j, 0 ≤ branch_box_5825.lower j ∧ 0 ≤ branch_box_5825.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5825, Box.profileLo, Box.profileHi, box_5825]
theorem leaf_5825_BranchSafe : CertificateConsequences.BranchSafe branch_box_5825 := by
  left; refine ⟨branch_box_5825_nonnegative, ?_⟩
  intro z hz; exact leaf_5825_sound hz

theorem leaf_5826_ok : checkAt 527 1000 box_5826 cert_5826 = true := by
  have h := List.all_eq_true.mp batch_116_14_ok accepted_5826 (by simp [batch_116_14_values])
  exact h
theorem leaf_5826_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5826.profileLo box_5826.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5826_ok
theorem branch_box_5826_nonnegative : ∀ j, 0 ≤ branch_box_5826.lower j ∧ 0 ≤ branch_box_5826.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5826, Box.profileLo, Box.profileHi, box_5826]
theorem leaf_5826_BranchSafe : CertificateConsequences.BranchSafe branch_box_5826 := by
  left; refine ⟨branch_box_5826_nonnegative, ?_⟩
  intro z hz; exact leaf_5826_sound hz

theorem leaf_5833_ok : checkAt 527 1000 box_5833 cert_5833 = true := by
  have h := List.all_eq_true.mp batch_116_15_ok accepted_5833 (by simp [batch_116_15_values])
  exact h
theorem leaf_5833_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5833.profileLo box_5833.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5833_ok
theorem branch_box_5833_nonnegative : ∀ j, 0 ≤ branch_box_5833.lower j ∧ 0 ≤ branch_box_5833.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5833, Box.profileLo, Box.profileHi, box_5833]
theorem leaf_5833_BranchSafe : CertificateConsequences.BranchSafe branch_box_5833 := by
  left; refine ⟨branch_box_5833_nonnegative, ?_⟩
  intro z hz; exact leaf_5833_sound hz

theorem leaf_5835_ok : checkAt 527 1000 box_5835 cert_5835 = true := by
  have h := List.all_eq_true.mp batch_116_16_ok accepted_5835 (by simp [batch_116_16_values])
  exact h
theorem leaf_5835_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5835.profileLo box_5835.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5835_ok
theorem branch_box_5835_nonnegative : ∀ j, 0 ≤ branch_box_5835.lower j ∧ 0 ≤ branch_box_5835.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5835, Box.profileLo, Box.profileHi, box_5835]
theorem leaf_5835_BranchSafe : CertificateConsequences.BranchSafe branch_box_5835 := by
  left; refine ⟨branch_box_5835_nonnegative, ?_⟩
  intro z hz; exact leaf_5835_sound hz

theorem leaf_5837_ok : checkAt 527 1000 box_5837 cert_5837 = true := by
  have h := List.all_eq_true.mp batch_116_17_ok accepted_5837 (by simp [batch_116_17_values])
  exact h
theorem leaf_5837_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5837.profileLo box_5837.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5837_ok
theorem branch_box_5837_nonnegative : ∀ j, 0 ≤ branch_box_5837.lower j ∧ 0 ≤ branch_box_5837.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5837, Box.profileLo, Box.profileHi, box_5837]
theorem leaf_5837_BranchSafe : CertificateConsequences.BranchSafe branch_box_5837 := by
  left; refine ⟨branch_box_5837_nonnegative, ?_⟩
  intro z hz; exact leaf_5837_sound hz

theorem leaf_5838_ok : checkAt 527 1000 box_5838 cert_5838 = true := by
  have h := List.all_eq_true.mp batch_116_18_ok accepted_5838 (by simp [batch_116_18_values])
  exact h
theorem leaf_5838_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5838.profileLo box_5838.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5838_ok
theorem branch_box_5838_nonnegative : ∀ j, 0 ≤ branch_box_5838.lower j ∧ 0 ≤ branch_box_5838.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5838, Box.profileLo, Box.profileHi, box_5838]
theorem leaf_5838_BranchSafe : CertificateConsequences.BranchSafe branch_box_5838 := by
  left; refine ⟨branch_box_5838_nonnegative, ?_⟩
  intro z hz; exact leaf_5838_sound hz

theorem leaf_5839_ok : checkAt 527 1000 box_5839 cert_5839 = true := by
  have h := List.all_eq_true.mp batch_116_19_ok accepted_5839 (by simp [batch_116_19_values])
  exact h
theorem leaf_5839_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5839.profileLo box_5839.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5839_ok
theorem branch_box_5839_nonnegative : ∀ j, 0 ≤ branch_box_5839.lower j ∧ 0 ≤ branch_box_5839.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5839, Box.profileLo, Box.profileHi, box_5839]
theorem leaf_5839_BranchSafe : CertificateConsequences.BranchSafe branch_box_5839 := by
  left; refine ⟨branch_box_5839_nonnegative, ?_⟩
  intro z hz; exact leaf_5839_sound hz

theorem leaf_5841_ok : checkAt 527 1000 box_5841 cert_5841 = true := by
  have h := List.all_eq_true.mp batch_116_20_ok accepted_5841 (by simp [batch_116_20_values])
  exact h
theorem leaf_5841_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5841.profileLo box_5841.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5841_ok
theorem branch_box_5841_nonnegative : ∀ j, 0 ≤ branch_box_5841.lower j ∧ 0 ≤ branch_box_5841.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5841, Box.profileLo, Box.profileHi, box_5841]
theorem leaf_5841_BranchSafe : CertificateConsequences.BranchSafe branch_box_5841 := by
  left; refine ⟨branch_box_5841_nonnegative, ?_⟩
  intro z hz; exact leaf_5841_sound hz

theorem leaf_5842_ok : checkAt 527 1000 box_5842 cert_5842 = true := by
  have h := List.all_eq_true.mp batch_116_21_ok accepted_5842 (by simp [batch_116_21_values])
  exact h
theorem leaf_5842_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5842.profileLo box_5842.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5842_ok
theorem branch_box_5842_nonnegative : ∀ j, 0 ≤ branch_box_5842.lower j ∧ 0 ≤ branch_box_5842.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5842, Box.profileLo, Box.profileHi, box_5842]
theorem leaf_5842_BranchSafe : CertificateConsequences.BranchSafe branch_box_5842 := by
  left; refine ⟨branch_box_5842_nonnegative, ?_⟩
  intro z hz; exact leaf_5842_sound hz

theorem leaf_5843_ok : checkAt 527 1000 box_5843 cert_5843 = true := by
  have h := List.all_eq_true.mp batch_116_22_ok accepted_5843 (by simp [batch_116_22_values])
  exact h
theorem leaf_5843_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5843.profileLo box_5843.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5843_ok
theorem branch_box_5843_nonnegative : ∀ j, 0 ≤ branch_box_5843.lower j ∧ 0 ≤ branch_box_5843.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5843, Box.profileLo, Box.profileHi, box_5843]
theorem leaf_5843_BranchSafe : CertificateConsequences.BranchSafe branch_box_5843 := by
  left; refine ⟨branch_box_5843_nonnegative, ?_⟩
  intro z hz; exact leaf_5843_sound hz

theorem leaf_5845_ok : checkAt 527 1000 box_5845 cert_5845 = true := by
  have h := List.all_eq_true.mp batch_116_23_ok accepted_5845 (by simp [batch_116_23_values])
  exact h
theorem leaf_5845_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5845.profileLo box_5845.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5845_ok
theorem branch_box_5845_nonnegative : ∀ j, 0 ≤ branch_box_5845.lower j ∧ 0 ≤ branch_box_5845.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5845, Box.profileLo, Box.profileHi, box_5845]
theorem leaf_5845_BranchSafe : CertificateConsequences.BranchSafe branch_box_5845 := by
  left; refine ⟨branch_box_5845_nonnegative, ?_⟩
  intro z hz; exact leaf_5845_sound hz

theorem leaf_5848_ok : checkAt 527 1000 box_5848 cert_5848 = true := by
  have h := List.all_eq_true.mp batch_116_24_ok accepted_5848 (by simp [batch_116_24_values])
  exact h
theorem leaf_5848_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5848.profileLo box_5848.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5848_ok
theorem branch_box_5848_nonnegative : ∀ j, 0 ≤ branch_box_5848.lower j ∧ 0 ≤ branch_box_5848.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5848, Box.profileLo, Box.profileHi, box_5848]
theorem leaf_5848_BranchSafe : CertificateConsequences.BranchSafe branch_box_5848 := by
  left; refine ⟨branch_box_5848_nonnegative, ?_⟩
  intro z hz; exact leaf_5848_sound hz

theorem leaf_5849_ok : checkAt 527 1000 box_5849 cert_5849 = true := by
  have h := List.all_eq_true.mp batch_116_25_ok accepted_5849 (by simp [batch_116_25_values])
  exact h
theorem leaf_5849_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5849.profileLo box_5849.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5849_ok
theorem branch_box_5849_nonnegative : ∀ j, 0 ≤ branch_box_5849.lower j ∧ 0 ≤ branch_box_5849.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5849, Box.profileLo, Box.profileHi, box_5849]
theorem leaf_5849_BranchSafe : CertificateConsequences.BranchSafe branch_box_5849 := by
  left; refine ⟨branch_box_5849_nonnegative, ?_⟩
  intro z hz; exact leaf_5849_sound hz

#print axioms batch_116_00_ok
#print axioms leaf_5801_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
