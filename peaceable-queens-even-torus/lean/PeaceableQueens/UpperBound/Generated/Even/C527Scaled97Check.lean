import PeaceableQueens.UpperBound.Generated.Even.C527Scaled97Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_97_00_values : List Bool := [accepted_4850]
theorem batch_97_00_ok : batch_97_00_values.all id = true := by decide

def batch_97_01_values : List Bool := [accepted_4851]
theorem batch_97_01_ok : batch_97_01_values.all id = true := by decide

def batch_97_02_values : List Bool := [accepted_4852]
theorem batch_97_02_ok : batch_97_02_values.all id = true := by decide

def batch_97_03_values : List Bool := [accepted_4853]
theorem batch_97_03_ok : batch_97_03_values.all id = true := by decide

def batch_97_04_values : List Bool := [accepted_4854]
theorem batch_97_04_ok : batch_97_04_values.all id = true := by decide

def batch_97_05_values : List Bool := [accepted_4860]
theorem batch_97_05_ok : batch_97_05_values.all id = true := by decide

def batch_97_06_values : List Bool := [accepted_4861]
theorem batch_97_06_ok : batch_97_06_values.all id = true := by decide

def batch_97_07_values : List Bool := [accepted_4862]
theorem batch_97_07_ok : batch_97_07_values.all id = true := by decide

def batch_97_08_values : List Bool := [accepted_4864]
theorem batch_97_08_ok : batch_97_08_values.all id = true := by decide

def batch_97_09_values : List Bool := [accepted_4865]
theorem batch_97_09_ok : batch_97_09_values.all id = true := by decide

def batch_97_10_values : List Bool := [accepted_4867]
theorem batch_97_10_ok : batch_97_10_values.all id = true := by decide

def batch_97_11_values : List Bool := [accepted_4871]
theorem batch_97_11_ok : batch_97_11_values.all id = true := by decide

def batch_97_12_values : List Bool := [accepted_4872]
theorem batch_97_12_ok : batch_97_12_values.all id = true := by decide

def batch_97_13_values : List Bool := [accepted_4873]
theorem batch_97_13_ok : batch_97_13_values.all id = true := by decide

def batch_97_14_values : List Bool := [accepted_4874]
theorem batch_97_14_ok : batch_97_14_values.all id = true := by decide

def batch_97_15_values : List Bool := [accepted_4875]
theorem batch_97_15_ok : batch_97_15_values.all id = true := by decide

def batch_97_16_values : List Bool := [accepted_4877]
theorem batch_97_16_ok : batch_97_16_values.all id = true := by decide

def batch_97_17_values : List Bool := [accepted_4878]
theorem batch_97_17_ok : batch_97_17_values.all id = true := by decide

def batch_97_18_values : List Bool := [accepted_4881]
theorem batch_97_18_ok : batch_97_18_values.all id = true := by decide

def batch_97_19_values : List Bool := [accepted_4883]
theorem batch_97_19_ok : batch_97_19_values.all id = true := by decide

def batch_97_20_values : List Bool := [accepted_4884]
theorem batch_97_20_ok : batch_97_20_values.all id = true := by decide

def batch_97_21_values : List Bool := [accepted_4885]
theorem batch_97_21_ok : batch_97_21_values.all id = true := by decide

def batch_97_22_values : List Bool := [accepted_4886]
theorem batch_97_22_ok : batch_97_22_values.all id = true := by decide

def batch_97_23_values : List Bool := [accepted_4895]
theorem batch_97_23_ok : batch_97_23_values.all id = true := by decide

def batch_97_24_values : List Bool := [accepted_4897]
theorem batch_97_24_ok : batch_97_24_values.all id = true := by decide

def batch_97_25_values : List Bool := [accepted_4898]
theorem batch_97_25_ok : batch_97_25_values.all id = true := by decide

def batch_97_26_values : List Bool := [accepted_4899]
theorem batch_97_26_ok : batch_97_26_values.all id = true := by decide

theorem leaf_4850_ok : checkAt 527 1000 box_4850 cert_4850 = true := by
  have h := List.all_eq_true.mp batch_97_00_ok accepted_4850 (by simp [batch_97_00_values])
  exact h
theorem leaf_4850_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4850.profileLo box_4850.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4850_ok
theorem branch_box_4850_nonnegative : ∀ j, 0 ≤ branch_box_4850.lower j ∧ 0 ≤ branch_box_4850.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4850, Box.profileLo, Box.profileHi, box_4850]
theorem leaf_4850_BranchSafe : CertificateConsequences.BranchSafe branch_box_4850 := by
  left; refine ⟨branch_box_4850_nonnegative, ?_⟩
  intro z hz; exact leaf_4850_sound hz

theorem leaf_4851_ok : checkAt 527 1000 box_4851 cert_4851 = true := by
  have h := List.all_eq_true.mp batch_97_01_ok accepted_4851 (by simp [batch_97_01_values])
  exact h
theorem leaf_4851_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4851.profileLo box_4851.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4851_ok
theorem branch_box_4851_nonnegative : ∀ j, 0 ≤ branch_box_4851.lower j ∧ 0 ≤ branch_box_4851.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4851, Box.profileLo, Box.profileHi, box_4851]
theorem leaf_4851_BranchSafe : CertificateConsequences.BranchSafe branch_box_4851 := by
  left; refine ⟨branch_box_4851_nonnegative, ?_⟩
  intro z hz; exact leaf_4851_sound hz

theorem leaf_4852_ok : checkAt 527 1000 box_4852 cert_4852 = true := by
  have h := List.all_eq_true.mp batch_97_02_ok accepted_4852 (by simp [batch_97_02_values])
  exact h
theorem leaf_4852_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4852.profileLo box_4852.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4852_ok
theorem branch_box_4852_nonnegative : ∀ j, 0 ≤ branch_box_4852.lower j ∧ 0 ≤ branch_box_4852.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4852, Box.profileLo, Box.profileHi, box_4852]
theorem leaf_4852_BranchSafe : CertificateConsequences.BranchSafe branch_box_4852 := by
  left; refine ⟨branch_box_4852_nonnegative, ?_⟩
  intro z hz; exact leaf_4852_sound hz

theorem leaf_4853_ok : checkAt 527 1000 box_4853 cert_4853 = true := by
  have h := List.all_eq_true.mp batch_97_03_ok accepted_4853 (by simp [batch_97_03_values])
  exact h
theorem leaf_4853_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4853.profileLo box_4853.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4853_ok
theorem branch_box_4853_nonnegative : ∀ j, 0 ≤ branch_box_4853.lower j ∧ 0 ≤ branch_box_4853.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4853, Box.profileLo, Box.profileHi, box_4853]
theorem leaf_4853_BranchSafe : CertificateConsequences.BranchSafe branch_box_4853 := by
  left; refine ⟨branch_box_4853_nonnegative, ?_⟩
  intro z hz; exact leaf_4853_sound hz

theorem leaf_4854_ok : checkAt 527 1000 box_4854 cert_4854 = true := by
  have h := List.all_eq_true.mp batch_97_04_ok accepted_4854 (by simp [batch_97_04_values])
  exact h
theorem leaf_4854_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4854.profileLo box_4854.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4854_ok
theorem branch_box_4854_nonnegative : ∀ j, 0 ≤ branch_box_4854.lower j ∧ 0 ≤ branch_box_4854.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4854, Box.profileLo, Box.profileHi, box_4854]
theorem leaf_4854_BranchSafe : CertificateConsequences.BranchSafe branch_box_4854 := by
  left; refine ⟨branch_box_4854_nonnegative, ?_⟩
  intro z hz; exact leaf_4854_sound hz

theorem leaf_4860_ok : checkAt 527 1000 box_4860 cert_4860 = true := by
  have h := List.all_eq_true.mp batch_97_05_ok accepted_4860 (by simp [batch_97_05_values])
  exact h
theorem leaf_4860_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4860.profileLo box_4860.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4860_ok
theorem branch_box_4860_nonnegative : ∀ j, 0 ≤ branch_box_4860.lower j ∧ 0 ≤ branch_box_4860.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4860, Box.profileLo, Box.profileHi, box_4860]
theorem leaf_4860_BranchSafe : CertificateConsequences.BranchSafe branch_box_4860 := by
  left; refine ⟨branch_box_4860_nonnegative, ?_⟩
  intro z hz; exact leaf_4860_sound hz

theorem leaf_4861_ok : checkAt 527 1000 box_4861 cert_4861 = true := by
  have h := List.all_eq_true.mp batch_97_06_ok accepted_4861 (by simp [batch_97_06_values])
  exact h
theorem leaf_4861_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4861.profileLo box_4861.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4861_ok
theorem branch_box_4861_nonnegative : ∀ j, 0 ≤ branch_box_4861.lower j ∧ 0 ≤ branch_box_4861.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4861, Box.profileLo, Box.profileHi, box_4861]
theorem leaf_4861_BranchSafe : CertificateConsequences.BranchSafe branch_box_4861 := by
  left; refine ⟨branch_box_4861_nonnegative, ?_⟩
  intro z hz; exact leaf_4861_sound hz

theorem leaf_4862_ok : checkAt 527 1000 box_4862 cert_4862 = true := by
  have h := List.all_eq_true.mp batch_97_07_ok accepted_4862 (by simp [batch_97_07_values])
  exact h
theorem leaf_4862_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4862.profileLo box_4862.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4862_ok
theorem branch_box_4862_nonnegative : ∀ j, 0 ≤ branch_box_4862.lower j ∧ 0 ≤ branch_box_4862.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4862, Box.profileLo, Box.profileHi, box_4862]
theorem leaf_4862_BranchSafe : CertificateConsequences.BranchSafe branch_box_4862 := by
  left; refine ⟨branch_box_4862_nonnegative, ?_⟩
  intro z hz; exact leaf_4862_sound hz

theorem leaf_4864_ok : checkAt 527 1000 box_4864 cert_4864 = true := by
  have h := List.all_eq_true.mp batch_97_08_ok accepted_4864 (by simp [batch_97_08_values])
  exact h
theorem leaf_4864_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4864.profileLo box_4864.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4864_ok
theorem branch_box_4864_nonnegative : ∀ j, 0 ≤ branch_box_4864.lower j ∧ 0 ≤ branch_box_4864.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4864, Box.profileLo, Box.profileHi, box_4864]
theorem leaf_4864_BranchSafe : CertificateConsequences.BranchSafe branch_box_4864 := by
  left; refine ⟨branch_box_4864_nonnegative, ?_⟩
  intro z hz; exact leaf_4864_sound hz

theorem leaf_4865_ok : checkAt 527 1000 box_4865 cert_4865 = true := by
  have h := List.all_eq_true.mp batch_97_09_ok accepted_4865 (by simp [batch_97_09_values])
  exact h
theorem leaf_4865_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4865.profileLo box_4865.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4865_ok
theorem branch_box_4865_nonnegative : ∀ j, 0 ≤ branch_box_4865.lower j ∧ 0 ≤ branch_box_4865.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4865, Box.profileLo, Box.profileHi, box_4865]
theorem leaf_4865_BranchSafe : CertificateConsequences.BranchSafe branch_box_4865 := by
  left; refine ⟨branch_box_4865_nonnegative, ?_⟩
  intro z hz; exact leaf_4865_sound hz

theorem leaf_4867_ok : checkAt 527 1000 box_4867 cert_4867 = true := by
  have h := List.all_eq_true.mp batch_97_10_ok accepted_4867 (by simp [batch_97_10_values])
  exact h
theorem leaf_4867_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4867.profileLo box_4867.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4867_ok
theorem branch_box_4867_nonnegative : ∀ j, 0 ≤ branch_box_4867.lower j ∧ 0 ≤ branch_box_4867.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4867, Box.profileLo, Box.profileHi, box_4867]
theorem leaf_4867_BranchSafe : CertificateConsequences.BranchSafe branch_box_4867 := by
  left; refine ⟨branch_box_4867_nonnegative, ?_⟩
  intro z hz; exact leaf_4867_sound hz

theorem leaf_4871_ok : checkAt 527 1000 box_4871 cert_4871 = true := by
  have h := List.all_eq_true.mp batch_97_11_ok accepted_4871 (by simp [batch_97_11_values])
  exact h
theorem leaf_4871_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4871.profileLo box_4871.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4871_ok
theorem branch_box_4871_nonnegative : ∀ j, 0 ≤ branch_box_4871.lower j ∧ 0 ≤ branch_box_4871.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4871, Box.profileLo, Box.profileHi, box_4871]
theorem leaf_4871_BranchSafe : CertificateConsequences.BranchSafe branch_box_4871 := by
  left; refine ⟨branch_box_4871_nonnegative, ?_⟩
  intro z hz; exact leaf_4871_sound hz

theorem leaf_4872_ok : checkAt 527 1000 box_4872 cert_4872 = true := by
  have h := List.all_eq_true.mp batch_97_12_ok accepted_4872 (by simp [batch_97_12_values])
  exact h
theorem leaf_4872_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4872.profileLo box_4872.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4872_ok
theorem branch_box_4872_nonnegative : ∀ j, 0 ≤ branch_box_4872.lower j ∧ 0 ≤ branch_box_4872.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4872, Box.profileLo, Box.profileHi, box_4872]
theorem leaf_4872_BranchSafe : CertificateConsequences.BranchSafe branch_box_4872 := by
  left; refine ⟨branch_box_4872_nonnegative, ?_⟩
  intro z hz; exact leaf_4872_sound hz

theorem leaf_4873_ok : checkAt 527 1000 box_4873 cert_4873 = true := by
  have h := List.all_eq_true.mp batch_97_13_ok accepted_4873 (by simp [batch_97_13_values])
  exact h
theorem leaf_4873_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4873.profileLo box_4873.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4873_ok
theorem branch_box_4873_nonnegative : ∀ j, 0 ≤ branch_box_4873.lower j ∧ 0 ≤ branch_box_4873.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4873, Box.profileLo, Box.profileHi, box_4873]
theorem leaf_4873_BranchSafe : CertificateConsequences.BranchSafe branch_box_4873 := by
  left; refine ⟨branch_box_4873_nonnegative, ?_⟩
  intro z hz; exact leaf_4873_sound hz

theorem leaf_4874_ok : checkAt 527 1000 box_4874 cert_4874 = true := by
  have h := List.all_eq_true.mp batch_97_14_ok accepted_4874 (by simp [batch_97_14_values])
  exact h
theorem leaf_4874_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4874.profileLo box_4874.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4874_ok
theorem branch_box_4874_nonnegative : ∀ j, 0 ≤ branch_box_4874.lower j ∧ 0 ≤ branch_box_4874.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4874, Box.profileLo, Box.profileHi, box_4874]
theorem leaf_4874_BranchSafe : CertificateConsequences.BranchSafe branch_box_4874 := by
  left; refine ⟨branch_box_4874_nonnegative, ?_⟩
  intro z hz; exact leaf_4874_sound hz

theorem leaf_4875_ok : checkAt 527 1000 box_4875 cert_4875 = true := by
  have h := List.all_eq_true.mp batch_97_15_ok accepted_4875 (by simp [batch_97_15_values])
  exact h
theorem leaf_4875_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4875.profileLo box_4875.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4875_ok
theorem branch_box_4875_nonnegative : ∀ j, 0 ≤ branch_box_4875.lower j ∧ 0 ≤ branch_box_4875.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4875, Box.profileLo, Box.profileHi, box_4875]
theorem leaf_4875_BranchSafe : CertificateConsequences.BranchSafe branch_box_4875 := by
  left; refine ⟨branch_box_4875_nonnegative, ?_⟩
  intro z hz; exact leaf_4875_sound hz

theorem leaf_4877_ok : checkAt 527 1000 box_4877 cert_4877 = true := by
  have h := List.all_eq_true.mp batch_97_16_ok accepted_4877 (by simp [batch_97_16_values])
  exact h
theorem leaf_4877_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4877.profileLo box_4877.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4877_ok
theorem branch_box_4877_nonnegative : ∀ j, 0 ≤ branch_box_4877.lower j ∧ 0 ≤ branch_box_4877.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4877, Box.profileLo, Box.profileHi, box_4877]
theorem leaf_4877_BranchSafe : CertificateConsequences.BranchSafe branch_box_4877 := by
  left; refine ⟨branch_box_4877_nonnegative, ?_⟩
  intro z hz; exact leaf_4877_sound hz

theorem leaf_4878_ok : checkAt 527 1000 box_4878 cert_4878 = true := by
  have h := List.all_eq_true.mp batch_97_17_ok accepted_4878 (by simp [batch_97_17_values])
  exact h
theorem leaf_4878_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4878.profileLo box_4878.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4878_ok
theorem branch_box_4878_nonnegative : ∀ j, 0 ≤ branch_box_4878.lower j ∧ 0 ≤ branch_box_4878.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4878, Box.profileLo, Box.profileHi, box_4878]
theorem leaf_4878_BranchSafe : CertificateConsequences.BranchSafe branch_box_4878 := by
  left; refine ⟨branch_box_4878_nonnegative, ?_⟩
  intro z hz; exact leaf_4878_sound hz

theorem leaf_4881_ok : checkAt 527 1000 box_4881 cert_4881 = true := by
  have h := List.all_eq_true.mp batch_97_18_ok accepted_4881 (by simp [batch_97_18_values])
  exact h
theorem leaf_4881_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4881.profileLo box_4881.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4881_ok
theorem branch_box_4881_nonnegative : ∀ j, 0 ≤ branch_box_4881.lower j ∧ 0 ≤ branch_box_4881.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4881, Box.profileLo, Box.profileHi, box_4881]
theorem leaf_4881_BranchSafe : CertificateConsequences.BranchSafe branch_box_4881 := by
  left; refine ⟨branch_box_4881_nonnegative, ?_⟩
  intro z hz; exact leaf_4881_sound hz

theorem leaf_4883_ok : checkAt 527 1000 box_4883 cert_4883 = true := by
  have h := List.all_eq_true.mp batch_97_19_ok accepted_4883 (by simp [batch_97_19_values])
  exact h
theorem leaf_4883_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4883.profileLo box_4883.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4883_ok
theorem branch_box_4883_nonnegative : ∀ j, 0 ≤ branch_box_4883.lower j ∧ 0 ≤ branch_box_4883.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4883, Box.profileLo, Box.profileHi, box_4883]
theorem leaf_4883_BranchSafe : CertificateConsequences.BranchSafe branch_box_4883 := by
  left; refine ⟨branch_box_4883_nonnegative, ?_⟩
  intro z hz; exact leaf_4883_sound hz

theorem leaf_4884_ok : checkAt 527 1000 box_4884 cert_4884 = true := by
  have h := List.all_eq_true.mp batch_97_20_ok accepted_4884 (by simp [batch_97_20_values])
  exact h
theorem leaf_4884_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4884.profileLo box_4884.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4884_ok
theorem branch_box_4884_nonnegative : ∀ j, 0 ≤ branch_box_4884.lower j ∧ 0 ≤ branch_box_4884.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4884, Box.profileLo, Box.profileHi, box_4884]
theorem leaf_4884_BranchSafe : CertificateConsequences.BranchSafe branch_box_4884 := by
  left; refine ⟨branch_box_4884_nonnegative, ?_⟩
  intro z hz; exact leaf_4884_sound hz

theorem leaf_4885_ok : checkAt 527 1000 box_4885 cert_4885 = true := by
  have h := List.all_eq_true.mp batch_97_21_ok accepted_4885 (by simp [batch_97_21_values])
  exact h
theorem leaf_4885_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4885.profileLo box_4885.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4885_ok
theorem branch_box_4885_nonnegative : ∀ j, 0 ≤ branch_box_4885.lower j ∧ 0 ≤ branch_box_4885.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4885, Box.profileLo, Box.profileHi, box_4885]
theorem leaf_4885_BranchSafe : CertificateConsequences.BranchSafe branch_box_4885 := by
  left; refine ⟨branch_box_4885_nonnegative, ?_⟩
  intro z hz; exact leaf_4885_sound hz

theorem leaf_4886_ok : checkAt 527 1000 box_4886 cert_4886 = true := by
  have h := List.all_eq_true.mp batch_97_22_ok accepted_4886 (by simp [batch_97_22_values])
  exact h
theorem leaf_4886_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4886.profileLo box_4886.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4886_ok
theorem branch_box_4886_nonnegative : ∀ j, 0 ≤ branch_box_4886.lower j ∧ 0 ≤ branch_box_4886.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4886, Box.profileLo, Box.profileHi, box_4886]
theorem leaf_4886_BranchSafe : CertificateConsequences.BranchSafe branch_box_4886 := by
  left; refine ⟨branch_box_4886_nonnegative, ?_⟩
  intro z hz; exact leaf_4886_sound hz

theorem leaf_4895_ok : checkAt 527 1000 box_4895 cert_4895 = true := by
  have h := List.all_eq_true.mp batch_97_23_ok accepted_4895 (by simp [batch_97_23_values])
  exact h
theorem leaf_4895_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4895.profileLo box_4895.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4895_ok
theorem branch_box_4895_nonnegative : ∀ j, 0 ≤ branch_box_4895.lower j ∧ 0 ≤ branch_box_4895.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4895, Box.profileLo, Box.profileHi, box_4895]
theorem leaf_4895_BranchSafe : CertificateConsequences.BranchSafe branch_box_4895 := by
  left; refine ⟨branch_box_4895_nonnegative, ?_⟩
  intro z hz; exact leaf_4895_sound hz

theorem leaf_4897_ok : checkAt 527 1000 box_4897 cert_4897 = true := by
  have h := List.all_eq_true.mp batch_97_24_ok accepted_4897 (by simp [batch_97_24_values])
  exact h
theorem leaf_4897_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4897.profileLo box_4897.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4897_ok
theorem branch_box_4897_nonnegative : ∀ j, 0 ≤ branch_box_4897.lower j ∧ 0 ≤ branch_box_4897.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4897, Box.profileLo, Box.profileHi, box_4897]
theorem leaf_4897_BranchSafe : CertificateConsequences.BranchSafe branch_box_4897 := by
  left; refine ⟨branch_box_4897_nonnegative, ?_⟩
  intro z hz; exact leaf_4897_sound hz

theorem leaf_4898_ok : checkAt 527 1000 box_4898 cert_4898 = true := by
  have h := List.all_eq_true.mp batch_97_25_ok accepted_4898 (by simp [batch_97_25_values])
  exact h
theorem leaf_4898_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4898.profileLo box_4898.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4898_ok
theorem branch_box_4898_nonnegative : ∀ j, 0 ≤ branch_box_4898.lower j ∧ 0 ≤ branch_box_4898.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4898, Box.profileLo, Box.profileHi, box_4898]
theorem leaf_4898_BranchSafe : CertificateConsequences.BranchSafe branch_box_4898 := by
  left; refine ⟨branch_box_4898_nonnegative, ?_⟩
  intro z hz; exact leaf_4898_sound hz

theorem leaf_4899_ok : checkAt 527 1000 box_4899 cert_4899 = true := by
  have h := List.all_eq_true.mp batch_97_26_ok accepted_4899 (by simp [batch_97_26_values])
  exact h
theorem leaf_4899_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4899.profileLo box_4899.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4899_ok
theorem branch_box_4899_nonnegative : ∀ j, 0 ≤ branch_box_4899.lower j ∧ 0 ≤ branch_box_4899.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4899, Box.profileLo, Box.profileHi, box_4899]
theorem leaf_4899_BranchSafe : CertificateConsequences.BranchSafe branch_box_4899 := by
  left; refine ⟨branch_box_4899_nonnegative, ?_⟩
  intro z hz; exact leaf_4899_sound hz

#print axioms batch_97_00_ok
#print axioms leaf_4850_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
