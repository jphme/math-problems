import PeaceableQueens.UpperBound.Generated.Even.C527Scaled77Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_77_00_values : List Bool := [accepted_3850]
theorem batch_77_00_ok : batch_77_00_values.all id = true := by decide

def batch_77_01_values : List Bool := [accepted_3851]
theorem batch_77_01_ok : batch_77_01_values.all id = true := by decide

def batch_77_02_values : List Bool := [accepted_3852]
theorem batch_77_02_ok : batch_77_02_values.all id = true := by decide

def batch_77_03_values : List Bool := [accepted_3857]
theorem batch_77_03_ok : batch_77_03_values.all id = true := by decide

def batch_77_04_values : List Bool := [accepted_3858]
theorem batch_77_04_ok : batch_77_04_values.all id = true := by decide

def batch_77_05_values : List Bool := [accepted_3859]
theorem batch_77_05_ok : batch_77_05_values.all id = true := by decide

def batch_77_06_values : List Bool := [accepted_3860]
theorem batch_77_06_ok : batch_77_06_values.all id = true := by decide

def batch_77_07_values : List Bool := [accepted_3861]
theorem batch_77_07_ok : batch_77_07_values.all id = true := by decide

def batch_77_08_values : List Bool := [accepted_3862]
theorem batch_77_08_ok : batch_77_08_values.all id = true := by decide

def batch_77_09_values : List Bool := [accepted_3869]
theorem batch_77_09_ok : batch_77_09_values.all id = true := by decide

def batch_77_10_values : List Bool := [accepted_3872]
theorem batch_77_10_ok : batch_77_10_values.all id = true := by decide

def batch_77_11_values : List Bool := [accepted_3873]
theorem batch_77_11_ok : batch_77_11_values.all id = true := by decide

def batch_77_12_values : List Bool := [accepted_3874]
theorem batch_77_12_ok : batch_77_12_values.all id = true := by decide

def batch_77_13_values : List Bool := [accepted_3879]
theorem batch_77_13_ok : batch_77_13_values.all id = true := by decide

def batch_77_14_values : List Bool := [accepted_3880]
theorem batch_77_14_ok : batch_77_14_values.all id = true := by decide

def batch_77_15_values : List Bool := [accepted_3881]
theorem batch_77_15_ok : batch_77_15_values.all id = true := by decide

def batch_77_16_values : List Bool := [accepted_3882]
theorem batch_77_16_ok : batch_77_16_values.all id = true := by decide

def batch_77_17_values : List Bool := [accepted_3883]
theorem batch_77_17_ok : batch_77_17_values.all id = true := by decide

def batch_77_18_values : List Bool := [accepted_3885]
theorem batch_77_18_ok : batch_77_18_values.all id = true := by decide

def batch_77_19_values : List Bool := [accepted_3886]
theorem batch_77_19_ok : batch_77_19_values.all id = true := by decide

def batch_77_20_values : List Bool := [accepted_3895]
theorem batch_77_20_ok : batch_77_20_values.all id = true := by decide

def batch_77_21_values : List Bool := [accepted_3896]
theorem batch_77_21_ok : batch_77_21_values.all id = true := by decide

def batch_77_22_values : List Bool := [accepted_3897]
theorem batch_77_22_ok : batch_77_22_values.all id = true := by decide

def batch_77_23_values : List Bool := [accepted_3898]
theorem batch_77_23_ok : batch_77_23_values.all id = true := by decide

def batch_77_24_values : List Bool := [accepted_3899]
theorem batch_77_24_ok : batch_77_24_values.all id = true := by decide

theorem leaf_3850_ok : checkAt 527 1000 box_3850 cert_3850 = true := by
  have h := List.all_eq_true.mp batch_77_00_ok accepted_3850 (by simp [batch_77_00_values])
  exact h
theorem leaf_3850_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3850.profileLo box_3850.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3850_ok
theorem branch_box_3850_nonnegative : ∀ j, 0 ≤ branch_box_3850.lower j ∧ 0 ≤ branch_box_3850.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3850, Box.profileLo, Box.profileHi, box_3850]
theorem leaf_3850_BranchSafe : CertificateConsequences.BranchSafe branch_box_3850 := by
  left; refine ⟨branch_box_3850_nonnegative, ?_⟩
  intro z hz; exact leaf_3850_sound hz

theorem leaf_3851_ok : checkAt 527 1000 box_3851 cert_3851 = true := by
  have h := List.all_eq_true.mp batch_77_01_ok accepted_3851 (by simp [batch_77_01_values])
  exact h
theorem leaf_3851_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3851.profileLo box_3851.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3851_ok
theorem branch_box_3851_nonnegative : ∀ j, 0 ≤ branch_box_3851.lower j ∧ 0 ≤ branch_box_3851.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3851, Box.profileLo, Box.profileHi, box_3851]
theorem leaf_3851_BranchSafe : CertificateConsequences.BranchSafe branch_box_3851 := by
  left; refine ⟨branch_box_3851_nonnegative, ?_⟩
  intro z hz; exact leaf_3851_sound hz

theorem leaf_3852_ok : checkAt 527 1000 box_3852 cert_3852 = true := by
  have h := List.all_eq_true.mp batch_77_02_ok accepted_3852 (by simp [batch_77_02_values])
  exact h
theorem leaf_3852_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3852.profileLo box_3852.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3852_ok
theorem branch_box_3852_nonnegative : ∀ j, 0 ≤ branch_box_3852.lower j ∧ 0 ≤ branch_box_3852.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3852, Box.profileLo, Box.profileHi, box_3852]
theorem leaf_3852_BranchSafe : CertificateConsequences.BranchSafe branch_box_3852 := by
  left; refine ⟨branch_box_3852_nonnegative, ?_⟩
  intro z hz; exact leaf_3852_sound hz

theorem leaf_3857_ok : checkAt 527 1000 box_3857 cert_3857 = true := by
  have h := List.all_eq_true.mp batch_77_03_ok accepted_3857 (by simp [batch_77_03_values])
  exact h
theorem leaf_3857_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3857.profileLo box_3857.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3857_ok
theorem branch_box_3857_nonnegative : ∀ j, 0 ≤ branch_box_3857.lower j ∧ 0 ≤ branch_box_3857.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3857, Box.profileLo, Box.profileHi, box_3857]
theorem leaf_3857_BranchSafe : CertificateConsequences.BranchSafe branch_box_3857 := by
  left; refine ⟨branch_box_3857_nonnegative, ?_⟩
  intro z hz; exact leaf_3857_sound hz

theorem leaf_3858_ok : checkAt 527 1000 box_3858 cert_3858 = true := by
  have h := List.all_eq_true.mp batch_77_04_ok accepted_3858 (by simp [batch_77_04_values])
  exact h
theorem leaf_3858_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3858.profileLo box_3858.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3858_ok
theorem branch_box_3858_nonnegative : ∀ j, 0 ≤ branch_box_3858.lower j ∧ 0 ≤ branch_box_3858.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3858, Box.profileLo, Box.profileHi, box_3858]
theorem leaf_3858_BranchSafe : CertificateConsequences.BranchSafe branch_box_3858 := by
  left; refine ⟨branch_box_3858_nonnegative, ?_⟩
  intro z hz; exact leaf_3858_sound hz

theorem leaf_3859_ok : checkAt 527 1000 box_3859 cert_3859 = true := by
  have h := List.all_eq_true.mp batch_77_05_ok accepted_3859 (by simp [batch_77_05_values])
  exact h
theorem leaf_3859_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3859.profileLo box_3859.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3859_ok
theorem branch_box_3859_nonnegative : ∀ j, 0 ≤ branch_box_3859.lower j ∧ 0 ≤ branch_box_3859.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3859, Box.profileLo, Box.profileHi, box_3859]
theorem leaf_3859_BranchSafe : CertificateConsequences.BranchSafe branch_box_3859 := by
  left; refine ⟨branch_box_3859_nonnegative, ?_⟩
  intro z hz; exact leaf_3859_sound hz

theorem leaf_3860_ok : checkAt 527 1000 box_3860 cert_3860 = true := by
  have h := List.all_eq_true.mp batch_77_06_ok accepted_3860 (by simp [batch_77_06_values])
  exact h
theorem leaf_3860_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3860.profileLo box_3860.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3860_ok
theorem branch_box_3860_nonnegative : ∀ j, 0 ≤ branch_box_3860.lower j ∧ 0 ≤ branch_box_3860.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3860, Box.profileLo, Box.profileHi, box_3860]
theorem leaf_3860_BranchSafe : CertificateConsequences.BranchSafe branch_box_3860 := by
  left; refine ⟨branch_box_3860_nonnegative, ?_⟩
  intro z hz; exact leaf_3860_sound hz

theorem leaf_3861_ok : checkAt 527 1000 box_3861 cert_3861 = true := by
  have h := List.all_eq_true.mp batch_77_07_ok accepted_3861 (by simp [batch_77_07_values])
  exact h
theorem leaf_3861_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3861.profileLo box_3861.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3861_ok
theorem branch_box_3861_nonnegative : ∀ j, 0 ≤ branch_box_3861.lower j ∧ 0 ≤ branch_box_3861.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3861, Box.profileLo, Box.profileHi, box_3861]
theorem leaf_3861_BranchSafe : CertificateConsequences.BranchSafe branch_box_3861 := by
  left; refine ⟨branch_box_3861_nonnegative, ?_⟩
  intro z hz; exact leaf_3861_sound hz

theorem leaf_3862_ok : checkAt 527 1000 box_3862 cert_3862 = true := by
  have h := List.all_eq_true.mp batch_77_08_ok accepted_3862 (by simp [batch_77_08_values])
  exact h
theorem leaf_3862_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3862.profileLo box_3862.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3862_ok
theorem branch_box_3862_nonnegative : ∀ j, 0 ≤ branch_box_3862.lower j ∧ 0 ≤ branch_box_3862.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3862, Box.profileLo, Box.profileHi, box_3862]
theorem leaf_3862_BranchSafe : CertificateConsequences.BranchSafe branch_box_3862 := by
  left; refine ⟨branch_box_3862_nonnegative, ?_⟩
  intro z hz; exact leaf_3862_sound hz

theorem leaf_3869_ok : checkAt 527 1000 box_3869 cert_3869 = true := by
  have h := List.all_eq_true.mp batch_77_09_ok accepted_3869 (by simp [batch_77_09_values])
  exact h
theorem leaf_3869_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3869.profileLo box_3869.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3869_ok
theorem branch_box_3869_nonnegative : ∀ j, 0 ≤ branch_box_3869.lower j ∧ 0 ≤ branch_box_3869.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3869, Box.profileLo, Box.profileHi, box_3869]
theorem leaf_3869_BranchSafe : CertificateConsequences.BranchSafe branch_box_3869 := by
  left; refine ⟨branch_box_3869_nonnegative, ?_⟩
  intro z hz; exact leaf_3869_sound hz

theorem leaf_3872_ok : checkAt 527 1000 box_3872 cert_3872 = true := by
  have h := List.all_eq_true.mp batch_77_10_ok accepted_3872 (by simp [batch_77_10_values])
  exact h
theorem leaf_3872_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3872.profileLo box_3872.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3872_ok
theorem branch_box_3872_nonnegative : ∀ j, 0 ≤ branch_box_3872.lower j ∧ 0 ≤ branch_box_3872.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3872, Box.profileLo, Box.profileHi, box_3872]
theorem leaf_3872_BranchSafe : CertificateConsequences.BranchSafe branch_box_3872 := by
  left; refine ⟨branch_box_3872_nonnegative, ?_⟩
  intro z hz; exact leaf_3872_sound hz

theorem leaf_3873_ok : checkAt 527 1000 box_3873 cert_3873 = true := by
  have h := List.all_eq_true.mp batch_77_11_ok accepted_3873 (by simp [batch_77_11_values])
  exact h
theorem leaf_3873_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3873.profileLo box_3873.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3873_ok
theorem branch_box_3873_nonnegative : ∀ j, 0 ≤ branch_box_3873.lower j ∧ 0 ≤ branch_box_3873.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3873, Box.profileLo, Box.profileHi, box_3873]
theorem leaf_3873_BranchSafe : CertificateConsequences.BranchSafe branch_box_3873 := by
  left; refine ⟨branch_box_3873_nonnegative, ?_⟩
  intro z hz; exact leaf_3873_sound hz

theorem leaf_3874_ok : checkAt 527 1000 box_3874 cert_3874 = true := by
  have h := List.all_eq_true.mp batch_77_12_ok accepted_3874 (by simp [batch_77_12_values])
  exact h
theorem leaf_3874_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3874.profileLo box_3874.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3874_ok
theorem branch_box_3874_nonnegative : ∀ j, 0 ≤ branch_box_3874.lower j ∧ 0 ≤ branch_box_3874.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3874, Box.profileLo, Box.profileHi, box_3874]
theorem leaf_3874_BranchSafe : CertificateConsequences.BranchSafe branch_box_3874 := by
  left; refine ⟨branch_box_3874_nonnegative, ?_⟩
  intro z hz; exact leaf_3874_sound hz

theorem leaf_3879_ok : checkAt 527 1000 box_3879 cert_3879 = true := by
  have h := List.all_eq_true.mp batch_77_13_ok accepted_3879 (by simp [batch_77_13_values])
  exact h
theorem leaf_3879_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3879.profileLo box_3879.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3879_ok
theorem branch_box_3879_nonnegative : ∀ j, 0 ≤ branch_box_3879.lower j ∧ 0 ≤ branch_box_3879.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3879, Box.profileLo, Box.profileHi, box_3879]
theorem leaf_3879_BranchSafe : CertificateConsequences.BranchSafe branch_box_3879 := by
  left; refine ⟨branch_box_3879_nonnegative, ?_⟩
  intro z hz; exact leaf_3879_sound hz

theorem leaf_3880_ok : checkAt 527 1000 box_3880 cert_3880 = true := by
  have h := List.all_eq_true.mp batch_77_14_ok accepted_3880 (by simp [batch_77_14_values])
  exact h
theorem leaf_3880_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3880.profileLo box_3880.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3880_ok
theorem branch_box_3880_nonnegative : ∀ j, 0 ≤ branch_box_3880.lower j ∧ 0 ≤ branch_box_3880.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3880, Box.profileLo, Box.profileHi, box_3880]
theorem leaf_3880_BranchSafe : CertificateConsequences.BranchSafe branch_box_3880 := by
  left; refine ⟨branch_box_3880_nonnegative, ?_⟩
  intro z hz; exact leaf_3880_sound hz

theorem leaf_3881_ok : checkAt 527 1000 box_3881 cert_3881 = true := by
  have h := List.all_eq_true.mp batch_77_15_ok accepted_3881 (by simp [batch_77_15_values])
  exact h
theorem leaf_3881_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3881.profileLo box_3881.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3881_ok
theorem branch_box_3881_nonnegative : ∀ j, 0 ≤ branch_box_3881.lower j ∧ 0 ≤ branch_box_3881.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3881, Box.profileLo, Box.profileHi, box_3881]
theorem leaf_3881_BranchSafe : CertificateConsequences.BranchSafe branch_box_3881 := by
  left; refine ⟨branch_box_3881_nonnegative, ?_⟩
  intro z hz; exact leaf_3881_sound hz

theorem leaf_3882_ok : checkAt 527 1000 box_3882 cert_3882 = true := by
  have h := List.all_eq_true.mp batch_77_16_ok accepted_3882 (by simp [batch_77_16_values])
  exact h
theorem leaf_3882_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3882.profileLo box_3882.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3882_ok
theorem branch_box_3882_nonnegative : ∀ j, 0 ≤ branch_box_3882.lower j ∧ 0 ≤ branch_box_3882.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3882, Box.profileLo, Box.profileHi, box_3882]
theorem leaf_3882_BranchSafe : CertificateConsequences.BranchSafe branch_box_3882 := by
  left; refine ⟨branch_box_3882_nonnegative, ?_⟩
  intro z hz; exact leaf_3882_sound hz

theorem leaf_3883_ok : checkAt 527 1000 box_3883 cert_3883 = true := by
  have h := List.all_eq_true.mp batch_77_17_ok accepted_3883 (by simp [batch_77_17_values])
  exact h
theorem leaf_3883_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3883.profileLo box_3883.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3883_ok
theorem branch_box_3883_nonnegative : ∀ j, 0 ≤ branch_box_3883.lower j ∧ 0 ≤ branch_box_3883.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3883, Box.profileLo, Box.profileHi, box_3883]
theorem leaf_3883_BranchSafe : CertificateConsequences.BranchSafe branch_box_3883 := by
  left; refine ⟨branch_box_3883_nonnegative, ?_⟩
  intro z hz; exact leaf_3883_sound hz

theorem leaf_3885_ok : checkAt 527 1000 box_3885 cert_3885 = true := by
  have h := List.all_eq_true.mp batch_77_18_ok accepted_3885 (by simp [batch_77_18_values])
  exact h
theorem leaf_3885_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3885.profileLo box_3885.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3885_ok
theorem branch_box_3885_nonnegative : ∀ j, 0 ≤ branch_box_3885.lower j ∧ 0 ≤ branch_box_3885.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3885, Box.profileLo, Box.profileHi, box_3885]
theorem leaf_3885_BranchSafe : CertificateConsequences.BranchSafe branch_box_3885 := by
  left; refine ⟨branch_box_3885_nonnegative, ?_⟩
  intro z hz; exact leaf_3885_sound hz

theorem leaf_3886_ok : checkAt 527 1000 box_3886 cert_3886 = true := by
  have h := List.all_eq_true.mp batch_77_19_ok accepted_3886 (by simp [batch_77_19_values])
  exact h
theorem leaf_3886_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3886.profileLo box_3886.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3886_ok
theorem branch_box_3886_nonnegative : ∀ j, 0 ≤ branch_box_3886.lower j ∧ 0 ≤ branch_box_3886.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3886, Box.profileLo, Box.profileHi, box_3886]
theorem leaf_3886_BranchSafe : CertificateConsequences.BranchSafe branch_box_3886 := by
  left; refine ⟨branch_box_3886_nonnegative, ?_⟩
  intro z hz; exact leaf_3886_sound hz

theorem leaf_3895_ok : checkAt 527 1000 box_3895 cert_3895 = true := by
  have h := List.all_eq_true.mp batch_77_20_ok accepted_3895 (by simp [batch_77_20_values])
  exact h
theorem leaf_3895_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3895.profileLo box_3895.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3895_ok
theorem branch_box_3895_nonnegative : ∀ j, 0 ≤ branch_box_3895.lower j ∧ 0 ≤ branch_box_3895.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3895, Box.profileLo, Box.profileHi, box_3895]
theorem leaf_3895_BranchSafe : CertificateConsequences.BranchSafe branch_box_3895 := by
  left; refine ⟨branch_box_3895_nonnegative, ?_⟩
  intro z hz; exact leaf_3895_sound hz

theorem leaf_3896_ok : checkAt 527 1000 box_3896 cert_3896 = true := by
  have h := List.all_eq_true.mp batch_77_21_ok accepted_3896 (by simp [batch_77_21_values])
  exact h
theorem leaf_3896_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3896.profileLo box_3896.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3896_ok
theorem branch_box_3896_nonnegative : ∀ j, 0 ≤ branch_box_3896.lower j ∧ 0 ≤ branch_box_3896.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3896, Box.profileLo, Box.profileHi, box_3896]
theorem leaf_3896_BranchSafe : CertificateConsequences.BranchSafe branch_box_3896 := by
  left; refine ⟨branch_box_3896_nonnegative, ?_⟩
  intro z hz; exact leaf_3896_sound hz

theorem leaf_3897_ok : checkAt 527 1000 box_3897 cert_3897 = true := by
  have h := List.all_eq_true.mp batch_77_22_ok accepted_3897 (by simp [batch_77_22_values])
  exact h
theorem leaf_3897_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3897.profileLo box_3897.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3897_ok
theorem branch_box_3897_nonnegative : ∀ j, 0 ≤ branch_box_3897.lower j ∧ 0 ≤ branch_box_3897.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3897, Box.profileLo, Box.profileHi, box_3897]
theorem leaf_3897_BranchSafe : CertificateConsequences.BranchSafe branch_box_3897 := by
  left; refine ⟨branch_box_3897_nonnegative, ?_⟩
  intro z hz; exact leaf_3897_sound hz

theorem leaf_3898_ok : checkAt 527 1000 box_3898 cert_3898 = true := by
  have h := List.all_eq_true.mp batch_77_23_ok accepted_3898 (by simp [batch_77_23_values])
  exact h
theorem leaf_3898_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3898.profileLo box_3898.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3898_ok
theorem branch_box_3898_nonnegative : ∀ j, 0 ≤ branch_box_3898.lower j ∧ 0 ≤ branch_box_3898.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3898, Box.profileLo, Box.profileHi, box_3898]
theorem leaf_3898_BranchSafe : CertificateConsequences.BranchSafe branch_box_3898 := by
  left; refine ⟨branch_box_3898_nonnegative, ?_⟩
  intro z hz; exact leaf_3898_sound hz

theorem leaf_3899_ok : checkAt 527 1000 box_3899 cert_3899 = true := by
  have h := List.all_eq_true.mp batch_77_24_ok accepted_3899 (by simp [batch_77_24_values])
  exact h
theorem leaf_3899_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3899.profileLo box_3899.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3899_ok
theorem branch_box_3899_nonnegative : ∀ j, 0 ≤ branch_box_3899.lower j ∧ 0 ≤ branch_box_3899.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3899, Box.profileLo, Box.profileHi, box_3899]
theorem leaf_3899_BranchSafe : CertificateConsequences.BranchSafe branch_box_3899 := by
  left; refine ⟨branch_box_3899_nonnegative, ?_⟩
  intro z hz; exact leaf_3899_sound hz

#print axioms batch_77_00_ok
#print axioms leaf_3850_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
