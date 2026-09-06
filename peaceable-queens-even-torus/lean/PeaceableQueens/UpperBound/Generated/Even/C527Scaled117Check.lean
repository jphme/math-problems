import PeaceableQueens.UpperBound.Generated.Even.C527Scaled117Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_117_00_values : List Bool := [accepted_5850]
theorem batch_117_00_ok : batch_117_00_values.all id = true := by decide

def batch_117_01_values : List Bool := [accepted_5857]
theorem batch_117_01_ok : batch_117_01_values.all id = true := by decide

def batch_117_02_values : List Bool := [accepted_5858]
theorem batch_117_02_ok : batch_117_02_values.all id = true := by decide

def batch_117_03_values : List Bool := [accepted_5860]
theorem batch_117_03_ok : batch_117_03_values.all id = true := by decide

def batch_117_04_values : List Bool := [accepted_5861]
theorem batch_117_04_ok : batch_117_04_values.all id = true := by decide

def batch_117_05_values : List Bool := [accepted_5862]
theorem batch_117_05_ok : batch_117_05_values.all id = true := by decide

def batch_117_06_values : List Bool := [accepted_5863]
theorem batch_117_06_ok : batch_117_06_values.all id = true := by decide

def batch_117_07_values : List Bool := [accepted_5865]
theorem batch_117_07_ok : batch_117_07_values.all id = true := by decide

def batch_117_08_values : List Bool := [accepted_5867]
theorem batch_117_08_ok : batch_117_08_values.all id = true := by decide

def batch_117_09_values : List Bool := [accepted_5868]
theorem batch_117_09_ok : batch_117_09_values.all id = true := by decide

def batch_117_10_values : List Bool := [accepted_5873]
theorem batch_117_10_ok : batch_117_10_values.all id = true := by decide

def batch_117_11_values : List Bool := [accepted_5876]
theorem batch_117_11_ok : batch_117_11_values.all id = true := by decide

def batch_117_12_values : List Bool := [accepted_5877]
theorem batch_117_12_ok : batch_117_12_values.all id = true := by decide

def batch_117_13_values : List Bool := [accepted_5879]
theorem batch_117_13_ok : batch_117_13_values.all id = true := by decide

def batch_117_14_values : List Bool := [accepted_5880]
theorem batch_117_14_ok : batch_117_14_values.all id = true := by decide

def batch_117_15_values : List Bool := [accepted_5883]
theorem batch_117_15_ok : batch_117_15_values.all id = true := by decide

def batch_117_16_values : List Bool := [accepted_5884]
theorem batch_117_16_ok : batch_117_16_values.all id = true := by decide

def batch_117_17_values : List Bool := [accepted_5885]
theorem batch_117_17_ok : batch_117_17_values.all id = true := by decide

def batch_117_18_values : List Bool := [accepted_5886]
theorem batch_117_18_ok : batch_117_18_values.all id = true := by decide

def batch_117_19_values : List Bool := [accepted_5891]
theorem batch_117_19_ok : batch_117_19_values.all id = true := by decide

def batch_117_20_values : List Bool := [accepted_5896]
theorem batch_117_20_ok : batch_117_20_values.all id = true := by decide

def batch_117_21_values : List Bool := [accepted_5898]
theorem batch_117_21_ok : batch_117_21_values.all id = true := by decide

def batch_117_22_values : List Bool := [accepted_5899]
theorem batch_117_22_ok : batch_117_22_values.all id = true := by decide

theorem leaf_5850_ok : checkAt 527 1000 box_5850 cert_5850 = true := by
  have h := List.all_eq_true.mp batch_117_00_ok accepted_5850 (by simp [batch_117_00_values])
  exact h
theorem leaf_5850_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5850.profileLo box_5850.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5850_ok
theorem branch_box_5850_nonnegative : ∀ j, 0 ≤ branch_box_5850.lower j ∧ 0 ≤ branch_box_5850.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5850, Box.profileLo, Box.profileHi, box_5850]
theorem leaf_5850_BranchSafe : CertificateConsequences.BranchSafe branch_box_5850 := by
  left; refine ⟨branch_box_5850_nonnegative, ?_⟩
  intro z hz; exact leaf_5850_sound hz

theorem leaf_5857_ok : checkAt 527 1000 box_5857 cert_5857 = true := by
  have h := List.all_eq_true.mp batch_117_01_ok accepted_5857 (by simp [batch_117_01_values])
  exact h
theorem leaf_5857_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5857.profileLo box_5857.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5857_ok
theorem branch_box_5857_nonnegative : ∀ j, 0 ≤ branch_box_5857.lower j ∧ 0 ≤ branch_box_5857.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5857, Box.profileLo, Box.profileHi, box_5857]
theorem leaf_5857_BranchSafe : CertificateConsequences.BranchSafe branch_box_5857 := by
  left; refine ⟨branch_box_5857_nonnegative, ?_⟩
  intro z hz; exact leaf_5857_sound hz

theorem leaf_5858_ok : checkAt 527 1000 box_5858 cert_5858 = true := by
  have h := List.all_eq_true.mp batch_117_02_ok accepted_5858 (by simp [batch_117_02_values])
  exact h
theorem leaf_5858_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5858.profileLo box_5858.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5858_ok
theorem branch_box_5858_nonnegative : ∀ j, 0 ≤ branch_box_5858.lower j ∧ 0 ≤ branch_box_5858.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5858, Box.profileLo, Box.profileHi, box_5858]
theorem leaf_5858_BranchSafe : CertificateConsequences.BranchSafe branch_box_5858 := by
  left; refine ⟨branch_box_5858_nonnegative, ?_⟩
  intro z hz; exact leaf_5858_sound hz

theorem leaf_5860_ok : checkAt 527 1000 box_5860 cert_5860 = true := by
  have h := List.all_eq_true.mp batch_117_03_ok accepted_5860 (by simp [batch_117_03_values])
  exact h
theorem leaf_5860_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5860.profileLo box_5860.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5860_ok
theorem branch_box_5860_nonnegative : ∀ j, 0 ≤ branch_box_5860.lower j ∧ 0 ≤ branch_box_5860.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5860, Box.profileLo, Box.profileHi, box_5860]
theorem leaf_5860_BranchSafe : CertificateConsequences.BranchSafe branch_box_5860 := by
  left; refine ⟨branch_box_5860_nonnegative, ?_⟩
  intro z hz; exact leaf_5860_sound hz

theorem leaf_5861_ok : checkAt 527 1000 box_5861 cert_5861 = true := by
  have h := List.all_eq_true.mp batch_117_04_ok accepted_5861 (by simp [batch_117_04_values])
  exact h
theorem leaf_5861_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5861.profileLo box_5861.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5861_ok
theorem branch_box_5861_nonnegative : ∀ j, 0 ≤ branch_box_5861.lower j ∧ 0 ≤ branch_box_5861.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5861, Box.profileLo, Box.profileHi, box_5861]
theorem leaf_5861_BranchSafe : CertificateConsequences.BranchSafe branch_box_5861 := by
  left; refine ⟨branch_box_5861_nonnegative, ?_⟩
  intro z hz; exact leaf_5861_sound hz

theorem leaf_5862_ok : checkAt 527 1000 box_5862 cert_5862 = true := by
  have h := List.all_eq_true.mp batch_117_05_ok accepted_5862 (by simp [batch_117_05_values])
  exact h
theorem leaf_5862_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5862.profileLo box_5862.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5862_ok
theorem branch_box_5862_nonnegative : ∀ j, 0 ≤ branch_box_5862.lower j ∧ 0 ≤ branch_box_5862.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5862, Box.profileLo, Box.profileHi, box_5862]
theorem leaf_5862_BranchSafe : CertificateConsequences.BranchSafe branch_box_5862 := by
  left; refine ⟨branch_box_5862_nonnegative, ?_⟩
  intro z hz; exact leaf_5862_sound hz

theorem leaf_5863_ok : checkAt 527 1000 box_5863 cert_5863 = true := by
  have h := List.all_eq_true.mp batch_117_06_ok accepted_5863 (by simp [batch_117_06_values])
  exact h
theorem leaf_5863_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5863.profileLo box_5863.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5863_ok
theorem branch_box_5863_nonnegative : ∀ j, 0 ≤ branch_box_5863.lower j ∧ 0 ≤ branch_box_5863.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5863, Box.profileLo, Box.profileHi, box_5863]
theorem leaf_5863_BranchSafe : CertificateConsequences.BranchSafe branch_box_5863 := by
  left; refine ⟨branch_box_5863_nonnegative, ?_⟩
  intro z hz; exact leaf_5863_sound hz

theorem leaf_5865_ok : checkAt 527 1000 box_5865 cert_5865 = true := by
  have h := List.all_eq_true.mp batch_117_07_ok accepted_5865 (by simp [batch_117_07_values])
  exact h
theorem leaf_5865_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5865.profileLo box_5865.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5865_ok
theorem branch_box_5865_nonnegative : ∀ j, 0 ≤ branch_box_5865.lower j ∧ 0 ≤ branch_box_5865.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5865, Box.profileLo, Box.profileHi, box_5865]
theorem leaf_5865_BranchSafe : CertificateConsequences.BranchSafe branch_box_5865 := by
  left; refine ⟨branch_box_5865_nonnegative, ?_⟩
  intro z hz; exact leaf_5865_sound hz

theorem leaf_5867_ok : checkAt 527 1000 box_5867 cert_5867 = true := by
  have h := List.all_eq_true.mp batch_117_08_ok accepted_5867 (by simp [batch_117_08_values])
  exact h
theorem leaf_5867_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5867.profileLo box_5867.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5867_ok
theorem branch_box_5867_nonnegative : ∀ j, 0 ≤ branch_box_5867.lower j ∧ 0 ≤ branch_box_5867.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5867, Box.profileLo, Box.profileHi, box_5867]
theorem leaf_5867_BranchSafe : CertificateConsequences.BranchSafe branch_box_5867 := by
  left; refine ⟨branch_box_5867_nonnegative, ?_⟩
  intro z hz; exact leaf_5867_sound hz

theorem leaf_5868_ok : checkAt 527 1000 box_5868 cert_5868 = true := by
  have h := List.all_eq_true.mp batch_117_09_ok accepted_5868 (by simp [batch_117_09_values])
  exact h
theorem leaf_5868_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5868.profileLo box_5868.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5868_ok
theorem branch_box_5868_nonnegative : ∀ j, 0 ≤ branch_box_5868.lower j ∧ 0 ≤ branch_box_5868.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5868, Box.profileLo, Box.profileHi, box_5868]
theorem leaf_5868_BranchSafe : CertificateConsequences.BranchSafe branch_box_5868 := by
  left; refine ⟨branch_box_5868_nonnegative, ?_⟩
  intro z hz; exact leaf_5868_sound hz

theorem leaf_5873_ok : checkAt 527 1000 box_5873 cert_5873 = true := by
  have h := List.all_eq_true.mp batch_117_10_ok accepted_5873 (by simp [batch_117_10_values])
  exact h
theorem leaf_5873_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5873.profileLo box_5873.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5873_ok
theorem branch_box_5873_nonnegative : ∀ j, 0 ≤ branch_box_5873.lower j ∧ 0 ≤ branch_box_5873.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5873, Box.profileLo, Box.profileHi, box_5873]
theorem leaf_5873_BranchSafe : CertificateConsequences.BranchSafe branch_box_5873 := by
  left; refine ⟨branch_box_5873_nonnegative, ?_⟩
  intro z hz; exact leaf_5873_sound hz

theorem leaf_5876_ok : checkAt 527 1000 box_5876 cert_5876 = true := by
  have h := List.all_eq_true.mp batch_117_11_ok accepted_5876 (by simp [batch_117_11_values])
  exact h
theorem leaf_5876_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5876.profileLo box_5876.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5876_ok
theorem branch_box_5876_nonnegative : ∀ j, 0 ≤ branch_box_5876.lower j ∧ 0 ≤ branch_box_5876.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5876, Box.profileLo, Box.profileHi, box_5876]
theorem leaf_5876_BranchSafe : CertificateConsequences.BranchSafe branch_box_5876 := by
  left; refine ⟨branch_box_5876_nonnegative, ?_⟩
  intro z hz; exact leaf_5876_sound hz

theorem leaf_5877_ok : checkAt 527 1000 box_5877 cert_5877 = true := by
  have h := List.all_eq_true.mp batch_117_12_ok accepted_5877 (by simp [batch_117_12_values])
  exact h
theorem leaf_5877_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5877.profileLo box_5877.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5877_ok
theorem branch_box_5877_nonnegative : ∀ j, 0 ≤ branch_box_5877.lower j ∧ 0 ≤ branch_box_5877.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5877, Box.profileLo, Box.profileHi, box_5877]
theorem leaf_5877_BranchSafe : CertificateConsequences.BranchSafe branch_box_5877 := by
  left; refine ⟨branch_box_5877_nonnegative, ?_⟩
  intro z hz; exact leaf_5877_sound hz

theorem leaf_5879_ok : checkAt 527 1000 box_5879 cert_5879 = true := by
  have h := List.all_eq_true.mp batch_117_13_ok accepted_5879 (by simp [batch_117_13_values])
  exact h
theorem leaf_5879_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5879.profileLo box_5879.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5879_ok
theorem branch_box_5879_nonnegative : ∀ j, 0 ≤ branch_box_5879.lower j ∧ 0 ≤ branch_box_5879.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5879, Box.profileLo, Box.profileHi, box_5879]
theorem leaf_5879_BranchSafe : CertificateConsequences.BranchSafe branch_box_5879 := by
  left; refine ⟨branch_box_5879_nonnegative, ?_⟩
  intro z hz; exact leaf_5879_sound hz

theorem leaf_5880_ok : checkAt 527 1000 box_5880 cert_5880 = true := by
  have h := List.all_eq_true.mp batch_117_14_ok accepted_5880 (by simp [batch_117_14_values])
  exact h
theorem leaf_5880_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5880.profileLo box_5880.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5880_ok
theorem branch_box_5880_nonnegative : ∀ j, 0 ≤ branch_box_5880.lower j ∧ 0 ≤ branch_box_5880.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5880, Box.profileLo, Box.profileHi, box_5880]
theorem leaf_5880_BranchSafe : CertificateConsequences.BranchSafe branch_box_5880 := by
  left; refine ⟨branch_box_5880_nonnegative, ?_⟩
  intro z hz; exact leaf_5880_sound hz

theorem leaf_5883_ok : checkAt 527 1000 box_5883 cert_5883 = true := by
  have h := List.all_eq_true.mp batch_117_15_ok accepted_5883 (by simp [batch_117_15_values])
  exact h
theorem leaf_5883_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5883.profileLo box_5883.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5883_ok
theorem branch_box_5883_nonnegative : ∀ j, 0 ≤ branch_box_5883.lower j ∧ 0 ≤ branch_box_5883.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5883, Box.profileLo, Box.profileHi, box_5883]
theorem leaf_5883_BranchSafe : CertificateConsequences.BranchSafe branch_box_5883 := by
  left; refine ⟨branch_box_5883_nonnegative, ?_⟩
  intro z hz; exact leaf_5883_sound hz

theorem leaf_5884_ok : checkAt 527 1000 box_5884 cert_5884 = true := by
  have h := List.all_eq_true.mp batch_117_16_ok accepted_5884 (by simp [batch_117_16_values])
  exact h
theorem leaf_5884_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5884.profileLo box_5884.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5884_ok
theorem branch_box_5884_nonnegative : ∀ j, 0 ≤ branch_box_5884.lower j ∧ 0 ≤ branch_box_5884.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5884, Box.profileLo, Box.profileHi, box_5884]
theorem leaf_5884_BranchSafe : CertificateConsequences.BranchSafe branch_box_5884 := by
  left; refine ⟨branch_box_5884_nonnegative, ?_⟩
  intro z hz; exact leaf_5884_sound hz

theorem leaf_5885_ok : checkAt 527 1000 box_5885 cert_5885 = true := by
  have h := List.all_eq_true.mp batch_117_17_ok accepted_5885 (by simp [batch_117_17_values])
  exact h
theorem leaf_5885_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5885.profileLo box_5885.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5885_ok
theorem branch_box_5885_nonnegative : ∀ j, 0 ≤ branch_box_5885.lower j ∧ 0 ≤ branch_box_5885.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5885, Box.profileLo, Box.profileHi, box_5885]
theorem leaf_5885_BranchSafe : CertificateConsequences.BranchSafe branch_box_5885 := by
  left; refine ⟨branch_box_5885_nonnegative, ?_⟩
  intro z hz; exact leaf_5885_sound hz

theorem leaf_5886_ok : checkAt 527 1000 box_5886 cert_5886 = true := by
  have h := List.all_eq_true.mp batch_117_18_ok accepted_5886 (by simp [batch_117_18_values])
  exact h
theorem leaf_5886_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5886.profileLo box_5886.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5886_ok
theorem branch_box_5886_nonnegative : ∀ j, 0 ≤ branch_box_5886.lower j ∧ 0 ≤ branch_box_5886.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5886, Box.profileLo, Box.profileHi, box_5886]
theorem leaf_5886_BranchSafe : CertificateConsequences.BranchSafe branch_box_5886 := by
  left; refine ⟨branch_box_5886_nonnegative, ?_⟩
  intro z hz; exact leaf_5886_sound hz

theorem leaf_5891_ok : checkAt 527 1000 box_5891 cert_5891 = true := by
  have h := List.all_eq_true.mp batch_117_19_ok accepted_5891 (by simp [batch_117_19_values])
  exact h
theorem leaf_5891_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5891.profileLo box_5891.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5891_ok
theorem branch_box_5891_nonnegative : ∀ j, 0 ≤ branch_box_5891.lower j ∧ 0 ≤ branch_box_5891.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5891, Box.profileLo, Box.profileHi, box_5891]
theorem leaf_5891_BranchSafe : CertificateConsequences.BranchSafe branch_box_5891 := by
  left; refine ⟨branch_box_5891_nonnegative, ?_⟩
  intro z hz; exact leaf_5891_sound hz

theorem leaf_5896_ok : checkAt 527 1000 box_5896 cert_5896 = true := by
  have h := List.all_eq_true.mp batch_117_20_ok accepted_5896 (by simp [batch_117_20_values])
  exact h
theorem leaf_5896_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5896.profileLo box_5896.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5896_ok
theorem branch_box_5896_nonnegative : ∀ j, 0 ≤ branch_box_5896.lower j ∧ 0 ≤ branch_box_5896.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5896, Box.profileLo, Box.profileHi, box_5896]
theorem leaf_5896_BranchSafe : CertificateConsequences.BranchSafe branch_box_5896 := by
  left; refine ⟨branch_box_5896_nonnegative, ?_⟩
  intro z hz; exact leaf_5896_sound hz

theorem leaf_5898_ok : checkAt 527 1000 box_5898 cert_5898 = true := by
  have h := List.all_eq_true.mp batch_117_21_ok accepted_5898 (by simp [batch_117_21_values])
  exact h
theorem leaf_5898_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5898.profileLo box_5898.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5898_ok
theorem branch_box_5898_nonnegative : ∀ j, 0 ≤ branch_box_5898.lower j ∧ 0 ≤ branch_box_5898.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5898, Box.profileLo, Box.profileHi, box_5898]
theorem leaf_5898_BranchSafe : CertificateConsequences.BranchSafe branch_box_5898 := by
  left; refine ⟨branch_box_5898_nonnegative, ?_⟩
  intro z hz; exact leaf_5898_sound hz

theorem leaf_5899_ok : checkAt 527 1000 box_5899 cert_5899 = true := by
  have h := List.all_eq_true.mp batch_117_22_ok accepted_5899 (by simp [batch_117_22_values])
  exact h
theorem leaf_5899_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5899.profileLo box_5899.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5899_ok
theorem branch_box_5899_nonnegative : ∀ j, 0 ≤ branch_box_5899.lower j ∧ 0 ≤ branch_box_5899.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5899, Box.profileLo, Box.profileHi, box_5899]
theorem leaf_5899_BranchSafe : CertificateConsequences.BranchSafe branch_box_5899 := by
  left; refine ⟨branch_box_5899_nonnegative, ?_⟩
  intro z hz; exact leaf_5899_sound hz

#print axioms batch_117_00_ok
#print axioms leaf_5850_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
