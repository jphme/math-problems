import PeaceableQueens.UpperBound.Generated.Even.C527Scaled80Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_80_00_values : List Bool := [accepted_4000]
theorem batch_80_00_ok : batch_80_00_values.all id = true := by decide

def batch_80_01_values : List Bool := [accepted_4001]
theorem batch_80_01_ok : batch_80_01_values.all id = true := by decide

def batch_80_02_values : List Bool := [accepted_4003]
theorem batch_80_02_ok : batch_80_02_values.all id = true := by decide

def batch_80_03_values : List Bool := [accepted_4006]
theorem batch_80_03_ok : batch_80_03_values.all id = true := by decide

def batch_80_04_values : List Bool := [accepted_4007]
theorem batch_80_04_ok : batch_80_04_values.all id = true := by decide

def batch_80_05_values : List Bool := [accepted_4010]
theorem batch_80_05_ok : batch_80_05_values.all id = true := by decide

def batch_80_06_values : List Bool := [accepted_4012]
theorem batch_80_06_ok : batch_80_06_values.all id = true := by decide

def batch_80_07_values : List Bool := [accepted_4014]
theorem batch_80_07_ok : batch_80_07_values.all id = true := by decide

def batch_80_08_values : List Bool := [accepted_4016]
theorem batch_80_08_ok : batch_80_08_values.all id = true := by decide

def batch_80_09_values : List Bool := [accepted_4019]
theorem batch_80_09_ok : batch_80_09_values.all id = true := by decide

def batch_80_10_values : List Bool := [accepted_4022]
theorem batch_80_10_ok : batch_80_10_values.all id = true := by decide

def batch_80_11_values : List Bool := [accepted_4023]
theorem batch_80_11_ok : batch_80_11_values.all id = true := by decide

def batch_80_12_values : List Bool := [accepted_4026]
theorem batch_80_12_ok : batch_80_12_values.all id = true := by decide

def batch_80_13_values : List Bool := [accepted_4028]
theorem batch_80_13_ok : batch_80_13_values.all id = true := by decide

def batch_80_14_values : List Bool := [accepted_4029]
theorem batch_80_14_ok : batch_80_14_values.all id = true := by decide

def batch_80_15_values : List Bool := [accepted_4030]
theorem batch_80_15_ok : batch_80_15_values.all id = true := by decide

def batch_80_16_values : List Bool := [accepted_4033]
theorem batch_80_16_ok : batch_80_16_values.all id = true := by decide

def batch_80_17_values : List Bool := [accepted_4036]
theorem batch_80_17_ok : batch_80_17_values.all id = true := by decide

def batch_80_18_values : List Bool := [accepted_4038]
theorem batch_80_18_ok : batch_80_18_values.all id = true := by decide

def batch_80_19_values : List Bool := [accepted_4041]
theorem batch_80_19_ok : batch_80_19_values.all id = true := by decide

def batch_80_20_values : List Bool := [accepted_4044]
theorem batch_80_20_ok : batch_80_20_values.all id = true := by decide

def batch_80_21_values : List Bool := [accepted_4046]
theorem batch_80_21_ok : batch_80_21_values.all id = true := by decide

def batch_80_22_values : List Bool := [accepted_4047]
theorem batch_80_22_ok : batch_80_22_values.all id = true := by decide

theorem leaf_4000_ok : checkAt 527 1000 box_4000 cert_4000 = true := by
  have h := List.all_eq_true.mp batch_80_00_ok accepted_4000 (by simp [batch_80_00_values])
  exact h
theorem leaf_4000_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4000.profileLo box_4000.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4000_ok
theorem branch_box_4000_nonnegative : ∀ j, 0 ≤ branch_box_4000.lower j ∧ 0 ≤ branch_box_4000.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4000, Box.profileLo, Box.profileHi, box_4000]
theorem leaf_4000_BranchSafe : CertificateConsequences.BranchSafe branch_box_4000 := by
  left; refine ⟨branch_box_4000_nonnegative, ?_⟩
  intro z hz; exact leaf_4000_sound hz

theorem leaf_4001_ok : checkAt 527 1000 box_4001 cert_4001 = true := by
  have h := List.all_eq_true.mp batch_80_01_ok accepted_4001 (by simp [batch_80_01_values])
  exact h
theorem leaf_4001_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4001.profileLo box_4001.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4001_ok
theorem branch_box_4001_nonnegative : ∀ j, 0 ≤ branch_box_4001.lower j ∧ 0 ≤ branch_box_4001.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4001, Box.profileLo, Box.profileHi, box_4001]
theorem leaf_4001_BranchSafe : CertificateConsequences.BranchSafe branch_box_4001 := by
  left; refine ⟨branch_box_4001_nonnegative, ?_⟩
  intro z hz; exact leaf_4001_sound hz

theorem leaf_4003_ok : checkAt 527 1000 box_4003 cert_4003 = true := by
  have h := List.all_eq_true.mp batch_80_02_ok accepted_4003 (by simp [batch_80_02_values])
  exact h
theorem leaf_4003_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4003.profileLo box_4003.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4003_ok
theorem branch_box_4003_nonnegative : ∀ j, 0 ≤ branch_box_4003.lower j ∧ 0 ≤ branch_box_4003.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4003, Box.profileLo, Box.profileHi, box_4003]
theorem leaf_4003_BranchSafe : CertificateConsequences.BranchSafe branch_box_4003 := by
  left; refine ⟨branch_box_4003_nonnegative, ?_⟩
  intro z hz; exact leaf_4003_sound hz

theorem leaf_4006_ok : checkAt 527 1000 box_4006 cert_4006 = true := by
  have h := List.all_eq_true.mp batch_80_03_ok accepted_4006 (by simp [batch_80_03_values])
  exact h
theorem leaf_4006_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4006.profileLo box_4006.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4006_ok
theorem branch_box_4006_nonnegative : ∀ j, 0 ≤ branch_box_4006.lower j ∧ 0 ≤ branch_box_4006.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4006, Box.profileLo, Box.profileHi, box_4006]
theorem leaf_4006_BranchSafe : CertificateConsequences.BranchSafe branch_box_4006 := by
  left; refine ⟨branch_box_4006_nonnegative, ?_⟩
  intro z hz; exact leaf_4006_sound hz

theorem leaf_4007_ok : checkAt 527 1000 box_4007 cert_4007 = true := by
  have h := List.all_eq_true.mp batch_80_04_ok accepted_4007 (by simp [batch_80_04_values])
  exact h
theorem leaf_4007_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4007.profileLo box_4007.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4007_ok
theorem branch_box_4007_nonnegative : ∀ j, 0 ≤ branch_box_4007.lower j ∧ 0 ≤ branch_box_4007.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4007, Box.profileLo, Box.profileHi, box_4007]
theorem leaf_4007_BranchSafe : CertificateConsequences.BranchSafe branch_box_4007 := by
  left; refine ⟨branch_box_4007_nonnegative, ?_⟩
  intro z hz; exact leaf_4007_sound hz

theorem leaf_4010_ok : checkAt 527 1000 box_4010 cert_4010 = true := by
  have h := List.all_eq_true.mp batch_80_05_ok accepted_4010 (by simp [batch_80_05_values])
  exact h
theorem leaf_4010_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4010.profileLo box_4010.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4010_ok
theorem branch_box_4010_nonnegative : ∀ j, 0 ≤ branch_box_4010.lower j ∧ 0 ≤ branch_box_4010.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4010, Box.profileLo, Box.profileHi, box_4010]
theorem leaf_4010_BranchSafe : CertificateConsequences.BranchSafe branch_box_4010 := by
  left; refine ⟨branch_box_4010_nonnegative, ?_⟩
  intro z hz; exact leaf_4010_sound hz

theorem leaf_4012_ok : checkAt 527 1000 box_4012 cert_4012 = true := by
  have h := List.all_eq_true.mp batch_80_06_ok accepted_4012 (by simp [batch_80_06_values])
  exact h
theorem leaf_4012_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4012.profileLo box_4012.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4012_ok
theorem branch_box_4012_nonnegative : ∀ j, 0 ≤ branch_box_4012.lower j ∧ 0 ≤ branch_box_4012.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4012, Box.profileLo, Box.profileHi, box_4012]
theorem leaf_4012_BranchSafe : CertificateConsequences.BranchSafe branch_box_4012 := by
  left; refine ⟨branch_box_4012_nonnegative, ?_⟩
  intro z hz; exact leaf_4012_sound hz

theorem leaf_4014_ok : checkAt 527 1000 box_4014 cert_4014 = true := by
  have h := List.all_eq_true.mp batch_80_07_ok accepted_4014 (by simp [batch_80_07_values])
  exact h
theorem leaf_4014_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4014.profileLo box_4014.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4014_ok
theorem branch_box_4014_nonnegative : ∀ j, 0 ≤ branch_box_4014.lower j ∧ 0 ≤ branch_box_4014.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4014, Box.profileLo, Box.profileHi, box_4014]
theorem leaf_4014_BranchSafe : CertificateConsequences.BranchSafe branch_box_4014 := by
  left; refine ⟨branch_box_4014_nonnegative, ?_⟩
  intro z hz; exact leaf_4014_sound hz

theorem leaf_4016_ok : checkAt 527 1000 box_4016 cert_4016 = true := by
  have h := List.all_eq_true.mp batch_80_08_ok accepted_4016 (by simp [batch_80_08_values])
  exact h
theorem leaf_4016_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4016.profileLo box_4016.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4016_ok
theorem branch_box_4016_nonnegative : ∀ j, 0 ≤ branch_box_4016.lower j ∧ 0 ≤ branch_box_4016.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4016, Box.profileLo, Box.profileHi, box_4016]
theorem leaf_4016_BranchSafe : CertificateConsequences.BranchSafe branch_box_4016 := by
  left; refine ⟨branch_box_4016_nonnegative, ?_⟩
  intro z hz; exact leaf_4016_sound hz

theorem leaf_4019_ok : checkAt 527 1000 box_4019 cert_4019 = true := by
  have h := List.all_eq_true.mp batch_80_09_ok accepted_4019 (by simp [batch_80_09_values])
  exact h
theorem leaf_4019_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4019.profileLo box_4019.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4019_ok
theorem branch_box_4019_nonnegative : ∀ j, 0 ≤ branch_box_4019.lower j ∧ 0 ≤ branch_box_4019.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4019, Box.profileLo, Box.profileHi, box_4019]
theorem leaf_4019_BranchSafe : CertificateConsequences.BranchSafe branch_box_4019 := by
  left; refine ⟨branch_box_4019_nonnegative, ?_⟩
  intro z hz; exact leaf_4019_sound hz

theorem leaf_4022_ok : checkAt 527 1000 box_4022 cert_4022 = true := by
  have h := List.all_eq_true.mp batch_80_10_ok accepted_4022 (by simp [batch_80_10_values])
  exact h
theorem leaf_4022_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4022.profileLo box_4022.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4022_ok
theorem branch_box_4022_nonnegative : ∀ j, 0 ≤ branch_box_4022.lower j ∧ 0 ≤ branch_box_4022.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4022, Box.profileLo, Box.profileHi, box_4022]
theorem leaf_4022_BranchSafe : CertificateConsequences.BranchSafe branch_box_4022 := by
  left; refine ⟨branch_box_4022_nonnegative, ?_⟩
  intro z hz; exact leaf_4022_sound hz

theorem leaf_4023_ok : checkAt 527 1000 box_4023 cert_4023 = true := by
  have h := List.all_eq_true.mp batch_80_11_ok accepted_4023 (by simp [batch_80_11_values])
  exact h
theorem leaf_4023_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4023.profileLo box_4023.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4023_ok
theorem branch_box_4023_nonnegative : ∀ j, 0 ≤ branch_box_4023.lower j ∧ 0 ≤ branch_box_4023.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4023, Box.profileLo, Box.profileHi, box_4023]
theorem leaf_4023_BranchSafe : CertificateConsequences.BranchSafe branch_box_4023 := by
  left; refine ⟨branch_box_4023_nonnegative, ?_⟩
  intro z hz; exact leaf_4023_sound hz

theorem leaf_4026_ok : checkAt 527 1000 box_4026 cert_4026 = true := by
  have h := List.all_eq_true.mp batch_80_12_ok accepted_4026 (by simp [batch_80_12_values])
  exact h
theorem leaf_4026_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4026.profileLo box_4026.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4026_ok
theorem branch_box_4026_nonnegative : ∀ j, 0 ≤ branch_box_4026.lower j ∧ 0 ≤ branch_box_4026.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4026, Box.profileLo, Box.profileHi, box_4026]
theorem leaf_4026_BranchSafe : CertificateConsequences.BranchSafe branch_box_4026 := by
  left; refine ⟨branch_box_4026_nonnegative, ?_⟩
  intro z hz; exact leaf_4026_sound hz

theorem leaf_4028_ok : checkAt 527 1000 box_4028 cert_4028 = true := by
  have h := List.all_eq_true.mp batch_80_13_ok accepted_4028 (by simp [batch_80_13_values])
  exact h
theorem leaf_4028_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4028.profileLo box_4028.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4028_ok
theorem branch_box_4028_nonnegative : ∀ j, 0 ≤ branch_box_4028.lower j ∧ 0 ≤ branch_box_4028.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4028, Box.profileLo, Box.profileHi, box_4028]
theorem leaf_4028_BranchSafe : CertificateConsequences.BranchSafe branch_box_4028 := by
  left; refine ⟨branch_box_4028_nonnegative, ?_⟩
  intro z hz; exact leaf_4028_sound hz

theorem leaf_4029_ok : checkAt 527 1000 box_4029 cert_4029 = true := by
  have h := List.all_eq_true.mp batch_80_14_ok accepted_4029 (by simp [batch_80_14_values])
  exact h
theorem leaf_4029_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4029.profileLo box_4029.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4029_ok
theorem branch_box_4029_nonnegative : ∀ j, 0 ≤ branch_box_4029.lower j ∧ 0 ≤ branch_box_4029.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4029, Box.profileLo, Box.profileHi, box_4029]
theorem leaf_4029_BranchSafe : CertificateConsequences.BranchSafe branch_box_4029 := by
  left; refine ⟨branch_box_4029_nonnegative, ?_⟩
  intro z hz; exact leaf_4029_sound hz

theorem leaf_4030_ok : checkAt 527 1000 box_4030 cert_4030 = true := by
  have h := List.all_eq_true.mp batch_80_15_ok accepted_4030 (by simp [batch_80_15_values])
  exact h
theorem leaf_4030_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4030.profileLo box_4030.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4030_ok
theorem branch_box_4030_nonnegative : ∀ j, 0 ≤ branch_box_4030.lower j ∧ 0 ≤ branch_box_4030.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4030, Box.profileLo, Box.profileHi, box_4030]
theorem leaf_4030_BranchSafe : CertificateConsequences.BranchSafe branch_box_4030 := by
  left; refine ⟨branch_box_4030_nonnegative, ?_⟩
  intro z hz; exact leaf_4030_sound hz

theorem leaf_4033_ok : checkAt 527 1000 box_4033 cert_4033 = true := by
  have h := List.all_eq_true.mp batch_80_16_ok accepted_4033 (by simp [batch_80_16_values])
  exact h
theorem leaf_4033_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4033.profileLo box_4033.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4033_ok
theorem branch_box_4033_nonnegative : ∀ j, 0 ≤ branch_box_4033.lower j ∧ 0 ≤ branch_box_4033.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4033, Box.profileLo, Box.profileHi, box_4033]
theorem leaf_4033_BranchSafe : CertificateConsequences.BranchSafe branch_box_4033 := by
  left; refine ⟨branch_box_4033_nonnegative, ?_⟩
  intro z hz; exact leaf_4033_sound hz

theorem leaf_4036_ok : checkAt 527 1000 box_4036 cert_4036 = true := by
  have h := List.all_eq_true.mp batch_80_17_ok accepted_4036 (by simp [batch_80_17_values])
  exact h
theorem leaf_4036_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4036.profileLo box_4036.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4036_ok
theorem branch_box_4036_nonnegative : ∀ j, 0 ≤ branch_box_4036.lower j ∧ 0 ≤ branch_box_4036.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4036, Box.profileLo, Box.profileHi, box_4036]
theorem leaf_4036_BranchSafe : CertificateConsequences.BranchSafe branch_box_4036 := by
  left; refine ⟨branch_box_4036_nonnegative, ?_⟩
  intro z hz; exact leaf_4036_sound hz

theorem leaf_4038_ok : checkAt 527 1000 box_4038 cert_4038 = true := by
  have h := List.all_eq_true.mp batch_80_18_ok accepted_4038 (by simp [batch_80_18_values])
  exact h
theorem leaf_4038_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4038.profileLo box_4038.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4038_ok
theorem branch_box_4038_nonnegative : ∀ j, 0 ≤ branch_box_4038.lower j ∧ 0 ≤ branch_box_4038.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4038, Box.profileLo, Box.profileHi, box_4038]
theorem leaf_4038_BranchSafe : CertificateConsequences.BranchSafe branch_box_4038 := by
  left; refine ⟨branch_box_4038_nonnegative, ?_⟩
  intro z hz; exact leaf_4038_sound hz

theorem leaf_4041_ok : checkAt 527 1000 box_4041 cert_4041 = true := by
  have h := List.all_eq_true.mp batch_80_19_ok accepted_4041 (by simp [batch_80_19_values])
  exact h
theorem leaf_4041_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4041.profileLo box_4041.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4041_ok
theorem branch_box_4041_nonnegative : ∀ j, 0 ≤ branch_box_4041.lower j ∧ 0 ≤ branch_box_4041.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4041, Box.profileLo, Box.profileHi, box_4041]
theorem leaf_4041_BranchSafe : CertificateConsequences.BranchSafe branch_box_4041 := by
  left; refine ⟨branch_box_4041_nonnegative, ?_⟩
  intro z hz; exact leaf_4041_sound hz

theorem leaf_4044_ok : checkAt 527 1000 box_4044 cert_4044 = true := by
  have h := List.all_eq_true.mp batch_80_20_ok accepted_4044 (by simp [batch_80_20_values])
  exact h
theorem leaf_4044_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4044.profileLo box_4044.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4044_ok
theorem branch_box_4044_nonnegative : ∀ j, 0 ≤ branch_box_4044.lower j ∧ 0 ≤ branch_box_4044.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4044, Box.profileLo, Box.profileHi, box_4044]
theorem leaf_4044_BranchSafe : CertificateConsequences.BranchSafe branch_box_4044 := by
  left; refine ⟨branch_box_4044_nonnegative, ?_⟩
  intro z hz; exact leaf_4044_sound hz

theorem leaf_4046_ok : checkAt 527 1000 box_4046 cert_4046 = true := by
  have h := List.all_eq_true.mp batch_80_21_ok accepted_4046 (by simp [batch_80_21_values])
  exact h
theorem leaf_4046_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4046.profileLo box_4046.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4046_ok
theorem branch_box_4046_nonnegative : ∀ j, 0 ≤ branch_box_4046.lower j ∧ 0 ≤ branch_box_4046.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4046, Box.profileLo, Box.profileHi, box_4046]
theorem leaf_4046_BranchSafe : CertificateConsequences.BranchSafe branch_box_4046 := by
  left; refine ⟨branch_box_4046_nonnegative, ?_⟩
  intro z hz; exact leaf_4046_sound hz

theorem leaf_4047_ok : checkAt 527 1000 box_4047 cert_4047 = true := by
  have h := List.all_eq_true.mp batch_80_22_ok accepted_4047 (by simp [batch_80_22_values])
  exact h
theorem leaf_4047_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4047.profileLo box_4047.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4047_ok
theorem branch_box_4047_nonnegative : ∀ j, 0 ≤ branch_box_4047.lower j ∧ 0 ≤ branch_box_4047.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4047, Box.profileLo, Box.profileHi, box_4047]
theorem leaf_4047_BranchSafe : CertificateConsequences.BranchSafe branch_box_4047 := by
  left; refine ⟨branch_box_4047_nonnegative, ?_⟩
  intro z hz; exact leaf_4047_sound hz

#print axioms batch_80_00_ok
#print axioms leaf_4000_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
