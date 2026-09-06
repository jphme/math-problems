import PeaceableQueens.UpperBound.Generated.Even.CoreScaled20Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_20_00_values : List Bool := [accepted_1002]
theorem batch_20_00_ok : batch_20_00_values.all id = true := by decide

def batch_20_01_values : List Bool := [accepted_1004]
theorem batch_20_01_ok : batch_20_01_values.all id = true := by decide

def batch_20_02_values : List Bool := [accepted_1005]
theorem batch_20_02_ok : batch_20_02_values.all id = true := by decide

def batch_20_03_values : List Bool := [accepted_1007]
theorem batch_20_03_ok : batch_20_03_values.all id = true := by decide

def batch_20_04_values : List Bool := [accepted_1009]
theorem batch_20_04_ok : batch_20_04_values.all id = true := by decide

def batch_20_05_values : List Bool := [accepted_1014]
theorem batch_20_05_ok : batch_20_05_values.all id = true := by decide

def batch_20_06_values : List Bool := [accepted_1015]
theorem batch_20_06_ok : batch_20_06_values.all id = true := by decide

def batch_20_07_values : List Bool := [accepted_1018]
theorem batch_20_07_ok : batch_20_07_values.all id = true := by decide

def batch_20_08_values : List Bool := [accepted_1020]
theorem batch_20_08_ok : batch_20_08_values.all id = true := by decide

def batch_20_09_values : List Bool := [accepted_1021]
theorem batch_20_09_ok : batch_20_09_values.all id = true := by decide

def batch_20_10_values : List Bool := [accepted_1024]
theorem batch_20_10_ok : batch_20_10_values.all id = true := by decide

def batch_20_11_values : List Bool := [accepted_1026]
theorem batch_20_11_ok : batch_20_11_values.all id = true := by decide

def batch_20_12_values : List Bool := [accepted_1028]
theorem batch_20_12_ok : batch_20_12_values.all id = true := by decide

def batch_20_13_values : List Bool := [accepted_1029]
theorem batch_20_13_ok : batch_20_13_values.all id = true := by decide

def batch_20_14_values : List Bool := [accepted_1031]
theorem batch_20_14_ok : batch_20_14_values.all id = true := by decide

def batch_20_15_values : List Bool := [accepted_1036]
theorem batch_20_15_ok : batch_20_15_values.all id = true := by decide

def batch_20_16_values : List Bool := [accepted_1038]
theorem batch_20_16_ok : batch_20_16_values.all id = true := by decide

def batch_20_17_values : List Bool := [accepted_1040]
theorem batch_20_17_ok : batch_20_17_values.all id = true := by decide

def batch_20_18_values : List Bool := [accepted_1041]
theorem batch_20_18_ok : batch_20_18_values.all id = true := by decide

def batch_20_19_values : List Bool := [accepted_1043]
theorem batch_20_19_ok : batch_20_19_values.all id = true := by decide

def batch_20_20_values : List Bool := [accepted_1045]
theorem batch_20_20_ok : batch_20_20_values.all id = true := by decide

theorem leaf_1002_ok : checkAt 527 1000 box_1002 cert_1002 = true := by
  have h := List.all_eq_true.mp batch_20_00_ok accepted_1002 (by simp [batch_20_00_values])
  exact h
theorem leaf_1002_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1002.profileLo box_1002.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1002_ok
theorem branch_box_1002_nonnegative : ∀ j, 0 ≤ branch_box_1002.lower j ∧ 0 ≤ branch_box_1002.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1002, Box.profileLo, Box.profileHi, box_1002]
theorem leaf_1002_BranchSafe : CertificateConsequences.BranchSafe branch_box_1002 := by
  left; refine ⟨branch_box_1002_nonnegative, ?_⟩
  intro z hz; exact leaf_1002_sound hz

theorem leaf_1004_ok : checkAt 527 1000 box_1004 cert_1004 = true := by
  have h := List.all_eq_true.mp batch_20_01_ok accepted_1004 (by simp [batch_20_01_values])
  exact h
theorem leaf_1004_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1004.profileLo box_1004.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1004_ok
theorem branch_box_1004_nonnegative : ∀ j, 0 ≤ branch_box_1004.lower j ∧ 0 ≤ branch_box_1004.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1004, Box.profileLo, Box.profileHi, box_1004]
theorem leaf_1004_BranchSafe : CertificateConsequences.BranchSafe branch_box_1004 := by
  left; refine ⟨branch_box_1004_nonnegative, ?_⟩
  intro z hz; exact leaf_1004_sound hz

theorem leaf_1005_ok : checkAt 527 1000 box_1005 cert_1005 = true := by
  have h := List.all_eq_true.mp batch_20_02_ok accepted_1005 (by simp [batch_20_02_values])
  exact h
theorem leaf_1005_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1005.profileLo box_1005.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1005_ok
theorem branch_box_1005_nonnegative : ∀ j, 0 ≤ branch_box_1005.lower j ∧ 0 ≤ branch_box_1005.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1005, Box.profileLo, Box.profileHi, box_1005]
theorem leaf_1005_BranchSafe : CertificateConsequences.BranchSafe branch_box_1005 := by
  left; refine ⟨branch_box_1005_nonnegative, ?_⟩
  intro z hz; exact leaf_1005_sound hz

theorem leaf_1007_ok : checkAt 527 1000 box_1007 cert_1007 = true := by
  have h := List.all_eq_true.mp batch_20_03_ok accepted_1007 (by simp [batch_20_03_values])
  exact h
theorem leaf_1007_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1007.profileLo box_1007.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1007_ok
theorem branch_box_1007_nonnegative : ∀ j, 0 ≤ branch_box_1007.lower j ∧ 0 ≤ branch_box_1007.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1007, Box.profileLo, Box.profileHi, box_1007]
theorem leaf_1007_BranchSafe : CertificateConsequences.BranchSafe branch_box_1007 := by
  left; refine ⟨branch_box_1007_nonnegative, ?_⟩
  intro z hz; exact leaf_1007_sound hz

theorem leaf_1009_ok : checkAt 527 1000 box_1009 cert_1009 = true := by
  have h := List.all_eq_true.mp batch_20_04_ok accepted_1009 (by simp [batch_20_04_values])
  exact h
theorem leaf_1009_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1009.profileLo box_1009.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1009_ok
theorem branch_box_1009_nonnegative : ∀ j, 0 ≤ branch_box_1009.lower j ∧ 0 ≤ branch_box_1009.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1009, Box.profileLo, Box.profileHi, box_1009]
theorem leaf_1009_BranchSafe : CertificateConsequences.BranchSafe branch_box_1009 := by
  left; refine ⟨branch_box_1009_nonnegative, ?_⟩
  intro z hz; exact leaf_1009_sound hz

theorem leaf_1014_ok : checkAt 527 1000 box_1014 cert_1014 = true := by
  have h := List.all_eq_true.mp batch_20_05_ok accepted_1014 (by simp [batch_20_05_values])
  exact h
theorem leaf_1014_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1014.profileLo box_1014.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1014_ok
theorem branch_box_1014_nonnegative : ∀ j, 0 ≤ branch_box_1014.lower j ∧ 0 ≤ branch_box_1014.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1014, Box.profileLo, Box.profileHi, box_1014]
theorem leaf_1014_BranchSafe : CertificateConsequences.BranchSafe branch_box_1014 := by
  left; refine ⟨branch_box_1014_nonnegative, ?_⟩
  intro z hz; exact leaf_1014_sound hz

theorem leaf_1015_ok : checkAt 527 1000 box_1015 cert_1015 = true := by
  have h := List.all_eq_true.mp batch_20_06_ok accepted_1015 (by simp [batch_20_06_values])
  exact h
theorem leaf_1015_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1015.profileLo box_1015.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1015_ok
theorem branch_box_1015_nonnegative : ∀ j, 0 ≤ branch_box_1015.lower j ∧ 0 ≤ branch_box_1015.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1015, Box.profileLo, Box.profileHi, box_1015]
theorem leaf_1015_BranchSafe : CertificateConsequences.BranchSafe branch_box_1015 := by
  left; refine ⟨branch_box_1015_nonnegative, ?_⟩
  intro z hz; exact leaf_1015_sound hz

theorem leaf_1018_ok : checkAt 527 1000 box_1018 cert_1018 = true := by
  have h := List.all_eq_true.mp batch_20_07_ok accepted_1018 (by simp [batch_20_07_values])
  exact h
theorem leaf_1018_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1018.profileLo box_1018.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1018_ok
theorem branch_box_1018_nonnegative : ∀ j, 0 ≤ branch_box_1018.lower j ∧ 0 ≤ branch_box_1018.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1018, Box.profileLo, Box.profileHi, box_1018]
theorem leaf_1018_BranchSafe : CertificateConsequences.BranchSafe branch_box_1018 := by
  left; refine ⟨branch_box_1018_nonnegative, ?_⟩
  intro z hz; exact leaf_1018_sound hz

theorem leaf_1020_ok : checkAt 527 1000 box_1020 cert_1020 = true := by
  have h := List.all_eq_true.mp batch_20_08_ok accepted_1020 (by simp [batch_20_08_values])
  exact h
theorem leaf_1020_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1020.profileLo box_1020.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1020_ok
theorem branch_box_1020_nonnegative : ∀ j, 0 ≤ branch_box_1020.lower j ∧ 0 ≤ branch_box_1020.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1020, Box.profileLo, Box.profileHi, box_1020]
theorem leaf_1020_BranchSafe : CertificateConsequences.BranchSafe branch_box_1020 := by
  left; refine ⟨branch_box_1020_nonnegative, ?_⟩
  intro z hz; exact leaf_1020_sound hz

theorem leaf_1021_ok : checkAt 527 1000 box_1021 cert_1021 = true := by
  have h := List.all_eq_true.mp batch_20_09_ok accepted_1021 (by simp [batch_20_09_values])
  exact h
theorem leaf_1021_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1021.profileLo box_1021.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1021_ok
theorem branch_box_1021_nonnegative : ∀ j, 0 ≤ branch_box_1021.lower j ∧ 0 ≤ branch_box_1021.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1021, Box.profileLo, Box.profileHi, box_1021]
theorem leaf_1021_BranchSafe : CertificateConsequences.BranchSafe branch_box_1021 := by
  left; refine ⟨branch_box_1021_nonnegative, ?_⟩
  intro z hz; exact leaf_1021_sound hz

theorem leaf_1024_ok : checkAt 527 1000 box_1024 cert_1024 = true := by
  have h := List.all_eq_true.mp batch_20_10_ok accepted_1024 (by simp [batch_20_10_values])
  exact h
theorem leaf_1024_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1024.profileLo box_1024.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1024_ok
theorem branch_box_1024_nonnegative : ∀ j, 0 ≤ branch_box_1024.lower j ∧ 0 ≤ branch_box_1024.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1024, Box.profileLo, Box.profileHi, box_1024]
theorem leaf_1024_BranchSafe : CertificateConsequences.BranchSafe branch_box_1024 := by
  left; refine ⟨branch_box_1024_nonnegative, ?_⟩
  intro z hz; exact leaf_1024_sound hz

theorem leaf_1026_ok : checkAt 527 1000 box_1026 cert_1026 = true := by
  have h := List.all_eq_true.mp batch_20_11_ok accepted_1026 (by simp [batch_20_11_values])
  exact h
theorem leaf_1026_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1026.profileLo box_1026.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1026_ok
theorem branch_box_1026_nonnegative : ∀ j, 0 ≤ branch_box_1026.lower j ∧ 0 ≤ branch_box_1026.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1026, Box.profileLo, Box.profileHi, box_1026]
theorem leaf_1026_BranchSafe : CertificateConsequences.BranchSafe branch_box_1026 := by
  left; refine ⟨branch_box_1026_nonnegative, ?_⟩
  intro z hz; exact leaf_1026_sound hz

theorem leaf_1028_ok : checkAt 527 1000 box_1028 cert_1028 = true := by
  have h := List.all_eq_true.mp batch_20_12_ok accepted_1028 (by simp [batch_20_12_values])
  exact h
theorem leaf_1028_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1028.profileLo box_1028.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1028_ok
theorem branch_box_1028_nonnegative : ∀ j, 0 ≤ branch_box_1028.lower j ∧ 0 ≤ branch_box_1028.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1028, Box.profileLo, Box.profileHi, box_1028]
theorem leaf_1028_BranchSafe : CertificateConsequences.BranchSafe branch_box_1028 := by
  left; refine ⟨branch_box_1028_nonnegative, ?_⟩
  intro z hz; exact leaf_1028_sound hz

theorem leaf_1029_ok : checkAt 527 1000 box_1029 cert_1029 = true := by
  have h := List.all_eq_true.mp batch_20_13_ok accepted_1029 (by simp [batch_20_13_values])
  exact h
theorem leaf_1029_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1029.profileLo box_1029.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1029_ok
theorem branch_box_1029_nonnegative : ∀ j, 0 ≤ branch_box_1029.lower j ∧ 0 ≤ branch_box_1029.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1029, Box.profileLo, Box.profileHi, box_1029]
theorem leaf_1029_BranchSafe : CertificateConsequences.BranchSafe branch_box_1029 := by
  left; refine ⟨branch_box_1029_nonnegative, ?_⟩
  intro z hz; exact leaf_1029_sound hz

theorem leaf_1031_ok : checkAt 527 1000 box_1031 cert_1031 = true := by
  have h := List.all_eq_true.mp batch_20_14_ok accepted_1031 (by simp [batch_20_14_values])
  exact h
theorem leaf_1031_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1031.profileLo box_1031.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1031_ok
theorem branch_box_1031_nonnegative : ∀ j, 0 ≤ branch_box_1031.lower j ∧ 0 ≤ branch_box_1031.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1031, Box.profileLo, Box.profileHi, box_1031]
theorem leaf_1031_BranchSafe : CertificateConsequences.BranchSafe branch_box_1031 := by
  left; refine ⟨branch_box_1031_nonnegative, ?_⟩
  intro z hz; exact leaf_1031_sound hz

theorem leaf_1036_ok : checkAt 527 1000 box_1036 cert_1036 = true := by
  have h := List.all_eq_true.mp batch_20_15_ok accepted_1036 (by simp [batch_20_15_values])
  exact h
theorem leaf_1036_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1036.profileLo box_1036.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1036_ok
theorem branch_box_1036_nonnegative : ∀ j, 0 ≤ branch_box_1036.lower j ∧ 0 ≤ branch_box_1036.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1036, Box.profileLo, Box.profileHi, box_1036]
theorem leaf_1036_BranchSafe : CertificateConsequences.BranchSafe branch_box_1036 := by
  left; refine ⟨branch_box_1036_nonnegative, ?_⟩
  intro z hz; exact leaf_1036_sound hz

theorem leaf_1038_ok : checkAt 527 1000 box_1038 cert_1038 = true := by
  have h := List.all_eq_true.mp batch_20_16_ok accepted_1038 (by simp [batch_20_16_values])
  exact h
theorem leaf_1038_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1038.profileLo box_1038.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1038_ok
theorem branch_box_1038_nonnegative : ∀ j, 0 ≤ branch_box_1038.lower j ∧ 0 ≤ branch_box_1038.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1038, Box.profileLo, Box.profileHi, box_1038]
theorem leaf_1038_BranchSafe : CertificateConsequences.BranchSafe branch_box_1038 := by
  left; refine ⟨branch_box_1038_nonnegative, ?_⟩
  intro z hz; exact leaf_1038_sound hz

theorem leaf_1040_ok : checkAt 527 1000 box_1040 cert_1040 = true := by
  have h := List.all_eq_true.mp batch_20_17_ok accepted_1040 (by simp [batch_20_17_values])
  exact h
theorem leaf_1040_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1040.profileLo box_1040.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1040_ok
theorem branch_box_1040_nonnegative : ∀ j, 0 ≤ branch_box_1040.lower j ∧ 0 ≤ branch_box_1040.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1040, Box.profileLo, Box.profileHi, box_1040]
theorem leaf_1040_BranchSafe : CertificateConsequences.BranchSafe branch_box_1040 := by
  left; refine ⟨branch_box_1040_nonnegative, ?_⟩
  intro z hz; exact leaf_1040_sound hz

theorem leaf_1041_ok : checkAt 527 1000 box_1041 cert_1041 = true := by
  have h := List.all_eq_true.mp batch_20_18_ok accepted_1041 (by simp [batch_20_18_values])
  exact h
theorem leaf_1041_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1041.profileLo box_1041.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1041_ok
theorem branch_box_1041_nonnegative : ∀ j, 0 ≤ branch_box_1041.lower j ∧ 0 ≤ branch_box_1041.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1041, Box.profileLo, Box.profileHi, box_1041]
theorem leaf_1041_BranchSafe : CertificateConsequences.BranchSafe branch_box_1041 := by
  left; refine ⟨branch_box_1041_nonnegative, ?_⟩
  intro z hz; exact leaf_1041_sound hz

theorem leaf_1043_ok : checkAt 527 1000 box_1043 cert_1043 = true := by
  have h := List.all_eq_true.mp batch_20_19_ok accepted_1043 (by simp [batch_20_19_values])
  exact h
theorem leaf_1043_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1043.profileLo box_1043.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1043_ok
theorem branch_box_1043_nonnegative : ∀ j, 0 ≤ branch_box_1043.lower j ∧ 0 ≤ branch_box_1043.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1043, Box.profileLo, Box.profileHi, box_1043]
theorem leaf_1043_BranchSafe : CertificateConsequences.BranchSafe branch_box_1043 := by
  left; refine ⟨branch_box_1043_nonnegative, ?_⟩
  intro z hz; exact leaf_1043_sound hz

theorem leaf_1045_ok : checkAt 527 1000 box_1045 cert_1045 = true := by
  have h := List.all_eq_true.mp batch_20_20_ok accepted_1045 (by simp [batch_20_20_values])
  exact h
theorem leaf_1045_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1045.profileLo box_1045.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1045_ok
theorem branch_box_1045_nonnegative : ∀ j, 0 ≤ branch_box_1045.lower j ∧ 0 ≤ branch_box_1045.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1045, Box.profileLo, Box.profileHi, box_1045]
theorem leaf_1045_BranchSafe : CertificateConsequences.BranchSafe branch_box_1045 := by
  left; refine ⟨branch_box_1045_nonnegative, ?_⟩
  intro z hz; exact leaf_1045_sound hz

#print axioms batch_20_00_ok
#print axioms leaf_1002_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
