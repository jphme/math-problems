import PeaceableQueens.UpperBound.Generated.Even.C527Scaled20Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_20_00_values : List Bool := [accepted_1001]
theorem batch_20_00_ok : batch_20_00_values.all id = true := by decide

def batch_20_01_values : List Bool := [accepted_1003]
theorem batch_20_01_ok : batch_20_01_values.all id = true := by decide

def batch_20_02_values : List Bool := [accepted_1004]
theorem batch_20_02_ok : batch_20_02_values.all id = true := by decide

def batch_20_03_values : List Bool := [accepted_1007]
theorem batch_20_03_ok : batch_20_03_values.all id = true := by decide

def batch_20_04_values : List Bool := [accepted_1008]
theorem batch_20_04_ok : batch_20_04_values.all id = true := by decide

def batch_20_05_values : List Bool := [accepted_1009]
theorem batch_20_05_ok : batch_20_05_values.all id = true := by decide

def batch_20_06_values : List Bool := [accepted_1011]
theorem batch_20_06_ok : batch_20_06_values.all id = true := by decide

def batch_20_07_values : List Bool := [accepted_1012]
theorem batch_20_07_ok : batch_20_07_values.all id = true := by decide

def batch_20_08_values : List Bool := [accepted_1025]
theorem batch_20_08_ok : batch_20_08_values.all id = true := by decide

def batch_20_09_values : List Bool := [accepted_1026]
theorem batch_20_09_ok : batch_20_09_values.all id = true := by decide

def batch_20_10_values : List Bool := [accepted_1029]
theorem batch_20_10_ok : batch_20_10_values.all id = true := by decide

def batch_20_11_values : List Bool := [accepted_1033]
theorem batch_20_11_ok : batch_20_11_values.all id = true := by decide

def batch_20_12_values : List Bool := [accepted_1034]
theorem batch_20_12_ok : batch_20_12_values.all id = true := by decide

def batch_20_13_values : List Bool := [accepted_1035]
theorem batch_20_13_ok : batch_20_13_values.all id = true := by decide

def batch_20_14_values : List Bool := [accepted_1036]
theorem batch_20_14_ok : batch_20_14_values.all id = true := by decide

def batch_20_15_values : List Bool := [accepted_1037]
theorem batch_20_15_ok : batch_20_15_values.all id = true := by decide

def batch_20_16_values : List Bool := [accepted_1038]
theorem batch_20_16_ok : batch_20_16_values.all id = true := by decide

def batch_20_17_values : List Bool := [accepted_1047]
theorem batch_20_17_ok : batch_20_17_values.all id = true := by decide

def batch_20_18_values : List Bool := [accepted_1048]
theorem batch_20_18_ok : batch_20_18_values.all id = true := by decide

def batch_20_19_values : List Bool := [accepted_1049]
theorem batch_20_19_ok : batch_20_19_values.all id = true := by decide

theorem leaf_1001_ok : checkAt 527 1000 box_1001 cert_1001 = true := by
  have h := List.all_eq_true.mp batch_20_00_ok accepted_1001 (by simp [batch_20_00_values])
  exact h
theorem leaf_1001_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1001.profileLo box_1001.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1001_ok
theorem branch_box_1001_nonnegative : ∀ j, 0 ≤ branch_box_1001.lower j ∧ 0 ≤ branch_box_1001.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1001, Box.profileLo, Box.profileHi, box_1001]
theorem leaf_1001_BranchSafe : CertificateConsequences.BranchSafe branch_box_1001 := by
  left; refine ⟨branch_box_1001_nonnegative, ?_⟩
  intro z hz; exact leaf_1001_sound hz

theorem leaf_1003_ok : checkAt 527 1000 box_1003 cert_1003 = true := by
  have h := List.all_eq_true.mp batch_20_01_ok accepted_1003 (by simp [batch_20_01_values])
  exact h
theorem leaf_1003_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1003.profileLo box_1003.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1003_ok
theorem branch_box_1003_nonnegative : ∀ j, 0 ≤ branch_box_1003.lower j ∧ 0 ≤ branch_box_1003.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1003, Box.profileLo, Box.profileHi, box_1003]
theorem leaf_1003_BranchSafe : CertificateConsequences.BranchSafe branch_box_1003 := by
  left; refine ⟨branch_box_1003_nonnegative, ?_⟩
  intro z hz; exact leaf_1003_sound hz

theorem leaf_1004_ok : checkAt 527 1000 box_1004 cert_1004 = true := by
  have h := List.all_eq_true.mp batch_20_02_ok accepted_1004 (by simp [batch_20_02_values])
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

theorem leaf_1008_ok : checkAt 527 1000 box_1008 cert_1008 = true := by
  have h := List.all_eq_true.mp batch_20_04_ok accepted_1008 (by simp [batch_20_04_values])
  exact h
theorem leaf_1008_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1008.profileLo box_1008.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1008_ok
theorem branch_box_1008_nonnegative : ∀ j, 0 ≤ branch_box_1008.lower j ∧ 0 ≤ branch_box_1008.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1008, Box.profileLo, Box.profileHi, box_1008]
theorem leaf_1008_BranchSafe : CertificateConsequences.BranchSafe branch_box_1008 := by
  left; refine ⟨branch_box_1008_nonnegative, ?_⟩
  intro z hz; exact leaf_1008_sound hz

theorem leaf_1009_ok : checkAt 527 1000 box_1009 cert_1009 = true := by
  have h := List.all_eq_true.mp batch_20_05_ok accepted_1009 (by simp [batch_20_05_values])
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

theorem leaf_1011_ok : checkAt 527 1000 box_1011 cert_1011 = true := by
  have h := List.all_eq_true.mp batch_20_06_ok accepted_1011 (by simp [batch_20_06_values])
  exact h
theorem leaf_1011_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1011.profileLo box_1011.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1011_ok
theorem branch_box_1011_nonnegative : ∀ j, 0 ≤ branch_box_1011.lower j ∧ 0 ≤ branch_box_1011.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1011, Box.profileLo, Box.profileHi, box_1011]
theorem leaf_1011_BranchSafe : CertificateConsequences.BranchSafe branch_box_1011 := by
  left; refine ⟨branch_box_1011_nonnegative, ?_⟩
  intro z hz; exact leaf_1011_sound hz

theorem leaf_1012_ok : checkAt 527 1000 box_1012 cert_1012 = true := by
  have h := List.all_eq_true.mp batch_20_07_ok accepted_1012 (by simp [batch_20_07_values])
  exact h
theorem leaf_1012_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1012.profileLo box_1012.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1012_ok
theorem branch_box_1012_nonnegative : ∀ j, 0 ≤ branch_box_1012.lower j ∧ 0 ≤ branch_box_1012.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1012, Box.profileLo, Box.profileHi, box_1012]
theorem leaf_1012_BranchSafe : CertificateConsequences.BranchSafe branch_box_1012 := by
  left; refine ⟨branch_box_1012_nonnegative, ?_⟩
  intro z hz; exact leaf_1012_sound hz

theorem leaf_1025_ok : checkAt 527 1000 box_1025 cert_1025 = true := by
  have h := List.all_eq_true.mp batch_20_08_ok accepted_1025 (by simp [batch_20_08_values])
  exact h
theorem leaf_1025_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1025.profileLo box_1025.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1025_ok
theorem branch_box_1025_nonnegative : ∀ j, 0 ≤ branch_box_1025.lower j ∧ 0 ≤ branch_box_1025.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1025, Box.profileLo, Box.profileHi, box_1025]
theorem leaf_1025_BranchSafe : CertificateConsequences.BranchSafe branch_box_1025 := by
  left; refine ⟨branch_box_1025_nonnegative, ?_⟩
  intro z hz; exact leaf_1025_sound hz

theorem leaf_1026_ok : checkAt 527 1000 box_1026 cert_1026 = true := by
  have h := List.all_eq_true.mp batch_20_09_ok accepted_1026 (by simp [batch_20_09_values])
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

theorem leaf_1029_ok : checkAt 527 1000 box_1029 cert_1029 = true := by
  have h := List.all_eq_true.mp batch_20_10_ok accepted_1029 (by simp [batch_20_10_values])
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

theorem leaf_1033_ok : checkAt 527 1000 box_1033 cert_1033 = true := by
  have h := List.all_eq_true.mp batch_20_11_ok accepted_1033 (by simp [batch_20_11_values])
  exact h
theorem leaf_1033_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1033.profileLo box_1033.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1033_ok
theorem branch_box_1033_nonnegative : ∀ j, 0 ≤ branch_box_1033.lower j ∧ 0 ≤ branch_box_1033.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1033, Box.profileLo, Box.profileHi, box_1033]
theorem leaf_1033_BranchSafe : CertificateConsequences.BranchSafe branch_box_1033 := by
  left; refine ⟨branch_box_1033_nonnegative, ?_⟩
  intro z hz; exact leaf_1033_sound hz

theorem leaf_1034_ok : checkAt 527 1000 box_1034 cert_1034 = true := by
  have h := List.all_eq_true.mp batch_20_12_ok accepted_1034 (by simp [batch_20_12_values])
  exact h
theorem leaf_1034_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1034.profileLo box_1034.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1034_ok
theorem branch_box_1034_nonnegative : ∀ j, 0 ≤ branch_box_1034.lower j ∧ 0 ≤ branch_box_1034.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1034, Box.profileLo, Box.profileHi, box_1034]
theorem leaf_1034_BranchSafe : CertificateConsequences.BranchSafe branch_box_1034 := by
  left; refine ⟨branch_box_1034_nonnegative, ?_⟩
  intro z hz; exact leaf_1034_sound hz

theorem leaf_1035_ok : checkAt 527 1000 box_1035 cert_1035 = true := by
  have h := List.all_eq_true.mp batch_20_13_ok accepted_1035 (by simp [batch_20_13_values])
  exact h
theorem leaf_1035_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1035.profileLo box_1035.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1035_ok
theorem branch_box_1035_nonnegative : ∀ j, 0 ≤ branch_box_1035.lower j ∧ 0 ≤ branch_box_1035.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1035, Box.profileLo, Box.profileHi, box_1035]
theorem leaf_1035_BranchSafe : CertificateConsequences.BranchSafe branch_box_1035 := by
  left; refine ⟨branch_box_1035_nonnegative, ?_⟩
  intro z hz; exact leaf_1035_sound hz

theorem leaf_1036_ok : checkAt 527 1000 box_1036 cert_1036 = true := by
  have h := List.all_eq_true.mp batch_20_14_ok accepted_1036 (by simp [batch_20_14_values])
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

theorem leaf_1037_ok : checkAt 527 1000 box_1037 cert_1037 = true := by
  have h := List.all_eq_true.mp batch_20_15_ok accepted_1037 (by simp [batch_20_15_values])
  exact h
theorem leaf_1037_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1037.profileLo box_1037.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1037_ok
theorem branch_box_1037_nonnegative : ∀ j, 0 ≤ branch_box_1037.lower j ∧ 0 ≤ branch_box_1037.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1037, Box.profileLo, Box.profileHi, box_1037]
theorem leaf_1037_BranchSafe : CertificateConsequences.BranchSafe branch_box_1037 := by
  left; refine ⟨branch_box_1037_nonnegative, ?_⟩
  intro z hz; exact leaf_1037_sound hz

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

theorem leaf_1047_ok : checkAt 527 1000 box_1047 cert_1047 = true := by
  have h := List.all_eq_true.mp batch_20_17_ok accepted_1047 (by simp [batch_20_17_values])
  exact h
theorem leaf_1047_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1047.profileLo box_1047.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1047_ok
theorem branch_box_1047_nonnegative : ∀ j, 0 ≤ branch_box_1047.lower j ∧ 0 ≤ branch_box_1047.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1047, Box.profileLo, Box.profileHi, box_1047]
theorem leaf_1047_BranchSafe : CertificateConsequences.BranchSafe branch_box_1047 := by
  left; refine ⟨branch_box_1047_nonnegative, ?_⟩
  intro z hz; exact leaf_1047_sound hz

theorem leaf_1048_ok : checkAt 527 1000 box_1048 cert_1048 = true := by
  have h := List.all_eq_true.mp batch_20_18_ok accepted_1048 (by simp [batch_20_18_values])
  exact h
theorem leaf_1048_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1048.profileLo box_1048.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1048_ok
theorem branch_box_1048_nonnegative : ∀ j, 0 ≤ branch_box_1048.lower j ∧ 0 ≤ branch_box_1048.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1048, Box.profileLo, Box.profileHi, box_1048]
theorem leaf_1048_BranchSafe : CertificateConsequences.BranchSafe branch_box_1048 := by
  left; refine ⟨branch_box_1048_nonnegative, ?_⟩
  intro z hz; exact leaf_1048_sound hz

theorem leaf_1049_ok : checkAt 527 1000 box_1049 cert_1049 = true := by
  have h := List.all_eq_true.mp batch_20_19_ok accepted_1049 (by simp [batch_20_19_values])
  exact h
theorem leaf_1049_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1049.profileLo box_1049.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1049_ok
theorem branch_box_1049_nonnegative : ∀ j, 0 ≤ branch_box_1049.lower j ∧ 0 ≤ branch_box_1049.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1049, Box.profileLo, Box.profileHi, box_1049]
theorem leaf_1049_BranchSafe : CertificateConsequences.BranchSafe branch_box_1049 := by
  left; refine ⟨branch_box_1049_nonnegative, ?_⟩
  intro z hz; exact leaf_1049_sound hz

#print axioms batch_20_00_ok
#print axioms leaf_1001_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
