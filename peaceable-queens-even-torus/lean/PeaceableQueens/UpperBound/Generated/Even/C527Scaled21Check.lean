import PeaceableQueens.UpperBound.Generated.Even.C527Scaled21Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_21_00_values : List Bool := [accepted_1050]
theorem batch_21_00_ok : batch_21_00_values.all id = true := by decide

def batch_21_01_values : List Bool := [accepted_1052]
theorem batch_21_01_ok : batch_21_01_values.all id = true := by decide

def batch_21_02_values : List Bool := [accepted_1053]
theorem batch_21_02_ok : batch_21_02_values.all id = true := by decide

def batch_21_03_values : List Bool := [accepted_1054]
theorem batch_21_03_ok : batch_21_03_values.all id = true := by decide

def batch_21_04_values : List Bool := [accepted_1055]
theorem batch_21_04_ok : batch_21_04_values.all id = true := by decide

def batch_21_05_values : List Bool := [accepted_1057]
theorem batch_21_05_ok : batch_21_05_values.all id = true := by decide

def batch_21_06_values : List Bool := [accepted_1058]
theorem batch_21_06_ok : batch_21_06_values.all id = true := by decide

def batch_21_07_values : List Bool := [accepted_1065]
theorem batch_21_07_ok : batch_21_07_values.all id = true := by decide

def batch_21_08_values : List Bool := [accepted_1066]
theorem batch_21_08_ok : batch_21_08_values.all id = true := by decide

def batch_21_09_values : List Bool := [accepted_1067]
theorem batch_21_09_ok : batch_21_09_values.all id = true := by decide

def batch_21_10_values : List Bool := [accepted_1068]
theorem batch_21_10_ok : batch_21_10_values.all id = true := by decide

def batch_21_11_values : List Bool := [accepted_1073]
theorem batch_21_11_ok : batch_21_11_values.all id = true := by decide

def batch_21_12_values : List Bool := [accepted_1074]
theorem batch_21_12_ok : batch_21_12_values.all id = true := by decide

def batch_21_13_values : List Bool := [accepted_1075]
theorem batch_21_13_ok : batch_21_13_values.all id = true := by decide

def batch_21_14_values : List Bool := [accepted_1077]
theorem batch_21_14_ok : batch_21_14_values.all id = true := by decide

def batch_21_15_values : List Bool := [accepted_1078]
theorem batch_21_15_ok : batch_21_15_values.all id = true := by decide

def batch_21_16_values : List Bool := [accepted_1081]
theorem batch_21_16_ok : batch_21_16_values.all id = true := by decide

def batch_21_17_values : List Bool := [accepted_1082]
theorem batch_21_17_ok : batch_21_17_values.all id = true := by decide

def batch_21_18_values : List Bool := [accepted_1083]
theorem batch_21_18_ok : batch_21_18_values.all id = true := by decide

def batch_21_19_values : List Bool := [accepted_1085]
theorem batch_21_19_ok : batch_21_19_values.all id = true := by decide

def batch_21_20_values : List Bool := [accepted_1086]
theorem batch_21_20_ok : batch_21_20_values.all id = true := by decide

def batch_21_21_values : List Bool := [accepted_1090]
theorem batch_21_21_ok : batch_21_21_values.all id = true := by decide

def batch_21_22_values : List Bool := [accepted_1091]
theorem batch_21_22_ok : batch_21_22_values.all id = true := by decide

def batch_21_23_values : List Bool := [accepted_1092]
theorem batch_21_23_ok : batch_21_23_values.all id = true := by decide

def batch_21_24_values : List Bool := [accepted_1093]
theorem batch_21_24_ok : batch_21_24_values.all id = true := by decide

def batch_21_25_values : List Bool := [accepted_1094]
theorem batch_21_25_ok : batch_21_25_values.all id = true := by decide

theorem leaf_1050_ok : checkAt 527 1000 box_1050 cert_1050 = true := by
  have h := List.all_eq_true.mp batch_21_00_ok accepted_1050 (by simp [batch_21_00_values])
  exact h
theorem leaf_1050_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1050.profileLo box_1050.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1050_ok
theorem branch_box_1050_nonnegative : ∀ j, 0 ≤ branch_box_1050.lower j ∧ 0 ≤ branch_box_1050.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1050, Box.profileLo, Box.profileHi, box_1050]
theorem leaf_1050_BranchSafe : CertificateConsequences.BranchSafe branch_box_1050 := by
  left; refine ⟨branch_box_1050_nonnegative, ?_⟩
  intro z hz; exact leaf_1050_sound hz

theorem leaf_1052_ok : checkAt 527 1000 box_1052 cert_1052 = true := by
  have h := List.all_eq_true.mp batch_21_01_ok accepted_1052 (by simp [batch_21_01_values])
  exact h
theorem leaf_1052_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1052.profileLo box_1052.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1052_ok
theorem branch_box_1052_nonnegative : ∀ j, 0 ≤ branch_box_1052.lower j ∧ 0 ≤ branch_box_1052.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1052, Box.profileLo, Box.profileHi, box_1052]
theorem leaf_1052_BranchSafe : CertificateConsequences.BranchSafe branch_box_1052 := by
  left; refine ⟨branch_box_1052_nonnegative, ?_⟩
  intro z hz; exact leaf_1052_sound hz

theorem leaf_1053_ok : checkAt 527 1000 box_1053 cert_1053 = true := by
  have h := List.all_eq_true.mp batch_21_02_ok accepted_1053 (by simp [batch_21_02_values])
  exact h
theorem leaf_1053_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1053.profileLo box_1053.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1053_ok
theorem branch_box_1053_nonnegative : ∀ j, 0 ≤ branch_box_1053.lower j ∧ 0 ≤ branch_box_1053.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1053, Box.profileLo, Box.profileHi, box_1053]
theorem leaf_1053_BranchSafe : CertificateConsequences.BranchSafe branch_box_1053 := by
  left; refine ⟨branch_box_1053_nonnegative, ?_⟩
  intro z hz; exact leaf_1053_sound hz

theorem leaf_1054_ok : checkAt 527 1000 box_1054 cert_1054 = true := by
  have h := List.all_eq_true.mp batch_21_03_ok accepted_1054 (by simp [batch_21_03_values])
  exact h
theorem leaf_1054_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1054.profileLo box_1054.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1054_ok
theorem branch_box_1054_nonnegative : ∀ j, 0 ≤ branch_box_1054.lower j ∧ 0 ≤ branch_box_1054.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1054, Box.profileLo, Box.profileHi, box_1054]
theorem leaf_1054_BranchSafe : CertificateConsequences.BranchSafe branch_box_1054 := by
  left; refine ⟨branch_box_1054_nonnegative, ?_⟩
  intro z hz; exact leaf_1054_sound hz

theorem leaf_1055_ok : checkAt 527 1000 box_1055 cert_1055 = true := by
  have h := List.all_eq_true.mp batch_21_04_ok accepted_1055 (by simp [batch_21_04_values])
  exact h
theorem leaf_1055_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1055.profileLo box_1055.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1055_ok
theorem branch_box_1055_nonnegative : ∀ j, 0 ≤ branch_box_1055.lower j ∧ 0 ≤ branch_box_1055.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1055, Box.profileLo, Box.profileHi, box_1055]
theorem leaf_1055_BranchSafe : CertificateConsequences.BranchSafe branch_box_1055 := by
  left; refine ⟨branch_box_1055_nonnegative, ?_⟩
  intro z hz; exact leaf_1055_sound hz

theorem leaf_1057_ok : checkAt 527 1000 box_1057 cert_1057 = true := by
  have h := List.all_eq_true.mp batch_21_05_ok accepted_1057 (by simp [batch_21_05_values])
  exact h
theorem leaf_1057_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1057.profileLo box_1057.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1057_ok
theorem branch_box_1057_nonnegative : ∀ j, 0 ≤ branch_box_1057.lower j ∧ 0 ≤ branch_box_1057.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1057, Box.profileLo, Box.profileHi, box_1057]
theorem leaf_1057_BranchSafe : CertificateConsequences.BranchSafe branch_box_1057 := by
  left; refine ⟨branch_box_1057_nonnegative, ?_⟩
  intro z hz; exact leaf_1057_sound hz

theorem leaf_1058_ok : checkAt 527 1000 box_1058 cert_1058 = true := by
  have h := List.all_eq_true.mp batch_21_06_ok accepted_1058 (by simp [batch_21_06_values])
  exact h
theorem leaf_1058_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1058.profileLo box_1058.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1058_ok
theorem branch_box_1058_nonnegative : ∀ j, 0 ≤ branch_box_1058.lower j ∧ 0 ≤ branch_box_1058.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1058, Box.profileLo, Box.profileHi, box_1058]
theorem leaf_1058_BranchSafe : CertificateConsequences.BranchSafe branch_box_1058 := by
  left; refine ⟨branch_box_1058_nonnegative, ?_⟩
  intro z hz; exact leaf_1058_sound hz

theorem leaf_1065_ok : checkAt 527 1000 box_1065 cert_1065 = true := by
  have h := List.all_eq_true.mp batch_21_07_ok accepted_1065 (by simp [batch_21_07_values])
  exact h
theorem leaf_1065_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1065.profileLo box_1065.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1065_ok
theorem branch_box_1065_nonnegative : ∀ j, 0 ≤ branch_box_1065.lower j ∧ 0 ≤ branch_box_1065.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1065, Box.profileLo, Box.profileHi, box_1065]
theorem leaf_1065_BranchSafe : CertificateConsequences.BranchSafe branch_box_1065 := by
  left; refine ⟨branch_box_1065_nonnegative, ?_⟩
  intro z hz; exact leaf_1065_sound hz

theorem leaf_1066_ok : checkAt 527 1000 box_1066 cert_1066 = true := by
  have h := List.all_eq_true.mp batch_21_08_ok accepted_1066 (by simp [batch_21_08_values])
  exact h
theorem leaf_1066_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1066.profileLo box_1066.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1066_ok
theorem branch_box_1066_nonnegative : ∀ j, 0 ≤ branch_box_1066.lower j ∧ 0 ≤ branch_box_1066.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1066, Box.profileLo, Box.profileHi, box_1066]
theorem leaf_1066_BranchSafe : CertificateConsequences.BranchSafe branch_box_1066 := by
  left; refine ⟨branch_box_1066_nonnegative, ?_⟩
  intro z hz; exact leaf_1066_sound hz

theorem leaf_1067_ok : checkAt 527 1000 box_1067 cert_1067 = true := by
  have h := List.all_eq_true.mp batch_21_09_ok accepted_1067 (by simp [batch_21_09_values])
  exact h
theorem leaf_1067_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1067.profileLo box_1067.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1067_ok
theorem branch_box_1067_nonnegative : ∀ j, 0 ≤ branch_box_1067.lower j ∧ 0 ≤ branch_box_1067.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1067, Box.profileLo, Box.profileHi, box_1067]
theorem leaf_1067_BranchSafe : CertificateConsequences.BranchSafe branch_box_1067 := by
  left; refine ⟨branch_box_1067_nonnegative, ?_⟩
  intro z hz; exact leaf_1067_sound hz

theorem leaf_1068_ok : checkAt 527 1000 box_1068 cert_1068 = true := by
  have h := List.all_eq_true.mp batch_21_10_ok accepted_1068 (by simp [batch_21_10_values])
  exact h
theorem leaf_1068_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1068.profileLo box_1068.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1068_ok
theorem branch_box_1068_nonnegative : ∀ j, 0 ≤ branch_box_1068.lower j ∧ 0 ≤ branch_box_1068.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1068, Box.profileLo, Box.profileHi, box_1068]
theorem leaf_1068_BranchSafe : CertificateConsequences.BranchSafe branch_box_1068 := by
  left; refine ⟨branch_box_1068_nonnegative, ?_⟩
  intro z hz; exact leaf_1068_sound hz

theorem leaf_1073_ok : checkAt 527 1000 box_1073 cert_1073 = true := by
  have h := List.all_eq_true.mp batch_21_11_ok accepted_1073 (by simp [batch_21_11_values])
  exact h
theorem leaf_1073_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1073.profileLo box_1073.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1073_ok
theorem branch_box_1073_nonnegative : ∀ j, 0 ≤ branch_box_1073.lower j ∧ 0 ≤ branch_box_1073.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1073, Box.profileLo, Box.profileHi, box_1073]
theorem leaf_1073_BranchSafe : CertificateConsequences.BranchSafe branch_box_1073 := by
  left; refine ⟨branch_box_1073_nonnegative, ?_⟩
  intro z hz; exact leaf_1073_sound hz

theorem leaf_1074_ok : checkAt 527 1000 box_1074 cert_1074 = true := by
  have h := List.all_eq_true.mp batch_21_12_ok accepted_1074 (by simp [batch_21_12_values])
  exact h
theorem leaf_1074_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1074.profileLo box_1074.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1074_ok
theorem branch_box_1074_nonnegative : ∀ j, 0 ≤ branch_box_1074.lower j ∧ 0 ≤ branch_box_1074.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1074, Box.profileLo, Box.profileHi, box_1074]
theorem leaf_1074_BranchSafe : CertificateConsequences.BranchSafe branch_box_1074 := by
  left; refine ⟨branch_box_1074_nonnegative, ?_⟩
  intro z hz; exact leaf_1074_sound hz

theorem leaf_1075_ok : checkAt 527 1000 box_1075 cert_1075 = true := by
  have h := List.all_eq_true.mp batch_21_13_ok accepted_1075 (by simp [batch_21_13_values])
  exact h
theorem leaf_1075_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1075.profileLo box_1075.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1075_ok
theorem branch_box_1075_nonnegative : ∀ j, 0 ≤ branch_box_1075.lower j ∧ 0 ≤ branch_box_1075.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1075, Box.profileLo, Box.profileHi, box_1075]
theorem leaf_1075_BranchSafe : CertificateConsequences.BranchSafe branch_box_1075 := by
  left; refine ⟨branch_box_1075_nonnegative, ?_⟩
  intro z hz; exact leaf_1075_sound hz

theorem leaf_1077_ok : checkAt 527 1000 box_1077 cert_1077 = true := by
  have h := List.all_eq_true.mp batch_21_14_ok accepted_1077 (by simp [batch_21_14_values])
  exact h
theorem leaf_1077_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1077.profileLo box_1077.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1077_ok
theorem branch_box_1077_nonnegative : ∀ j, 0 ≤ branch_box_1077.lower j ∧ 0 ≤ branch_box_1077.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1077, Box.profileLo, Box.profileHi, box_1077]
theorem leaf_1077_BranchSafe : CertificateConsequences.BranchSafe branch_box_1077 := by
  left; refine ⟨branch_box_1077_nonnegative, ?_⟩
  intro z hz; exact leaf_1077_sound hz

theorem leaf_1078_ok : checkAt 527 1000 box_1078 cert_1078 = true := by
  have h := List.all_eq_true.mp batch_21_15_ok accepted_1078 (by simp [batch_21_15_values])
  exact h
theorem leaf_1078_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1078.profileLo box_1078.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1078_ok
theorem branch_box_1078_nonnegative : ∀ j, 0 ≤ branch_box_1078.lower j ∧ 0 ≤ branch_box_1078.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1078, Box.profileLo, Box.profileHi, box_1078]
theorem leaf_1078_BranchSafe : CertificateConsequences.BranchSafe branch_box_1078 := by
  left; refine ⟨branch_box_1078_nonnegative, ?_⟩
  intro z hz; exact leaf_1078_sound hz

theorem leaf_1081_ok : checkAt 527 1000 box_1081 cert_1081 = true := by
  have h := List.all_eq_true.mp batch_21_16_ok accepted_1081 (by simp [batch_21_16_values])
  exact h
theorem leaf_1081_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1081.profileLo box_1081.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1081_ok
theorem branch_box_1081_nonnegative : ∀ j, 0 ≤ branch_box_1081.lower j ∧ 0 ≤ branch_box_1081.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1081, Box.profileLo, Box.profileHi, box_1081]
theorem leaf_1081_BranchSafe : CertificateConsequences.BranchSafe branch_box_1081 := by
  left; refine ⟨branch_box_1081_nonnegative, ?_⟩
  intro z hz; exact leaf_1081_sound hz

theorem leaf_1082_ok : checkAt 527 1000 box_1082 cert_1082 = true := by
  have h := List.all_eq_true.mp batch_21_17_ok accepted_1082 (by simp [batch_21_17_values])
  exact h
theorem leaf_1082_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1082.profileLo box_1082.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1082_ok
theorem branch_box_1082_nonnegative : ∀ j, 0 ≤ branch_box_1082.lower j ∧ 0 ≤ branch_box_1082.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1082, Box.profileLo, Box.profileHi, box_1082]
theorem leaf_1082_BranchSafe : CertificateConsequences.BranchSafe branch_box_1082 := by
  left; refine ⟨branch_box_1082_nonnegative, ?_⟩
  intro z hz; exact leaf_1082_sound hz

theorem leaf_1083_ok : checkAt 527 1000 box_1083 cert_1083 = true := by
  have h := List.all_eq_true.mp batch_21_18_ok accepted_1083 (by simp [batch_21_18_values])
  exact h
theorem leaf_1083_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1083.profileLo box_1083.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1083_ok
theorem branch_box_1083_nonnegative : ∀ j, 0 ≤ branch_box_1083.lower j ∧ 0 ≤ branch_box_1083.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1083, Box.profileLo, Box.profileHi, box_1083]
theorem leaf_1083_BranchSafe : CertificateConsequences.BranchSafe branch_box_1083 := by
  left; refine ⟨branch_box_1083_nonnegative, ?_⟩
  intro z hz; exact leaf_1083_sound hz

theorem leaf_1085_ok : checkAt 527 1000 box_1085 cert_1085 = true := by
  have h := List.all_eq_true.mp batch_21_19_ok accepted_1085 (by simp [batch_21_19_values])
  exact h
theorem leaf_1085_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1085.profileLo box_1085.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1085_ok
theorem branch_box_1085_nonnegative : ∀ j, 0 ≤ branch_box_1085.lower j ∧ 0 ≤ branch_box_1085.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1085, Box.profileLo, Box.profileHi, box_1085]
theorem leaf_1085_BranchSafe : CertificateConsequences.BranchSafe branch_box_1085 := by
  left; refine ⟨branch_box_1085_nonnegative, ?_⟩
  intro z hz; exact leaf_1085_sound hz

theorem leaf_1086_ok : checkAt 527 1000 box_1086 cert_1086 = true := by
  have h := List.all_eq_true.mp batch_21_20_ok accepted_1086 (by simp [batch_21_20_values])
  exact h
theorem leaf_1086_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1086.profileLo box_1086.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1086_ok
theorem branch_box_1086_nonnegative : ∀ j, 0 ≤ branch_box_1086.lower j ∧ 0 ≤ branch_box_1086.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1086, Box.profileLo, Box.profileHi, box_1086]
theorem leaf_1086_BranchSafe : CertificateConsequences.BranchSafe branch_box_1086 := by
  left; refine ⟨branch_box_1086_nonnegative, ?_⟩
  intro z hz; exact leaf_1086_sound hz

theorem leaf_1090_ok : checkAt 527 1000 box_1090 cert_1090 = true := by
  have h := List.all_eq_true.mp batch_21_21_ok accepted_1090 (by simp [batch_21_21_values])
  exact h
theorem leaf_1090_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1090.profileLo box_1090.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1090_ok
theorem branch_box_1090_nonnegative : ∀ j, 0 ≤ branch_box_1090.lower j ∧ 0 ≤ branch_box_1090.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1090, Box.profileLo, Box.profileHi, box_1090]
theorem leaf_1090_BranchSafe : CertificateConsequences.BranchSafe branch_box_1090 := by
  left; refine ⟨branch_box_1090_nonnegative, ?_⟩
  intro z hz; exact leaf_1090_sound hz

theorem leaf_1091_ok : checkAt 527 1000 box_1091 cert_1091 = true := by
  have h := List.all_eq_true.mp batch_21_22_ok accepted_1091 (by simp [batch_21_22_values])
  exact h
theorem leaf_1091_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1091.profileLo box_1091.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1091_ok
theorem branch_box_1091_nonnegative : ∀ j, 0 ≤ branch_box_1091.lower j ∧ 0 ≤ branch_box_1091.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1091, Box.profileLo, Box.profileHi, box_1091]
theorem leaf_1091_BranchSafe : CertificateConsequences.BranchSafe branch_box_1091 := by
  left; refine ⟨branch_box_1091_nonnegative, ?_⟩
  intro z hz; exact leaf_1091_sound hz

theorem leaf_1092_ok : checkAt 527 1000 box_1092 cert_1092 = true := by
  have h := List.all_eq_true.mp batch_21_23_ok accepted_1092 (by simp [batch_21_23_values])
  exact h
theorem leaf_1092_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1092.profileLo box_1092.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1092_ok
theorem branch_box_1092_nonnegative : ∀ j, 0 ≤ branch_box_1092.lower j ∧ 0 ≤ branch_box_1092.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1092, Box.profileLo, Box.profileHi, box_1092]
theorem leaf_1092_BranchSafe : CertificateConsequences.BranchSafe branch_box_1092 := by
  left; refine ⟨branch_box_1092_nonnegative, ?_⟩
  intro z hz; exact leaf_1092_sound hz

theorem leaf_1093_ok : checkAt 527 1000 box_1093 cert_1093 = true := by
  have h := List.all_eq_true.mp batch_21_24_ok accepted_1093 (by simp [batch_21_24_values])
  exact h
theorem leaf_1093_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1093.profileLo box_1093.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1093_ok
theorem branch_box_1093_nonnegative : ∀ j, 0 ≤ branch_box_1093.lower j ∧ 0 ≤ branch_box_1093.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1093, Box.profileLo, Box.profileHi, box_1093]
theorem leaf_1093_BranchSafe : CertificateConsequences.BranchSafe branch_box_1093 := by
  left; refine ⟨branch_box_1093_nonnegative, ?_⟩
  intro z hz; exact leaf_1093_sound hz

theorem leaf_1094_ok : checkAt 527 1000 box_1094 cert_1094 = true := by
  have h := List.all_eq_true.mp batch_21_25_ok accepted_1094 (by simp [batch_21_25_values])
  exact h
theorem leaf_1094_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1094.profileLo box_1094.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1094_ok
theorem branch_box_1094_nonnegative : ∀ j, 0 ≤ branch_box_1094.lower j ∧ 0 ≤ branch_box_1094.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1094, Box.profileLo, Box.profileHi, box_1094]
theorem leaf_1094_BranchSafe : CertificateConsequences.BranchSafe branch_box_1094 := by
  left; refine ⟨branch_box_1094_nonnegative, ?_⟩
  intro z hz; exact leaf_1094_sound hz

#print axioms batch_21_00_ok
#print axioms leaf_1050_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
