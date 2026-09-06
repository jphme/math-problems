import PeaceableQueens.UpperBound.Generated.Even.CoreScaled21Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_21_00_values : List Bool := [accepted_1052]
theorem batch_21_00_ok : batch_21_00_values.all id = true := by decide

def batch_21_01_values : List Bool := [accepted_1053]
theorem batch_21_01_ok : batch_21_01_values.all id = true := by decide

def batch_21_02_values : List Bool := [accepted_1055]
theorem batch_21_02_ok : batch_21_02_values.all id = true := by decide

def batch_21_03_values : List Bool := [accepted_1057]
theorem batch_21_03_ok : batch_21_03_values.all id = true := by decide

def batch_21_04_values : List Bool := [accepted_1060]
theorem batch_21_04_ok : batch_21_04_values.all id = true := by decide

def batch_21_05_values : List Bool := [accepted_1062]
theorem batch_21_05_ok : batch_21_05_values.all id = true := by decide

def batch_21_06_values : List Bool := [accepted_1063]
theorem batch_21_06_ok : batch_21_06_values.all id = true := by decide

def batch_21_07_values : List Bool := [accepted_1065]
theorem batch_21_07_ok : batch_21_07_values.all id = true := by decide

def batch_21_08_values : List Bool := [accepted_1067]
theorem batch_21_08_ok : batch_21_08_values.all id = true := by decide

def batch_21_09_values : List Bool := [accepted_1072]
theorem batch_21_09_ok : batch_21_09_values.all id = true := by decide

def batch_21_10_values : List Bool := [accepted_1073]
theorem batch_21_10_ok : batch_21_10_values.all id = true := by decide

def batch_21_11_values : List Bool := [accepted_1076]
theorem batch_21_11_ok : batch_21_11_values.all id = true := by decide

def batch_21_12_values : List Bool := [accepted_1078]
theorem batch_21_12_ok : batch_21_12_values.all id = true := by decide

def batch_21_13_values : List Bool := [accepted_1079]
theorem batch_21_13_ok : batch_21_13_values.all id = true := by decide

def batch_21_14_values : List Bool := [accepted_1082]
theorem batch_21_14_ok : batch_21_14_values.all id = true := by decide

def batch_21_15_values : List Bool := [accepted_1084]
theorem batch_21_15_ok : batch_21_15_values.all id = true := by decide

def batch_21_16_values : List Bool := [accepted_1086]
theorem batch_21_16_ok : batch_21_16_values.all id = true := by decide

def batch_21_17_values : List Bool := [accepted_1087]
theorem batch_21_17_ok : batch_21_17_values.all id = true := by decide

def batch_21_18_values : List Bool := [accepted_1089]
theorem batch_21_18_ok : batch_21_18_values.all id = true := by decide

def batch_21_19_values : List Bool := [accepted_1091]
theorem batch_21_19_ok : batch_21_19_values.all id = true := by decide

def batch_21_20_values : List Bool := [accepted_1096]
theorem batch_21_20_ok : batch_21_20_values.all id = true := by decide

def batch_21_21_values : List Bool := [accepted_1098]
theorem batch_21_21_ok : batch_21_21_values.all id = true := by decide

theorem leaf_1052_ok : checkAt 527 1000 box_1052 cert_1052 = true := by
  have h := List.all_eq_true.mp batch_21_00_ok accepted_1052 (by simp [batch_21_00_values])
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
  have h := List.all_eq_true.mp batch_21_01_ok accepted_1053 (by simp [batch_21_01_values])
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

theorem leaf_1055_ok : checkAt 527 1000 box_1055 cert_1055 = true := by
  have h := List.all_eq_true.mp batch_21_02_ok accepted_1055 (by simp [batch_21_02_values])
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
  have h := List.all_eq_true.mp batch_21_03_ok accepted_1057 (by simp [batch_21_03_values])
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

theorem leaf_1060_ok : checkAt 527 1000 box_1060 cert_1060 = true := by
  have h := List.all_eq_true.mp batch_21_04_ok accepted_1060 (by simp [batch_21_04_values])
  exact h
theorem leaf_1060_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1060.profileLo box_1060.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1060_ok
theorem branch_box_1060_nonnegative : ∀ j, 0 ≤ branch_box_1060.lower j ∧ 0 ≤ branch_box_1060.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1060, Box.profileLo, Box.profileHi, box_1060]
theorem leaf_1060_BranchSafe : CertificateConsequences.BranchSafe branch_box_1060 := by
  left; refine ⟨branch_box_1060_nonnegative, ?_⟩
  intro z hz; exact leaf_1060_sound hz

theorem leaf_1062_ok : checkAt 527 1000 box_1062 cert_1062 = true := by
  have h := List.all_eq_true.mp batch_21_05_ok accepted_1062 (by simp [batch_21_05_values])
  exact h
theorem leaf_1062_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1062.profileLo box_1062.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1062_ok
theorem branch_box_1062_nonnegative : ∀ j, 0 ≤ branch_box_1062.lower j ∧ 0 ≤ branch_box_1062.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1062, Box.profileLo, Box.profileHi, box_1062]
theorem leaf_1062_BranchSafe : CertificateConsequences.BranchSafe branch_box_1062 := by
  left; refine ⟨branch_box_1062_nonnegative, ?_⟩
  intro z hz; exact leaf_1062_sound hz

theorem leaf_1063_ok : checkAt 527 1000 box_1063 cert_1063 = true := by
  have h := List.all_eq_true.mp batch_21_06_ok accepted_1063 (by simp [batch_21_06_values])
  exact h
theorem leaf_1063_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1063.profileLo box_1063.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1063_ok
theorem branch_box_1063_nonnegative : ∀ j, 0 ≤ branch_box_1063.lower j ∧ 0 ≤ branch_box_1063.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1063, Box.profileLo, Box.profileHi, box_1063]
theorem leaf_1063_BranchSafe : CertificateConsequences.BranchSafe branch_box_1063 := by
  left; refine ⟨branch_box_1063_nonnegative, ?_⟩
  intro z hz; exact leaf_1063_sound hz

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

theorem leaf_1067_ok : checkAt 527 1000 box_1067 cert_1067 = true := by
  have h := List.all_eq_true.mp batch_21_08_ok accepted_1067 (by simp [batch_21_08_values])
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

theorem leaf_1072_ok : checkAt 527 1000 box_1072 cert_1072 = true := by
  have h := List.all_eq_true.mp batch_21_09_ok accepted_1072 (by simp [batch_21_09_values])
  exact h
theorem leaf_1072_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1072.profileLo box_1072.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1072_ok
theorem branch_box_1072_nonnegative : ∀ j, 0 ≤ branch_box_1072.lower j ∧ 0 ≤ branch_box_1072.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1072, Box.profileLo, Box.profileHi, box_1072]
theorem leaf_1072_BranchSafe : CertificateConsequences.BranchSafe branch_box_1072 := by
  left; refine ⟨branch_box_1072_nonnegative, ?_⟩
  intro z hz; exact leaf_1072_sound hz

theorem leaf_1073_ok : checkAt 527 1000 box_1073 cert_1073 = true := by
  have h := List.all_eq_true.mp batch_21_10_ok accepted_1073 (by simp [batch_21_10_values])
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

theorem leaf_1076_ok : checkAt 527 1000 box_1076 cert_1076 = true := by
  have h := List.all_eq_true.mp batch_21_11_ok accepted_1076 (by simp [batch_21_11_values])
  exact h
theorem leaf_1076_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1076.profileLo box_1076.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1076_ok
theorem branch_box_1076_nonnegative : ∀ j, 0 ≤ branch_box_1076.lower j ∧ 0 ≤ branch_box_1076.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1076, Box.profileLo, Box.profileHi, box_1076]
theorem leaf_1076_BranchSafe : CertificateConsequences.BranchSafe branch_box_1076 := by
  left; refine ⟨branch_box_1076_nonnegative, ?_⟩
  intro z hz; exact leaf_1076_sound hz

theorem leaf_1078_ok : checkAt 527 1000 box_1078 cert_1078 = true := by
  have h := List.all_eq_true.mp batch_21_12_ok accepted_1078 (by simp [batch_21_12_values])
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

theorem leaf_1079_ok : checkAt 527 1000 box_1079 cert_1079 = true := by
  have h := List.all_eq_true.mp batch_21_13_ok accepted_1079 (by simp [batch_21_13_values])
  exact h
theorem leaf_1079_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1079.profileLo box_1079.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1079_ok
theorem branch_box_1079_nonnegative : ∀ j, 0 ≤ branch_box_1079.lower j ∧ 0 ≤ branch_box_1079.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1079, Box.profileLo, Box.profileHi, box_1079]
theorem leaf_1079_BranchSafe : CertificateConsequences.BranchSafe branch_box_1079 := by
  left; refine ⟨branch_box_1079_nonnegative, ?_⟩
  intro z hz; exact leaf_1079_sound hz

theorem leaf_1082_ok : checkAt 527 1000 box_1082 cert_1082 = true := by
  have h := List.all_eq_true.mp batch_21_14_ok accepted_1082 (by simp [batch_21_14_values])
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

theorem leaf_1084_ok : checkAt 527 1000 box_1084 cert_1084 = true := by
  have h := List.all_eq_true.mp batch_21_15_ok accepted_1084 (by simp [batch_21_15_values])
  exact h
theorem leaf_1084_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1084.profileLo box_1084.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1084_ok
theorem branch_box_1084_nonnegative : ∀ j, 0 ≤ branch_box_1084.lower j ∧ 0 ≤ branch_box_1084.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1084, Box.profileLo, Box.profileHi, box_1084]
theorem leaf_1084_BranchSafe : CertificateConsequences.BranchSafe branch_box_1084 := by
  left; refine ⟨branch_box_1084_nonnegative, ?_⟩
  intro z hz; exact leaf_1084_sound hz

theorem leaf_1086_ok : checkAt 527 1000 box_1086 cert_1086 = true := by
  have h := List.all_eq_true.mp batch_21_16_ok accepted_1086 (by simp [batch_21_16_values])
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

theorem leaf_1087_ok : checkAt 527 1000 box_1087 cert_1087 = true := by
  have h := List.all_eq_true.mp batch_21_17_ok accepted_1087 (by simp [batch_21_17_values])
  exact h
theorem leaf_1087_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1087.profileLo box_1087.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1087_ok
theorem branch_box_1087_nonnegative : ∀ j, 0 ≤ branch_box_1087.lower j ∧ 0 ≤ branch_box_1087.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1087, Box.profileLo, Box.profileHi, box_1087]
theorem leaf_1087_BranchSafe : CertificateConsequences.BranchSafe branch_box_1087 := by
  left; refine ⟨branch_box_1087_nonnegative, ?_⟩
  intro z hz; exact leaf_1087_sound hz

theorem leaf_1089_ok : checkAt 527 1000 box_1089 cert_1089 = true := by
  have h := List.all_eq_true.mp batch_21_18_ok accepted_1089 (by simp [batch_21_18_values])
  exact h
theorem leaf_1089_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1089.profileLo box_1089.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1089_ok
theorem branch_box_1089_nonnegative : ∀ j, 0 ≤ branch_box_1089.lower j ∧ 0 ≤ branch_box_1089.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1089, Box.profileLo, Box.profileHi, box_1089]
theorem leaf_1089_BranchSafe : CertificateConsequences.BranchSafe branch_box_1089 := by
  left; refine ⟨branch_box_1089_nonnegative, ?_⟩
  intro z hz; exact leaf_1089_sound hz

theorem leaf_1091_ok : checkAt 527 1000 box_1091 cert_1091 = true := by
  have h := List.all_eq_true.mp batch_21_19_ok accepted_1091 (by simp [batch_21_19_values])
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

theorem leaf_1096_ok : checkAt 527 1000 box_1096 cert_1096 = true := by
  have h := List.all_eq_true.mp batch_21_20_ok accepted_1096 (by simp [batch_21_20_values])
  exact h
theorem leaf_1096_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1096.profileLo box_1096.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1096_ok
theorem branch_box_1096_nonnegative : ∀ j, 0 ≤ branch_box_1096.lower j ∧ 0 ≤ branch_box_1096.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1096, Box.profileLo, Box.profileHi, box_1096]
theorem leaf_1096_BranchSafe : CertificateConsequences.BranchSafe branch_box_1096 := by
  left; refine ⟨branch_box_1096_nonnegative, ?_⟩
  intro z hz; exact leaf_1096_sound hz

theorem leaf_1098_ok : checkAt 527 1000 box_1098 cert_1098 = true := by
  have h := List.all_eq_true.mp batch_21_21_ok accepted_1098 (by simp [batch_21_21_values])
  exact h
theorem leaf_1098_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1098.profileLo box_1098.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1098_ok
theorem branch_box_1098_nonnegative : ∀ j, 0 ≤ branch_box_1098.lower j ∧ 0 ≤ branch_box_1098.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1098, Box.profileLo, Box.profileHi, box_1098]
theorem leaf_1098_BranchSafe : CertificateConsequences.BranchSafe branch_box_1098 := by
  left; refine ⟨branch_box_1098_nonnegative, ?_⟩
  intro z hz; exact leaf_1098_sound hz

#print axioms batch_21_00_ok
#print axioms leaf_1052_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
