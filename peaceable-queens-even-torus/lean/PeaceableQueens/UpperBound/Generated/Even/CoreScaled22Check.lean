import PeaceableQueens.UpperBound.Generated.Even.CoreScaled22Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_22_00_values : List Bool := [accepted_1100]
theorem batch_22_00_ok : batch_22_00_values.all id = true := by decide

def batch_22_01_values : List Bool := [accepted_1101]
theorem batch_22_01_ok : batch_22_01_values.all id = true := by decide

def batch_22_02_values : List Bool := [accepted_1103]
theorem batch_22_02_ok : batch_22_02_values.all id = true := by decide

def batch_22_03_values : List Bool := [accepted_1105]
theorem batch_22_03_ok : batch_22_03_values.all id = true := by decide

def batch_22_04_values : List Bool := [accepted_1108]
theorem batch_22_04_ok : batch_22_04_values.all id = true := by decide

def batch_22_05_values : List Bool := [accepted_1110]
theorem batch_22_05_ok : batch_22_05_values.all id = true := by decide

def batch_22_06_values : List Bool := [accepted_1112]
theorem batch_22_06_ok : batch_22_06_values.all id = true := by decide

def batch_22_07_values : List Bool := [accepted_1114]
theorem batch_22_07_ok : batch_22_07_values.all id = true := by decide

def batch_22_08_values : List Bool := [accepted_1116]
theorem batch_22_08_ok : batch_22_08_values.all id = true := by decide

def batch_22_09_values : List Bool := [accepted_1117]
theorem batch_22_09_ok : batch_22_09_values.all id = true := by decide

def batch_22_10_values : List Bool := [accepted_1120]
theorem batch_22_10_ok : batch_22_10_values.all id = true := by decide

def batch_22_11_values : List Bool := [accepted_1122]
theorem batch_22_11_ok : batch_22_11_values.all id = true := by decide

def batch_22_12_values : List Bool := [accepted_1126]
theorem batch_22_12_ok : batch_22_12_values.all id = true := by decide

def batch_22_13_values : List Bool := [accepted_1128]
theorem batch_22_13_ok : batch_22_13_values.all id = true := by decide

def batch_22_14_values : List Bool := [accepted_1130]
theorem batch_22_14_ok : batch_22_14_values.all id = true := by decide

def batch_22_15_values : List Bool := [accepted_1138]
theorem batch_22_15_ok : batch_22_15_values.all id = true := by decide

def batch_22_16_values : List Bool := [accepted_1140]
theorem batch_22_16_ok : batch_22_16_values.all id = true := by decide

def batch_22_17_values : List Bool := [accepted_1141]
theorem batch_22_17_ok : batch_22_17_values.all id = true := by decide

def batch_22_18_values : List Bool := [accepted_1143]
theorem batch_22_18_ok : batch_22_18_values.all id = true := by decide

def batch_22_19_values : List Bool := [accepted_1145]
theorem batch_22_19_ok : batch_22_19_values.all id = true := by decide

def batch_22_20_values : List Bool := [accepted_1147]
theorem batch_22_20_ok : batch_22_20_values.all id = true := by decide

theorem leaf_1100_ok : checkAt 527 1000 box_1100 cert_1100 = true := by
  have h := List.all_eq_true.mp batch_22_00_ok accepted_1100 (by simp [batch_22_00_values])
  exact h
theorem leaf_1100_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1100.profileLo box_1100.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1100_ok
theorem branch_box_1100_nonnegative : ∀ j, 0 ≤ branch_box_1100.lower j ∧ 0 ≤ branch_box_1100.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1100, Box.profileLo, Box.profileHi, box_1100]
theorem leaf_1100_BranchSafe : CertificateConsequences.BranchSafe branch_box_1100 := by
  left; refine ⟨branch_box_1100_nonnegative, ?_⟩
  intro z hz; exact leaf_1100_sound hz

theorem leaf_1101_ok : checkAt 527 1000 box_1101 cert_1101 = true := by
  have h := List.all_eq_true.mp batch_22_01_ok accepted_1101 (by simp [batch_22_01_values])
  exact h
theorem leaf_1101_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1101.profileLo box_1101.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1101_ok
theorem branch_box_1101_nonnegative : ∀ j, 0 ≤ branch_box_1101.lower j ∧ 0 ≤ branch_box_1101.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1101, Box.profileLo, Box.profileHi, box_1101]
theorem leaf_1101_BranchSafe : CertificateConsequences.BranchSafe branch_box_1101 := by
  left; refine ⟨branch_box_1101_nonnegative, ?_⟩
  intro z hz; exact leaf_1101_sound hz

theorem leaf_1103_ok : checkAt 527 1000 box_1103 cert_1103 = true := by
  have h := List.all_eq_true.mp batch_22_02_ok accepted_1103 (by simp [batch_22_02_values])
  exact h
theorem leaf_1103_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1103.profileLo box_1103.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1103_ok
theorem branch_box_1103_nonnegative : ∀ j, 0 ≤ branch_box_1103.lower j ∧ 0 ≤ branch_box_1103.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1103, Box.profileLo, Box.profileHi, box_1103]
theorem leaf_1103_BranchSafe : CertificateConsequences.BranchSafe branch_box_1103 := by
  left; refine ⟨branch_box_1103_nonnegative, ?_⟩
  intro z hz; exact leaf_1103_sound hz

theorem leaf_1105_ok : checkAt 527 1000 box_1105 cert_1105 = true := by
  have h := List.all_eq_true.mp batch_22_03_ok accepted_1105 (by simp [batch_22_03_values])
  exact h
theorem leaf_1105_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1105.profileLo box_1105.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1105_ok
theorem branch_box_1105_nonnegative : ∀ j, 0 ≤ branch_box_1105.lower j ∧ 0 ≤ branch_box_1105.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1105, Box.profileLo, Box.profileHi, box_1105]
theorem leaf_1105_BranchSafe : CertificateConsequences.BranchSafe branch_box_1105 := by
  left; refine ⟨branch_box_1105_nonnegative, ?_⟩
  intro z hz; exact leaf_1105_sound hz

theorem leaf_1108_ok : checkAt 527 1000 box_1108 cert_1108 = true := by
  have h := List.all_eq_true.mp batch_22_04_ok accepted_1108 (by simp [batch_22_04_values])
  exact h
theorem leaf_1108_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1108.profileLo box_1108.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1108_ok
theorem branch_box_1108_nonnegative : ∀ j, 0 ≤ branch_box_1108.lower j ∧ 0 ≤ branch_box_1108.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1108, Box.profileLo, Box.profileHi, box_1108]
theorem leaf_1108_BranchSafe : CertificateConsequences.BranchSafe branch_box_1108 := by
  left; refine ⟨branch_box_1108_nonnegative, ?_⟩
  intro z hz; exact leaf_1108_sound hz

theorem leaf_1110_ok : checkAt 527 1000 box_1110 cert_1110 = true := by
  have h := List.all_eq_true.mp batch_22_05_ok accepted_1110 (by simp [batch_22_05_values])
  exact h
theorem leaf_1110_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1110.profileLo box_1110.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1110_ok
theorem branch_box_1110_nonnegative : ∀ j, 0 ≤ branch_box_1110.lower j ∧ 0 ≤ branch_box_1110.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1110, Box.profileLo, Box.profileHi, box_1110]
theorem leaf_1110_BranchSafe : CertificateConsequences.BranchSafe branch_box_1110 := by
  left; refine ⟨branch_box_1110_nonnegative, ?_⟩
  intro z hz; exact leaf_1110_sound hz

theorem leaf_1112_ok : checkAt 527 1000 box_1112 cert_1112 = true := by
  have h := List.all_eq_true.mp batch_22_06_ok accepted_1112 (by simp [batch_22_06_values])
  exact h
theorem leaf_1112_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1112.profileLo box_1112.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1112_ok
theorem branch_box_1112_nonnegative : ∀ j, 0 ≤ branch_box_1112.lower j ∧ 0 ≤ branch_box_1112.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1112, Box.profileLo, Box.profileHi, box_1112]
theorem leaf_1112_BranchSafe : CertificateConsequences.BranchSafe branch_box_1112 := by
  left; refine ⟨branch_box_1112_nonnegative, ?_⟩
  intro z hz; exact leaf_1112_sound hz

theorem leaf_1114_ok : checkAt 527 1000 box_1114 cert_1114 = true := by
  have h := List.all_eq_true.mp batch_22_07_ok accepted_1114 (by simp [batch_22_07_values])
  exact h
theorem leaf_1114_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1114.profileLo box_1114.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1114_ok
theorem branch_box_1114_nonnegative : ∀ j, 0 ≤ branch_box_1114.lower j ∧ 0 ≤ branch_box_1114.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1114, Box.profileLo, Box.profileHi, box_1114]
theorem leaf_1114_BranchSafe : CertificateConsequences.BranchSafe branch_box_1114 := by
  left; refine ⟨branch_box_1114_nonnegative, ?_⟩
  intro z hz; exact leaf_1114_sound hz

theorem leaf_1116_ok : checkAt 527 1000 box_1116 cert_1116 = true := by
  have h := List.all_eq_true.mp batch_22_08_ok accepted_1116 (by simp [batch_22_08_values])
  exact h
theorem leaf_1116_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1116.profileLo box_1116.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1116_ok
theorem branch_box_1116_nonnegative : ∀ j, 0 ≤ branch_box_1116.lower j ∧ 0 ≤ branch_box_1116.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1116, Box.profileLo, Box.profileHi, box_1116]
theorem leaf_1116_BranchSafe : CertificateConsequences.BranchSafe branch_box_1116 := by
  left; refine ⟨branch_box_1116_nonnegative, ?_⟩
  intro z hz; exact leaf_1116_sound hz

theorem leaf_1117_ok : checkAt 527 1000 box_1117 cert_1117 = true := by
  have h := List.all_eq_true.mp batch_22_09_ok accepted_1117 (by simp [batch_22_09_values])
  exact h
theorem leaf_1117_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1117.profileLo box_1117.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1117_ok
theorem branch_box_1117_nonnegative : ∀ j, 0 ≤ branch_box_1117.lower j ∧ 0 ≤ branch_box_1117.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1117, Box.profileLo, Box.profileHi, box_1117]
theorem leaf_1117_BranchSafe : CertificateConsequences.BranchSafe branch_box_1117 := by
  left; refine ⟨branch_box_1117_nonnegative, ?_⟩
  intro z hz; exact leaf_1117_sound hz

theorem leaf_1120_ok : checkAt 527 1000 box_1120 cert_1120 = true := by
  have h := List.all_eq_true.mp batch_22_10_ok accepted_1120 (by simp [batch_22_10_values])
  exact h
theorem leaf_1120_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1120.profileLo box_1120.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1120_ok
theorem branch_box_1120_nonnegative : ∀ j, 0 ≤ branch_box_1120.lower j ∧ 0 ≤ branch_box_1120.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1120, Box.profileLo, Box.profileHi, box_1120]
theorem leaf_1120_BranchSafe : CertificateConsequences.BranchSafe branch_box_1120 := by
  left; refine ⟨branch_box_1120_nonnegative, ?_⟩
  intro z hz; exact leaf_1120_sound hz

theorem leaf_1122_ok : checkAt 527 1000 box_1122 cert_1122 = true := by
  have h := List.all_eq_true.mp batch_22_11_ok accepted_1122 (by simp [batch_22_11_values])
  exact h
theorem leaf_1122_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1122.profileLo box_1122.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1122_ok
theorem branch_box_1122_nonnegative : ∀ j, 0 ≤ branch_box_1122.lower j ∧ 0 ≤ branch_box_1122.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1122, Box.profileLo, Box.profileHi, box_1122]
theorem leaf_1122_BranchSafe : CertificateConsequences.BranchSafe branch_box_1122 := by
  left; refine ⟨branch_box_1122_nonnegative, ?_⟩
  intro z hz; exact leaf_1122_sound hz

theorem leaf_1126_ok : checkAt 527 1000 box_1126 cert_1126 = true := by
  have h := List.all_eq_true.mp batch_22_12_ok accepted_1126 (by simp [batch_22_12_values])
  exact h
theorem leaf_1126_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1126.profileLo box_1126.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1126_ok
theorem branch_box_1126_nonnegative : ∀ j, 0 ≤ branch_box_1126.lower j ∧ 0 ≤ branch_box_1126.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1126, Box.profileLo, Box.profileHi, box_1126]
theorem leaf_1126_BranchSafe : CertificateConsequences.BranchSafe branch_box_1126 := by
  left; refine ⟨branch_box_1126_nonnegative, ?_⟩
  intro z hz; exact leaf_1126_sound hz

theorem leaf_1128_ok : checkAt 527 1000 box_1128 cert_1128 = true := by
  have h := List.all_eq_true.mp batch_22_13_ok accepted_1128 (by simp [batch_22_13_values])
  exact h
theorem leaf_1128_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1128.profileLo box_1128.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1128_ok
theorem branch_box_1128_nonnegative : ∀ j, 0 ≤ branch_box_1128.lower j ∧ 0 ≤ branch_box_1128.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1128, Box.profileLo, Box.profileHi, box_1128]
theorem leaf_1128_BranchSafe : CertificateConsequences.BranchSafe branch_box_1128 := by
  left; refine ⟨branch_box_1128_nonnegative, ?_⟩
  intro z hz; exact leaf_1128_sound hz

theorem leaf_1130_ok : checkAt 527 1000 box_1130 cert_1130 = true := by
  have h := List.all_eq_true.mp batch_22_14_ok accepted_1130 (by simp [batch_22_14_values])
  exact h
theorem leaf_1130_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1130.profileLo box_1130.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1130_ok
theorem branch_box_1130_nonnegative : ∀ j, 0 ≤ branch_box_1130.lower j ∧ 0 ≤ branch_box_1130.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1130, Box.profileLo, Box.profileHi, box_1130]
theorem leaf_1130_BranchSafe : CertificateConsequences.BranchSafe branch_box_1130 := by
  left; refine ⟨branch_box_1130_nonnegative, ?_⟩
  intro z hz; exact leaf_1130_sound hz

theorem leaf_1138_ok : checkAt 527 1000 box_1138 cert_1138 = true := by
  have h := List.all_eq_true.mp batch_22_15_ok accepted_1138 (by simp [batch_22_15_values])
  exact h
theorem leaf_1138_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1138.profileLo box_1138.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1138_ok
theorem branch_box_1138_nonnegative : ∀ j, 0 ≤ branch_box_1138.lower j ∧ 0 ≤ branch_box_1138.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1138, Box.profileLo, Box.profileHi, box_1138]
theorem leaf_1138_BranchSafe : CertificateConsequences.BranchSafe branch_box_1138 := by
  left; refine ⟨branch_box_1138_nonnegative, ?_⟩
  intro z hz; exact leaf_1138_sound hz

theorem leaf_1140_ok : checkAt 527 1000 box_1140 cert_1140 = true := by
  have h := List.all_eq_true.mp batch_22_16_ok accepted_1140 (by simp [batch_22_16_values])
  exact h
theorem leaf_1140_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1140.profileLo box_1140.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1140_ok
theorem branch_box_1140_nonnegative : ∀ j, 0 ≤ branch_box_1140.lower j ∧ 0 ≤ branch_box_1140.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1140, Box.profileLo, Box.profileHi, box_1140]
theorem leaf_1140_BranchSafe : CertificateConsequences.BranchSafe branch_box_1140 := by
  left; refine ⟨branch_box_1140_nonnegative, ?_⟩
  intro z hz; exact leaf_1140_sound hz

theorem leaf_1141_ok : checkAt 527 1000 box_1141 cert_1141 = true := by
  have h := List.all_eq_true.mp batch_22_17_ok accepted_1141 (by simp [batch_22_17_values])
  exact h
theorem leaf_1141_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1141.profileLo box_1141.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1141_ok
theorem branch_box_1141_nonnegative : ∀ j, 0 ≤ branch_box_1141.lower j ∧ 0 ≤ branch_box_1141.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1141, Box.profileLo, Box.profileHi, box_1141]
theorem leaf_1141_BranchSafe : CertificateConsequences.BranchSafe branch_box_1141 := by
  left; refine ⟨branch_box_1141_nonnegative, ?_⟩
  intro z hz; exact leaf_1141_sound hz

theorem leaf_1143_ok : checkAt 527 1000 box_1143 cert_1143 = true := by
  have h := List.all_eq_true.mp batch_22_18_ok accepted_1143 (by simp [batch_22_18_values])
  exact h
theorem leaf_1143_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1143.profileLo box_1143.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1143_ok
theorem branch_box_1143_nonnegative : ∀ j, 0 ≤ branch_box_1143.lower j ∧ 0 ≤ branch_box_1143.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1143, Box.profileLo, Box.profileHi, box_1143]
theorem leaf_1143_BranchSafe : CertificateConsequences.BranchSafe branch_box_1143 := by
  left; refine ⟨branch_box_1143_nonnegative, ?_⟩
  intro z hz; exact leaf_1143_sound hz

theorem leaf_1145_ok : checkAt 527 1000 box_1145 cert_1145 = true := by
  have h := List.all_eq_true.mp batch_22_19_ok accepted_1145 (by simp [batch_22_19_values])
  exact h
theorem leaf_1145_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1145.profileLo box_1145.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1145_ok
theorem branch_box_1145_nonnegative : ∀ j, 0 ≤ branch_box_1145.lower j ∧ 0 ≤ branch_box_1145.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1145, Box.profileLo, Box.profileHi, box_1145]
theorem leaf_1145_BranchSafe : CertificateConsequences.BranchSafe branch_box_1145 := by
  left; refine ⟨branch_box_1145_nonnegative, ?_⟩
  intro z hz; exact leaf_1145_sound hz

theorem leaf_1147_ok : checkAt 527 1000 box_1147 cert_1147 = true := by
  have h := List.all_eq_true.mp batch_22_20_ok accepted_1147 (by simp [batch_22_20_values])
  exact h
theorem leaf_1147_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1147.profileLo box_1147.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1147_ok
theorem branch_box_1147_nonnegative : ∀ j, 0 ≤ branch_box_1147.lower j ∧ 0 ≤ branch_box_1147.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1147, Box.profileLo, Box.profileHi, box_1147]
theorem leaf_1147_BranchSafe : CertificateConsequences.BranchSafe branch_box_1147 := by
  left; refine ⟨branch_box_1147_nonnegative, ?_⟩
  intro z hz; exact leaf_1147_sound hz

#print axioms batch_22_00_ok
#print axioms leaf_1100_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
