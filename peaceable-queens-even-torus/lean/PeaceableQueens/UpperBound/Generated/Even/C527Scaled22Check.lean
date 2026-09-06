import PeaceableQueens.UpperBound.Generated.Even.C527Scaled22Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_22_00_values : List Bool := [accepted_1103]
theorem batch_22_00_ok : batch_22_00_values.all id = true := by decide

def batch_22_01_values : List Bool := [accepted_1104]
theorem batch_22_01_ok : batch_22_01_values.all id = true := by decide

def batch_22_02_values : List Bool := [accepted_1105]
theorem batch_22_02_ok : batch_22_02_values.all id = true := by decide

def batch_22_03_values : List Bool := [accepted_1106]
theorem batch_22_03_ok : batch_22_03_values.all id = true := by decide

def batch_22_04_values : List Bool := [accepted_1110]
theorem batch_22_04_ok : batch_22_04_values.all id = true := by decide

def batch_22_05_values : List Bool := [accepted_1111]
theorem batch_22_05_ok : batch_22_05_values.all id = true := by decide

def batch_22_06_values : List Bool := [accepted_1112]
theorem batch_22_06_ok : batch_22_06_values.all id = true := by decide

def batch_22_07_values : List Bool := [accepted_1113]
theorem batch_22_07_ok : batch_22_07_values.all id = true := by decide

def batch_22_08_values : List Bool := [accepted_1114]
theorem batch_22_08_ok : batch_22_08_values.all id = true := by decide

def batch_22_09_values : List Bool := [accepted_1119]
theorem batch_22_09_ok : batch_22_09_values.all id = true := by decide

def batch_22_10_values : List Bool := [accepted_1120]
theorem batch_22_10_ok : batch_22_10_values.all id = true := by decide

def batch_22_11_values : List Bool := [accepted_1123]
theorem batch_22_11_ok : batch_22_11_values.all id = true := by decide

def batch_22_12_values : List Bool := [accepted_1124]
theorem batch_22_12_ok : batch_22_12_values.all id = true := by decide

def batch_22_13_values : List Bool := [accepted_1127]
theorem batch_22_13_ok : batch_22_13_values.all id = true := by decide

def batch_22_14_values : List Bool := [accepted_1128]
theorem batch_22_14_ok : batch_22_14_values.all id = true := by decide

def batch_22_15_values : List Bool := [accepted_1130]
theorem batch_22_15_ok : batch_22_15_values.all id = true := by decide

def batch_22_16_values : List Bool := [accepted_1131]
theorem batch_22_16_ok : batch_22_16_values.all id = true := by decide

def batch_22_17_values : List Bool := [accepted_1132]
theorem batch_22_17_ok : batch_22_17_values.all id = true := by decide

def batch_22_18_values : List Bool := [accepted_1135]
theorem batch_22_18_ok : batch_22_18_values.all id = true := by decide

def batch_22_19_values : List Bool := [accepted_1136]
theorem batch_22_19_ok : batch_22_19_values.all id = true := by decide

def batch_22_20_values : List Bool := [accepted_1141]
theorem batch_22_20_ok : batch_22_20_values.all id = true := by decide

def batch_22_21_values : List Bool := [accepted_1142]
theorem batch_22_21_ok : batch_22_21_values.all id = true := by decide

def batch_22_22_values : List Bool := [accepted_1143]
theorem batch_22_22_ok : batch_22_22_values.all id = true := by decide

def batch_22_23_values : List Bool := [accepted_1144]
theorem batch_22_23_ok : batch_22_23_values.all id = true := by decide

def batch_22_24_values : List Bool := [accepted_1146]
theorem batch_22_24_ok : batch_22_24_values.all id = true := by decide

def batch_22_25_values : List Bool := [accepted_1148]
theorem batch_22_25_ok : batch_22_25_values.all id = true := by decide

theorem leaf_1103_ok : checkAt 527 1000 box_1103 cert_1103 = true := by
  have h := List.all_eq_true.mp batch_22_00_ok accepted_1103 (by simp [batch_22_00_values])
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

theorem leaf_1104_ok : checkAt 527 1000 box_1104 cert_1104 = true := by
  have h := List.all_eq_true.mp batch_22_01_ok accepted_1104 (by simp [batch_22_01_values])
  exact h
theorem leaf_1104_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1104.profileLo box_1104.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1104_ok
theorem branch_box_1104_nonnegative : ∀ j, 0 ≤ branch_box_1104.lower j ∧ 0 ≤ branch_box_1104.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1104, Box.profileLo, Box.profileHi, box_1104]
theorem leaf_1104_BranchSafe : CertificateConsequences.BranchSafe branch_box_1104 := by
  left; refine ⟨branch_box_1104_nonnegative, ?_⟩
  intro z hz; exact leaf_1104_sound hz

theorem leaf_1105_ok : checkAt 527 1000 box_1105 cert_1105 = true := by
  have h := List.all_eq_true.mp batch_22_02_ok accepted_1105 (by simp [batch_22_02_values])
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

theorem leaf_1106_ok : checkAt 527 1000 box_1106 cert_1106 = true := by
  have h := List.all_eq_true.mp batch_22_03_ok accepted_1106 (by simp [batch_22_03_values])
  exact h
theorem leaf_1106_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1106.profileLo box_1106.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1106_ok
theorem branch_box_1106_nonnegative : ∀ j, 0 ≤ branch_box_1106.lower j ∧ 0 ≤ branch_box_1106.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1106, Box.profileLo, Box.profileHi, box_1106]
theorem leaf_1106_BranchSafe : CertificateConsequences.BranchSafe branch_box_1106 := by
  left; refine ⟨branch_box_1106_nonnegative, ?_⟩
  intro z hz; exact leaf_1106_sound hz

theorem leaf_1110_ok : checkAt 527 1000 box_1110 cert_1110 = true := by
  have h := List.all_eq_true.mp batch_22_04_ok accepted_1110 (by simp [batch_22_04_values])
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

theorem leaf_1111_ok : checkAt 527 1000 box_1111 cert_1111 = true := by
  have h := List.all_eq_true.mp batch_22_05_ok accepted_1111 (by simp [batch_22_05_values])
  exact h
theorem leaf_1111_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1111.profileLo box_1111.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1111_ok
theorem branch_box_1111_nonnegative : ∀ j, 0 ≤ branch_box_1111.lower j ∧ 0 ≤ branch_box_1111.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1111, Box.profileLo, Box.profileHi, box_1111]
theorem leaf_1111_BranchSafe : CertificateConsequences.BranchSafe branch_box_1111 := by
  left; refine ⟨branch_box_1111_nonnegative, ?_⟩
  intro z hz; exact leaf_1111_sound hz

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

theorem leaf_1113_ok : checkAt 527 1000 box_1113 cert_1113 = true := by
  have h := List.all_eq_true.mp batch_22_07_ok accepted_1113 (by simp [batch_22_07_values])
  exact h
theorem leaf_1113_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1113.profileLo box_1113.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1113_ok
theorem branch_box_1113_nonnegative : ∀ j, 0 ≤ branch_box_1113.lower j ∧ 0 ≤ branch_box_1113.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1113, Box.profileLo, Box.profileHi, box_1113]
theorem leaf_1113_BranchSafe : CertificateConsequences.BranchSafe branch_box_1113 := by
  left; refine ⟨branch_box_1113_nonnegative, ?_⟩
  intro z hz; exact leaf_1113_sound hz

theorem leaf_1114_ok : checkAt 527 1000 box_1114 cert_1114 = true := by
  have h := List.all_eq_true.mp batch_22_08_ok accepted_1114 (by simp [batch_22_08_values])
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

theorem leaf_1119_ok : checkAt 527 1000 box_1119 cert_1119 = true := by
  have h := List.all_eq_true.mp batch_22_09_ok accepted_1119 (by simp [batch_22_09_values])
  exact h
theorem leaf_1119_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1119.profileLo box_1119.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1119_ok
theorem branch_box_1119_nonnegative : ∀ j, 0 ≤ branch_box_1119.lower j ∧ 0 ≤ branch_box_1119.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1119, Box.profileLo, Box.profileHi, box_1119]
theorem leaf_1119_BranchSafe : CertificateConsequences.BranchSafe branch_box_1119 := by
  left; refine ⟨branch_box_1119_nonnegative, ?_⟩
  intro z hz; exact leaf_1119_sound hz

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

theorem leaf_1123_ok : checkAt 527 1000 box_1123 cert_1123 = true := by
  have h := List.all_eq_true.mp batch_22_11_ok accepted_1123 (by simp [batch_22_11_values])
  exact h
theorem leaf_1123_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1123.profileLo box_1123.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1123_ok
theorem branch_box_1123_nonnegative : ∀ j, 0 ≤ branch_box_1123.lower j ∧ 0 ≤ branch_box_1123.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1123, Box.profileLo, Box.profileHi, box_1123]
theorem leaf_1123_BranchSafe : CertificateConsequences.BranchSafe branch_box_1123 := by
  left; refine ⟨branch_box_1123_nonnegative, ?_⟩
  intro z hz; exact leaf_1123_sound hz

theorem leaf_1124_ok : checkAt 527 1000 box_1124 cert_1124 = true := by
  have h := List.all_eq_true.mp batch_22_12_ok accepted_1124 (by simp [batch_22_12_values])
  exact h
theorem leaf_1124_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1124.profileLo box_1124.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1124_ok
theorem branch_box_1124_nonnegative : ∀ j, 0 ≤ branch_box_1124.lower j ∧ 0 ≤ branch_box_1124.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1124, Box.profileLo, Box.profileHi, box_1124]
theorem leaf_1124_BranchSafe : CertificateConsequences.BranchSafe branch_box_1124 := by
  left; refine ⟨branch_box_1124_nonnegative, ?_⟩
  intro z hz; exact leaf_1124_sound hz

theorem leaf_1127_ok : checkAt 527 1000 box_1127 cert_1127 = true := by
  have h := List.all_eq_true.mp batch_22_13_ok accepted_1127 (by simp [batch_22_13_values])
  exact h
theorem leaf_1127_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1127.profileLo box_1127.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1127_ok
theorem branch_box_1127_nonnegative : ∀ j, 0 ≤ branch_box_1127.lower j ∧ 0 ≤ branch_box_1127.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1127, Box.profileLo, Box.profileHi, box_1127]
theorem leaf_1127_BranchSafe : CertificateConsequences.BranchSafe branch_box_1127 := by
  left; refine ⟨branch_box_1127_nonnegative, ?_⟩
  intro z hz; exact leaf_1127_sound hz

theorem leaf_1128_ok : checkAt 527 1000 box_1128 cert_1128 = true := by
  have h := List.all_eq_true.mp batch_22_14_ok accepted_1128 (by simp [batch_22_14_values])
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
  have h := List.all_eq_true.mp batch_22_15_ok accepted_1130 (by simp [batch_22_15_values])
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

theorem leaf_1131_ok : checkAt 527 1000 box_1131 cert_1131 = true := by
  have h := List.all_eq_true.mp batch_22_16_ok accepted_1131 (by simp [batch_22_16_values])
  exact h
theorem leaf_1131_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1131.profileLo box_1131.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1131_ok
theorem branch_box_1131_nonnegative : ∀ j, 0 ≤ branch_box_1131.lower j ∧ 0 ≤ branch_box_1131.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1131, Box.profileLo, Box.profileHi, box_1131]
theorem leaf_1131_BranchSafe : CertificateConsequences.BranchSafe branch_box_1131 := by
  left; refine ⟨branch_box_1131_nonnegative, ?_⟩
  intro z hz; exact leaf_1131_sound hz

theorem leaf_1132_ok : checkAt 527 1000 box_1132 cert_1132 = true := by
  have h := List.all_eq_true.mp batch_22_17_ok accepted_1132 (by simp [batch_22_17_values])
  exact h
theorem leaf_1132_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1132.profileLo box_1132.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1132_ok
theorem branch_box_1132_nonnegative : ∀ j, 0 ≤ branch_box_1132.lower j ∧ 0 ≤ branch_box_1132.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1132, Box.profileLo, Box.profileHi, box_1132]
theorem leaf_1132_BranchSafe : CertificateConsequences.BranchSafe branch_box_1132 := by
  left; refine ⟨branch_box_1132_nonnegative, ?_⟩
  intro z hz; exact leaf_1132_sound hz

theorem leaf_1135_ok : checkAt 527 1000 box_1135 cert_1135 = true := by
  have h := List.all_eq_true.mp batch_22_18_ok accepted_1135 (by simp [batch_22_18_values])
  exact h
theorem leaf_1135_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1135.profileLo box_1135.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1135_ok
theorem branch_box_1135_nonnegative : ∀ j, 0 ≤ branch_box_1135.lower j ∧ 0 ≤ branch_box_1135.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1135, Box.profileLo, Box.profileHi, box_1135]
theorem leaf_1135_BranchSafe : CertificateConsequences.BranchSafe branch_box_1135 := by
  left; refine ⟨branch_box_1135_nonnegative, ?_⟩
  intro z hz; exact leaf_1135_sound hz

theorem leaf_1136_ok : checkAt 527 1000 box_1136 cert_1136 = true := by
  have h := List.all_eq_true.mp batch_22_19_ok accepted_1136 (by simp [batch_22_19_values])
  exact h
theorem leaf_1136_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1136.profileLo box_1136.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1136_ok
theorem branch_box_1136_nonnegative : ∀ j, 0 ≤ branch_box_1136.lower j ∧ 0 ≤ branch_box_1136.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1136, Box.profileLo, Box.profileHi, box_1136]
theorem leaf_1136_BranchSafe : CertificateConsequences.BranchSafe branch_box_1136 := by
  left; refine ⟨branch_box_1136_nonnegative, ?_⟩
  intro z hz; exact leaf_1136_sound hz

theorem leaf_1141_ok : checkAt 527 1000 box_1141 cert_1141 = true := by
  have h := List.all_eq_true.mp batch_22_20_ok accepted_1141 (by simp [batch_22_20_values])
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

theorem leaf_1142_ok : checkAt 527 1000 box_1142 cert_1142 = true := by
  have h := List.all_eq_true.mp batch_22_21_ok accepted_1142 (by simp [batch_22_21_values])
  exact h
theorem leaf_1142_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1142.profileLo box_1142.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1142_ok
theorem branch_box_1142_nonnegative : ∀ j, 0 ≤ branch_box_1142.lower j ∧ 0 ≤ branch_box_1142.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1142, Box.profileLo, Box.profileHi, box_1142]
theorem leaf_1142_BranchSafe : CertificateConsequences.BranchSafe branch_box_1142 := by
  left; refine ⟨branch_box_1142_nonnegative, ?_⟩
  intro z hz; exact leaf_1142_sound hz

theorem leaf_1143_ok : checkAt 527 1000 box_1143 cert_1143 = true := by
  have h := List.all_eq_true.mp batch_22_22_ok accepted_1143 (by simp [batch_22_22_values])
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

theorem leaf_1144_ok : checkAt 527 1000 box_1144 cert_1144 = true := by
  have h := List.all_eq_true.mp batch_22_23_ok accepted_1144 (by simp [batch_22_23_values])
  exact h
theorem leaf_1144_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1144.profileLo box_1144.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1144_ok
theorem branch_box_1144_nonnegative : ∀ j, 0 ≤ branch_box_1144.lower j ∧ 0 ≤ branch_box_1144.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1144, Box.profileLo, Box.profileHi, box_1144]
theorem leaf_1144_BranchSafe : CertificateConsequences.BranchSafe branch_box_1144 := by
  left; refine ⟨branch_box_1144_nonnegative, ?_⟩
  intro z hz; exact leaf_1144_sound hz

theorem leaf_1146_ok : checkAt 527 1000 box_1146 cert_1146 = true := by
  have h := List.all_eq_true.mp batch_22_24_ok accepted_1146 (by simp [batch_22_24_values])
  exact h
theorem leaf_1146_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1146.profileLo box_1146.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1146_ok
theorem branch_box_1146_nonnegative : ∀ j, 0 ≤ branch_box_1146.lower j ∧ 0 ≤ branch_box_1146.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1146, Box.profileLo, Box.profileHi, box_1146]
theorem leaf_1146_BranchSafe : CertificateConsequences.BranchSafe branch_box_1146 := by
  left; refine ⟨branch_box_1146_nonnegative, ?_⟩
  intro z hz; exact leaf_1146_sound hz

theorem leaf_1148_ok : checkAt 527 1000 box_1148 cert_1148 = true := by
  have h := List.all_eq_true.mp batch_22_25_ok accepted_1148 (by simp [batch_22_25_values])
  exact h
theorem leaf_1148_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1148.profileLo box_1148.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1148_ok
theorem branch_box_1148_nonnegative : ∀ j, 0 ≤ branch_box_1148.lower j ∧ 0 ≤ branch_box_1148.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1148, Box.profileLo, Box.profileHi, box_1148]
theorem leaf_1148_BranchSafe : CertificateConsequences.BranchSafe branch_box_1148 := by
  left; refine ⟨branch_box_1148_nonnegative, ?_⟩
  intro z hz; exact leaf_1148_sound hz

#print axioms batch_22_00_ok
#print axioms leaf_1103_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
