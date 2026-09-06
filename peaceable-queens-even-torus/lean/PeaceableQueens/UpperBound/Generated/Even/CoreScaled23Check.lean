import PeaceableQueens.UpperBound.Generated.Even.CoreScaled23Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_23_00_values : List Bool := [accepted_1150]
theorem batch_23_00_ok : batch_23_00_values.all id = true := by decide

def batch_23_01_values : List Bool := [accepted_1151]
theorem batch_23_01_ok : batch_23_01_values.all id = true := by decide

def batch_23_02_values : List Bool := [accepted_1154]
theorem batch_23_02_ok : batch_23_02_values.all id = true := by decide

def batch_23_03_values : List Bool := [accepted_1156]
theorem batch_23_03_ok : batch_23_03_values.all id = true := by decide

def batch_23_04_values : List Bool := [accepted_1158]
theorem batch_23_04_ok : batch_23_04_values.all id = true := by decide

def batch_23_05_values : List Bool := [accepted_1159]
theorem batch_23_05_ok : batch_23_05_values.all id = true := by decide

def batch_23_06_values : List Bool := [accepted_1161]
theorem batch_23_06_ok : batch_23_06_values.all id = true := by decide

def batch_23_07_values : List Bool := [accepted_1163]
theorem batch_23_07_ok : batch_23_07_values.all id = true := by decide

def batch_23_08_values : List Bool := [accepted_1165]
theorem batch_23_08_ok : batch_23_08_values.all id = true := by decide

def batch_23_09_values : List Bool := [accepted_1168]
theorem batch_23_09_ok : batch_23_09_values.all id = true := by decide

def batch_23_10_values : List Bool := [accepted_1169]
theorem batch_23_10_ok : batch_23_10_values.all id = true := by decide

def batch_23_11_values : List Bool := [accepted_1174]
theorem batch_23_11_ok : batch_23_11_values.all id = true := by decide

def batch_23_12_values : List Bool := [accepted_1176]
theorem batch_23_12_ok : batch_23_12_values.all id = true := by decide

def batch_23_13_values : List Bool := [accepted_1177]
theorem batch_23_13_ok : batch_23_13_values.all id = true := by decide

def batch_23_14_values : List Bool := [accepted_1179]
theorem batch_23_14_ok : batch_23_14_values.all id = true := by decide

def batch_23_15_values : List Bool := [accepted_1186]
theorem batch_23_15_ok : batch_23_15_values.all id = true := by decide

def batch_23_16_values : List Bool := [accepted_1187]
theorem batch_23_16_ok : batch_23_16_values.all id = true := by decide

def batch_23_17_values : List Bool := [accepted_1190]
theorem batch_23_17_ok : batch_23_17_values.all id = true := by decide

def batch_23_18_values : List Bool := [accepted_1191]
theorem batch_23_18_ok : batch_23_18_values.all id = true := by decide

def batch_23_19_values : List Bool := [accepted_1193]
theorem batch_23_19_ok : batch_23_19_values.all id = true := by decide

def batch_23_20_values : List Bool := [accepted_1196]
theorem batch_23_20_ok : batch_23_20_values.all id = true := by decide

theorem leaf_1150_ok : checkAt 527 1000 box_1150 cert_1150 = true := by
  have h := List.all_eq_true.mp batch_23_00_ok accepted_1150 (by simp [batch_23_00_values])
  exact h
theorem leaf_1150_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1150.profileLo box_1150.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1150_ok
theorem branch_box_1150_nonnegative : ∀ j, 0 ≤ branch_box_1150.lower j ∧ 0 ≤ branch_box_1150.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1150, Box.profileLo, Box.profileHi, box_1150]
theorem leaf_1150_BranchSafe : CertificateConsequences.BranchSafe branch_box_1150 := by
  left; refine ⟨branch_box_1150_nonnegative, ?_⟩
  intro z hz; exact leaf_1150_sound hz

theorem leaf_1151_ok : checkAt 527 1000 box_1151 cert_1151 = true := by
  have h := List.all_eq_true.mp batch_23_01_ok accepted_1151 (by simp [batch_23_01_values])
  exact h
theorem leaf_1151_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1151.profileLo box_1151.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1151_ok
theorem branch_box_1151_nonnegative : ∀ j, 0 ≤ branch_box_1151.lower j ∧ 0 ≤ branch_box_1151.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1151, Box.profileLo, Box.profileHi, box_1151]
theorem leaf_1151_BranchSafe : CertificateConsequences.BranchSafe branch_box_1151 := by
  left; refine ⟨branch_box_1151_nonnegative, ?_⟩
  intro z hz; exact leaf_1151_sound hz

theorem leaf_1154_ok : checkAt 527 1000 box_1154 cert_1154 = true := by
  have h := List.all_eq_true.mp batch_23_02_ok accepted_1154 (by simp [batch_23_02_values])
  exact h
theorem leaf_1154_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1154.profileLo box_1154.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1154_ok
theorem branch_box_1154_nonnegative : ∀ j, 0 ≤ branch_box_1154.lower j ∧ 0 ≤ branch_box_1154.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1154, Box.profileLo, Box.profileHi, box_1154]
theorem leaf_1154_BranchSafe : CertificateConsequences.BranchSafe branch_box_1154 := by
  left; refine ⟨branch_box_1154_nonnegative, ?_⟩
  intro z hz; exact leaf_1154_sound hz

theorem leaf_1156_ok : checkAt 527 1000 box_1156 cert_1156 = true := by
  have h := List.all_eq_true.mp batch_23_03_ok accepted_1156 (by simp [batch_23_03_values])
  exact h
theorem leaf_1156_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1156.profileLo box_1156.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1156_ok
theorem branch_box_1156_nonnegative : ∀ j, 0 ≤ branch_box_1156.lower j ∧ 0 ≤ branch_box_1156.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1156, Box.profileLo, Box.profileHi, box_1156]
theorem leaf_1156_BranchSafe : CertificateConsequences.BranchSafe branch_box_1156 := by
  left; refine ⟨branch_box_1156_nonnegative, ?_⟩
  intro z hz; exact leaf_1156_sound hz

theorem leaf_1158_ok : checkAt 527 1000 box_1158 cert_1158 = true := by
  have h := List.all_eq_true.mp batch_23_04_ok accepted_1158 (by simp [batch_23_04_values])
  exact h
theorem leaf_1158_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1158.profileLo box_1158.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1158_ok
theorem branch_box_1158_nonnegative : ∀ j, 0 ≤ branch_box_1158.lower j ∧ 0 ≤ branch_box_1158.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1158, Box.profileLo, Box.profileHi, box_1158]
theorem leaf_1158_BranchSafe : CertificateConsequences.BranchSafe branch_box_1158 := by
  left; refine ⟨branch_box_1158_nonnegative, ?_⟩
  intro z hz; exact leaf_1158_sound hz

theorem leaf_1159_ok : checkAt 527 1000 box_1159 cert_1159 = true := by
  have h := List.all_eq_true.mp batch_23_05_ok accepted_1159 (by simp [batch_23_05_values])
  exact h
theorem leaf_1159_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1159.profileLo box_1159.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1159_ok
theorem branch_box_1159_nonnegative : ∀ j, 0 ≤ branch_box_1159.lower j ∧ 0 ≤ branch_box_1159.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1159, Box.profileLo, Box.profileHi, box_1159]
theorem leaf_1159_BranchSafe : CertificateConsequences.BranchSafe branch_box_1159 := by
  left; refine ⟨branch_box_1159_nonnegative, ?_⟩
  intro z hz; exact leaf_1159_sound hz

theorem leaf_1161_ok : checkAt 527 1000 box_1161 cert_1161 = true := by
  have h := List.all_eq_true.mp batch_23_06_ok accepted_1161 (by simp [batch_23_06_values])
  exact h
theorem leaf_1161_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1161.profileLo box_1161.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1161_ok
theorem branch_box_1161_nonnegative : ∀ j, 0 ≤ branch_box_1161.lower j ∧ 0 ≤ branch_box_1161.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1161, Box.profileLo, Box.profileHi, box_1161]
theorem leaf_1161_BranchSafe : CertificateConsequences.BranchSafe branch_box_1161 := by
  left; refine ⟨branch_box_1161_nonnegative, ?_⟩
  intro z hz; exact leaf_1161_sound hz

theorem leaf_1163_ok : checkAt 527 1000 box_1163 cert_1163 = true := by
  have h := List.all_eq_true.mp batch_23_07_ok accepted_1163 (by simp [batch_23_07_values])
  exact h
theorem leaf_1163_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1163.profileLo box_1163.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1163_ok
theorem branch_box_1163_nonnegative : ∀ j, 0 ≤ branch_box_1163.lower j ∧ 0 ≤ branch_box_1163.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1163, Box.profileLo, Box.profileHi, box_1163]
theorem leaf_1163_BranchSafe : CertificateConsequences.BranchSafe branch_box_1163 := by
  left; refine ⟨branch_box_1163_nonnegative, ?_⟩
  intro z hz; exact leaf_1163_sound hz

theorem leaf_1165_ok : checkAt 527 1000 box_1165 cert_1165 = true := by
  have h := List.all_eq_true.mp batch_23_08_ok accepted_1165 (by simp [batch_23_08_values])
  exact h
theorem leaf_1165_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1165.profileLo box_1165.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1165_ok
theorem branch_box_1165_nonnegative : ∀ j, 0 ≤ branch_box_1165.lower j ∧ 0 ≤ branch_box_1165.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1165, Box.profileLo, Box.profileHi, box_1165]
theorem leaf_1165_BranchSafe : CertificateConsequences.BranchSafe branch_box_1165 := by
  left; refine ⟨branch_box_1165_nonnegative, ?_⟩
  intro z hz; exact leaf_1165_sound hz

theorem leaf_1168_ok : checkAt 527 1000 box_1168 cert_1168 = true := by
  have h := List.all_eq_true.mp batch_23_09_ok accepted_1168 (by simp [batch_23_09_values])
  exact h
theorem leaf_1168_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1168.profileLo box_1168.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1168_ok
theorem branch_box_1168_nonnegative : ∀ j, 0 ≤ branch_box_1168.lower j ∧ 0 ≤ branch_box_1168.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1168, Box.profileLo, Box.profileHi, box_1168]
theorem leaf_1168_BranchSafe : CertificateConsequences.BranchSafe branch_box_1168 := by
  left; refine ⟨branch_box_1168_nonnegative, ?_⟩
  intro z hz; exact leaf_1168_sound hz

theorem leaf_1169_ok : checkAt 527 1000 box_1169 cert_1169 = true := by
  have h := List.all_eq_true.mp batch_23_10_ok accepted_1169 (by simp [batch_23_10_values])
  exact h
theorem leaf_1169_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1169.profileLo box_1169.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1169_ok
theorem branch_box_1169_nonnegative : ∀ j, 0 ≤ branch_box_1169.lower j ∧ 0 ≤ branch_box_1169.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1169, Box.profileLo, Box.profileHi, box_1169]
theorem leaf_1169_BranchSafe : CertificateConsequences.BranchSafe branch_box_1169 := by
  left; refine ⟨branch_box_1169_nonnegative, ?_⟩
  intro z hz; exact leaf_1169_sound hz

theorem leaf_1174_ok : checkAt 527 1000 box_1174 cert_1174 = true := by
  have h := List.all_eq_true.mp batch_23_11_ok accepted_1174 (by simp [batch_23_11_values])
  exact h
theorem leaf_1174_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1174.profileLo box_1174.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1174_ok
theorem branch_box_1174_nonnegative : ∀ j, 0 ≤ branch_box_1174.lower j ∧ 0 ≤ branch_box_1174.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1174, Box.profileLo, Box.profileHi, box_1174]
theorem leaf_1174_BranchSafe : CertificateConsequences.BranchSafe branch_box_1174 := by
  left; refine ⟨branch_box_1174_nonnegative, ?_⟩
  intro z hz; exact leaf_1174_sound hz

theorem leaf_1176_ok : checkAt 527 1000 box_1176 cert_1176 = true := by
  have h := List.all_eq_true.mp batch_23_12_ok accepted_1176 (by simp [batch_23_12_values])
  exact h
theorem leaf_1176_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1176.profileLo box_1176.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1176_ok
theorem branch_box_1176_nonnegative : ∀ j, 0 ≤ branch_box_1176.lower j ∧ 0 ≤ branch_box_1176.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1176, Box.profileLo, Box.profileHi, box_1176]
theorem leaf_1176_BranchSafe : CertificateConsequences.BranchSafe branch_box_1176 := by
  left; refine ⟨branch_box_1176_nonnegative, ?_⟩
  intro z hz; exact leaf_1176_sound hz

theorem leaf_1177_ok : checkAt 527 1000 box_1177 cert_1177 = true := by
  have h := List.all_eq_true.mp batch_23_13_ok accepted_1177 (by simp [batch_23_13_values])
  exact h
theorem leaf_1177_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1177.profileLo box_1177.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1177_ok
theorem branch_box_1177_nonnegative : ∀ j, 0 ≤ branch_box_1177.lower j ∧ 0 ≤ branch_box_1177.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1177, Box.profileLo, Box.profileHi, box_1177]
theorem leaf_1177_BranchSafe : CertificateConsequences.BranchSafe branch_box_1177 := by
  left; refine ⟨branch_box_1177_nonnegative, ?_⟩
  intro z hz; exact leaf_1177_sound hz

theorem leaf_1179_ok : checkAt 527 1000 box_1179 cert_1179 = true := by
  have h := List.all_eq_true.mp batch_23_14_ok accepted_1179 (by simp [batch_23_14_values])
  exact h
theorem leaf_1179_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1179.profileLo box_1179.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1179_ok
theorem branch_box_1179_nonnegative : ∀ j, 0 ≤ branch_box_1179.lower j ∧ 0 ≤ branch_box_1179.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1179, Box.profileLo, Box.profileHi, box_1179]
theorem leaf_1179_BranchSafe : CertificateConsequences.BranchSafe branch_box_1179 := by
  left; refine ⟨branch_box_1179_nonnegative, ?_⟩
  intro z hz; exact leaf_1179_sound hz

theorem leaf_1186_ok : checkAt 527 1000 box_1186 cert_1186 = true := by
  have h := List.all_eq_true.mp batch_23_15_ok accepted_1186 (by simp [batch_23_15_values])
  exact h
theorem leaf_1186_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1186.profileLo box_1186.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1186_ok
theorem branch_box_1186_nonnegative : ∀ j, 0 ≤ branch_box_1186.lower j ∧ 0 ≤ branch_box_1186.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1186, Box.profileLo, Box.profileHi, box_1186]
theorem leaf_1186_BranchSafe : CertificateConsequences.BranchSafe branch_box_1186 := by
  left; refine ⟨branch_box_1186_nonnegative, ?_⟩
  intro z hz; exact leaf_1186_sound hz

theorem leaf_1187_ok : checkAt 527 1000 box_1187 cert_1187 = true := by
  have h := List.all_eq_true.mp batch_23_16_ok accepted_1187 (by simp [batch_23_16_values])
  exact h
theorem leaf_1187_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1187.profileLo box_1187.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1187_ok
theorem branch_box_1187_nonnegative : ∀ j, 0 ≤ branch_box_1187.lower j ∧ 0 ≤ branch_box_1187.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1187, Box.profileLo, Box.profileHi, box_1187]
theorem leaf_1187_BranchSafe : CertificateConsequences.BranchSafe branch_box_1187 := by
  left; refine ⟨branch_box_1187_nonnegative, ?_⟩
  intro z hz; exact leaf_1187_sound hz

theorem leaf_1190_ok : checkAt 527 1000 box_1190 cert_1190 = true := by
  have h := List.all_eq_true.mp batch_23_17_ok accepted_1190 (by simp [batch_23_17_values])
  exact h
theorem leaf_1190_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1190.profileLo box_1190.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1190_ok
theorem branch_box_1190_nonnegative : ∀ j, 0 ≤ branch_box_1190.lower j ∧ 0 ≤ branch_box_1190.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1190, Box.profileLo, Box.profileHi, box_1190]
theorem leaf_1190_BranchSafe : CertificateConsequences.BranchSafe branch_box_1190 := by
  left; refine ⟨branch_box_1190_nonnegative, ?_⟩
  intro z hz; exact leaf_1190_sound hz

theorem leaf_1191_ok : checkAt 527 1000 box_1191 cert_1191 = true := by
  have h := List.all_eq_true.mp batch_23_18_ok accepted_1191 (by simp [batch_23_18_values])
  exact h
theorem leaf_1191_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1191.profileLo box_1191.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1191_ok
theorem branch_box_1191_nonnegative : ∀ j, 0 ≤ branch_box_1191.lower j ∧ 0 ≤ branch_box_1191.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1191, Box.profileLo, Box.profileHi, box_1191]
theorem leaf_1191_BranchSafe : CertificateConsequences.BranchSafe branch_box_1191 := by
  left; refine ⟨branch_box_1191_nonnegative, ?_⟩
  intro z hz; exact leaf_1191_sound hz

theorem leaf_1193_ok : checkAt 527 1000 box_1193 cert_1193 = true := by
  have h := List.all_eq_true.mp batch_23_19_ok accepted_1193 (by simp [batch_23_19_values])
  exact h
theorem leaf_1193_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1193.profileLo box_1193.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1193_ok
theorem branch_box_1193_nonnegative : ∀ j, 0 ≤ branch_box_1193.lower j ∧ 0 ≤ branch_box_1193.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1193, Box.profileLo, Box.profileHi, box_1193]
theorem leaf_1193_BranchSafe : CertificateConsequences.BranchSafe branch_box_1193 := by
  left; refine ⟨branch_box_1193_nonnegative, ?_⟩
  intro z hz; exact leaf_1193_sound hz

theorem leaf_1196_ok : checkAt 527 1000 box_1196 cert_1196 = true := by
  have h := List.all_eq_true.mp batch_23_20_ok accepted_1196 (by simp [batch_23_20_values])
  exact h
theorem leaf_1196_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1196.profileLo box_1196.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1196_ok
theorem branch_box_1196_nonnegative : ∀ j, 0 ≤ branch_box_1196.lower j ∧ 0 ≤ branch_box_1196.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1196, Box.profileLo, Box.profileHi, box_1196]
theorem leaf_1196_BranchSafe : CertificateConsequences.BranchSafe branch_box_1196 := by
  left; refine ⟨branch_box_1196_nonnegative, ?_⟩
  intro z hz; exact leaf_1196_sound hz

#print axioms batch_23_00_ok
#print axioms leaf_1150_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
