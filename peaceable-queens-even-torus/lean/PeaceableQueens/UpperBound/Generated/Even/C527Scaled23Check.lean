import PeaceableQueens.UpperBound.Generated.Even.C527Scaled23Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_23_00_values : List Bool := [accepted_1150]
theorem batch_23_00_ok : batch_23_00_values.all id = true := by decide

def batch_23_01_values : List Bool := [accepted_1151]
theorem batch_23_01_ok : batch_23_01_values.all id = true := by decide

def batch_23_02_values : List Bool := [accepted_1152]
theorem batch_23_02_ok : batch_23_02_values.all id = true := by decide

def batch_23_03_values : List Bool := [accepted_1157]
theorem batch_23_03_ok : batch_23_03_values.all id = true := by decide

def batch_23_04_values : List Bool := [accepted_1158]
theorem batch_23_04_ok : batch_23_04_values.all id = true := by decide

def batch_23_05_values : List Bool := [accepted_1159]
theorem batch_23_05_ok : batch_23_05_values.all id = true := by decide

def batch_23_06_values : List Bool := [accepted_1160]
theorem batch_23_06_ok : batch_23_06_values.all id = true := by decide

def batch_23_07_values : List Bool := [accepted_1163]
theorem batch_23_07_ok : batch_23_07_values.all id = true := by decide

def batch_23_08_values : List Bool := [accepted_1164]
theorem batch_23_08_ok : batch_23_08_values.all id = true := by decide

def batch_23_09_values : List Bool := [accepted_1167]
theorem batch_23_09_ok : batch_23_09_values.all id = true := by decide

def batch_23_10_values : List Bool := [accepted_1168]
theorem batch_23_10_ok : batch_23_10_values.all id = true := by decide

def batch_23_11_values : List Bool := [accepted_1169]
theorem batch_23_11_ok : batch_23_11_values.all id = true := by decide

def batch_23_12_values : List Bool := [accepted_1172]
theorem batch_23_12_ok : batch_23_12_values.all id = true := by decide

def batch_23_13_values : List Bool := [accepted_1174]
theorem batch_23_13_ok : batch_23_13_values.all id = true := by decide

def batch_23_14_values : List Bool := [accepted_1175]
theorem batch_23_14_ok : batch_23_14_values.all id = true := by decide

def batch_23_15_values : List Bool := [accepted_1176]
theorem batch_23_15_ok : batch_23_15_values.all id = true := by decide

def batch_23_16_values : List Bool := [accepted_1189]
theorem batch_23_16_ok : batch_23_16_values.all id = true := by decide

def batch_23_17_values : List Bool := [accepted_1190]
theorem batch_23_17_ok : batch_23_17_values.all id = true := by decide

def batch_23_18_values : List Bool := [accepted_1191]
theorem batch_23_18_ok : batch_23_18_values.all id = true := by decide

def batch_23_19_values : List Bool := [accepted_1192]
theorem batch_23_19_ok : batch_23_19_values.all id = true := by decide

def batch_23_20_values : List Bool := [accepted_1195]
theorem batch_23_20_ok : batch_23_20_values.all id = true := by decide

def batch_23_21_values : List Bool := [accepted_1196]
theorem batch_23_21_ok : batch_23_21_values.all id = true := by decide

def batch_23_22_values : List Bool := [accepted_1197]
theorem batch_23_22_ok : batch_23_22_values.all id = true := by decide

def batch_23_23_values : List Bool := [accepted_1198]
theorem batch_23_23_ok : batch_23_23_values.all id = true := by decide

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

theorem leaf_1152_ok : checkAt 527 1000 box_1152 cert_1152 = true := by
  have h := List.all_eq_true.mp batch_23_02_ok accepted_1152 (by simp [batch_23_02_values])
  exact h
theorem leaf_1152_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1152.profileLo box_1152.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1152_ok
theorem branch_box_1152_nonnegative : ∀ j, 0 ≤ branch_box_1152.lower j ∧ 0 ≤ branch_box_1152.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1152, Box.profileLo, Box.profileHi, box_1152]
theorem leaf_1152_BranchSafe : CertificateConsequences.BranchSafe branch_box_1152 := by
  left; refine ⟨branch_box_1152_nonnegative, ?_⟩
  intro z hz; exact leaf_1152_sound hz

theorem leaf_1157_ok : checkAt 527 1000 box_1157 cert_1157 = true := by
  have h := List.all_eq_true.mp batch_23_03_ok accepted_1157 (by simp [batch_23_03_values])
  exact h
theorem leaf_1157_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1157.profileLo box_1157.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1157_ok
theorem branch_box_1157_nonnegative : ∀ j, 0 ≤ branch_box_1157.lower j ∧ 0 ≤ branch_box_1157.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1157, Box.profileLo, Box.profileHi, box_1157]
theorem leaf_1157_BranchSafe : CertificateConsequences.BranchSafe branch_box_1157 := by
  left; refine ⟨branch_box_1157_nonnegative, ?_⟩
  intro z hz; exact leaf_1157_sound hz

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

theorem leaf_1160_ok : checkAt 527 1000 box_1160 cert_1160 = true := by
  have h := List.all_eq_true.mp batch_23_06_ok accepted_1160 (by simp [batch_23_06_values])
  exact h
theorem leaf_1160_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1160.profileLo box_1160.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1160_ok
theorem branch_box_1160_nonnegative : ∀ j, 0 ≤ branch_box_1160.lower j ∧ 0 ≤ branch_box_1160.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1160, Box.profileLo, Box.profileHi, box_1160]
theorem leaf_1160_BranchSafe : CertificateConsequences.BranchSafe branch_box_1160 := by
  left; refine ⟨branch_box_1160_nonnegative, ?_⟩
  intro z hz; exact leaf_1160_sound hz

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

theorem leaf_1164_ok : checkAt 527 1000 box_1164 cert_1164 = true := by
  have h := List.all_eq_true.mp batch_23_08_ok accepted_1164 (by simp [batch_23_08_values])
  exact h
theorem leaf_1164_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1164.profileLo box_1164.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1164_ok
theorem branch_box_1164_nonnegative : ∀ j, 0 ≤ branch_box_1164.lower j ∧ 0 ≤ branch_box_1164.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1164, Box.profileLo, Box.profileHi, box_1164]
theorem leaf_1164_BranchSafe : CertificateConsequences.BranchSafe branch_box_1164 := by
  left; refine ⟨branch_box_1164_nonnegative, ?_⟩
  intro z hz; exact leaf_1164_sound hz

theorem leaf_1167_ok : checkAt 527 1000 box_1167 cert_1167 = true := by
  have h := List.all_eq_true.mp batch_23_09_ok accepted_1167 (by simp [batch_23_09_values])
  exact h
theorem leaf_1167_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1167.profileLo box_1167.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1167_ok
theorem branch_box_1167_nonnegative : ∀ j, 0 ≤ branch_box_1167.lower j ∧ 0 ≤ branch_box_1167.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1167, Box.profileLo, Box.profileHi, box_1167]
theorem leaf_1167_BranchSafe : CertificateConsequences.BranchSafe branch_box_1167 := by
  left; refine ⟨branch_box_1167_nonnegative, ?_⟩
  intro z hz; exact leaf_1167_sound hz

theorem leaf_1168_ok : checkAt 527 1000 box_1168 cert_1168 = true := by
  have h := List.all_eq_true.mp batch_23_10_ok accepted_1168 (by simp [batch_23_10_values])
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
  have h := List.all_eq_true.mp batch_23_11_ok accepted_1169 (by simp [batch_23_11_values])
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

theorem leaf_1172_ok : checkAt 527 1000 box_1172 cert_1172 = true := by
  have h := List.all_eq_true.mp batch_23_12_ok accepted_1172 (by simp [batch_23_12_values])
  exact h
theorem leaf_1172_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1172.profileLo box_1172.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1172_ok
theorem branch_box_1172_nonnegative : ∀ j, 0 ≤ branch_box_1172.lower j ∧ 0 ≤ branch_box_1172.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1172, Box.profileLo, Box.profileHi, box_1172]
theorem leaf_1172_BranchSafe : CertificateConsequences.BranchSafe branch_box_1172 := by
  left; refine ⟨branch_box_1172_nonnegative, ?_⟩
  intro z hz; exact leaf_1172_sound hz

theorem leaf_1174_ok : checkAt 527 1000 box_1174 cert_1174 = true := by
  have h := List.all_eq_true.mp batch_23_13_ok accepted_1174 (by simp [batch_23_13_values])
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

theorem leaf_1175_ok : checkAt 527 1000 box_1175 cert_1175 = true := by
  have h := List.all_eq_true.mp batch_23_14_ok accepted_1175 (by simp [batch_23_14_values])
  exact h
theorem leaf_1175_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1175.profileLo box_1175.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1175_ok
theorem branch_box_1175_nonnegative : ∀ j, 0 ≤ branch_box_1175.lower j ∧ 0 ≤ branch_box_1175.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1175, Box.profileLo, Box.profileHi, box_1175]
theorem leaf_1175_BranchSafe : CertificateConsequences.BranchSafe branch_box_1175 := by
  left; refine ⟨branch_box_1175_nonnegative, ?_⟩
  intro z hz; exact leaf_1175_sound hz

theorem leaf_1176_ok : checkAt 527 1000 box_1176 cert_1176 = true := by
  have h := List.all_eq_true.mp batch_23_15_ok accepted_1176 (by simp [batch_23_15_values])
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

theorem leaf_1189_ok : checkAt 527 1000 box_1189 cert_1189 = true := by
  have h := List.all_eq_true.mp batch_23_16_ok accepted_1189 (by simp [batch_23_16_values])
  exact h
theorem leaf_1189_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1189.profileLo box_1189.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1189_ok
theorem branch_box_1189_nonnegative : ∀ j, 0 ≤ branch_box_1189.lower j ∧ 0 ≤ branch_box_1189.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1189, Box.profileLo, Box.profileHi, box_1189]
theorem leaf_1189_BranchSafe : CertificateConsequences.BranchSafe branch_box_1189 := by
  left; refine ⟨branch_box_1189_nonnegative, ?_⟩
  intro z hz; exact leaf_1189_sound hz

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

theorem leaf_1192_ok : checkAt 527 1000 box_1192 cert_1192 = true := by
  have h := List.all_eq_true.mp batch_23_19_ok accepted_1192 (by simp [batch_23_19_values])
  exact h
theorem leaf_1192_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1192.profileLo box_1192.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1192_ok
theorem branch_box_1192_nonnegative : ∀ j, 0 ≤ branch_box_1192.lower j ∧ 0 ≤ branch_box_1192.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1192, Box.profileLo, Box.profileHi, box_1192]
theorem leaf_1192_BranchSafe : CertificateConsequences.BranchSafe branch_box_1192 := by
  left; refine ⟨branch_box_1192_nonnegative, ?_⟩
  intro z hz; exact leaf_1192_sound hz

theorem leaf_1195_ok : checkAt 527 1000 box_1195 cert_1195 = true := by
  have h := List.all_eq_true.mp batch_23_20_ok accepted_1195 (by simp [batch_23_20_values])
  exact h
theorem leaf_1195_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1195.profileLo box_1195.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1195_ok
theorem branch_box_1195_nonnegative : ∀ j, 0 ≤ branch_box_1195.lower j ∧ 0 ≤ branch_box_1195.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1195, Box.profileLo, Box.profileHi, box_1195]
theorem leaf_1195_BranchSafe : CertificateConsequences.BranchSafe branch_box_1195 := by
  left; refine ⟨branch_box_1195_nonnegative, ?_⟩
  intro z hz; exact leaf_1195_sound hz

theorem leaf_1196_ok : checkAt 527 1000 box_1196 cert_1196 = true := by
  have h := List.all_eq_true.mp batch_23_21_ok accepted_1196 (by simp [batch_23_21_values])
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

theorem leaf_1197_ok : checkAt 527 1000 box_1197 cert_1197 = true := by
  have h := List.all_eq_true.mp batch_23_22_ok accepted_1197 (by simp [batch_23_22_values])
  exact h
theorem leaf_1197_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1197.profileLo box_1197.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1197_ok
theorem branch_box_1197_nonnegative : ∀ j, 0 ≤ branch_box_1197.lower j ∧ 0 ≤ branch_box_1197.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1197, Box.profileLo, Box.profileHi, box_1197]
theorem leaf_1197_BranchSafe : CertificateConsequences.BranchSafe branch_box_1197 := by
  left; refine ⟨branch_box_1197_nonnegative, ?_⟩
  intro z hz; exact leaf_1197_sound hz

theorem leaf_1198_ok : checkAt 527 1000 box_1198 cert_1198 = true := by
  have h := List.all_eq_true.mp batch_23_23_ok accepted_1198 (by simp [batch_23_23_values])
  exact h
theorem leaf_1198_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1198.profileLo box_1198.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1198_ok
theorem branch_box_1198_nonnegative : ∀ j, 0 ≤ branch_box_1198.lower j ∧ 0 ≤ branch_box_1198.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1198, Box.profileLo, Box.profileHi, box_1198]
theorem leaf_1198_BranchSafe : CertificateConsequences.BranchSafe branch_box_1198 := by
  left; refine ⟨branch_box_1198_nonnegative, ?_⟩
  intro z hz; exact leaf_1198_sound hz

#print axioms batch_23_00_ok
#print axioms leaf_1150_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
