import PeaceableQueens.UpperBound.Generated.Even.CoreScaled25Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_25_00_values : List Bool := [accepted_1252]
theorem batch_25_00_ok : batch_25_00_values.all id = true := by decide

def batch_25_01_values : List Bool := [accepted_1254]
theorem batch_25_01_ok : batch_25_01_values.all id = true := by decide

def batch_25_02_values : List Bool := [accepted_1255]
theorem batch_25_02_ok : batch_25_02_values.all id = true := by decide

def batch_25_03_values : List Bool := [accepted_1257]
theorem batch_25_03_ok : batch_25_03_values.all id = true := by decide

def batch_25_04_values : List Bool := [accepted_1264]
theorem batch_25_04_ok : batch_25_04_values.all id = true := by decide

def batch_25_05_values : List Bool := [accepted_1267]
theorem batch_25_05_ok : batch_25_05_values.all id = true := by decide

def batch_25_06_values : List Bool := [accepted_1270]
theorem batch_25_06_ok : batch_25_06_values.all id = true := by decide

def batch_25_07_values : List Bool := [accepted_1273]
theorem batch_25_07_ok : batch_25_07_values.all id = true := by decide

def batch_25_08_values : List Bool := [accepted_1282]
theorem batch_25_08_ok : batch_25_08_values.all id = true := by decide

def batch_25_09_values : List Bool := [accepted_1284]
theorem batch_25_09_ok : batch_25_09_values.all id = true := by decide

def batch_25_10_values : List Bool := [accepted_1288]
theorem batch_25_10_ok : batch_25_10_values.all id = true := by decide

def batch_25_11_values : List Bool := [accepted_1296]
theorem batch_25_11_ok : batch_25_11_values.all id = true := by decide

def batch_25_12_values : List Bool := [accepted_1298]
theorem batch_25_12_ok : batch_25_12_values.all id = true := by decide

theorem leaf_1252_ok : checkAt 527 1000 box_1252 cert_1252 = true := by
  have h := List.all_eq_true.mp batch_25_00_ok accepted_1252 (by simp [batch_25_00_values])
  exact h
theorem leaf_1252_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1252.profileLo box_1252.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1252_ok
theorem branch_box_1252_nonnegative : ∀ j, 0 ≤ branch_box_1252.lower j ∧ 0 ≤ branch_box_1252.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1252, Box.profileLo, Box.profileHi, box_1252]
theorem leaf_1252_BranchSafe : CertificateConsequences.BranchSafe branch_box_1252 := by
  left; refine ⟨branch_box_1252_nonnegative, ?_⟩
  intro z hz; exact leaf_1252_sound hz

theorem leaf_1254_ok : checkAt 527 1000 box_1254 cert_1254 = true := by
  have h := List.all_eq_true.mp batch_25_01_ok accepted_1254 (by simp [batch_25_01_values])
  exact h
theorem leaf_1254_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1254.profileLo box_1254.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1254_ok
theorem branch_box_1254_nonnegative : ∀ j, 0 ≤ branch_box_1254.lower j ∧ 0 ≤ branch_box_1254.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1254, Box.profileLo, Box.profileHi, box_1254]
theorem leaf_1254_BranchSafe : CertificateConsequences.BranchSafe branch_box_1254 := by
  left; refine ⟨branch_box_1254_nonnegative, ?_⟩
  intro z hz; exact leaf_1254_sound hz

theorem leaf_1255_ok : checkAt 527 1000 box_1255 cert_1255 = true := by
  have h := List.all_eq_true.mp batch_25_02_ok accepted_1255 (by simp [batch_25_02_values])
  exact h
theorem leaf_1255_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1255.profileLo box_1255.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1255_ok
theorem branch_box_1255_nonnegative : ∀ j, 0 ≤ branch_box_1255.lower j ∧ 0 ≤ branch_box_1255.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1255, Box.profileLo, Box.profileHi, box_1255]
theorem leaf_1255_BranchSafe : CertificateConsequences.BranchSafe branch_box_1255 := by
  left; refine ⟨branch_box_1255_nonnegative, ?_⟩
  intro z hz; exact leaf_1255_sound hz

theorem leaf_1257_ok : checkAt 527 1000 box_1257 cert_1257 = true := by
  have h := List.all_eq_true.mp batch_25_03_ok accepted_1257 (by simp [batch_25_03_values])
  exact h
theorem leaf_1257_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1257.profileLo box_1257.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1257_ok
theorem branch_box_1257_nonnegative : ∀ j, 0 ≤ branch_box_1257.lower j ∧ 0 ≤ branch_box_1257.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1257, Box.profileLo, Box.profileHi, box_1257]
theorem leaf_1257_BranchSafe : CertificateConsequences.BranchSafe branch_box_1257 := by
  left; refine ⟨branch_box_1257_nonnegative, ?_⟩
  intro z hz; exact leaf_1257_sound hz

theorem leaf_1264_ok : checkAt 527 1000 box_1264 cert_1264 = true := by
  have h := List.all_eq_true.mp batch_25_04_ok accepted_1264 (by simp [batch_25_04_values])
  exact h
theorem leaf_1264_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1264.profileLo box_1264.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1264_ok
theorem branch_box_1264_nonnegative : ∀ j, 0 ≤ branch_box_1264.lower j ∧ 0 ≤ branch_box_1264.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1264, Box.profileLo, Box.profileHi, box_1264]
theorem leaf_1264_BranchSafe : CertificateConsequences.BranchSafe branch_box_1264 := by
  left; refine ⟨branch_box_1264_nonnegative, ?_⟩
  intro z hz; exact leaf_1264_sound hz

theorem leaf_1267_ok : checkAt 527 1000 box_1267 cert_1267 = true := by
  have h := List.all_eq_true.mp batch_25_05_ok accepted_1267 (by simp [batch_25_05_values])
  exact h
theorem leaf_1267_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1267.profileLo box_1267.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1267_ok
theorem branch_box_1267_nonnegative : ∀ j, 0 ≤ branch_box_1267.lower j ∧ 0 ≤ branch_box_1267.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1267, Box.profileLo, Box.profileHi, box_1267]
theorem leaf_1267_BranchSafe : CertificateConsequences.BranchSafe branch_box_1267 := by
  left; refine ⟨branch_box_1267_nonnegative, ?_⟩
  intro z hz; exact leaf_1267_sound hz

theorem leaf_1270_ok : checkAt 527 1000 box_1270 cert_1270 = true := by
  have h := List.all_eq_true.mp batch_25_06_ok accepted_1270 (by simp [batch_25_06_values])
  exact h
theorem leaf_1270_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1270.profileLo box_1270.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1270_ok
theorem branch_box_1270_nonnegative : ∀ j, 0 ≤ branch_box_1270.lower j ∧ 0 ≤ branch_box_1270.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1270, Box.profileLo, Box.profileHi, box_1270]
theorem leaf_1270_BranchSafe : CertificateConsequences.BranchSafe branch_box_1270 := by
  left; refine ⟨branch_box_1270_nonnegative, ?_⟩
  intro z hz; exact leaf_1270_sound hz

theorem leaf_1273_ok : checkAt 527 1000 box_1273 cert_1273 = true := by
  have h := List.all_eq_true.mp batch_25_07_ok accepted_1273 (by simp [batch_25_07_values])
  exact h
theorem leaf_1273_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1273.profileLo box_1273.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1273_ok
theorem branch_box_1273_nonnegative : ∀ j, 0 ≤ branch_box_1273.lower j ∧ 0 ≤ branch_box_1273.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1273, Box.profileLo, Box.profileHi, box_1273]
theorem leaf_1273_BranchSafe : CertificateConsequences.BranchSafe branch_box_1273 := by
  left; refine ⟨branch_box_1273_nonnegative, ?_⟩
  intro z hz; exact leaf_1273_sound hz

theorem leaf_1282_ok : checkAt 527 1000 box_1282 cert_1282 = true := by
  have h := List.all_eq_true.mp batch_25_08_ok accepted_1282 (by simp [batch_25_08_values])
  exact h
theorem leaf_1282_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1282.profileLo box_1282.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1282_ok
theorem branch_box_1282_nonnegative : ∀ j, 0 ≤ branch_box_1282.lower j ∧ 0 ≤ branch_box_1282.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1282, Box.profileLo, Box.profileHi, box_1282]
theorem leaf_1282_BranchSafe : CertificateConsequences.BranchSafe branch_box_1282 := by
  left; refine ⟨branch_box_1282_nonnegative, ?_⟩
  intro z hz; exact leaf_1282_sound hz

theorem leaf_1284_ok : checkAt 527 1000 box_1284 cert_1284 = true := by
  have h := List.all_eq_true.mp batch_25_09_ok accepted_1284 (by simp [batch_25_09_values])
  exact h
theorem leaf_1284_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1284.profileLo box_1284.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1284_ok
theorem branch_box_1284_nonnegative : ∀ j, 0 ≤ branch_box_1284.lower j ∧ 0 ≤ branch_box_1284.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1284, Box.profileLo, Box.profileHi, box_1284]
theorem leaf_1284_BranchSafe : CertificateConsequences.BranchSafe branch_box_1284 := by
  left; refine ⟨branch_box_1284_nonnegative, ?_⟩
  intro z hz; exact leaf_1284_sound hz

theorem leaf_1288_ok : checkAt 527 1000 box_1288 cert_1288 = true := by
  have h := List.all_eq_true.mp batch_25_10_ok accepted_1288 (by simp [batch_25_10_values])
  exact h
theorem leaf_1288_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1288.profileLo box_1288.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1288_ok
theorem branch_box_1288_nonnegative : ∀ j, 0 ≤ branch_box_1288.lower j ∧ 0 ≤ branch_box_1288.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1288, Box.profileLo, Box.profileHi, box_1288]
theorem leaf_1288_BranchSafe : CertificateConsequences.BranchSafe branch_box_1288 := by
  left; refine ⟨branch_box_1288_nonnegative, ?_⟩
  intro z hz; exact leaf_1288_sound hz

theorem leaf_1296_ok : checkAt 527 1000 box_1296 cert_1296 = true := by
  have h := List.all_eq_true.mp batch_25_11_ok accepted_1296 (by simp [batch_25_11_values])
  exact h
theorem leaf_1296_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1296.profileLo box_1296.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1296_ok
theorem branch_box_1296_nonnegative : ∀ j, 0 ≤ branch_box_1296.lower j ∧ 0 ≤ branch_box_1296.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1296, Box.profileLo, Box.profileHi, box_1296]
theorem leaf_1296_BranchSafe : CertificateConsequences.BranchSafe branch_box_1296 := by
  left; refine ⟨branch_box_1296_nonnegative, ?_⟩
  intro z hz; exact leaf_1296_sound hz

theorem leaf_1298_ok : checkAt 527 1000 box_1298 cert_1298 = true := by
  have h := List.all_eq_true.mp batch_25_12_ok accepted_1298 (by simp [batch_25_12_values])
  exact h
theorem leaf_1298_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1298.profileLo box_1298.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1298_ok
theorem branch_box_1298_nonnegative : ∀ j, 0 ≤ branch_box_1298.lower j ∧ 0 ≤ branch_box_1298.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1298, Box.profileLo, Box.profileHi, box_1298]
theorem leaf_1298_BranchSafe : CertificateConsequences.BranchSafe branch_box_1298 := by
  left; refine ⟨branch_box_1298_nonnegative, ?_⟩
  intro z hz; exact leaf_1298_sound hz

#print axioms batch_25_00_ok
#print axioms leaf_1252_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
