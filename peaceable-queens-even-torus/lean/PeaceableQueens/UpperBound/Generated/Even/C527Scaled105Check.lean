import PeaceableQueens.UpperBound.Generated.Even.C527Scaled105Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_105_00_values : List Bool := [accepted_5250]
theorem batch_105_00_ok : batch_105_00_values.all id = true := by decide

def batch_105_01_values : List Bool := [accepted_5252]
theorem batch_105_01_ok : batch_105_01_values.all id = true := by decide

def batch_105_02_values : List Bool := [accepted_5253]
theorem batch_105_02_ok : batch_105_02_values.all id = true := by decide

def batch_105_03_values : List Bool := [accepted_5254]
theorem batch_105_03_ok : batch_105_03_values.all id = true := by decide

def batch_105_04_values : List Bool := [accepted_5257]
theorem batch_105_04_ok : batch_105_04_values.all id = true := by decide

def batch_105_05_values : List Bool := [accepted_5260]
theorem batch_105_05_ok : batch_105_05_values.all id = true := by decide

def batch_105_06_values : List Bool := [accepted_5261]
theorem batch_105_06_ok : batch_105_06_values.all id = true := by decide

def batch_105_07_values : List Bool := [accepted_5262]
theorem batch_105_07_ok : batch_105_07_values.all id = true := by decide

def batch_105_08_values : List Bool := [accepted_5267]
theorem batch_105_08_ok : batch_105_08_values.all id = true := by decide

def batch_105_09_values : List Bool := [accepted_5269]
theorem batch_105_09_ok : batch_105_09_values.all id = true := by decide

def batch_105_10_values : List Bool := [accepted_5271]
theorem batch_105_10_ok : batch_105_10_values.all id = true := by decide

def batch_105_11_values : List Bool := [accepted_5273]
theorem batch_105_11_ok : batch_105_11_values.all id = true := by decide

def batch_105_12_values : List Bool := [accepted_5274]
theorem batch_105_12_ok : batch_105_12_values.all id = true := by decide

def batch_105_13_values : List Bool := [accepted_5275]
theorem batch_105_13_ok : batch_105_13_values.all id = true := by decide

def batch_105_14_values : List Bool := [accepted_5277]
theorem batch_105_14_ok : batch_105_14_values.all id = true := by decide

def batch_105_15_values : List Bool := [accepted_5279]
theorem batch_105_15_ok : batch_105_15_values.all id = true := by decide

def batch_105_16_values : List Bool := [accepted_5280]
theorem batch_105_16_ok : batch_105_16_values.all id = true := by decide

def batch_105_17_values : List Bool := [accepted_5281]
theorem batch_105_17_ok : batch_105_17_values.all id = true := by decide

def batch_105_18_values : List Bool := [accepted_5282]
theorem batch_105_18_ok : batch_105_18_values.all id = true := by decide

def batch_105_19_values : List Bool := [accepted_5289]
theorem batch_105_19_ok : batch_105_19_values.all id = true := by decide

def batch_105_20_values : List Bool := [accepted_5290]
theorem batch_105_20_ok : batch_105_20_values.all id = true := by decide

def batch_105_21_values : List Bool := [accepted_5291]
theorem batch_105_21_ok : batch_105_21_values.all id = true := by decide

def batch_105_22_values : List Bool := [accepted_5293]
theorem batch_105_22_ok : batch_105_22_values.all id = true := by decide

def batch_105_23_values : List Bool := [accepted_5294]
theorem batch_105_23_ok : batch_105_23_values.all id = true := by decide

theorem leaf_5250_ok : checkAt 527 1000 box_5250 cert_5250 = true := by
  have h := List.all_eq_true.mp batch_105_00_ok accepted_5250 (by simp [batch_105_00_values])
  exact h
theorem leaf_5250_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5250.profileLo box_5250.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5250_ok
theorem branch_box_5250_nonnegative : ∀ j, 0 ≤ branch_box_5250.lower j ∧ 0 ≤ branch_box_5250.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5250, Box.profileLo, Box.profileHi, box_5250]
theorem leaf_5250_BranchSafe : CertificateConsequences.BranchSafe branch_box_5250 := by
  left; refine ⟨branch_box_5250_nonnegative, ?_⟩
  intro z hz; exact leaf_5250_sound hz

theorem leaf_5252_ok : checkAt 527 1000 box_5252 cert_5252 = true := by
  have h := List.all_eq_true.mp batch_105_01_ok accepted_5252 (by simp [batch_105_01_values])
  exact h
theorem leaf_5252_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5252.profileLo box_5252.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5252_ok
theorem branch_box_5252_nonnegative : ∀ j, 0 ≤ branch_box_5252.lower j ∧ 0 ≤ branch_box_5252.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5252, Box.profileLo, Box.profileHi, box_5252]
theorem leaf_5252_BranchSafe : CertificateConsequences.BranchSafe branch_box_5252 := by
  left; refine ⟨branch_box_5252_nonnegative, ?_⟩
  intro z hz; exact leaf_5252_sound hz

theorem leaf_5253_ok : checkAt 527 1000 box_5253 cert_5253 = true := by
  have h := List.all_eq_true.mp batch_105_02_ok accepted_5253 (by simp [batch_105_02_values])
  exact h
theorem leaf_5253_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5253.profileLo box_5253.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5253_ok
theorem branch_box_5253_nonnegative : ∀ j, 0 ≤ branch_box_5253.lower j ∧ 0 ≤ branch_box_5253.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5253, Box.profileLo, Box.profileHi, box_5253]
theorem leaf_5253_BranchSafe : CertificateConsequences.BranchSafe branch_box_5253 := by
  left; refine ⟨branch_box_5253_nonnegative, ?_⟩
  intro z hz; exact leaf_5253_sound hz

theorem leaf_5254_ok : checkAt 527 1000 box_5254 cert_5254 = true := by
  have h := List.all_eq_true.mp batch_105_03_ok accepted_5254 (by simp [batch_105_03_values])
  exact h
theorem leaf_5254_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5254.profileLo box_5254.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5254_ok
theorem branch_box_5254_nonnegative : ∀ j, 0 ≤ branch_box_5254.lower j ∧ 0 ≤ branch_box_5254.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5254, Box.profileLo, Box.profileHi, box_5254]
theorem leaf_5254_BranchSafe : CertificateConsequences.BranchSafe branch_box_5254 := by
  left; refine ⟨branch_box_5254_nonnegative, ?_⟩
  intro z hz; exact leaf_5254_sound hz

theorem leaf_5257_ok : checkAt 527 1000 box_5257 cert_5257 = true := by
  have h := List.all_eq_true.mp batch_105_04_ok accepted_5257 (by simp [batch_105_04_values])
  exact h
theorem leaf_5257_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5257.profileLo box_5257.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5257_ok
theorem branch_box_5257_nonnegative : ∀ j, 0 ≤ branch_box_5257.lower j ∧ 0 ≤ branch_box_5257.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5257, Box.profileLo, Box.profileHi, box_5257]
theorem leaf_5257_BranchSafe : CertificateConsequences.BranchSafe branch_box_5257 := by
  left; refine ⟨branch_box_5257_nonnegative, ?_⟩
  intro z hz; exact leaf_5257_sound hz

theorem leaf_5260_ok : checkAt 527 1000 box_5260 cert_5260 = true := by
  have h := List.all_eq_true.mp batch_105_05_ok accepted_5260 (by simp [batch_105_05_values])
  exact h
theorem leaf_5260_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5260.profileLo box_5260.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5260_ok
theorem branch_box_5260_nonnegative : ∀ j, 0 ≤ branch_box_5260.lower j ∧ 0 ≤ branch_box_5260.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5260, Box.profileLo, Box.profileHi, box_5260]
theorem leaf_5260_BranchSafe : CertificateConsequences.BranchSafe branch_box_5260 := by
  left; refine ⟨branch_box_5260_nonnegative, ?_⟩
  intro z hz; exact leaf_5260_sound hz

theorem leaf_5261_ok : checkAt 527 1000 box_5261 cert_5261 = true := by
  have h := List.all_eq_true.mp batch_105_06_ok accepted_5261 (by simp [batch_105_06_values])
  exact h
theorem leaf_5261_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5261.profileLo box_5261.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5261_ok
theorem branch_box_5261_nonnegative : ∀ j, 0 ≤ branch_box_5261.lower j ∧ 0 ≤ branch_box_5261.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5261, Box.profileLo, Box.profileHi, box_5261]
theorem leaf_5261_BranchSafe : CertificateConsequences.BranchSafe branch_box_5261 := by
  left; refine ⟨branch_box_5261_nonnegative, ?_⟩
  intro z hz; exact leaf_5261_sound hz

theorem leaf_5262_ok : checkAt 527 1000 box_5262 cert_5262 = true := by
  have h := List.all_eq_true.mp batch_105_07_ok accepted_5262 (by simp [batch_105_07_values])
  exact h
theorem leaf_5262_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5262.profileLo box_5262.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5262_ok
theorem branch_box_5262_nonnegative : ∀ j, 0 ≤ branch_box_5262.lower j ∧ 0 ≤ branch_box_5262.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5262, Box.profileLo, Box.profileHi, box_5262]
theorem leaf_5262_BranchSafe : CertificateConsequences.BranchSafe branch_box_5262 := by
  left; refine ⟨branch_box_5262_nonnegative, ?_⟩
  intro z hz; exact leaf_5262_sound hz

theorem leaf_5267_ok : checkAt 527 1000 box_5267 cert_5267 = true := by
  have h := List.all_eq_true.mp batch_105_08_ok accepted_5267 (by simp [batch_105_08_values])
  exact h
theorem leaf_5267_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5267.profileLo box_5267.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5267_ok
theorem branch_box_5267_nonnegative : ∀ j, 0 ≤ branch_box_5267.lower j ∧ 0 ≤ branch_box_5267.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5267, Box.profileLo, Box.profileHi, box_5267]
theorem leaf_5267_BranchSafe : CertificateConsequences.BranchSafe branch_box_5267 := by
  left; refine ⟨branch_box_5267_nonnegative, ?_⟩
  intro z hz; exact leaf_5267_sound hz

theorem leaf_5269_ok : checkAt 527 1000 box_5269 cert_5269 = true := by
  have h := List.all_eq_true.mp batch_105_09_ok accepted_5269 (by simp [batch_105_09_values])
  exact h
theorem leaf_5269_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5269.profileLo box_5269.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5269_ok
theorem branch_box_5269_nonnegative : ∀ j, 0 ≤ branch_box_5269.lower j ∧ 0 ≤ branch_box_5269.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5269, Box.profileLo, Box.profileHi, box_5269]
theorem leaf_5269_BranchSafe : CertificateConsequences.BranchSafe branch_box_5269 := by
  left; refine ⟨branch_box_5269_nonnegative, ?_⟩
  intro z hz; exact leaf_5269_sound hz

theorem leaf_5271_ok : checkAt 527 1000 box_5271 cert_5271 = true := by
  have h := List.all_eq_true.mp batch_105_10_ok accepted_5271 (by simp [batch_105_10_values])
  exact h
theorem leaf_5271_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5271.profileLo box_5271.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5271_ok
theorem branch_box_5271_nonnegative : ∀ j, 0 ≤ branch_box_5271.lower j ∧ 0 ≤ branch_box_5271.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5271, Box.profileLo, Box.profileHi, box_5271]
theorem leaf_5271_BranchSafe : CertificateConsequences.BranchSafe branch_box_5271 := by
  left; refine ⟨branch_box_5271_nonnegative, ?_⟩
  intro z hz; exact leaf_5271_sound hz

theorem leaf_5273_ok : checkAt 527 1000 box_5273 cert_5273 = true := by
  have h := List.all_eq_true.mp batch_105_11_ok accepted_5273 (by simp [batch_105_11_values])
  exact h
theorem leaf_5273_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5273.profileLo box_5273.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5273_ok
theorem branch_box_5273_nonnegative : ∀ j, 0 ≤ branch_box_5273.lower j ∧ 0 ≤ branch_box_5273.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5273, Box.profileLo, Box.profileHi, box_5273]
theorem leaf_5273_BranchSafe : CertificateConsequences.BranchSafe branch_box_5273 := by
  left; refine ⟨branch_box_5273_nonnegative, ?_⟩
  intro z hz; exact leaf_5273_sound hz

theorem leaf_5274_ok : checkAt 527 1000 box_5274 cert_5274 = true := by
  have h := List.all_eq_true.mp batch_105_12_ok accepted_5274 (by simp [batch_105_12_values])
  exact h
theorem leaf_5274_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5274.profileLo box_5274.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5274_ok
theorem branch_box_5274_nonnegative : ∀ j, 0 ≤ branch_box_5274.lower j ∧ 0 ≤ branch_box_5274.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5274, Box.profileLo, Box.profileHi, box_5274]
theorem leaf_5274_BranchSafe : CertificateConsequences.BranchSafe branch_box_5274 := by
  left; refine ⟨branch_box_5274_nonnegative, ?_⟩
  intro z hz; exact leaf_5274_sound hz

theorem leaf_5275_ok : checkAt 527 1000 box_5275 cert_5275 = true := by
  have h := List.all_eq_true.mp batch_105_13_ok accepted_5275 (by simp [batch_105_13_values])
  exact h
theorem leaf_5275_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5275.profileLo box_5275.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5275_ok
theorem branch_box_5275_nonnegative : ∀ j, 0 ≤ branch_box_5275.lower j ∧ 0 ≤ branch_box_5275.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5275, Box.profileLo, Box.profileHi, box_5275]
theorem leaf_5275_BranchSafe : CertificateConsequences.BranchSafe branch_box_5275 := by
  left; refine ⟨branch_box_5275_nonnegative, ?_⟩
  intro z hz; exact leaf_5275_sound hz

theorem leaf_5277_ok : checkAt 527 1000 box_5277 cert_5277 = true := by
  have h := List.all_eq_true.mp batch_105_14_ok accepted_5277 (by simp [batch_105_14_values])
  exact h
theorem leaf_5277_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5277.profileLo box_5277.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5277_ok
theorem branch_box_5277_nonnegative : ∀ j, 0 ≤ branch_box_5277.lower j ∧ 0 ≤ branch_box_5277.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5277, Box.profileLo, Box.profileHi, box_5277]
theorem leaf_5277_BranchSafe : CertificateConsequences.BranchSafe branch_box_5277 := by
  left; refine ⟨branch_box_5277_nonnegative, ?_⟩
  intro z hz; exact leaf_5277_sound hz

theorem leaf_5279_ok : checkAt 527 1000 box_5279 cert_5279 = true := by
  have h := List.all_eq_true.mp batch_105_15_ok accepted_5279 (by simp [batch_105_15_values])
  exact h
theorem leaf_5279_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5279.profileLo box_5279.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5279_ok
theorem branch_box_5279_nonnegative : ∀ j, 0 ≤ branch_box_5279.lower j ∧ 0 ≤ branch_box_5279.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5279, Box.profileLo, Box.profileHi, box_5279]
theorem leaf_5279_BranchSafe : CertificateConsequences.BranchSafe branch_box_5279 := by
  left; refine ⟨branch_box_5279_nonnegative, ?_⟩
  intro z hz; exact leaf_5279_sound hz

theorem leaf_5280_ok : checkAt 527 1000 box_5280 cert_5280 = true := by
  have h := List.all_eq_true.mp batch_105_16_ok accepted_5280 (by simp [batch_105_16_values])
  exact h
theorem leaf_5280_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5280.profileLo box_5280.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5280_ok
theorem branch_box_5280_nonnegative : ∀ j, 0 ≤ branch_box_5280.lower j ∧ 0 ≤ branch_box_5280.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5280, Box.profileLo, Box.profileHi, box_5280]
theorem leaf_5280_BranchSafe : CertificateConsequences.BranchSafe branch_box_5280 := by
  left; refine ⟨branch_box_5280_nonnegative, ?_⟩
  intro z hz; exact leaf_5280_sound hz

theorem leaf_5281_ok : checkAt 527 1000 box_5281 cert_5281 = true := by
  have h := List.all_eq_true.mp batch_105_17_ok accepted_5281 (by simp [batch_105_17_values])
  exact h
theorem leaf_5281_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5281.profileLo box_5281.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5281_ok
theorem branch_box_5281_nonnegative : ∀ j, 0 ≤ branch_box_5281.lower j ∧ 0 ≤ branch_box_5281.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5281, Box.profileLo, Box.profileHi, box_5281]
theorem leaf_5281_BranchSafe : CertificateConsequences.BranchSafe branch_box_5281 := by
  left; refine ⟨branch_box_5281_nonnegative, ?_⟩
  intro z hz; exact leaf_5281_sound hz

theorem leaf_5282_ok : checkAt 527 1000 box_5282 cert_5282 = true := by
  have h := List.all_eq_true.mp batch_105_18_ok accepted_5282 (by simp [batch_105_18_values])
  exact h
theorem leaf_5282_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5282.profileLo box_5282.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5282_ok
theorem branch_box_5282_nonnegative : ∀ j, 0 ≤ branch_box_5282.lower j ∧ 0 ≤ branch_box_5282.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5282, Box.profileLo, Box.profileHi, box_5282]
theorem leaf_5282_BranchSafe : CertificateConsequences.BranchSafe branch_box_5282 := by
  left; refine ⟨branch_box_5282_nonnegative, ?_⟩
  intro z hz; exact leaf_5282_sound hz

theorem leaf_5289_ok : checkAt 527 1000 box_5289 cert_5289 = true := by
  have h := List.all_eq_true.mp batch_105_19_ok accepted_5289 (by simp [batch_105_19_values])
  exact h
theorem leaf_5289_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5289.profileLo box_5289.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5289_ok
theorem branch_box_5289_nonnegative : ∀ j, 0 ≤ branch_box_5289.lower j ∧ 0 ≤ branch_box_5289.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5289, Box.profileLo, Box.profileHi, box_5289]
theorem leaf_5289_BranchSafe : CertificateConsequences.BranchSafe branch_box_5289 := by
  left; refine ⟨branch_box_5289_nonnegative, ?_⟩
  intro z hz; exact leaf_5289_sound hz

theorem leaf_5290_ok : checkAt 527 1000 box_5290 cert_5290 = true := by
  have h := List.all_eq_true.mp batch_105_20_ok accepted_5290 (by simp [batch_105_20_values])
  exact h
theorem leaf_5290_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5290.profileLo box_5290.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5290_ok
theorem branch_box_5290_nonnegative : ∀ j, 0 ≤ branch_box_5290.lower j ∧ 0 ≤ branch_box_5290.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5290, Box.profileLo, Box.profileHi, box_5290]
theorem leaf_5290_BranchSafe : CertificateConsequences.BranchSafe branch_box_5290 := by
  left; refine ⟨branch_box_5290_nonnegative, ?_⟩
  intro z hz; exact leaf_5290_sound hz

theorem leaf_5291_ok : checkAt 527 1000 box_5291 cert_5291 = true := by
  have h := List.all_eq_true.mp batch_105_21_ok accepted_5291 (by simp [batch_105_21_values])
  exact h
theorem leaf_5291_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5291.profileLo box_5291.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5291_ok
theorem branch_box_5291_nonnegative : ∀ j, 0 ≤ branch_box_5291.lower j ∧ 0 ≤ branch_box_5291.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5291, Box.profileLo, Box.profileHi, box_5291]
theorem leaf_5291_BranchSafe : CertificateConsequences.BranchSafe branch_box_5291 := by
  left; refine ⟨branch_box_5291_nonnegative, ?_⟩
  intro z hz; exact leaf_5291_sound hz

theorem leaf_5293_ok : checkAt 527 1000 box_5293 cert_5293 = true := by
  have h := List.all_eq_true.mp batch_105_22_ok accepted_5293 (by simp [batch_105_22_values])
  exact h
theorem leaf_5293_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5293.profileLo box_5293.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5293_ok
theorem branch_box_5293_nonnegative : ∀ j, 0 ≤ branch_box_5293.lower j ∧ 0 ≤ branch_box_5293.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5293, Box.profileLo, Box.profileHi, box_5293]
theorem leaf_5293_BranchSafe : CertificateConsequences.BranchSafe branch_box_5293 := by
  left; refine ⟨branch_box_5293_nonnegative, ?_⟩
  intro z hz; exact leaf_5293_sound hz

theorem leaf_5294_ok : checkAt 527 1000 box_5294 cert_5294 = true := by
  have h := List.all_eq_true.mp batch_105_23_ok accepted_5294 (by simp [batch_105_23_values])
  exact h
theorem leaf_5294_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5294.profileLo box_5294.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5294_ok
theorem branch_box_5294_nonnegative : ∀ j, 0 ≤ branch_box_5294.lower j ∧ 0 ≤ branch_box_5294.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5294, Box.profileLo, Box.profileHi, box_5294]
theorem leaf_5294_BranchSafe : CertificateConsequences.BranchSafe branch_box_5294 := by
  left; refine ⟨branch_box_5294_nonnegative, ?_⟩
  intro z hz; exact leaf_5294_sound hz

#print axioms batch_105_00_ok
#print axioms leaf_5250_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
