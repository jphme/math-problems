import PeaceableQueens.UpperBound.Generated.Even.C527Scaled122Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_122_00_values : List Bool := [accepted_6101]
theorem batch_122_00_ok : batch_122_00_values.all id = true := by decide

def batch_122_01_values : List Bool := [accepted_6102]
theorem batch_122_01_ok : batch_122_01_values.all id = true := by decide

def batch_122_02_values : List Bool := [accepted_6109]
theorem batch_122_02_ok : batch_122_02_values.all id = true := by decide

def batch_122_03_values : List Bool := [accepted_6110]
theorem batch_122_03_ok : batch_122_03_values.all id = true := by decide

def batch_122_04_values : List Bool := [accepted_6111]
theorem batch_122_04_ok : batch_122_04_values.all id = true := by decide

def batch_122_05_values : List Bool := [accepted_6112]
theorem batch_122_05_ok : batch_122_05_values.all id = true := by decide

def batch_122_06_values : List Bool := [accepted_6113]
theorem batch_122_06_ok : batch_122_06_values.all id = true := by decide

def batch_122_07_values : List Bool := [accepted_6114]
theorem batch_122_07_ok : batch_122_07_values.all id = true := by decide

def batch_122_08_values : List Bool := [accepted_6116]
theorem batch_122_08_ok : batch_122_08_values.all id = true := by decide

def batch_122_09_values : List Bool := [accepted_6117]
theorem batch_122_09_ok : batch_122_09_values.all id = true := by decide

def batch_122_10_values : List Bool := [accepted_6118]
theorem batch_122_10_ok : batch_122_10_values.all id = true := by decide

def batch_122_11_values : List Bool := [accepted_6121]
theorem batch_122_11_ok : batch_122_11_values.all id = true := by decide

def batch_122_12_values : List Bool := [accepted_6124]
theorem batch_122_12_ok : batch_122_12_values.all id = true := by decide

def batch_122_13_values : List Bool := [accepted_6125]
theorem batch_122_13_ok : batch_122_13_values.all id = true := by decide

def batch_122_14_values : List Bool := [accepted_6127]
theorem batch_122_14_ok : batch_122_14_values.all id = true := by decide

def batch_122_15_values : List Bool := [accepted_6129]
theorem batch_122_15_ok : batch_122_15_values.all id = true := by decide

def batch_122_16_values : List Bool := [accepted_6130]
theorem batch_122_16_ok : batch_122_16_values.all id = true := by decide

def batch_122_17_values : List Bool := [accepted_6133]
theorem batch_122_17_ok : batch_122_17_values.all id = true := by decide

def batch_122_18_values : List Bool := [accepted_6134]
theorem batch_122_18_ok : batch_122_18_values.all id = true := by decide

def batch_122_19_values : List Bool := [accepted_6135]
theorem batch_122_19_ok : batch_122_19_values.all id = true := by decide

def batch_122_20_values : List Bool := [accepted_6139]
theorem batch_122_20_ok : batch_122_20_values.all id = true := by decide

def batch_122_21_values : List Bool := [accepted_6140]
theorem batch_122_21_ok : batch_122_21_values.all id = true := by decide

def batch_122_22_values : List Bool := [accepted_6147]
theorem batch_122_22_ok : batch_122_22_values.all id = true := by decide

def batch_122_23_values : List Bool := [accepted_6148]
theorem batch_122_23_ok : batch_122_23_values.all id = true := by decide

theorem leaf_6101_ok : checkAt 527 1000 box_6101 cert_6101 = true := by
  have h := List.all_eq_true.mp batch_122_00_ok accepted_6101 (by simp [batch_122_00_values])
  exact h
theorem leaf_6101_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6101.profileLo box_6101.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6101_ok
theorem branch_box_6101_nonnegative : ∀ j, 0 ≤ branch_box_6101.lower j ∧ 0 ≤ branch_box_6101.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6101, Box.profileLo, Box.profileHi, box_6101]
theorem leaf_6101_BranchSafe : CertificateConsequences.BranchSafe branch_box_6101 := by
  left; refine ⟨branch_box_6101_nonnegative, ?_⟩
  intro z hz; exact leaf_6101_sound hz

theorem leaf_6102_ok : checkAt 527 1000 box_6102 cert_6102 = true := by
  have h := List.all_eq_true.mp batch_122_01_ok accepted_6102 (by simp [batch_122_01_values])
  exact h
theorem leaf_6102_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6102.profileLo box_6102.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6102_ok
theorem branch_box_6102_nonnegative : ∀ j, 0 ≤ branch_box_6102.lower j ∧ 0 ≤ branch_box_6102.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6102, Box.profileLo, Box.profileHi, box_6102]
theorem leaf_6102_BranchSafe : CertificateConsequences.BranchSafe branch_box_6102 := by
  left; refine ⟨branch_box_6102_nonnegative, ?_⟩
  intro z hz; exact leaf_6102_sound hz

theorem leaf_6109_ok : checkAt 527 1000 box_6109 cert_6109 = true := by
  have h := List.all_eq_true.mp batch_122_02_ok accepted_6109 (by simp [batch_122_02_values])
  exact h
theorem leaf_6109_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6109.profileLo box_6109.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6109_ok
theorem branch_box_6109_nonnegative : ∀ j, 0 ≤ branch_box_6109.lower j ∧ 0 ≤ branch_box_6109.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6109, Box.profileLo, Box.profileHi, box_6109]
theorem leaf_6109_BranchSafe : CertificateConsequences.BranchSafe branch_box_6109 := by
  left; refine ⟨branch_box_6109_nonnegative, ?_⟩
  intro z hz; exact leaf_6109_sound hz

theorem leaf_6110_ok : checkAt 527 1000 box_6110 cert_6110 = true := by
  have h := List.all_eq_true.mp batch_122_03_ok accepted_6110 (by simp [batch_122_03_values])
  exact h
theorem leaf_6110_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6110.profileLo box_6110.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6110_ok
theorem branch_box_6110_nonnegative : ∀ j, 0 ≤ branch_box_6110.lower j ∧ 0 ≤ branch_box_6110.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6110, Box.profileLo, Box.profileHi, box_6110]
theorem leaf_6110_BranchSafe : CertificateConsequences.BranchSafe branch_box_6110 := by
  left; refine ⟨branch_box_6110_nonnegative, ?_⟩
  intro z hz; exact leaf_6110_sound hz

theorem leaf_6111_ok : checkAt 527 1000 box_6111 cert_6111 = true := by
  have h := List.all_eq_true.mp batch_122_04_ok accepted_6111 (by simp [batch_122_04_values])
  exact h
theorem leaf_6111_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6111.profileLo box_6111.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6111_ok
theorem branch_box_6111_nonnegative : ∀ j, 0 ≤ branch_box_6111.lower j ∧ 0 ≤ branch_box_6111.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6111, Box.profileLo, Box.profileHi, box_6111]
theorem leaf_6111_BranchSafe : CertificateConsequences.BranchSafe branch_box_6111 := by
  left; refine ⟨branch_box_6111_nonnegative, ?_⟩
  intro z hz; exact leaf_6111_sound hz

theorem leaf_6112_ok : checkAt 527 1000 box_6112 cert_6112 = true := by
  have h := List.all_eq_true.mp batch_122_05_ok accepted_6112 (by simp [batch_122_05_values])
  exact h
theorem leaf_6112_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6112.profileLo box_6112.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6112_ok
theorem branch_box_6112_nonnegative : ∀ j, 0 ≤ branch_box_6112.lower j ∧ 0 ≤ branch_box_6112.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6112, Box.profileLo, Box.profileHi, box_6112]
theorem leaf_6112_BranchSafe : CertificateConsequences.BranchSafe branch_box_6112 := by
  left; refine ⟨branch_box_6112_nonnegative, ?_⟩
  intro z hz; exact leaf_6112_sound hz

theorem leaf_6113_ok : checkAt 527 1000 box_6113 cert_6113 = true := by
  have h := List.all_eq_true.mp batch_122_06_ok accepted_6113 (by simp [batch_122_06_values])
  exact h
theorem leaf_6113_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6113.profileLo box_6113.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6113_ok
theorem branch_box_6113_nonnegative : ∀ j, 0 ≤ branch_box_6113.lower j ∧ 0 ≤ branch_box_6113.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6113, Box.profileLo, Box.profileHi, box_6113]
theorem leaf_6113_BranchSafe : CertificateConsequences.BranchSafe branch_box_6113 := by
  left; refine ⟨branch_box_6113_nonnegative, ?_⟩
  intro z hz; exact leaf_6113_sound hz

theorem leaf_6114_ok : checkAt 527 1000 box_6114 cert_6114 = true := by
  have h := List.all_eq_true.mp batch_122_07_ok accepted_6114 (by simp [batch_122_07_values])
  exact h
theorem leaf_6114_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6114.profileLo box_6114.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6114_ok
theorem branch_box_6114_nonnegative : ∀ j, 0 ≤ branch_box_6114.lower j ∧ 0 ≤ branch_box_6114.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6114, Box.profileLo, Box.profileHi, box_6114]
theorem leaf_6114_BranchSafe : CertificateConsequences.BranchSafe branch_box_6114 := by
  left; refine ⟨branch_box_6114_nonnegative, ?_⟩
  intro z hz; exact leaf_6114_sound hz

theorem leaf_6116_ok : checkAt 527 1000 box_6116 cert_6116 = true := by
  have h := List.all_eq_true.mp batch_122_08_ok accepted_6116 (by simp [batch_122_08_values])
  exact h
theorem leaf_6116_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6116.profileLo box_6116.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6116_ok
theorem branch_box_6116_nonnegative : ∀ j, 0 ≤ branch_box_6116.lower j ∧ 0 ≤ branch_box_6116.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6116, Box.profileLo, Box.profileHi, box_6116]
theorem leaf_6116_BranchSafe : CertificateConsequences.BranchSafe branch_box_6116 := by
  left; refine ⟨branch_box_6116_nonnegative, ?_⟩
  intro z hz; exact leaf_6116_sound hz

theorem leaf_6117_ok : checkAt 527 1000 box_6117 cert_6117 = true := by
  have h := List.all_eq_true.mp batch_122_09_ok accepted_6117 (by simp [batch_122_09_values])
  exact h
theorem leaf_6117_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6117.profileLo box_6117.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6117_ok
theorem branch_box_6117_nonnegative : ∀ j, 0 ≤ branch_box_6117.lower j ∧ 0 ≤ branch_box_6117.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6117, Box.profileLo, Box.profileHi, box_6117]
theorem leaf_6117_BranchSafe : CertificateConsequences.BranchSafe branch_box_6117 := by
  left; refine ⟨branch_box_6117_nonnegative, ?_⟩
  intro z hz; exact leaf_6117_sound hz

theorem leaf_6118_ok : checkAt 527 1000 box_6118 cert_6118 = true := by
  have h := List.all_eq_true.mp batch_122_10_ok accepted_6118 (by simp [batch_122_10_values])
  exact h
theorem leaf_6118_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6118.profileLo box_6118.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6118_ok
theorem branch_box_6118_nonnegative : ∀ j, 0 ≤ branch_box_6118.lower j ∧ 0 ≤ branch_box_6118.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6118, Box.profileLo, Box.profileHi, box_6118]
theorem leaf_6118_BranchSafe : CertificateConsequences.BranchSafe branch_box_6118 := by
  left; refine ⟨branch_box_6118_nonnegative, ?_⟩
  intro z hz; exact leaf_6118_sound hz

theorem leaf_6121_ok : checkAt 527 1000 box_6121 cert_6121 = true := by
  have h := List.all_eq_true.mp batch_122_11_ok accepted_6121 (by simp [batch_122_11_values])
  exact h
theorem leaf_6121_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6121.profileLo box_6121.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6121_ok
theorem branch_box_6121_nonnegative : ∀ j, 0 ≤ branch_box_6121.lower j ∧ 0 ≤ branch_box_6121.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6121, Box.profileLo, Box.profileHi, box_6121]
theorem leaf_6121_BranchSafe : CertificateConsequences.BranchSafe branch_box_6121 := by
  left; refine ⟨branch_box_6121_nonnegative, ?_⟩
  intro z hz; exact leaf_6121_sound hz

theorem leaf_6124_ok : checkAt 527 1000 box_6124 cert_6124 = true := by
  have h := List.all_eq_true.mp batch_122_12_ok accepted_6124 (by simp [batch_122_12_values])
  exact h
theorem leaf_6124_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6124.profileLo box_6124.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6124_ok
theorem branch_box_6124_nonnegative : ∀ j, 0 ≤ branch_box_6124.lower j ∧ 0 ≤ branch_box_6124.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6124, Box.profileLo, Box.profileHi, box_6124]
theorem leaf_6124_BranchSafe : CertificateConsequences.BranchSafe branch_box_6124 := by
  left; refine ⟨branch_box_6124_nonnegative, ?_⟩
  intro z hz; exact leaf_6124_sound hz

theorem leaf_6125_ok : checkAt 527 1000 box_6125 cert_6125 = true := by
  have h := List.all_eq_true.mp batch_122_13_ok accepted_6125 (by simp [batch_122_13_values])
  exact h
theorem leaf_6125_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6125.profileLo box_6125.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6125_ok
theorem branch_box_6125_nonnegative : ∀ j, 0 ≤ branch_box_6125.lower j ∧ 0 ≤ branch_box_6125.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6125, Box.profileLo, Box.profileHi, box_6125]
theorem leaf_6125_BranchSafe : CertificateConsequences.BranchSafe branch_box_6125 := by
  left; refine ⟨branch_box_6125_nonnegative, ?_⟩
  intro z hz; exact leaf_6125_sound hz

theorem leaf_6127_ok : checkAt 527 1000 box_6127 cert_6127 = true := by
  have h := List.all_eq_true.mp batch_122_14_ok accepted_6127 (by simp [batch_122_14_values])
  exact h
theorem leaf_6127_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6127.profileLo box_6127.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6127_ok
theorem branch_box_6127_nonnegative : ∀ j, 0 ≤ branch_box_6127.lower j ∧ 0 ≤ branch_box_6127.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6127, Box.profileLo, Box.profileHi, box_6127]
theorem leaf_6127_BranchSafe : CertificateConsequences.BranchSafe branch_box_6127 := by
  left; refine ⟨branch_box_6127_nonnegative, ?_⟩
  intro z hz; exact leaf_6127_sound hz

theorem leaf_6129_ok : checkAt 527 1000 box_6129 cert_6129 = true := by
  have h := List.all_eq_true.mp batch_122_15_ok accepted_6129 (by simp [batch_122_15_values])
  exact h
theorem leaf_6129_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6129.profileLo box_6129.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6129_ok
theorem branch_box_6129_nonnegative : ∀ j, 0 ≤ branch_box_6129.lower j ∧ 0 ≤ branch_box_6129.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6129, Box.profileLo, Box.profileHi, box_6129]
theorem leaf_6129_BranchSafe : CertificateConsequences.BranchSafe branch_box_6129 := by
  left; refine ⟨branch_box_6129_nonnegative, ?_⟩
  intro z hz; exact leaf_6129_sound hz

theorem leaf_6130_ok : checkAt 527 1000 box_6130 cert_6130 = true := by
  have h := List.all_eq_true.mp batch_122_16_ok accepted_6130 (by simp [batch_122_16_values])
  exact h
theorem leaf_6130_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6130.profileLo box_6130.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6130_ok
theorem branch_box_6130_nonnegative : ∀ j, 0 ≤ branch_box_6130.lower j ∧ 0 ≤ branch_box_6130.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6130, Box.profileLo, Box.profileHi, box_6130]
theorem leaf_6130_BranchSafe : CertificateConsequences.BranchSafe branch_box_6130 := by
  left; refine ⟨branch_box_6130_nonnegative, ?_⟩
  intro z hz; exact leaf_6130_sound hz

theorem leaf_6133_ok : checkAt 527 1000 box_6133 cert_6133 = true := by
  have h := List.all_eq_true.mp batch_122_17_ok accepted_6133 (by simp [batch_122_17_values])
  exact h
theorem leaf_6133_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6133.profileLo box_6133.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6133_ok
theorem branch_box_6133_nonnegative : ∀ j, 0 ≤ branch_box_6133.lower j ∧ 0 ≤ branch_box_6133.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6133, Box.profileLo, Box.profileHi, box_6133]
theorem leaf_6133_BranchSafe : CertificateConsequences.BranchSafe branch_box_6133 := by
  left; refine ⟨branch_box_6133_nonnegative, ?_⟩
  intro z hz; exact leaf_6133_sound hz

theorem leaf_6134_ok : checkAt 527 1000 box_6134 cert_6134 = true := by
  have h := List.all_eq_true.mp batch_122_18_ok accepted_6134 (by simp [batch_122_18_values])
  exact h
theorem leaf_6134_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6134.profileLo box_6134.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6134_ok
theorem branch_box_6134_nonnegative : ∀ j, 0 ≤ branch_box_6134.lower j ∧ 0 ≤ branch_box_6134.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6134, Box.profileLo, Box.profileHi, box_6134]
theorem leaf_6134_BranchSafe : CertificateConsequences.BranchSafe branch_box_6134 := by
  left; refine ⟨branch_box_6134_nonnegative, ?_⟩
  intro z hz; exact leaf_6134_sound hz

theorem leaf_6135_ok : checkAt 527 1000 box_6135 cert_6135 = true := by
  have h := List.all_eq_true.mp batch_122_19_ok accepted_6135 (by simp [batch_122_19_values])
  exact h
theorem leaf_6135_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6135.profileLo box_6135.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6135_ok
theorem branch_box_6135_nonnegative : ∀ j, 0 ≤ branch_box_6135.lower j ∧ 0 ≤ branch_box_6135.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6135, Box.profileLo, Box.profileHi, box_6135]
theorem leaf_6135_BranchSafe : CertificateConsequences.BranchSafe branch_box_6135 := by
  left; refine ⟨branch_box_6135_nonnegative, ?_⟩
  intro z hz; exact leaf_6135_sound hz

theorem leaf_6139_ok : checkAt 527 1000 box_6139 cert_6139 = true := by
  have h := List.all_eq_true.mp batch_122_20_ok accepted_6139 (by simp [batch_122_20_values])
  exact h
theorem leaf_6139_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6139.profileLo box_6139.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6139_ok
theorem branch_box_6139_nonnegative : ∀ j, 0 ≤ branch_box_6139.lower j ∧ 0 ≤ branch_box_6139.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6139, Box.profileLo, Box.profileHi, box_6139]
theorem leaf_6139_BranchSafe : CertificateConsequences.BranchSafe branch_box_6139 := by
  left; refine ⟨branch_box_6139_nonnegative, ?_⟩
  intro z hz; exact leaf_6139_sound hz

theorem leaf_6140_ok : checkAt 527 1000 box_6140 cert_6140 = true := by
  have h := List.all_eq_true.mp batch_122_21_ok accepted_6140 (by simp [batch_122_21_values])
  exact h
theorem leaf_6140_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6140.profileLo box_6140.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6140_ok
theorem branch_box_6140_nonnegative : ∀ j, 0 ≤ branch_box_6140.lower j ∧ 0 ≤ branch_box_6140.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6140, Box.profileLo, Box.profileHi, box_6140]
theorem leaf_6140_BranchSafe : CertificateConsequences.BranchSafe branch_box_6140 := by
  left; refine ⟨branch_box_6140_nonnegative, ?_⟩
  intro z hz; exact leaf_6140_sound hz

theorem leaf_6147_ok : checkAt 527 1000 box_6147 cert_6147 = true := by
  have h := List.all_eq_true.mp batch_122_22_ok accepted_6147 (by simp [batch_122_22_values])
  exact h
theorem leaf_6147_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6147.profileLo box_6147.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6147_ok
theorem branch_box_6147_nonnegative : ∀ j, 0 ≤ branch_box_6147.lower j ∧ 0 ≤ branch_box_6147.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6147, Box.profileLo, Box.profileHi, box_6147]
theorem leaf_6147_BranchSafe : CertificateConsequences.BranchSafe branch_box_6147 := by
  left; refine ⟨branch_box_6147_nonnegative, ?_⟩
  intro z hz; exact leaf_6147_sound hz

theorem leaf_6148_ok : checkAt 527 1000 box_6148 cert_6148 = true := by
  have h := List.all_eq_true.mp batch_122_23_ok accepted_6148 (by simp [batch_122_23_values])
  exact h
theorem leaf_6148_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6148.profileLo box_6148.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6148_ok
theorem branch_box_6148_nonnegative : ∀ j, 0 ≤ branch_box_6148.lower j ∧ 0 ≤ branch_box_6148.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6148, Box.profileLo, Box.profileHi, box_6148]
theorem leaf_6148_BranchSafe : CertificateConsequences.BranchSafe branch_box_6148 := by
  left; refine ⟨branch_box_6148_nonnegative, ?_⟩
  intro z hz; exact leaf_6148_sound hz

#print axioms batch_122_00_ok
#print axioms leaf_6101_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
