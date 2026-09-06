import PeaceableQueens.UpperBound.Generated.Even.CoreScaled82Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_82_00_values : List Bool := [accepted_4102]
theorem batch_82_00_ok : batch_82_00_values.all id = true := by decide

def batch_82_01_values : List Bool := [accepted_4104]
theorem batch_82_01_ok : batch_82_01_values.all id = true := by decide

def batch_82_02_values : List Bool := [accepted_4108]
theorem batch_82_02_ok : batch_82_02_values.all id = true := by decide

def batch_82_03_values : List Bool := [accepted_4109]
theorem batch_82_03_ok : batch_82_03_values.all id = true := by decide

def batch_82_04_values : List Bool := [accepted_4112]
theorem batch_82_04_ok : batch_82_04_values.all id = true := by decide

def batch_82_05_values : List Bool := [accepted_4114]
theorem batch_82_05_ok : batch_82_05_values.all id = true := by decide

def batch_82_06_values : List Bool := [accepted_4116]
theorem batch_82_06_ok : batch_82_06_values.all id = true := by decide

def batch_82_07_values : List Bool := [accepted_4120]
theorem batch_82_07_ok : batch_82_07_values.all id = true := by decide

def batch_82_08_values : List Bool := [accepted_4124]
theorem batch_82_08_ok : batch_82_08_values.all id = true := by decide

def batch_82_09_values : List Bool := [accepted_4126]
theorem batch_82_09_ok : batch_82_09_values.all id = true := by decide

def batch_82_10_values : List Bool := [accepted_4127]
theorem batch_82_10_ok : batch_82_10_values.all id = true := by decide

def batch_82_11_values : List Bool := [accepted_4129]
theorem batch_82_11_ok : batch_82_11_values.all id = true := by decide

def batch_82_12_values : List Bool := [accepted_4133]
theorem batch_82_12_ok : batch_82_12_values.all id = true := by decide

def batch_82_13_values : List Bool := [accepted_4138]
theorem batch_82_13_ok : batch_82_13_values.all id = true := by decide

def batch_82_14_values : List Bool := [accepted_4139]
theorem batch_82_14_ok : batch_82_14_values.all id = true := by decide

def batch_82_15_values : List Bool := [accepted_4141]
theorem batch_82_15_ok : batch_82_15_values.all id = true := by decide

def batch_82_16_values : List Bool := [accepted_4143]
theorem batch_82_16_ok : batch_82_16_values.all id = true := by decide

def batch_82_17_values : List Bool := [accepted_4148]
theorem batch_82_17_ok : batch_82_17_values.all id = true := by decide

def batch_82_18_values : List Bool := [accepted_4149]
theorem batch_82_18_ok : batch_82_18_values.all id = true := by decide

theorem leaf_4102_ok : checkAt 527 1000 box_4102 cert_4102 = true := by
  have h := List.all_eq_true.mp batch_82_00_ok accepted_4102 (by simp [batch_82_00_values])
  exact h
theorem leaf_4102_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4102.profileLo box_4102.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4102_ok
theorem branch_box_4102_nonnegative : ∀ j, 0 ≤ branch_box_4102.lower j ∧ 0 ≤ branch_box_4102.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4102, Box.profileLo, Box.profileHi, box_4102]
theorem leaf_4102_BranchSafe : CertificateConsequences.BranchSafe branch_box_4102 := by
  left; refine ⟨branch_box_4102_nonnegative, ?_⟩
  intro z hz; exact leaf_4102_sound hz

theorem leaf_4104_ok : checkAt 527 1000 box_4104 cert_4104 = true := by
  have h := List.all_eq_true.mp batch_82_01_ok accepted_4104 (by simp [batch_82_01_values])
  exact h
theorem leaf_4104_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4104.profileLo box_4104.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4104_ok
theorem branch_box_4104_nonnegative : ∀ j, 0 ≤ branch_box_4104.lower j ∧ 0 ≤ branch_box_4104.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4104, Box.profileLo, Box.profileHi, box_4104]
theorem leaf_4104_BranchSafe : CertificateConsequences.BranchSafe branch_box_4104 := by
  left; refine ⟨branch_box_4104_nonnegative, ?_⟩
  intro z hz; exact leaf_4104_sound hz

theorem leaf_4108_ok : checkAt 527 1000 box_4108 cert_4108 = true := by
  have h := List.all_eq_true.mp batch_82_02_ok accepted_4108 (by simp [batch_82_02_values])
  exact h
theorem leaf_4108_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4108.profileLo box_4108.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4108_ok
theorem branch_box_4108_nonnegative : ∀ j, 0 ≤ branch_box_4108.lower j ∧ 0 ≤ branch_box_4108.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4108, Box.profileLo, Box.profileHi, box_4108]
theorem leaf_4108_BranchSafe : CertificateConsequences.BranchSafe branch_box_4108 := by
  left; refine ⟨branch_box_4108_nonnegative, ?_⟩
  intro z hz; exact leaf_4108_sound hz

theorem leaf_4109_ok : checkAt 527 1000 box_4109 cert_4109 = true := by
  have h := List.all_eq_true.mp batch_82_03_ok accepted_4109 (by simp [batch_82_03_values])
  exact h
theorem leaf_4109_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4109.profileLo box_4109.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4109_ok
theorem branch_box_4109_nonnegative : ∀ j, 0 ≤ branch_box_4109.lower j ∧ 0 ≤ branch_box_4109.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4109, Box.profileLo, Box.profileHi, box_4109]
theorem leaf_4109_BranchSafe : CertificateConsequences.BranchSafe branch_box_4109 := by
  left; refine ⟨branch_box_4109_nonnegative, ?_⟩
  intro z hz; exact leaf_4109_sound hz

theorem leaf_4112_ok : checkAt 527 1000 box_4112 cert_4112 = true := by
  have h := List.all_eq_true.mp batch_82_04_ok accepted_4112 (by simp [batch_82_04_values])
  exact h
theorem leaf_4112_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4112.profileLo box_4112.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4112_ok
theorem branch_box_4112_nonnegative : ∀ j, 0 ≤ branch_box_4112.lower j ∧ 0 ≤ branch_box_4112.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4112, Box.profileLo, Box.profileHi, box_4112]
theorem leaf_4112_BranchSafe : CertificateConsequences.BranchSafe branch_box_4112 := by
  left; refine ⟨branch_box_4112_nonnegative, ?_⟩
  intro z hz; exact leaf_4112_sound hz

theorem leaf_4114_ok : checkAt 527 1000 box_4114 cert_4114 = true := by
  have h := List.all_eq_true.mp batch_82_05_ok accepted_4114 (by simp [batch_82_05_values])
  exact h
theorem leaf_4114_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4114.profileLo box_4114.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4114_ok
theorem branch_box_4114_nonnegative : ∀ j, 0 ≤ branch_box_4114.lower j ∧ 0 ≤ branch_box_4114.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4114, Box.profileLo, Box.profileHi, box_4114]
theorem leaf_4114_BranchSafe : CertificateConsequences.BranchSafe branch_box_4114 := by
  left; refine ⟨branch_box_4114_nonnegative, ?_⟩
  intro z hz; exact leaf_4114_sound hz

theorem leaf_4116_ok : checkAt 527 1000 box_4116 cert_4116 = true := by
  have h := List.all_eq_true.mp batch_82_06_ok accepted_4116 (by simp [batch_82_06_values])
  exact h
theorem leaf_4116_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4116.profileLo box_4116.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4116_ok
theorem branch_box_4116_nonnegative : ∀ j, 0 ≤ branch_box_4116.lower j ∧ 0 ≤ branch_box_4116.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4116, Box.profileLo, Box.profileHi, box_4116]
theorem leaf_4116_BranchSafe : CertificateConsequences.BranchSafe branch_box_4116 := by
  left; refine ⟨branch_box_4116_nonnegative, ?_⟩
  intro z hz; exact leaf_4116_sound hz

theorem leaf_4120_ok : checkAt 527 1000 box_4120 cert_4120 = true := by
  have h := List.all_eq_true.mp batch_82_07_ok accepted_4120 (by simp [batch_82_07_values])
  exact h
theorem leaf_4120_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4120.profileLo box_4120.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4120_ok
theorem branch_box_4120_nonnegative : ∀ j, 0 ≤ branch_box_4120.lower j ∧ 0 ≤ branch_box_4120.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4120, Box.profileLo, Box.profileHi, box_4120]
theorem leaf_4120_BranchSafe : CertificateConsequences.BranchSafe branch_box_4120 := by
  left; refine ⟨branch_box_4120_nonnegative, ?_⟩
  intro z hz; exact leaf_4120_sound hz

theorem leaf_4124_ok : checkAt 527 1000 box_4124 cert_4124 = true := by
  have h := List.all_eq_true.mp batch_82_08_ok accepted_4124 (by simp [batch_82_08_values])
  exact h
theorem leaf_4124_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4124.profileLo box_4124.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4124_ok
theorem branch_box_4124_nonnegative : ∀ j, 0 ≤ branch_box_4124.lower j ∧ 0 ≤ branch_box_4124.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4124, Box.profileLo, Box.profileHi, box_4124]
theorem leaf_4124_BranchSafe : CertificateConsequences.BranchSafe branch_box_4124 := by
  left; refine ⟨branch_box_4124_nonnegative, ?_⟩
  intro z hz; exact leaf_4124_sound hz

theorem leaf_4126_ok : checkAt 527 1000 box_4126 cert_4126 = true := by
  have h := List.all_eq_true.mp batch_82_09_ok accepted_4126 (by simp [batch_82_09_values])
  exact h
theorem leaf_4126_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4126.profileLo box_4126.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4126_ok
theorem branch_box_4126_nonnegative : ∀ j, 0 ≤ branch_box_4126.lower j ∧ 0 ≤ branch_box_4126.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4126, Box.profileLo, Box.profileHi, box_4126]
theorem leaf_4126_BranchSafe : CertificateConsequences.BranchSafe branch_box_4126 := by
  left; refine ⟨branch_box_4126_nonnegative, ?_⟩
  intro z hz; exact leaf_4126_sound hz

theorem leaf_4127_ok : checkAt 527 1000 box_4127 cert_4127 = true := by
  have h := List.all_eq_true.mp batch_82_10_ok accepted_4127 (by simp [batch_82_10_values])
  exact h
theorem leaf_4127_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4127.profileLo box_4127.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4127_ok
theorem branch_box_4127_nonnegative : ∀ j, 0 ≤ branch_box_4127.lower j ∧ 0 ≤ branch_box_4127.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4127, Box.profileLo, Box.profileHi, box_4127]
theorem leaf_4127_BranchSafe : CertificateConsequences.BranchSafe branch_box_4127 := by
  left; refine ⟨branch_box_4127_nonnegative, ?_⟩
  intro z hz; exact leaf_4127_sound hz

theorem leaf_4129_ok : checkAt 527 1000 box_4129 cert_4129 = true := by
  have h := List.all_eq_true.mp batch_82_11_ok accepted_4129 (by simp [batch_82_11_values])
  exact h
theorem leaf_4129_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4129.profileLo box_4129.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4129_ok
theorem branch_box_4129_nonnegative : ∀ j, 0 ≤ branch_box_4129.lower j ∧ 0 ≤ branch_box_4129.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4129, Box.profileLo, Box.profileHi, box_4129]
theorem leaf_4129_BranchSafe : CertificateConsequences.BranchSafe branch_box_4129 := by
  left; refine ⟨branch_box_4129_nonnegative, ?_⟩
  intro z hz; exact leaf_4129_sound hz

theorem leaf_4133_ok : checkAt 527 1000 box_4133 cert_4133 = true := by
  have h := List.all_eq_true.mp batch_82_12_ok accepted_4133 (by simp [batch_82_12_values])
  exact h
theorem leaf_4133_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4133.profileLo box_4133.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4133_ok
theorem branch_box_4133_nonnegative : ∀ j, 0 ≤ branch_box_4133.lower j ∧ 0 ≤ branch_box_4133.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4133, Box.profileLo, Box.profileHi, box_4133]
theorem leaf_4133_BranchSafe : CertificateConsequences.BranchSafe branch_box_4133 := by
  left; refine ⟨branch_box_4133_nonnegative, ?_⟩
  intro z hz; exact leaf_4133_sound hz

theorem leaf_4138_ok : checkAt 527 1000 box_4138 cert_4138 = true := by
  have h := List.all_eq_true.mp batch_82_13_ok accepted_4138 (by simp [batch_82_13_values])
  exact h
theorem leaf_4138_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4138.profileLo box_4138.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4138_ok
theorem branch_box_4138_nonnegative : ∀ j, 0 ≤ branch_box_4138.lower j ∧ 0 ≤ branch_box_4138.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4138, Box.profileLo, Box.profileHi, box_4138]
theorem leaf_4138_BranchSafe : CertificateConsequences.BranchSafe branch_box_4138 := by
  left; refine ⟨branch_box_4138_nonnegative, ?_⟩
  intro z hz; exact leaf_4138_sound hz

theorem leaf_4139_ok : checkAt 527 1000 box_4139 cert_4139 = true := by
  have h := List.all_eq_true.mp batch_82_14_ok accepted_4139 (by simp [batch_82_14_values])
  exact h
theorem leaf_4139_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4139.profileLo box_4139.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4139_ok
theorem branch_box_4139_nonnegative : ∀ j, 0 ≤ branch_box_4139.lower j ∧ 0 ≤ branch_box_4139.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4139, Box.profileLo, Box.profileHi, box_4139]
theorem leaf_4139_BranchSafe : CertificateConsequences.BranchSafe branch_box_4139 := by
  left; refine ⟨branch_box_4139_nonnegative, ?_⟩
  intro z hz; exact leaf_4139_sound hz

theorem leaf_4141_ok : checkAt 527 1000 box_4141 cert_4141 = true := by
  have h := List.all_eq_true.mp batch_82_15_ok accepted_4141 (by simp [batch_82_15_values])
  exact h
theorem leaf_4141_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4141.profileLo box_4141.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4141_ok
theorem branch_box_4141_nonnegative : ∀ j, 0 ≤ branch_box_4141.lower j ∧ 0 ≤ branch_box_4141.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4141, Box.profileLo, Box.profileHi, box_4141]
theorem leaf_4141_BranchSafe : CertificateConsequences.BranchSafe branch_box_4141 := by
  left; refine ⟨branch_box_4141_nonnegative, ?_⟩
  intro z hz; exact leaf_4141_sound hz

theorem leaf_4143_ok : checkAt 527 1000 box_4143 cert_4143 = true := by
  have h := List.all_eq_true.mp batch_82_16_ok accepted_4143 (by simp [batch_82_16_values])
  exact h
theorem leaf_4143_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4143.profileLo box_4143.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4143_ok
theorem branch_box_4143_nonnegative : ∀ j, 0 ≤ branch_box_4143.lower j ∧ 0 ≤ branch_box_4143.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4143, Box.profileLo, Box.profileHi, box_4143]
theorem leaf_4143_BranchSafe : CertificateConsequences.BranchSafe branch_box_4143 := by
  left; refine ⟨branch_box_4143_nonnegative, ?_⟩
  intro z hz; exact leaf_4143_sound hz

theorem leaf_4148_ok : checkAt 527 1000 box_4148 cert_4148 = true := by
  have h := List.all_eq_true.mp batch_82_17_ok accepted_4148 (by simp [batch_82_17_values])
  exact h
theorem leaf_4148_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4148.profileLo box_4148.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4148_ok
theorem branch_box_4148_nonnegative : ∀ j, 0 ≤ branch_box_4148.lower j ∧ 0 ≤ branch_box_4148.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4148, Box.profileLo, Box.profileHi, box_4148]
theorem leaf_4148_BranchSafe : CertificateConsequences.BranchSafe branch_box_4148 := by
  left; refine ⟨branch_box_4148_nonnegative, ?_⟩
  intro z hz; exact leaf_4148_sound hz

theorem leaf_4149_ok : checkAt 527 1000 box_4149 cert_4149 = true := by
  have h := List.all_eq_true.mp batch_82_18_ok accepted_4149 (by simp [batch_82_18_values])
  exact h
theorem leaf_4149_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4149.profileLo box_4149.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4149_ok
theorem branch_box_4149_nonnegative : ∀ j, 0 ≤ branch_box_4149.lower j ∧ 0 ≤ branch_box_4149.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4149, Box.profileLo, Box.profileHi, box_4149]
theorem leaf_4149_BranchSafe : CertificateConsequences.BranchSafe branch_box_4149 := by
  left; refine ⟨branch_box_4149_nonnegative, ?_⟩
  intro z hz; exact leaf_4149_sound hz

#print axioms batch_82_00_ok
#print axioms leaf_4102_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
