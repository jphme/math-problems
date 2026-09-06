import PeaceableQueens.UpperBound.Generated.Even.C527Scaled82Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_82_00_values : List Bool := [accepted_4107]
theorem batch_82_00_ok : batch_82_00_values.all id = true := by decide

def batch_82_01_values : List Bool := [accepted_4109]
theorem batch_82_01_ok : batch_82_01_values.all id = true := by decide

def batch_82_02_values : List Bool := [accepted_4110]
theorem batch_82_02_ok : batch_82_02_values.all id = true := by decide

def batch_82_03_values : List Bool := [accepted_4111]
theorem batch_82_03_ok : batch_82_03_values.all id = true := by decide

def batch_82_04_values : List Bool := [accepted_4112]
theorem batch_82_04_ok : batch_82_04_values.all id = true := by decide

def batch_82_05_values : List Bool := [accepted_4113]
theorem batch_82_05_ok : batch_82_05_values.all id = true := by decide

def batch_82_06_values : List Bool := [accepted_4116]
theorem batch_82_06_ok : batch_82_06_values.all id = true := by decide

def batch_82_07_values : List Bool := [accepted_4117]
theorem batch_82_07_ok : batch_82_07_values.all id = true := by decide

def batch_82_08_values : List Bool := [accepted_4118]
theorem batch_82_08_ok : batch_82_08_values.all id = true := by decide

def batch_82_09_values : List Bool := [accepted_4119]
theorem batch_82_09_ok : batch_82_09_values.all id = true := by decide

def batch_82_10_values : List Bool := [accepted_4121]
theorem batch_82_10_ok : batch_82_10_values.all id = true := by decide

def batch_82_11_values : List Bool := [accepted_4122]
theorem batch_82_11_ok : batch_82_11_values.all id = true := by decide

def batch_82_12_values : List Bool := [accepted_4129]
theorem batch_82_12_ok : batch_82_12_values.all id = true := by decide

def batch_82_13_values : List Bool := [accepted_4132]
theorem batch_82_13_ok : batch_82_13_values.all id = true := by decide

def batch_82_14_values : List Bool := [accepted_4133]
theorem batch_82_14_ok : batch_82_14_values.all id = true := by decide

def batch_82_15_values : List Bool := [accepted_4134]
theorem batch_82_15_ok : batch_82_15_values.all id = true := by decide

def batch_82_16_values : List Bool := [accepted_4135]
theorem batch_82_16_ok : batch_82_16_values.all id = true := by decide

def batch_82_17_values : List Bool := [accepted_4138]
theorem batch_82_17_ok : batch_82_17_values.all id = true := by decide

def batch_82_18_values : List Bool := [accepted_4139]
theorem batch_82_18_ok : batch_82_18_values.all id = true := by decide

def batch_82_19_values : List Bool := [accepted_4142]
theorem batch_82_19_ok : batch_82_19_values.all id = true := by decide

def batch_82_20_values : List Bool := [accepted_4143]
theorem batch_82_20_ok : batch_82_20_values.all id = true := by decide

def batch_82_21_values : List Bool := [accepted_4144]
theorem batch_82_21_ok : batch_82_21_values.all id = true := by decide

def batch_82_22_values : List Bool := [accepted_4147]
theorem batch_82_22_ok : batch_82_22_values.all id = true := by decide

def batch_82_23_values : List Bool := [accepted_4148]
theorem batch_82_23_ok : batch_82_23_values.all id = true := by decide

theorem leaf_4107_ok : checkAt 527 1000 box_4107 cert_4107 = true := by
  have h := List.all_eq_true.mp batch_82_00_ok accepted_4107 (by simp [batch_82_00_values])
  exact h
theorem leaf_4107_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4107.profileLo box_4107.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4107_ok
theorem branch_box_4107_nonnegative : ∀ j, 0 ≤ branch_box_4107.lower j ∧ 0 ≤ branch_box_4107.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4107, Box.profileLo, Box.profileHi, box_4107]
theorem leaf_4107_BranchSafe : CertificateConsequences.BranchSafe branch_box_4107 := by
  left; refine ⟨branch_box_4107_nonnegative, ?_⟩
  intro z hz; exact leaf_4107_sound hz

theorem leaf_4109_ok : checkAt 527 1000 box_4109 cert_4109 = true := by
  have h := List.all_eq_true.mp batch_82_01_ok accepted_4109 (by simp [batch_82_01_values])
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

theorem leaf_4110_ok : checkAt 527 1000 box_4110 cert_4110 = true := by
  have h := List.all_eq_true.mp batch_82_02_ok accepted_4110 (by simp [batch_82_02_values])
  exact h
theorem leaf_4110_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4110.profileLo box_4110.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4110_ok
theorem branch_box_4110_nonnegative : ∀ j, 0 ≤ branch_box_4110.lower j ∧ 0 ≤ branch_box_4110.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4110, Box.profileLo, Box.profileHi, box_4110]
theorem leaf_4110_BranchSafe : CertificateConsequences.BranchSafe branch_box_4110 := by
  left; refine ⟨branch_box_4110_nonnegative, ?_⟩
  intro z hz; exact leaf_4110_sound hz

theorem leaf_4111_ok : checkAt 527 1000 box_4111 cert_4111 = true := by
  have h := List.all_eq_true.mp batch_82_03_ok accepted_4111 (by simp [batch_82_03_values])
  exact h
theorem leaf_4111_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4111.profileLo box_4111.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4111_ok
theorem branch_box_4111_nonnegative : ∀ j, 0 ≤ branch_box_4111.lower j ∧ 0 ≤ branch_box_4111.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4111, Box.profileLo, Box.profileHi, box_4111]
theorem leaf_4111_BranchSafe : CertificateConsequences.BranchSafe branch_box_4111 := by
  left; refine ⟨branch_box_4111_nonnegative, ?_⟩
  intro z hz; exact leaf_4111_sound hz

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

theorem leaf_4113_ok : checkAt 527 1000 box_4113 cert_4113 = true := by
  have h := List.all_eq_true.mp batch_82_05_ok accepted_4113 (by simp [batch_82_05_values])
  exact h
theorem leaf_4113_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4113.profileLo box_4113.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4113_ok
theorem branch_box_4113_nonnegative : ∀ j, 0 ≤ branch_box_4113.lower j ∧ 0 ≤ branch_box_4113.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4113, Box.profileLo, Box.profileHi, box_4113]
theorem leaf_4113_BranchSafe : CertificateConsequences.BranchSafe branch_box_4113 := by
  left; refine ⟨branch_box_4113_nonnegative, ?_⟩
  intro z hz; exact leaf_4113_sound hz

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

theorem leaf_4117_ok : checkAt 527 1000 box_4117 cert_4117 = true := by
  have h := List.all_eq_true.mp batch_82_07_ok accepted_4117 (by simp [batch_82_07_values])
  exact h
theorem leaf_4117_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4117.profileLo box_4117.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4117_ok
theorem branch_box_4117_nonnegative : ∀ j, 0 ≤ branch_box_4117.lower j ∧ 0 ≤ branch_box_4117.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4117, Box.profileLo, Box.profileHi, box_4117]
theorem leaf_4117_BranchSafe : CertificateConsequences.BranchSafe branch_box_4117 := by
  left; refine ⟨branch_box_4117_nonnegative, ?_⟩
  intro z hz; exact leaf_4117_sound hz

theorem leaf_4118_ok : checkAt 527 1000 box_4118 cert_4118 = true := by
  have h := List.all_eq_true.mp batch_82_08_ok accepted_4118 (by simp [batch_82_08_values])
  exact h
theorem leaf_4118_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4118.profileLo box_4118.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4118_ok
theorem branch_box_4118_nonnegative : ∀ j, 0 ≤ branch_box_4118.lower j ∧ 0 ≤ branch_box_4118.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4118, Box.profileLo, Box.profileHi, box_4118]
theorem leaf_4118_BranchSafe : CertificateConsequences.BranchSafe branch_box_4118 := by
  left; refine ⟨branch_box_4118_nonnegative, ?_⟩
  intro z hz; exact leaf_4118_sound hz

theorem leaf_4119_ok : checkAt 527 1000 box_4119 cert_4119 = true := by
  have h := List.all_eq_true.mp batch_82_09_ok accepted_4119 (by simp [batch_82_09_values])
  exact h
theorem leaf_4119_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4119.profileLo box_4119.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4119_ok
theorem branch_box_4119_nonnegative : ∀ j, 0 ≤ branch_box_4119.lower j ∧ 0 ≤ branch_box_4119.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4119, Box.profileLo, Box.profileHi, box_4119]
theorem leaf_4119_BranchSafe : CertificateConsequences.BranchSafe branch_box_4119 := by
  left; refine ⟨branch_box_4119_nonnegative, ?_⟩
  intro z hz; exact leaf_4119_sound hz

theorem leaf_4121_ok : checkAt 527 1000 box_4121 cert_4121 = true := by
  have h := List.all_eq_true.mp batch_82_10_ok accepted_4121 (by simp [batch_82_10_values])
  exact h
theorem leaf_4121_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4121.profileLo box_4121.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4121_ok
theorem branch_box_4121_nonnegative : ∀ j, 0 ≤ branch_box_4121.lower j ∧ 0 ≤ branch_box_4121.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4121, Box.profileLo, Box.profileHi, box_4121]
theorem leaf_4121_BranchSafe : CertificateConsequences.BranchSafe branch_box_4121 := by
  left; refine ⟨branch_box_4121_nonnegative, ?_⟩
  intro z hz; exact leaf_4121_sound hz

theorem leaf_4122_ok : checkAt 527 1000 box_4122 cert_4122 = true := by
  have h := List.all_eq_true.mp batch_82_11_ok accepted_4122 (by simp [batch_82_11_values])
  exact h
theorem leaf_4122_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4122.profileLo box_4122.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4122_ok
theorem branch_box_4122_nonnegative : ∀ j, 0 ≤ branch_box_4122.lower j ∧ 0 ≤ branch_box_4122.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4122, Box.profileLo, Box.profileHi, box_4122]
theorem leaf_4122_BranchSafe : CertificateConsequences.BranchSafe branch_box_4122 := by
  left; refine ⟨branch_box_4122_nonnegative, ?_⟩
  intro z hz; exact leaf_4122_sound hz

theorem leaf_4129_ok : checkAt 527 1000 box_4129 cert_4129 = true := by
  have h := List.all_eq_true.mp batch_82_12_ok accepted_4129 (by simp [batch_82_12_values])
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

theorem leaf_4132_ok : checkAt 527 1000 box_4132 cert_4132 = true := by
  have h := List.all_eq_true.mp batch_82_13_ok accepted_4132 (by simp [batch_82_13_values])
  exact h
theorem leaf_4132_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4132.profileLo box_4132.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4132_ok
theorem branch_box_4132_nonnegative : ∀ j, 0 ≤ branch_box_4132.lower j ∧ 0 ≤ branch_box_4132.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4132, Box.profileLo, Box.profileHi, box_4132]
theorem leaf_4132_BranchSafe : CertificateConsequences.BranchSafe branch_box_4132 := by
  left; refine ⟨branch_box_4132_nonnegative, ?_⟩
  intro z hz; exact leaf_4132_sound hz

theorem leaf_4133_ok : checkAt 527 1000 box_4133 cert_4133 = true := by
  have h := List.all_eq_true.mp batch_82_14_ok accepted_4133 (by simp [batch_82_14_values])
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

theorem leaf_4134_ok : checkAt 527 1000 box_4134 cert_4134 = true := by
  have h := List.all_eq_true.mp batch_82_15_ok accepted_4134 (by simp [batch_82_15_values])
  exact h
theorem leaf_4134_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4134.profileLo box_4134.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4134_ok
theorem branch_box_4134_nonnegative : ∀ j, 0 ≤ branch_box_4134.lower j ∧ 0 ≤ branch_box_4134.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4134, Box.profileLo, Box.profileHi, box_4134]
theorem leaf_4134_BranchSafe : CertificateConsequences.BranchSafe branch_box_4134 := by
  left; refine ⟨branch_box_4134_nonnegative, ?_⟩
  intro z hz; exact leaf_4134_sound hz

theorem leaf_4135_ok : checkAt 527 1000 box_4135 cert_4135 = true := by
  have h := List.all_eq_true.mp batch_82_16_ok accepted_4135 (by simp [batch_82_16_values])
  exact h
theorem leaf_4135_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4135.profileLo box_4135.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4135_ok
theorem branch_box_4135_nonnegative : ∀ j, 0 ≤ branch_box_4135.lower j ∧ 0 ≤ branch_box_4135.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4135, Box.profileLo, Box.profileHi, box_4135]
theorem leaf_4135_BranchSafe : CertificateConsequences.BranchSafe branch_box_4135 := by
  left; refine ⟨branch_box_4135_nonnegative, ?_⟩
  intro z hz; exact leaf_4135_sound hz

theorem leaf_4138_ok : checkAt 527 1000 box_4138 cert_4138 = true := by
  have h := List.all_eq_true.mp batch_82_17_ok accepted_4138 (by simp [batch_82_17_values])
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
  have h := List.all_eq_true.mp batch_82_18_ok accepted_4139 (by simp [batch_82_18_values])
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

theorem leaf_4142_ok : checkAt 527 1000 box_4142 cert_4142 = true := by
  have h := List.all_eq_true.mp batch_82_19_ok accepted_4142 (by simp [batch_82_19_values])
  exact h
theorem leaf_4142_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4142.profileLo box_4142.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4142_ok
theorem branch_box_4142_nonnegative : ∀ j, 0 ≤ branch_box_4142.lower j ∧ 0 ≤ branch_box_4142.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4142, Box.profileLo, Box.profileHi, box_4142]
theorem leaf_4142_BranchSafe : CertificateConsequences.BranchSafe branch_box_4142 := by
  left; refine ⟨branch_box_4142_nonnegative, ?_⟩
  intro z hz; exact leaf_4142_sound hz

theorem leaf_4143_ok : checkAt 527 1000 box_4143 cert_4143 = true := by
  have h := List.all_eq_true.mp batch_82_20_ok accepted_4143 (by simp [batch_82_20_values])
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

theorem leaf_4144_ok : checkAt 527 1000 box_4144 cert_4144 = true := by
  have h := List.all_eq_true.mp batch_82_21_ok accepted_4144 (by simp [batch_82_21_values])
  exact h
theorem leaf_4144_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4144.profileLo box_4144.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4144_ok
theorem branch_box_4144_nonnegative : ∀ j, 0 ≤ branch_box_4144.lower j ∧ 0 ≤ branch_box_4144.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4144, Box.profileLo, Box.profileHi, box_4144]
theorem leaf_4144_BranchSafe : CertificateConsequences.BranchSafe branch_box_4144 := by
  left; refine ⟨branch_box_4144_nonnegative, ?_⟩
  intro z hz; exact leaf_4144_sound hz

theorem leaf_4147_ok : checkAt 527 1000 box_4147 cert_4147 = true := by
  have h := List.all_eq_true.mp batch_82_22_ok accepted_4147 (by simp [batch_82_22_values])
  exact h
theorem leaf_4147_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4147.profileLo box_4147.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4147_ok
theorem branch_box_4147_nonnegative : ∀ j, 0 ≤ branch_box_4147.lower j ∧ 0 ≤ branch_box_4147.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4147, Box.profileLo, Box.profileHi, box_4147]
theorem leaf_4147_BranchSafe : CertificateConsequences.BranchSafe branch_box_4147 := by
  left; refine ⟨branch_box_4147_nonnegative, ?_⟩
  intro z hz; exact leaf_4147_sound hz

theorem leaf_4148_ok : checkAt 527 1000 box_4148 cert_4148 = true := by
  have h := List.all_eq_true.mp batch_82_23_ok accepted_4148 (by simp [batch_82_23_values])
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

#print axioms batch_82_00_ok
#print axioms leaf_4107_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
