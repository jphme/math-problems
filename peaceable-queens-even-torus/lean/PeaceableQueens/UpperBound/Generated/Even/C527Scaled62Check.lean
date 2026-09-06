import PeaceableQueens.UpperBound.Generated.Even.C527Scaled62Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_62_00_values : List Bool := [accepted_3100]
theorem batch_62_00_ok : batch_62_00_values.all id = true := by decide

def batch_62_01_values : List Bool := [accepted_3113]
theorem batch_62_01_ok : batch_62_01_values.all id = true := by decide

def batch_62_02_values : List Bool := [accepted_3114]
theorem batch_62_02_ok : batch_62_02_values.all id = true := by decide

def batch_62_03_values : List Bool := [accepted_3115]
theorem batch_62_03_ok : batch_62_03_values.all id = true := by decide

def batch_62_04_values : List Bool := [accepted_3116]
theorem batch_62_04_ok : batch_62_04_values.all id = true := by decide

def batch_62_05_values : List Bool := [accepted_3120]
theorem batch_62_05_ok : batch_62_05_values.all id = true := by decide

def batch_62_06_values : List Bool := [accepted_3121]
theorem batch_62_06_ok : batch_62_06_values.all id = true := by decide

def batch_62_07_values : List Bool := [accepted_3122]
theorem batch_62_07_ok : batch_62_07_values.all id = true := by decide

def batch_62_08_values : List Bool := [accepted_3124]
theorem batch_62_08_ok : batch_62_08_values.all id = true := by decide

def batch_62_09_values : List Bool := [accepted_3125]
theorem batch_62_09_ok : batch_62_09_values.all id = true := by decide

def batch_62_10_values : List Bool := [accepted_3126]
theorem batch_62_10_ok : batch_62_10_values.all id = true := by decide

def batch_62_11_values : List Bool := [accepted_3129]
theorem batch_62_11_ok : batch_62_11_values.all id = true := by decide

def batch_62_12_values : List Bool := [accepted_3131]
theorem batch_62_12_ok : batch_62_12_values.all id = true := by decide

def batch_62_13_values : List Bool := [accepted_3132]
theorem batch_62_13_ok : batch_62_13_values.all id = true := by decide

def batch_62_14_values : List Bool := [accepted_3135]
theorem batch_62_14_ok : batch_62_14_values.all id = true := by decide

def batch_62_15_values : List Bool := [accepted_3136]
theorem batch_62_15_ok : batch_62_15_values.all id = true := by decide

def batch_62_16_values : List Bool := [accepted_3140]
theorem batch_62_16_ok : batch_62_16_values.all id = true := by decide

def batch_62_17_values : List Bool := [accepted_3141]
theorem batch_62_17_ok : batch_62_17_values.all id = true := by decide

def batch_62_18_values : List Bool := [accepted_3142]
theorem batch_62_18_ok : batch_62_18_values.all id = true := by decide

def batch_62_19_values : List Bool := [accepted_3143]
theorem batch_62_19_ok : batch_62_19_values.all id = true := by decide

def batch_62_20_values : List Bool := [accepted_3145]
theorem batch_62_20_ok : batch_62_20_values.all id = true := by decide

def batch_62_21_values : List Bool := [accepted_3146]
theorem batch_62_21_ok : batch_62_21_values.all id = true := by decide

theorem leaf_3100_ok : checkAt 527 1000 box_3100 cert_3100 = true := by
  have h := List.all_eq_true.mp batch_62_00_ok accepted_3100 (by simp [batch_62_00_values])
  exact h
theorem leaf_3100_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3100.profileLo box_3100.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3100_ok
theorem branch_box_3100_nonnegative : ∀ j, 0 ≤ branch_box_3100.lower j ∧ 0 ≤ branch_box_3100.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3100, Box.profileLo, Box.profileHi, box_3100]
theorem leaf_3100_BranchSafe : CertificateConsequences.BranchSafe branch_box_3100 := by
  left; refine ⟨branch_box_3100_nonnegative, ?_⟩
  intro z hz; exact leaf_3100_sound hz

theorem leaf_3113_ok : checkAt 527 1000 box_3113 cert_3113 = true := by
  have h := List.all_eq_true.mp batch_62_01_ok accepted_3113 (by simp [batch_62_01_values])
  exact h
theorem leaf_3113_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3113.profileLo box_3113.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3113_ok
theorem branch_box_3113_nonnegative : ∀ j, 0 ≤ branch_box_3113.lower j ∧ 0 ≤ branch_box_3113.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3113, Box.profileLo, Box.profileHi, box_3113]
theorem leaf_3113_BranchSafe : CertificateConsequences.BranchSafe branch_box_3113 := by
  left; refine ⟨branch_box_3113_nonnegative, ?_⟩
  intro z hz; exact leaf_3113_sound hz

theorem leaf_3114_ok : checkAt 527 1000 box_3114 cert_3114 = true := by
  have h := List.all_eq_true.mp batch_62_02_ok accepted_3114 (by simp [batch_62_02_values])
  exact h
theorem leaf_3114_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3114.profileLo box_3114.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3114_ok
theorem branch_box_3114_nonnegative : ∀ j, 0 ≤ branch_box_3114.lower j ∧ 0 ≤ branch_box_3114.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3114, Box.profileLo, Box.profileHi, box_3114]
theorem leaf_3114_BranchSafe : CertificateConsequences.BranchSafe branch_box_3114 := by
  left; refine ⟨branch_box_3114_nonnegative, ?_⟩
  intro z hz; exact leaf_3114_sound hz

theorem leaf_3115_ok : checkAt 527 1000 box_3115 cert_3115 = true := by
  have h := List.all_eq_true.mp batch_62_03_ok accepted_3115 (by simp [batch_62_03_values])
  exact h
theorem leaf_3115_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3115.profileLo box_3115.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3115_ok
theorem branch_box_3115_nonnegative : ∀ j, 0 ≤ branch_box_3115.lower j ∧ 0 ≤ branch_box_3115.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3115, Box.profileLo, Box.profileHi, box_3115]
theorem leaf_3115_BranchSafe : CertificateConsequences.BranchSafe branch_box_3115 := by
  left; refine ⟨branch_box_3115_nonnegative, ?_⟩
  intro z hz; exact leaf_3115_sound hz

theorem leaf_3116_ok : checkAt 527 1000 box_3116 cert_3116 = true := by
  have h := List.all_eq_true.mp batch_62_04_ok accepted_3116 (by simp [batch_62_04_values])
  exact h
theorem leaf_3116_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3116.profileLo box_3116.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3116_ok
theorem branch_box_3116_nonnegative : ∀ j, 0 ≤ branch_box_3116.lower j ∧ 0 ≤ branch_box_3116.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3116, Box.profileLo, Box.profileHi, box_3116]
theorem leaf_3116_BranchSafe : CertificateConsequences.BranchSafe branch_box_3116 := by
  left; refine ⟨branch_box_3116_nonnegative, ?_⟩
  intro z hz; exact leaf_3116_sound hz

theorem leaf_3120_ok : checkAt 527 1000 box_3120 cert_3120 = true := by
  have h := List.all_eq_true.mp batch_62_05_ok accepted_3120 (by simp [batch_62_05_values])
  exact h
theorem leaf_3120_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3120.profileLo box_3120.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3120_ok
theorem branch_box_3120_nonnegative : ∀ j, 0 ≤ branch_box_3120.lower j ∧ 0 ≤ branch_box_3120.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3120, Box.profileLo, Box.profileHi, box_3120]
theorem leaf_3120_BranchSafe : CertificateConsequences.BranchSafe branch_box_3120 := by
  left; refine ⟨branch_box_3120_nonnegative, ?_⟩
  intro z hz; exact leaf_3120_sound hz

theorem leaf_3121_ok : checkAt 527 1000 box_3121 cert_3121 = true := by
  have h := List.all_eq_true.mp batch_62_06_ok accepted_3121 (by simp [batch_62_06_values])
  exact h
theorem leaf_3121_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3121.profileLo box_3121.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3121_ok
theorem branch_box_3121_nonnegative : ∀ j, 0 ≤ branch_box_3121.lower j ∧ 0 ≤ branch_box_3121.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3121, Box.profileLo, Box.profileHi, box_3121]
theorem leaf_3121_BranchSafe : CertificateConsequences.BranchSafe branch_box_3121 := by
  left; refine ⟨branch_box_3121_nonnegative, ?_⟩
  intro z hz; exact leaf_3121_sound hz

theorem leaf_3122_ok : checkAt 527 1000 box_3122 cert_3122 = true := by
  have h := List.all_eq_true.mp batch_62_07_ok accepted_3122 (by simp [batch_62_07_values])
  exact h
theorem leaf_3122_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3122.profileLo box_3122.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3122_ok
theorem branch_box_3122_nonnegative : ∀ j, 0 ≤ branch_box_3122.lower j ∧ 0 ≤ branch_box_3122.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3122, Box.profileLo, Box.profileHi, box_3122]
theorem leaf_3122_BranchSafe : CertificateConsequences.BranchSafe branch_box_3122 := by
  left; refine ⟨branch_box_3122_nonnegative, ?_⟩
  intro z hz; exact leaf_3122_sound hz

theorem leaf_3124_ok : checkAt 527 1000 box_3124 cert_3124 = true := by
  have h := List.all_eq_true.mp batch_62_08_ok accepted_3124 (by simp [batch_62_08_values])
  exact h
theorem leaf_3124_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3124.profileLo box_3124.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3124_ok
theorem branch_box_3124_nonnegative : ∀ j, 0 ≤ branch_box_3124.lower j ∧ 0 ≤ branch_box_3124.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3124, Box.profileLo, Box.profileHi, box_3124]
theorem leaf_3124_BranchSafe : CertificateConsequences.BranchSafe branch_box_3124 := by
  left; refine ⟨branch_box_3124_nonnegative, ?_⟩
  intro z hz; exact leaf_3124_sound hz

theorem leaf_3125_ok : checkAt 527 1000 box_3125 cert_3125 = true := by
  have h := List.all_eq_true.mp batch_62_09_ok accepted_3125 (by simp [batch_62_09_values])
  exact h
theorem leaf_3125_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3125.profileLo box_3125.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3125_ok
theorem branch_box_3125_nonnegative : ∀ j, 0 ≤ branch_box_3125.lower j ∧ 0 ≤ branch_box_3125.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3125, Box.profileLo, Box.profileHi, box_3125]
theorem leaf_3125_BranchSafe : CertificateConsequences.BranchSafe branch_box_3125 := by
  left; refine ⟨branch_box_3125_nonnegative, ?_⟩
  intro z hz; exact leaf_3125_sound hz

theorem leaf_3126_ok : checkAt 527 1000 box_3126 cert_3126 = true := by
  have h := List.all_eq_true.mp batch_62_10_ok accepted_3126 (by simp [batch_62_10_values])
  exact h
theorem leaf_3126_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3126.profileLo box_3126.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3126_ok
theorem branch_box_3126_nonnegative : ∀ j, 0 ≤ branch_box_3126.lower j ∧ 0 ≤ branch_box_3126.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3126, Box.profileLo, Box.profileHi, box_3126]
theorem leaf_3126_BranchSafe : CertificateConsequences.BranchSafe branch_box_3126 := by
  left; refine ⟨branch_box_3126_nonnegative, ?_⟩
  intro z hz; exact leaf_3126_sound hz

theorem leaf_3129_ok : checkAt 527 1000 box_3129 cert_3129 = true := by
  have h := List.all_eq_true.mp batch_62_11_ok accepted_3129 (by simp [batch_62_11_values])
  exact h
theorem leaf_3129_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3129.profileLo box_3129.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3129_ok
theorem branch_box_3129_nonnegative : ∀ j, 0 ≤ branch_box_3129.lower j ∧ 0 ≤ branch_box_3129.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3129, Box.profileLo, Box.profileHi, box_3129]
theorem leaf_3129_BranchSafe : CertificateConsequences.BranchSafe branch_box_3129 := by
  left; refine ⟨branch_box_3129_nonnegative, ?_⟩
  intro z hz; exact leaf_3129_sound hz

theorem leaf_3131_ok : checkAt 527 1000 box_3131 cert_3131 = true := by
  have h := List.all_eq_true.mp batch_62_12_ok accepted_3131 (by simp [batch_62_12_values])
  exact h
theorem leaf_3131_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3131.profileLo box_3131.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3131_ok
theorem branch_box_3131_nonnegative : ∀ j, 0 ≤ branch_box_3131.lower j ∧ 0 ≤ branch_box_3131.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3131, Box.profileLo, Box.profileHi, box_3131]
theorem leaf_3131_BranchSafe : CertificateConsequences.BranchSafe branch_box_3131 := by
  left; refine ⟨branch_box_3131_nonnegative, ?_⟩
  intro z hz; exact leaf_3131_sound hz

theorem leaf_3132_ok : checkAt 527 1000 box_3132 cert_3132 = true := by
  have h := List.all_eq_true.mp batch_62_13_ok accepted_3132 (by simp [batch_62_13_values])
  exact h
theorem leaf_3132_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3132.profileLo box_3132.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3132_ok
theorem branch_box_3132_nonnegative : ∀ j, 0 ≤ branch_box_3132.lower j ∧ 0 ≤ branch_box_3132.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3132, Box.profileLo, Box.profileHi, box_3132]
theorem leaf_3132_BranchSafe : CertificateConsequences.BranchSafe branch_box_3132 := by
  left; refine ⟨branch_box_3132_nonnegative, ?_⟩
  intro z hz; exact leaf_3132_sound hz

theorem leaf_3135_ok : checkAt 527 1000 box_3135 cert_3135 = true := by
  have h := List.all_eq_true.mp batch_62_14_ok accepted_3135 (by simp [batch_62_14_values])
  exact h
theorem leaf_3135_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3135.profileLo box_3135.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3135_ok
theorem branch_box_3135_nonnegative : ∀ j, 0 ≤ branch_box_3135.lower j ∧ 0 ≤ branch_box_3135.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3135, Box.profileLo, Box.profileHi, box_3135]
theorem leaf_3135_BranchSafe : CertificateConsequences.BranchSafe branch_box_3135 := by
  left; refine ⟨branch_box_3135_nonnegative, ?_⟩
  intro z hz; exact leaf_3135_sound hz

theorem leaf_3136_ok : checkAt 527 1000 box_3136 cert_3136 = true := by
  have h := List.all_eq_true.mp batch_62_15_ok accepted_3136 (by simp [batch_62_15_values])
  exact h
theorem leaf_3136_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3136.profileLo box_3136.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3136_ok
theorem branch_box_3136_nonnegative : ∀ j, 0 ≤ branch_box_3136.lower j ∧ 0 ≤ branch_box_3136.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3136, Box.profileLo, Box.profileHi, box_3136]
theorem leaf_3136_BranchSafe : CertificateConsequences.BranchSafe branch_box_3136 := by
  left; refine ⟨branch_box_3136_nonnegative, ?_⟩
  intro z hz; exact leaf_3136_sound hz

theorem leaf_3140_ok : checkAt 527 1000 box_3140 cert_3140 = true := by
  have h := List.all_eq_true.mp batch_62_16_ok accepted_3140 (by simp [batch_62_16_values])
  exact h
theorem leaf_3140_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3140.profileLo box_3140.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3140_ok
theorem branch_box_3140_nonnegative : ∀ j, 0 ≤ branch_box_3140.lower j ∧ 0 ≤ branch_box_3140.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3140, Box.profileLo, Box.profileHi, box_3140]
theorem leaf_3140_BranchSafe : CertificateConsequences.BranchSafe branch_box_3140 := by
  left; refine ⟨branch_box_3140_nonnegative, ?_⟩
  intro z hz; exact leaf_3140_sound hz

theorem leaf_3141_ok : checkAt 527 1000 box_3141 cert_3141 = true := by
  have h := List.all_eq_true.mp batch_62_17_ok accepted_3141 (by simp [batch_62_17_values])
  exact h
theorem leaf_3141_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3141.profileLo box_3141.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3141_ok
theorem branch_box_3141_nonnegative : ∀ j, 0 ≤ branch_box_3141.lower j ∧ 0 ≤ branch_box_3141.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3141, Box.profileLo, Box.profileHi, box_3141]
theorem leaf_3141_BranchSafe : CertificateConsequences.BranchSafe branch_box_3141 := by
  left; refine ⟨branch_box_3141_nonnegative, ?_⟩
  intro z hz; exact leaf_3141_sound hz

theorem leaf_3142_ok : checkAt 527 1000 box_3142 cert_3142 = true := by
  have h := List.all_eq_true.mp batch_62_18_ok accepted_3142 (by simp [batch_62_18_values])
  exact h
theorem leaf_3142_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3142.profileLo box_3142.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3142_ok
theorem branch_box_3142_nonnegative : ∀ j, 0 ≤ branch_box_3142.lower j ∧ 0 ≤ branch_box_3142.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3142, Box.profileLo, Box.profileHi, box_3142]
theorem leaf_3142_BranchSafe : CertificateConsequences.BranchSafe branch_box_3142 := by
  left; refine ⟨branch_box_3142_nonnegative, ?_⟩
  intro z hz; exact leaf_3142_sound hz

theorem leaf_3143_ok : checkAt 527 1000 box_3143 cert_3143 = true := by
  have h := List.all_eq_true.mp batch_62_19_ok accepted_3143 (by simp [batch_62_19_values])
  exact h
theorem leaf_3143_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3143.profileLo box_3143.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3143_ok
theorem branch_box_3143_nonnegative : ∀ j, 0 ≤ branch_box_3143.lower j ∧ 0 ≤ branch_box_3143.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3143, Box.profileLo, Box.profileHi, box_3143]
theorem leaf_3143_BranchSafe : CertificateConsequences.BranchSafe branch_box_3143 := by
  left; refine ⟨branch_box_3143_nonnegative, ?_⟩
  intro z hz; exact leaf_3143_sound hz

theorem leaf_3145_ok : checkAt 527 1000 box_3145 cert_3145 = true := by
  have h := List.all_eq_true.mp batch_62_20_ok accepted_3145 (by simp [batch_62_20_values])
  exact h
theorem leaf_3145_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3145.profileLo box_3145.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3145_ok
theorem branch_box_3145_nonnegative : ∀ j, 0 ≤ branch_box_3145.lower j ∧ 0 ≤ branch_box_3145.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3145, Box.profileLo, Box.profileHi, box_3145]
theorem leaf_3145_BranchSafe : CertificateConsequences.BranchSafe branch_box_3145 := by
  left; refine ⟨branch_box_3145_nonnegative, ?_⟩
  intro z hz; exact leaf_3145_sound hz

theorem leaf_3146_ok : checkAt 527 1000 box_3146 cert_3146 = true := by
  have h := List.all_eq_true.mp batch_62_21_ok accepted_3146 (by simp [batch_62_21_values])
  exact h
theorem leaf_3146_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3146.profileLo box_3146.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3146_ok
theorem branch_box_3146_nonnegative : ∀ j, 0 ≤ branch_box_3146.lower j ∧ 0 ≤ branch_box_3146.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3146, Box.profileLo, Box.profileHi, box_3146]
theorem leaf_3146_BranchSafe : CertificateConsequences.BranchSafe branch_box_3146 := by
  left; refine ⟨branch_box_3146_nonnegative, ?_⟩
  intro z hz; exact leaf_3146_sound hz

#print axioms batch_62_00_ok
#print axioms leaf_3100_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
