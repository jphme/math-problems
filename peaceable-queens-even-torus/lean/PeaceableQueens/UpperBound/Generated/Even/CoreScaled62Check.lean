import PeaceableQueens.UpperBound.Generated.Even.CoreScaled62Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_62_00_values : List Bool := [accepted_3100]
theorem batch_62_00_ok : batch_62_00_values.all id = true := by decide

def batch_62_01_values : List Bool := [accepted_3102]
theorem batch_62_01_ok : batch_62_01_values.all id = true := by decide

def batch_62_02_values : List Bool := [accepted_3103]
theorem batch_62_02_ok : batch_62_02_values.all id = true := by decide

def batch_62_03_values : List Bool := [accepted_3106]
theorem batch_62_03_ok : batch_62_03_values.all id = true := by decide

def batch_62_04_values : List Bool := [accepted_3108]
theorem batch_62_04_ok : batch_62_04_values.all id = true := by decide

def batch_62_05_values : List Bool := [accepted_3110]
theorem batch_62_05_ok : batch_62_05_values.all id = true := by decide

def batch_62_06_values : List Bool := [accepted_3112]
theorem batch_62_06_ok : batch_62_06_values.all id = true := by decide

def batch_62_07_values : List Bool := [accepted_3114]
theorem batch_62_07_ok : batch_62_07_values.all id = true := by decide

def batch_62_08_values : List Bool := [accepted_3117]
theorem batch_62_08_ok : batch_62_08_values.all id = true := by decide

def batch_62_09_values : List Bool := [accepted_3120]
theorem batch_62_09_ok : batch_62_09_values.all id = true := by decide

def batch_62_10_values : List Bool := [accepted_3122]
theorem batch_62_10_ok : batch_62_10_values.all id = true := by decide

def batch_62_11_values : List Bool := [accepted_3124]
theorem batch_62_11_ok : batch_62_11_values.all id = true := by decide

def batch_62_12_values : List Bool := [accepted_3126]
theorem batch_62_12_ok : batch_62_12_values.all id = true := by decide

def batch_62_13_values : List Bool := [accepted_3128]
theorem batch_62_13_ok : batch_62_13_values.all id = true := by decide

def batch_62_14_values : List Bool := [accepted_3130]
theorem batch_62_14_ok : batch_62_14_values.all id = true := by decide

def batch_62_15_values : List Bool := [accepted_3138]
theorem batch_62_15_ok : batch_62_15_values.all id = true := by decide

def batch_62_16_values : List Bool := [accepted_3140]
theorem batch_62_16_ok : batch_62_16_values.all id = true := by decide

def batch_62_17_values : List Bool := [accepted_3142]
theorem batch_62_17_ok : batch_62_17_values.all id = true := by decide

def batch_62_18_values : List Bool := [accepted_3143]
theorem batch_62_18_ok : batch_62_18_values.all id = true := by decide

def batch_62_19_values : List Bool := [accepted_3145]
theorem batch_62_19_ok : batch_62_19_values.all id = true := by decide

def batch_62_20_values : List Bool := [accepted_3149]
theorem batch_62_20_ok : batch_62_20_values.all id = true := by decide

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

theorem leaf_3102_ok : checkAt 527 1000 box_3102 cert_3102 = true := by
  have h := List.all_eq_true.mp batch_62_01_ok accepted_3102 (by simp [batch_62_01_values])
  exact h
theorem leaf_3102_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3102.profileLo box_3102.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3102_ok
theorem branch_box_3102_nonnegative : ∀ j, 0 ≤ branch_box_3102.lower j ∧ 0 ≤ branch_box_3102.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3102, Box.profileLo, Box.profileHi, box_3102]
theorem leaf_3102_BranchSafe : CertificateConsequences.BranchSafe branch_box_3102 := by
  left; refine ⟨branch_box_3102_nonnegative, ?_⟩
  intro z hz; exact leaf_3102_sound hz

theorem leaf_3103_ok : checkAt 527 1000 box_3103 cert_3103 = true := by
  have h := List.all_eq_true.mp batch_62_02_ok accepted_3103 (by simp [batch_62_02_values])
  exact h
theorem leaf_3103_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3103.profileLo box_3103.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3103_ok
theorem branch_box_3103_nonnegative : ∀ j, 0 ≤ branch_box_3103.lower j ∧ 0 ≤ branch_box_3103.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3103, Box.profileLo, Box.profileHi, box_3103]
theorem leaf_3103_BranchSafe : CertificateConsequences.BranchSafe branch_box_3103 := by
  left; refine ⟨branch_box_3103_nonnegative, ?_⟩
  intro z hz; exact leaf_3103_sound hz

theorem leaf_3106_ok : checkAt 527 1000 box_3106 cert_3106 = true := by
  have h := List.all_eq_true.mp batch_62_03_ok accepted_3106 (by simp [batch_62_03_values])
  exact h
theorem leaf_3106_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3106.profileLo box_3106.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3106_ok
theorem branch_box_3106_nonnegative : ∀ j, 0 ≤ branch_box_3106.lower j ∧ 0 ≤ branch_box_3106.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3106, Box.profileLo, Box.profileHi, box_3106]
theorem leaf_3106_BranchSafe : CertificateConsequences.BranchSafe branch_box_3106 := by
  left; refine ⟨branch_box_3106_nonnegative, ?_⟩
  intro z hz; exact leaf_3106_sound hz

theorem leaf_3108_ok : checkAt 527 1000 box_3108 cert_3108 = true := by
  have h := List.all_eq_true.mp batch_62_04_ok accepted_3108 (by simp [batch_62_04_values])
  exact h
theorem leaf_3108_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3108.profileLo box_3108.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3108_ok
theorem branch_box_3108_nonnegative : ∀ j, 0 ≤ branch_box_3108.lower j ∧ 0 ≤ branch_box_3108.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3108, Box.profileLo, Box.profileHi, box_3108]
theorem leaf_3108_BranchSafe : CertificateConsequences.BranchSafe branch_box_3108 := by
  left; refine ⟨branch_box_3108_nonnegative, ?_⟩
  intro z hz; exact leaf_3108_sound hz

theorem leaf_3110_ok : checkAt 527 1000 box_3110 cert_3110 = true := by
  have h := List.all_eq_true.mp batch_62_05_ok accepted_3110 (by simp [batch_62_05_values])
  exact h
theorem leaf_3110_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3110.profileLo box_3110.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3110_ok
theorem branch_box_3110_nonnegative : ∀ j, 0 ≤ branch_box_3110.lower j ∧ 0 ≤ branch_box_3110.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3110, Box.profileLo, Box.profileHi, box_3110]
theorem leaf_3110_BranchSafe : CertificateConsequences.BranchSafe branch_box_3110 := by
  left; refine ⟨branch_box_3110_nonnegative, ?_⟩
  intro z hz; exact leaf_3110_sound hz

theorem leaf_3112_ok : checkAt 527 1000 box_3112 cert_3112 = true := by
  have h := List.all_eq_true.mp batch_62_06_ok accepted_3112 (by simp [batch_62_06_values])
  exact h
theorem leaf_3112_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3112.profileLo box_3112.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3112_ok
theorem branch_box_3112_nonnegative : ∀ j, 0 ≤ branch_box_3112.lower j ∧ 0 ≤ branch_box_3112.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3112, Box.profileLo, Box.profileHi, box_3112]
theorem leaf_3112_BranchSafe : CertificateConsequences.BranchSafe branch_box_3112 := by
  left; refine ⟨branch_box_3112_nonnegative, ?_⟩
  intro z hz; exact leaf_3112_sound hz

theorem leaf_3114_ok : checkAt 527 1000 box_3114 cert_3114 = true := by
  have h := List.all_eq_true.mp batch_62_07_ok accepted_3114 (by simp [batch_62_07_values])
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

theorem leaf_3117_ok : checkAt 527 1000 box_3117 cert_3117 = true := by
  have h := List.all_eq_true.mp batch_62_08_ok accepted_3117 (by simp [batch_62_08_values])
  exact h
theorem leaf_3117_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3117.profileLo box_3117.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3117_ok
theorem branch_box_3117_nonnegative : ∀ j, 0 ≤ branch_box_3117.lower j ∧ 0 ≤ branch_box_3117.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3117, Box.profileLo, Box.profileHi, box_3117]
theorem leaf_3117_BranchSafe : CertificateConsequences.BranchSafe branch_box_3117 := by
  left; refine ⟨branch_box_3117_nonnegative, ?_⟩
  intro z hz; exact leaf_3117_sound hz

theorem leaf_3120_ok : checkAt 527 1000 box_3120 cert_3120 = true := by
  have h := List.all_eq_true.mp batch_62_09_ok accepted_3120 (by simp [batch_62_09_values])
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

theorem leaf_3122_ok : checkAt 527 1000 box_3122 cert_3122 = true := by
  have h := List.all_eq_true.mp batch_62_10_ok accepted_3122 (by simp [batch_62_10_values])
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
  have h := List.all_eq_true.mp batch_62_11_ok accepted_3124 (by simp [batch_62_11_values])
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

theorem leaf_3126_ok : checkAt 527 1000 box_3126 cert_3126 = true := by
  have h := List.all_eq_true.mp batch_62_12_ok accepted_3126 (by simp [batch_62_12_values])
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

theorem leaf_3128_ok : checkAt 527 1000 box_3128 cert_3128 = true := by
  have h := List.all_eq_true.mp batch_62_13_ok accepted_3128 (by simp [batch_62_13_values])
  exact h
theorem leaf_3128_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3128.profileLo box_3128.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3128_ok
theorem branch_box_3128_nonnegative : ∀ j, 0 ≤ branch_box_3128.lower j ∧ 0 ≤ branch_box_3128.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3128, Box.profileLo, Box.profileHi, box_3128]
theorem leaf_3128_BranchSafe : CertificateConsequences.BranchSafe branch_box_3128 := by
  left; refine ⟨branch_box_3128_nonnegative, ?_⟩
  intro z hz; exact leaf_3128_sound hz

theorem leaf_3130_ok : checkAt 527 1000 box_3130 cert_3130 = true := by
  have h := List.all_eq_true.mp batch_62_14_ok accepted_3130 (by simp [batch_62_14_values])
  exact h
theorem leaf_3130_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3130.profileLo box_3130.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3130_ok
theorem branch_box_3130_nonnegative : ∀ j, 0 ≤ branch_box_3130.lower j ∧ 0 ≤ branch_box_3130.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3130, Box.profileLo, Box.profileHi, box_3130]
theorem leaf_3130_BranchSafe : CertificateConsequences.BranchSafe branch_box_3130 := by
  left; refine ⟨branch_box_3130_nonnegative, ?_⟩
  intro z hz; exact leaf_3130_sound hz

theorem leaf_3138_ok : checkAt 527 1000 box_3138 cert_3138 = true := by
  have h := List.all_eq_true.mp batch_62_15_ok accepted_3138 (by simp [batch_62_15_values])
  exact h
theorem leaf_3138_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3138.profileLo box_3138.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3138_ok
theorem branch_box_3138_nonnegative : ∀ j, 0 ≤ branch_box_3138.lower j ∧ 0 ≤ branch_box_3138.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3138, Box.profileLo, Box.profileHi, box_3138]
theorem leaf_3138_BranchSafe : CertificateConsequences.BranchSafe branch_box_3138 := by
  left; refine ⟨branch_box_3138_nonnegative, ?_⟩
  intro z hz; exact leaf_3138_sound hz

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

theorem leaf_3142_ok : checkAt 527 1000 box_3142 cert_3142 = true := by
  have h := List.all_eq_true.mp batch_62_17_ok accepted_3142 (by simp [batch_62_17_values])
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
  have h := List.all_eq_true.mp batch_62_18_ok accepted_3143 (by simp [batch_62_18_values])
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
  have h := List.all_eq_true.mp batch_62_19_ok accepted_3145 (by simp [batch_62_19_values])
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

theorem leaf_3149_ok : checkAt 527 1000 box_3149 cert_3149 = true := by
  have h := List.all_eq_true.mp batch_62_20_ok accepted_3149 (by simp [batch_62_20_values])
  exact h
theorem leaf_3149_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3149.profileLo box_3149.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3149_ok
theorem branch_box_3149_nonnegative : ∀ j, 0 ≤ branch_box_3149.lower j ∧ 0 ≤ branch_box_3149.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3149, Box.profileLo, Box.profileHi, box_3149]
theorem leaf_3149_BranchSafe : CertificateConsequences.BranchSafe branch_box_3149 := by
  left; refine ⟨branch_box_3149_nonnegative, ?_⟩
  intro z hz; exact leaf_3149_sound hz

#print axioms batch_62_00_ok
#print axioms leaf_3100_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
