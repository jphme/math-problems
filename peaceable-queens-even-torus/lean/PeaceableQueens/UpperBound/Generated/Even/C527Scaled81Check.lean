import PeaceableQueens.UpperBound.Generated.Even.C527Scaled81Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_81_00_values : List Bool := [accepted_4050]
theorem batch_81_00_ok : batch_81_00_values.all id = true := by decide

def batch_81_01_values : List Bool := [accepted_4051]
theorem batch_81_01_ok : batch_81_01_values.all id = true := by decide

def batch_81_02_values : List Bool := [accepted_4054]
theorem batch_81_02_ok : batch_81_02_values.all id = true := by decide

def batch_81_03_values : List Bool := [accepted_4055]
theorem batch_81_03_ok : batch_81_03_values.all id = true := by decide

def batch_81_04_values : List Bool := [accepted_4058]
theorem batch_81_04_ok : batch_81_04_values.all id = true := by decide

def batch_81_05_values : List Bool := [accepted_4059]
theorem batch_81_05_ok : batch_81_05_values.all id = true := by decide

def batch_81_06_values : List Bool := [accepted_4060]
theorem batch_81_06_ok : batch_81_06_values.all id = true := by decide

def batch_81_07_values : List Bool := [accepted_4062]
theorem batch_81_07_ok : batch_81_07_values.all id = true := by decide

def batch_81_08_values : List Bool := [accepted_4064]
theorem batch_81_08_ok : batch_81_08_values.all id = true := by decide

def batch_81_09_values : List Bool := [accepted_4066]
theorem batch_81_09_ok : batch_81_09_values.all id = true := by decide

def batch_81_10_values : List Bool := [accepted_4068]
theorem batch_81_10_ok : batch_81_10_values.all id = true := by decide

def batch_81_11_values : List Bool := [accepted_4069]
theorem batch_81_11_ok : batch_81_11_values.all id = true := by decide

def batch_81_12_values : List Bool := [accepted_4072]
theorem batch_81_12_ok : batch_81_12_values.all id = true := by decide

def batch_81_13_values : List Bool := [accepted_4073]
theorem batch_81_13_ok : batch_81_13_values.all id = true := by decide

def batch_81_14_values : List Bool := [accepted_4076]
theorem batch_81_14_ok : batch_81_14_values.all id = true := by decide

def batch_81_15_values : List Bool := [accepted_4079]
theorem batch_81_15_ok : batch_81_15_values.all id = true := by decide

def batch_81_16_values : List Bool := [accepted_4081]
theorem batch_81_16_ok : batch_81_16_values.all id = true := by decide

def batch_81_17_values : List Bool := [accepted_4084]
theorem batch_81_17_ok : batch_81_17_values.all id = true := by decide

def batch_81_18_values : List Bool := [accepted_4086]
theorem batch_81_18_ok : batch_81_18_values.all id = true := by decide

def batch_81_19_values : List Bool := [accepted_4087]
theorem batch_81_19_ok : batch_81_19_values.all id = true := by decide

def batch_81_20_values : List Bool := [accepted_4088]
theorem batch_81_20_ok : batch_81_20_values.all id = true := by decide

def batch_81_21_values : List Bool := [accepted_4091]
theorem batch_81_21_ok : batch_81_21_values.all id = true := by decide

def batch_81_22_values : List Bool := [accepted_4092]
theorem batch_81_22_ok : batch_81_22_values.all id = true := by decide

def batch_81_23_values : List Bool := [accepted_4093]
theorem batch_81_23_ok : batch_81_23_values.all id = true := by decide

def batch_81_24_values : List Bool := [accepted_4095]
theorem batch_81_24_ok : batch_81_24_values.all id = true := by decide

def batch_81_25_values : List Bool := [accepted_4096]
theorem batch_81_25_ok : batch_81_25_values.all id = true := by decide

theorem leaf_4050_ok : checkAt 527 1000 box_4050 cert_4050 = true := by
  have h := List.all_eq_true.mp batch_81_00_ok accepted_4050 (by simp [batch_81_00_values])
  exact h
theorem leaf_4050_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4050.profileLo box_4050.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4050_ok
theorem branch_box_4050_nonnegative : ∀ j, 0 ≤ branch_box_4050.lower j ∧ 0 ≤ branch_box_4050.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4050, Box.profileLo, Box.profileHi, box_4050]
theorem leaf_4050_BranchSafe : CertificateConsequences.BranchSafe branch_box_4050 := by
  left; refine ⟨branch_box_4050_nonnegative, ?_⟩
  intro z hz; exact leaf_4050_sound hz

theorem leaf_4051_ok : checkAt 527 1000 box_4051 cert_4051 = true := by
  have h := List.all_eq_true.mp batch_81_01_ok accepted_4051 (by simp [batch_81_01_values])
  exact h
theorem leaf_4051_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4051.profileLo box_4051.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4051_ok
theorem branch_box_4051_nonnegative : ∀ j, 0 ≤ branch_box_4051.lower j ∧ 0 ≤ branch_box_4051.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4051, Box.profileLo, Box.profileHi, box_4051]
theorem leaf_4051_BranchSafe : CertificateConsequences.BranchSafe branch_box_4051 := by
  left; refine ⟨branch_box_4051_nonnegative, ?_⟩
  intro z hz; exact leaf_4051_sound hz

theorem leaf_4054_ok : checkAt 527 1000 box_4054 cert_4054 = true := by
  have h := List.all_eq_true.mp batch_81_02_ok accepted_4054 (by simp [batch_81_02_values])
  exact h
theorem leaf_4054_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4054.profileLo box_4054.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4054_ok
theorem branch_box_4054_nonnegative : ∀ j, 0 ≤ branch_box_4054.lower j ∧ 0 ≤ branch_box_4054.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4054, Box.profileLo, Box.profileHi, box_4054]
theorem leaf_4054_BranchSafe : CertificateConsequences.BranchSafe branch_box_4054 := by
  left; refine ⟨branch_box_4054_nonnegative, ?_⟩
  intro z hz; exact leaf_4054_sound hz

theorem leaf_4055_ok : checkAt 527 1000 box_4055 cert_4055 = true := by
  have h := List.all_eq_true.mp batch_81_03_ok accepted_4055 (by simp [batch_81_03_values])
  exact h
theorem leaf_4055_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4055.profileLo box_4055.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4055_ok
theorem branch_box_4055_nonnegative : ∀ j, 0 ≤ branch_box_4055.lower j ∧ 0 ≤ branch_box_4055.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4055, Box.profileLo, Box.profileHi, box_4055]
theorem leaf_4055_BranchSafe : CertificateConsequences.BranchSafe branch_box_4055 := by
  left; refine ⟨branch_box_4055_nonnegative, ?_⟩
  intro z hz; exact leaf_4055_sound hz

theorem leaf_4058_ok : checkAt 527 1000 box_4058 cert_4058 = true := by
  have h := List.all_eq_true.mp batch_81_04_ok accepted_4058 (by simp [batch_81_04_values])
  exact h
theorem leaf_4058_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4058.profileLo box_4058.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4058_ok
theorem branch_box_4058_nonnegative : ∀ j, 0 ≤ branch_box_4058.lower j ∧ 0 ≤ branch_box_4058.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4058, Box.profileLo, Box.profileHi, box_4058]
theorem leaf_4058_BranchSafe : CertificateConsequences.BranchSafe branch_box_4058 := by
  left; refine ⟨branch_box_4058_nonnegative, ?_⟩
  intro z hz; exact leaf_4058_sound hz

theorem leaf_4059_ok : checkAt 527 1000 box_4059 cert_4059 = true := by
  have h := List.all_eq_true.mp batch_81_05_ok accepted_4059 (by simp [batch_81_05_values])
  exact h
theorem leaf_4059_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4059.profileLo box_4059.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4059_ok
theorem branch_box_4059_nonnegative : ∀ j, 0 ≤ branch_box_4059.lower j ∧ 0 ≤ branch_box_4059.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4059, Box.profileLo, Box.profileHi, box_4059]
theorem leaf_4059_BranchSafe : CertificateConsequences.BranchSafe branch_box_4059 := by
  left; refine ⟨branch_box_4059_nonnegative, ?_⟩
  intro z hz; exact leaf_4059_sound hz

theorem leaf_4060_ok : checkAt 527 1000 box_4060 cert_4060 = true := by
  have h := List.all_eq_true.mp batch_81_06_ok accepted_4060 (by simp [batch_81_06_values])
  exact h
theorem leaf_4060_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4060.profileLo box_4060.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4060_ok
theorem branch_box_4060_nonnegative : ∀ j, 0 ≤ branch_box_4060.lower j ∧ 0 ≤ branch_box_4060.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4060, Box.profileLo, Box.profileHi, box_4060]
theorem leaf_4060_BranchSafe : CertificateConsequences.BranchSafe branch_box_4060 := by
  left; refine ⟨branch_box_4060_nonnegative, ?_⟩
  intro z hz; exact leaf_4060_sound hz

theorem leaf_4062_ok : checkAt 527 1000 box_4062 cert_4062 = true := by
  have h := List.all_eq_true.mp batch_81_07_ok accepted_4062 (by simp [batch_81_07_values])
  exact h
theorem leaf_4062_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4062.profileLo box_4062.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4062_ok
theorem branch_box_4062_nonnegative : ∀ j, 0 ≤ branch_box_4062.lower j ∧ 0 ≤ branch_box_4062.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4062, Box.profileLo, Box.profileHi, box_4062]
theorem leaf_4062_BranchSafe : CertificateConsequences.BranchSafe branch_box_4062 := by
  left; refine ⟨branch_box_4062_nonnegative, ?_⟩
  intro z hz; exact leaf_4062_sound hz

theorem leaf_4064_ok : checkAt 527 1000 box_4064 cert_4064 = true := by
  have h := List.all_eq_true.mp batch_81_08_ok accepted_4064 (by simp [batch_81_08_values])
  exact h
theorem leaf_4064_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4064.profileLo box_4064.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4064_ok
theorem branch_box_4064_nonnegative : ∀ j, 0 ≤ branch_box_4064.lower j ∧ 0 ≤ branch_box_4064.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4064, Box.profileLo, Box.profileHi, box_4064]
theorem leaf_4064_BranchSafe : CertificateConsequences.BranchSafe branch_box_4064 := by
  left; refine ⟨branch_box_4064_nonnegative, ?_⟩
  intro z hz; exact leaf_4064_sound hz

theorem leaf_4066_ok : checkAt 527 1000 box_4066 cert_4066 = true := by
  have h := List.all_eq_true.mp batch_81_09_ok accepted_4066 (by simp [batch_81_09_values])
  exact h
theorem leaf_4066_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4066.profileLo box_4066.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4066_ok
theorem branch_box_4066_nonnegative : ∀ j, 0 ≤ branch_box_4066.lower j ∧ 0 ≤ branch_box_4066.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4066, Box.profileLo, Box.profileHi, box_4066]
theorem leaf_4066_BranchSafe : CertificateConsequences.BranchSafe branch_box_4066 := by
  left; refine ⟨branch_box_4066_nonnegative, ?_⟩
  intro z hz; exact leaf_4066_sound hz

theorem leaf_4068_ok : checkAt 527 1000 box_4068 cert_4068 = true := by
  have h := List.all_eq_true.mp batch_81_10_ok accepted_4068 (by simp [batch_81_10_values])
  exact h
theorem leaf_4068_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4068.profileLo box_4068.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4068_ok
theorem branch_box_4068_nonnegative : ∀ j, 0 ≤ branch_box_4068.lower j ∧ 0 ≤ branch_box_4068.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4068, Box.profileLo, Box.profileHi, box_4068]
theorem leaf_4068_BranchSafe : CertificateConsequences.BranchSafe branch_box_4068 := by
  left; refine ⟨branch_box_4068_nonnegative, ?_⟩
  intro z hz; exact leaf_4068_sound hz

theorem leaf_4069_ok : checkAt 527 1000 box_4069 cert_4069 = true := by
  have h := List.all_eq_true.mp batch_81_11_ok accepted_4069 (by simp [batch_81_11_values])
  exact h
theorem leaf_4069_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4069.profileLo box_4069.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4069_ok
theorem branch_box_4069_nonnegative : ∀ j, 0 ≤ branch_box_4069.lower j ∧ 0 ≤ branch_box_4069.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4069, Box.profileLo, Box.profileHi, box_4069]
theorem leaf_4069_BranchSafe : CertificateConsequences.BranchSafe branch_box_4069 := by
  left; refine ⟨branch_box_4069_nonnegative, ?_⟩
  intro z hz; exact leaf_4069_sound hz

theorem leaf_4072_ok : checkAt 527 1000 box_4072 cert_4072 = true := by
  have h := List.all_eq_true.mp batch_81_12_ok accepted_4072 (by simp [batch_81_12_values])
  exact h
theorem leaf_4072_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4072.profileLo box_4072.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4072_ok
theorem branch_box_4072_nonnegative : ∀ j, 0 ≤ branch_box_4072.lower j ∧ 0 ≤ branch_box_4072.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4072, Box.profileLo, Box.profileHi, box_4072]
theorem leaf_4072_BranchSafe : CertificateConsequences.BranchSafe branch_box_4072 := by
  left; refine ⟨branch_box_4072_nonnegative, ?_⟩
  intro z hz; exact leaf_4072_sound hz

theorem leaf_4073_ok : checkAt 527 1000 box_4073 cert_4073 = true := by
  have h := List.all_eq_true.mp batch_81_13_ok accepted_4073 (by simp [batch_81_13_values])
  exact h
theorem leaf_4073_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4073.profileLo box_4073.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4073_ok
theorem branch_box_4073_nonnegative : ∀ j, 0 ≤ branch_box_4073.lower j ∧ 0 ≤ branch_box_4073.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4073, Box.profileLo, Box.profileHi, box_4073]
theorem leaf_4073_BranchSafe : CertificateConsequences.BranchSafe branch_box_4073 := by
  left; refine ⟨branch_box_4073_nonnegative, ?_⟩
  intro z hz; exact leaf_4073_sound hz

theorem leaf_4076_ok : checkAt 527 1000 box_4076 cert_4076 = true := by
  have h := List.all_eq_true.mp batch_81_14_ok accepted_4076 (by simp [batch_81_14_values])
  exact h
theorem leaf_4076_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4076.profileLo box_4076.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4076_ok
theorem branch_box_4076_nonnegative : ∀ j, 0 ≤ branch_box_4076.lower j ∧ 0 ≤ branch_box_4076.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4076, Box.profileLo, Box.profileHi, box_4076]
theorem leaf_4076_BranchSafe : CertificateConsequences.BranchSafe branch_box_4076 := by
  left; refine ⟨branch_box_4076_nonnegative, ?_⟩
  intro z hz; exact leaf_4076_sound hz

theorem leaf_4079_ok : checkAt 527 1000 box_4079 cert_4079 = true := by
  have h := List.all_eq_true.mp batch_81_15_ok accepted_4079 (by simp [batch_81_15_values])
  exact h
theorem leaf_4079_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4079.profileLo box_4079.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4079_ok
theorem branch_box_4079_nonnegative : ∀ j, 0 ≤ branch_box_4079.lower j ∧ 0 ≤ branch_box_4079.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4079, Box.profileLo, Box.profileHi, box_4079]
theorem leaf_4079_BranchSafe : CertificateConsequences.BranchSafe branch_box_4079 := by
  left; refine ⟨branch_box_4079_nonnegative, ?_⟩
  intro z hz; exact leaf_4079_sound hz

theorem leaf_4081_ok : checkAt 527 1000 box_4081 cert_4081 = true := by
  have h := List.all_eq_true.mp batch_81_16_ok accepted_4081 (by simp [batch_81_16_values])
  exact h
theorem leaf_4081_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4081.profileLo box_4081.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4081_ok
theorem branch_box_4081_nonnegative : ∀ j, 0 ≤ branch_box_4081.lower j ∧ 0 ≤ branch_box_4081.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4081, Box.profileLo, Box.profileHi, box_4081]
theorem leaf_4081_BranchSafe : CertificateConsequences.BranchSafe branch_box_4081 := by
  left; refine ⟨branch_box_4081_nonnegative, ?_⟩
  intro z hz; exact leaf_4081_sound hz

theorem leaf_4084_ok : checkAt 527 1000 box_4084 cert_4084 = true := by
  have h := List.all_eq_true.mp batch_81_17_ok accepted_4084 (by simp [batch_81_17_values])
  exact h
theorem leaf_4084_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4084.profileLo box_4084.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4084_ok
theorem branch_box_4084_nonnegative : ∀ j, 0 ≤ branch_box_4084.lower j ∧ 0 ≤ branch_box_4084.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4084, Box.profileLo, Box.profileHi, box_4084]
theorem leaf_4084_BranchSafe : CertificateConsequences.BranchSafe branch_box_4084 := by
  left; refine ⟨branch_box_4084_nonnegative, ?_⟩
  intro z hz; exact leaf_4084_sound hz

theorem leaf_4086_ok : checkAt 527 1000 box_4086 cert_4086 = true := by
  have h := List.all_eq_true.mp batch_81_18_ok accepted_4086 (by simp [batch_81_18_values])
  exact h
theorem leaf_4086_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4086.profileLo box_4086.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4086_ok
theorem branch_box_4086_nonnegative : ∀ j, 0 ≤ branch_box_4086.lower j ∧ 0 ≤ branch_box_4086.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4086, Box.profileLo, Box.profileHi, box_4086]
theorem leaf_4086_BranchSafe : CertificateConsequences.BranchSafe branch_box_4086 := by
  left; refine ⟨branch_box_4086_nonnegative, ?_⟩
  intro z hz; exact leaf_4086_sound hz

theorem leaf_4087_ok : checkAt 527 1000 box_4087 cert_4087 = true := by
  have h := List.all_eq_true.mp batch_81_19_ok accepted_4087 (by simp [batch_81_19_values])
  exact h
theorem leaf_4087_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4087.profileLo box_4087.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4087_ok
theorem branch_box_4087_nonnegative : ∀ j, 0 ≤ branch_box_4087.lower j ∧ 0 ≤ branch_box_4087.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4087, Box.profileLo, Box.profileHi, box_4087]
theorem leaf_4087_BranchSafe : CertificateConsequences.BranchSafe branch_box_4087 := by
  left; refine ⟨branch_box_4087_nonnegative, ?_⟩
  intro z hz; exact leaf_4087_sound hz

theorem leaf_4088_ok : checkAt 527 1000 box_4088 cert_4088 = true := by
  have h := List.all_eq_true.mp batch_81_20_ok accepted_4088 (by simp [batch_81_20_values])
  exact h
theorem leaf_4088_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4088.profileLo box_4088.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4088_ok
theorem branch_box_4088_nonnegative : ∀ j, 0 ≤ branch_box_4088.lower j ∧ 0 ≤ branch_box_4088.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4088, Box.profileLo, Box.profileHi, box_4088]
theorem leaf_4088_BranchSafe : CertificateConsequences.BranchSafe branch_box_4088 := by
  left; refine ⟨branch_box_4088_nonnegative, ?_⟩
  intro z hz; exact leaf_4088_sound hz

theorem leaf_4091_ok : checkAt 527 1000 box_4091 cert_4091 = true := by
  have h := List.all_eq_true.mp batch_81_21_ok accepted_4091 (by simp [batch_81_21_values])
  exact h
theorem leaf_4091_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4091.profileLo box_4091.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4091_ok
theorem branch_box_4091_nonnegative : ∀ j, 0 ≤ branch_box_4091.lower j ∧ 0 ≤ branch_box_4091.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4091, Box.profileLo, Box.profileHi, box_4091]
theorem leaf_4091_BranchSafe : CertificateConsequences.BranchSafe branch_box_4091 := by
  left; refine ⟨branch_box_4091_nonnegative, ?_⟩
  intro z hz; exact leaf_4091_sound hz

theorem leaf_4092_ok : checkAt 527 1000 box_4092 cert_4092 = true := by
  have h := List.all_eq_true.mp batch_81_22_ok accepted_4092 (by simp [batch_81_22_values])
  exact h
theorem leaf_4092_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4092.profileLo box_4092.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4092_ok
theorem branch_box_4092_nonnegative : ∀ j, 0 ≤ branch_box_4092.lower j ∧ 0 ≤ branch_box_4092.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4092, Box.profileLo, Box.profileHi, box_4092]
theorem leaf_4092_BranchSafe : CertificateConsequences.BranchSafe branch_box_4092 := by
  left; refine ⟨branch_box_4092_nonnegative, ?_⟩
  intro z hz; exact leaf_4092_sound hz

theorem leaf_4093_ok : checkAt 527 1000 box_4093 cert_4093 = true := by
  have h := List.all_eq_true.mp batch_81_23_ok accepted_4093 (by simp [batch_81_23_values])
  exact h
theorem leaf_4093_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4093.profileLo box_4093.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4093_ok
theorem branch_box_4093_nonnegative : ∀ j, 0 ≤ branch_box_4093.lower j ∧ 0 ≤ branch_box_4093.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4093, Box.profileLo, Box.profileHi, box_4093]
theorem leaf_4093_BranchSafe : CertificateConsequences.BranchSafe branch_box_4093 := by
  left; refine ⟨branch_box_4093_nonnegative, ?_⟩
  intro z hz; exact leaf_4093_sound hz

theorem leaf_4095_ok : checkAt 527 1000 box_4095 cert_4095 = true := by
  have h := List.all_eq_true.mp batch_81_24_ok accepted_4095 (by simp [batch_81_24_values])
  exact h
theorem leaf_4095_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4095.profileLo box_4095.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4095_ok
theorem branch_box_4095_nonnegative : ∀ j, 0 ≤ branch_box_4095.lower j ∧ 0 ≤ branch_box_4095.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4095, Box.profileLo, Box.profileHi, box_4095]
theorem leaf_4095_BranchSafe : CertificateConsequences.BranchSafe branch_box_4095 := by
  left; refine ⟨branch_box_4095_nonnegative, ?_⟩
  intro z hz; exact leaf_4095_sound hz

theorem leaf_4096_ok : checkAt 527 1000 box_4096 cert_4096 = true := by
  have h := List.all_eq_true.mp batch_81_25_ok accepted_4096 (by simp [batch_81_25_values])
  exact h
theorem leaf_4096_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4096.profileLo box_4096.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4096_ok
theorem branch_box_4096_nonnegative : ∀ j, 0 ≤ branch_box_4096.lower j ∧ 0 ≤ branch_box_4096.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4096, Box.profileLo, Box.profileHi, box_4096]
theorem leaf_4096_BranchSafe : CertificateConsequences.BranchSafe branch_box_4096 := by
  left; refine ⟨branch_box_4096_nonnegative, ?_⟩
  intro z hz; exact leaf_4096_sound hz

#print axioms batch_81_00_ok
#print axioms leaf_4050_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
