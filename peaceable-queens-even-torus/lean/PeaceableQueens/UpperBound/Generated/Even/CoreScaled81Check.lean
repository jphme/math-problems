import PeaceableQueens.UpperBound.Generated.Even.CoreScaled81Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_81_00_values : List Bool := [accepted_4052]
theorem batch_81_00_ok : batch_81_00_values.all id = true := by decide

def batch_81_01_values : List Bool := [accepted_4054]
theorem batch_81_01_ok : batch_81_01_values.all id = true := by decide

def batch_81_02_values : List Bool := [accepted_4056]
theorem batch_81_02_ok : batch_81_02_values.all id = true := by decide

def batch_81_03_values : List Bool := [accepted_4058]
theorem batch_81_03_ok : batch_81_03_values.all id = true := by decide

def batch_81_04_values : List Bool := [accepted_4060]
theorem batch_81_04_ok : batch_81_04_values.all id = true := by decide

def batch_81_05_values : List Bool := [accepted_4062]
theorem batch_81_05_ok : batch_81_05_values.all id = true := by decide

def batch_81_06_values : List Bool := [accepted_4065]
theorem batch_81_06_ok : batch_81_06_values.all id = true := by decide

def batch_81_07_values : List Bool := [accepted_4068]
theorem batch_81_07_ok : batch_81_07_values.all id = true := by decide

def batch_81_08_values : List Bool := [accepted_4070]
theorem batch_81_08_ok : batch_81_08_values.all id = true := by decide

def batch_81_09_values : List Bool := [accepted_4072]
theorem batch_81_09_ok : batch_81_09_values.all id = true := by decide

def batch_81_10_values : List Bool := [accepted_4074]
theorem batch_81_10_ok : batch_81_10_values.all id = true := by decide

def batch_81_11_values : List Bool := [accepted_4075]
theorem batch_81_11_ok : batch_81_11_values.all id = true := by decide

def batch_81_12_values : List Bool := [accepted_4077]
theorem batch_81_12_ok : batch_81_12_values.all id = true := by decide

def batch_81_13_values : List Bool := [accepted_4080]
theorem batch_81_13_ok : batch_81_13_values.all id = true := by decide

def batch_81_14_values : List Bool := [accepted_4082]
theorem batch_81_14_ok : batch_81_14_values.all id = true := by decide

def batch_81_15_values : List Bool := [accepted_4084]
theorem batch_81_15_ok : batch_81_15_values.all id = true := by decide

def batch_81_16_values : List Bool := [accepted_4086]
theorem batch_81_16_ok : batch_81_16_values.all id = true := by decide

def batch_81_17_values : List Bool := [accepted_4087]
theorem batch_81_17_ok : batch_81_17_values.all id = true := by decide

def batch_81_18_values : List Bool := [accepted_4090]
theorem batch_81_18_ok : batch_81_18_values.all id = true := by decide

def batch_81_19_values : List Bool := [accepted_4091]
theorem batch_81_19_ok : batch_81_19_values.all id = true := by decide

def batch_81_20_values : List Bool := [accepted_4094]
theorem batch_81_20_ok : batch_81_20_values.all id = true := by decide

def batch_81_21_values : List Bool := [accepted_4096]
theorem batch_81_21_ok : batch_81_21_values.all id = true := by decide

def batch_81_22_values : List Bool := [accepted_4097]
theorem batch_81_22_ok : batch_81_22_values.all id = true := by decide

def batch_81_23_values : List Bool := [accepted_4099]
theorem batch_81_23_ok : batch_81_23_values.all id = true := by decide

theorem leaf_4052_ok : checkAt 527 1000 box_4052 cert_4052 = true := by
  have h := List.all_eq_true.mp batch_81_00_ok accepted_4052 (by simp [batch_81_00_values])
  exact h
theorem leaf_4052_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4052.profileLo box_4052.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4052_ok
theorem branch_box_4052_nonnegative : ∀ j, 0 ≤ branch_box_4052.lower j ∧ 0 ≤ branch_box_4052.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4052, Box.profileLo, Box.profileHi, box_4052]
theorem leaf_4052_BranchSafe : CertificateConsequences.BranchSafe branch_box_4052 := by
  left; refine ⟨branch_box_4052_nonnegative, ?_⟩
  intro z hz; exact leaf_4052_sound hz

theorem leaf_4054_ok : checkAt 527 1000 box_4054 cert_4054 = true := by
  have h := List.all_eq_true.mp batch_81_01_ok accepted_4054 (by simp [batch_81_01_values])
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

theorem leaf_4056_ok : checkAt 527 1000 box_4056 cert_4056 = true := by
  have h := List.all_eq_true.mp batch_81_02_ok accepted_4056 (by simp [batch_81_02_values])
  exact h
theorem leaf_4056_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4056.profileLo box_4056.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4056_ok
theorem branch_box_4056_nonnegative : ∀ j, 0 ≤ branch_box_4056.lower j ∧ 0 ≤ branch_box_4056.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4056, Box.profileLo, Box.profileHi, box_4056]
theorem leaf_4056_BranchSafe : CertificateConsequences.BranchSafe branch_box_4056 := by
  left; refine ⟨branch_box_4056_nonnegative, ?_⟩
  intro z hz; exact leaf_4056_sound hz

theorem leaf_4058_ok : checkAt 527 1000 box_4058 cert_4058 = true := by
  have h := List.all_eq_true.mp batch_81_03_ok accepted_4058 (by simp [batch_81_03_values])
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

theorem leaf_4060_ok : checkAt 527 1000 box_4060 cert_4060 = true := by
  have h := List.all_eq_true.mp batch_81_04_ok accepted_4060 (by simp [batch_81_04_values])
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
  have h := List.all_eq_true.mp batch_81_05_ok accepted_4062 (by simp [batch_81_05_values])
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

theorem leaf_4065_ok : checkAt 527 1000 box_4065 cert_4065 = true := by
  have h := List.all_eq_true.mp batch_81_06_ok accepted_4065 (by simp [batch_81_06_values])
  exact h
theorem leaf_4065_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4065.profileLo box_4065.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4065_ok
theorem branch_box_4065_nonnegative : ∀ j, 0 ≤ branch_box_4065.lower j ∧ 0 ≤ branch_box_4065.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4065, Box.profileLo, Box.profileHi, box_4065]
theorem leaf_4065_BranchSafe : CertificateConsequences.BranchSafe branch_box_4065 := by
  left; refine ⟨branch_box_4065_nonnegative, ?_⟩
  intro z hz; exact leaf_4065_sound hz

theorem leaf_4068_ok : checkAt 527 1000 box_4068 cert_4068 = true := by
  have h := List.all_eq_true.mp batch_81_07_ok accepted_4068 (by simp [batch_81_07_values])
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

theorem leaf_4070_ok : checkAt 527 1000 box_4070 cert_4070 = true := by
  have h := List.all_eq_true.mp batch_81_08_ok accepted_4070 (by simp [batch_81_08_values])
  exact h
theorem leaf_4070_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4070.profileLo box_4070.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4070_ok
theorem branch_box_4070_nonnegative : ∀ j, 0 ≤ branch_box_4070.lower j ∧ 0 ≤ branch_box_4070.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4070, Box.profileLo, Box.profileHi, box_4070]
theorem leaf_4070_BranchSafe : CertificateConsequences.BranchSafe branch_box_4070 := by
  left; refine ⟨branch_box_4070_nonnegative, ?_⟩
  intro z hz; exact leaf_4070_sound hz

theorem leaf_4072_ok : checkAt 527 1000 box_4072 cert_4072 = true := by
  have h := List.all_eq_true.mp batch_81_09_ok accepted_4072 (by simp [batch_81_09_values])
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

theorem leaf_4074_ok : checkAt 527 1000 box_4074 cert_4074 = true := by
  have h := List.all_eq_true.mp batch_81_10_ok accepted_4074 (by simp [batch_81_10_values])
  exact h
theorem leaf_4074_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4074.profileLo box_4074.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4074_ok
theorem branch_box_4074_nonnegative : ∀ j, 0 ≤ branch_box_4074.lower j ∧ 0 ≤ branch_box_4074.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4074, Box.profileLo, Box.profileHi, box_4074]
theorem leaf_4074_BranchSafe : CertificateConsequences.BranchSafe branch_box_4074 := by
  left; refine ⟨branch_box_4074_nonnegative, ?_⟩
  intro z hz; exact leaf_4074_sound hz

theorem leaf_4075_ok : checkAt 527 1000 box_4075 cert_4075 = true := by
  have h := List.all_eq_true.mp batch_81_11_ok accepted_4075 (by simp [batch_81_11_values])
  exact h
theorem leaf_4075_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4075.profileLo box_4075.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4075_ok
theorem branch_box_4075_nonnegative : ∀ j, 0 ≤ branch_box_4075.lower j ∧ 0 ≤ branch_box_4075.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4075, Box.profileLo, Box.profileHi, box_4075]
theorem leaf_4075_BranchSafe : CertificateConsequences.BranchSafe branch_box_4075 := by
  left; refine ⟨branch_box_4075_nonnegative, ?_⟩
  intro z hz; exact leaf_4075_sound hz

theorem leaf_4077_ok : checkAt 527 1000 box_4077 cert_4077 = true := by
  have h := List.all_eq_true.mp batch_81_12_ok accepted_4077 (by simp [batch_81_12_values])
  exact h
theorem leaf_4077_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4077.profileLo box_4077.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4077_ok
theorem branch_box_4077_nonnegative : ∀ j, 0 ≤ branch_box_4077.lower j ∧ 0 ≤ branch_box_4077.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4077, Box.profileLo, Box.profileHi, box_4077]
theorem leaf_4077_BranchSafe : CertificateConsequences.BranchSafe branch_box_4077 := by
  left; refine ⟨branch_box_4077_nonnegative, ?_⟩
  intro z hz; exact leaf_4077_sound hz

theorem leaf_4080_ok : checkAt 527 1000 box_4080 cert_4080 = true := by
  have h := List.all_eq_true.mp batch_81_13_ok accepted_4080 (by simp [batch_81_13_values])
  exact h
theorem leaf_4080_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4080.profileLo box_4080.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4080_ok
theorem branch_box_4080_nonnegative : ∀ j, 0 ≤ branch_box_4080.lower j ∧ 0 ≤ branch_box_4080.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4080, Box.profileLo, Box.profileHi, box_4080]
theorem leaf_4080_BranchSafe : CertificateConsequences.BranchSafe branch_box_4080 := by
  left; refine ⟨branch_box_4080_nonnegative, ?_⟩
  intro z hz; exact leaf_4080_sound hz

theorem leaf_4082_ok : checkAt 527 1000 box_4082 cert_4082 = true := by
  have h := List.all_eq_true.mp batch_81_14_ok accepted_4082 (by simp [batch_81_14_values])
  exact h
theorem leaf_4082_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4082.profileLo box_4082.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4082_ok
theorem branch_box_4082_nonnegative : ∀ j, 0 ≤ branch_box_4082.lower j ∧ 0 ≤ branch_box_4082.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4082, Box.profileLo, Box.profileHi, box_4082]
theorem leaf_4082_BranchSafe : CertificateConsequences.BranchSafe branch_box_4082 := by
  left; refine ⟨branch_box_4082_nonnegative, ?_⟩
  intro z hz; exact leaf_4082_sound hz

theorem leaf_4084_ok : checkAt 527 1000 box_4084 cert_4084 = true := by
  have h := List.all_eq_true.mp batch_81_15_ok accepted_4084 (by simp [batch_81_15_values])
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
  have h := List.all_eq_true.mp batch_81_16_ok accepted_4086 (by simp [batch_81_16_values])
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
  have h := List.all_eq_true.mp batch_81_17_ok accepted_4087 (by simp [batch_81_17_values])
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

theorem leaf_4090_ok : checkAt 527 1000 box_4090 cert_4090 = true := by
  have h := List.all_eq_true.mp batch_81_18_ok accepted_4090 (by simp [batch_81_18_values])
  exact h
theorem leaf_4090_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4090.profileLo box_4090.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4090_ok
theorem branch_box_4090_nonnegative : ∀ j, 0 ≤ branch_box_4090.lower j ∧ 0 ≤ branch_box_4090.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4090, Box.profileLo, Box.profileHi, box_4090]
theorem leaf_4090_BranchSafe : CertificateConsequences.BranchSafe branch_box_4090 := by
  left; refine ⟨branch_box_4090_nonnegative, ?_⟩
  intro z hz; exact leaf_4090_sound hz

theorem leaf_4091_ok : checkAt 527 1000 box_4091 cert_4091 = true := by
  have h := List.all_eq_true.mp batch_81_19_ok accepted_4091 (by simp [batch_81_19_values])
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

theorem leaf_4094_ok : checkAt 527 1000 box_4094 cert_4094 = true := by
  have h := List.all_eq_true.mp batch_81_20_ok accepted_4094 (by simp [batch_81_20_values])
  exact h
theorem leaf_4094_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4094.profileLo box_4094.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4094_ok
theorem branch_box_4094_nonnegative : ∀ j, 0 ≤ branch_box_4094.lower j ∧ 0 ≤ branch_box_4094.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4094, Box.profileLo, Box.profileHi, box_4094]
theorem leaf_4094_BranchSafe : CertificateConsequences.BranchSafe branch_box_4094 := by
  left; refine ⟨branch_box_4094_nonnegative, ?_⟩
  intro z hz; exact leaf_4094_sound hz

theorem leaf_4096_ok : checkAt 527 1000 box_4096 cert_4096 = true := by
  have h := List.all_eq_true.mp batch_81_21_ok accepted_4096 (by simp [batch_81_21_values])
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

theorem leaf_4097_ok : checkAt 527 1000 box_4097 cert_4097 = true := by
  have h := List.all_eq_true.mp batch_81_22_ok accepted_4097 (by simp [batch_81_22_values])
  exact h
theorem leaf_4097_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4097.profileLo box_4097.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4097_ok
theorem branch_box_4097_nonnegative : ∀ j, 0 ≤ branch_box_4097.lower j ∧ 0 ≤ branch_box_4097.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4097, Box.profileLo, Box.profileHi, box_4097]
theorem leaf_4097_BranchSafe : CertificateConsequences.BranchSafe branch_box_4097 := by
  left; refine ⟨branch_box_4097_nonnegative, ?_⟩
  intro z hz; exact leaf_4097_sound hz

theorem leaf_4099_ok : checkAt 527 1000 box_4099 cert_4099 = true := by
  have h := List.all_eq_true.mp batch_81_23_ok accepted_4099 (by simp [batch_81_23_values])
  exact h
theorem leaf_4099_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4099.profileLo box_4099.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4099_ok
theorem branch_box_4099_nonnegative : ∀ j, 0 ≤ branch_box_4099.lower j ∧ 0 ≤ branch_box_4099.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4099, Box.profileLo, Box.profileHi, box_4099]
theorem leaf_4099_BranchSafe : CertificateConsequences.BranchSafe branch_box_4099 := by
  left; refine ⟨branch_box_4099_nonnegative, ?_⟩
  intro z hz; exact leaf_4099_sound hz

#print axioms batch_81_00_ok
#print axioms leaf_4052_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
