import PeaceableQueens.UpperBound.Generated.Even.C527Scaled85Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_85_00_values : List Bool := [accepted_4255]
theorem batch_85_00_ok : batch_85_00_values.all id = true := by decide

def batch_85_01_values : List Bool := [accepted_4256]
theorem batch_85_01_ok : batch_85_01_values.all id = true := by decide

def batch_85_02_values : List Bool := [accepted_4261]
theorem batch_85_02_ok : batch_85_02_values.all id = true := by decide

def batch_85_03_values : List Bool := [accepted_4262]
theorem batch_85_03_ok : batch_85_03_values.all id = true := by decide

def batch_85_04_values : List Bool := [accepted_4263]
theorem batch_85_04_ok : batch_85_04_values.all id = true := by decide

def batch_85_05_values : List Bool := [accepted_4264]
theorem batch_85_05_ok : batch_85_05_values.all id = true := by decide

def batch_85_06_values : List Bool := [accepted_4265]
theorem batch_85_06_ok : batch_85_06_values.all id = true := by decide

def batch_85_07_values : List Bool := [accepted_4266]
theorem batch_85_07_ok : batch_85_07_values.all id = true := by decide

def batch_85_08_values : List Bool := [accepted_4271]
theorem batch_85_08_ok : batch_85_08_values.all id = true := by decide

def batch_85_09_values : List Bool := [accepted_4273]
theorem batch_85_09_ok : batch_85_09_values.all id = true := by decide

def batch_85_10_values : List Bool := [accepted_4274]
theorem batch_85_10_ok : batch_85_10_values.all id = true := by decide

def batch_85_11_values : List Bool := [accepted_4275]
theorem batch_85_11_ok : batch_85_11_values.all id = true := by decide

def batch_85_12_values : List Bool := [accepted_4277]
theorem batch_85_12_ok : batch_85_12_values.all id = true := by decide

def batch_85_13_values : List Bool := [accepted_4278]
theorem batch_85_13_ok : batch_85_13_values.all id = true := by decide

def batch_85_14_values : List Bool := [accepted_4282]
theorem batch_85_14_ok : batch_85_14_values.all id = true := by decide

def batch_85_15_values : List Bool := [accepted_4284]
theorem batch_85_15_ok : batch_85_15_values.all id = true := by decide

def batch_85_16_values : List Bool := [accepted_4287]
theorem batch_85_16_ok : batch_85_16_values.all id = true := by decide

def batch_85_17_values : List Bool := [accepted_4288]
theorem batch_85_17_ok : batch_85_17_values.all id = true := by decide

def batch_85_18_values : List Bool := [accepted_4289]
theorem batch_85_18_ok : batch_85_18_values.all id = true := by decide

def batch_85_19_values : List Bool := [accepted_4290]
theorem batch_85_19_ok : batch_85_19_values.all id = true := by decide

def batch_85_20_values : List Bool := [accepted_4295]
theorem batch_85_20_ok : batch_85_20_values.all id = true := by decide

def batch_85_21_values : List Bool := [accepted_4296]
theorem batch_85_21_ok : batch_85_21_values.all id = true := by decide

def batch_85_22_values : List Bool := [accepted_4297]
theorem batch_85_22_ok : batch_85_22_values.all id = true := by decide

def batch_85_23_values : List Bool := [accepted_4298]
theorem batch_85_23_ok : batch_85_23_values.all id = true := by decide

theorem leaf_4255_ok : checkAt 527 1000 box_4255 cert_4255 = true := by
  have h := List.all_eq_true.mp batch_85_00_ok accepted_4255 (by simp [batch_85_00_values])
  exact h
theorem leaf_4255_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4255.profileLo box_4255.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4255_ok
theorem branch_box_4255_nonnegative : ∀ j, 0 ≤ branch_box_4255.lower j ∧ 0 ≤ branch_box_4255.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4255, Box.profileLo, Box.profileHi, box_4255]
theorem leaf_4255_BranchSafe : CertificateConsequences.BranchSafe branch_box_4255 := by
  left; refine ⟨branch_box_4255_nonnegative, ?_⟩
  intro z hz; exact leaf_4255_sound hz

theorem leaf_4256_ok : checkAt 527 1000 box_4256 cert_4256 = true := by
  have h := List.all_eq_true.mp batch_85_01_ok accepted_4256 (by simp [batch_85_01_values])
  exact h
theorem leaf_4256_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4256.profileLo box_4256.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4256_ok
theorem branch_box_4256_nonnegative : ∀ j, 0 ≤ branch_box_4256.lower j ∧ 0 ≤ branch_box_4256.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4256, Box.profileLo, Box.profileHi, box_4256]
theorem leaf_4256_BranchSafe : CertificateConsequences.BranchSafe branch_box_4256 := by
  left; refine ⟨branch_box_4256_nonnegative, ?_⟩
  intro z hz; exact leaf_4256_sound hz

theorem leaf_4261_ok : checkAt 527 1000 box_4261 cert_4261 = true := by
  have h := List.all_eq_true.mp batch_85_02_ok accepted_4261 (by simp [batch_85_02_values])
  exact h
theorem leaf_4261_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4261.profileLo box_4261.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4261_ok
theorem branch_box_4261_nonnegative : ∀ j, 0 ≤ branch_box_4261.lower j ∧ 0 ≤ branch_box_4261.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4261, Box.profileLo, Box.profileHi, box_4261]
theorem leaf_4261_BranchSafe : CertificateConsequences.BranchSafe branch_box_4261 := by
  left; refine ⟨branch_box_4261_nonnegative, ?_⟩
  intro z hz; exact leaf_4261_sound hz

theorem leaf_4262_ok : checkAt 527 1000 box_4262 cert_4262 = true := by
  have h := List.all_eq_true.mp batch_85_03_ok accepted_4262 (by simp [batch_85_03_values])
  exact h
theorem leaf_4262_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4262.profileLo box_4262.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4262_ok
theorem branch_box_4262_nonnegative : ∀ j, 0 ≤ branch_box_4262.lower j ∧ 0 ≤ branch_box_4262.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4262, Box.profileLo, Box.profileHi, box_4262]
theorem leaf_4262_BranchSafe : CertificateConsequences.BranchSafe branch_box_4262 := by
  left; refine ⟨branch_box_4262_nonnegative, ?_⟩
  intro z hz; exact leaf_4262_sound hz

theorem leaf_4263_ok : checkAt 527 1000 box_4263 cert_4263 = true := by
  have h := List.all_eq_true.mp batch_85_04_ok accepted_4263 (by simp [batch_85_04_values])
  exact h
theorem leaf_4263_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4263.profileLo box_4263.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4263_ok
theorem branch_box_4263_nonnegative : ∀ j, 0 ≤ branch_box_4263.lower j ∧ 0 ≤ branch_box_4263.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4263, Box.profileLo, Box.profileHi, box_4263]
theorem leaf_4263_BranchSafe : CertificateConsequences.BranchSafe branch_box_4263 := by
  left; refine ⟨branch_box_4263_nonnegative, ?_⟩
  intro z hz; exact leaf_4263_sound hz

theorem leaf_4264_ok : checkAt 527 1000 box_4264 cert_4264 = true := by
  have h := List.all_eq_true.mp batch_85_05_ok accepted_4264 (by simp [batch_85_05_values])
  exact h
theorem leaf_4264_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4264.profileLo box_4264.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4264_ok
theorem branch_box_4264_nonnegative : ∀ j, 0 ≤ branch_box_4264.lower j ∧ 0 ≤ branch_box_4264.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4264, Box.profileLo, Box.profileHi, box_4264]
theorem leaf_4264_BranchSafe : CertificateConsequences.BranchSafe branch_box_4264 := by
  left; refine ⟨branch_box_4264_nonnegative, ?_⟩
  intro z hz; exact leaf_4264_sound hz

theorem leaf_4265_ok : checkAt 527 1000 box_4265 cert_4265 = true := by
  have h := List.all_eq_true.mp batch_85_06_ok accepted_4265 (by simp [batch_85_06_values])
  exact h
theorem leaf_4265_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4265.profileLo box_4265.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4265_ok
theorem branch_box_4265_nonnegative : ∀ j, 0 ≤ branch_box_4265.lower j ∧ 0 ≤ branch_box_4265.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4265, Box.profileLo, Box.profileHi, box_4265]
theorem leaf_4265_BranchSafe : CertificateConsequences.BranchSafe branch_box_4265 := by
  left; refine ⟨branch_box_4265_nonnegative, ?_⟩
  intro z hz; exact leaf_4265_sound hz

theorem leaf_4266_ok : checkAt 527 1000 box_4266 cert_4266 = true := by
  have h := List.all_eq_true.mp batch_85_07_ok accepted_4266 (by simp [batch_85_07_values])
  exact h
theorem leaf_4266_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4266.profileLo box_4266.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4266_ok
theorem branch_box_4266_nonnegative : ∀ j, 0 ≤ branch_box_4266.lower j ∧ 0 ≤ branch_box_4266.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4266, Box.profileLo, Box.profileHi, box_4266]
theorem leaf_4266_BranchSafe : CertificateConsequences.BranchSafe branch_box_4266 := by
  left; refine ⟨branch_box_4266_nonnegative, ?_⟩
  intro z hz; exact leaf_4266_sound hz

theorem leaf_4271_ok : checkAt 527 1000 box_4271 cert_4271 = true := by
  have h := List.all_eq_true.mp batch_85_08_ok accepted_4271 (by simp [batch_85_08_values])
  exact h
theorem leaf_4271_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4271.profileLo box_4271.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4271_ok
theorem branch_box_4271_nonnegative : ∀ j, 0 ≤ branch_box_4271.lower j ∧ 0 ≤ branch_box_4271.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4271, Box.profileLo, Box.profileHi, box_4271]
theorem leaf_4271_BranchSafe : CertificateConsequences.BranchSafe branch_box_4271 := by
  left; refine ⟨branch_box_4271_nonnegative, ?_⟩
  intro z hz; exact leaf_4271_sound hz

theorem leaf_4273_ok : checkAt 527 1000 box_4273 cert_4273 = true := by
  have h := List.all_eq_true.mp batch_85_09_ok accepted_4273 (by simp [batch_85_09_values])
  exact h
theorem leaf_4273_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4273.profileLo box_4273.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4273_ok
theorem branch_box_4273_nonnegative : ∀ j, 0 ≤ branch_box_4273.lower j ∧ 0 ≤ branch_box_4273.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4273, Box.profileLo, Box.profileHi, box_4273]
theorem leaf_4273_BranchSafe : CertificateConsequences.BranchSafe branch_box_4273 := by
  left; refine ⟨branch_box_4273_nonnegative, ?_⟩
  intro z hz; exact leaf_4273_sound hz

theorem leaf_4274_ok : checkAt 527 1000 box_4274 cert_4274 = true := by
  have h := List.all_eq_true.mp batch_85_10_ok accepted_4274 (by simp [batch_85_10_values])
  exact h
theorem leaf_4274_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4274.profileLo box_4274.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4274_ok
theorem branch_box_4274_nonnegative : ∀ j, 0 ≤ branch_box_4274.lower j ∧ 0 ≤ branch_box_4274.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4274, Box.profileLo, Box.profileHi, box_4274]
theorem leaf_4274_BranchSafe : CertificateConsequences.BranchSafe branch_box_4274 := by
  left; refine ⟨branch_box_4274_nonnegative, ?_⟩
  intro z hz; exact leaf_4274_sound hz

theorem leaf_4275_ok : checkAt 527 1000 box_4275 cert_4275 = true := by
  have h := List.all_eq_true.mp batch_85_11_ok accepted_4275 (by simp [batch_85_11_values])
  exact h
theorem leaf_4275_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4275.profileLo box_4275.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4275_ok
theorem branch_box_4275_nonnegative : ∀ j, 0 ≤ branch_box_4275.lower j ∧ 0 ≤ branch_box_4275.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4275, Box.profileLo, Box.profileHi, box_4275]
theorem leaf_4275_BranchSafe : CertificateConsequences.BranchSafe branch_box_4275 := by
  left; refine ⟨branch_box_4275_nonnegative, ?_⟩
  intro z hz; exact leaf_4275_sound hz

theorem leaf_4277_ok : checkAt 527 1000 box_4277 cert_4277 = true := by
  have h := List.all_eq_true.mp batch_85_12_ok accepted_4277 (by simp [batch_85_12_values])
  exact h
theorem leaf_4277_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4277.profileLo box_4277.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4277_ok
theorem branch_box_4277_nonnegative : ∀ j, 0 ≤ branch_box_4277.lower j ∧ 0 ≤ branch_box_4277.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4277, Box.profileLo, Box.profileHi, box_4277]
theorem leaf_4277_BranchSafe : CertificateConsequences.BranchSafe branch_box_4277 := by
  left; refine ⟨branch_box_4277_nonnegative, ?_⟩
  intro z hz; exact leaf_4277_sound hz

theorem leaf_4278_ok : checkAt 527 1000 box_4278 cert_4278 = true := by
  have h := List.all_eq_true.mp batch_85_13_ok accepted_4278 (by simp [batch_85_13_values])
  exact h
theorem leaf_4278_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4278.profileLo box_4278.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4278_ok
theorem branch_box_4278_nonnegative : ∀ j, 0 ≤ branch_box_4278.lower j ∧ 0 ≤ branch_box_4278.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4278, Box.profileLo, Box.profileHi, box_4278]
theorem leaf_4278_BranchSafe : CertificateConsequences.BranchSafe branch_box_4278 := by
  left; refine ⟨branch_box_4278_nonnegative, ?_⟩
  intro z hz; exact leaf_4278_sound hz

theorem leaf_4282_ok : checkAt 527 1000 box_4282 cert_4282 = true := by
  have h := List.all_eq_true.mp batch_85_14_ok accepted_4282 (by simp [batch_85_14_values])
  exact h
theorem leaf_4282_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4282.profileLo box_4282.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4282_ok
theorem branch_box_4282_nonnegative : ∀ j, 0 ≤ branch_box_4282.lower j ∧ 0 ≤ branch_box_4282.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4282, Box.profileLo, Box.profileHi, box_4282]
theorem leaf_4282_BranchSafe : CertificateConsequences.BranchSafe branch_box_4282 := by
  left; refine ⟨branch_box_4282_nonnegative, ?_⟩
  intro z hz; exact leaf_4282_sound hz

theorem leaf_4284_ok : checkAt 527 1000 box_4284 cert_4284 = true := by
  have h := List.all_eq_true.mp batch_85_15_ok accepted_4284 (by simp [batch_85_15_values])
  exact h
theorem leaf_4284_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4284.profileLo box_4284.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4284_ok
theorem branch_box_4284_nonnegative : ∀ j, 0 ≤ branch_box_4284.lower j ∧ 0 ≤ branch_box_4284.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4284, Box.profileLo, Box.profileHi, box_4284]
theorem leaf_4284_BranchSafe : CertificateConsequences.BranchSafe branch_box_4284 := by
  left; refine ⟨branch_box_4284_nonnegative, ?_⟩
  intro z hz; exact leaf_4284_sound hz

theorem leaf_4287_ok : checkAt 527 1000 box_4287 cert_4287 = true := by
  have h := List.all_eq_true.mp batch_85_16_ok accepted_4287 (by simp [batch_85_16_values])
  exact h
theorem leaf_4287_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4287.profileLo box_4287.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4287_ok
theorem branch_box_4287_nonnegative : ∀ j, 0 ≤ branch_box_4287.lower j ∧ 0 ≤ branch_box_4287.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4287, Box.profileLo, Box.profileHi, box_4287]
theorem leaf_4287_BranchSafe : CertificateConsequences.BranchSafe branch_box_4287 := by
  left; refine ⟨branch_box_4287_nonnegative, ?_⟩
  intro z hz; exact leaf_4287_sound hz

theorem leaf_4288_ok : checkAt 527 1000 box_4288 cert_4288 = true := by
  have h := List.all_eq_true.mp batch_85_17_ok accepted_4288 (by simp [batch_85_17_values])
  exact h
theorem leaf_4288_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4288.profileLo box_4288.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4288_ok
theorem branch_box_4288_nonnegative : ∀ j, 0 ≤ branch_box_4288.lower j ∧ 0 ≤ branch_box_4288.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4288, Box.profileLo, Box.profileHi, box_4288]
theorem leaf_4288_BranchSafe : CertificateConsequences.BranchSafe branch_box_4288 := by
  left; refine ⟨branch_box_4288_nonnegative, ?_⟩
  intro z hz; exact leaf_4288_sound hz

theorem leaf_4289_ok : checkAt 527 1000 box_4289 cert_4289 = true := by
  have h := List.all_eq_true.mp batch_85_18_ok accepted_4289 (by simp [batch_85_18_values])
  exact h
theorem leaf_4289_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4289.profileLo box_4289.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4289_ok
theorem branch_box_4289_nonnegative : ∀ j, 0 ≤ branch_box_4289.lower j ∧ 0 ≤ branch_box_4289.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4289, Box.profileLo, Box.profileHi, box_4289]
theorem leaf_4289_BranchSafe : CertificateConsequences.BranchSafe branch_box_4289 := by
  left; refine ⟨branch_box_4289_nonnegative, ?_⟩
  intro z hz; exact leaf_4289_sound hz

theorem leaf_4290_ok : checkAt 527 1000 box_4290 cert_4290 = true := by
  have h := List.all_eq_true.mp batch_85_19_ok accepted_4290 (by simp [batch_85_19_values])
  exact h
theorem leaf_4290_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4290.profileLo box_4290.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4290_ok
theorem branch_box_4290_nonnegative : ∀ j, 0 ≤ branch_box_4290.lower j ∧ 0 ≤ branch_box_4290.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4290, Box.profileLo, Box.profileHi, box_4290]
theorem leaf_4290_BranchSafe : CertificateConsequences.BranchSafe branch_box_4290 := by
  left; refine ⟨branch_box_4290_nonnegative, ?_⟩
  intro z hz; exact leaf_4290_sound hz

theorem leaf_4295_ok : checkAt 527 1000 box_4295 cert_4295 = true := by
  have h := List.all_eq_true.mp batch_85_20_ok accepted_4295 (by simp [batch_85_20_values])
  exact h
theorem leaf_4295_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4295.profileLo box_4295.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4295_ok
theorem branch_box_4295_nonnegative : ∀ j, 0 ≤ branch_box_4295.lower j ∧ 0 ≤ branch_box_4295.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4295, Box.profileLo, Box.profileHi, box_4295]
theorem leaf_4295_BranchSafe : CertificateConsequences.BranchSafe branch_box_4295 := by
  left; refine ⟨branch_box_4295_nonnegative, ?_⟩
  intro z hz; exact leaf_4295_sound hz

theorem leaf_4296_ok : checkAt 527 1000 box_4296 cert_4296 = true := by
  have h := List.all_eq_true.mp batch_85_21_ok accepted_4296 (by simp [batch_85_21_values])
  exact h
theorem leaf_4296_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4296.profileLo box_4296.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4296_ok
theorem branch_box_4296_nonnegative : ∀ j, 0 ≤ branch_box_4296.lower j ∧ 0 ≤ branch_box_4296.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4296, Box.profileLo, Box.profileHi, box_4296]
theorem leaf_4296_BranchSafe : CertificateConsequences.BranchSafe branch_box_4296 := by
  left; refine ⟨branch_box_4296_nonnegative, ?_⟩
  intro z hz; exact leaf_4296_sound hz

theorem leaf_4297_ok : checkAt 527 1000 box_4297 cert_4297 = true := by
  have h := List.all_eq_true.mp batch_85_22_ok accepted_4297 (by simp [batch_85_22_values])
  exact h
theorem leaf_4297_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4297.profileLo box_4297.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4297_ok
theorem branch_box_4297_nonnegative : ∀ j, 0 ≤ branch_box_4297.lower j ∧ 0 ≤ branch_box_4297.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4297, Box.profileLo, Box.profileHi, box_4297]
theorem leaf_4297_BranchSafe : CertificateConsequences.BranchSafe branch_box_4297 := by
  left; refine ⟨branch_box_4297_nonnegative, ?_⟩
  intro z hz; exact leaf_4297_sound hz

theorem leaf_4298_ok : checkAt 527 1000 box_4298 cert_4298 = true := by
  have h := List.all_eq_true.mp batch_85_23_ok accepted_4298 (by simp [batch_85_23_values])
  exact h
theorem leaf_4298_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4298.profileLo box_4298.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4298_ok
theorem branch_box_4298_nonnegative : ∀ j, 0 ≤ branch_box_4298.lower j ∧ 0 ≤ branch_box_4298.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4298, Box.profileLo, Box.profileHi, box_4298]
theorem leaf_4298_BranchSafe : CertificateConsequences.BranchSafe branch_box_4298 := by
  left; refine ⟨branch_box_4298_nonnegative, ?_⟩
  intro z hz; exact leaf_4298_sound hz

#print axioms batch_85_00_ok
#print axioms leaf_4255_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
