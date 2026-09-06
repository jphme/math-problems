import PeaceableQueens.UpperBound.Generated.Even.C527Scaled130Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_130_00_values : List Bool := [accepted_6500]
theorem batch_130_00_ok : batch_130_00_values.all id = true := by decide

def batch_130_01_values : List Bool := [accepted_6501]
theorem batch_130_01_ok : batch_130_01_values.all id = true := by decide

def batch_130_02_values : List Bool := [accepted_6502]
theorem batch_130_02_ok : batch_130_02_values.all id = true := by decide

def batch_130_03_values : List Bool := [accepted_6507]
theorem batch_130_03_ok : batch_130_03_values.all id = true := by decide

def batch_130_04_values : List Bool := [accepted_6511]
theorem batch_130_04_ok : batch_130_04_values.all id = true := by decide

def batch_130_05_values : List Bool := [accepted_6514]
theorem batch_130_05_ok : batch_130_05_values.all id = true := by decide

def batch_130_06_values : List Bool := [accepted_6515]
theorem batch_130_06_ok : batch_130_06_values.all id = true := by decide

def batch_130_07_values : List Bool := [accepted_6516]
theorem batch_130_07_ok : batch_130_07_values.all id = true := by decide

def batch_130_08_values : List Bool := [accepted_6517]
theorem batch_130_08_ok : batch_130_08_values.all id = true := by decide

def batch_130_09_values : List Bool := [accepted_6518]
theorem batch_130_09_ok : batch_130_09_values.all id = true := by decide

def batch_130_10_values : List Bool := [accepted_6519]
theorem batch_130_10_ok : batch_130_10_values.all id = true := by decide

def batch_130_11_values : List Bool := [accepted_6521]
theorem batch_130_11_ok : batch_130_11_values.all id = true := by decide

def batch_130_12_values : List Bool := [accepted_6523]
theorem batch_130_12_ok : batch_130_12_values.all id = true := by decide

def batch_130_13_values : List Bool := [accepted_6527]
theorem batch_130_13_ok : batch_130_13_values.all id = true := by decide

def batch_130_14_values : List Bool := [accepted_6528]
theorem batch_130_14_ok : batch_130_14_values.all id = true := by decide

def batch_130_15_values : List Bool := [accepted_6529]
theorem batch_130_15_ok : batch_130_15_values.all id = true := by decide

def batch_130_16_values : List Bool := [accepted_6530]
theorem batch_130_16_ok : batch_130_16_values.all id = true := by decide

def batch_130_17_values : List Bool := [accepted_6533]
theorem batch_130_17_ok : batch_130_17_values.all id = true := by decide

def batch_130_18_values : List Bool := [accepted_6535]
theorem batch_130_18_ok : batch_130_18_values.all id = true := by decide

def batch_130_19_values : List Bool := [accepted_6541]
theorem batch_130_19_ok : batch_130_19_values.all id = true := by decide

def batch_130_20_values : List Bool := [accepted_6542]
theorem batch_130_20_ok : batch_130_20_values.all id = true := by decide

def batch_130_21_values : List Bool := [accepted_6547]
theorem batch_130_21_ok : batch_130_21_values.all id = true := by decide

theorem leaf_6500_ok : checkAt 527 1000 box_6500 cert_6500 = true := by
  have h := List.all_eq_true.mp batch_130_00_ok accepted_6500 (by simp [batch_130_00_values])
  exact h
theorem leaf_6500_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6500.profileLo box_6500.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6500_ok
theorem branch_box_6500_nonnegative : ∀ j, 0 ≤ branch_box_6500.lower j ∧ 0 ≤ branch_box_6500.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6500, Box.profileLo, Box.profileHi, box_6500]
theorem leaf_6500_BranchSafe : CertificateConsequences.BranchSafe branch_box_6500 := by
  left; refine ⟨branch_box_6500_nonnegative, ?_⟩
  intro z hz; exact leaf_6500_sound hz

theorem leaf_6501_ok : checkAt 527 1000 box_6501 cert_6501 = true := by
  have h := List.all_eq_true.mp batch_130_01_ok accepted_6501 (by simp [batch_130_01_values])
  exact h
theorem leaf_6501_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6501.profileLo box_6501.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6501_ok
theorem branch_box_6501_nonnegative : ∀ j, 0 ≤ branch_box_6501.lower j ∧ 0 ≤ branch_box_6501.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6501, Box.profileLo, Box.profileHi, box_6501]
theorem leaf_6501_BranchSafe : CertificateConsequences.BranchSafe branch_box_6501 := by
  left; refine ⟨branch_box_6501_nonnegative, ?_⟩
  intro z hz; exact leaf_6501_sound hz

theorem leaf_6502_ok : checkAt 527 1000 box_6502 cert_6502 = true := by
  have h := List.all_eq_true.mp batch_130_02_ok accepted_6502 (by simp [batch_130_02_values])
  exact h
theorem leaf_6502_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6502.profileLo box_6502.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6502_ok
theorem branch_box_6502_nonnegative : ∀ j, 0 ≤ branch_box_6502.lower j ∧ 0 ≤ branch_box_6502.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6502, Box.profileLo, Box.profileHi, box_6502]
theorem leaf_6502_BranchSafe : CertificateConsequences.BranchSafe branch_box_6502 := by
  left; refine ⟨branch_box_6502_nonnegative, ?_⟩
  intro z hz; exact leaf_6502_sound hz

theorem leaf_6507_ok : checkAt 527 1000 box_6507 cert_6507 = true := by
  have h := List.all_eq_true.mp batch_130_03_ok accepted_6507 (by simp [batch_130_03_values])
  exact h
theorem leaf_6507_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6507.profileLo box_6507.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6507_ok
theorem branch_box_6507_nonnegative : ∀ j, 0 ≤ branch_box_6507.lower j ∧ 0 ≤ branch_box_6507.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6507, Box.profileLo, Box.profileHi, box_6507]
theorem leaf_6507_BranchSafe : CertificateConsequences.BranchSafe branch_box_6507 := by
  left; refine ⟨branch_box_6507_nonnegative, ?_⟩
  intro z hz; exact leaf_6507_sound hz

theorem leaf_6511_ok : checkAt 527 1000 box_6511 cert_6511 = true := by
  have h := List.all_eq_true.mp batch_130_04_ok accepted_6511 (by simp [batch_130_04_values])
  exact h
theorem leaf_6511_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6511.profileLo box_6511.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6511_ok
theorem branch_box_6511_nonnegative : ∀ j, 0 ≤ branch_box_6511.lower j ∧ 0 ≤ branch_box_6511.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6511, Box.profileLo, Box.profileHi, box_6511]
theorem leaf_6511_BranchSafe : CertificateConsequences.BranchSafe branch_box_6511 := by
  left; refine ⟨branch_box_6511_nonnegative, ?_⟩
  intro z hz; exact leaf_6511_sound hz

theorem leaf_6514_ok : checkAt 527 1000 box_6514 cert_6514 = true := by
  have h := List.all_eq_true.mp batch_130_05_ok accepted_6514 (by simp [batch_130_05_values])
  exact h
theorem leaf_6514_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6514.profileLo box_6514.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6514_ok
theorem branch_box_6514_nonnegative : ∀ j, 0 ≤ branch_box_6514.lower j ∧ 0 ≤ branch_box_6514.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6514, Box.profileLo, Box.profileHi, box_6514]
theorem leaf_6514_BranchSafe : CertificateConsequences.BranchSafe branch_box_6514 := by
  left; refine ⟨branch_box_6514_nonnegative, ?_⟩
  intro z hz; exact leaf_6514_sound hz

theorem leaf_6515_ok : checkAt 527 1000 box_6515 cert_6515 = true := by
  have h := List.all_eq_true.mp batch_130_06_ok accepted_6515 (by simp [batch_130_06_values])
  exact h
theorem leaf_6515_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6515.profileLo box_6515.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6515_ok
theorem branch_box_6515_nonnegative : ∀ j, 0 ≤ branch_box_6515.lower j ∧ 0 ≤ branch_box_6515.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6515, Box.profileLo, Box.profileHi, box_6515]
theorem leaf_6515_BranchSafe : CertificateConsequences.BranchSafe branch_box_6515 := by
  left; refine ⟨branch_box_6515_nonnegative, ?_⟩
  intro z hz; exact leaf_6515_sound hz

theorem leaf_6516_ok : checkAt 527 1000 box_6516 cert_6516 = true := by
  have h := List.all_eq_true.mp batch_130_07_ok accepted_6516 (by simp [batch_130_07_values])
  exact h
theorem leaf_6516_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6516.profileLo box_6516.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6516_ok
theorem branch_box_6516_nonnegative : ∀ j, 0 ≤ branch_box_6516.lower j ∧ 0 ≤ branch_box_6516.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6516, Box.profileLo, Box.profileHi, box_6516]
theorem leaf_6516_BranchSafe : CertificateConsequences.BranchSafe branch_box_6516 := by
  left; refine ⟨branch_box_6516_nonnegative, ?_⟩
  intro z hz; exact leaf_6516_sound hz

theorem leaf_6517_ok : checkAt 527 1000 box_6517 cert_6517 = true := by
  have h := List.all_eq_true.mp batch_130_08_ok accepted_6517 (by simp [batch_130_08_values])
  exact h
theorem leaf_6517_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6517.profileLo box_6517.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6517_ok
theorem branch_box_6517_nonnegative : ∀ j, 0 ≤ branch_box_6517.lower j ∧ 0 ≤ branch_box_6517.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6517, Box.profileLo, Box.profileHi, box_6517]
theorem leaf_6517_BranchSafe : CertificateConsequences.BranchSafe branch_box_6517 := by
  left; refine ⟨branch_box_6517_nonnegative, ?_⟩
  intro z hz; exact leaf_6517_sound hz

theorem leaf_6518_ok : checkAt 527 1000 box_6518 cert_6518 = true := by
  have h := List.all_eq_true.mp batch_130_09_ok accepted_6518 (by simp [batch_130_09_values])
  exact h
theorem leaf_6518_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6518.profileLo box_6518.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6518_ok
theorem branch_box_6518_nonnegative : ∀ j, 0 ≤ branch_box_6518.lower j ∧ 0 ≤ branch_box_6518.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6518, Box.profileLo, Box.profileHi, box_6518]
theorem leaf_6518_BranchSafe : CertificateConsequences.BranchSafe branch_box_6518 := by
  left; refine ⟨branch_box_6518_nonnegative, ?_⟩
  intro z hz; exact leaf_6518_sound hz

theorem leaf_6519_ok : checkAt 527 1000 box_6519 cert_6519 = true := by
  have h := List.all_eq_true.mp batch_130_10_ok accepted_6519 (by simp [batch_130_10_values])
  exact h
theorem leaf_6519_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6519.profileLo box_6519.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6519_ok
theorem branch_box_6519_nonnegative : ∀ j, 0 ≤ branch_box_6519.lower j ∧ 0 ≤ branch_box_6519.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6519, Box.profileLo, Box.profileHi, box_6519]
theorem leaf_6519_BranchSafe : CertificateConsequences.BranchSafe branch_box_6519 := by
  left; refine ⟨branch_box_6519_nonnegative, ?_⟩
  intro z hz; exact leaf_6519_sound hz

theorem leaf_6521_ok : checkAt 527 1000 box_6521 cert_6521 = true := by
  have h := List.all_eq_true.mp batch_130_11_ok accepted_6521 (by simp [batch_130_11_values])
  exact h
theorem leaf_6521_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6521.profileLo box_6521.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6521_ok
theorem branch_box_6521_nonnegative : ∀ j, 0 ≤ branch_box_6521.lower j ∧ 0 ≤ branch_box_6521.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6521, Box.profileLo, Box.profileHi, box_6521]
theorem leaf_6521_BranchSafe : CertificateConsequences.BranchSafe branch_box_6521 := by
  left; refine ⟨branch_box_6521_nonnegative, ?_⟩
  intro z hz; exact leaf_6521_sound hz

theorem leaf_6523_ok : checkAt 527 1000 box_6523 cert_6523 = true := by
  have h := List.all_eq_true.mp batch_130_12_ok accepted_6523 (by simp [batch_130_12_values])
  exact h
theorem leaf_6523_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6523.profileLo box_6523.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6523_ok
theorem branch_box_6523_nonnegative : ∀ j, 0 ≤ branch_box_6523.lower j ∧ 0 ≤ branch_box_6523.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6523, Box.profileLo, Box.profileHi, box_6523]
theorem leaf_6523_BranchSafe : CertificateConsequences.BranchSafe branch_box_6523 := by
  left; refine ⟨branch_box_6523_nonnegative, ?_⟩
  intro z hz; exact leaf_6523_sound hz

theorem leaf_6527_ok : checkAt 527 1000 box_6527 cert_6527 = true := by
  have h := List.all_eq_true.mp batch_130_13_ok accepted_6527 (by simp [batch_130_13_values])
  exact h
theorem leaf_6527_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6527.profileLo box_6527.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6527_ok
theorem branch_box_6527_nonnegative : ∀ j, 0 ≤ branch_box_6527.lower j ∧ 0 ≤ branch_box_6527.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6527, Box.profileLo, Box.profileHi, box_6527]
theorem leaf_6527_BranchSafe : CertificateConsequences.BranchSafe branch_box_6527 := by
  left; refine ⟨branch_box_6527_nonnegative, ?_⟩
  intro z hz; exact leaf_6527_sound hz

theorem leaf_6528_ok : checkAt 527 1000 box_6528 cert_6528 = true := by
  have h := List.all_eq_true.mp batch_130_14_ok accepted_6528 (by simp [batch_130_14_values])
  exact h
theorem leaf_6528_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6528.profileLo box_6528.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6528_ok
theorem branch_box_6528_nonnegative : ∀ j, 0 ≤ branch_box_6528.lower j ∧ 0 ≤ branch_box_6528.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6528, Box.profileLo, Box.profileHi, box_6528]
theorem leaf_6528_BranchSafe : CertificateConsequences.BranchSafe branch_box_6528 := by
  left; refine ⟨branch_box_6528_nonnegative, ?_⟩
  intro z hz; exact leaf_6528_sound hz

theorem leaf_6529_ok : checkAt 527 1000 box_6529 cert_6529 = true := by
  have h := List.all_eq_true.mp batch_130_15_ok accepted_6529 (by simp [batch_130_15_values])
  exact h
theorem leaf_6529_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6529.profileLo box_6529.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6529_ok
theorem branch_box_6529_nonnegative : ∀ j, 0 ≤ branch_box_6529.lower j ∧ 0 ≤ branch_box_6529.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6529, Box.profileLo, Box.profileHi, box_6529]
theorem leaf_6529_BranchSafe : CertificateConsequences.BranchSafe branch_box_6529 := by
  left; refine ⟨branch_box_6529_nonnegative, ?_⟩
  intro z hz; exact leaf_6529_sound hz

theorem leaf_6530_ok : checkAt 527 1000 box_6530 cert_6530 = true := by
  have h := List.all_eq_true.mp batch_130_16_ok accepted_6530 (by simp [batch_130_16_values])
  exact h
theorem leaf_6530_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6530.profileLo box_6530.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6530_ok
theorem branch_box_6530_nonnegative : ∀ j, 0 ≤ branch_box_6530.lower j ∧ 0 ≤ branch_box_6530.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6530, Box.profileLo, Box.profileHi, box_6530]
theorem leaf_6530_BranchSafe : CertificateConsequences.BranchSafe branch_box_6530 := by
  left; refine ⟨branch_box_6530_nonnegative, ?_⟩
  intro z hz; exact leaf_6530_sound hz

theorem leaf_6533_ok : checkAt 527 1000 box_6533 cert_6533 = true := by
  have h := List.all_eq_true.mp batch_130_17_ok accepted_6533 (by simp [batch_130_17_values])
  exact h
theorem leaf_6533_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6533.profileLo box_6533.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6533_ok
theorem branch_box_6533_nonnegative : ∀ j, 0 ≤ branch_box_6533.lower j ∧ 0 ≤ branch_box_6533.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6533, Box.profileLo, Box.profileHi, box_6533]
theorem leaf_6533_BranchSafe : CertificateConsequences.BranchSafe branch_box_6533 := by
  left; refine ⟨branch_box_6533_nonnegative, ?_⟩
  intro z hz; exact leaf_6533_sound hz

theorem leaf_6535_ok : checkAt 527 1000 box_6535 cert_6535 = true := by
  have h := List.all_eq_true.mp batch_130_18_ok accepted_6535 (by simp [batch_130_18_values])
  exact h
theorem leaf_6535_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6535.profileLo box_6535.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6535_ok
theorem branch_box_6535_nonnegative : ∀ j, 0 ≤ branch_box_6535.lower j ∧ 0 ≤ branch_box_6535.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6535, Box.profileLo, Box.profileHi, box_6535]
theorem leaf_6535_BranchSafe : CertificateConsequences.BranchSafe branch_box_6535 := by
  left; refine ⟨branch_box_6535_nonnegative, ?_⟩
  intro z hz; exact leaf_6535_sound hz

theorem leaf_6541_ok : checkAt 527 1000 box_6541 cert_6541 = true := by
  have h := List.all_eq_true.mp batch_130_19_ok accepted_6541 (by simp [batch_130_19_values])
  exact h
theorem leaf_6541_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6541.profileLo box_6541.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6541_ok
theorem branch_box_6541_nonnegative : ∀ j, 0 ≤ branch_box_6541.lower j ∧ 0 ≤ branch_box_6541.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6541, Box.profileLo, Box.profileHi, box_6541]
theorem leaf_6541_BranchSafe : CertificateConsequences.BranchSafe branch_box_6541 := by
  left; refine ⟨branch_box_6541_nonnegative, ?_⟩
  intro z hz; exact leaf_6541_sound hz

theorem leaf_6542_ok : checkAt 527 1000 box_6542 cert_6542 = true := by
  have h := List.all_eq_true.mp batch_130_20_ok accepted_6542 (by simp [batch_130_20_values])
  exact h
theorem leaf_6542_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6542.profileLo box_6542.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6542_ok
theorem branch_box_6542_nonnegative : ∀ j, 0 ≤ branch_box_6542.lower j ∧ 0 ≤ branch_box_6542.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6542, Box.profileLo, Box.profileHi, box_6542]
theorem leaf_6542_BranchSafe : CertificateConsequences.BranchSafe branch_box_6542 := by
  left; refine ⟨branch_box_6542_nonnegative, ?_⟩
  intro z hz; exact leaf_6542_sound hz

theorem leaf_6547_ok : checkAt 527 1000 box_6547 cert_6547 = true := by
  have h := List.all_eq_true.mp batch_130_21_ok accepted_6547 (by simp [batch_130_21_values])
  exact h
theorem leaf_6547_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6547.profileLo box_6547.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6547_ok
theorem branch_box_6547_nonnegative : ∀ j, 0 ≤ branch_box_6547.lower j ∧ 0 ≤ branch_box_6547.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6547, Box.profileLo, Box.profileHi, box_6547]
theorem leaf_6547_BranchSafe : CertificateConsequences.BranchSafe branch_box_6547 := by
  left; refine ⟨branch_box_6547_nonnegative, ?_⟩
  intro z hz; exact leaf_6547_sound hz

#print axioms batch_130_00_ok
#print axioms leaf_6500_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
