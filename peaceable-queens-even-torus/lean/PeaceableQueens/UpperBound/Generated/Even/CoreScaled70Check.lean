import PeaceableQueens.UpperBound.Generated.Even.CoreScaled70Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_70_00_values : List Bool := [accepted_3500]
theorem batch_70_00_ok : batch_70_00_values.all id = true := by decide

def batch_70_01_values : List Bool := [accepted_3501]
theorem batch_70_01_ok : batch_70_01_values.all id = true := by decide

def batch_70_02_values : List Bool := [accepted_3508]
theorem batch_70_02_ok : batch_70_02_values.all id = true := by decide

def batch_70_03_values : List Bool := [accepted_3510]
theorem batch_70_03_ok : batch_70_03_values.all id = true := by decide

def batch_70_04_values : List Bool := [accepted_3512]
theorem batch_70_04_ok : batch_70_04_values.all id = true := by decide

def batch_70_05_values : List Bool := [accepted_3514]
theorem batch_70_05_ok : batch_70_05_values.all id = true := by decide

def batch_70_06_values : List Bool := [accepted_3516]
theorem batch_70_06_ok : batch_70_06_values.all id = true := by decide

def batch_70_07_values : List Bool := [accepted_3518]
theorem batch_70_07_ok : batch_70_07_values.all id = true := by decide

def batch_70_08_values : List Bool := [accepted_3520]
theorem batch_70_08_ok : batch_70_08_values.all id = true := by decide

def batch_70_09_values : List Bool := [accepted_3521]
theorem batch_70_09_ok : batch_70_09_values.all id = true := by decide

def batch_70_10_values : List Bool := [accepted_3523]
theorem batch_70_10_ok : batch_70_10_values.all id = true := by decide

def batch_70_11_values : List Bool := [accepted_3527]
theorem batch_70_11_ok : batch_70_11_values.all id = true := by decide

def batch_70_12_values : List Bool := [accepted_3530]
theorem batch_70_12_ok : batch_70_12_values.all id = true := by decide

def batch_70_13_values : List Bool := [accepted_3532]
theorem batch_70_13_ok : batch_70_13_values.all id = true := by decide

def batch_70_14_values : List Bool := [accepted_3534]
theorem batch_70_14_ok : batch_70_14_values.all id = true := by decide

def batch_70_15_values : List Bool := [accepted_3535]
theorem batch_70_15_ok : batch_70_15_values.all id = true := by decide

def batch_70_16_values : List Bool := [accepted_3537]
theorem batch_70_16_ok : batch_70_16_values.all id = true := by decide

def batch_70_17_values : List Bool := [accepted_3539]
theorem batch_70_17_ok : batch_70_17_values.all id = true := by decide

def batch_70_18_values : List Bool := [accepted_3542]
theorem batch_70_18_ok : batch_70_18_values.all id = true := by decide

def batch_70_19_values : List Bool := [accepted_3544]
theorem batch_70_19_ok : batch_70_19_values.all id = true := by decide

def batch_70_20_values : List Bool := [accepted_3548]
theorem batch_70_20_ok : batch_70_20_values.all id = true := by decide

theorem leaf_3500_ok : checkAt 527 1000 box_3500 cert_3500 = true := by
  have h := List.all_eq_true.mp batch_70_00_ok accepted_3500 (by simp [batch_70_00_values])
  exact h
theorem leaf_3500_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3500.profileLo box_3500.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3500_ok
theorem branch_box_3500_nonnegative : ∀ j, 0 ≤ branch_box_3500.lower j ∧ 0 ≤ branch_box_3500.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3500, Box.profileLo, Box.profileHi, box_3500]
theorem leaf_3500_BranchSafe : CertificateConsequences.BranchSafe branch_box_3500 := by
  left; refine ⟨branch_box_3500_nonnegative, ?_⟩
  intro z hz; exact leaf_3500_sound hz

theorem leaf_3501_ok : checkAt 527 1000 box_3501 cert_3501 = true := by
  have h := List.all_eq_true.mp batch_70_01_ok accepted_3501 (by simp [batch_70_01_values])
  exact h
theorem leaf_3501_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3501.profileLo box_3501.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3501_ok
theorem branch_box_3501_nonnegative : ∀ j, 0 ≤ branch_box_3501.lower j ∧ 0 ≤ branch_box_3501.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3501, Box.profileLo, Box.profileHi, box_3501]
theorem leaf_3501_BranchSafe : CertificateConsequences.BranchSafe branch_box_3501 := by
  left; refine ⟨branch_box_3501_nonnegative, ?_⟩
  intro z hz; exact leaf_3501_sound hz

theorem leaf_3508_ok : checkAt 527 1000 box_3508 cert_3508 = true := by
  have h := List.all_eq_true.mp batch_70_02_ok accepted_3508 (by simp [batch_70_02_values])
  exact h
theorem leaf_3508_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3508.profileLo box_3508.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3508_ok
theorem branch_box_3508_nonnegative : ∀ j, 0 ≤ branch_box_3508.lower j ∧ 0 ≤ branch_box_3508.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3508, Box.profileLo, Box.profileHi, box_3508]
theorem leaf_3508_BranchSafe : CertificateConsequences.BranchSafe branch_box_3508 := by
  left; refine ⟨branch_box_3508_nonnegative, ?_⟩
  intro z hz; exact leaf_3508_sound hz

theorem leaf_3510_ok : checkAt 527 1000 box_3510 cert_3510 = true := by
  have h := List.all_eq_true.mp batch_70_03_ok accepted_3510 (by simp [batch_70_03_values])
  exact h
theorem leaf_3510_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3510.profileLo box_3510.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3510_ok
theorem branch_box_3510_nonnegative : ∀ j, 0 ≤ branch_box_3510.lower j ∧ 0 ≤ branch_box_3510.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3510, Box.profileLo, Box.profileHi, box_3510]
theorem leaf_3510_BranchSafe : CertificateConsequences.BranchSafe branch_box_3510 := by
  left; refine ⟨branch_box_3510_nonnegative, ?_⟩
  intro z hz; exact leaf_3510_sound hz

theorem leaf_3512_ok : checkAt 527 1000 box_3512 cert_3512 = true := by
  have h := List.all_eq_true.mp batch_70_04_ok accepted_3512 (by simp [batch_70_04_values])
  exact h
theorem leaf_3512_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3512.profileLo box_3512.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3512_ok
theorem branch_box_3512_nonnegative : ∀ j, 0 ≤ branch_box_3512.lower j ∧ 0 ≤ branch_box_3512.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3512, Box.profileLo, Box.profileHi, box_3512]
theorem leaf_3512_BranchSafe : CertificateConsequences.BranchSafe branch_box_3512 := by
  left; refine ⟨branch_box_3512_nonnegative, ?_⟩
  intro z hz; exact leaf_3512_sound hz

theorem leaf_3514_ok : checkAt 527 1000 box_3514 cert_3514 = true := by
  have h := List.all_eq_true.mp batch_70_05_ok accepted_3514 (by simp [batch_70_05_values])
  exact h
theorem leaf_3514_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3514.profileLo box_3514.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3514_ok
theorem branch_box_3514_nonnegative : ∀ j, 0 ≤ branch_box_3514.lower j ∧ 0 ≤ branch_box_3514.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3514, Box.profileLo, Box.profileHi, box_3514]
theorem leaf_3514_BranchSafe : CertificateConsequences.BranchSafe branch_box_3514 := by
  left; refine ⟨branch_box_3514_nonnegative, ?_⟩
  intro z hz; exact leaf_3514_sound hz

theorem leaf_3516_ok : checkAt 527 1000 box_3516 cert_3516 = true := by
  have h := List.all_eq_true.mp batch_70_06_ok accepted_3516 (by simp [batch_70_06_values])
  exact h
theorem leaf_3516_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3516.profileLo box_3516.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3516_ok
theorem branch_box_3516_nonnegative : ∀ j, 0 ≤ branch_box_3516.lower j ∧ 0 ≤ branch_box_3516.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3516, Box.profileLo, Box.profileHi, box_3516]
theorem leaf_3516_BranchSafe : CertificateConsequences.BranchSafe branch_box_3516 := by
  left; refine ⟨branch_box_3516_nonnegative, ?_⟩
  intro z hz; exact leaf_3516_sound hz

theorem leaf_3518_ok : checkAt 527 1000 box_3518 cert_3518 = true := by
  have h := List.all_eq_true.mp batch_70_07_ok accepted_3518 (by simp [batch_70_07_values])
  exact h
theorem leaf_3518_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3518.profileLo box_3518.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3518_ok
theorem branch_box_3518_nonnegative : ∀ j, 0 ≤ branch_box_3518.lower j ∧ 0 ≤ branch_box_3518.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3518, Box.profileLo, Box.profileHi, box_3518]
theorem leaf_3518_BranchSafe : CertificateConsequences.BranchSafe branch_box_3518 := by
  left; refine ⟨branch_box_3518_nonnegative, ?_⟩
  intro z hz; exact leaf_3518_sound hz

theorem leaf_3520_ok : checkAt 527 1000 box_3520 cert_3520 = true := by
  have h := List.all_eq_true.mp batch_70_08_ok accepted_3520 (by simp [batch_70_08_values])
  exact h
theorem leaf_3520_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3520.profileLo box_3520.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3520_ok
theorem branch_box_3520_nonnegative : ∀ j, 0 ≤ branch_box_3520.lower j ∧ 0 ≤ branch_box_3520.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3520, Box.profileLo, Box.profileHi, box_3520]
theorem leaf_3520_BranchSafe : CertificateConsequences.BranchSafe branch_box_3520 := by
  left; refine ⟨branch_box_3520_nonnegative, ?_⟩
  intro z hz; exact leaf_3520_sound hz

theorem leaf_3521_ok : checkAt 527 1000 box_3521 cert_3521 = true := by
  have h := List.all_eq_true.mp batch_70_09_ok accepted_3521 (by simp [batch_70_09_values])
  exact h
theorem leaf_3521_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3521.profileLo box_3521.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3521_ok
theorem branch_box_3521_nonnegative : ∀ j, 0 ≤ branch_box_3521.lower j ∧ 0 ≤ branch_box_3521.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3521, Box.profileLo, Box.profileHi, box_3521]
theorem leaf_3521_BranchSafe : CertificateConsequences.BranchSafe branch_box_3521 := by
  left; refine ⟨branch_box_3521_nonnegative, ?_⟩
  intro z hz; exact leaf_3521_sound hz

theorem leaf_3523_ok : checkAt 527 1000 box_3523 cert_3523 = true := by
  have h := List.all_eq_true.mp batch_70_10_ok accepted_3523 (by simp [batch_70_10_values])
  exact h
theorem leaf_3523_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3523.profileLo box_3523.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3523_ok
theorem branch_box_3523_nonnegative : ∀ j, 0 ≤ branch_box_3523.lower j ∧ 0 ≤ branch_box_3523.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3523, Box.profileLo, Box.profileHi, box_3523]
theorem leaf_3523_BranchSafe : CertificateConsequences.BranchSafe branch_box_3523 := by
  left; refine ⟨branch_box_3523_nonnegative, ?_⟩
  intro z hz; exact leaf_3523_sound hz

theorem leaf_3527_ok : checkAt 527 1000 box_3527 cert_3527 = true := by
  have h := List.all_eq_true.mp batch_70_11_ok accepted_3527 (by simp [batch_70_11_values])
  exact h
theorem leaf_3527_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3527.profileLo box_3527.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3527_ok
theorem branch_box_3527_nonnegative : ∀ j, 0 ≤ branch_box_3527.lower j ∧ 0 ≤ branch_box_3527.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3527, Box.profileLo, Box.profileHi, box_3527]
theorem leaf_3527_BranchSafe : CertificateConsequences.BranchSafe branch_box_3527 := by
  left; refine ⟨branch_box_3527_nonnegative, ?_⟩
  intro z hz; exact leaf_3527_sound hz

theorem leaf_3530_ok : checkAt 527 1000 box_3530 cert_3530 = true := by
  have h := List.all_eq_true.mp batch_70_12_ok accepted_3530 (by simp [batch_70_12_values])
  exact h
theorem leaf_3530_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3530.profileLo box_3530.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3530_ok
theorem branch_box_3530_nonnegative : ∀ j, 0 ≤ branch_box_3530.lower j ∧ 0 ≤ branch_box_3530.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3530, Box.profileLo, Box.profileHi, box_3530]
theorem leaf_3530_BranchSafe : CertificateConsequences.BranchSafe branch_box_3530 := by
  left; refine ⟨branch_box_3530_nonnegative, ?_⟩
  intro z hz; exact leaf_3530_sound hz

theorem leaf_3532_ok : checkAt 527 1000 box_3532 cert_3532 = true := by
  have h := List.all_eq_true.mp batch_70_13_ok accepted_3532 (by simp [batch_70_13_values])
  exact h
theorem leaf_3532_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3532.profileLo box_3532.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3532_ok
theorem branch_box_3532_nonnegative : ∀ j, 0 ≤ branch_box_3532.lower j ∧ 0 ≤ branch_box_3532.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3532, Box.profileLo, Box.profileHi, box_3532]
theorem leaf_3532_BranchSafe : CertificateConsequences.BranchSafe branch_box_3532 := by
  left; refine ⟨branch_box_3532_nonnegative, ?_⟩
  intro z hz; exact leaf_3532_sound hz

theorem leaf_3534_ok : checkAt 527 1000 box_3534 cert_3534 = true := by
  have h := List.all_eq_true.mp batch_70_14_ok accepted_3534 (by simp [batch_70_14_values])
  exact h
theorem leaf_3534_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3534.profileLo box_3534.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3534_ok
theorem branch_box_3534_nonnegative : ∀ j, 0 ≤ branch_box_3534.lower j ∧ 0 ≤ branch_box_3534.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3534, Box.profileLo, Box.profileHi, box_3534]
theorem leaf_3534_BranchSafe : CertificateConsequences.BranchSafe branch_box_3534 := by
  left; refine ⟨branch_box_3534_nonnegative, ?_⟩
  intro z hz; exact leaf_3534_sound hz

theorem leaf_3535_ok : checkAt 527 1000 box_3535 cert_3535 = true := by
  have h := List.all_eq_true.mp batch_70_15_ok accepted_3535 (by simp [batch_70_15_values])
  exact h
theorem leaf_3535_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3535.profileLo box_3535.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3535_ok
theorem branch_box_3535_nonnegative : ∀ j, 0 ≤ branch_box_3535.lower j ∧ 0 ≤ branch_box_3535.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3535, Box.profileLo, Box.profileHi, box_3535]
theorem leaf_3535_BranchSafe : CertificateConsequences.BranchSafe branch_box_3535 := by
  left; refine ⟨branch_box_3535_nonnegative, ?_⟩
  intro z hz; exact leaf_3535_sound hz

theorem leaf_3537_ok : checkAt 527 1000 box_3537 cert_3537 = true := by
  have h := List.all_eq_true.mp batch_70_16_ok accepted_3537 (by simp [batch_70_16_values])
  exact h
theorem leaf_3537_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3537.profileLo box_3537.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3537_ok
theorem branch_box_3537_nonnegative : ∀ j, 0 ≤ branch_box_3537.lower j ∧ 0 ≤ branch_box_3537.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3537, Box.profileLo, Box.profileHi, box_3537]
theorem leaf_3537_BranchSafe : CertificateConsequences.BranchSafe branch_box_3537 := by
  left; refine ⟨branch_box_3537_nonnegative, ?_⟩
  intro z hz; exact leaf_3537_sound hz

theorem leaf_3539_ok : checkAt 527 1000 box_3539 cert_3539 = true := by
  have h := List.all_eq_true.mp batch_70_17_ok accepted_3539 (by simp [batch_70_17_values])
  exact h
theorem leaf_3539_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3539.profileLo box_3539.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3539_ok
theorem branch_box_3539_nonnegative : ∀ j, 0 ≤ branch_box_3539.lower j ∧ 0 ≤ branch_box_3539.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3539, Box.profileLo, Box.profileHi, box_3539]
theorem leaf_3539_BranchSafe : CertificateConsequences.BranchSafe branch_box_3539 := by
  left; refine ⟨branch_box_3539_nonnegative, ?_⟩
  intro z hz; exact leaf_3539_sound hz

theorem leaf_3542_ok : checkAt 527 1000 box_3542 cert_3542 = true := by
  have h := List.all_eq_true.mp batch_70_18_ok accepted_3542 (by simp [batch_70_18_values])
  exact h
theorem leaf_3542_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3542.profileLo box_3542.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3542_ok
theorem branch_box_3542_nonnegative : ∀ j, 0 ≤ branch_box_3542.lower j ∧ 0 ≤ branch_box_3542.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3542, Box.profileLo, Box.profileHi, box_3542]
theorem leaf_3542_BranchSafe : CertificateConsequences.BranchSafe branch_box_3542 := by
  left; refine ⟨branch_box_3542_nonnegative, ?_⟩
  intro z hz; exact leaf_3542_sound hz

theorem leaf_3544_ok : checkAt 527 1000 box_3544 cert_3544 = true := by
  have h := List.all_eq_true.mp batch_70_19_ok accepted_3544 (by simp [batch_70_19_values])
  exact h
theorem leaf_3544_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3544.profileLo box_3544.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3544_ok
theorem branch_box_3544_nonnegative : ∀ j, 0 ≤ branch_box_3544.lower j ∧ 0 ≤ branch_box_3544.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3544, Box.profileLo, Box.profileHi, box_3544]
theorem leaf_3544_BranchSafe : CertificateConsequences.BranchSafe branch_box_3544 := by
  left; refine ⟨branch_box_3544_nonnegative, ?_⟩
  intro z hz; exact leaf_3544_sound hz

theorem leaf_3548_ok : checkAt 527 1000 box_3548 cert_3548 = true := by
  have h := List.all_eq_true.mp batch_70_20_ok accepted_3548 (by simp [batch_70_20_values])
  exact h
theorem leaf_3548_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3548.profileLo box_3548.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3548_ok
theorem branch_box_3548_nonnegative : ∀ j, 0 ≤ branch_box_3548.lower j ∧ 0 ≤ branch_box_3548.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3548, Box.profileLo, Box.profileHi, box_3548]
theorem leaf_3548_BranchSafe : CertificateConsequences.BranchSafe branch_box_3548 := by
  left; refine ⟨branch_box_3548_nonnegative, ?_⟩
  intro z hz; exact leaf_3548_sound hz

#print axioms batch_70_00_ok
#print axioms leaf_3500_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
