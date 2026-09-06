import PeaceableQueens.UpperBound.Generated.Even.C527Scaled70Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_70_00_values : List Bool := [accepted_3500]
theorem batch_70_00_ok : batch_70_00_values.all id = true := by decide

def batch_70_01_values : List Bool := [accepted_3506]
theorem batch_70_01_ok : batch_70_01_values.all id = true := by decide

def batch_70_02_values : List Bool := [accepted_3507]
theorem batch_70_02_ok : batch_70_02_values.all id = true := by decide

def batch_70_03_values : List Bool := [accepted_3508]
theorem batch_70_03_ok : batch_70_03_values.all id = true := by decide

def batch_70_04_values : List Bool := [accepted_3511]
theorem batch_70_04_ok : batch_70_04_values.all id = true := by decide

def batch_70_05_values : List Bool := [accepted_3513]
theorem batch_70_05_ok : batch_70_05_values.all id = true := by decide

def batch_70_06_values : List Bool := [accepted_3514]
theorem batch_70_06_ok : batch_70_06_values.all id = true := by decide

def batch_70_07_values : List Bool := [accepted_3518]
theorem batch_70_07_ok : batch_70_07_values.all id = true := by decide

def batch_70_08_values : List Bool := [accepted_3519]
theorem batch_70_08_ok : batch_70_08_values.all id = true := by decide

def batch_70_09_values : List Bool := [accepted_3522]
theorem batch_70_09_ok : batch_70_09_values.all id = true := by decide

def batch_70_10_values : List Bool := [accepted_3523]
theorem batch_70_10_ok : batch_70_10_values.all id = true := by decide

def batch_70_11_values : List Bool := [accepted_3524]
theorem batch_70_11_ok : batch_70_11_values.all id = true := by decide

def batch_70_12_values : List Bool := [accepted_3525]
theorem batch_70_12_ok : batch_70_12_values.all id = true := by decide

def batch_70_13_values : List Bool := [accepted_3526]
theorem batch_70_13_ok : batch_70_13_values.all id = true := by decide

def batch_70_14_values : List Bool := [accepted_3529]
theorem batch_70_14_ok : batch_70_14_values.all id = true := by decide

def batch_70_15_values : List Bool := [accepted_3530]
theorem batch_70_15_ok : batch_70_15_values.all id = true := by decide

def batch_70_16_values : List Bool := [accepted_3533]
theorem batch_70_16_ok : batch_70_16_values.all id = true := by decide

def batch_70_17_values : List Bool := [accepted_3534]
theorem batch_70_17_ok : batch_70_17_values.all id = true := by decide

def batch_70_18_values : List Bool := [accepted_3537]
theorem batch_70_18_ok : batch_70_18_values.all id = true := by decide

def batch_70_19_values : List Bool := [accepted_3538]
theorem batch_70_19_ok : batch_70_19_values.all id = true := by decide

def batch_70_20_values : List Bool := [accepted_3542]
theorem batch_70_20_ok : batch_70_20_values.all id = true := by decide

def batch_70_21_values : List Bool := [accepted_3544]
theorem batch_70_21_ok : batch_70_21_values.all id = true := by decide

def batch_70_22_values : List Bool := [accepted_3545]
theorem batch_70_22_ok : batch_70_22_values.all id = true := by decide

def batch_70_23_values : List Bool := [accepted_3546]
theorem batch_70_23_ok : batch_70_23_values.all id = true := by decide

def batch_70_24_values : List Bool := [accepted_3549]
theorem batch_70_24_ok : batch_70_24_values.all id = true := by decide

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

theorem leaf_3506_ok : checkAt 527 1000 box_3506 cert_3506 = true := by
  have h := List.all_eq_true.mp batch_70_01_ok accepted_3506 (by simp [batch_70_01_values])
  exact h
theorem leaf_3506_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3506.profileLo box_3506.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3506_ok
theorem branch_box_3506_nonnegative : ∀ j, 0 ≤ branch_box_3506.lower j ∧ 0 ≤ branch_box_3506.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3506, Box.profileLo, Box.profileHi, box_3506]
theorem leaf_3506_BranchSafe : CertificateConsequences.BranchSafe branch_box_3506 := by
  left; refine ⟨branch_box_3506_nonnegative, ?_⟩
  intro z hz; exact leaf_3506_sound hz

theorem leaf_3507_ok : checkAt 527 1000 box_3507 cert_3507 = true := by
  have h := List.all_eq_true.mp batch_70_02_ok accepted_3507 (by simp [batch_70_02_values])
  exact h
theorem leaf_3507_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3507.profileLo box_3507.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3507_ok
theorem branch_box_3507_nonnegative : ∀ j, 0 ≤ branch_box_3507.lower j ∧ 0 ≤ branch_box_3507.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3507, Box.profileLo, Box.profileHi, box_3507]
theorem leaf_3507_BranchSafe : CertificateConsequences.BranchSafe branch_box_3507 := by
  left; refine ⟨branch_box_3507_nonnegative, ?_⟩
  intro z hz; exact leaf_3507_sound hz

theorem leaf_3508_ok : checkAt 527 1000 box_3508 cert_3508 = true := by
  have h := List.all_eq_true.mp batch_70_03_ok accepted_3508 (by simp [batch_70_03_values])
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

theorem leaf_3511_ok : checkAt 527 1000 box_3511 cert_3511 = true := by
  have h := List.all_eq_true.mp batch_70_04_ok accepted_3511 (by simp [batch_70_04_values])
  exact h
theorem leaf_3511_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3511.profileLo box_3511.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3511_ok
theorem branch_box_3511_nonnegative : ∀ j, 0 ≤ branch_box_3511.lower j ∧ 0 ≤ branch_box_3511.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3511, Box.profileLo, Box.profileHi, box_3511]
theorem leaf_3511_BranchSafe : CertificateConsequences.BranchSafe branch_box_3511 := by
  left; refine ⟨branch_box_3511_nonnegative, ?_⟩
  intro z hz; exact leaf_3511_sound hz

theorem leaf_3513_ok : checkAt 527 1000 box_3513 cert_3513 = true := by
  have h := List.all_eq_true.mp batch_70_05_ok accepted_3513 (by simp [batch_70_05_values])
  exact h
theorem leaf_3513_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3513.profileLo box_3513.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3513_ok
theorem branch_box_3513_nonnegative : ∀ j, 0 ≤ branch_box_3513.lower j ∧ 0 ≤ branch_box_3513.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3513, Box.profileLo, Box.profileHi, box_3513]
theorem leaf_3513_BranchSafe : CertificateConsequences.BranchSafe branch_box_3513 := by
  left; refine ⟨branch_box_3513_nonnegative, ?_⟩
  intro z hz; exact leaf_3513_sound hz

theorem leaf_3514_ok : checkAt 527 1000 box_3514 cert_3514 = true := by
  have h := List.all_eq_true.mp batch_70_06_ok accepted_3514 (by simp [batch_70_06_values])
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

theorem leaf_3519_ok : checkAt 527 1000 box_3519 cert_3519 = true := by
  have h := List.all_eq_true.mp batch_70_08_ok accepted_3519 (by simp [batch_70_08_values])
  exact h
theorem leaf_3519_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3519.profileLo box_3519.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3519_ok
theorem branch_box_3519_nonnegative : ∀ j, 0 ≤ branch_box_3519.lower j ∧ 0 ≤ branch_box_3519.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3519, Box.profileLo, Box.profileHi, box_3519]
theorem leaf_3519_BranchSafe : CertificateConsequences.BranchSafe branch_box_3519 := by
  left; refine ⟨branch_box_3519_nonnegative, ?_⟩
  intro z hz; exact leaf_3519_sound hz

theorem leaf_3522_ok : checkAt 527 1000 box_3522 cert_3522 = true := by
  have h := List.all_eq_true.mp batch_70_09_ok accepted_3522 (by simp [batch_70_09_values])
  exact h
theorem leaf_3522_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3522.profileLo box_3522.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3522_ok
theorem branch_box_3522_nonnegative : ∀ j, 0 ≤ branch_box_3522.lower j ∧ 0 ≤ branch_box_3522.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3522, Box.profileLo, Box.profileHi, box_3522]
theorem leaf_3522_BranchSafe : CertificateConsequences.BranchSafe branch_box_3522 := by
  left; refine ⟨branch_box_3522_nonnegative, ?_⟩
  intro z hz; exact leaf_3522_sound hz

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

theorem leaf_3524_ok : checkAt 527 1000 box_3524 cert_3524 = true := by
  have h := List.all_eq_true.mp batch_70_11_ok accepted_3524 (by simp [batch_70_11_values])
  exact h
theorem leaf_3524_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3524.profileLo box_3524.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3524_ok
theorem branch_box_3524_nonnegative : ∀ j, 0 ≤ branch_box_3524.lower j ∧ 0 ≤ branch_box_3524.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3524, Box.profileLo, Box.profileHi, box_3524]
theorem leaf_3524_BranchSafe : CertificateConsequences.BranchSafe branch_box_3524 := by
  left; refine ⟨branch_box_3524_nonnegative, ?_⟩
  intro z hz; exact leaf_3524_sound hz

theorem leaf_3525_ok : checkAt 527 1000 box_3525 cert_3525 = true := by
  have h := List.all_eq_true.mp batch_70_12_ok accepted_3525 (by simp [batch_70_12_values])
  exact h
theorem leaf_3525_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3525.profileLo box_3525.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3525_ok
theorem branch_box_3525_nonnegative : ∀ j, 0 ≤ branch_box_3525.lower j ∧ 0 ≤ branch_box_3525.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3525, Box.profileLo, Box.profileHi, box_3525]
theorem leaf_3525_BranchSafe : CertificateConsequences.BranchSafe branch_box_3525 := by
  left; refine ⟨branch_box_3525_nonnegative, ?_⟩
  intro z hz; exact leaf_3525_sound hz

theorem leaf_3526_ok : checkAt 527 1000 box_3526 cert_3526 = true := by
  have h := List.all_eq_true.mp batch_70_13_ok accepted_3526 (by simp [batch_70_13_values])
  exact h
theorem leaf_3526_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3526.profileLo box_3526.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3526_ok
theorem branch_box_3526_nonnegative : ∀ j, 0 ≤ branch_box_3526.lower j ∧ 0 ≤ branch_box_3526.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3526, Box.profileLo, Box.profileHi, box_3526]
theorem leaf_3526_BranchSafe : CertificateConsequences.BranchSafe branch_box_3526 := by
  left; refine ⟨branch_box_3526_nonnegative, ?_⟩
  intro z hz; exact leaf_3526_sound hz

theorem leaf_3529_ok : checkAt 527 1000 box_3529 cert_3529 = true := by
  have h := List.all_eq_true.mp batch_70_14_ok accepted_3529 (by simp [batch_70_14_values])
  exact h
theorem leaf_3529_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3529.profileLo box_3529.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3529_ok
theorem branch_box_3529_nonnegative : ∀ j, 0 ≤ branch_box_3529.lower j ∧ 0 ≤ branch_box_3529.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3529, Box.profileLo, Box.profileHi, box_3529]
theorem leaf_3529_BranchSafe : CertificateConsequences.BranchSafe branch_box_3529 := by
  left; refine ⟨branch_box_3529_nonnegative, ?_⟩
  intro z hz; exact leaf_3529_sound hz

theorem leaf_3530_ok : checkAt 527 1000 box_3530 cert_3530 = true := by
  have h := List.all_eq_true.mp batch_70_15_ok accepted_3530 (by simp [batch_70_15_values])
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

theorem leaf_3533_ok : checkAt 527 1000 box_3533 cert_3533 = true := by
  have h := List.all_eq_true.mp batch_70_16_ok accepted_3533 (by simp [batch_70_16_values])
  exact h
theorem leaf_3533_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3533.profileLo box_3533.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3533_ok
theorem branch_box_3533_nonnegative : ∀ j, 0 ≤ branch_box_3533.lower j ∧ 0 ≤ branch_box_3533.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3533, Box.profileLo, Box.profileHi, box_3533]
theorem leaf_3533_BranchSafe : CertificateConsequences.BranchSafe branch_box_3533 := by
  left; refine ⟨branch_box_3533_nonnegative, ?_⟩
  intro z hz; exact leaf_3533_sound hz

theorem leaf_3534_ok : checkAt 527 1000 box_3534 cert_3534 = true := by
  have h := List.all_eq_true.mp batch_70_17_ok accepted_3534 (by simp [batch_70_17_values])
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

theorem leaf_3537_ok : checkAt 527 1000 box_3537 cert_3537 = true := by
  have h := List.all_eq_true.mp batch_70_18_ok accepted_3537 (by simp [batch_70_18_values])
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

theorem leaf_3538_ok : checkAt 527 1000 box_3538 cert_3538 = true := by
  have h := List.all_eq_true.mp batch_70_19_ok accepted_3538 (by simp [batch_70_19_values])
  exact h
theorem leaf_3538_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3538.profileLo box_3538.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3538_ok
theorem branch_box_3538_nonnegative : ∀ j, 0 ≤ branch_box_3538.lower j ∧ 0 ≤ branch_box_3538.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3538, Box.profileLo, Box.profileHi, box_3538]
theorem leaf_3538_BranchSafe : CertificateConsequences.BranchSafe branch_box_3538 := by
  left; refine ⟨branch_box_3538_nonnegative, ?_⟩
  intro z hz; exact leaf_3538_sound hz

theorem leaf_3542_ok : checkAt 527 1000 box_3542 cert_3542 = true := by
  have h := List.all_eq_true.mp batch_70_20_ok accepted_3542 (by simp [batch_70_20_values])
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
  have h := List.all_eq_true.mp batch_70_21_ok accepted_3544 (by simp [batch_70_21_values])
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

theorem leaf_3545_ok : checkAt 527 1000 box_3545 cert_3545 = true := by
  have h := List.all_eq_true.mp batch_70_22_ok accepted_3545 (by simp [batch_70_22_values])
  exact h
theorem leaf_3545_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3545.profileLo box_3545.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3545_ok
theorem branch_box_3545_nonnegative : ∀ j, 0 ≤ branch_box_3545.lower j ∧ 0 ≤ branch_box_3545.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3545, Box.profileLo, Box.profileHi, box_3545]
theorem leaf_3545_BranchSafe : CertificateConsequences.BranchSafe branch_box_3545 := by
  left; refine ⟨branch_box_3545_nonnegative, ?_⟩
  intro z hz; exact leaf_3545_sound hz

theorem leaf_3546_ok : checkAt 527 1000 box_3546 cert_3546 = true := by
  have h := List.all_eq_true.mp batch_70_23_ok accepted_3546 (by simp [batch_70_23_values])
  exact h
theorem leaf_3546_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3546.profileLo box_3546.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3546_ok
theorem branch_box_3546_nonnegative : ∀ j, 0 ≤ branch_box_3546.lower j ∧ 0 ≤ branch_box_3546.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3546, Box.profileLo, Box.profileHi, box_3546]
theorem leaf_3546_BranchSafe : CertificateConsequences.BranchSafe branch_box_3546 := by
  left; refine ⟨branch_box_3546_nonnegative, ?_⟩
  intro z hz; exact leaf_3546_sound hz

theorem leaf_3549_ok : checkAt 527 1000 box_3549 cert_3549 = true := by
  have h := List.all_eq_true.mp batch_70_24_ok accepted_3549 (by simp [batch_70_24_values])
  exact h
theorem leaf_3549_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3549.profileLo box_3549.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3549_ok
theorem branch_box_3549_nonnegative : ∀ j, 0 ≤ branch_box_3549.lower j ∧ 0 ≤ branch_box_3549.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3549, Box.profileLo, Box.profileHi, box_3549]
theorem leaf_3549_BranchSafe : CertificateConsequences.BranchSafe branch_box_3549 := by
  left; refine ⟨branch_box_3549_nonnegative, ?_⟩
  intro z hz; exact leaf_3549_sound hz

#print axioms batch_70_00_ok
#print axioms leaf_3500_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
