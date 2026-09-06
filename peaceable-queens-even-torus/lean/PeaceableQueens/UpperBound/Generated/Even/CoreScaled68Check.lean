import PeaceableQueens.UpperBound.Generated.Even.CoreScaled68Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_68_00_values : List Bool := [accepted_3400]
theorem batch_68_00_ok : batch_68_00_values.all id = true := by decide

def batch_68_01_values : List Bool := [accepted_3401]
theorem batch_68_01_ok : batch_68_01_values.all id = true := by decide

def batch_68_02_values : List Bool := [accepted_3403]
theorem batch_68_02_ok : batch_68_02_values.all id = true := by decide

def batch_68_03_values : List Bool := [accepted_3405]
theorem batch_68_03_ok : batch_68_03_values.all id = true := by decide

def batch_68_04_values : List Bool := [accepted_3410]
theorem batch_68_04_ok : batch_68_04_values.all id = true := by decide

def batch_68_05_values : List Bool := [accepted_3411]
theorem batch_68_05_ok : batch_68_05_values.all id = true := by decide

def batch_68_06_values : List Bool := [accepted_3413]
theorem batch_68_06_ok : batch_68_06_values.all id = true := by decide

def batch_68_07_values : List Bool := [accepted_3415]
theorem batch_68_07_ok : batch_68_07_values.all id = true := by decide

def batch_68_08_values : List Bool := [accepted_3418]
theorem batch_68_08_ok : batch_68_08_values.all id = true := by decide

def batch_68_09_values : List Bool := [accepted_3419]
theorem batch_68_09_ok : batch_68_09_values.all id = true := by decide

def batch_68_10_values : List Bool := [accepted_3421]
theorem batch_68_10_ok : batch_68_10_values.all id = true := by decide

def batch_68_11_values : List Bool := [accepted_3423]
theorem batch_68_11_ok : batch_68_11_values.all id = true := by decide

def batch_68_12_values : List Bool := [accepted_3430]
theorem batch_68_12_ok : batch_68_12_values.all id = true := by decide

def batch_68_13_values : List Bool := [accepted_3432]
theorem batch_68_13_ok : batch_68_13_values.all id = true := by decide

def batch_68_14_values : List Bool := [accepted_3434]
theorem batch_68_14_ok : batch_68_14_values.all id = true := by decide

def batch_68_15_values : List Bool := [accepted_3436]
theorem batch_68_15_ok : batch_68_15_values.all id = true := by decide

def batch_68_16_values : List Bool := [accepted_3438]
theorem batch_68_16_ok : batch_68_16_values.all id = true := by decide

def batch_68_17_values : List Bool := [accepted_3444]
theorem batch_68_17_ok : batch_68_17_values.all id = true := by decide

def batch_68_18_values : List Bool := [accepted_3445]
theorem batch_68_18_ok : batch_68_18_values.all id = true := by decide

def batch_68_19_values : List Bool := [accepted_3447]
theorem batch_68_19_ok : batch_68_19_values.all id = true := by decide

def batch_68_20_values : List Bool := [accepted_3449]
theorem batch_68_20_ok : batch_68_20_values.all id = true := by decide

theorem leaf_3400_ok : checkAt 527 1000 box_3400 cert_3400 = true := by
  have h := List.all_eq_true.mp batch_68_00_ok accepted_3400 (by simp [batch_68_00_values])
  exact h
theorem leaf_3400_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3400.profileLo box_3400.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3400_ok
theorem branch_box_3400_nonnegative : ∀ j, 0 ≤ branch_box_3400.lower j ∧ 0 ≤ branch_box_3400.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3400, Box.profileLo, Box.profileHi, box_3400]
theorem leaf_3400_BranchSafe : CertificateConsequences.BranchSafe branch_box_3400 := by
  left; refine ⟨branch_box_3400_nonnegative, ?_⟩
  intro z hz; exact leaf_3400_sound hz

theorem leaf_3401_ok : checkAt 527 1000 box_3401 cert_3401 = true := by
  have h := List.all_eq_true.mp batch_68_01_ok accepted_3401 (by simp [batch_68_01_values])
  exact h
theorem leaf_3401_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3401.profileLo box_3401.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3401_ok
theorem branch_box_3401_nonnegative : ∀ j, 0 ≤ branch_box_3401.lower j ∧ 0 ≤ branch_box_3401.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3401, Box.profileLo, Box.profileHi, box_3401]
theorem leaf_3401_BranchSafe : CertificateConsequences.BranchSafe branch_box_3401 := by
  left; refine ⟨branch_box_3401_nonnegative, ?_⟩
  intro z hz; exact leaf_3401_sound hz

theorem leaf_3403_ok : checkAt 527 1000 box_3403 cert_3403 = true := by
  have h := List.all_eq_true.mp batch_68_02_ok accepted_3403 (by simp [batch_68_02_values])
  exact h
theorem leaf_3403_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3403.profileLo box_3403.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3403_ok
theorem branch_box_3403_nonnegative : ∀ j, 0 ≤ branch_box_3403.lower j ∧ 0 ≤ branch_box_3403.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3403, Box.profileLo, Box.profileHi, box_3403]
theorem leaf_3403_BranchSafe : CertificateConsequences.BranchSafe branch_box_3403 := by
  left; refine ⟨branch_box_3403_nonnegative, ?_⟩
  intro z hz; exact leaf_3403_sound hz

theorem leaf_3405_ok : checkAt 527 1000 box_3405 cert_3405 = true := by
  have h := List.all_eq_true.mp batch_68_03_ok accepted_3405 (by simp [batch_68_03_values])
  exact h
theorem leaf_3405_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3405.profileLo box_3405.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3405_ok
theorem branch_box_3405_nonnegative : ∀ j, 0 ≤ branch_box_3405.lower j ∧ 0 ≤ branch_box_3405.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3405, Box.profileLo, Box.profileHi, box_3405]
theorem leaf_3405_BranchSafe : CertificateConsequences.BranchSafe branch_box_3405 := by
  left; refine ⟨branch_box_3405_nonnegative, ?_⟩
  intro z hz; exact leaf_3405_sound hz

theorem leaf_3410_ok : checkAt 527 1000 box_3410 cert_3410 = true := by
  have h := List.all_eq_true.mp batch_68_04_ok accepted_3410 (by simp [batch_68_04_values])
  exact h
theorem leaf_3410_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3410.profileLo box_3410.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3410_ok
theorem branch_box_3410_nonnegative : ∀ j, 0 ≤ branch_box_3410.lower j ∧ 0 ≤ branch_box_3410.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3410, Box.profileLo, Box.profileHi, box_3410]
theorem leaf_3410_BranchSafe : CertificateConsequences.BranchSafe branch_box_3410 := by
  left; refine ⟨branch_box_3410_nonnegative, ?_⟩
  intro z hz; exact leaf_3410_sound hz

theorem leaf_3411_ok : checkAt 527 1000 box_3411 cert_3411 = true := by
  have h := List.all_eq_true.mp batch_68_05_ok accepted_3411 (by simp [batch_68_05_values])
  exact h
theorem leaf_3411_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3411.profileLo box_3411.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3411_ok
theorem branch_box_3411_nonnegative : ∀ j, 0 ≤ branch_box_3411.lower j ∧ 0 ≤ branch_box_3411.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3411, Box.profileLo, Box.profileHi, box_3411]
theorem leaf_3411_BranchSafe : CertificateConsequences.BranchSafe branch_box_3411 := by
  left; refine ⟨branch_box_3411_nonnegative, ?_⟩
  intro z hz; exact leaf_3411_sound hz

theorem leaf_3413_ok : checkAt 527 1000 box_3413 cert_3413 = true := by
  have h := List.all_eq_true.mp batch_68_06_ok accepted_3413 (by simp [batch_68_06_values])
  exact h
theorem leaf_3413_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3413.profileLo box_3413.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3413_ok
theorem branch_box_3413_nonnegative : ∀ j, 0 ≤ branch_box_3413.lower j ∧ 0 ≤ branch_box_3413.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3413, Box.profileLo, Box.profileHi, box_3413]
theorem leaf_3413_BranchSafe : CertificateConsequences.BranchSafe branch_box_3413 := by
  left; refine ⟨branch_box_3413_nonnegative, ?_⟩
  intro z hz; exact leaf_3413_sound hz

theorem leaf_3415_ok : checkAt 527 1000 box_3415 cert_3415 = true := by
  have h := List.all_eq_true.mp batch_68_07_ok accepted_3415 (by simp [batch_68_07_values])
  exact h
theorem leaf_3415_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3415.profileLo box_3415.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3415_ok
theorem branch_box_3415_nonnegative : ∀ j, 0 ≤ branch_box_3415.lower j ∧ 0 ≤ branch_box_3415.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3415, Box.profileLo, Box.profileHi, box_3415]
theorem leaf_3415_BranchSafe : CertificateConsequences.BranchSafe branch_box_3415 := by
  left; refine ⟨branch_box_3415_nonnegative, ?_⟩
  intro z hz; exact leaf_3415_sound hz

theorem leaf_3418_ok : checkAt 527 1000 box_3418 cert_3418 = true := by
  have h := List.all_eq_true.mp batch_68_08_ok accepted_3418 (by simp [batch_68_08_values])
  exact h
theorem leaf_3418_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3418.profileLo box_3418.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3418_ok
theorem branch_box_3418_nonnegative : ∀ j, 0 ≤ branch_box_3418.lower j ∧ 0 ≤ branch_box_3418.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3418, Box.profileLo, Box.profileHi, box_3418]
theorem leaf_3418_BranchSafe : CertificateConsequences.BranchSafe branch_box_3418 := by
  left; refine ⟨branch_box_3418_nonnegative, ?_⟩
  intro z hz; exact leaf_3418_sound hz

theorem leaf_3419_ok : checkAt 527 1000 box_3419 cert_3419 = true := by
  have h := List.all_eq_true.mp batch_68_09_ok accepted_3419 (by simp [batch_68_09_values])
  exact h
theorem leaf_3419_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3419.profileLo box_3419.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3419_ok
theorem branch_box_3419_nonnegative : ∀ j, 0 ≤ branch_box_3419.lower j ∧ 0 ≤ branch_box_3419.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3419, Box.profileLo, Box.profileHi, box_3419]
theorem leaf_3419_BranchSafe : CertificateConsequences.BranchSafe branch_box_3419 := by
  left; refine ⟨branch_box_3419_nonnegative, ?_⟩
  intro z hz; exact leaf_3419_sound hz

theorem leaf_3421_ok : checkAt 527 1000 box_3421 cert_3421 = true := by
  have h := List.all_eq_true.mp batch_68_10_ok accepted_3421 (by simp [batch_68_10_values])
  exact h
theorem leaf_3421_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3421.profileLo box_3421.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3421_ok
theorem branch_box_3421_nonnegative : ∀ j, 0 ≤ branch_box_3421.lower j ∧ 0 ≤ branch_box_3421.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3421, Box.profileLo, Box.profileHi, box_3421]
theorem leaf_3421_BranchSafe : CertificateConsequences.BranchSafe branch_box_3421 := by
  left; refine ⟨branch_box_3421_nonnegative, ?_⟩
  intro z hz; exact leaf_3421_sound hz

theorem leaf_3423_ok : checkAt 527 1000 box_3423 cert_3423 = true := by
  have h := List.all_eq_true.mp batch_68_11_ok accepted_3423 (by simp [batch_68_11_values])
  exact h
theorem leaf_3423_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3423.profileLo box_3423.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3423_ok
theorem branch_box_3423_nonnegative : ∀ j, 0 ≤ branch_box_3423.lower j ∧ 0 ≤ branch_box_3423.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3423, Box.profileLo, Box.profileHi, box_3423]
theorem leaf_3423_BranchSafe : CertificateConsequences.BranchSafe branch_box_3423 := by
  left; refine ⟨branch_box_3423_nonnegative, ?_⟩
  intro z hz; exact leaf_3423_sound hz

theorem leaf_3430_ok : checkAt 527 1000 box_3430 cert_3430 = true := by
  have h := List.all_eq_true.mp batch_68_12_ok accepted_3430 (by simp [batch_68_12_values])
  exact h
theorem leaf_3430_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3430.profileLo box_3430.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3430_ok
theorem branch_box_3430_nonnegative : ∀ j, 0 ≤ branch_box_3430.lower j ∧ 0 ≤ branch_box_3430.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3430, Box.profileLo, Box.profileHi, box_3430]
theorem leaf_3430_BranchSafe : CertificateConsequences.BranchSafe branch_box_3430 := by
  left; refine ⟨branch_box_3430_nonnegative, ?_⟩
  intro z hz; exact leaf_3430_sound hz

theorem leaf_3432_ok : checkAt 527 1000 box_3432 cert_3432 = true := by
  have h := List.all_eq_true.mp batch_68_13_ok accepted_3432 (by simp [batch_68_13_values])
  exact h
theorem leaf_3432_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3432.profileLo box_3432.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3432_ok
theorem branch_box_3432_nonnegative : ∀ j, 0 ≤ branch_box_3432.lower j ∧ 0 ≤ branch_box_3432.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3432, Box.profileLo, Box.profileHi, box_3432]
theorem leaf_3432_BranchSafe : CertificateConsequences.BranchSafe branch_box_3432 := by
  left; refine ⟨branch_box_3432_nonnegative, ?_⟩
  intro z hz; exact leaf_3432_sound hz

theorem leaf_3434_ok : checkAt 527 1000 box_3434 cert_3434 = true := by
  have h := List.all_eq_true.mp batch_68_14_ok accepted_3434 (by simp [batch_68_14_values])
  exact h
theorem leaf_3434_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3434.profileLo box_3434.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3434_ok
theorem branch_box_3434_nonnegative : ∀ j, 0 ≤ branch_box_3434.lower j ∧ 0 ≤ branch_box_3434.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3434, Box.profileLo, Box.profileHi, box_3434]
theorem leaf_3434_BranchSafe : CertificateConsequences.BranchSafe branch_box_3434 := by
  left; refine ⟨branch_box_3434_nonnegative, ?_⟩
  intro z hz; exact leaf_3434_sound hz

theorem leaf_3436_ok : checkAt 527 1000 box_3436 cert_3436 = true := by
  have h := List.all_eq_true.mp batch_68_15_ok accepted_3436 (by simp [batch_68_15_values])
  exact h
theorem leaf_3436_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3436.profileLo box_3436.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3436_ok
theorem branch_box_3436_nonnegative : ∀ j, 0 ≤ branch_box_3436.lower j ∧ 0 ≤ branch_box_3436.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3436, Box.profileLo, Box.profileHi, box_3436]
theorem leaf_3436_BranchSafe : CertificateConsequences.BranchSafe branch_box_3436 := by
  left; refine ⟨branch_box_3436_nonnegative, ?_⟩
  intro z hz; exact leaf_3436_sound hz

theorem leaf_3438_ok : checkAt 527 1000 box_3438 cert_3438 = true := by
  have h := List.all_eq_true.mp batch_68_16_ok accepted_3438 (by simp [batch_68_16_values])
  exact h
theorem leaf_3438_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3438.profileLo box_3438.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3438_ok
theorem branch_box_3438_nonnegative : ∀ j, 0 ≤ branch_box_3438.lower j ∧ 0 ≤ branch_box_3438.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3438, Box.profileLo, Box.profileHi, box_3438]
theorem leaf_3438_BranchSafe : CertificateConsequences.BranchSafe branch_box_3438 := by
  left; refine ⟨branch_box_3438_nonnegative, ?_⟩
  intro z hz; exact leaf_3438_sound hz

theorem leaf_3444_ok : checkAt 527 1000 box_3444 cert_3444 = true := by
  have h := List.all_eq_true.mp batch_68_17_ok accepted_3444 (by simp [batch_68_17_values])
  exact h
theorem leaf_3444_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3444.profileLo box_3444.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3444_ok
theorem branch_box_3444_nonnegative : ∀ j, 0 ≤ branch_box_3444.lower j ∧ 0 ≤ branch_box_3444.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3444, Box.profileLo, Box.profileHi, box_3444]
theorem leaf_3444_BranchSafe : CertificateConsequences.BranchSafe branch_box_3444 := by
  left; refine ⟨branch_box_3444_nonnegative, ?_⟩
  intro z hz; exact leaf_3444_sound hz

theorem leaf_3445_ok : checkAt 527 1000 box_3445 cert_3445 = true := by
  have h := List.all_eq_true.mp batch_68_18_ok accepted_3445 (by simp [batch_68_18_values])
  exact h
theorem leaf_3445_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3445.profileLo box_3445.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3445_ok
theorem branch_box_3445_nonnegative : ∀ j, 0 ≤ branch_box_3445.lower j ∧ 0 ≤ branch_box_3445.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3445, Box.profileLo, Box.profileHi, box_3445]
theorem leaf_3445_BranchSafe : CertificateConsequences.BranchSafe branch_box_3445 := by
  left; refine ⟨branch_box_3445_nonnegative, ?_⟩
  intro z hz; exact leaf_3445_sound hz

theorem leaf_3447_ok : checkAt 527 1000 box_3447 cert_3447 = true := by
  have h := List.all_eq_true.mp batch_68_19_ok accepted_3447 (by simp [batch_68_19_values])
  exact h
theorem leaf_3447_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3447.profileLo box_3447.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3447_ok
theorem branch_box_3447_nonnegative : ∀ j, 0 ≤ branch_box_3447.lower j ∧ 0 ≤ branch_box_3447.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3447, Box.profileLo, Box.profileHi, box_3447]
theorem leaf_3447_BranchSafe : CertificateConsequences.BranchSafe branch_box_3447 := by
  left; refine ⟨branch_box_3447_nonnegative, ?_⟩
  intro z hz; exact leaf_3447_sound hz

theorem leaf_3449_ok : checkAt 527 1000 box_3449 cert_3449 = true := by
  have h := List.all_eq_true.mp batch_68_20_ok accepted_3449 (by simp [batch_68_20_values])
  exact h
theorem leaf_3449_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3449.profileLo box_3449.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3449_ok
theorem branch_box_3449_nonnegative : ∀ j, 0 ≤ branch_box_3449.lower j ∧ 0 ≤ branch_box_3449.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3449, Box.profileLo, Box.profileHi, box_3449]
theorem leaf_3449_BranchSafe : CertificateConsequences.BranchSafe branch_box_3449 := by
  left; refine ⟨branch_box_3449_nonnegative, ?_⟩
  intro z hz; exact leaf_3449_sound hz

#print axioms batch_68_00_ok
#print axioms leaf_3400_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
