import PeaceableQueens.UpperBound.Generated.Even.C527Scaled08Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_08_00_values : List Bool := [accepted_400]
theorem batch_08_00_ok : batch_08_00_values.all id = true := by decide

def batch_08_01_values : List Bool := [accepted_401]
theorem batch_08_01_ok : batch_08_01_values.all id = true := by decide

def batch_08_02_values : List Bool := [accepted_406]
theorem batch_08_02_ok : batch_08_02_values.all id = true := by decide

def batch_08_03_values : List Bool := [accepted_408]
theorem batch_08_03_ok : batch_08_03_values.all id = true := by decide

def batch_08_04_values : List Bool := [accepted_409]
theorem batch_08_04_ok : batch_08_04_values.all id = true := by decide

def batch_08_05_values : List Bool := [accepted_410]
theorem batch_08_05_ok : batch_08_05_values.all id = true := by decide

def batch_08_06_values : List Bool := [accepted_411]
theorem batch_08_06_ok : batch_08_06_values.all id = true := by decide

def batch_08_07_values : List Bool := [accepted_412]
theorem batch_08_07_ok : batch_08_07_values.all id = true := by decide

def batch_08_08_values : List Bool := [accepted_417]
theorem batch_08_08_ok : batch_08_08_values.all id = true := by decide

def batch_08_09_values : List Bool := [accepted_418]
theorem batch_08_09_ok : batch_08_09_values.all id = true := by decide

def batch_08_10_values : List Bool := [accepted_419]
theorem batch_08_10_ok : batch_08_10_values.all id = true := by decide

def batch_08_11_values : List Bool := [accepted_421]
theorem batch_08_11_ok : batch_08_11_values.all id = true := by decide

def batch_08_12_values : List Bool := [accepted_422]
theorem batch_08_12_ok : batch_08_12_values.all id = true := by decide

def batch_08_13_values : List Bool := [accepted_423]
theorem batch_08_13_ok : batch_08_13_values.all id = true := by decide

def batch_08_14_values : List Bool := [accepted_427]
theorem batch_08_14_ok : batch_08_14_values.all id = true := by decide

def batch_08_15_values : List Bool := [accepted_428]
theorem batch_08_15_ok : batch_08_15_values.all id = true := by decide

def batch_08_16_values : List Bool := [accepted_429]
theorem batch_08_16_ok : batch_08_16_values.all id = true := by decide

def batch_08_17_values : List Bool := [accepted_430]
theorem batch_08_17_ok : batch_08_17_values.all id = true := by decide

def batch_08_18_values : List Bool := [accepted_435]
theorem batch_08_18_ok : batch_08_18_values.all id = true := by decide

def batch_08_19_values : List Bool := [accepted_436]
theorem batch_08_19_ok : batch_08_19_values.all id = true := by decide

def batch_08_20_values : List Bool := [accepted_439]
theorem batch_08_20_ok : batch_08_20_values.all id = true := by decide

def batch_08_21_values : List Bool := [accepted_441]
theorem batch_08_21_ok : batch_08_21_values.all id = true := by decide

def batch_08_22_values : List Bool := [accepted_442]
theorem batch_08_22_ok : batch_08_22_values.all id = true := by decide

def batch_08_23_values : List Bool := [accepted_443]
theorem batch_08_23_ok : batch_08_23_values.all id = true := by decide

def batch_08_24_values : List Bool := [accepted_445]
theorem batch_08_24_ok : batch_08_24_values.all id = true := by decide

def batch_08_25_values : List Bool := [accepted_447]
theorem batch_08_25_ok : batch_08_25_values.all id = true := by decide

def batch_08_26_values : List Bool := [accepted_449]
theorem batch_08_26_ok : batch_08_26_values.all id = true := by decide

theorem leaf_400_ok : checkAt 527 1000 box_400 cert_400 = true := by
  have h := List.all_eq_true.mp batch_08_00_ok accepted_400 (by simp [batch_08_00_values])
  exact h
theorem leaf_400_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_400.profileLo box_400.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_400_ok
theorem branch_box_400_nonnegative : ∀ j, 0 ≤ branch_box_400.lower j ∧ 0 ≤ branch_box_400.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_400, Box.profileLo, Box.profileHi, box_400]
theorem leaf_400_BranchSafe : CertificateConsequences.BranchSafe branch_box_400 := by
  left; refine ⟨branch_box_400_nonnegative, ?_⟩
  intro z hz; exact leaf_400_sound hz

theorem leaf_401_ok : checkAt 527 1000 box_401 cert_401 = true := by
  have h := List.all_eq_true.mp batch_08_01_ok accepted_401 (by simp [batch_08_01_values])
  exact h
theorem leaf_401_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_401.profileLo box_401.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_401_ok
theorem branch_box_401_nonnegative : ∀ j, 0 ≤ branch_box_401.lower j ∧ 0 ≤ branch_box_401.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_401, Box.profileLo, Box.profileHi, box_401]
theorem leaf_401_BranchSafe : CertificateConsequences.BranchSafe branch_box_401 := by
  left; refine ⟨branch_box_401_nonnegative, ?_⟩
  intro z hz; exact leaf_401_sound hz

theorem leaf_406_ok : checkAt 527 1000 box_406 cert_406 = true := by
  have h := List.all_eq_true.mp batch_08_02_ok accepted_406 (by simp [batch_08_02_values])
  exact h
theorem leaf_406_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_406.profileLo box_406.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_406_ok
theorem branch_box_406_nonnegative : ∀ j, 0 ≤ branch_box_406.lower j ∧ 0 ≤ branch_box_406.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_406, Box.profileLo, Box.profileHi, box_406]
theorem leaf_406_BranchSafe : CertificateConsequences.BranchSafe branch_box_406 := by
  left; refine ⟨branch_box_406_nonnegative, ?_⟩
  intro z hz; exact leaf_406_sound hz

theorem leaf_408_ok : checkAt 527 1000 box_408 cert_408 = true := by
  have h := List.all_eq_true.mp batch_08_03_ok accepted_408 (by simp [batch_08_03_values])
  exact h
theorem leaf_408_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_408.profileLo box_408.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_408_ok
theorem branch_box_408_nonnegative : ∀ j, 0 ≤ branch_box_408.lower j ∧ 0 ≤ branch_box_408.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_408, Box.profileLo, Box.profileHi, box_408]
theorem leaf_408_BranchSafe : CertificateConsequences.BranchSafe branch_box_408 := by
  left; refine ⟨branch_box_408_nonnegative, ?_⟩
  intro z hz; exact leaf_408_sound hz

theorem leaf_409_ok : checkAt 527 1000 box_409 cert_409 = true := by
  have h := List.all_eq_true.mp batch_08_04_ok accepted_409 (by simp [batch_08_04_values])
  exact h
theorem leaf_409_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_409.profileLo box_409.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_409_ok
theorem branch_box_409_nonnegative : ∀ j, 0 ≤ branch_box_409.lower j ∧ 0 ≤ branch_box_409.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_409, Box.profileLo, Box.profileHi, box_409]
theorem leaf_409_BranchSafe : CertificateConsequences.BranchSafe branch_box_409 := by
  left; refine ⟨branch_box_409_nonnegative, ?_⟩
  intro z hz; exact leaf_409_sound hz

theorem leaf_410_ok : checkAt 527 1000 box_410 cert_410 = true := by
  have h := List.all_eq_true.mp batch_08_05_ok accepted_410 (by simp [batch_08_05_values])
  exact h
theorem leaf_410_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_410.profileLo box_410.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_410_ok
theorem branch_box_410_nonnegative : ∀ j, 0 ≤ branch_box_410.lower j ∧ 0 ≤ branch_box_410.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_410, Box.profileLo, Box.profileHi, box_410]
theorem leaf_410_BranchSafe : CertificateConsequences.BranchSafe branch_box_410 := by
  left; refine ⟨branch_box_410_nonnegative, ?_⟩
  intro z hz; exact leaf_410_sound hz

theorem leaf_411_ok : checkAt 527 1000 box_411 cert_411 = true := by
  have h := List.all_eq_true.mp batch_08_06_ok accepted_411 (by simp [batch_08_06_values])
  exact h
theorem leaf_411_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_411.profileLo box_411.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_411_ok
theorem branch_box_411_nonnegative : ∀ j, 0 ≤ branch_box_411.lower j ∧ 0 ≤ branch_box_411.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_411, Box.profileLo, Box.profileHi, box_411]
theorem leaf_411_BranchSafe : CertificateConsequences.BranchSafe branch_box_411 := by
  left; refine ⟨branch_box_411_nonnegative, ?_⟩
  intro z hz; exact leaf_411_sound hz

theorem leaf_412_ok : checkAt 527 1000 box_412 cert_412 = true := by
  have h := List.all_eq_true.mp batch_08_07_ok accepted_412 (by simp [batch_08_07_values])
  exact h
theorem leaf_412_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_412.profileLo box_412.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_412_ok
theorem branch_box_412_nonnegative : ∀ j, 0 ≤ branch_box_412.lower j ∧ 0 ≤ branch_box_412.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_412, Box.profileLo, Box.profileHi, box_412]
theorem leaf_412_BranchSafe : CertificateConsequences.BranchSafe branch_box_412 := by
  left; refine ⟨branch_box_412_nonnegative, ?_⟩
  intro z hz; exact leaf_412_sound hz

theorem leaf_417_ok : checkAt 527 1000 box_417 cert_417 = true := by
  have h := List.all_eq_true.mp batch_08_08_ok accepted_417 (by simp [batch_08_08_values])
  exact h
theorem leaf_417_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_417.profileLo box_417.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_417_ok
theorem branch_box_417_nonnegative : ∀ j, 0 ≤ branch_box_417.lower j ∧ 0 ≤ branch_box_417.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_417, Box.profileLo, Box.profileHi, box_417]
theorem leaf_417_BranchSafe : CertificateConsequences.BranchSafe branch_box_417 := by
  left; refine ⟨branch_box_417_nonnegative, ?_⟩
  intro z hz; exact leaf_417_sound hz

theorem leaf_418_ok : checkAt 527 1000 box_418 cert_418 = true := by
  have h := List.all_eq_true.mp batch_08_09_ok accepted_418 (by simp [batch_08_09_values])
  exact h
theorem leaf_418_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_418.profileLo box_418.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_418_ok
theorem branch_box_418_nonnegative : ∀ j, 0 ≤ branch_box_418.lower j ∧ 0 ≤ branch_box_418.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_418, Box.profileLo, Box.profileHi, box_418]
theorem leaf_418_BranchSafe : CertificateConsequences.BranchSafe branch_box_418 := by
  left; refine ⟨branch_box_418_nonnegative, ?_⟩
  intro z hz; exact leaf_418_sound hz

theorem leaf_419_ok : checkAt 527 1000 box_419 cert_419 = true := by
  have h := List.all_eq_true.mp batch_08_10_ok accepted_419 (by simp [batch_08_10_values])
  exact h
theorem leaf_419_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_419.profileLo box_419.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_419_ok
theorem branch_box_419_nonnegative : ∀ j, 0 ≤ branch_box_419.lower j ∧ 0 ≤ branch_box_419.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_419, Box.profileLo, Box.profileHi, box_419]
theorem leaf_419_BranchSafe : CertificateConsequences.BranchSafe branch_box_419 := by
  left; refine ⟨branch_box_419_nonnegative, ?_⟩
  intro z hz; exact leaf_419_sound hz

theorem leaf_421_ok : checkAt 527 1000 box_421 cert_421 = true := by
  have h := List.all_eq_true.mp batch_08_11_ok accepted_421 (by simp [batch_08_11_values])
  exact h
theorem leaf_421_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_421.profileLo box_421.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_421_ok
theorem branch_box_421_nonnegative : ∀ j, 0 ≤ branch_box_421.lower j ∧ 0 ≤ branch_box_421.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_421, Box.profileLo, Box.profileHi, box_421]
theorem leaf_421_BranchSafe : CertificateConsequences.BranchSafe branch_box_421 := by
  left; refine ⟨branch_box_421_nonnegative, ?_⟩
  intro z hz; exact leaf_421_sound hz

theorem leaf_422_ok : checkAt 527 1000 box_422 cert_422 = true := by
  have h := List.all_eq_true.mp batch_08_12_ok accepted_422 (by simp [batch_08_12_values])
  exact h
theorem leaf_422_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_422.profileLo box_422.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_422_ok
theorem branch_box_422_nonnegative : ∀ j, 0 ≤ branch_box_422.lower j ∧ 0 ≤ branch_box_422.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_422, Box.profileLo, Box.profileHi, box_422]
theorem leaf_422_BranchSafe : CertificateConsequences.BranchSafe branch_box_422 := by
  left; refine ⟨branch_box_422_nonnegative, ?_⟩
  intro z hz; exact leaf_422_sound hz

theorem leaf_423_ok : checkAt 527 1000 box_423 cert_423 = true := by
  have h := List.all_eq_true.mp batch_08_13_ok accepted_423 (by simp [batch_08_13_values])
  exact h
theorem leaf_423_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_423.profileLo box_423.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_423_ok
theorem branch_box_423_nonnegative : ∀ j, 0 ≤ branch_box_423.lower j ∧ 0 ≤ branch_box_423.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_423, Box.profileLo, Box.profileHi, box_423]
theorem leaf_423_BranchSafe : CertificateConsequences.BranchSafe branch_box_423 := by
  left; refine ⟨branch_box_423_nonnegative, ?_⟩
  intro z hz; exact leaf_423_sound hz

theorem leaf_427_ok : checkAt 527 1000 box_427 cert_427 = true := by
  have h := List.all_eq_true.mp batch_08_14_ok accepted_427 (by simp [batch_08_14_values])
  exact h
theorem leaf_427_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_427.profileLo box_427.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_427_ok
theorem branch_box_427_nonnegative : ∀ j, 0 ≤ branch_box_427.lower j ∧ 0 ≤ branch_box_427.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_427, Box.profileLo, Box.profileHi, box_427]
theorem leaf_427_BranchSafe : CertificateConsequences.BranchSafe branch_box_427 := by
  left; refine ⟨branch_box_427_nonnegative, ?_⟩
  intro z hz; exact leaf_427_sound hz

theorem leaf_428_ok : checkAt 527 1000 box_428 cert_428 = true := by
  have h := List.all_eq_true.mp batch_08_15_ok accepted_428 (by simp [batch_08_15_values])
  exact h
theorem leaf_428_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_428.profileLo box_428.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_428_ok
theorem branch_box_428_nonnegative : ∀ j, 0 ≤ branch_box_428.lower j ∧ 0 ≤ branch_box_428.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_428, Box.profileLo, Box.profileHi, box_428]
theorem leaf_428_BranchSafe : CertificateConsequences.BranchSafe branch_box_428 := by
  left; refine ⟨branch_box_428_nonnegative, ?_⟩
  intro z hz; exact leaf_428_sound hz

theorem leaf_429_ok : checkAt 527 1000 box_429 cert_429 = true := by
  have h := List.all_eq_true.mp batch_08_16_ok accepted_429 (by simp [batch_08_16_values])
  exact h
theorem leaf_429_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_429.profileLo box_429.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_429_ok
theorem branch_box_429_nonnegative : ∀ j, 0 ≤ branch_box_429.lower j ∧ 0 ≤ branch_box_429.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_429, Box.profileLo, Box.profileHi, box_429]
theorem leaf_429_BranchSafe : CertificateConsequences.BranchSafe branch_box_429 := by
  left; refine ⟨branch_box_429_nonnegative, ?_⟩
  intro z hz; exact leaf_429_sound hz

theorem leaf_430_ok : checkAt 527 1000 box_430 cert_430 = true := by
  have h := List.all_eq_true.mp batch_08_17_ok accepted_430 (by simp [batch_08_17_values])
  exact h
theorem leaf_430_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_430.profileLo box_430.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_430_ok
theorem branch_box_430_nonnegative : ∀ j, 0 ≤ branch_box_430.lower j ∧ 0 ≤ branch_box_430.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_430, Box.profileLo, Box.profileHi, box_430]
theorem leaf_430_BranchSafe : CertificateConsequences.BranchSafe branch_box_430 := by
  left; refine ⟨branch_box_430_nonnegative, ?_⟩
  intro z hz; exact leaf_430_sound hz

theorem leaf_435_ok : checkAt 527 1000 box_435 cert_435 = true := by
  have h := List.all_eq_true.mp batch_08_18_ok accepted_435 (by simp [batch_08_18_values])
  exact h
theorem leaf_435_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_435.profileLo box_435.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_435_ok
theorem branch_box_435_nonnegative : ∀ j, 0 ≤ branch_box_435.lower j ∧ 0 ≤ branch_box_435.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_435, Box.profileLo, Box.profileHi, box_435]
theorem leaf_435_BranchSafe : CertificateConsequences.BranchSafe branch_box_435 := by
  left; refine ⟨branch_box_435_nonnegative, ?_⟩
  intro z hz; exact leaf_435_sound hz

theorem leaf_436_ok : checkAt 527 1000 box_436 cert_436 = true := by
  have h := List.all_eq_true.mp batch_08_19_ok accepted_436 (by simp [batch_08_19_values])
  exact h
theorem leaf_436_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_436.profileLo box_436.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_436_ok
theorem branch_box_436_nonnegative : ∀ j, 0 ≤ branch_box_436.lower j ∧ 0 ≤ branch_box_436.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_436, Box.profileLo, Box.profileHi, box_436]
theorem leaf_436_BranchSafe : CertificateConsequences.BranchSafe branch_box_436 := by
  left; refine ⟨branch_box_436_nonnegative, ?_⟩
  intro z hz; exact leaf_436_sound hz

theorem leaf_439_ok : checkAt 527 1000 box_439 cert_439 = true := by
  have h := List.all_eq_true.mp batch_08_20_ok accepted_439 (by simp [batch_08_20_values])
  exact h
theorem leaf_439_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_439.profileLo box_439.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_439_ok
theorem branch_box_439_nonnegative : ∀ j, 0 ≤ branch_box_439.lower j ∧ 0 ≤ branch_box_439.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_439, Box.profileLo, Box.profileHi, box_439]
theorem leaf_439_BranchSafe : CertificateConsequences.BranchSafe branch_box_439 := by
  left; refine ⟨branch_box_439_nonnegative, ?_⟩
  intro z hz; exact leaf_439_sound hz

theorem leaf_441_ok : checkAt 527 1000 box_441 cert_441 = true := by
  have h := List.all_eq_true.mp batch_08_21_ok accepted_441 (by simp [batch_08_21_values])
  exact h
theorem leaf_441_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_441.profileLo box_441.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_441_ok
theorem branch_box_441_nonnegative : ∀ j, 0 ≤ branch_box_441.lower j ∧ 0 ≤ branch_box_441.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_441, Box.profileLo, Box.profileHi, box_441]
theorem leaf_441_BranchSafe : CertificateConsequences.BranchSafe branch_box_441 := by
  left; refine ⟨branch_box_441_nonnegative, ?_⟩
  intro z hz; exact leaf_441_sound hz

theorem leaf_442_ok : checkAt 527 1000 box_442 cert_442 = true := by
  have h := List.all_eq_true.mp batch_08_22_ok accepted_442 (by simp [batch_08_22_values])
  exact h
theorem leaf_442_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_442.profileLo box_442.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_442_ok
theorem branch_box_442_nonnegative : ∀ j, 0 ≤ branch_box_442.lower j ∧ 0 ≤ branch_box_442.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_442, Box.profileLo, Box.profileHi, box_442]
theorem leaf_442_BranchSafe : CertificateConsequences.BranchSafe branch_box_442 := by
  left; refine ⟨branch_box_442_nonnegative, ?_⟩
  intro z hz; exact leaf_442_sound hz

theorem leaf_443_ok : checkAt 527 1000 box_443 cert_443 = true := by
  have h := List.all_eq_true.mp batch_08_23_ok accepted_443 (by simp [batch_08_23_values])
  exact h
theorem leaf_443_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_443.profileLo box_443.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_443_ok
theorem branch_box_443_nonnegative : ∀ j, 0 ≤ branch_box_443.lower j ∧ 0 ≤ branch_box_443.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_443, Box.profileLo, Box.profileHi, box_443]
theorem leaf_443_BranchSafe : CertificateConsequences.BranchSafe branch_box_443 := by
  left; refine ⟨branch_box_443_nonnegative, ?_⟩
  intro z hz; exact leaf_443_sound hz

theorem leaf_445_ok : checkAt 527 1000 box_445 cert_445 = true := by
  have h := List.all_eq_true.mp batch_08_24_ok accepted_445 (by simp [batch_08_24_values])
  exact h
theorem leaf_445_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_445.profileLo box_445.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_445_ok
theorem branch_box_445_nonnegative : ∀ j, 0 ≤ branch_box_445.lower j ∧ 0 ≤ branch_box_445.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_445, Box.profileLo, Box.profileHi, box_445]
theorem leaf_445_BranchSafe : CertificateConsequences.BranchSafe branch_box_445 := by
  left; refine ⟨branch_box_445_nonnegative, ?_⟩
  intro z hz; exact leaf_445_sound hz

theorem leaf_447_ok : checkAt 527 1000 box_447 cert_447 = true := by
  have h := List.all_eq_true.mp batch_08_25_ok accepted_447 (by simp [batch_08_25_values])
  exact h
theorem leaf_447_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_447.profileLo box_447.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_447_ok
theorem branch_box_447_nonnegative : ∀ j, 0 ≤ branch_box_447.lower j ∧ 0 ≤ branch_box_447.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_447, Box.profileLo, Box.profileHi, box_447]
theorem leaf_447_BranchSafe : CertificateConsequences.BranchSafe branch_box_447 := by
  left; refine ⟨branch_box_447_nonnegative, ?_⟩
  intro z hz; exact leaf_447_sound hz

theorem leaf_449_ok : checkAt 527 1000 box_449 cert_449 = true := by
  have h := List.all_eq_true.mp batch_08_26_ok accepted_449 (by simp [batch_08_26_values])
  exact h
theorem leaf_449_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_449.profileLo box_449.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_449_ok
theorem branch_box_449_nonnegative : ∀ j, 0 ≤ branch_box_449.lower j ∧ 0 ≤ branch_box_449.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_449, Box.profileLo, Box.profileHi, box_449]
theorem leaf_449_BranchSafe : CertificateConsequences.BranchSafe branch_box_449 := by
  left; refine ⟨branch_box_449_nonnegative, ?_⟩
  intro z hz; exact leaf_449_sound hz

#print axioms batch_08_00_ok
#print axioms leaf_400_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
