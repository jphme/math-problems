import PeaceableQueens.UpperBound.Generated.Even.C527Scaled10Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_10_00_values : List Bool := [accepted_501]
theorem batch_10_00_ok : batch_10_00_values.all id = true := by decide

def batch_10_01_values : List Bool := [accepted_503]
theorem batch_10_01_ok : batch_10_01_values.all id = true := by decide

def batch_10_02_values : List Bool := [accepted_505]
theorem batch_10_02_ok : batch_10_02_values.all id = true := by decide

def batch_10_03_values : List Bool := [accepted_506]
theorem batch_10_03_ok : batch_10_03_values.all id = true := by decide

def batch_10_04_values : List Bool := [accepted_507]
theorem batch_10_04_ok : batch_10_04_values.all id = true := by decide

def batch_10_05_values : List Bool := [accepted_508]
theorem batch_10_05_ok : batch_10_05_values.all id = true := by decide

def batch_10_06_values : List Bool := [accepted_515]
theorem batch_10_06_ok : batch_10_06_values.all id = true := by decide

def batch_10_07_values : List Bool := [accepted_517]
theorem batch_10_07_ok : batch_10_07_values.all id = true := by decide

def batch_10_08_values : List Bool := [accepted_519]
theorem batch_10_08_ok : batch_10_08_values.all id = true := by decide

def batch_10_09_values : List Bool := [accepted_520]
theorem batch_10_09_ok : batch_10_09_values.all id = true := by decide

def batch_10_10_values : List Bool := [accepted_522]
theorem batch_10_10_ok : batch_10_10_values.all id = true := by decide

def batch_10_11_values : List Bool := [accepted_525]
theorem batch_10_11_ok : batch_10_11_values.all id = true := by decide

def batch_10_12_values : List Bool := [accepted_526]
theorem batch_10_12_ok : batch_10_12_values.all id = true := by decide

def batch_10_13_values : List Bool := [accepted_527]
theorem batch_10_13_ok : batch_10_13_values.all id = true := by decide

def batch_10_14_values : List Bool := [accepted_528]
theorem batch_10_14_ok : batch_10_14_values.all id = true := by decide

def batch_10_15_values : List Bool := [accepted_530]
theorem batch_10_15_ok : batch_10_15_values.all id = true := by decide

def batch_10_16_values : List Bool := [accepted_533]
theorem batch_10_16_ok : batch_10_16_values.all id = true := by decide

def batch_10_17_values : List Bool := [accepted_534]
theorem batch_10_17_ok : batch_10_17_values.all id = true := by decide

def batch_10_18_values : List Bool := [accepted_535]
theorem batch_10_18_ok : batch_10_18_values.all id = true := by decide

def batch_10_19_values : List Bool := [accepted_536]
theorem batch_10_19_ok : batch_10_19_values.all id = true := by decide

def batch_10_20_values : List Bool := [accepted_542]
theorem batch_10_20_ok : batch_10_20_values.all id = true := by decide

def batch_10_21_values : List Bool := [accepted_543]
theorem batch_10_21_ok : batch_10_21_values.all id = true := by decide

def batch_10_22_values : List Bool := [accepted_545]
theorem batch_10_22_ok : batch_10_22_values.all id = true := by decide

def batch_10_23_values : List Bool := [accepted_546]
theorem batch_10_23_ok : batch_10_23_values.all id = true := by decide

theorem leaf_501_ok : checkAt 527 1000 box_501 cert_501 = true := by
  have h := List.all_eq_true.mp batch_10_00_ok accepted_501 (by simp [batch_10_00_values])
  exact h
theorem leaf_501_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_501.profileLo box_501.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_501_ok
theorem branch_box_501_nonnegative : ∀ j, 0 ≤ branch_box_501.lower j ∧ 0 ≤ branch_box_501.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_501, Box.profileLo, Box.profileHi, box_501]
theorem leaf_501_BranchSafe : CertificateConsequences.BranchSafe branch_box_501 := by
  left; refine ⟨branch_box_501_nonnegative, ?_⟩
  intro z hz; exact leaf_501_sound hz

theorem leaf_503_ok : checkAt 527 1000 box_503 cert_503 = true := by
  have h := List.all_eq_true.mp batch_10_01_ok accepted_503 (by simp [batch_10_01_values])
  exact h
theorem leaf_503_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_503.profileLo box_503.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_503_ok
theorem branch_box_503_nonnegative : ∀ j, 0 ≤ branch_box_503.lower j ∧ 0 ≤ branch_box_503.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_503, Box.profileLo, Box.profileHi, box_503]
theorem leaf_503_BranchSafe : CertificateConsequences.BranchSafe branch_box_503 := by
  left; refine ⟨branch_box_503_nonnegative, ?_⟩
  intro z hz; exact leaf_503_sound hz

theorem leaf_505_ok : checkAt 527 1000 box_505 cert_505 = true := by
  have h := List.all_eq_true.mp batch_10_02_ok accepted_505 (by simp [batch_10_02_values])
  exact h
theorem leaf_505_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_505.profileLo box_505.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_505_ok
theorem branch_box_505_nonnegative : ∀ j, 0 ≤ branch_box_505.lower j ∧ 0 ≤ branch_box_505.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_505, Box.profileLo, Box.profileHi, box_505]
theorem leaf_505_BranchSafe : CertificateConsequences.BranchSafe branch_box_505 := by
  left; refine ⟨branch_box_505_nonnegative, ?_⟩
  intro z hz; exact leaf_505_sound hz

theorem leaf_506_ok : checkAt 527 1000 box_506 cert_506 = true := by
  have h := List.all_eq_true.mp batch_10_03_ok accepted_506 (by simp [batch_10_03_values])
  exact h
theorem leaf_506_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_506.profileLo box_506.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_506_ok
theorem branch_box_506_nonnegative : ∀ j, 0 ≤ branch_box_506.lower j ∧ 0 ≤ branch_box_506.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_506, Box.profileLo, Box.profileHi, box_506]
theorem leaf_506_BranchSafe : CertificateConsequences.BranchSafe branch_box_506 := by
  left; refine ⟨branch_box_506_nonnegative, ?_⟩
  intro z hz; exact leaf_506_sound hz

theorem leaf_507_ok : checkAt 527 1000 box_507 cert_507 = true := by
  have h := List.all_eq_true.mp batch_10_04_ok accepted_507 (by simp [batch_10_04_values])
  exact h
theorem leaf_507_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_507.profileLo box_507.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_507_ok
theorem branch_box_507_nonnegative : ∀ j, 0 ≤ branch_box_507.lower j ∧ 0 ≤ branch_box_507.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_507, Box.profileLo, Box.profileHi, box_507]
theorem leaf_507_BranchSafe : CertificateConsequences.BranchSafe branch_box_507 := by
  left; refine ⟨branch_box_507_nonnegative, ?_⟩
  intro z hz; exact leaf_507_sound hz

theorem leaf_508_ok : checkAt 527 1000 box_508 cert_508 = true := by
  have h := List.all_eq_true.mp batch_10_05_ok accepted_508 (by simp [batch_10_05_values])
  exact h
theorem leaf_508_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_508.profileLo box_508.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_508_ok
theorem branch_box_508_nonnegative : ∀ j, 0 ≤ branch_box_508.lower j ∧ 0 ≤ branch_box_508.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_508, Box.profileLo, Box.profileHi, box_508]
theorem leaf_508_BranchSafe : CertificateConsequences.BranchSafe branch_box_508 := by
  left; refine ⟨branch_box_508_nonnegative, ?_⟩
  intro z hz; exact leaf_508_sound hz

theorem leaf_515_ok : checkAt 527 1000 box_515 cert_515 = true := by
  have h := List.all_eq_true.mp batch_10_06_ok accepted_515 (by simp [batch_10_06_values])
  exact h
theorem leaf_515_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_515.profileLo box_515.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_515_ok
theorem branch_box_515_nonnegative : ∀ j, 0 ≤ branch_box_515.lower j ∧ 0 ≤ branch_box_515.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_515, Box.profileLo, Box.profileHi, box_515]
theorem leaf_515_BranchSafe : CertificateConsequences.BranchSafe branch_box_515 := by
  left; refine ⟨branch_box_515_nonnegative, ?_⟩
  intro z hz; exact leaf_515_sound hz

theorem leaf_517_ok : checkAt 527 1000 box_517 cert_517 = true := by
  have h := List.all_eq_true.mp batch_10_07_ok accepted_517 (by simp [batch_10_07_values])
  exact h
theorem leaf_517_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_517.profileLo box_517.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_517_ok
theorem branch_box_517_nonnegative : ∀ j, 0 ≤ branch_box_517.lower j ∧ 0 ≤ branch_box_517.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_517, Box.profileLo, Box.profileHi, box_517]
theorem leaf_517_BranchSafe : CertificateConsequences.BranchSafe branch_box_517 := by
  left; refine ⟨branch_box_517_nonnegative, ?_⟩
  intro z hz; exact leaf_517_sound hz

theorem leaf_519_ok : checkAt 527 1000 box_519 cert_519 = true := by
  have h := List.all_eq_true.mp batch_10_08_ok accepted_519 (by simp [batch_10_08_values])
  exact h
theorem leaf_519_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_519.profileLo box_519.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_519_ok
theorem branch_box_519_nonnegative : ∀ j, 0 ≤ branch_box_519.lower j ∧ 0 ≤ branch_box_519.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_519, Box.profileLo, Box.profileHi, box_519]
theorem leaf_519_BranchSafe : CertificateConsequences.BranchSafe branch_box_519 := by
  left; refine ⟨branch_box_519_nonnegative, ?_⟩
  intro z hz; exact leaf_519_sound hz

theorem leaf_520_ok : checkAt 527 1000 box_520 cert_520 = true := by
  have h := List.all_eq_true.mp batch_10_09_ok accepted_520 (by simp [batch_10_09_values])
  exact h
theorem leaf_520_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_520.profileLo box_520.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_520_ok
theorem branch_box_520_nonnegative : ∀ j, 0 ≤ branch_box_520.lower j ∧ 0 ≤ branch_box_520.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_520, Box.profileLo, Box.profileHi, box_520]
theorem leaf_520_BranchSafe : CertificateConsequences.BranchSafe branch_box_520 := by
  left; refine ⟨branch_box_520_nonnegative, ?_⟩
  intro z hz; exact leaf_520_sound hz

theorem leaf_522_ok : checkAt 527 1000 box_522 cert_522 = true := by
  have h := List.all_eq_true.mp batch_10_10_ok accepted_522 (by simp [batch_10_10_values])
  exact h
theorem leaf_522_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_522.profileLo box_522.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_522_ok
theorem branch_box_522_nonnegative : ∀ j, 0 ≤ branch_box_522.lower j ∧ 0 ≤ branch_box_522.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_522, Box.profileLo, Box.profileHi, box_522]
theorem leaf_522_BranchSafe : CertificateConsequences.BranchSafe branch_box_522 := by
  left; refine ⟨branch_box_522_nonnegative, ?_⟩
  intro z hz; exact leaf_522_sound hz

theorem leaf_525_ok : checkAt 527 1000 box_525 cert_525 = true := by
  have h := List.all_eq_true.mp batch_10_11_ok accepted_525 (by simp [batch_10_11_values])
  exact h
theorem leaf_525_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_525.profileLo box_525.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_525_ok
theorem branch_box_525_nonnegative : ∀ j, 0 ≤ branch_box_525.lower j ∧ 0 ≤ branch_box_525.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_525, Box.profileLo, Box.profileHi, box_525]
theorem leaf_525_BranchSafe : CertificateConsequences.BranchSafe branch_box_525 := by
  left; refine ⟨branch_box_525_nonnegative, ?_⟩
  intro z hz; exact leaf_525_sound hz

theorem leaf_526_ok : checkAt 527 1000 box_526 cert_526 = true := by
  have h := List.all_eq_true.mp batch_10_12_ok accepted_526 (by simp [batch_10_12_values])
  exact h
theorem leaf_526_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_526.profileLo box_526.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_526_ok
theorem branch_box_526_nonnegative : ∀ j, 0 ≤ branch_box_526.lower j ∧ 0 ≤ branch_box_526.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_526, Box.profileLo, Box.profileHi, box_526]
theorem leaf_526_BranchSafe : CertificateConsequences.BranchSafe branch_box_526 := by
  left; refine ⟨branch_box_526_nonnegative, ?_⟩
  intro z hz; exact leaf_526_sound hz

theorem leaf_527_ok : checkAt 527 1000 box_527 cert_527 = true := by
  have h := List.all_eq_true.mp batch_10_13_ok accepted_527 (by simp [batch_10_13_values])
  exact h
theorem leaf_527_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_527.profileLo box_527.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_527_ok
theorem branch_box_527_nonnegative : ∀ j, 0 ≤ branch_box_527.lower j ∧ 0 ≤ branch_box_527.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_527, Box.profileLo, Box.profileHi, box_527]
theorem leaf_527_BranchSafe : CertificateConsequences.BranchSafe branch_box_527 := by
  left; refine ⟨branch_box_527_nonnegative, ?_⟩
  intro z hz; exact leaf_527_sound hz

theorem leaf_528_ok : checkAt 527 1000 box_528 cert_528 = true := by
  have h := List.all_eq_true.mp batch_10_14_ok accepted_528 (by simp [batch_10_14_values])
  exact h
theorem leaf_528_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_528.profileLo box_528.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_528_ok
theorem branch_box_528_nonnegative : ∀ j, 0 ≤ branch_box_528.lower j ∧ 0 ≤ branch_box_528.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_528, Box.profileLo, Box.profileHi, box_528]
theorem leaf_528_BranchSafe : CertificateConsequences.BranchSafe branch_box_528 := by
  left; refine ⟨branch_box_528_nonnegative, ?_⟩
  intro z hz; exact leaf_528_sound hz

theorem leaf_530_ok : checkAt 527 1000 box_530 cert_530 = true := by
  have h := List.all_eq_true.mp batch_10_15_ok accepted_530 (by simp [batch_10_15_values])
  exact h
theorem leaf_530_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_530.profileLo box_530.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_530_ok
theorem branch_box_530_nonnegative : ∀ j, 0 ≤ branch_box_530.lower j ∧ 0 ≤ branch_box_530.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_530, Box.profileLo, Box.profileHi, box_530]
theorem leaf_530_BranchSafe : CertificateConsequences.BranchSafe branch_box_530 := by
  left; refine ⟨branch_box_530_nonnegative, ?_⟩
  intro z hz; exact leaf_530_sound hz

theorem leaf_533_ok : checkAt 527 1000 box_533 cert_533 = true := by
  have h := List.all_eq_true.mp batch_10_16_ok accepted_533 (by simp [batch_10_16_values])
  exact h
theorem leaf_533_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_533.profileLo box_533.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_533_ok
theorem branch_box_533_nonnegative : ∀ j, 0 ≤ branch_box_533.lower j ∧ 0 ≤ branch_box_533.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_533, Box.profileLo, Box.profileHi, box_533]
theorem leaf_533_BranchSafe : CertificateConsequences.BranchSafe branch_box_533 := by
  left; refine ⟨branch_box_533_nonnegative, ?_⟩
  intro z hz; exact leaf_533_sound hz

theorem leaf_534_ok : checkAt 527 1000 box_534 cert_534 = true := by
  have h := List.all_eq_true.mp batch_10_17_ok accepted_534 (by simp [batch_10_17_values])
  exact h
theorem leaf_534_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_534.profileLo box_534.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_534_ok
theorem branch_box_534_nonnegative : ∀ j, 0 ≤ branch_box_534.lower j ∧ 0 ≤ branch_box_534.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_534, Box.profileLo, Box.profileHi, box_534]
theorem leaf_534_BranchSafe : CertificateConsequences.BranchSafe branch_box_534 := by
  left; refine ⟨branch_box_534_nonnegative, ?_⟩
  intro z hz; exact leaf_534_sound hz

theorem leaf_535_ok : checkAt 527 1000 box_535 cert_535 = true := by
  have h := List.all_eq_true.mp batch_10_18_ok accepted_535 (by simp [batch_10_18_values])
  exact h
theorem leaf_535_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_535.profileLo box_535.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_535_ok
theorem branch_box_535_nonnegative : ∀ j, 0 ≤ branch_box_535.lower j ∧ 0 ≤ branch_box_535.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_535, Box.profileLo, Box.profileHi, box_535]
theorem leaf_535_BranchSafe : CertificateConsequences.BranchSafe branch_box_535 := by
  left; refine ⟨branch_box_535_nonnegative, ?_⟩
  intro z hz; exact leaf_535_sound hz

theorem leaf_536_ok : checkAt 527 1000 box_536 cert_536 = true := by
  have h := List.all_eq_true.mp batch_10_19_ok accepted_536 (by simp [batch_10_19_values])
  exact h
theorem leaf_536_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_536.profileLo box_536.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_536_ok
theorem branch_box_536_nonnegative : ∀ j, 0 ≤ branch_box_536.lower j ∧ 0 ≤ branch_box_536.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_536, Box.profileLo, Box.profileHi, box_536]
theorem leaf_536_BranchSafe : CertificateConsequences.BranchSafe branch_box_536 := by
  left; refine ⟨branch_box_536_nonnegative, ?_⟩
  intro z hz; exact leaf_536_sound hz

theorem leaf_542_ok : checkAt 527 1000 box_542 cert_542 = true := by
  have h := List.all_eq_true.mp batch_10_20_ok accepted_542 (by simp [batch_10_20_values])
  exact h
theorem leaf_542_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_542.profileLo box_542.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_542_ok
theorem branch_box_542_nonnegative : ∀ j, 0 ≤ branch_box_542.lower j ∧ 0 ≤ branch_box_542.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_542, Box.profileLo, Box.profileHi, box_542]
theorem leaf_542_BranchSafe : CertificateConsequences.BranchSafe branch_box_542 := by
  left; refine ⟨branch_box_542_nonnegative, ?_⟩
  intro z hz; exact leaf_542_sound hz

theorem leaf_543_ok : checkAt 527 1000 box_543 cert_543 = true := by
  have h := List.all_eq_true.mp batch_10_21_ok accepted_543 (by simp [batch_10_21_values])
  exact h
theorem leaf_543_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_543.profileLo box_543.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_543_ok
theorem branch_box_543_nonnegative : ∀ j, 0 ≤ branch_box_543.lower j ∧ 0 ≤ branch_box_543.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_543, Box.profileLo, Box.profileHi, box_543]
theorem leaf_543_BranchSafe : CertificateConsequences.BranchSafe branch_box_543 := by
  left; refine ⟨branch_box_543_nonnegative, ?_⟩
  intro z hz; exact leaf_543_sound hz

theorem leaf_545_ok : checkAt 527 1000 box_545 cert_545 = true := by
  have h := List.all_eq_true.mp batch_10_22_ok accepted_545 (by simp [batch_10_22_values])
  exact h
theorem leaf_545_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_545.profileLo box_545.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_545_ok
theorem branch_box_545_nonnegative : ∀ j, 0 ≤ branch_box_545.lower j ∧ 0 ≤ branch_box_545.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_545, Box.profileLo, Box.profileHi, box_545]
theorem leaf_545_BranchSafe : CertificateConsequences.BranchSafe branch_box_545 := by
  left; refine ⟨branch_box_545_nonnegative, ?_⟩
  intro z hz; exact leaf_545_sound hz

theorem leaf_546_ok : checkAt 527 1000 box_546 cert_546 = true := by
  have h := List.all_eq_true.mp batch_10_23_ok accepted_546 (by simp [batch_10_23_values])
  exact h
theorem leaf_546_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_546.profileLo box_546.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_546_ok
theorem branch_box_546_nonnegative : ∀ j, 0 ≤ branch_box_546.lower j ∧ 0 ≤ branch_box_546.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_546, Box.profileLo, Box.profileHi, box_546]
theorem leaf_546_BranchSafe : CertificateConsequences.BranchSafe branch_box_546 := by
  left; refine ⟨branch_box_546_nonnegative, ?_⟩
  intro z hz; exact leaf_546_sound hz

#print axioms batch_10_00_ok
#print axioms leaf_501_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
