import PeaceableQueens.UpperBound.Generated.Even.C527Scaled69Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_69_00_values : List Bool := [accepted_3451]
theorem batch_69_00_ok : batch_69_00_values.all id = true := by decide

def batch_69_01_values : List Bool := [accepted_3452]
theorem batch_69_01_ok : batch_69_01_values.all id = true := by decide

def batch_69_02_values : List Bool := [accepted_3455]
theorem batch_69_02_ok : batch_69_02_values.all id = true := by decide

def batch_69_03_values : List Bool := [accepted_3457]
theorem batch_69_03_ok : batch_69_03_values.all id = true := by decide

def batch_69_04_values : List Bool := [accepted_3458]
theorem batch_69_04_ok : batch_69_04_values.all id = true := by decide

def batch_69_05_values : List Bool := [accepted_3459]
theorem batch_69_05_ok : batch_69_05_values.all id = true := by decide

def batch_69_06_values : List Bool := [accepted_3461]
theorem batch_69_06_ok : batch_69_06_values.all id = true := by decide

def batch_69_07_values : List Bool := [accepted_3462]
theorem batch_69_07_ok : batch_69_07_values.all id = true := by decide

def batch_69_08_values : List Bool := [accepted_3467]
theorem batch_69_08_ok : batch_69_08_values.all id = true := by decide

def batch_69_09_values : List Bool := [accepted_3468]
theorem batch_69_09_ok : batch_69_09_values.all id = true := by decide

def batch_69_10_values : List Bool := [accepted_3469]
theorem batch_69_10_ok : batch_69_10_values.all id = true := by decide

def batch_69_11_values : List Bool := [accepted_3471]
theorem batch_69_11_ok : batch_69_11_values.all id = true := by decide

def batch_69_12_values : List Bool := [accepted_3472]
theorem batch_69_12_ok : batch_69_12_values.all id = true := by decide

def batch_69_13_values : List Bool := [accepted_3477]
theorem batch_69_13_ok : batch_69_13_values.all id = true := by decide

def batch_69_14_values : List Bool := [accepted_3478]
theorem batch_69_14_ok : batch_69_14_values.all id = true := by decide

def batch_69_15_values : List Bool := [accepted_3479]
theorem batch_69_15_ok : batch_69_15_values.all id = true := by decide

def batch_69_16_values : List Bool := [accepted_3480]
theorem batch_69_16_ok : batch_69_16_values.all id = true := by decide

def batch_69_17_values : List Bool := [accepted_3481]
theorem batch_69_17_ok : batch_69_17_values.all id = true := by decide

def batch_69_18_values : List Bool := [accepted_3483]
theorem batch_69_18_ok : batch_69_18_values.all id = true := by decide

def batch_69_19_values : List Bool := [accepted_3485]
theorem batch_69_19_ok : batch_69_19_values.all id = true := by decide

def batch_69_20_values : List Bool := [accepted_3486]
theorem batch_69_20_ok : batch_69_20_values.all id = true := by decide

def batch_69_21_values : List Bool := [accepted_3492]
theorem batch_69_21_ok : batch_69_21_values.all id = true := by decide

def batch_69_22_values : List Bool := [accepted_3493]
theorem batch_69_22_ok : batch_69_22_values.all id = true := by decide

def batch_69_23_values : List Bool := [accepted_3494]
theorem batch_69_23_ok : batch_69_23_values.all id = true := by decide

def batch_69_24_values : List Bool := [accepted_3496]
theorem batch_69_24_ok : batch_69_24_values.all id = true := by decide

def batch_69_25_values : List Bool := [accepted_3498]
theorem batch_69_25_ok : batch_69_25_values.all id = true := by decide

def batch_69_26_values : List Bool := [accepted_3499]
theorem batch_69_26_ok : batch_69_26_values.all id = true := by decide

theorem leaf_3451_ok : checkAt 527 1000 box_3451 cert_3451 = true := by
  have h := List.all_eq_true.mp batch_69_00_ok accepted_3451 (by simp [batch_69_00_values])
  exact h
theorem leaf_3451_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3451.profileLo box_3451.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3451_ok
theorem branch_box_3451_nonnegative : ∀ j, 0 ≤ branch_box_3451.lower j ∧ 0 ≤ branch_box_3451.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3451, Box.profileLo, Box.profileHi, box_3451]
theorem leaf_3451_BranchSafe : CertificateConsequences.BranchSafe branch_box_3451 := by
  left; refine ⟨branch_box_3451_nonnegative, ?_⟩
  intro z hz; exact leaf_3451_sound hz

theorem leaf_3452_ok : checkAt 527 1000 box_3452 cert_3452 = true := by
  have h := List.all_eq_true.mp batch_69_01_ok accepted_3452 (by simp [batch_69_01_values])
  exact h
theorem leaf_3452_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3452.profileLo box_3452.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3452_ok
theorem branch_box_3452_nonnegative : ∀ j, 0 ≤ branch_box_3452.lower j ∧ 0 ≤ branch_box_3452.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3452, Box.profileLo, Box.profileHi, box_3452]
theorem leaf_3452_BranchSafe : CertificateConsequences.BranchSafe branch_box_3452 := by
  left; refine ⟨branch_box_3452_nonnegative, ?_⟩
  intro z hz; exact leaf_3452_sound hz

theorem leaf_3455_ok : checkAt 527 1000 box_3455 cert_3455 = true := by
  have h := List.all_eq_true.mp batch_69_02_ok accepted_3455 (by simp [batch_69_02_values])
  exact h
theorem leaf_3455_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3455.profileLo box_3455.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3455_ok
theorem branch_box_3455_nonnegative : ∀ j, 0 ≤ branch_box_3455.lower j ∧ 0 ≤ branch_box_3455.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3455, Box.profileLo, Box.profileHi, box_3455]
theorem leaf_3455_BranchSafe : CertificateConsequences.BranchSafe branch_box_3455 := by
  left; refine ⟨branch_box_3455_nonnegative, ?_⟩
  intro z hz; exact leaf_3455_sound hz

theorem leaf_3457_ok : checkAt 527 1000 box_3457 cert_3457 = true := by
  have h := List.all_eq_true.mp batch_69_03_ok accepted_3457 (by simp [batch_69_03_values])
  exact h
theorem leaf_3457_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3457.profileLo box_3457.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3457_ok
theorem branch_box_3457_nonnegative : ∀ j, 0 ≤ branch_box_3457.lower j ∧ 0 ≤ branch_box_3457.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3457, Box.profileLo, Box.profileHi, box_3457]
theorem leaf_3457_BranchSafe : CertificateConsequences.BranchSafe branch_box_3457 := by
  left; refine ⟨branch_box_3457_nonnegative, ?_⟩
  intro z hz; exact leaf_3457_sound hz

theorem leaf_3458_ok : checkAt 527 1000 box_3458 cert_3458 = true := by
  have h := List.all_eq_true.mp batch_69_04_ok accepted_3458 (by simp [batch_69_04_values])
  exact h
theorem leaf_3458_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3458.profileLo box_3458.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3458_ok
theorem branch_box_3458_nonnegative : ∀ j, 0 ≤ branch_box_3458.lower j ∧ 0 ≤ branch_box_3458.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3458, Box.profileLo, Box.profileHi, box_3458]
theorem leaf_3458_BranchSafe : CertificateConsequences.BranchSafe branch_box_3458 := by
  left; refine ⟨branch_box_3458_nonnegative, ?_⟩
  intro z hz; exact leaf_3458_sound hz

theorem leaf_3459_ok : checkAt 527 1000 box_3459 cert_3459 = true := by
  have h := List.all_eq_true.mp batch_69_05_ok accepted_3459 (by simp [batch_69_05_values])
  exact h
theorem leaf_3459_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3459.profileLo box_3459.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3459_ok
theorem branch_box_3459_nonnegative : ∀ j, 0 ≤ branch_box_3459.lower j ∧ 0 ≤ branch_box_3459.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3459, Box.profileLo, Box.profileHi, box_3459]
theorem leaf_3459_BranchSafe : CertificateConsequences.BranchSafe branch_box_3459 := by
  left; refine ⟨branch_box_3459_nonnegative, ?_⟩
  intro z hz; exact leaf_3459_sound hz

theorem leaf_3461_ok : checkAt 527 1000 box_3461 cert_3461 = true := by
  have h := List.all_eq_true.mp batch_69_06_ok accepted_3461 (by simp [batch_69_06_values])
  exact h
theorem leaf_3461_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3461.profileLo box_3461.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3461_ok
theorem branch_box_3461_nonnegative : ∀ j, 0 ≤ branch_box_3461.lower j ∧ 0 ≤ branch_box_3461.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3461, Box.profileLo, Box.profileHi, box_3461]
theorem leaf_3461_BranchSafe : CertificateConsequences.BranchSafe branch_box_3461 := by
  left; refine ⟨branch_box_3461_nonnegative, ?_⟩
  intro z hz; exact leaf_3461_sound hz

theorem leaf_3462_ok : checkAt 527 1000 box_3462 cert_3462 = true := by
  have h := List.all_eq_true.mp batch_69_07_ok accepted_3462 (by simp [batch_69_07_values])
  exact h
theorem leaf_3462_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3462.profileLo box_3462.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3462_ok
theorem branch_box_3462_nonnegative : ∀ j, 0 ≤ branch_box_3462.lower j ∧ 0 ≤ branch_box_3462.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3462, Box.profileLo, Box.profileHi, box_3462]
theorem leaf_3462_BranchSafe : CertificateConsequences.BranchSafe branch_box_3462 := by
  left; refine ⟨branch_box_3462_nonnegative, ?_⟩
  intro z hz; exact leaf_3462_sound hz

theorem leaf_3467_ok : checkAt 527 1000 box_3467 cert_3467 = true := by
  have h := List.all_eq_true.mp batch_69_08_ok accepted_3467 (by simp [batch_69_08_values])
  exact h
theorem leaf_3467_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3467.profileLo box_3467.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3467_ok
theorem branch_box_3467_nonnegative : ∀ j, 0 ≤ branch_box_3467.lower j ∧ 0 ≤ branch_box_3467.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3467, Box.profileLo, Box.profileHi, box_3467]
theorem leaf_3467_BranchSafe : CertificateConsequences.BranchSafe branch_box_3467 := by
  left; refine ⟨branch_box_3467_nonnegative, ?_⟩
  intro z hz; exact leaf_3467_sound hz

theorem leaf_3468_ok : checkAt 527 1000 box_3468 cert_3468 = true := by
  have h := List.all_eq_true.mp batch_69_09_ok accepted_3468 (by simp [batch_69_09_values])
  exact h
theorem leaf_3468_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3468.profileLo box_3468.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3468_ok
theorem branch_box_3468_nonnegative : ∀ j, 0 ≤ branch_box_3468.lower j ∧ 0 ≤ branch_box_3468.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3468, Box.profileLo, Box.profileHi, box_3468]
theorem leaf_3468_BranchSafe : CertificateConsequences.BranchSafe branch_box_3468 := by
  left; refine ⟨branch_box_3468_nonnegative, ?_⟩
  intro z hz; exact leaf_3468_sound hz

theorem leaf_3469_ok : checkAt 527 1000 box_3469 cert_3469 = true := by
  have h := List.all_eq_true.mp batch_69_10_ok accepted_3469 (by simp [batch_69_10_values])
  exact h
theorem leaf_3469_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3469.profileLo box_3469.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3469_ok
theorem branch_box_3469_nonnegative : ∀ j, 0 ≤ branch_box_3469.lower j ∧ 0 ≤ branch_box_3469.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3469, Box.profileLo, Box.profileHi, box_3469]
theorem leaf_3469_BranchSafe : CertificateConsequences.BranchSafe branch_box_3469 := by
  left; refine ⟨branch_box_3469_nonnegative, ?_⟩
  intro z hz; exact leaf_3469_sound hz

theorem leaf_3471_ok : checkAt 527 1000 box_3471 cert_3471 = true := by
  have h := List.all_eq_true.mp batch_69_11_ok accepted_3471 (by simp [batch_69_11_values])
  exact h
theorem leaf_3471_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3471.profileLo box_3471.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3471_ok
theorem branch_box_3471_nonnegative : ∀ j, 0 ≤ branch_box_3471.lower j ∧ 0 ≤ branch_box_3471.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3471, Box.profileLo, Box.profileHi, box_3471]
theorem leaf_3471_BranchSafe : CertificateConsequences.BranchSafe branch_box_3471 := by
  left; refine ⟨branch_box_3471_nonnegative, ?_⟩
  intro z hz; exact leaf_3471_sound hz

theorem leaf_3472_ok : checkAt 527 1000 box_3472 cert_3472 = true := by
  have h := List.all_eq_true.mp batch_69_12_ok accepted_3472 (by simp [batch_69_12_values])
  exact h
theorem leaf_3472_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3472.profileLo box_3472.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3472_ok
theorem branch_box_3472_nonnegative : ∀ j, 0 ≤ branch_box_3472.lower j ∧ 0 ≤ branch_box_3472.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3472, Box.profileLo, Box.profileHi, box_3472]
theorem leaf_3472_BranchSafe : CertificateConsequences.BranchSafe branch_box_3472 := by
  left; refine ⟨branch_box_3472_nonnegative, ?_⟩
  intro z hz; exact leaf_3472_sound hz

theorem leaf_3477_ok : checkAt 527 1000 box_3477 cert_3477 = true := by
  have h := List.all_eq_true.mp batch_69_13_ok accepted_3477 (by simp [batch_69_13_values])
  exact h
theorem leaf_3477_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3477.profileLo box_3477.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3477_ok
theorem branch_box_3477_nonnegative : ∀ j, 0 ≤ branch_box_3477.lower j ∧ 0 ≤ branch_box_3477.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3477, Box.profileLo, Box.profileHi, box_3477]
theorem leaf_3477_BranchSafe : CertificateConsequences.BranchSafe branch_box_3477 := by
  left; refine ⟨branch_box_3477_nonnegative, ?_⟩
  intro z hz; exact leaf_3477_sound hz

theorem leaf_3478_ok : checkAt 527 1000 box_3478 cert_3478 = true := by
  have h := List.all_eq_true.mp batch_69_14_ok accepted_3478 (by simp [batch_69_14_values])
  exact h
theorem leaf_3478_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3478.profileLo box_3478.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3478_ok
theorem branch_box_3478_nonnegative : ∀ j, 0 ≤ branch_box_3478.lower j ∧ 0 ≤ branch_box_3478.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3478, Box.profileLo, Box.profileHi, box_3478]
theorem leaf_3478_BranchSafe : CertificateConsequences.BranchSafe branch_box_3478 := by
  left; refine ⟨branch_box_3478_nonnegative, ?_⟩
  intro z hz; exact leaf_3478_sound hz

theorem leaf_3479_ok : checkAt 527 1000 box_3479 cert_3479 = true := by
  have h := List.all_eq_true.mp batch_69_15_ok accepted_3479 (by simp [batch_69_15_values])
  exact h
theorem leaf_3479_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3479.profileLo box_3479.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3479_ok
theorem branch_box_3479_nonnegative : ∀ j, 0 ≤ branch_box_3479.lower j ∧ 0 ≤ branch_box_3479.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3479, Box.profileLo, Box.profileHi, box_3479]
theorem leaf_3479_BranchSafe : CertificateConsequences.BranchSafe branch_box_3479 := by
  left; refine ⟨branch_box_3479_nonnegative, ?_⟩
  intro z hz; exact leaf_3479_sound hz

theorem leaf_3480_ok : checkAt 527 1000 box_3480 cert_3480 = true := by
  have h := List.all_eq_true.mp batch_69_16_ok accepted_3480 (by simp [batch_69_16_values])
  exact h
theorem leaf_3480_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3480.profileLo box_3480.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3480_ok
theorem branch_box_3480_nonnegative : ∀ j, 0 ≤ branch_box_3480.lower j ∧ 0 ≤ branch_box_3480.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3480, Box.profileLo, Box.profileHi, box_3480]
theorem leaf_3480_BranchSafe : CertificateConsequences.BranchSafe branch_box_3480 := by
  left; refine ⟨branch_box_3480_nonnegative, ?_⟩
  intro z hz; exact leaf_3480_sound hz

theorem leaf_3481_ok : checkAt 527 1000 box_3481 cert_3481 = true := by
  have h := List.all_eq_true.mp batch_69_17_ok accepted_3481 (by simp [batch_69_17_values])
  exact h
theorem leaf_3481_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3481.profileLo box_3481.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3481_ok
theorem branch_box_3481_nonnegative : ∀ j, 0 ≤ branch_box_3481.lower j ∧ 0 ≤ branch_box_3481.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3481, Box.profileLo, Box.profileHi, box_3481]
theorem leaf_3481_BranchSafe : CertificateConsequences.BranchSafe branch_box_3481 := by
  left; refine ⟨branch_box_3481_nonnegative, ?_⟩
  intro z hz; exact leaf_3481_sound hz

theorem leaf_3483_ok : checkAt 527 1000 box_3483 cert_3483 = true := by
  have h := List.all_eq_true.mp batch_69_18_ok accepted_3483 (by simp [batch_69_18_values])
  exact h
theorem leaf_3483_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3483.profileLo box_3483.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3483_ok
theorem branch_box_3483_nonnegative : ∀ j, 0 ≤ branch_box_3483.lower j ∧ 0 ≤ branch_box_3483.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3483, Box.profileLo, Box.profileHi, box_3483]
theorem leaf_3483_BranchSafe : CertificateConsequences.BranchSafe branch_box_3483 := by
  left; refine ⟨branch_box_3483_nonnegative, ?_⟩
  intro z hz; exact leaf_3483_sound hz

theorem leaf_3485_ok : checkAt 527 1000 box_3485 cert_3485 = true := by
  have h := List.all_eq_true.mp batch_69_19_ok accepted_3485 (by simp [batch_69_19_values])
  exact h
theorem leaf_3485_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3485.profileLo box_3485.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3485_ok
theorem branch_box_3485_nonnegative : ∀ j, 0 ≤ branch_box_3485.lower j ∧ 0 ≤ branch_box_3485.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3485, Box.profileLo, Box.profileHi, box_3485]
theorem leaf_3485_BranchSafe : CertificateConsequences.BranchSafe branch_box_3485 := by
  left; refine ⟨branch_box_3485_nonnegative, ?_⟩
  intro z hz; exact leaf_3485_sound hz

theorem leaf_3486_ok : checkAt 527 1000 box_3486 cert_3486 = true := by
  have h := List.all_eq_true.mp batch_69_20_ok accepted_3486 (by simp [batch_69_20_values])
  exact h
theorem leaf_3486_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3486.profileLo box_3486.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3486_ok
theorem branch_box_3486_nonnegative : ∀ j, 0 ≤ branch_box_3486.lower j ∧ 0 ≤ branch_box_3486.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3486, Box.profileLo, Box.profileHi, box_3486]
theorem leaf_3486_BranchSafe : CertificateConsequences.BranchSafe branch_box_3486 := by
  left; refine ⟨branch_box_3486_nonnegative, ?_⟩
  intro z hz; exact leaf_3486_sound hz

theorem leaf_3492_ok : checkAt 527 1000 box_3492 cert_3492 = true := by
  have h := List.all_eq_true.mp batch_69_21_ok accepted_3492 (by simp [batch_69_21_values])
  exact h
theorem leaf_3492_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3492.profileLo box_3492.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3492_ok
theorem branch_box_3492_nonnegative : ∀ j, 0 ≤ branch_box_3492.lower j ∧ 0 ≤ branch_box_3492.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3492, Box.profileLo, Box.profileHi, box_3492]
theorem leaf_3492_BranchSafe : CertificateConsequences.BranchSafe branch_box_3492 := by
  left; refine ⟨branch_box_3492_nonnegative, ?_⟩
  intro z hz; exact leaf_3492_sound hz

theorem leaf_3493_ok : checkAt 527 1000 box_3493 cert_3493 = true := by
  have h := List.all_eq_true.mp batch_69_22_ok accepted_3493 (by simp [batch_69_22_values])
  exact h
theorem leaf_3493_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3493.profileLo box_3493.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3493_ok
theorem branch_box_3493_nonnegative : ∀ j, 0 ≤ branch_box_3493.lower j ∧ 0 ≤ branch_box_3493.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3493, Box.profileLo, Box.profileHi, box_3493]
theorem leaf_3493_BranchSafe : CertificateConsequences.BranchSafe branch_box_3493 := by
  left; refine ⟨branch_box_3493_nonnegative, ?_⟩
  intro z hz; exact leaf_3493_sound hz

theorem leaf_3494_ok : checkAt 527 1000 box_3494 cert_3494 = true := by
  have h := List.all_eq_true.mp batch_69_23_ok accepted_3494 (by simp [batch_69_23_values])
  exact h
theorem leaf_3494_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3494.profileLo box_3494.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3494_ok
theorem branch_box_3494_nonnegative : ∀ j, 0 ≤ branch_box_3494.lower j ∧ 0 ≤ branch_box_3494.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3494, Box.profileLo, Box.profileHi, box_3494]
theorem leaf_3494_BranchSafe : CertificateConsequences.BranchSafe branch_box_3494 := by
  left; refine ⟨branch_box_3494_nonnegative, ?_⟩
  intro z hz; exact leaf_3494_sound hz

theorem leaf_3496_ok : checkAt 527 1000 box_3496 cert_3496 = true := by
  have h := List.all_eq_true.mp batch_69_24_ok accepted_3496 (by simp [batch_69_24_values])
  exact h
theorem leaf_3496_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3496.profileLo box_3496.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3496_ok
theorem branch_box_3496_nonnegative : ∀ j, 0 ≤ branch_box_3496.lower j ∧ 0 ≤ branch_box_3496.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3496, Box.profileLo, Box.profileHi, box_3496]
theorem leaf_3496_BranchSafe : CertificateConsequences.BranchSafe branch_box_3496 := by
  left; refine ⟨branch_box_3496_nonnegative, ?_⟩
  intro z hz; exact leaf_3496_sound hz

theorem leaf_3498_ok : checkAt 527 1000 box_3498 cert_3498 = true := by
  have h := List.all_eq_true.mp batch_69_25_ok accepted_3498 (by simp [batch_69_25_values])
  exact h
theorem leaf_3498_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3498.profileLo box_3498.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3498_ok
theorem branch_box_3498_nonnegative : ∀ j, 0 ≤ branch_box_3498.lower j ∧ 0 ≤ branch_box_3498.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3498, Box.profileLo, Box.profileHi, box_3498]
theorem leaf_3498_BranchSafe : CertificateConsequences.BranchSafe branch_box_3498 := by
  left; refine ⟨branch_box_3498_nonnegative, ?_⟩
  intro z hz; exact leaf_3498_sound hz

theorem leaf_3499_ok : checkAt 527 1000 box_3499 cert_3499 = true := by
  have h := List.all_eq_true.mp batch_69_26_ok accepted_3499 (by simp [batch_69_26_values])
  exact h
theorem leaf_3499_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3499.profileLo box_3499.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3499_ok
theorem branch_box_3499_nonnegative : ∀ j, 0 ≤ branch_box_3499.lower j ∧ 0 ≤ branch_box_3499.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3499, Box.profileLo, Box.profileHi, box_3499]
theorem leaf_3499_BranchSafe : CertificateConsequences.BranchSafe branch_box_3499 := by
  left; refine ⟨branch_box_3499_nonnegative, ?_⟩
  intro z hz; exact leaf_3499_sound hz

#print axioms batch_69_00_ok
#print axioms leaf_3451_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
