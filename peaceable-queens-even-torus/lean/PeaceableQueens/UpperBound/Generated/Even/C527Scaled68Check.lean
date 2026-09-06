import PeaceableQueens.UpperBound.Generated.Even.C527Scaled68Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
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

def batch_68_03_values : List Bool := [accepted_3404]
theorem batch_68_03_ok : batch_68_03_values.all id = true := by decide

def batch_68_04_values : List Bool := [accepted_3411]
theorem batch_68_04_ok : batch_68_04_values.all id = true := by decide

def batch_68_05_values : List Bool := [accepted_3412]
theorem batch_68_05_ok : batch_68_05_values.all id = true := by decide

def batch_68_06_values : List Bool := [accepted_3418]
theorem batch_68_06_ok : batch_68_06_values.all id = true := by decide

def batch_68_07_values : List Bool := [accepted_3419]
theorem batch_68_07_ok : batch_68_07_values.all id = true := by decide

def batch_68_08_values : List Bool := [accepted_3420]
theorem batch_68_08_ok : batch_68_08_values.all id = true := by decide

def batch_68_09_values : List Bool := [accepted_3423]
theorem batch_68_09_ok : batch_68_09_values.all id = true := by decide

def batch_68_10_values : List Bool := [accepted_3424]
theorem batch_68_10_ok : batch_68_10_values.all id = true := by decide

def batch_68_11_values : List Bool := [accepted_3425]
theorem batch_68_11_ok : batch_68_11_values.all id = true := by decide

def batch_68_12_values : List Bool := [accepted_3426]
theorem batch_68_12_ok : batch_68_12_values.all id = true := by decide

def batch_68_13_values : List Bool := [accepted_3427]
theorem batch_68_13_ok : batch_68_13_values.all id = true := by decide

def batch_68_14_values : List Bool := [accepted_3428]
theorem batch_68_14_ok : batch_68_14_values.all id = true := by decide

def batch_68_15_values : List Bool := [accepted_3433]
theorem batch_68_15_ok : batch_68_15_values.all id = true := by decide

def batch_68_16_values : List Bool := [accepted_3434]
theorem batch_68_16_ok : batch_68_16_values.all id = true := by decide

def batch_68_17_values : List Bool := [accepted_3439]
theorem batch_68_17_ok : batch_68_17_values.all id = true := by decide

def batch_68_18_values : List Bool := [accepted_3441]
theorem batch_68_18_ok : batch_68_18_values.all id = true := by decide

def batch_68_19_values : List Bool := [accepted_3442]
theorem batch_68_19_ok : batch_68_19_values.all id = true := by decide

def batch_68_20_values : List Bool := [accepted_3443]
theorem batch_68_20_ok : batch_68_20_values.all id = true := by decide

def batch_68_21_values : List Bool := [accepted_3444]
theorem batch_68_21_ok : batch_68_21_values.all id = true := by decide

def batch_68_22_values : List Bool := [accepted_3447]
theorem batch_68_22_ok : batch_68_22_values.all id = true := by decide

def batch_68_23_values : List Bool := [accepted_3448]
theorem batch_68_23_ok : batch_68_23_values.all id = true := by decide

def batch_68_24_values : List Bool := [accepted_3449]
theorem batch_68_24_ok : batch_68_24_values.all id = true := by decide

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

theorem leaf_3404_ok : checkAt 527 1000 box_3404 cert_3404 = true := by
  have h := List.all_eq_true.mp batch_68_03_ok accepted_3404 (by simp [batch_68_03_values])
  exact h
theorem leaf_3404_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3404.profileLo box_3404.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3404_ok
theorem branch_box_3404_nonnegative : ∀ j, 0 ≤ branch_box_3404.lower j ∧ 0 ≤ branch_box_3404.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3404, Box.profileLo, Box.profileHi, box_3404]
theorem leaf_3404_BranchSafe : CertificateConsequences.BranchSafe branch_box_3404 := by
  left; refine ⟨branch_box_3404_nonnegative, ?_⟩
  intro z hz; exact leaf_3404_sound hz

theorem leaf_3411_ok : checkAt 527 1000 box_3411 cert_3411 = true := by
  have h := List.all_eq_true.mp batch_68_04_ok accepted_3411 (by simp [batch_68_04_values])
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

theorem leaf_3412_ok : checkAt 527 1000 box_3412 cert_3412 = true := by
  have h := List.all_eq_true.mp batch_68_05_ok accepted_3412 (by simp [batch_68_05_values])
  exact h
theorem leaf_3412_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3412.profileLo box_3412.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3412_ok
theorem branch_box_3412_nonnegative : ∀ j, 0 ≤ branch_box_3412.lower j ∧ 0 ≤ branch_box_3412.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3412, Box.profileLo, Box.profileHi, box_3412]
theorem leaf_3412_BranchSafe : CertificateConsequences.BranchSafe branch_box_3412 := by
  left; refine ⟨branch_box_3412_nonnegative, ?_⟩
  intro z hz; exact leaf_3412_sound hz

theorem leaf_3418_ok : checkAt 527 1000 box_3418 cert_3418 = true := by
  have h := List.all_eq_true.mp batch_68_06_ok accepted_3418 (by simp [batch_68_06_values])
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
  have h := List.all_eq_true.mp batch_68_07_ok accepted_3419 (by simp [batch_68_07_values])
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

theorem leaf_3420_ok : checkAt 527 1000 box_3420 cert_3420 = true := by
  have h := List.all_eq_true.mp batch_68_08_ok accepted_3420 (by simp [batch_68_08_values])
  exact h
theorem leaf_3420_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3420.profileLo box_3420.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3420_ok
theorem branch_box_3420_nonnegative : ∀ j, 0 ≤ branch_box_3420.lower j ∧ 0 ≤ branch_box_3420.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3420, Box.profileLo, Box.profileHi, box_3420]
theorem leaf_3420_BranchSafe : CertificateConsequences.BranchSafe branch_box_3420 := by
  left; refine ⟨branch_box_3420_nonnegative, ?_⟩
  intro z hz; exact leaf_3420_sound hz

theorem leaf_3423_ok : checkAt 527 1000 box_3423 cert_3423 = true := by
  have h := List.all_eq_true.mp batch_68_09_ok accepted_3423 (by simp [batch_68_09_values])
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

theorem leaf_3424_ok : checkAt 527 1000 box_3424 cert_3424 = true := by
  have h := List.all_eq_true.mp batch_68_10_ok accepted_3424 (by simp [batch_68_10_values])
  exact h
theorem leaf_3424_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3424.profileLo box_3424.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3424_ok
theorem branch_box_3424_nonnegative : ∀ j, 0 ≤ branch_box_3424.lower j ∧ 0 ≤ branch_box_3424.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3424, Box.profileLo, Box.profileHi, box_3424]
theorem leaf_3424_BranchSafe : CertificateConsequences.BranchSafe branch_box_3424 := by
  left; refine ⟨branch_box_3424_nonnegative, ?_⟩
  intro z hz; exact leaf_3424_sound hz

theorem leaf_3425_ok : checkAt 527 1000 box_3425 cert_3425 = true := by
  have h := List.all_eq_true.mp batch_68_11_ok accepted_3425 (by simp [batch_68_11_values])
  exact h
theorem leaf_3425_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3425.profileLo box_3425.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3425_ok
theorem branch_box_3425_nonnegative : ∀ j, 0 ≤ branch_box_3425.lower j ∧ 0 ≤ branch_box_3425.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3425, Box.profileLo, Box.profileHi, box_3425]
theorem leaf_3425_BranchSafe : CertificateConsequences.BranchSafe branch_box_3425 := by
  left; refine ⟨branch_box_3425_nonnegative, ?_⟩
  intro z hz; exact leaf_3425_sound hz

theorem leaf_3426_ok : checkAt 527 1000 box_3426 cert_3426 = true := by
  have h := List.all_eq_true.mp batch_68_12_ok accepted_3426 (by simp [batch_68_12_values])
  exact h
theorem leaf_3426_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3426.profileLo box_3426.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3426_ok
theorem branch_box_3426_nonnegative : ∀ j, 0 ≤ branch_box_3426.lower j ∧ 0 ≤ branch_box_3426.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3426, Box.profileLo, Box.profileHi, box_3426]
theorem leaf_3426_BranchSafe : CertificateConsequences.BranchSafe branch_box_3426 := by
  left; refine ⟨branch_box_3426_nonnegative, ?_⟩
  intro z hz; exact leaf_3426_sound hz

theorem leaf_3427_ok : checkAt 527 1000 box_3427 cert_3427 = true := by
  have h := List.all_eq_true.mp batch_68_13_ok accepted_3427 (by simp [batch_68_13_values])
  exact h
theorem leaf_3427_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3427.profileLo box_3427.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3427_ok
theorem branch_box_3427_nonnegative : ∀ j, 0 ≤ branch_box_3427.lower j ∧ 0 ≤ branch_box_3427.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3427, Box.profileLo, Box.profileHi, box_3427]
theorem leaf_3427_BranchSafe : CertificateConsequences.BranchSafe branch_box_3427 := by
  left; refine ⟨branch_box_3427_nonnegative, ?_⟩
  intro z hz; exact leaf_3427_sound hz

theorem leaf_3428_ok : checkAt 527 1000 box_3428 cert_3428 = true := by
  have h := List.all_eq_true.mp batch_68_14_ok accepted_3428 (by simp [batch_68_14_values])
  exact h
theorem leaf_3428_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3428.profileLo box_3428.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3428_ok
theorem branch_box_3428_nonnegative : ∀ j, 0 ≤ branch_box_3428.lower j ∧ 0 ≤ branch_box_3428.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3428, Box.profileLo, Box.profileHi, box_3428]
theorem leaf_3428_BranchSafe : CertificateConsequences.BranchSafe branch_box_3428 := by
  left; refine ⟨branch_box_3428_nonnegative, ?_⟩
  intro z hz; exact leaf_3428_sound hz

theorem leaf_3433_ok : checkAt 527 1000 box_3433 cert_3433 = true := by
  have h := List.all_eq_true.mp batch_68_15_ok accepted_3433 (by simp [batch_68_15_values])
  exact h
theorem leaf_3433_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3433.profileLo box_3433.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3433_ok
theorem branch_box_3433_nonnegative : ∀ j, 0 ≤ branch_box_3433.lower j ∧ 0 ≤ branch_box_3433.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3433, Box.profileLo, Box.profileHi, box_3433]
theorem leaf_3433_BranchSafe : CertificateConsequences.BranchSafe branch_box_3433 := by
  left; refine ⟨branch_box_3433_nonnegative, ?_⟩
  intro z hz; exact leaf_3433_sound hz

theorem leaf_3434_ok : checkAt 527 1000 box_3434 cert_3434 = true := by
  have h := List.all_eq_true.mp batch_68_16_ok accepted_3434 (by simp [batch_68_16_values])
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

theorem leaf_3439_ok : checkAt 527 1000 box_3439 cert_3439 = true := by
  have h := List.all_eq_true.mp batch_68_17_ok accepted_3439 (by simp [batch_68_17_values])
  exact h
theorem leaf_3439_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3439.profileLo box_3439.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3439_ok
theorem branch_box_3439_nonnegative : ∀ j, 0 ≤ branch_box_3439.lower j ∧ 0 ≤ branch_box_3439.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3439, Box.profileLo, Box.profileHi, box_3439]
theorem leaf_3439_BranchSafe : CertificateConsequences.BranchSafe branch_box_3439 := by
  left; refine ⟨branch_box_3439_nonnegative, ?_⟩
  intro z hz; exact leaf_3439_sound hz

theorem leaf_3441_ok : checkAt 527 1000 box_3441 cert_3441 = true := by
  have h := List.all_eq_true.mp batch_68_18_ok accepted_3441 (by simp [batch_68_18_values])
  exact h
theorem leaf_3441_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3441.profileLo box_3441.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3441_ok
theorem branch_box_3441_nonnegative : ∀ j, 0 ≤ branch_box_3441.lower j ∧ 0 ≤ branch_box_3441.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3441, Box.profileLo, Box.profileHi, box_3441]
theorem leaf_3441_BranchSafe : CertificateConsequences.BranchSafe branch_box_3441 := by
  left; refine ⟨branch_box_3441_nonnegative, ?_⟩
  intro z hz; exact leaf_3441_sound hz

theorem leaf_3442_ok : checkAt 527 1000 box_3442 cert_3442 = true := by
  have h := List.all_eq_true.mp batch_68_19_ok accepted_3442 (by simp [batch_68_19_values])
  exact h
theorem leaf_3442_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3442.profileLo box_3442.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3442_ok
theorem branch_box_3442_nonnegative : ∀ j, 0 ≤ branch_box_3442.lower j ∧ 0 ≤ branch_box_3442.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3442, Box.profileLo, Box.profileHi, box_3442]
theorem leaf_3442_BranchSafe : CertificateConsequences.BranchSafe branch_box_3442 := by
  left; refine ⟨branch_box_3442_nonnegative, ?_⟩
  intro z hz; exact leaf_3442_sound hz

theorem leaf_3443_ok : checkAt 527 1000 box_3443 cert_3443 = true := by
  have h := List.all_eq_true.mp batch_68_20_ok accepted_3443 (by simp [batch_68_20_values])
  exact h
theorem leaf_3443_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3443.profileLo box_3443.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3443_ok
theorem branch_box_3443_nonnegative : ∀ j, 0 ≤ branch_box_3443.lower j ∧ 0 ≤ branch_box_3443.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3443, Box.profileLo, Box.profileHi, box_3443]
theorem leaf_3443_BranchSafe : CertificateConsequences.BranchSafe branch_box_3443 := by
  left; refine ⟨branch_box_3443_nonnegative, ?_⟩
  intro z hz; exact leaf_3443_sound hz

theorem leaf_3444_ok : checkAt 527 1000 box_3444 cert_3444 = true := by
  have h := List.all_eq_true.mp batch_68_21_ok accepted_3444 (by simp [batch_68_21_values])
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

theorem leaf_3447_ok : checkAt 527 1000 box_3447 cert_3447 = true := by
  have h := List.all_eq_true.mp batch_68_22_ok accepted_3447 (by simp [batch_68_22_values])
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

theorem leaf_3448_ok : checkAt 527 1000 box_3448 cert_3448 = true := by
  have h := List.all_eq_true.mp batch_68_23_ok accepted_3448 (by simp [batch_68_23_values])
  exact h
theorem leaf_3448_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3448.profileLo box_3448.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3448_ok
theorem branch_box_3448_nonnegative : ∀ j, 0 ≤ branch_box_3448.lower j ∧ 0 ≤ branch_box_3448.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3448, Box.profileLo, Box.profileHi, box_3448]
theorem leaf_3448_BranchSafe : CertificateConsequences.BranchSafe branch_box_3448 := by
  left; refine ⟨branch_box_3448_nonnegative, ?_⟩
  intro z hz; exact leaf_3448_sound hz

theorem leaf_3449_ok : checkAt 527 1000 box_3449 cert_3449 = true := by
  have h := List.all_eq_true.mp batch_68_24_ok accepted_3449 (by simp [batch_68_24_values])
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
end PeaceableQueens.UpperBound.Generated.Even.C527
