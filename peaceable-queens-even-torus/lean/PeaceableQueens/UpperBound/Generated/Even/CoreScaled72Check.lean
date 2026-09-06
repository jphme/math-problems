import PeaceableQueens.UpperBound.Generated.Even.CoreScaled72Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_72_00_values : List Bool := [accepted_3600]
theorem batch_72_00_ok : batch_72_00_values.all id = true := by decide

def batch_72_01_values : List Bool := [accepted_3602]
theorem batch_72_01_ok : batch_72_01_values.all id = true := by decide

def batch_72_02_values : List Bool := [accepted_3604]
theorem batch_72_02_ok : batch_72_02_values.all id = true := by decide

def batch_72_03_values : List Bool := [accepted_3606]
theorem batch_72_03_ok : batch_72_03_values.all id = true := by decide

def batch_72_04_values : List Bool := [accepted_3608]
theorem batch_72_04_ok : batch_72_04_values.all id = true := by decide

def batch_72_05_values : List Bool := [accepted_3610]
theorem batch_72_05_ok : batch_72_05_values.all id = true := by decide

def batch_72_06_values : List Bool := [accepted_3611]
theorem batch_72_06_ok : batch_72_06_values.all id = true := by decide

def batch_72_07_values : List Bool := [accepted_3613]
theorem batch_72_07_ok : batch_72_07_values.all id = true := by decide

def batch_72_08_values : List Bool := [accepted_3617]
theorem batch_72_08_ok : batch_72_08_values.all id = true := by decide

def batch_72_09_values : List Bool := [accepted_3620]
theorem batch_72_09_ok : batch_72_09_values.all id = true := by decide

def batch_72_10_values : List Bool := [accepted_3622]
theorem batch_72_10_ok : batch_72_10_values.all id = true := by decide

def batch_72_11_values : List Bool := [accepted_3624]
theorem batch_72_11_ok : batch_72_11_values.all id = true := by decide

def batch_72_12_values : List Bool := [accepted_3625]
theorem batch_72_12_ok : batch_72_12_values.all id = true := by decide

def batch_72_13_values : List Bool := [accepted_3627]
theorem batch_72_13_ok : batch_72_13_values.all id = true := by decide

def batch_72_14_values : List Bool := [accepted_3629]
theorem batch_72_14_ok : batch_72_14_values.all id = true := by decide

def batch_72_15_values : List Bool := [accepted_3632]
theorem batch_72_15_ok : batch_72_15_values.all id = true := by decide

def batch_72_16_values : List Bool := [accepted_3636]
theorem batch_72_16_ok : batch_72_16_values.all id = true := by decide

def batch_72_17_values : List Bool := [accepted_3638]
theorem batch_72_17_ok : batch_72_17_values.all id = true := by decide

def batch_72_18_values : List Bool := [accepted_3639]
theorem batch_72_18_ok : batch_72_18_values.all id = true := by decide

def batch_72_19_values : List Bool := [accepted_3642]
theorem batch_72_19_ok : batch_72_19_values.all id = true := by decide

def batch_72_20_values : List Bool := [accepted_3644]
theorem batch_72_20_ok : batch_72_20_values.all id = true := by decide

def batch_72_21_values : List Bool := [accepted_3646]
theorem batch_72_21_ok : batch_72_21_values.all id = true := by decide

def batch_72_22_values : List Bool := [accepted_3647]
theorem batch_72_22_ok : batch_72_22_values.all id = true := by decide

theorem leaf_3600_ok : checkAt 527 1000 box_3600 cert_3600 = true := by
  have h := List.all_eq_true.mp batch_72_00_ok accepted_3600 (by simp [batch_72_00_values])
  exact h
theorem leaf_3600_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3600.profileLo box_3600.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3600_ok
theorem branch_box_3600_nonnegative : ∀ j, 0 ≤ branch_box_3600.lower j ∧ 0 ≤ branch_box_3600.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3600, Box.profileLo, Box.profileHi, box_3600]
theorem leaf_3600_BranchSafe : CertificateConsequences.BranchSafe branch_box_3600 := by
  left; refine ⟨branch_box_3600_nonnegative, ?_⟩
  intro z hz; exact leaf_3600_sound hz

theorem leaf_3602_ok : checkAt 527 1000 box_3602 cert_3602 = true := by
  have h := List.all_eq_true.mp batch_72_01_ok accepted_3602 (by simp [batch_72_01_values])
  exact h
theorem leaf_3602_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3602.profileLo box_3602.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3602_ok
theorem branch_box_3602_nonnegative : ∀ j, 0 ≤ branch_box_3602.lower j ∧ 0 ≤ branch_box_3602.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3602, Box.profileLo, Box.profileHi, box_3602]
theorem leaf_3602_BranchSafe : CertificateConsequences.BranchSafe branch_box_3602 := by
  left; refine ⟨branch_box_3602_nonnegative, ?_⟩
  intro z hz; exact leaf_3602_sound hz

theorem leaf_3604_ok : checkAt 527 1000 box_3604 cert_3604 = true := by
  have h := List.all_eq_true.mp batch_72_02_ok accepted_3604 (by simp [batch_72_02_values])
  exact h
theorem leaf_3604_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3604.profileLo box_3604.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3604_ok
theorem branch_box_3604_nonnegative : ∀ j, 0 ≤ branch_box_3604.lower j ∧ 0 ≤ branch_box_3604.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3604, Box.profileLo, Box.profileHi, box_3604]
theorem leaf_3604_BranchSafe : CertificateConsequences.BranchSafe branch_box_3604 := by
  left; refine ⟨branch_box_3604_nonnegative, ?_⟩
  intro z hz; exact leaf_3604_sound hz

theorem leaf_3606_ok : checkAt 527 1000 box_3606 cert_3606 = true := by
  have h := List.all_eq_true.mp batch_72_03_ok accepted_3606 (by simp [batch_72_03_values])
  exact h
theorem leaf_3606_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3606.profileLo box_3606.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3606_ok
theorem branch_box_3606_nonnegative : ∀ j, 0 ≤ branch_box_3606.lower j ∧ 0 ≤ branch_box_3606.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3606, Box.profileLo, Box.profileHi, box_3606]
theorem leaf_3606_BranchSafe : CertificateConsequences.BranchSafe branch_box_3606 := by
  left; refine ⟨branch_box_3606_nonnegative, ?_⟩
  intro z hz; exact leaf_3606_sound hz

theorem leaf_3608_ok : checkAt 527 1000 box_3608 cert_3608 = true := by
  have h := List.all_eq_true.mp batch_72_04_ok accepted_3608 (by simp [batch_72_04_values])
  exact h
theorem leaf_3608_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3608.profileLo box_3608.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3608_ok
theorem branch_box_3608_nonnegative : ∀ j, 0 ≤ branch_box_3608.lower j ∧ 0 ≤ branch_box_3608.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3608, Box.profileLo, Box.profileHi, box_3608]
theorem leaf_3608_BranchSafe : CertificateConsequences.BranchSafe branch_box_3608 := by
  left; refine ⟨branch_box_3608_nonnegative, ?_⟩
  intro z hz; exact leaf_3608_sound hz

theorem leaf_3610_ok : checkAt 527 1000 box_3610 cert_3610 = true := by
  have h := List.all_eq_true.mp batch_72_05_ok accepted_3610 (by simp [batch_72_05_values])
  exact h
theorem leaf_3610_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3610.profileLo box_3610.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3610_ok
theorem branch_box_3610_nonnegative : ∀ j, 0 ≤ branch_box_3610.lower j ∧ 0 ≤ branch_box_3610.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3610, Box.profileLo, Box.profileHi, box_3610]
theorem leaf_3610_BranchSafe : CertificateConsequences.BranchSafe branch_box_3610 := by
  left; refine ⟨branch_box_3610_nonnegative, ?_⟩
  intro z hz; exact leaf_3610_sound hz

theorem leaf_3611_ok : checkAt 527 1000 box_3611 cert_3611 = true := by
  have h := List.all_eq_true.mp batch_72_06_ok accepted_3611 (by simp [batch_72_06_values])
  exact h
theorem leaf_3611_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3611.profileLo box_3611.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3611_ok
theorem branch_box_3611_nonnegative : ∀ j, 0 ≤ branch_box_3611.lower j ∧ 0 ≤ branch_box_3611.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3611, Box.profileLo, Box.profileHi, box_3611]
theorem leaf_3611_BranchSafe : CertificateConsequences.BranchSafe branch_box_3611 := by
  left; refine ⟨branch_box_3611_nonnegative, ?_⟩
  intro z hz; exact leaf_3611_sound hz

theorem leaf_3613_ok : checkAt 527 1000 box_3613 cert_3613 = true := by
  have h := List.all_eq_true.mp batch_72_07_ok accepted_3613 (by simp [batch_72_07_values])
  exact h
theorem leaf_3613_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3613.profileLo box_3613.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3613_ok
theorem branch_box_3613_nonnegative : ∀ j, 0 ≤ branch_box_3613.lower j ∧ 0 ≤ branch_box_3613.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3613, Box.profileLo, Box.profileHi, box_3613]
theorem leaf_3613_BranchSafe : CertificateConsequences.BranchSafe branch_box_3613 := by
  left; refine ⟨branch_box_3613_nonnegative, ?_⟩
  intro z hz; exact leaf_3613_sound hz

theorem leaf_3617_ok : checkAt 527 1000 box_3617 cert_3617 = true := by
  have h := List.all_eq_true.mp batch_72_08_ok accepted_3617 (by simp [batch_72_08_values])
  exact h
theorem leaf_3617_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3617.profileLo box_3617.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3617_ok
theorem branch_box_3617_nonnegative : ∀ j, 0 ≤ branch_box_3617.lower j ∧ 0 ≤ branch_box_3617.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3617, Box.profileLo, Box.profileHi, box_3617]
theorem leaf_3617_BranchSafe : CertificateConsequences.BranchSafe branch_box_3617 := by
  left; refine ⟨branch_box_3617_nonnegative, ?_⟩
  intro z hz; exact leaf_3617_sound hz

theorem leaf_3620_ok : checkAt 527 1000 box_3620 cert_3620 = true := by
  have h := List.all_eq_true.mp batch_72_09_ok accepted_3620 (by simp [batch_72_09_values])
  exact h
theorem leaf_3620_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3620.profileLo box_3620.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3620_ok
theorem branch_box_3620_nonnegative : ∀ j, 0 ≤ branch_box_3620.lower j ∧ 0 ≤ branch_box_3620.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3620, Box.profileLo, Box.profileHi, box_3620]
theorem leaf_3620_BranchSafe : CertificateConsequences.BranchSafe branch_box_3620 := by
  left; refine ⟨branch_box_3620_nonnegative, ?_⟩
  intro z hz; exact leaf_3620_sound hz

theorem leaf_3622_ok : checkAt 527 1000 box_3622 cert_3622 = true := by
  have h := List.all_eq_true.mp batch_72_10_ok accepted_3622 (by simp [batch_72_10_values])
  exact h
theorem leaf_3622_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3622.profileLo box_3622.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3622_ok
theorem branch_box_3622_nonnegative : ∀ j, 0 ≤ branch_box_3622.lower j ∧ 0 ≤ branch_box_3622.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3622, Box.profileLo, Box.profileHi, box_3622]
theorem leaf_3622_BranchSafe : CertificateConsequences.BranchSafe branch_box_3622 := by
  left; refine ⟨branch_box_3622_nonnegative, ?_⟩
  intro z hz; exact leaf_3622_sound hz

theorem leaf_3624_ok : checkAt 527 1000 box_3624 cert_3624 = true := by
  have h := List.all_eq_true.mp batch_72_11_ok accepted_3624 (by simp [batch_72_11_values])
  exact h
theorem leaf_3624_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3624.profileLo box_3624.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3624_ok
theorem branch_box_3624_nonnegative : ∀ j, 0 ≤ branch_box_3624.lower j ∧ 0 ≤ branch_box_3624.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3624, Box.profileLo, Box.profileHi, box_3624]
theorem leaf_3624_BranchSafe : CertificateConsequences.BranchSafe branch_box_3624 := by
  left; refine ⟨branch_box_3624_nonnegative, ?_⟩
  intro z hz; exact leaf_3624_sound hz

theorem leaf_3625_ok : checkAt 527 1000 box_3625 cert_3625 = true := by
  have h := List.all_eq_true.mp batch_72_12_ok accepted_3625 (by simp [batch_72_12_values])
  exact h
theorem leaf_3625_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3625.profileLo box_3625.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3625_ok
theorem branch_box_3625_nonnegative : ∀ j, 0 ≤ branch_box_3625.lower j ∧ 0 ≤ branch_box_3625.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3625, Box.profileLo, Box.profileHi, box_3625]
theorem leaf_3625_BranchSafe : CertificateConsequences.BranchSafe branch_box_3625 := by
  left; refine ⟨branch_box_3625_nonnegative, ?_⟩
  intro z hz; exact leaf_3625_sound hz

theorem leaf_3627_ok : checkAt 527 1000 box_3627 cert_3627 = true := by
  have h := List.all_eq_true.mp batch_72_13_ok accepted_3627 (by simp [batch_72_13_values])
  exact h
theorem leaf_3627_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3627.profileLo box_3627.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3627_ok
theorem branch_box_3627_nonnegative : ∀ j, 0 ≤ branch_box_3627.lower j ∧ 0 ≤ branch_box_3627.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3627, Box.profileLo, Box.profileHi, box_3627]
theorem leaf_3627_BranchSafe : CertificateConsequences.BranchSafe branch_box_3627 := by
  left; refine ⟨branch_box_3627_nonnegative, ?_⟩
  intro z hz; exact leaf_3627_sound hz

theorem leaf_3629_ok : checkAt 527 1000 box_3629 cert_3629 = true := by
  have h := List.all_eq_true.mp batch_72_14_ok accepted_3629 (by simp [batch_72_14_values])
  exact h
theorem leaf_3629_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3629.profileLo box_3629.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3629_ok
theorem branch_box_3629_nonnegative : ∀ j, 0 ≤ branch_box_3629.lower j ∧ 0 ≤ branch_box_3629.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3629, Box.profileLo, Box.profileHi, box_3629]
theorem leaf_3629_BranchSafe : CertificateConsequences.BranchSafe branch_box_3629 := by
  left; refine ⟨branch_box_3629_nonnegative, ?_⟩
  intro z hz; exact leaf_3629_sound hz

theorem leaf_3632_ok : checkAt 527 1000 box_3632 cert_3632 = true := by
  have h := List.all_eq_true.mp batch_72_15_ok accepted_3632 (by simp [batch_72_15_values])
  exact h
theorem leaf_3632_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3632.profileLo box_3632.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3632_ok
theorem branch_box_3632_nonnegative : ∀ j, 0 ≤ branch_box_3632.lower j ∧ 0 ≤ branch_box_3632.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3632, Box.profileLo, Box.profileHi, box_3632]
theorem leaf_3632_BranchSafe : CertificateConsequences.BranchSafe branch_box_3632 := by
  left; refine ⟨branch_box_3632_nonnegative, ?_⟩
  intro z hz; exact leaf_3632_sound hz

theorem leaf_3636_ok : checkAt 527 1000 box_3636 cert_3636 = true := by
  have h := List.all_eq_true.mp batch_72_16_ok accepted_3636 (by simp [batch_72_16_values])
  exact h
theorem leaf_3636_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3636.profileLo box_3636.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3636_ok
theorem branch_box_3636_nonnegative : ∀ j, 0 ≤ branch_box_3636.lower j ∧ 0 ≤ branch_box_3636.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3636, Box.profileLo, Box.profileHi, box_3636]
theorem leaf_3636_BranchSafe : CertificateConsequences.BranchSafe branch_box_3636 := by
  left; refine ⟨branch_box_3636_nonnegative, ?_⟩
  intro z hz; exact leaf_3636_sound hz

theorem leaf_3638_ok : checkAt 527 1000 box_3638 cert_3638 = true := by
  have h := List.all_eq_true.mp batch_72_17_ok accepted_3638 (by simp [batch_72_17_values])
  exact h
theorem leaf_3638_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3638.profileLo box_3638.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3638_ok
theorem branch_box_3638_nonnegative : ∀ j, 0 ≤ branch_box_3638.lower j ∧ 0 ≤ branch_box_3638.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3638, Box.profileLo, Box.profileHi, box_3638]
theorem leaf_3638_BranchSafe : CertificateConsequences.BranchSafe branch_box_3638 := by
  left; refine ⟨branch_box_3638_nonnegative, ?_⟩
  intro z hz; exact leaf_3638_sound hz

theorem leaf_3639_ok : checkAt 527 1000 box_3639 cert_3639 = true := by
  have h := List.all_eq_true.mp batch_72_18_ok accepted_3639 (by simp [batch_72_18_values])
  exact h
theorem leaf_3639_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3639.profileLo box_3639.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3639_ok
theorem branch_box_3639_nonnegative : ∀ j, 0 ≤ branch_box_3639.lower j ∧ 0 ≤ branch_box_3639.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3639, Box.profileLo, Box.profileHi, box_3639]
theorem leaf_3639_BranchSafe : CertificateConsequences.BranchSafe branch_box_3639 := by
  left; refine ⟨branch_box_3639_nonnegative, ?_⟩
  intro z hz; exact leaf_3639_sound hz

theorem leaf_3642_ok : checkAt 527 1000 box_3642 cert_3642 = true := by
  have h := List.all_eq_true.mp batch_72_19_ok accepted_3642 (by simp [batch_72_19_values])
  exact h
theorem leaf_3642_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3642.profileLo box_3642.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3642_ok
theorem branch_box_3642_nonnegative : ∀ j, 0 ≤ branch_box_3642.lower j ∧ 0 ≤ branch_box_3642.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3642, Box.profileLo, Box.profileHi, box_3642]
theorem leaf_3642_BranchSafe : CertificateConsequences.BranchSafe branch_box_3642 := by
  left; refine ⟨branch_box_3642_nonnegative, ?_⟩
  intro z hz; exact leaf_3642_sound hz

theorem leaf_3644_ok : checkAt 527 1000 box_3644 cert_3644 = true := by
  have h := List.all_eq_true.mp batch_72_20_ok accepted_3644 (by simp [batch_72_20_values])
  exact h
theorem leaf_3644_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3644.profileLo box_3644.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3644_ok
theorem branch_box_3644_nonnegative : ∀ j, 0 ≤ branch_box_3644.lower j ∧ 0 ≤ branch_box_3644.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3644, Box.profileLo, Box.profileHi, box_3644]
theorem leaf_3644_BranchSafe : CertificateConsequences.BranchSafe branch_box_3644 := by
  left; refine ⟨branch_box_3644_nonnegative, ?_⟩
  intro z hz; exact leaf_3644_sound hz

theorem leaf_3646_ok : checkAt 527 1000 box_3646 cert_3646 = true := by
  have h := List.all_eq_true.mp batch_72_21_ok accepted_3646 (by simp [batch_72_21_values])
  exact h
theorem leaf_3646_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3646.profileLo box_3646.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3646_ok
theorem branch_box_3646_nonnegative : ∀ j, 0 ≤ branch_box_3646.lower j ∧ 0 ≤ branch_box_3646.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3646, Box.profileLo, Box.profileHi, box_3646]
theorem leaf_3646_BranchSafe : CertificateConsequences.BranchSafe branch_box_3646 := by
  left; refine ⟨branch_box_3646_nonnegative, ?_⟩
  intro z hz; exact leaf_3646_sound hz

theorem leaf_3647_ok : checkAt 527 1000 box_3647 cert_3647 = true := by
  have h := List.all_eq_true.mp batch_72_22_ok accepted_3647 (by simp [batch_72_22_values])
  exact h
theorem leaf_3647_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3647.profileLo box_3647.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3647_ok
theorem branch_box_3647_nonnegative : ∀ j, 0 ≤ branch_box_3647.lower j ∧ 0 ≤ branch_box_3647.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3647, Box.profileLo, Box.profileHi, box_3647]
theorem leaf_3647_BranchSafe : CertificateConsequences.BranchSafe branch_box_3647 := by
  left; refine ⟨branch_box_3647_nonnegative, ?_⟩
  intro z hz; exact leaf_3647_sound hz

#print axioms batch_72_00_ok
#print axioms leaf_3600_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
