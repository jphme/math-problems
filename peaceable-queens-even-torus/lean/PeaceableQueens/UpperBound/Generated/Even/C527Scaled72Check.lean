import PeaceableQueens.UpperBound.Generated.Even.C527Scaled72Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_72_00_values : List Bool := [accepted_3600]
theorem batch_72_00_ok : batch_72_00_values.all id = true := by decide

def batch_72_01_values : List Bool := [accepted_3604]
theorem batch_72_01_ok : batch_72_01_values.all id = true := by decide

def batch_72_02_values : List Bool := [accepted_3607]
theorem batch_72_02_ok : batch_72_02_values.all id = true := by decide

def batch_72_03_values : List Bool := [accepted_3608]
theorem batch_72_03_ok : batch_72_03_values.all id = true := by decide

def batch_72_04_values : List Bool := [accepted_3611]
theorem batch_72_04_ok : batch_72_04_values.all id = true := by decide

def batch_72_05_values : List Bool := [accepted_3614]
theorem batch_72_05_ok : batch_72_05_values.all id = true := by decide

def batch_72_06_values : List Bool := [accepted_3615]
theorem batch_72_06_ok : batch_72_06_values.all id = true := by decide

def batch_72_07_values : List Bool := [accepted_3617]
theorem batch_72_07_ok : batch_72_07_values.all id = true := by decide

def batch_72_08_values : List Bool := [accepted_3619]
theorem batch_72_08_ok : batch_72_08_values.all id = true := by decide

def batch_72_09_values : List Bool := [accepted_3621]
theorem batch_72_09_ok : batch_72_09_values.all id = true := by decide

def batch_72_10_values : List Bool := [accepted_3622]
theorem batch_72_10_ok : batch_72_10_values.all id = true := by decide

def batch_72_11_values : List Bool := [accepted_3628]
theorem batch_72_11_ok : batch_72_11_values.all id = true := by decide

def batch_72_12_values : List Bool := [accepted_3630]
theorem batch_72_12_ok : batch_72_12_values.all id = true := by decide

def batch_72_13_values : List Bool := [accepted_3631]
theorem batch_72_13_ok : batch_72_13_values.all id = true := by decide

def batch_72_14_values : List Bool := [accepted_3632]
theorem batch_72_14_ok : batch_72_14_values.all id = true := by decide

def batch_72_15_values : List Bool := [accepted_3637]
theorem batch_72_15_ok : batch_72_15_values.all id = true := by decide

def batch_72_16_values : List Bool := [accepted_3638]
theorem batch_72_16_ok : batch_72_16_values.all id = true := by decide

def batch_72_17_values : List Bool := [accepted_3640]
theorem batch_72_17_ok : batch_72_17_values.all id = true := by decide

def batch_72_18_values : List Bool := [accepted_3641]
theorem batch_72_18_ok : batch_72_18_values.all id = true := by decide

def batch_72_19_values : List Bool := [accepted_3642]
theorem batch_72_19_ok : batch_72_19_values.all id = true := by decide

def batch_72_20_values : List Bool := [accepted_3645]
theorem batch_72_20_ok : batch_72_20_values.all id = true := by decide

def batch_72_21_values : List Bool := [accepted_3646]
theorem batch_72_21_ok : batch_72_21_values.all id = true := by decide

def batch_72_22_values : List Bool := [accepted_3647]
theorem batch_72_22_ok : batch_72_22_values.all id = true := by decide

def batch_72_23_values : List Bool := [accepted_3648]
theorem batch_72_23_ok : batch_72_23_values.all id = true := by decide

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

theorem leaf_3604_ok : checkAt 527 1000 box_3604 cert_3604 = true := by
  have h := List.all_eq_true.mp batch_72_01_ok accepted_3604 (by simp [batch_72_01_values])
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

theorem leaf_3607_ok : checkAt 527 1000 box_3607 cert_3607 = true := by
  have h := List.all_eq_true.mp batch_72_02_ok accepted_3607 (by simp [batch_72_02_values])
  exact h
theorem leaf_3607_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3607.profileLo box_3607.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3607_ok
theorem branch_box_3607_nonnegative : ∀ j, 0 ≤ branch_box_3607.lower j ∧ 0 ≤ branch_box_3607.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3607, Box.profileLo, Box.profileHi, box_3607]
theorem leaf_3607_BranchSafe : CertificateConsequences.BranchSafe branch_box_3607 := by
  left; refine ⟨branch_box_3607_nonnegative, ?_⟩
  intro z hz; exact leaf_3607_sound hz

theorem leaf_3608_ok : checkAt 527 1000 box_3608 cert_3608 = true := by
  have h := List.all_eq_true.mp batch_72_03_ok accepted_3608 (by simp [batch_72_03_values])
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

theorem leaf_3611_ok : checkAt 527 1000 box_3611 cert_3611 = true := by
  have h := List.all_eq_true.mp batch_72_04_ok accepted_3611 (by simp [batch_72_04_values])
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

theorem leaf_3614_ok : checkAt 527 1000 box_3614 cert_3614 = true := by
  have h := List.all_eq_true.mp batch_72_05_ok accepted_3614 (by simp [batch_72_05_values])
  exact h
theorem leaf_3614_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3614.profileLo box_3614.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3614_ok
theorem branch_box_3614_nonnegative : ∀ j, 0 ≤ branch_box_3614.lower j ∧ 0 ≤ branch_box_3614.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3614, Box.profileLo, Box.profileHi, box_3614]
theorem leaf_3614_BranchSafe : CertificateConsequences.BranchSafe branch_box_3614 := by
  left; refine ⟨branch_box_3614_nonnegative, ?_⟩
  intro z hz; exact leaf_3614_sound hz

theorem leaf_3615_ok : checkAt 527 1000 box_3615 cert_3615 = true := by
  have h := List.all_eq_true.mp batch_72_06_ok accepted_3615 (by simp [batch_72_06_values])
  exact h
theorem leaf_3615_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3615.profileLo box_3615.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3615_ok
theorem branch_box_3615_nonnegative : ∀ j, 0 ≤ branch_box_3615.lower j ∧ 0 ≤ branch_box_3615.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3615, Box.profileLo, Box.profileHi, box_3615]
theorem leaf_3615_BranchSafe : CertificateConsequences.BranchSafe branch_box_3615 := by
  left; refine ⟨branch_box_3615_nonnegative, ?_⟩
  intro z hz; exact leaf_3615_sound hz

theorem leaf_3617_ok : checkAt 527 1000 box_3617 cert_3617 = true := by
  have h := List.all_eq_true.mp batch_72_07_ok accepted_3617 (by simp [batch_72_07_values])
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

theorem leaf_3619_ok : checkAt 527 1000 box_3619 cert_3619 = true := by
  have h := List.all_eq_true.mp batch_72_08_ok accepted_3619 (by simp [batch_72_08_values])
  exact h
theorem leaf_3619_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3619.profileLo box_3619.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3619_ok
theorem branch_box_3619_nonnegative : ∀ j, 0 ≤ branch_box_3619.lower j ∧ 0 ≤ branch_box_3619.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3619, Box.profileLo, Box.profileHi, box_3619]
theorem leaf_3619_BranchSafe : CertificateConsequences.BranchSafe branch_box_3619 := by
  left; refine ⟨branch_box_3619_nonnegative, ?_⟩
  intro z hz; exact leaf_3619_sound hz

theorem leaf_3621_ok : checkAt 527 1000 box_3621 cert_3621 = true := by
  have h := List.all_eq_true.mp batch_72_09_ok accepted_3621 (by simp [batch_72_09_values])
  exact h
theorem leaf_3621_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3621.profileLo box_3621.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3621_ok
theorem branch_box_3621_nonnegative : ∀ j, 0 ≤ branch_box_3621.lower j ∧ 0 ≤ branch_box_3621.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3621, Box.profileLo, Box.profileHi, box_3621]
theorem leaf_3621_BranchSafe : CertificateConsequences.BranchSafe branch_box_3621 := by
  left; refine ⟨branch_box_3621_nonnegative, ?_⟩
  intro z hz; exact leaf_3621_sound hz

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

theorem leaf_3628_ok : checkAt 527 1000 box_3628 cert_3628 = true := by
  have h := List.all_eq_true.mp batch_72_11_ok accepted_3628 (by simp [batch_72_11_values])
  exact h
theorem leaf_3628_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3628.profileLo box_3628.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3628_ok
theorem branch_box_3628_nonnegative : ∀ j, 0 ≤ branch_box_3628.lower j ∧ 0 ≤ branch_box_3628.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3628, Box.profileLo, Box.profileHi, box_3628]
theorem leaf_3628_BranchSafe : CertificateConsequences.BranchSafe branch_box_3628 := by
  left; refine ⟨branch_box_3628_nonnegative, ?_⟩
  intro z hz; exact leaf_3628_sound hz

theorem leaf_3630_ok : checkAt 527 1000 box_3630 cert_3630 = true := by
  have h := List.all_eq_true.mp batch_72_12_ok accepted_3630 (by simp [batch_72_12_values])
  exact h
theorem leaf_3630_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3630.profileLo box_3630.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3630_ok
theorem branch_box_3630_nonnegative : ∀ j, 0 ≤ branch_box_3630.lower j ∧ 0 ≤ branch_box_3630.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3630, Box.profileLo, Box.profileHi, box_3630]
theorem leaf_3630_BranchSafe : CertificateConsequences.BranchSafe branch_box_3630 := by
  left; refine ⟨branch_box_3630_nonnegative, ?_⟩
  intro z hz; exact leaf_3630_sound hz

theorem leaf_3631_ok : checkAt 527 1000 box_3631 cert_3631 = true := by
  have h := List.all_eq_true.mp batch_72_13_ok accepted_3631 (by simp [batch_72_13_values])
  exact h
theorem leaf_3631_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3631.profileLo box_3631.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3631_ok
theorem branch_box_3631_nonnegative : ∀ j, 0 ≤ branch_box_3631.lower j ∧ 0 ≤ branch_box_3631.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3631, Box.profileLo, Box.profileHi, box_3631]
theorem leaf_3631_BranchSafe : CertificateConsequences.BranchSafe branch_box_3631 := by
  left; refine ⟨branch_box_3631_nonnegative, ?_⟩
  intro z hz; exact leaf_3631_sound hz

theorem leaf_3632_ok : checkAt 527 1000 box_3632 cert_3632 = true := by
  have h := List.all_eq_true.mp batch_72_14_ok accepted_3632 (by simp [batch_72_14_values])
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

theorem leaf_3637_ok : checkAt 527 1000 box_3637 cert_3637 = true := by
  have h := List.all_eq_true.mp batch_72_15_ok accepted_3637 (by simp [batch_72_15_values])
  exact h
theorem leaf_3637_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3637.profileLo box_3637.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3637_ok
theorem branch_box_3637_nonnegative : ∀ j, 0 ≤ branch_box_3637.lower j ∧ 0 ≤ branch_box_3637.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3637, Box.profileLo, Box.profileHi, box_3637]
theorem leaf_3637_BranchSafe : CertificateConsequences.BranchSafe branch_box_3637 := by
  left; refine ⟨branch_box_3637_nonnegative, ?_⟩
  intro z hz; exact leaf_3637_sound hz

theorem leaf_3638_ok : checkAt 527 1000 box_3638 cert_3638 = true := by
  have h := List.all_eq_true.mp batch_72_16_ok accepted_3638 (by simp [batch_72_16_values])
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

theorem leaf_3640_ok : checkAt 527 1000 box_3640 cert_3640 = true := by
  have h := List.all_eq_true.mp batch_72_17_ok accepted_3640 (by simp [batch_72_17_values])
  exact h
theorem leaf_3640_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3640.profileLo box_3640.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3640_ok
theorem branch_box_3640_nonnegative : ∀ j, 0 ≤ branch_box_3640.lower j ∧ 0 ≤ branch_box_3640.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3640, Box.profileLo, Box.profileHi, box_3640]
theorem leaf_3640_BranchSafe : CertificateConsequences.BranchSafe branch_box_3640 := by
  left; refine ⟨branch_box_3640_nonnegative, ?_⟩
  intro z hz; exact leaf_3640_sound hz

theorem leaf_3641_ok : checkAt 527 1000 box_3641 cert_3641 = true := by
  have h := List.all_eq_true.mp batch_72_18_ok accepted_3641 (by simp [batch_72_18_values])
  exact h
theorem leaf_3641_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3641.profileLo box_3641.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3641_ok
theorem branch_box_3641_nonnegative : ∀ j, 0 ≤ branch_box_3641.lower j ∧ 0 ≤ branch_box_3641.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3641, Box.profileLo, Box.profileHi, box_3641]
theorem leaf_3641_BranchSafe : CertificateConsequences.BranchSafe branch_box_3641 := by
  left; refine ⟨branch_box_3641_nonnegative, ?_⟩
  intro z hz; exact leaf_3641_sound hz

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

theorem leaf_3645_ok : checkAt 527 1000 box_3645 cert_3645 = true := by
  have h := List.all_eq_true.mp batch_72_20_ok accepted_3645 (by simp [batch_72_20_values])
  exact h
theorem leaf_3645_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3645.profileLo box_3645.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3645_ok
theorem branch_box_3645_nonnegative : ∀ j, 0 ≤ branch_box_3645.lower j ∧ 0 ≤ branch_box_3645.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3645, Box.profileLo, Box.profileHi, box_3645]
theorem leaf_3645_BranchSafe : CertificateConsequences.BranchSafe branch_box_3645 := by
  left; refine ⟨branch_box_3645_nonnegative, ?_⟩
  intro z hz; exact leaf_3645_sound hz

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

theorem leaf_3648_ok : checkAt 527 1000 box_3648 cert_3648 = true := by
  have h := List.all_eq_true.mp batch_72_23_ok accepted_3648 (by simp [batch_72_23_values])
  exact h
theorem leaf_3648_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3648.profileLo box_3648.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3648_ok
theorem branch_box_3648_nonnegative : ∀ j, 0 ≤ branch_box_3648.lower j ∧ 0 ≤ branch_box_3648.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3648, Box.profileLo, Box.profileHi, box_3648]
theorem leaf_3648_BranchSafe : CertificateConsequences.BranchSafe branch_box_3648 := by
  left; refine ⟨branch_box_3648_nonnegative, ?_⟩
  intro z hz; exact leaf_3648_sound hz

#print axioms batch_72_00_ok
#print axioms leaf_3600_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
