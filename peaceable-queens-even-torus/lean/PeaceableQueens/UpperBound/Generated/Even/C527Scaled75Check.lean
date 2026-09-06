import PeaceableQueens.UpperBound.Generated.Even.C527Scaled75Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_75_00_values : List Bool := [accepted_3750]
theorem batch_75_00_ok : batch_75_00_values.all id = true := by decide

def batch_75_01_values : List Bool := [accepted_3755]
theorem batch_75_01_ok : batch_75_01_values.all id = true := by decide

def batch_75_02_values : List Bool := [accepted_3756]
theorem batch_75_02_ok : batch_75_02_values.all id = true := by decide

def batch_75_03_values : List Bool := [accepted_3758]
theorem batch_75_03_ok : batch_75_03_values.all id = true := by decide

def batch_75_04_values : List Bool := [accepted_3761]
theorem batch_75_04_ok : batch_75_04_values.all id = true := by decide

def batch_75_05_values : List Bool := [accepted_3762]
theorem batch_75_05_ok : batch_75_05_values.all id = true := by decide

def batch_75_06_values : List Bool := [accepted_3763]
theorem batch_75_06_ok : batch_75_06_values.all id = true := by decide

def batch_75_07_values : List Bool := [accepted_3765]
theorem batch_75_07_ok : batch_75_07_values.all id = true := by decide

def batch_75_08_values : List Bool := [accepted_3766]
theorem batch_75_08_ok : batch_75_08_values.all id = true := by decide

def batch_75_09_values : List Bool := [accepted_3771]
theorem batch_75_09_ok : batch_75_09_values.all id = true := by decide

def batch_75_10_values : List Bool := [accepted_3772]
theorem batch_75_10_ok : batch_75_10_values.all id = true := by decide

def batch_75_11_values : List Bool := [accepted_3775]
theorem batch_75_11_ok : batch_75_11_values.all id = true := by decide

def batch_75_12_values : List Bool := [accepted_3776]
theorem batch_75_12_ok : batch_75_12_values.all id = true := by decide

def batch_75_13_values : List Bool := [accepted_3779]
theorem batch_75_13_ok : batch_75_13_values.all id = true := by decide

def batch_75_14_values : List Bool := [accepted_3781]
theorem batch_75_14_ok : batch_75_14_values.all id = true := by decide

def batch_75_15_values : List Bool := [accepted_3782]
theorem batch_75_15_ok : batch_75_15_values.all id = true := by decide

def batch_75_16_values : List Bool := [accepted_3783]
theorem batch_75_16_ok : batch_75_16_values.all id = true := by decide

def batch_75_17_values : List Bool := [accepted_3784]
theorem batch_75_17_ok : batch_75_17_values.all id = true := by decide

def batch_75_18_values : List Bool := [accepted_3785]
theorem batch_75_18_ok : batch_75_18_values.all id = true := by decide

def batch_75_19_values : List Bool := [accepted_3787]
theorem batch_75_19_ok : batch_75_19_values.all id = true := by decide

def batch_75_20_values : List Bool := [accepted_3788]
theorem batch_75_20_ok : batch_75_20_values.all id = true := by decide

def batch_75_21_values : List Bool := [accepted_3795]
theorem batch_75_21_ok : batch_75_21_values.all id = true := by decide

def batch_75_22_values : List Bool := [accepted_3796]
theorem batch_75_22_ok : batch_75_22_values.all id = true := by decide

def batch_75_23_values : List Bool := [accepted_3797]
theorem batch_75_23_ok : batch_75_23_values.all id = true := by decide

def batch_75_24_values : List Bool := [accepted_3798]
theorem batch_75_24_ok : batch_75_24_values.all id = true := by decide

def batch_75_25_values : List Bool := [accepted_3799]
theorem batch_75_25_ok : batch_75_25_values.all id = true := by decide

theorem leaf_3750_ok : checkAt 527 1000 box_3750 cert_3750 = true := by
  have h := List.all_eq_true.mp batch_75_00_ok accepted_3750 (by simp [batch_75_00_values])
  exact h
theorem leaf_3750_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3750.profileLo box_3750.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3750_ok
theorem branch_box_3750_nonnegative : ∀ j, 0 ≤ branch_box_3750.lower j ∧ 0 ≤ branch_box_3750.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3750, Box.profileLo, Box.profileHi, box_3750]
theorem leaf_3750_BranchSafe : CertificateConsequences.BranchSafe branch_box_3750 := by
  left; refine ⟨branch_box_3750_nonnegative, ?_⟩
  intro z hz; exact leaf_3750_sound hz

theorem leaf_3755_ok : checkAt 527 1000 box_3755 cert_3755 = true := by
  have h := List.all_eq_true.mp batch_75_01_ok accepted_3755 (by simp [batch_75_01_values])
  exact h
theorem leaf_3755_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3755.profileLo box_3755.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3755_ok
theorem branch_box_3755_nonnegative : ∀ j, 0 ≤ branch_box_3755.lower j ∧ 0 ≤ branch_box_3755.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3755, Box.profileLo, Box.profileHi, box_3755]
theorem leaf_3755_BranchSafe : CertificateConsequences.BranchSafe branch_box_3755 := by
  left; refine ⟨branch_box_3755_nonnegative, ?_⟩
  intro z hz; exact leaf_3755_sound hz

theorem leaf_3756_ok : checkAt 527 1000 box_3756 cert_3756 = true := by
  have h := List.all_eq_true.mp batch_75_02_ok accepted_3756 (by simp [batch_75_02_values])
  exact h
theorem leaf_3756_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3756.profileLo box_3756.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3756_ok
theorem branch_box_3756_nonnegative : ∀ j, 0 ≤ branch_box_3756.lower j ∧ 0 ≤ branch_box_3756.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3756, Box.profileLo, Box.profileHi, box_3756]
theorem leaf_3756_BranchSafe : CertificateConsequences.BranchSafe branch_box_3756 := by
  left; refine ⟨branch_box_3756_nonnegative, ?_⟩
  intro z hz; exact leaf_3756_sound hz

theorem leaf_3758_ok : checkAt 527 1000 box_3758 cert_3758 = true := by
  have h := List.all_eq_true.mp batch_75_03_ok accepted_3758 (by simp [batch_75_03_values])
  exact h
theorem leaf_3758_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3758.profileLo box_3758.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3758_ok
theorem branch_box_3758_nonnegative : ∀ j, 0 ≤ branch_box_3758.lower j ∧ 0 ≤ branch_box_3758.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3758, Box.profileLo, Box.profileHi, box_3758]
theorem leaf_3758_BranchSafe : CertificateConsequences.BranchSafe branch_box_3758 := by
  left; refine ⟨branch_box_3758_nonnegative, ?_⟩
  intro z hz; exact leaf_3758_sound hz

theorem leaf_3761_ok : checkAt 527 1000 box_3761 cert_3761 = true := by
  have h := List.all_eq_true.mp batch_75_04_ok accepted_3761 (by simp [batch_75_04_values])
  exact h
theorem leaf_3761_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3761.profileLo box_3761.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3761_ok
theorem branch_box_3761_nonnegative : ∀ j, 0 ≤ branch_box_3761.lower j ∧ 0 ≤ branch_box_3761.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3761, Box.profileLo, Box.profileHi, box_3761]
theorem leaf_3761_BranchSafe : CertificateConsequences.BranchSafe branch_box_3761 := by
  left; refine ⟨branch_box_3761_nonnegative, ?_⟩
  intro z hz; exact leaf_3761_sound hz

theorem leaf_3762_ok : checkAt 527 1000 box_3762 cert_3762 = true := by
  have h := List.all_eq_true.mp batch_75_05_ok accepted_3762 (by simp [batch_75_05_values])
  exact h
theorem leaf_3762_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3762.profileLo box_3762.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3762_ok
theorem branch_box_3762_nonnegative : ∀ j, 0 ≤ branch_box_3762.lower j ∧ 0 ≤ branch_box_3762.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3762, Box.profileLo, Box.profileHi, box_3762]
theorem leaf_3762_BranchSafe : CertificateConsequences.BranchSafe branch_box_3762 := by
  left; refine ⟨branch_box_3762_nonnegative, ?_⟩
  intro z hz; exact leaf_3762_sound hz

theorem leaf_3763_ok : checkAt 527 1000 box_3763 cert_3763 = true := by
  have h := List.all_eq_true.mp batch_75_06_ok accepted_3763 (by simp [batch_75_06_values])
  exact h
theorem leaf_3763_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3763.profileLo box_3763.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3763_ok
theorem branch_box_3763_nonnegative : ∀ j, 0 ≤ branch_box_3763.lower j ∧ 0 ≤ branch_box_3763.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3763, Box.profileLo, Box.profileHi, box_3763]
theorem leaf_3763_BranchSafe : CertificateConsequences.BranchSafe branch_box_3763 := by
  left; refine ⟨branch_box_3763_nonnegative, ?_⟩
  intro z hz; exact leaf_3763_sound hz

theorem leaf_3765_ok : checkAt 527 1000 box_3765 cert_3765 = true := by
  have h := List.all_eq_true.mp batch_75_07_ok accepted_3765 (by simp [batch_75_07_values])
  exact h
theorem leaf_3765_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3765.profileLo box_3765.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3765_ok
theorem branch_box_3765_nonnegative : ∀ j, 0 ≤ branch_box_3765.lower j ∧ 0 ≤ branch_box_3765.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3765, Box.profileLo, Box.profileHi, box_3765]
theorem leaf_3765_BranchSafe : CertificateConsequences.BranchSafe branch_box_3765 := by
  left; refine ⟨branch_box_3765_nonnegative, ?_⟩
  intro z hz; exact leaf_3765_sound hz

theorem leaf_3766_ok : checkAt 527 1000 box_3766 cert_3766 = true := by
  have h := List.all_eq_true.mp batch_75_08_ok accepted_3766 (by simp [batch_75_08_values])
  exact h
theorem leaf_3766_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3766.profileLo box_3766.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3766_ok
theorem branch_box_3766_nonnegative : ∀ j, 0 ≤ branch_box_3766.lower j ∧ 0 ≤ branch_box_3766.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3766, Box.profileLo, Box.profileHi, box_3766]
theorem leaf_3766_BranchSafe : CertificateConsequences.BranchSafe branch_box_3766 := by
  left; refine ⟨branch_box_3766_nonnegative, ?_⟩
  intro z hz; exact leaf_3766_sound hz

theorem leaf_3771_ok : checkAt 527 1000 box_3771 cert_3771 = true := by
  have h := List.all_eq_true.mp batch_75_09_ok accepted_3771 (by simp [batch_75_09_values])
  exact h
theorem leaf_3771_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3771.profileLo box_3771.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3771_ok
theorem branch_box_3771_nonnegative : ∀ j, 0 ≤ branch_box_3771.lower j ∧ 0 ≤ branch_box_3771.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3771, Box.profileLo, Box.profileHi, box_3771]
theorem leaf_3771_BranchSafe : CertificateConsequences.BranchSafe branch_box_3771 := by
  left; refine ⟨branch_box_3771_nonnegative, ?_⟩
  intro z hz; exact leaf_3771_sound hz

theorem leaf_3772_ok : checkAt 527 1000 box_3772 cert_3772 = true := by
  have h := List.all_eq_true.mp batch_75_10_ok accepted_3772 (by simp [batch_75_10_values])
  exact h
theorem leaf_3772_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3772.profileLo box_3772.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3772_ok
theorem branch_box_3772_nonnegative : ∀ j, 0 ≤ branch_box_3772.lower j ∧ 0 ≤ branch_box_3772.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3772, Box.profileLo, Box.profileHi, box_3772]
theorem leaf_3772_BranchSafe : CertificateConsequences.BranchSafe branch_box_3772 := by
  left; refine ⟨branch_box_3772_nonnegative, ?_⟩
  intro z hz; exact leaf_3772_sound hz

theorem leaf_3775_ok : checkAt 527 1000 box_3775 cert_3775 = true := by
  have h := List.all_eq_true.mp batch_75_11_ok accepted_3775 (by simp [batch_75_11_values])
  exact h
theorem leaf_3775_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3775.profileLo box_3775.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3775_ok
theorem branch_box_3775_nonnegative : ∀ j, 0 ≤ branch_box_3775.lower j ∧ 0 ≤ branch_box_3775.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3775, Box.profileLo, Box.profileHi, box_3775]
theorem leaf_3775_BranchSafe : CertificateConsequences.BranchSafe branch_box_3775 := by
  left; refine ⟨branch_box_3775_nonnegative, ?_⟩
  intro z hz; exact leaf_3775_sound hz

theorem leaf_3776_ok : checkAt 527 1000 box_3776 cert_3776 = true := by
  have h := List.all_eq_true.mp batch_75_12_ok accepted_3776 (by simp [batch_75_12_values])
  exact h
theorem leaf_3776_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3776.profileLo box_3776.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3776_ok
theorem branch_box_3776_nonnegative : ∀ j, 0 ≤ branch_box_3776.lower j ∧ 0 ≤ branch_box_3776.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3776, Box.profileLo, Box.profileHi, box_3776]
theorem leaf_3776_BranchSafe : CertificateConsequences.BranchSafe branch_box_3776 := by
  left; refine ⟨branch_box_3776_nonnegative, ?_⟩
  intro z hz; exact leaf_3776_sound hz

theorem leaf_3779_ok : checkAt 527 1000 box_3779 cert_3779 = true := by
  have h := List.all_eq_true.mp batch_75_13_ok accepted_3779 (by simp [batch_75_13_values])
  exact h
theorem leaf_3779_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3779.profileLo box_3779.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3779_ok
theorem branch_box_3779_nonnegative : ∀ j, 0 ≤ branch_box_3779.lower j ∧ 0 ≤ branch_box_3779.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3779, Box.profileLo, Box.profileHi, box_3779]
theorem leaf_3779_BranchSafe : CertificateConsequences.BranchSafe branch_box_3779 := by
  left; refine ⟨branch_box_3779_nonnegative, ?_⟩
  intro z hz; exact leaf_3779_sound hz

theorem leaf_3781_ok : checkAt 527 1000 box_3781 cert_3781 = true := by
  have h := List.all_eq_true.mp batch_75_14_ok accepted_3781 (by simp [batch_75_14_values])
  exact h
theorem leaf_3781_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3781.profileLo box_3781.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3781_ok
theorem branch_box_3781_nonnegative : ∀ j, 0 ≤ branch_box_3781.lower j ∧ 0 ≤ branch_box_3781.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3781, Box.profileLo, Box.profileHi, box_3781]
theorem leaf_3781_BranchSafe : CertificateConsequences.BranchSafe branch_box_3781 := by
  left; refine ⟨branch_box_3781_nonnegative, ?_⟩
  intro z hz; exact leaf_3781_sound hz

theorem leaf_3782_ok : checkAt 527 1000 box_3782 cert_3782 = true := by
  have h := List.all_eq_true.mp batch_75_15_ok accepted_3782 (by simp [batch_75_15_values])
  exact h
theorem leaf_3782_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3782.profileLo box_3782.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3782_ok
theorem branch_box_3782_nonnegative : ∀ j, 0 ≤ branch_box_3782.lower j ∧ 0 ≤ branch_box_3782.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3782, Box.profileLo, Box.profileHi, box_3782]
theorem leaf_3782_BranchSafe : CertificateConsequences.BranchSafe branch_box_3782 := by
  left; refine ⟨branch_box_3782_nonnegative, ?_⟩
  intro z hz; exact leaf_3782_sound hz

theorem leaf_3783_ok : checkAt 527 1000 box_3783 cert_3783 = true := by
  have h := List.all_eq_true.mp batch_75_16_ok accepted_3783 (by simp [batch_75_16_values])
  exact h
theorem leaf_3783_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3783.profileLo box_3783.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3783_ok
theorem branch_box_3783_nonnegative : ∀ j, 0 ≤ branch_box_3783.lower j ∧ 0 ≤ branch_box_3783.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3783, Box.profileLo, Box.profileHi, box_3783]
theorem leaf_3783_BranchSafe : CertificateConsequences.BranchSafe branch_box_3783 := by
  left; refine ⟨branch_box_3783_nonnegative, ?_⟩
  intro z hz; exact leaf_3783_sound hz

theorem leaf_3784_ok : checkAt 527 1000 box_3784 cert_3784 = true := by
  have h := List.all_eq_true.mp batch_75_17_ok accepted_3784 (by simp [batch_75_17_values])
  exact h
theorem leaf_3784_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3784.profileLo box_3784.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3784_ok
theorem branch_box_3784_nonnegative : ∀ j, 0 ≤ branch_box_3784.lower j ∧ 0 ≤ branch_box_3784.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3784, Box.profileLo, Box.profileHi, box_3784]
theorem leaf_3784_BranchSafe : CertificateConsequences.BranchSafe branch_box_3784 := by
  left; refine ⟨branch_box_3784_nonnegative, ?_⟩
  intro z hz; exact leaf_3784_sound hz

theorem leaf_3785_ok : checkAt 527 1000 box_3785 cert_3785 = true := by
  have h := List.all_eq_true.mp batch_75_18_ok accepted_3785 (by simp [batch_75_18_values])
  exact h
theorem leaf_3785_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3785.profileLo box_3785.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3785_ok
theorem branch_box_3785_nonnegative : ∀ j, 0 ≤ branch_box_3785.lower j ∧ 0 ≤ branch_box_3785.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3785, Box.profileLo, Box.profileHi, box_3785]
theorem leaf_3785_BranchSafe : CertificateConsequences.BranchSafe branch_box_3785 := by
  left; refine ⟨branch_box_3785_nonnegative, ?_⟩
  intro z hz; exact leaf_3785_sound hz

theorem leaf_3787_ok : checkAt 527 1000 box_3787 cert_3787 = true := by
  have h := List.all_eq_true.mp batch_75_19_ok accepted_3787 (by simp [batch_75_19_values])
  exact h
theorem leaf_3787_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3787.profileLo box_3787.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3787_ok
theorem branch_box_3787_nonnegative : ∀ j, 0 ≤ branch_box_3787.lower j ∧ 0 ≤ branch_box_3787.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3787, Box.profileLo, Box.profileHi, box_3787]
theorem leaf_3787_BranchSafe : CertificateConsequences.BranchSafe branch_box_3787 := by
  left; refine ⟨branch_box_3787_nonnegative, ?_⟩
  intro z hz; exact leaf_3787_sound hz

theorem leaf_3788_ok : checkAt 527 1000 box_3788 cert_3788 = true := by
  have h := List.all_eq_true.mp batch_75_20_ok accepted_3788 (by simp [batch_75_20_values])
  exact h
theorem leaf_3788_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3788.profileLo box_3788.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3788_ok
theorem branch_box_3788_nonnegative : ∀ j, 0 ≤ branch_box_3788.lower j ∧ 0 ≤ branch_box_3788.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3788, Box.profileLo, Box.profileHi, box_3788]
theorem leaf_3788_BranchSafe : CertificateConsequences.BranchSafe branch_box_3788 := by
  left; refine ⟨branch_box_3788_nonnegative, ?_⟩
  intro z hz; exact leaf_3788_sound hz

theorem leaf_3795_ok : checkAt 527 1000 box_3795 cert_3795 = true := by
  have h := List.all_eq_true.mp batch_75_21_ok accepted_3795 (by simp [batch_75_21_values])
  exact h
theorem leaf_3795_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3795.profileLo box_3795.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3795_ok
theorem branch_box_3795_nonnegative : ∀ j, 0 ≤ branch_box_3795.lower j ∧ 0 ≤ branch_box_3795.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3795, Box.profileLo, Box.profileHi, box_3795]
theorem leaf_3795_BranchSafe : CertificateConsequences.BranchSafe branch_box_3795 := by
  left; refine ⟨branch_box_3795_nonnegative, ?_⟩
  intro z hz; exact leaf_3795_sound hz

theorem leaf_3796_ok : checkAt 527 1000 box_3796 cert_3796 = true := by
  have h := List.all_eq_true.mp batch_75_22_ok accepted_3796 (by simp [batch_75_22_values])
  exact h
theorem leaf_3796_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3796.profileLo box_3796.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3796_ok
theorem branch_box_3796_nonnegative : ∀ j, 0 ≤ branch_box_3796.lower j ∧ 0 ≤ branch_box_3796.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3796, Box.profileLo, Box.profileHi, box_3796]
theorem leaf_3796_BranchSafe : CertificateConsequences.BranchSafe branch_box_3796 := by
  left; refine ⟨branch_box_3796_nonnegative, ?_⟩
  intro z hz; exact leaf_3796_sound hz

theorem leaf_3797_ok : checkAt 527 1000 box_3797 cert_3797 = true := by
  have h := List.all_eq_true.mp batch_75_23_ok accepted_3797 (by simp [batch_75_23_values])
  exact h
theorem leaf_3797_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3797.profileLo box_3797.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3797_ok
theorem branch_box_3797_nonnegative : ∀ j, 0 ≤ branch_box_3797.lower j ∧ 0 ≤ branch_box_3797.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3797, Box.profileLo, Box.profileHi, box_3797]
theorem leaf_3797_BranchSafe : CertificateConsequences.BranchSafe branch_box_3797 := by
  left; refine ⟨branch_box_3797_nonnegative, ?_⟩
  intro z hz; exact leaf_3797_sound hz

theorem leaf_3798_ok : checkAt 527 1000 box_3798 cert_3798 = true := by
  have h := List.all_eq_true.mp batch_75_24_ok accepted_3798 (by simp [batch_75_24_values])
  exact h
theorem leaf_3798_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3798.profileLo box_3798.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3798_ok
theorem branch_box_3798_nonnegative : ∀ j, 0 ≤ branch_box_3798.lower j ∧ 0 ≤ branch_box_3798.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3798, Box.profileLo, Box.profileHi, box_3798]
theorem leaf_3798_BranchSafe : CertificateConsequences.BranchSafe branch_box_3798 := by
  left; refine ⟨branch_box_3798_nonnegative, ?_⟩
  intro z hz; exact leaf_3798_sound hz

theorem leaf_3799_ok : checkAt 527 1000 box_3799 cert_3799 = true := by
  have h := List.all_eq_true.mp batch_75_25_ok accepted_3799 (by simp [batch_75_25_values])
  exact h
theorem leaf_3799_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3799.profileLo box_3799.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3799_ok
theorem branch_box_3799_nonnegative : ∀ j, 0 ≤ branch_box_3799.lower j ∧ 0 ≤ branch_box_3799.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3799, Box.profileLo, Box.profileHi, box_3799]
theorem leaf_3799_BranchSafe : CertificateConsequences.BranchSafe branch_box_3799 := by
  left; refine ⟨branch_box_3799_nonnegative, ?_⟩
  intro z hz; exact leaf_3799_sound hz

#print axioms batch_75_00_ok
#print axioms leaf_3750_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
