import PeaceableQueens.UpperBound.Generated.Even.CoreScaled75Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_75_00_values : List Bool := [accepted_3750]
theorem batch_75_00_ok : batch_75_00_values.all id = true := by decide

def batch_75_01_values : List Bool := [accepted_3752]
theorem batch_75_01_ok : batch_75_01_values.all id = true := by decide

def batch_75_02_values : List Bool := [accepted_3753]
theorem batch_75_02_ok : batch_75_02_values.all id = true := by decide

def batch_75_03_values : List Bool := [accepted_3756]
theorem batch_75_03_ok : batch_75_03_values.all id = true := by decide

def batch_75_04_values : List Bool := [accepted_3758]
theorem batch_75_04_ok : batch_75_04_values.all id = true := by decide

def batch_75_05_values : List Bool := [accepted_3760]
theorem batch_75_05_ok : batch_75_05_values.all id = true := by decide

def batch_75_06_values : List Bool := [accepted_3762]
theorem batch_75_06_ok : batch_75_06_values.all id = true := by decide

def batch_75_07_values : List Bool := [accepted_3764]
theorem batch_75_07_ok : batch_75_07_values.all id = true := by decide

def batch_75_08_values : List Bool := [accepted_3765]
theorem batch_75_08_ok : batch_75_08_values.all id = true := by decide

def batch_75_09_values : List Bool := [accepted_3767]
theorem batch_75_09_ok : batch_75_09_values.all id = true := by decide

def batch_75_10_values : List Bool := [accepted_3770]
theorem batch_75_10_ok : batch_75_10_values.all id = true := by decide

def batch_75_11_values : List Bool := [accepted_3772]
theorem batch_75_11_ok : batch_75_11_values.all id = true := by decide

def batch_75_12_values : List Bool := [accepted_3774]
theorem batch_75_12_ok : batch_75_12_values.all id = true := by decide

def batch_75_13_values : List Bool := [accepted_3776]
theorem batch_75_13_ok : batch_75_13_values.all id = true := by decide

def batch_75_14_values : List Bool := [accepted_3778]
theorem batch_75_14_ok : batch_75_14_values.all id = true := by decide

def batch_75_15_values : List Bool := [accepted_3779]
theorem batch_75_15_ok : batch_75_15_values.all id = true := by decide

def batch_75_16_values : List Bool := [accepted_3782]
theorem batch_75_16_ok : batch_75_16_values.all id = true := by decide

def batch_75_17_values : List Bool := [accepted_3784]
theorem batch_75_17_ok : batch_75_17_values.all id = true := by decide

def batch_75_18_values : List Bool := [accepted_3786]
theorem batch_75_18_ok : batch_75_18_values.all id = true := by decide

def batch_75_19_values : List Bool := [accepted_3788]
theorem batch_75_19_ok : batch_75_19_values.all id = true := by decide

def batch_75_20_values : List Bool := [accepted_3792]
theorem batch_75_20_ok : batch_75_20_values.all id = true := by decide

def batch_75_21_values : List Bool := [accepted_3794]
theorem batch_75_21_ok : batch_75_21_values.all id = true := by decide

def batch_75_22_values : List Bool := [accepted_3795]
theorem batch_75_22_ok : batch_75_22_values.all id = true := by decide

def batch_75_23_values : List Bool := [accepted_3797]
theorem batch_75_23_ok : batch_75_23_values.all id = true := by decide

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

theorem leaf_3752_ok : checkAt 527 1000 box_3752 cert_3752 = true := by
  have h := List.all_eq_true.mp batch_75_01_ok accepted_3752 (by simp [batch_75_01_values])
  exact h
theorem leaf_3752_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3752.profileLo box_3752.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3752_ok
theorem branch_box_3752_nonnegative : ∀ j, 0 ≤ branch_box_3752.lower j ∧ 0 ≤ branch_box_3752.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3752, Box.profileLo, Box.profileHi, box_3752]
theorem leaf_3752_BranchSafe : CertificateConsequences.BranchSafe branch_box_3752 := by
  left; refine ⟨branch_box_3752_nonnegative, ?_⟩
  intro z hz; exact leaf_3752_sound hz

theorem leaf_3753_ok : checkAt 527 1000 box_3753 cert_3753 = true := by
  have h := List.all_eq_true.mp batch_75_02_ok accepted_3753 (by simp [batch_75_02_values])
  exact h
theorem leaf_3753_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3753.profileLo box_3753.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3753_ok
theorem branch_box_3753_nonnegative : ∀ j, 0 ≤ branch_box_3753.lower j ∧ 0 ≤ branch_box_3753.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3753, Box.profileLo, Box.profileHi, box_3753]
theorem leaf_3753_BranchSafe : CertificateConsequences.BranchSafe branch_box_3753 := by
  left; refine ⟨branch_box_3753_nonnegative, ?_⟩
  intro z hz; exact leaf_3753_sound hz

theorem leaf_3756_ok : checkAt 527 1000 box_3756 cert_3756 = true := by
  have h := List.all_eq_true.mp batch_75_03_ok accepted_3756 (by simp [batch_75_03_values])
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
  have h := List.all_eq_true.mp batch_75_04_ok accepted_3758 (by simp [batch_75_04_values])
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

theorem leaf_3760_ok : checkAt 527 1000 box_3760 cert_3760 = true := by
  have h := List.all_eq_true.mp batch_75_05_ok accepted_3760 (by simp [batch_75_05_values])
  exact h
theorem leaf_3760_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3760.profileLo box_3760.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3760_ok
theorem branch_box_3760_nonnegative : ∀ j, 0 ≤ branch_box_3760.lower j ∧ 0 ≤ branch_box_3760.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3760, Box.profileLo, Box.profileHi, box_3760]
theorem leaf_3760_BranchSafe : CertificateConsequences.BranchSafe branch_box_3760 := by
  left; refine ⟨branch_box_3760_nonnegative, ?_⟩
  intro z hz; exact leaf_3760_sound hz

theorem leaf_3762_ok : checkAt 527 1000 box_3762 cert_3762 = true := by
  have h := List.all_eq_true.mp batch_75_06_ok accepted_3762 (by simp [batch_75_06_values])
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

theorem leaf_3764_ok : checkAt 527 1000 box_3764 cert_3764 = true := by
  have h := List.all_eq_true.mp batch_75_07_ok accepted_3764 (by simp [batch_75_07_values])
  exact h
theorem leaf_3764_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3764.profileLo box_3764.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3764_ok
theorem branch_box_3764_nonnegative : ∀ j, 0 ≤ branch_box_3764.lower j ∧ 0 ≤ branch_box_3764.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3764, Box.profileLo, Box.profileHi, box_3764]
theorem leaf_3764_BranchSafe : CertificateConsequences.BranchSafe branch_box_3764 := by
  left; refine ⟨branch_box_3764_nonnegative, ?_⟩
  intro z hz; exact leaf_3764_sound hz

theorem leaf_3765_ok : checkAt 527 1000 box_3765 cert_3765 = true := by
  have h := List.all_eq_true.mp batch_75_08_ok accepted_3765 (by simp [batch_75_08_values])
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

theorem leaf_3767_ok : checkAt 527 1000 box_3767 cert_3767 = true := by
  have h := List.all_eq_true.mp batch_75_09_ok accepted_3767 (by simp [batch_75_09_values])
  exact h
theorem leaf_3767_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3767.profileLo box_3767.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3767_ok
theorem branch_box_3767_nonnegative : ∀ j, 0 ≤ branch_box_3767.lower j ∧ 0 ≤ branch_box_3767.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3767, Box.profileLo, Box.profileHi, box_3767]
theorem leaf_3767_BranchSafe : CertificateConsequences.BranchSafe branch_box_3767 := by
  left; refine ⟨branch_box_3767_nonnegative, ?_⟩
  intro z hz; exact leaf_3767_sound hz

theorem leaf_3770_ok : checkAt 527 1000 box_3770 cert_3770 = true := by
  have h := List.all_eq_true.mp batch_75_10_ok accepted_3770 (by simp [batch_75_10_values])
  exact h
theorem leaf_3770_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3770.profileLo box_3770.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3770_ok
theorem branch_box_3770_nonnegative : ∀ j, 0 ≤ branch_box_3770.lower j ∧ 0 ≤ branch_box_3770.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3770, Box.profileLo, Box.profileHi, box_3770]
theorem leaf_3770_BranchSafe : CertificateConsequences.BranchSafe branch_box_3770 := by
  left; refine ⟨branch_box_3770_nonnegative, ?_⟩
  intro z hz; exact leaf_3770_sound hz

theorem leaf_3772_ok : checkAt 527 1000 box_3772 cert_3772 = true := by
  have h := List.all_eq_true.mp batch_75_11_ok accepted_3772 (by simp [batch_75_11_values])
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

theorem leaf_3774_ok : checkAt 527 1000 box_3774 cert_3774 = true := by
  have h := List.all_eq_true.mp batch_75_12_ok accepted_3774 (by simp [batch_75_12_values])
  exact h
theorem leaf_3774_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3774.profileLo box_3774.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3774_ok
theorem branch_box_3774_nonnegative : ∀ j, 0 ≤ branch_box_3774.lower j ∧ 0 ≤ branch_box_3774.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3774, Box.profileLo, Box.profileHi, box_3774]
theorem leaf_3774_BranchSafe : CertificateConsequences.BranchSafe branch_box_3774 := by
  left; refine ⟨branch_box_3774_nonnegative, ?_⟩
  intro z hz; exact leaf_3774_sound hz

theorem leaf_3776_ok : checkAt 527 1000 box_3776 cert_3776 = true := by
  have h := List.all_eq_true.mp batch_75_13_ok accepted_3776 (by simp [batch_75_13_values])
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

theorem leaf_3778_ok : checkAt 527 1000 box_3778 cert_3778 = true := by
  have h := List.all_eq_true.mp batch_75_14_ok accepted_3778 (by simp [batch_75_14_values])
  exact h
theorem leaf_3778_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3778.profileLo box_3778.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3778_ok
theorem branch_box_3778_nonnegative : ∀ j, 0 ≤ branch_box_3778.lower j ∧ 0 ≤ branch_box_3778.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3778, Box.profileLo, Box.profileHi, box_3778]
theorem leaf_3778_BranchSafe : CertificateConsequences.BranchSafe branch_box_3778 := by
  left; refine ⟨branch_box_3778_nonnegative, ?_⟩
  intro z hz; exact leaf_3778_sound hz

theorem leaf_3779_ok : checkAt 527 1000 box_3779 cert_3779 = true := by
  have h := List.all_eq_true.mp batch_75_15_ok accepted_3779 (by simp [batch_75_15_values])
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

theorem leaf_3782_ok : checkAt 527 1000 box_3782 cert_3782 = true := by
  have h := List.all_eq_true.mp batch_75_16_ok accepted_3782 (by simp [batch_75_16_values])
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

theorem leaf_3786_ok : checkAt 527 1000 box_3786 cert_3786 = true := by
  have h := List.all_eq_true.mp batch_75_18_ok accepted_3786 (by simp [batch_75_18_values])
  exact h
theorem leaf_3786_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3786.profileLo box_3786.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3786_ok
theorem branch_box_3786_nonnegative : ∀ j, 0 ≤ branch_box_3786.lower j ∧ 0 ≤ branch_box_3786.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3786, Box.profileLo, Box.profileHi, box_3786]
theorem leaf_3786_BranchSafe : CertificateConsequences.BranchSafe branch_box_3786 := by
  left; refine ⟨branch_box_3786_nonnegative, ?_⟩
  intro z hz; exact leaf_3786_sound hz

theorem leaf_3788_ok : checkAt 527 1000 box_3788 cert_3788 = true := by
  have h := List.all_eq_true.mp batch_75_19_ok accepted_3788 (by simp [batch_75_19_values])
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

theorem leaf_3792_ok : checkAt 527 1000 box_3792 cert_3792 = true := by
  have h := List.all_eq_true.mp batch_75_20_ok accepted_3792 (by simp [batch_75_20_values])
  exact h
theorem leaf_3792_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3792.profileLo box_3792.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3792_ok
theorem branch_box_3792_nonnegative : ∀ j, 0 ≤ branch_box_3792.lower j ∧ 0 ≤ branch_box_3792.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3792, Box.profileLo, Box.profileHi, box_3792]
theorem leaf_3792_BranchSafe : CertificateConsequences.BranchSafe branch_box_3792 := by
  left; refine ⟨branch_box_3792_nonnegative, ?_⟩
  intro z hz; exact leaf_3792_sound hz

theorem leaf_3794_ok : checkAt 527 1000 box_3794 cert_3794 = true := by
  have h := List.all_eq_true.mp batch_75_21_ok accepted_3794 (by simp [batch_75_21_values])
  exact h
theorem leaf_3794_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3794.profileLo box_3794.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3794_ok
theorem branch_box_3794_nonnegative : ∀ j, 0 ≤ branch_box_3794.lower j ∧ 0 ≤ branch_box_3794.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3794, Box.profileLo, Box.profileHi, box_3794]
theorem leaf_3794_BranchSafe : CertificateConsequences.BranchSafe branch_box_3794 := by
  left; refine ⟨branch_box_3794_nonnegative, ?_⟩
  intro z hz; exact leaf_3794_sound hz

theorem leaf_3795_ok : checkAt 527 1000 box_3795 cert_3795 = true := by
  have h := List.all_eq_true.mp batch_75_22_ok accepted_3795 (by simp [batch_75_22_values])
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

#print axioms batch_75_00_ok
#print axioms leaf_3750_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
