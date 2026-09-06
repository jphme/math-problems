import PeaceableQueens.UpperBound.Generated.Even.CoreScaled74Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_74_00_values : List Bool := [accepted_3700]
theorem batch_74_00_ok : batch_74_00_values.all id = true := by decide

def batch_74_01_values : List Bool := [accepted_3702]
theorem batch_74_01_ok : batch_74_01_values.all id = true := by decide

def batch_74_02_values : List Bool := [accepted_3704]
theorem batch_74_02_ok : batch_74_02_values.all id = true := by decide

def batch_74_03_values : List Bool := [accepted_3706]
theorem batch_74_03_ok : batch_74_03_values.all id = true := by decide

def batch_74_04_values : List Bool := [accepted_3707]
theorem batch_74_04_ok : batch_74_04_values.all id = true := by decide

def batch_74_05_values : List Bool := [accepted_3710]
theorem batch_74_05_ok : batch_74_05_values.all id = true := by decide

def batch_74_06_values : List Bool := [accepted_3712]
theorem batch_74_06_ok : batch_74_06_values.all id = true := by decide

def batch_74_07_values : List Bool := [accepted_3714]
theorem batch_74_07_ok : batch_74_07_values.all id = true := by decide

def batch_74_08_values : List Bool := [accepted_3718]
theorem batch_74_08_ok : batch_74_08_values.all id = true := by decide

def batch_74_09_values : List Bool := [accepted_3719]
theorem batch_74_09_ok : batch_74_09_values.all id = true := by decide

def batch_74_10_values : List Bool := [accepted_3722]
theorem batch_74_10_ok : batch_74_10_values.all id = true := by decide

def batch_74_11_values : List Bool := [accepted_3724]
theorem batch_74_11_ok : batch_74_11_values.all id = true := by decide

def batch_74_12_values : List Bool := [accepted_3726]
theorem batch_74_12_ok : batch_74_12_values.all id = true := by decide

def batch_74_13_values : List Bool := [accepted_3728]
theorem batch_74_13_ok : batch_74_13_values.all id = true := by decide

def batch_74_14_values : List Bool := [accepted_3729]
theorem batch_74_14_ok : batch_74_14_values.all id = true := by decide

def batch_74_15_values : List Bool := [accepted_3732]
theorem batch_74_15_ok : batch_74_15_values.all id = true := by decide

def batch_74_16_values : List Bool := [accepted_3734]
theorem batch_74_16_ok : batch_74_16_values.all id = true := by decide

def batch_74_17_values : List Bool := [accepted_3736]
theorem batch_74_17_ok : batch_74_17_values.all id = true := by decide

def batch_74_18_values : List Bool := [accepted_3738]
theorem batch_74_18_ok : batch_74_18_values.all id = true := by decide

def batch_74_19_values : List Bool := [accepted_3739]
theorem batch_74_19_ok : batch_74_19_values.all id = true := by decide

def batch_74_20_values : List Bool := [accepted_3741]
theorem batch_74_20_ok : batch_74_20_values.all id = true := by decide

def batch_74_21_values : List Bool := [accepted_3744]
theorem batch_74_21_ok : batch_74_21_values.all id = true := by decide

def batch_74_22_values : List Bool := [accepted_3746]
theorem batch_74_22_ok : batch_74_22_values.all id = true := by decide

def batch_74_23_values : List Bool := [accepted_3748]
theorem batch_74_23_ok : batch_74_23_values.all id = true := by decide

theorem leaf_3700_ok : checkAt 527 1000 box_3700 cert_3700 = true := by
  have h := List.all_eq_true.mp batch_74_00_ok accepted_3700 (by simp [batch_74_00_values])
  exact h
theorem leaf_3700_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3700.profileLo box_3700.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3700_ok
theorem branch_box_3700_nonnegative : ∀ j, 0 ≤ branch_box_3700.lower j ∧ 0 ≤ branch_box_3700.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3700, Box.profileLo, Box.profileHi, box_3700]
theorem leaf_3700_BranchSafe : CertificateConsequences.BranchSafe branch_box_3700 := by
  left; refine ⟨branch_box_3700_nonnegative, ?_⟩
  intro z hz; exact leaf_3700_sound hz

theorem leaf_3702_ok : checkAt 527 1000 box_3702 cert_3702 = true := by
  have h := List.all_eq_true.mp batch_74_01_ok accepted_3702 (by simp [batch_74_01_values])
  exact h
theorem leaf_3702_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3702.profileLo box_3702.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3702_ok
theorem branch_box_3702_nonnegative : ∀ j, 0 ≤ branch_box_3702.lower j ∧ 0 ≤ branch_box_3702.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3702, Box.profileLo, Box.profileHi, box_3702]
theorem leaf_3702_BranchSafe : CertificateConsequences.BranchSafe branch_box_3702 := by
  left; refine ⟨branch_box_3702_nonnegative, ?_⟩
  intro z hz; exact leaf_3702_sound hz

theorem leaf_3704_ok : checkAt 527 1000 box_3704 cert_3704 = true := by
  have h := List.all_eq_true.mp batch_74_02_ok accepted_3704 (by simp [batch_74_02_values])
  exact h
theorem leaf_3704_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3704.profileLo box_3704.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3704_ok
theorem branch_box_3704_nonnegative : ∀ j, 0 ≤ branch_box_3704.lower j ∧ 0 ≤ branch_box_3704.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3704, Box.profileLo, Box.profileHi, box_3704]
theorem leaf_3704_BranchSafe : CertificateConsequences.BranchSafe branch_box_3704 := by
  left; refine ⟨branch_box_3704_nonnegative, ?_⟩
  intro z hz; exact leaf_3704_sound hz

theorem leaf_3706_ok : checkAt 527 1000 box_3706 cert_3706 = true := by
  have h := List.all_eq_true.mp batch_74_03_ok accepted_3706 (by simp [batch_74_03_values])
  exact h
theorem leaf_3706_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3706.profileLo box_3706.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3706_ok
theorem branch_box_3706_nonnegative : ∀ j, 0 ≤ branch_box_3706.lower j ∧ 0 ≤ branch_box_3706.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3706, Box.profileLo, Box.profileHi, box_3706]
theorem leaf_3706_BranchSafe : CertificateConsequences.BranchSafe branch_box_3706 := by
  left; refine ⟨branch_box_3706_nonnegative, ?_⟩
  intro z hz; exact leaf_3706_sound hz

theorem leaf_3707_ok : checkAt 527 1000 box_3707 cert_3707 = true := by
  have h := List.all_eq_true.mp batch_74_04_ok accepted_3707 (by simp [batch_74_04_values])
  exact h
theorem leaf_3707_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3707.profileLo box_3707.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3707_ok
theorem branch_box_3707_nonnegative : ∀ j, 0 ≤ branch_box_3707.lower j ∧ 0 ≤ branch_box_3707.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3707, Box.profileLo, Box.profileHi, box_3707]
theorem leaf_3707_BranchSafe : CertificateConsequences.BranchSafe branch_box_3707 := by
  left; refine ⟨branch_box_3707_nonnegative, ?_⟩
  intro z hz; exact leaf_3707_sound hz

theorem leaf_3710_ok : checkAt 527 1000 box_3710 cert_3710 = true := by
  have h := List.all_eq_true.mp batch_74_05_ok accepted_3710 (by simp [batch_74_05_values])
  exact h
theorem leaf_3710_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3710.profileLo box_3710.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3710_ok
theorem branch_box_3710_nonnegative : ∀ j, 0 ≤ branch_box_3710.lower j ∧ 0 ≤ branch_box_3710.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3710, Box.profileLo, Box.profileHi, box_3710]
theorem leaf_3710_BranchSafe : CertificateConsequences.BranchSafe branch_box_3710 := by
  left; refine ⟨branch_box_3710_nonnegative, ?_⟩
  intro z hz; exact leaf_3710_sound hz

theorem leaf_3712_ok : checkAt 527 1000 box_3712 cert_3712 = true := by
  have h := List.all_eq_true.mp batch_74_06_ok accepted_3712 (by simp [batch_74_06_values])
  exact h
theorem leaf_3712_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3712.profileLo box_3712.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3712_ok
theorem branch_box_3712_nonnegative : ∀ j, 0 ≤ branch_box_3712.lower j ∧ 0 ≤ branch_box_3712.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3712, Box.profileLo, Box.profileHi, box_3712]
theorem leaf_3712_BranchSafe : CertificateConsequences.BranchSafe branch_box_3712 := by
  left; refine ⟨branch_box_3712_nonnegative, ?_⟩
  intro z hz; exact leaf_3712_sound hz

theorem leaf_3714_ok : checkAt 527 1000 box_3714 cert_3714 = true := by
  have h := List.all_eq_true.mp batch_74_07_ok accepted_3714 (by simp [batch_74_07_values])
  exact h
theorem leaf_3714_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3714.profileLo box_3714.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3714_ok
theorem branch_box_3714_nonnegative : ∀ j, 0 ≤ branch_box_3714.lower j ∧ 0 ≤ branch_box_3714.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3714, Box.profileLo, Box.profileHi, box_3714]
theorem leaf_3714_BranchSafe : CertificateConsequences.BranchSafe branch_box_3714 := by
  left; refine ⟨branch_box_3714_nonnegative, ?_⟩
  intro z hz; exact leaf_3714_sound hz

theorem leaf_3718_ok : checkAt 527 1000 box_3718 cert_3718 = true := by
  have h := List.all_eq_true.mp batch_74_08_ok accepted_3718 (by simp [batch_74_08_values])
  exact h
theorem leaf_3718_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3718.profileLo box_3718.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3718_ok
theorem branch_box_3718_nonnegative : ∀ j, 0 ≤ branch_box_3718.lower j ∧ 0 ≤ branch_box_3718.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3718, Box.profileLo, Box.profileHi, box_3718]
theorem leaf_3718_BranchSafe : CertificateConsequences.BranchSafe branch_box_3718 := by
  left; refine ⟨branch_box_3718_nonnegative, ?_⟩
  intro z hz; exact leaf_3718_sound hz

theorem leaf_3719_ok : checkAt 527 1000 box_3719 cert_3719 = true := by
  have h := List.all_eq_true.mp batch_74_09_ok accepted_3719 (by simp [batch_74_09_values])
  exact h
theorem leaf_3719_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3719.profileLo box_3719.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3719_ok
theorem branch_box_3719_nonnegative : ∀ j, 0 ≤ branch_box_3719.lower j ∧ 0 ≤ branch_box_3719.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3719, Box.profileLo, Box.profileHi, box_3719]
theorem leaf_3719_BranchSafe : CertificateConsequences.BranchSafe branch_box_3719 := by
  left; refine ⟨branch_box_3719_nonnegative, ?_⟩
  intro z hz; exact leaf_3719_sound hz

theorem leaf_3722_ok : checkAt 527 1000 box_3722 cert_3722 = true := by
  have h := List.all_eq_true.mp batch_74_10_ok accepted_3722 (by simp [batch_74_10_values])
  exact h
theorem leaf_3722_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3722.profileLo box_3722.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3722_ok
theorem branch_box_3722_nonnegative : ∀ j, 0 ≤ branch_box_3722.lower j ∧ 0 ≤ branch_box_3722.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3722, Box.profileLo, Box.profileHi, box_3722]
theorem leaf_3722_BranchSafe : CertificateConsequences.BranchSafe branch_box_3722 := by
  left; refine ⟨branch_box_3722_nonnegative, ?_⟩
  intro z hz; exact leaf_3722_sound hz

theorem leaf_3724_ok : checkAt 527 1000 box_3724 cert_3724 = true := by
  have h := List.all_eq_true.mp batch_74_11_ok accepted_3724 (by simp [batch_74_11_values])
  exact h
theorem leaf_3724_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3724.profileLo box_3724.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3724_ok
theorem branch_box_3724_nonnegative : ∀ j, 0 ≤ branch_box_3724.lower j ∧ 0 ≤ branch_box_3724.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3724, Box.profileLo, Box.profileHi, box_3724]
theorem leaf_3724_BranchSafe : CertificateConsequences.BranchSafe branch_box_3724 := by
  left; refine ⟨branch_box_3724_nonnegative, ?_⟩
  intro z hz; exact leaf_3724_sound hz

theorem leaf_3726_ok : checkAt 527 1000 box_3726 cert_3726 = true := by
  have h := List.all_eq_true.mp batch_74_12_ok accepted_3726 (by simp [batch_74_12_values])
  exact h
theorem leaf_3726_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3726.profileLo box_3726.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3726_ok
theorem branch_box_3726_nonnegative : ∀ j, 0 ≤ branch_box_3726.lower j ∧ 0 ≤ branch_box_3726.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3726, Box.profileLo, Box.profileHi, box_3726]
theorem leaf_3726_BranchSafe : CertificateConsequences.BranchSafe branch_box_3726 := by
  left; refine ⟨branch_box_3726_nonnegative, ?_⟩
  intro z hz; exact leaf_3726_sound hz

theorem leaf_3728_ok : checkAt 527 1000 box_3728 cert_3728 = true := by
  have h := List.all_eq_true.mp batch_74_13_ok accepted_3728 (by simp [batch_74_13_values])
  exact h
theorem leaf_3728_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3728.profileLo box_3728.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3728_ok
theorem branch_box_3728_nonnegative : ∀ j, 0 ≤ branch_box_3728.lower j ∧ 0 ≤ branch_box_3728.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3728, Box.profileLo, Box.profileHi, box_3728]
theorem leaf_3728_BranchSafe : CertificateConsequences.BranchSafe branch_box_3728 := by
  left; refine ⟨branch_box_3728_nonnegative, ?_⟩
  intro z hz; exact leaf_3728_sound hz

theorem leaf_3729_ok : checkAt 527 1000 box_3729 cert_3729 = true := by
  have h := List.all_eq_true.mp batch_74_14_ok accepted_3729 (by simp [batch_74_14_values])
  exact h
theorem leaf_3729_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3729.profileLo box_3729.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3729_ok
theorem branch_box_3729_nonnegative : ∀ j, 0 ≤ branch_box_3729.lower j ∧ 0 ≤ branch_box_3729.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3729, Box.profileLo, Box.profileHi, box_3729]
theorem leaf_3729_BranchSafe : CertificateConsequences.BranchSafe branch_box_3729 := by
  left; refine ⟨branch_box_3729_nonnegative, ?_⟩
  intro z hz; exact leaf_3729_sound hz

theorem leaf_3732_ok : checkAt 527 1000 box_3732 cert_3732 = true := by
  have h := List.all_eq_true.mp batch_74_15_ok accepted_3732 (by simp [batch_74_15_values])
  exact h
theorem leaf_3732_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3732.profileLo box_3732.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3732_ok
theorem branch_box_3732_nonnegative : ∀ j, 0 ≤ branch_box_3732.lower j ∧ 0 ≤ branch_box_3732.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3732, Box.profileLo, Box.profileHi, box_3732]
theorem leaf_3732_BranchSafe : CertificateConsequences.BranchSafe branch_box_3732 := by
  left; refine ⟨branch_box_3732_nonnegative, ?_⟩
  intro z hz; exact leaf_3732_sound hz

theorem leaf_3734_ok : checkAt 527 1000 box_3734 cert_3734 = true := by
  have h := List.all_eq_true.mp batch_74_16_ok accepted_3734 (by simp [batch_74_16_values])
  exact h
theorem leaf_3734_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3734.profileLo box_3734.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3734_ok
theorem branch_box_3734_nonnegative : ∀ j, 0 ≤ branch_box_3734.lower j ∧ 0 ≤ branch_box_3734.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3734, Box.profileLo, Box.profileHi, box_3734]
theorem leaf_3734_BranchSafe : CertificateConsequences.BranchSafe branch_box_3734 := by
  left; refine ⟨branch_box_3734_nonnegative, ?_⟩
  intro z hz; exact leaf_3734_sound hz

theorem leaf_3736_ok : checkAt 527 1000 box_3736 cert_3736 = true := by
  have h := List.all_eq_true.mp batch_74_17_ok accepted_3736 (by simp [batch_74_17_values])
  exact h
theorem leaf_3736_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3736.profileLo box_3736.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3736_ok
theorem branch_box_3736_nonnegative : ∀ j, 0 ≤ branch_box_3736.lower j ∧ 0 ≤ branch_box_3736.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3736, Box.profileLo, Box.profileHi, box_3736]
theorem leaf_3736_BranchSafe : CertificateConsequences.BranchSafe branch_box_3736 := by
  left; refine ⟨branch_box_3736_nonnegative, ?_⟩
  intro z hz; exact leaf_3736_sound hz

theorem leaf_3738_ok : checkAt 527 1000 box_3738 cert_3738 = true := by
  have h := List.all_eq_true.mp batch_74_18_ok accepted_3738 (by simp [batch_74_18_values])
  exact h
theorem leaf_3738_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3738.profileLo box_3738.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3738_ok
theorem branch_box_3738_nonnegative : ∀ j, 0 ≤ branch_box_3738.lower j ∧ 0 ≤ branch_box_3738.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3738, Box.profileLo, Box.profileHi, box_3738]
theorem leaf_3738_BranchSafe : CertificateConsequences.BranchSafe branch_box_3738 := by
  left; refine ⟨branch_box_3738_nonnegative, ?_⟩
  intro z hz; exact leaf_3738_sound hz

theorem leaf_3739_ok : checkAt 527 1000 box_3739 cert_3739 = true := by
  have h := List.all_eq_true.mp batch_74_19_ok accepted_3739 (by simp [batch_74_19_values])
  exact h
theorem leaf_3739_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3739.profileLo box_3739.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3739_ok
theorem branch_box_3739_nonnegative : ∀ j, 0 ≤ branch_box_3739.lower j ∧ 0 ≤ branch_box_3739.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3739, Box.profileLo, Box.profileHi, box_3739]
theorem leaf_3739_BranchSafe : CertificateConsequences.BranchSafe branch_box_3739 := by
  left; refine ⟨branch_box_3739_nonnegative, ?_⟩
  intro z hz; exact leaf_3739_sound hz

theorem leaf_3741_ok : checkAt 527 1000 box_3741 cert_3741 = true := by
  have h := List.all_eq_true.mp batch_74_20_ok accepted_3741 (by simp [batch_74_20_values])
  exact h
theorem leaf_3741_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3741.profileLo box_3741.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3741_ok
theorem branch_box_3741_nonnegative : ∀ j, 0 ≤ branch_box_3741.lower j ∧ 0 ≤ branch_box_3741.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3741, Box.profileLo, Box.profileHi, box_3741]
theorem leaf_3741_BranchSafe : CertificateConsequences.BranchSafe branch_box_3741 := by
  left; refine ⟨branch_box_3741_nonnegative, ?_⟩
  intro z hz; exact leaf_3741_sound hz

theorem leaf_3744_ok : checkAt 527 1000 box_3744 cert_3744 = true := by
  have h := List.all_eq_true.mp batch_74_21_ok accepted_3744 (by simp [batch_74_21_values])
  exact h
theorem leaf_3744_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3744.profileLo box_3744.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3744_ok
theorem branch_box_3744_nonnegative : ∀ j, 0 ≤ branch_box_3744.lower j ∧ 0 ≤ branch_box_3744.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3744, Box.profileLo, Box.profileHi, box_3744]
theorem leaf_3744_BranchSafe : CertificateConsequences.BranchSafe branch_box_3744 := by
  left; refine ⟨branch_box_3744_nonnegative, ?_⟩
  intro z hz; exact leaf_3744_sound hz

theorem leaf_3746_ok : checkAt 527 1000 box_3746 cert_3746 = true := by
  have h := List.all_eq_true.mp batch_74_22_ok accepted_3746 (by simp [batch_74_22_values])
  exact h
theorem leaf_3746_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3746.profileLo box_3746.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3746_ok
theorem branch_box_3746_nonnegative : ∀ j, 0 ≤ branch_box_3746.lower j ∧ 0 ≤ branch_box_3746.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3746, Box.profileLo, Box.profileHi, box_3746]
theorem leaf_3746_BranchSafe : CertificateConsequences.BranchSafe branch_box_3746 := by
  left; refine ⟨branch_box_3746_nonnegative, ?_⟩
  intro z hz; exact leaf_3746_sound hz

theorem leaf_3748_ok : checkAt 527 1000 box_3748 cert_3748 = true := by
  have h := List.all_eq_true.mp batch_74_23_ok accepted_3748 (by simp [batch_74_23_values])
  exact h
theorem leaf_3748_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3748.profileLo box_3748.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3748_ok
theorem branch_box_3748_nonnegative : ∀ j, 0 ≤ branch_box_3748.lower j ∧ 0 ≤ branch_box_3748.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3748, Box.profileLo, Box.profileHi, box_3748]
theorem leaf_3748_BranchSafe : CertificateConsequences.BranchSafe branch_box_3748 := by
  left; refine ⟨branch_box_3748_nonnegative, ?_⟩
  intro z hz; exact leaf_3748_sound hz

#print axioms batch_74_00_ok
#print axioms leaf_3700_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
