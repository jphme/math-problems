import PeaceableQueens.UpperBound.Generated.Even.C527Scaled74Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_74_00_values : List Bool := [accepted_3702]
theorem batch_74_00_ok : batch_74_00_values.all id = true := by decide

def batch_74_01_values : List Bool := [accepted_3703]
theorem batch_74_01_ok : batch_74_01_values.all id = true := by decide

def batch_74_02_values : List Bool := [accepted_3704]
theorem batch_74_02_ok : batch_74_02_values.all id = true := by decide

def batch_74_03_values : List Bool := [accepted_3706]
theorem batch_74_03_ok : batch_74_03_values.all id = true := by decide

def batch_74_04_values : List Bool := [accepted_3707]
theorem batch_74_04_ok : batch_74_04_values.all id = true := by decide

def batch_74_05_values : List Bool := [accepted_3708]
theorem batch_74_05_ok : batch_74_05_values.all id = true := by decide

def batch_74_06_values : List Bool := [accepted_3714]
theorem batch_74_06_ok : batch_74_06_values.all id = true := by decide

def batch_74_07_values : List Bool := [accepted_3715]
theorem batch_74_07_ok : batch_74_07_values.all id = true := by decide

def batch_74_08_values : List Bool := [accepted_3716]
theorem batch_74_08_ok : batch_74_08_values.all id = true := by decide

def batch_74_09_values : List Bool := [accepted_3717]
theorem batch_74_09_ok : batch_74_09_values.all id = true := by decide

def batch_74_10_values : List Bool := [accepted_3718]
theorem batch_74_10_ok : batch_74_10_values.all id = true := by decide

def batch_74_11_values : List Bool := [accepted_3723]
theorem batch_74_11_ok : batch_74_11_values.all id = true := by decide

def batch_74_12_values : List Bool := [accepted_3724]
theorem batch_74_12_ok : batch_74_12_values.all id = true := by decide

def batch_74_13_values : List Bool := [accepted_3726]
theorem batch_74_13_ok : batch_74_13_values.all id = true := by decide

def batch_74_14_values : List Bool := [accepted_3727]
theorem batch_74_14_ok : batch_74_14_values.all id = true := by decide

def batch_74_15_values : List Bool := [accepted_3728]
theorem batch_74_15_ok : batch_74_15_values.all id = true := by decide

def batch_74_16_values : List Bool := [accepted_3729]
theorem batch_74_16_ok : batch_74_16_values.all id = true := by decide

def batch_74_17_values : List Bool := [accepted_3731]
theorem batch_74_17_ok : batch_74_17_values.all id = true := by decide

def batch_74_18_values : List Bool := [accepted_3732]
theorem batch_74_18_ok : batch_74_18_values.all id = true := by decide

def batch_74_19_values : List Bool := [accepted_3748]
theorem batch_74_19_ok : batch_74_19_values.all id = true := by decide

def batch_74_20_values : List Bool := [accepted_3749]
theorem batch_74_20_ok : batch_74_20_values.all id = true := by decide

theorem leaf_3702_ok : checkAt 527 1000 box_3702 cert_3702 = true := by
  have h := List.all_eq_true.mp batch_74_00_ok accepted_3702 (by simp [batch_74_00_values])
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

theorem leaf_3703_ok : checkAt 527 1000 box_3703 cert_3703 = true := by
  have h := List.all_eq_true.mp batch_74_01_ok accepted_3703 (by simp [batch_74_01_values])
  exact h
theorem leaf_3703_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3703.profileLo box_3703.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3703_ok
theorem branch_box_3703_nonnegative : ∀ j, 0 ≤ branch_box_3703.lower j ∧ 0 ≤ branch_box_3703.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3703, Box.profileLo, Box.profileHi, box_3703]
theorem leaf_3703_BranchSafe : CertificateConsequences.BranchSafe branch_box_3703 := by
  left; refine ⟨branch_box_3703_nonnegative, ?_⟩
  intro z hz; exact leaf_3703_sound hz

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

theorem leaf_3708_ok : checkAt 527 1000 box_3708 cert_3708 = true := by
  have h := List.all_eq_true.mp batch_74_05_ok accepted_3708 (by simp [batch_74_05_values])
  exact h
theorem leaf_3708_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3708.profileLo box_3708.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3708_ok
theorem branch_box_3708_nonnegative : ∀ j, 0 ≤ branch_box_3708.lower j ∧ 0 ≤ branch_box_3708.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3708, Box.profileLo, Box.profileHi, box_3708]
theorem leaf_3708_BranchSafe : CertificateConsequences.BranchSafe branch_box_3708 := by
  left; refine ⟨branch_box_3708_nonnegative, ?_⟩
  intro z hz; exact leaf_3708_sound hz

theorem leaf_3714_ok : checkAt 527 1000 box_3714 cert_3714 = true := by
  have h := List.all_eq_true.mp batch_74_06_ok accepted_3714 (by simp [batch_74_06_values])
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

theorem leaf_3715_ok : checkAt 527 1000 box_3715 cert_3715 = true := by
  have h := List.all_eq_true.mp batch_74_07_ok accepted_3715 (by simp [batch_74_07_values])
  exact h
theorem leaf_3715_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3715.profileLo box_3715.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3715_ok
theorem branch_box_3715_nonnegative : ∀ j, 0 ≤ branch_box_3715.lower j ∧ 0 ≤ branch_box_3715.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3715, Box.profileLo, Box.profileHi, box_3715]
theorem leaf_3715_BranchSafe : CertificateConsequences.BranchSafe branch_box_3715 := by
  left; refine ⟨branch_box_3715_nonnegative, ?_⟩
  intro z hz; exact leaf_3715_sound hz

theorem leaf_3716_ok : checkAt 527 1000 box_3716 cert_3716 = true := by
  have h := List.all_eq_true.mp batch_74_08_ok accepted_3716 (by simp [batch_74_08_values])
  exact h
theorem leaf_3716_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3716.profileLo box_3716.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3716_ok
theorem branch_box_3716_nonnegative : ∀ j, 0 ≤ branch_box_3716.lower j ∧ 0 ≤ branch_box_3716.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3716, Box.profileLo, Box.profileHi, box_3716]
theorem leaf_3716_BranchSafe : CertificateConsequences.BranchSafe branch_box_3716 := by
  left; refine ⟨branch_box_3716_nonnegative, ?_⟩
  intro z hz; exact leaf_3716_sound hz

theorem leaf_3717_ok : checkAt 527 1000 box_3717 cert_3717 = true := by
  have h := List.all_eq_true.mp batch_74_09_ok accepted_3717 (by simp [batch_74_09_values])
  exact h
theorem leaf_3717_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3717.profileLo box_3717.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3717_ok
theorem branch_box_3717_nonnegative : ∀ j, 0 ≤ branch_box_3717.lower j ∧ 0 ≤ branch_box_3717.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3717, Box.profileLo, Box.profileHi, box_3717]
theorem leaf_3717_BranchSafe : CertificateConsequences.BranchSafe branch_box_3717 := by
  left; refine ⟨branch_box_3717_nonnegative, ?_⟩
  intro z hz; exact leaf_3717_sound hz

theorem leaf_3718_ok : checkAt 527 1000 box_3718 cert_3718 = true := by
  have h := List.all_eq_true.mp batch_74_10_ok accepted_3718 (by simp [batch_74_10_values])
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

theorem leaf_3723_ok : checkAt 527 1000 box_3723 cert_3723 = true := by
  have h := List.all_eq_true.mp batch_74_11_ok accepted_3723 (by simp [batch_74_11_values])
  exact h
theorem leaf_3723_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3723.profileLo box_3723.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3723_ok
theorem branch_box_3723_nonnegative : ∀ j, 0 ≤ branch_box_3723.lower j ∧ 0 ≤ branch_box_3723.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3723, Box.profileLo, Box.profileHi, box_3723]
theorem leaf_3723_BranchSafe : CertificateConsequences.BranchSafe branch_box_3723 := by
  left; refine ⟨branch_box_3723_nonnegative, ?_⟩
  intro z hz; exact leaf_3723_sound hz

theorem leaf_3724_ok : checkAt 527 1000 box_3724 cert_3724 = true := by
  have h := List.all_eq_true.mp batch_74_12_ok accepted_3724 (by simp [batch_74_12_values])
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
  have h := List.all_eq_true.mp batch_74_13_ok accepted_3726 (by simp [batch_74_13_values])
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

theorem leaf_3727_ok : checkAt 527 1000 box_3727 cert_3727 = true := by
  have h := List.all_eq_true.mp batch_74_14_ok accepted_3727 (by simp [batch_74_14_values])
  exact h
theorem leaf_3727_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3727.profileLo box_3727.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3727_ok
theorem branch_box_3727_nonnegative : ∀ j, 0 ≤ branch_box_3727.lower j ∧ 0 ≤ branch_box_3727.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3727, Box.profileLo, Box.profileHi, box_3727]
theorem leaf_3727_BranchSafe : CertificateConsequences.BranchSafe branch_box_3727 := by
  left; refine ⟨branch_box_3727_nonnegative, ?_⟩
  intro z hz; exact leaf_3727_sound hz

theorem leaf_3728_ok : checkAt 527 1000 box_3728 cert_3728 = true := by
  have h := List.all_eq_true.mp batch_74_15_ok accepted_3728 (by simp [batch_74_15_values])
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
  have h := List.all_eq_true.mp batch_74_16_ok accepted_3729 (by simp [batch_74_16_values])
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

theorem leaf_3731_ok : checkAt 527 1000 box_3731 cert_3731 = true := by
  have h := List.all_eq_true.mp batch_74_17_ok accepted_3731 (by simp [batch_74_17_values])
  exact h
theorem leaf_3731_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3731.profileLo box_3731.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3731_ok
theorem branch_box_3731_nonnegative : ∀ j, 0 ≤ branch_box_3731.lower j ∧ 0 ≤ branch_box_3731.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3731, Box.profileLo, Box.profileHi, box_3731]
theorem leaf_3731_BranchSafe : CertificateConsequences.BranchSafe branch_box_3731 := by
  left; refine ⟨branch_box_3731_nonnegative, ?_⟩
  intro z hz; exact leaf_3731_sound hz

theorem leaf_3732_ok : checkAt 527 1000 box_3732 cert_3732 = true := by
  have h := List.all_eq_true.mp batch_74_18_ok accepted_3732 (by simp [batch_74_18_values])
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

theorem leaf_3748_ok : checkAt 527 1000 box_3748 cert_3748 = true := by
  have h := List.all_eq_true.mp batch_74_19_ok accepted_3748 (by simp [batch_74_19_values])
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

theorem leaf_3749_ok : checkAt 527 1000 box_3749 cert_3749 = true := by
  have h := List.all_eq_true.mp batch_74_20_ok accepted_3749 (by simp [batch_74_20_values])
  exact h
theorem leaf_3749_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3749.profileLo box_3749.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3749_ok
theorem branch_box_3749_nonnegative : ∀ j, 0 ≤ branch_box_3749.lower j ∧ 0 ≤ branch_box_3749.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3749, Box.profileLo, Box.profileHi, box_3749]
theorem leaf_3749_BranchSafe : CertificateConsequences.BranchSafe branch_box_3749 := by
  left; refine ⟨branch_box_3749_nonnegative, ?_⟩
  intro z hz; exact leaf_3749_sound hz

#print axioms batch_74_00_ok
#print axioms leaf_3702_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
