import PeaceableQueens.UpperBound.Generated.Even.CoreScaled15Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_15_00_values : List Bool := [accepted_750]
theorem batch_15_00_ok : batch_15_00_values.all id = true := by decide

def batch_15_01_values : List Bool := [accepted_752]
theorem batch_15_01_ok : batch_15_01_values.all id = true := by decide

def batch_15_02_values : List Bool := [accepted_754]
theorem batch_15_02_ok : batch_15_02_values.all id = true := by decide

def batch_15_03_values : List Bool := [accepted_756]
theorem batch_15_03_ok : batch_15_03_values.all id = true := by decide

def batch_15_04_values : List Bool := [accepted_762]
theorem batch_15_04_ok : batch_15_04_values.all id = true := by decide

def batch_15_05_values : List Bool := [accepted_764]
theorem batch_15_05_ok : batch_15_05_values.all id = true := by decide

def batch_15_06_values : List Bool := [accepted_766]
theorem batch_15_06_ok : batch_15_06_values.all id = true := by decide

def batch_15_07_values : List Bool := [accepted_768]
theorem batch_15_07_ok : batch_15_07_values.all id = true := by decide

def batch_15_08_values : List Bool := [accepted_770]
theorem batch_15_08_ok : batch_15_08_values.all id = true := by decide

def batch_15_09_values : List Bool := [accepted_772]
theorem batch_15_09_ok : batch_15_09_values.all id = true := by decide

def batch_15_10_values : List Bool := [accepted_773]
theorem batch_15_10_ok : batch_15_10_values.all id = true := by decide

def batch_15_11_values : List Bool := [accepted_784]
theorem batch_15_11_ok : batch_15_11_values.all id = true := by decide

def batch_15_12_values : List Bool := [accepted_786]
theorem batch_15_12_ok : batch_15_12_values.all id = true := by decide

def batch_15_13_values : List Bool := [accepted_788]
theorem batch_15_13_ok : batch_15_13_values.all id = true := by decide

def batch_15_14_values : List Bool := [accepted_790]
theorem batch_15_14_ok : batch_15_14_values.all id = true := by decide

def batch_15_15_values : List Bool := [accepted_796]
theorem batch_15_15_ok : batch_15_15_values.all id = true := by decide

def batch_15_16_values : List Bool := [accepted_798]
theorem batch_15_16_ok : batch_15_16_values.all id = true := by decide

theorem leaf_750_ok : checkAt 527 1000 box_750 cert_750 = true := by
  have h := List.all_eq_true.mp batch_15_00_ok accepted_750 (by simp [batch_15_00_values])
  exact h
theorem leaf_750_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_750.profileLo box_750.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_750_ok
theorem branch_box_750_nonnegative : ∀ j, 0 ≤ branch_box_750.lower j ∧ 0 ≤ branch_box_750.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_750, Box.profileLo, Box.profileHi, box_750]
theorem leaf_750_BranchSafe : CertificateConsequences.BranchSafe branch_box_750 := by
  left; refine ⟨branch_box_750_nonnegative, ?_⟩
  intro z hz; exact leaf_750_sound hz

theorem leaf_752_ok : checkAt 527 1000 box_752 cert_752 = true := by
  have h := List.all_eq_true.mp batch_15_01_ok accepted_752 (by simp [batch_15_01_values])
  exact h
theorem leaf_752_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_752.profileLo box_752.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_752_ok
theorem branch_box_752_nonnegative : ∀ j, 0 ≤ branch_box_752.lower j ∧ 0 ≤ branch_box_752.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_752, Box.profileLo, Box.profileHi, box_752]
theorem leaf_752_BranchSafe : CertificateConsequences.BranchSafe branch_box_752 := by
  left; refine ⟨branch_box_752_nonnegative, ?_⟩
  intro z hz; exact leaf_752_sound hz

theorem leaf_754_ok : checkAt 527 1000 box_754 cert_754 = true := by
  have h := List.all_eq_true.mp batch_15_02_ok accepted_754 (by simp [batch_15_02_values])
  exact h
theorem leaf_754_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_754.profileLo box_754.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_754_ok
theorem branch_box_754_nonnegative : ∀ j, 0 ≤ branch_box_754.lower j ∧ 0 ≤ branch_box_754.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_754, Box.profileLo, Box.profileHi, box_754]
theorem leaf_754_BranchSafe : CertificateConsequences.BranchSafe branch_box_754 := by
  left; refine ⟨branch_box_754_nonnegative, ?_⟩
  intro z hz; exact leaf_754_sound hz

theorem leaf_756_ok : checkAt 527 1000 box_756 cert_756 = true := by
  have h := List.all_eq_true.mp batch_15_03_ok accepted_756 (by simp [batch_15_03_values])
  exact h
theorem leaf_756_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_756.profileLo box_756.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_756_ok
theorem branch_box_756_nonnegative : ∀ j, 0 ≤ branch_box_756.lower j ∧ 0 ≤ branch_box_756.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_756, Box.profileLo, Box.profileHi, box_756]
theorem leaf_756_BranchSafe : CertificateConsequences.BranchSafe branch_box_756 := by
  left; refine ⟨branch_box_756_nonnegative, ?_⟩
  intro z hz; exact leaf_756_sound hz

theorem leaf_762_ok : checkAt 527 1000 box_762 cert_762 = true := by
  have h := List.all_eq_true.mp batch_15_04_ok accepted_762 (by simp [batch_15_04_values])
  exact h
theorem leaf_762_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_762.profileLo box_762.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_762_ok
theorem branch_box_762_nonnegative : ∀ j, 0 ≤ branch_box_762.lower j ∧ 0 ≤ branch_box_762.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_762, Box.profileLo, Box.profileHi, box_762]
theorem leaf_762_BranchSafe : CertificateConsequences.BranchSafe branch_box_762 := by
  left; refine ⟨branch_box_762_nonnegative, ?_⟩
  intro z hz; exact leaf_762_sound hz

theorem leaf_764_ok : checkAt 527 1000 box_764 cert_764 = true := by
  have h := List.all_eq_true.mp batch_15_05_ok accepted_764 (by simp [batch_15_05_values])
  exact h
theorem leaf_764_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_764.profileLo box_764.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_764_ok
theorem branch_box_764_nonnegative : ∀ j, 0 ≤ branch_box_764.lower j ∧ 0 ≤ branch_box_764.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_764, Box.profileLo, Box.profileHi, box_764]
theorem leaf_764_BranchSafe : CertificateConsequences.BranchSafe branch_box_764 := by
  left; refine ⟨branch_box_764_nonnegative, ?_⟩
  intro z hz; exact leaf_764_sound hz

theorem leaf_766_ok : checkAt 527 1000 box_766 cert_766 = true := by
  have h := List.all_eq_true.mp batch_15_06_ok accepted_766 (by simp [batch_15_06_values])
  exact h
theorem leaf_766_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_766.profileLo box_766.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_766_ok
theorem branch_box_766_nonnegative : ∀ j, 0 ≤ branch_box_766.lower j ∧ 0 ≤ branch_box_766.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_766, Box.profileLo, Box.profileHi, box_766]
theorem leaf_766_BranchSafe : CertificateConsequences.BranchSafe branch_box_766 := by
  left; refine ⟨branch_box_766_nonnegative, ?_⟩
  intro z hz; exact leaf_766_sound hz

theorem leaf_768_ok : checkAt 527 1000 box_768 cert_768 = true := by
  have h := List.all_eq_true.mp batch_15_07_ok accepted_768 (by simp [batch_15_07_values])
  exact h
theorem leaf_768_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_768.profileLo box_768.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_768_ok
theorem branch_box_768_nonnegative : ∀ j, 0 ≤ branch_box_768.lower j ∧ 0 ≤ branch_box_768.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_768, Box.profileLo, Box.profileHi, box_768]
theorem leaf_768_BranchSafe : CertificateConsequences.BranchSafe branch_box_768 := by
  left; refine ⟨branch_box_768_nonnegative, ?_⟩
  intro z hz; exact leaf_768_sound hz

theorem leaf_770_ok : checkAt 527 1000 box_770 cert_770 = true := by
  have h := List.all_eq_true.mp batch_15_08_ok accepted_770 (by simp [batch_15_08_values])
  exact h
theorem leaf_770_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_770.profileLo box_770.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_770_ok
theorem branch_box_770_nonnegative : ∀ j, 0 ≤ branch_box_770.lower j ∧ 0 ≤ branch_box_770.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_770, Box.profileLo, Box.profileHi, box_770]
theorem leaf_770_BranchSafe : CertificateConsequences.BranchSafe branch_box_770 := by
  left; refine ⟨branch_box_770_nonnegative, ?_⟩
  intro z hz; exact leaf_770_sound hz

theorem leaf_772_ok : checkAt 527 1000 box_772 cert_772 = true := by
  have h := List.all_eq_true.mp batch_15_09_ok accepted_772 (by simp [batch_15_09_values])
  exact h
theorem leaf_772_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_772.profileLo box_772.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_772_ok
theorem branch_box_772_nonnegative : ∀ j, 0 ≤ branch_box_772.lower j ∧ 0 ≤ branch_box_772.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_772, Box.profileLo, Box.profileHi, box_772]
theorem leaf_772_BranchSafe : CertificateConsequences.BranchSafe branch_box_772 := by
  left; refine ⟨branch_box_772_nonnegative, ?_⟩
  intro z hz; exact leaf_772_sound hz

theorem leaf_773_ok : checkAt 527 1000 box_773 cert_773 = true := by
  have h := List.all_eq_true.mp batch_15_10_ok accepted_773 (by simp [batch_15_10_values])
  exact h
theorem leaf_773_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_773.profileLo box_773.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_773_ok
theorem branch_box_773_nonnegative : ∀ j, 0 ≤ branch_box_773.lower j ∧ 0 ≤ branch_box_773.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_773, Box.profileLo, Box.profileHi, box_773]
theorem leaf_773_BranchSafe : CertificateConsequences.BranchSafe branch_box_773 := by
  left; refine ⟨branch_box_773_nonnegative, ?_⟩
  intro z hz; exact leaf_773_sound hz

theorem leaf_784_ok : checkAt 527 1000 box_784 cert_784 = true := by
  have h := List.all_eq_true.mp batch_15_11_ok accepted_784 (by simp [batch_15_11_values])
  exact h
theorem leaf_784_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_784.profileLo box_784.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_784_ok
theorem branch_box_784_nonnegative : ∀ j, 0 ≤ branch_box_784.lower j ∧ 0 ≤ branch_box_784.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_784, Box.profileLo, Box.profileHi, box_784]
theorem leaf_784_BranchSafe : CertificateConsequences.BranchSafe branch_box_784 := by
  left; refine ⟨branch_box_784_nonnegative, ?_⟩
  intro z hz; exact leaf_784_sound hz

theorem leaf_786_ok : checkAt 527 1000 box_786 cert_786 = true := by
  have h := List.all_eq_true.mp batch_15_12_ok accepted_786 (by simp [batch_15_12_values])
  exact h
theorem leaf_786_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_786.profileLo box_786.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_786_ok
theorem branch_box_786_nonnegative : ∀ j, 0 ≤ branch_box_786.lower j ∧ 0 ≤ branch_box_786.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_786, Box.profileLo, Box.profileHi, box_786]
theorem leaf_786_BranchSafe : CertificateConsequences.BranchSafe branch_box_786 := by
  left; refine ⟨branch_box_786_nonnegative, ?_⟩
  intro z hz; exact leaf_786_sound hz

theorem leaf_788_ok : checkAt 527 1000 box_788 cert_788 = true := by
  have h := List.all_eq_true.mp batch_15_13_ok accepted_788 (by simp [batch_15_13_values])
  exact h
theorem leaf_788_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_788.profileLo box_788.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_788_ok
theorem branch_box_788_nonnegative : ∀ j, 0 ≤ branch_box_788.lower j ∧ 0 ≤ branch_box_788.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_788, Box.profileLo, Box.profileHi, box_788]
theorem leaf_788_BranchSafe : CertificateConsequences.BranchSafe branch_box_788 := by
  left; refine ⟨branch_box_788_nonnegative, ?_⟩
  intro z hz; exact leaf_788_sound hz

theorem leaf_790_ok : checkAt 527 1000 box_790 cert_790 = true := by
  have h := List.all_eq_true.mp batch_15_14_ok accepted_790 (by simp [batch_15_14_values])
  exact h
theorem leaf_790_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_790.profileLo box_790.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_790_ok
theorem branch_box_790_nonnegative : ∀ j, 0 ≤ branch_box_790.lower j ∧ 0 ≤ branch_box_790.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_790, Box.profileLo, Box.profileHi, box_790]
theorem leaf_790_BranchSafe : CertificateConsequences.BranchSafe branch_box_790 := by
  left; refine ⟨branch_box_790_nonnegative, ?_⟩
  intro z hz; exact leaf_790_sound hz

theorem leaf_796_ok : checkAt 527 1000 box_796 cert_796 = true := by
  have h := List.all_eq_true.mp batch_15_15_ok accepted_796 (by simp [batch_15_15_values])
  exact h
theorem leaf_796_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_796.profileLo box_796.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_796_ok
theorem branch_box_796_nonnegative : ∀ j, 0 ≤ branch_box_796.lower j ∧ 0 ≤ branch_box_796.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_796, Box.profileLo, Box.profileHi, box_796]
theorem leaf_796_BranchSafe : CertificateConsequences.BranchSafe branch_box_796 := by
  left; refine ⟨branch_box_796_nonnegative, ?_⟩
  intro z hz; exact leaf_796_sound hz

theorem leaf_798_ok : checkAt 527 1000 box_798 cert_798 = true := by
  have h := List.all_eq_true.mp batch_15_16_ok accepted_798 (by simp [batch_15_16_values])
  exact h
theorem leaf_798_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_798.profileLo box_798.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_798_ok
theorem branch_box_798_nonnegative : ∀ j, 0 ≤ branch_box_798.lower j ∧ 0 ≤ branch_box_798.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_798, Box.profileLo, Box.profileHi, box_798]
theorem leaf_798_BranchSafe : CertificateConsequences.BranchSafe branch_box_798 := by
  left; refine ⟨branch_box_798_nonnegative, ?_⟩
  intro z hz; exact leaf_798_sound hz

#print axioms batch_15_00_ok
#print axioms leaf_750_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
