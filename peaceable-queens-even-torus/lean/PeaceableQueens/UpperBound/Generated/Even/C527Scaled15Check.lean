import PeaceableQueens.UpperBound.Generated.Even.C527Scaled15Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_15_00_values : List Bool := [accepted_751]
theorem batch_15_00_ok : batch_15_00_values.all id = true := by decide

def batch_15_01_values : List Bool := [accepted_752]
theorem batch_15_01_ok : batch_15_01_values.all id = true := by decide

def batch_15_02_values : List Bool := [accepted_753]
theorem batch_15_02_ok : batch_15_02_values.all id = true := by decide

def batch_15_03_values : List Bool := [accepted_754]
theorem batch_15_03_ok : batch_15_03_values.all id = true := by decide

def batch_15_04_values : List Bool := [accepted_756]
theorem batch_15_04_ok : batch_15_04_values.all id = true := by decide

def batch_15_05_values : List Bool := [accepted_758]
theorem batch_15_05_ok : batch_15_05_values.all id = true := by decide

def batch_15_06_values : List Bool := [accepted_759]
theorem batch_15_06_ok : batch_15_06_values.all id = true := by decide

def batch_15_07_values : List Bool := [accepted_760]
theorem batch_15_07_ok : batch_15_07_values.all id = true := by decide

def batch_15_08_values : List Bool := [accepted_768]
theorem batch_15_08_ok : batch_15_08_values.all id = true := by decide

def batch_15_09_values : List Bool := [accepted_769]
theorem batch_15_09_ok : batch_15_09_values.all id = true := by decide

def batch_15_10_values : List Bool := [accepted_771]
theorem batch_15_10_ok : batch_15_10_values.all id = true := by decide

def batch_15_11_values : List Bool := [accepted_772]
theorem batch_15_11_ok : batch_15_11_values.all id = true := by decide

def batch_15_12_values : List Bool := [accepted_773]
theorem batch_15_12_ok : batch_15_12_values.all id = true := by decide

def batch_15_13_values : List Bool := [accepted_774]
theorem batch_15_13_ok : batch_15_13_values.all id = true := by decide

def batch_15_14_values : List Bool := [accepted_776]
theorem batch_15_14_ok : batch_15_14_values.all id = true := by decide

def batch_15_15_values : List Bool := [accepted_779]
theorem batch_15_15_ok : batch_15_15_values.all id = true := by decide

def batch_15_16_values : List Bool := [accepted_780]
theorem batch_15_16_ok : batch_15_16_values.all id = true := by decide

def batch_15_17_values : List Bool := [accepted_781]
theorem batch_15_17_ok : batch_15_17_values.all id = true := by decide

def batch_15_18_values : List Bool := [accepted_782]
theorem batch_15_18_ok : batch_15_18_values.all id = true := by decide

def batch_15_19_values : List Bool := [accepted_786]
theorem batch_15_19_ok : batch_15_19_values.all id = true := by decide

def batch_15_20_values : List Bool := [accepted_787]
theorem batch_15_20_ok : batch_15_20_values.all id = true := by decide

def batch_15_21_values : List Bool := [accepted_788]
theorem batch_15_21_ok : batch_15_21_values.all id = true := by decide

def batch_15_22_values : List Bool := [accepted_789]
theorem batch_15_22_ok : batch_15_22_values.all id = true := by decide

def batch_15_23_values : List Bool := [accepted_790]
theorem batch_15_23_ok : batch_15_23_values.all id = true := by decide

def batch_15_24_values : List Bool := [accepted_796]
theorem batch_15_24_ok : batch_15_24_values.all id = true := by decide

def batch_15_25_values : List Bool := [accepted_797]
theorem batch_15_25_ok : batch_15_25_values.all id = true := by decide

def batch_15_26_values : List Bool := [accepted_798]
theorem batch_15_26_ok : batch_15_26_values.all id = true := by decide

def batch_15_27_values : List Bool := [accepted_799]
theorem batch_15_27_ok : batch_15_27_values.all id = true := by decide

theorem leaf_751_ok : checkAt 527 1000 box_751 cert_751 = true := by
  have h := List.all_eq_true.mp batch_15_00_ok accepted_751 (by simp [batch_15_00_values])
  exact h
theorem leaf_751_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_751.profileLo box_751.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_751_ok
theorem branch_box_751_nonnegative : ∀ j, 0 ≤ branch_box_751.lower j ∧ 0 ≤ branch_box_751.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_751, Box.profileLo, Box.profileHi, box_751]
theorem leaf_751_BranchSafe : CertificateConsequences.BranchSafe branch_box_751 := by
  left; refine ⟨branch_box_751_nonnegative, ?_⟩
  intro z hz; exact leaf_751_sound hz

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

theorem leaf_753_ok : checkAt 527 1000 box_753 cert_753 = true := by
  have h := List.all_eq_true.mp batch_15_02_ok accepted_753 (by simp [batch_15_02_values])
  exact h
theorem leaf_753_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_753.profileLo box_753.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_753_ok
theorem branch_box_753_nonnegative : ∀ j, 0 ≤ branch_box_753.lower j ∧ 0 ≤ branch_box_753.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_753, Box.profileLo, Box.profileHi, box_753]
theorem leaf_753_BranchSafe : CertificateConsequences.BranchSafe branch_box_753 := by
  left; refine ⟨branch_box_753_nonnegative, ?_⟩
  intro z hz; exact leaf_753_sound hz

theorem leaf_754_ok : checkAt 527 1000 box_754 cert_754 = true := by
  have h := List.all_eq_true.mp batch_15_03_ok accepted_754 (by simp [batch_15_03_values])
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
  have h := List.all_eq_true.mp batch_15_04_ok accepted_756 (by simp [batch_15_04_values])
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

theorem leaf_758_ok : checkAt 527 1000 box_758 cert_758 = true := by
  have h := List.all_eq_true.mp batch_15_05_ok accepted_758 (by simp [batch_15_05_values])
  exact h
theorem leaf_758_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_758.profileLo box_758.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_758_ok
theorem branch_box_758_nonnegative : ∀ j, 0 ≤ branch_box_758.lower j ∧ 0 ≤ branch_box_758.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_758, Box.profileLo, Box.profileHi, box_758]
theorem leaf_758_BranchSafe : CertificateConsequences.BranchSafe branch_box_758 := by
  left; refine ⟨branch_box_758_nonnegative, ?_⟩
  intro z hz; exact leaf_758_sound hz

theorem leaf_759_ok : checkAt 527 1000 box_759 cert_759 = true := by
  have h := List.all_eq_true.mp batch_15_06_ok accepted_759 (by simp [batch_15_06_values])
  exact h
theorem leaf_759_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_759.profileLo box_759.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_759_ok
theorem branch_box_759_nonnegative : ∀ j, 0 ≤ branch_box_759.lower j ∧ 0 ≤ branch_box_759.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_759, Box.profileLo, Box.profileHi, box_759]
theorem leaf_759_BranchSafe : CertificateConsequences.BranchSafe branch_box_759 := by
  left; refine ⟨branch_box_759_nonnegative, ?_⟩
  intro z hz; exact leaf_759_sound hz

theorem leaf_760_ok : checkAt 527 1000 box_760 cert_760 = true := by
  have h := List.all_eq_true.mp batch_15_07_ok accepted_760 (by simp [batch_15_07_values])
  exact h
theorem leaf_760_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_760.profileLo box_760.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_760_ok
theorem branch_box_760_nonnegative : ∀ j, 0 ≤ branch_box_760.lower j ∧ 0 ≤ branch_box_760.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_760, Box.profileLo, Box.profileHi, box_760]
theorem leaf_760_BranchSafe : CertificateConsequences.BranchSafe branch_box_760 := by
  left; refine ⟨branch_box_760_nonnegative, ?_⟩
  intro z hz; exact leaf_760_sound hz

theorem leaf_768_ok : checkAt 527 1000 box_768 cert_768 = true := by
  have h := List.all_eq_true.mp batch_15_08_ok accepted_768 (by simp [batch_15_08_values])
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

theorem leaf_769_ok : checkAt 527 1000 box_769 cert_769 = true := by
  have h := List.all_eq_true.mp batch_15_09_ok accepted_769 (by simp [batch_15_09_values])
  exact h
theorem leaf_769_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_769.profileLo box_769.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_769_ok
theorem branch_box_769_nonnegative : ∀ j, 0 ≤ branch_box_769.lower j ∧ 0 ≤ branch_box_769.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_769, Box.profileLo, Box.profileHi, box_769]
theorem leaf_769_BranchSafe : CertificateConsequences.BranchSafe branch_box_769 := by
  left; refine ⟨branch_box_769_nonnegative, ?_⟩
  intro z hz; exact leaf_769_sound hz

theorem leaf_771_ok : checkAt 527 1000 box_771 cert_771 = true := by
  have h := List.all_eq_true.mp batch_15_10_ok accepted_771 (by simp [batch_15_10_values])
  exact h
theorem leaf_771_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_771.profileLo box_771.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_771_ok
theorem branch_box_771_nonnegative : ∀ j, 0 ≤ branch_box_771.lower j ∧ 0 ≤ branch_box_771.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_771, Box.profileLo, Box.profileHi, box_771]
theorem leaf_771_BranchSafe : CertificateConsequences.BranchSafe branch_box_771 := by
  left; refine ⟨branch_box_771_nonnegative, ?_⟩
  intro z hz; exact leaf_771_sound hz

theorem leaf_772_ok : checkAt 527 1000 box_772 cert_772 = true := by
  have h := List.all_eq_true.mp batch_15_11_ok accepted_772 (by simp [batch_15_11_values])
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
  have h := List.all_eq_true.mp batch_15_12_ok accepted_773 (by simp [batch_15_12_values])
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

theorem leaf_774_ok : checkAt 527 1000 box_774 cert_774 = true := by
  have h := List.all_eq_true.mp batch_15_13_ok accepted_774 (by simp [batch_15_13_values])
  exact h
theorem leaf_774_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_774.profileLo box_774.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_774_ok
theorem branch_box_774_nonnegative : ∀ j, 0 ≤ branch_box_774.lower j ∧ 0 ≤ branch_box_774.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_774, Box.profileLo, Box.profileHi, box_774]
theorem leaf_774_BranchSafe : CertificateConsequences.BranchSafe branch_box_774 := by
  left; refine ⟨branch_box_774_nonnegative, ?_⟩
  intro z hz; exact leaf_774_sound hz

theorem leaf_776_ok : checkAt 527 1000 box_776 cert_776 = true := by
  have h := List.all_eq_true.mp batch_15_14_ok accepted_776 (by simp [batch_15_14_values])
  exact h
theorem leaf_776_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_776.profileLo box_776.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_776_ok
theorem branch_box_776_nonnegative : ∀ j, 0 ≤ branch_box_776.lower j ∧ 0 ≤ branch_box_776.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_776, Box.profileLo, Box.profileHi, box_776]
theorem leaf_776_BranchSafe : CertificateConsequences.BranchSafe branch_box_776 := by
  left; refine ⟨branch_box_776_nonnegative, ?_⟩
  intro z hz; exact leaf_776_sound hz

theorem leaf_779_ok : checkAt 527 1000 box_779 cert_779 = true := by
  have h := List.all_eq_true.mp batch_15_15_ok accepted_779 (by simp [batch_15_15_values])
  exact h
theorem leaf_779_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_779.profileLo box_779.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_779_ok
theorem branch_box_779_nonnegative : ∀ j, 0 ≤ branch_box_779.lower j ∧ 0 ≤ branch_box_779.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_779, Box.profileLo, Box.profileHi, box_779]
theorem leaf_779_BranchSafe : CertificateConsequences.BranchSafe branch_box_779 := by
  left; refine ⟨branch_box_779_nonnegative, ?_⟩
  intro z hz; exact leaf_779_sound hz

theorem leaf_780_ok : checkAt 527 1000 box_780 cert_780 = true := by
  have h := List.all_eq_true.mp batch_15_16_ok accepted_780 (by simp [batch_15_16_values])
  exact h
theorem leaf_780_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_780.profileLo box_780.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_780_ok
theorem branch_box_780_nonnegative : ∀ j, 0 ≤ branch_box_780.lower j ∧ 0 ≤ branch_box_780.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_780, Box.profileLo, Box.profileHi, box_780]
theorem leaf_780_BranchSafe : CertificateConsequences.BranchSafe branch_box_780 := by
  left; refine ⟨branch_box_780_nonnegative, ?_⟩
  intro z hz; exact leaf_780_sound hz

theorem leaf_781_ok : checkAt 527 1000 box_781 cert_781 = true := by
  have h := List.all_eq_true.mp batch_15_17_ok accepted_781 (by simp [batch_15_17_values])
  exact h
theorem leaf_781_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_781.profileLo box_781.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_781_ok
theorem branch_box_781_nonnegative : ∀ j, 0 ≤ branch_box_781.lower j ∧ 0 ≤ branch_box_781.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_781, Box.profileLo, Box.profileHi, box_781]
theorem leaf_781_BranchSafe : CertificateConsequences.BranchSafe branch_box_781 := by
  left; refine ⟨branch_box_781_nonnegative, ?_⟩
  intro z hz; exact leaf_781_sound hz

theorem leaf_782_ok : checkAt 527 1000 box_782 cert_782 = true := by
  have h := List.all_eq_true.mp batch_15_18_ok accepted_782 (by simp [batch_15_18_values])
  exact h
theorem leaf_782_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_782.profileLo box_782.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_782_ok
theorem branch_box_782_nonnegative : ∀ j, 0 ≤ branch_box_782.lower j ∧ 0 ≤ branch_box_782.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_782, Box.profileLo, Box.profileHi, box_782]
theorem leaf_782_BranchSafe : CertificateConsequences.BranchSafe branch_box_782 := by
  left; refine ⟨branch_box_782_nonnegative, ?_⟩
  intro z hz; exact leaf_782_sound hz

theorem leaf_786_ok : checkAt 527 1000 box_786 cert_786 = true := by
  have h := List.all_eq_true.mp batch_15_19_ok accepted_786 (by simp [batch_15_19_values])
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

theorem leaf_787_ok : checkAt 527 1000 box_787 cert_787 = true := by
  have h := List.all_eq_true.mp batch_15_20_ok accepted_787 (by simp [batch_15_20_values])
  exact h
theorem leaf_787_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_787.profileLo box_787.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_787_ok
theorem branch_box_787_nonnegative : ∀ j, 0 ≤ branch_box_787.lower j ∧ 0 ≤ branch_box_787.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_787, Box.profileLo, Box.profileHi, box_787]
theorem leaf_787_BranchSafe : CertificateConsequences.BranchSafe branch_box_787 := by
  left; refine ⟨branch_box_787_nonnegative, ?_⟩
  intro z hz; exact leaf_787_sound hz

theorem leaf_788_ok : checkAt 527 1000 box_788 cert_788 = true := by
  have h := List.all_eq_true.mp batch_15_21_ok accepted_788 (by simp [batch_15_21_values])
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

theorem leaf_789_ok : checkAt 527 1000 box_789 cert_789 = true := by
  have h := List.all_eq_true.mp batch_15_22_ok accepted_789 (by simp [batch_15_22_values])
  exact h
theorem leaf_789_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_789.profileLo box_789.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_789_ok
theorem branch_box_789_nonnegative : ∀ j, 0 ≤ branch_box_789.lower j ∧ 0 ≤ branch_box_789.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_789, Box.profileLo, Box.profileHi, box_789]
theorem leaf_789_BranchSafe : CertificateConsequences.BranchSafe branch_box_789 := by
  left; refine ⟨branch_box_789_nonnegative, ?_⟩
  intro z hz; exact leaf_789_sound hz

theorem leaf_790_ok : checkAt 527 1000 box_790 cert_790 = true := by
  have h := List.all_eq_true.mp batch_15_23_ok accepted_790 (by simp [batch_15_23_values])
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
  have h := List.all_eq_true.mp batch_15_24_ok accepted_796 (by simp [batch_15_24_values])
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

theorem leaf_797_ok : checkAt 527 1000 box_797 cert_797 = true := by
  have h := List.all_eq_true.mp batch_15_25_ok accepted_797 (by simp [batch_15_25_values])
  exact h
theorem leaf_797_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_797.profileLo box_797.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_797_ok
theorem branch_box_797_nonnegative : ∀ j, 0 ≤ branch_box_797.lower j ∧ 0 ≤ branch_box_797.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_797, Box.profileLo, Box.profileHi, box_797]
theorem leaf_797_BranchSafe : CertificateConsequences.BranchSafe branch_box_797 := by
  left; refine ⟨branch_box_797_nonnegative, ?_⟩
  intro z hz; exact leaf_797_sound hz

theorem leaf_798_ok : checkAt 527 1000 box_798 cert_798 = true := by
  have h := List.all_eq_true.mp batch_15_26_ok accepted_798 (by simp [batch_15_26_values])
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

theorem leaf_799_ok : checkAt 527 1000 box_799 cert_799 = true := by
  have h := List.all_eq_true.mp batch_15_27_ok accepted_799 (by simp [batch_15_27_values])
  exact h
theorem leaf_799_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_799.profileLo box_799.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_799_ok
theorem branch_box_799_nonnegative : ∀ j, 0 ≤ branch_box_799.lower j ∧ 0 ≤ branch_box_799.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_799, Box.profileLo, Box.profileHi, box_799]
theorem leaf_799_BranchSafe : CertificateConsequences.BranchSafe branch_box_799 := by
  left; refine ⟨branch_box_799_nonnegative, ?_⟩
  intro z hz; exact leaf_799_sound hz

#print axioms batch_15_00_ok
#print axioms leaf_751_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
