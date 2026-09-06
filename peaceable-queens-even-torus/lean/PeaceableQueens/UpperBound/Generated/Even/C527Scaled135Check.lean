import PeaceableQueens.UpperBound.Generated.Even.C527Scaled135Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_135_00_values : List Bool := [accepted_6750]
theorem batch_135_00_ok : batch_135_00_values.all id = true := by decide

def batch_135_01_values : List Bool := [accepted_6753]
theorem batch_135_01_ok : batch_135_01_values.all id = true := by decide

def batch_135_02_values : List Bool := [accepted_6754]
theorem batch_135_02_ok : batch_135_02_values.all id = true := by decide

def batch_135_03_values : List Bool := [accepted_6760]
theorem batch_135_03_ok : batch_135_03_values.all id = true := by decide

def batch_135_04_values : List Bool := [accepted_6761]
theorem batch_135_04_ok : batch_135_04_values.all id = true := by decide

def batch_135_05_values : List Bool := [accepted_6762]
theorem batch_135_05_ok : batch_135_05_values.all id = true := by decide

def batch_135_06_values : List Bool := [accepted_6764]
theorem batch_135_06_ok : batch_135_06_values.all id = true := by decide

def batch_135_07_values : List Bool := [accepted_6765]
theorem batch_135_07_ok : batch_135_07_values.all id = true := by decide

def batch_135_08_values : List Bool := [accepted_6767]
theorem batch_135_08_ok : batch_135_08_values.all id = true := by decide

def batch_135_09_values : List Bool := [accepted_6768]
theorem batch_135_09_ok : batch_135_09_values.all id = true := by decide

def batch_135_10_values : List Bool := [accepted_6769]
theorem batch_135_10_ok : batch_135_10_values.all id = true := by decide

def batch_135_11_values : List Bool := [accepted_6770]
theorem batch_135_11_ok : batch_135_11_values.all id = true := by decide

def batch_135_12_values : List Bool := [accepted_6773]
theorem batch_135_12_ok : batch_135_12_values.all id = true := by decide

def batch_135_13_values : List Bool := [accepted_6775]
theorem batch_135_13_ok : batch_135_13_values.all id = true := by decide

def batch_135_14_values : List Bool := [accepted_6776]
theorem batch_135_14_ok : batch_135_14_values.all id = true := by decide

def batch_135_15_values : List Bool := [accepted_6779]
theorem batch_135_15_ok : batch_135_15_values.all id = true := by decide

def batch_135_16_values : List Bool := [accepted_6781]
theorem batch_135_16_ok : batch_135_16_values.all id = true := by decide

def batch_135_17_values : List Bool := [accepted_6782]
theorem batch_135_17_ok : batch_135_17_values.all id = true := by decide

def batch_135_18_values : List Bool := [accepted_6785]
theorem batch_135_18_ok : batch_135_18_values.all id = true := by decide

def batch_135_19_values : List Bool := [accepted_6786]
theorem batch_135_19_ok : batch_135_19_values.all id = true := by decide

def batch_135_20_values : List Bool := [accepted_6791]
theorem batch_135_20_ok : batch_135_20_values.all id = true := by decide

def batch_135_21_values : List Bool := [accepted_6792]
theorem batch_135_21_ok : batch_135_21_values.all id = true := by decide

def batch_135_22_values : List Bool := [accepted_6794]
theorem batch_135_22_ok : batch_135_22_values.all id = true := by decide

def batch_135_23_values : List Bool := [accepted_6795]
theorem batch_135_23_ok : batch_135_23_values.all id = true := by decide

def batch_135_24_values : List Bool := [accepted_6797]
theorem batch_135_24_ok : batch_135_24_values.all id = true := by decide

def batch_135_25_values : List Bool := [accepted_6798]
theorem batch_135_25_ok : batch_135_25_values.all id = true := by decide

def batch_135_26_values : List Bool := [accepted_6799]
theorem batch_135_26_ok : batch_135_26_values.all id = true := by decide

theorem leaf_6750_ok : checkAt 527 1000 box_6750 cert_6750 = true := by
  have h := List.all_eq_true.mp batch_135_00_ok accepted_6750 (by simp [batch_135_00_values])
  exact h
theorem leaf_6750_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6750.profileLo box_6750.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6750_ok
theorem branch_box_6750_nonnegative : ∀ j, 0 ≤ branch_box_6750.lower j ∧ 0 ≤ branch_box_6750.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6750, Box.profileLo, Box.profileHi, box_6750]
theorem leaf_6750_BranchSafe : CertificateConsequences.BranchSafe branch_box_6750 := by
  left; refine ⟨branch_box_6750_nonnegative, ?_⟩
  intro z hz; exact leaf_6750_sound hz

theorem leaf_6753_ok : checkAt 527 1000 box_6753 cert_6753 = true := by
  have h := List.all_eq_true.mp batch_135_01_ok accepted_6753 (by simp [batch_135_01_values])
  exact h
theorem leaf_6753_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6753.profileLo box_6753.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6753_ok
theorem branch_box_6753_nonnegative : ∀ j, 0 ≤ branch_box_6753.lower j ∧ 0 ≤ branch_box_6753.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6753, Box.profileLo, Box.profileHi, box_6753]
theorem leaf_6753_BranchSafe : CertificateConsequences.BranchSafe branch_box_6753 := by
  left; refine ⟨branch_box_6753_nonnegative, ?_⟩
  intro z hz; exact leaf_6753_sound hz

theorem leaf_6754_ok : checkAt 527 1000 box_6754 cert_6754 = true := by
  have h := List.all_eq_true.mp batch_135_02_ok accepted_6754 (by simp [batch_135_02_values])
  exact h
theorem leaf_6754_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6754.profileLo box_6754.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6754_ok
theorem branch_box_6754_nonnegative : ∀ j, 0 ≤ branch_box_6754.lower j ∧ 0 ≤ branch_box_6754.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6754, Box.profileLo, Box.profileHi, box_6754]
theorem leaf_6754_BranchSafe : CertificateConsequences.BranchSafe branch_box_6754 := by
  left; refine ⟨branch_box_6754_nonnegative, ?_⟩
  intro z hz; exact leaf_6754_sound hz

theorem leaf_6760_ok : checkAt 527 1000 box_6760 cert_6760 = true := by
  have h := List.all_eq_true.mp batch_135_03_ok accepted_6760 (by simp [batch_135_03_values])
  exact h
theorem leaf_6760_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6760.profileLo box_6760.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6760_ok
theorem branch_box_6760_nonnegative : ∀ j, 0 ≤ branch_box_6760.lower j ∧ 0 ≤ branch_box_6760.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6760, Box.profileLo, Box.profileHi, box_6760]
theorem leaf_6760_BranchSafe : CertificateConsequences.BranchSafe branch_box_6760 := by
  left; refine ⟨branch_box_6760_nonnegative, ?_⟩
  intro z hz; exact leaf_6760_sound hz

theorem leaf_6761_ok : checkAt 527 1000 box_6761 cert_6761 = true := by
  have h := List.all_eq_true.mp batch_135_04_ok accepted_6761 (by simp [batch_135_04_values])
  exact h
theorem leaf_6761_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6761.profileLo box_6761.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6761_ok
theorem branch_box_6761_nonnegative : ∀ j, 0 ≤ branch_box_6761.lower j ∧ 0 ≤ branch_box_6761.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6761, Box.profileLo, Box.profileHi, box_6761]
theorem leaf_6761_BranchSafe : CertificateConsequences.BranchSafe branch_box_6761 := by
  left; refine ⟨branch_box_6761_nonnegative, ?_⟩
  intro z hz; exact leaf_6761_sound hz

theorem leaf_6762_ok : checkAt 527 1000 box_6762 cert_6762 = true := by
  have h := List.all_eq_true.mp batch_135_05_ok accepted_6762 (by simp [batch_135_05_values])
  exact h
theorem leaf_6762_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6762.profileLo box_6762.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6762_ok
theorem branch_box_6762_nonnegative : ∀ j, 0 ≤ branch_box_6762.lower j ∧ 0 ≤ branch_box_6762.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6762, Box.profileLo, Box.profileHi, box_6762]
theorem leaf_6762_BranchSafe : CertificateConsequences.BranchSafe branch_box_6762 := by
  left; refine ⟨branch_box_6762_nonnegative, ?_⟩
  intro z hz; exact leaf_6762_sound hz

theorem leaf_6764_ok : checkAt 527 1000 box_6764 cert_6764 = true := by
  have h := List.all_eq_true.mp batch_135_06_ok accepted_6764 (by simp [batch_135_06_values])
  exact h
theorem leaf_6764_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6764.profileLo box_6764.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6764_ok
theorem branch_box_6764_nonnegative : ∀ j, 0 ≤ branch_box_6764.lower j ∧ 0 ≤ branch_box_6764.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6764, Box.profileLo, Box.profileHi, box_6764]
theorem leaf_6764_BranchSafe : CertificateConsequences.BranchSafe branch_box_6764 := by
  left; refine ⟨branch_box_6764_nonnegative, ?_⟩
  intro z hz; exact leaf_6764_sound hz

theorem leaf_6765_ok : checkAt 527 1000 box_6765 cert_6765 = true := by
  have h := List.all_eq_true.mp batch_135_07_ok accepted_6765 (by simp [batch_135_07_values])
  exact h
theorem leaf_6765_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6765.profileLo box_6765.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6765_ok
theorem branch_box_6765_nonnegative : ∀ j, 0 ≤ branch_box_6765.lower j ∧ 0 ≤ branch_box_6765.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6765, Box.profileLo, Box.profileHi, box_6765]
theorem leaf_6765_BranchSafe : CertificateConsequences.BranchSafe branch_box_6765 := by
  left; refine ⟨branch_box_6765_nonnegative, ?_⟩
  intro z hz; exact leaf_6765_sound hz

theorem leaf_6767_ok : checkAt 527 1000 box_6767 cert_6767 = true := by
  have h := List.all_eq_true.mp batch_135_08_ok accepted_6767 (by simp [batch_135_08_values])
  exact h
theorem leaf_6767_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6767.profileLo box_6767.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6767_ok
theorem branch_box_6767_nonnegative : ∀ j, 0 ≤ branch_box_6767.lower j ∧ 0 ≤ branch_box_6767.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6767, Box.profileLo, Box.profileHi, box_6767]
theorem leaf_6767_BranchSafe : CertificateConsequences.BranchSafe branch_box_6767 := by
  left; refine ⟨branch_box_6767_nonnegative, ?_⟩
  intro z hz; exact leaf_6767_sound hz

theorem leaf_6768_ok : checkAt 527 1000 box_6768 cert_6768 = true := by
  have h := List.all_eq_true.mp batch_135_09_ok accepted_6768 (by simp [batch_135_09_values])
  exact h
theorem leaf_6768_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6768.profileLo box_6768.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6768_ok
theorem branch_box_6768_nonnegative : ∀ j, 0 ≤ branch_box_6768.lower j ∧ 0 ≤ branch_box_6768.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6768, Box.profileLo, Box.profileHi, box_6768]
theorem leaf_6768_BranchSafe : CertificateConsequences.BranchSafe branch_box_6768 := by
  left; refine ⟨branch_box_6768_nonnegative, ?_⟩
  intro z hz; exact leaf_6768_sound hz

theorem leaf_6769_ok : checkAt 527 1000 box_6769 cert_6769 = true := by
  have h := List.all_eq_true.mp batch_135_10_ok accepted_6769 (by simp [batch_135_10_values])
  exact h
theorem leaf_6769_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6769.profileLo box_6769.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6769_ok
theorem branch_box_6769_nonnegative : ∀ j, 0 ≤ branch_box_6769.lower j ∧ 0 ≤ branch_box_6769.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6769, Box.profileLo, Box.profileHi, box_6769]
theorem leaf_6769_BranchSafe : CertificateConsequences.BranchSafe branch_box_6769 := by
  left; refine ⟨branch_box_6769_nonnegative, ?_⟩
  intro z hz; exact leaf_6769_sound hz

theorem leaf_6770_ok : checkAt 527 1000 box_6770 cert_6770 = true := by
  have h := List.all_eq_true.mp batch_135_11_ok accepted_6770 (by simp [batch_135_11_values])
  exact h
theorem leaf_6770_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6770.profileLo box_6770.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6770_ok
theorem branch_box_6770_nonnegative : ∀ j, 0 ≤ branch_box_6770.lower j ∧ 0 ≤ branch_box_6770.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6770, Box.profileLo, Box.profileHi, box_6770]
theorem leaf_6770_BranchSafe : CertificateConsequences.BranchSafe branch_box_6770 := by
  left; refine ⟨branch_box_6770_nonnegative, ?_⟩
  intro z hz; exact leaf_6770_sound hz

theorem leaf_6773_ok : checkAt 527 1000 box_6773 cert_6773 = true := by
  have h := List.all_eq_true.mp batch_135_12_ok accepted_6773 (by simp [batch_135_12_values])
  exact h
theorem leaf_6773_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6773.profileLo box_6773.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6773_ok
theorem branch_box_6773_nonnegative : ∀ j, 0 ≤ branch_box_6773.lower j ∧ 0 ≤ branch_box_6773.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6773, Box.profileLo, Box.profileHi, box_6773]
theorem leaf_6773_BranchSafe : CertificateConsequences.BranchSafe branch_box_6773 := by
  left; refine ⟨branch_box_6773_nonnegative, ?_⟩
  intro z hz; exact leaf_6773_sound hz

theorem leaf_6775_ok : checkAt 527 1000 box_6775 cert_6775 = true := by
  have h := List.all_eq_true.mp batch_135_13_ok accepted_6775 (by simp [batch_135_13_values])
  exact h
theorem leaf_6775_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6775.profileLo box_6775.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6775_ok
theorem branch_box_6775_nonnegative : ∀ j, 0 ≤ branch_box_6775.lower j ∧ 0 ≤ branch_box_6775.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6775, Box.profileLo, Box.profileHi, box_6775]
theorem leaf_6775_BranchSafe : CertificateConsequences.BranchSafe branch_box_6775 := by
  left; refine ⟨branch_box_6775_nonnegative, ?_⟩
  intro z hz; exact leaf_6775_sound hz

theorem leaf_6776_ok : checkAt 527 1000 box_6776 cert_6776 = true := by
  have h := List.all_eq_true.mp batch_135_14_ok accepted_6776 (by simp [batch_135_14_values])
  exact h
theorem leaf_6776_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6776.profileLo box_6776.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6776_ok
theorem branch_box_6776_nonnegative : ∀ j, 0 ≤ branch_box_6776.lower j ∧ 0 ≤ branch_box_6776.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6776, Box.profileLo, Box.profileHi, box_6776]
theorem leaf_6776_BranchSafe : CertificateConsequences.BranchSafe branch_box_6776 := by
  left; refine ⟨branch_box_6776_nonnegative, ?_⟩
  intro z hz; exact leaf_6776_sound hz

theorem leaf_6779_ok : checkAt 527 1000 box_6779 cert_6779 = true := by
  have h := List.all_eq_true.mp batch_135_15_ok accepted_6779 (by simp [batch_135_15_values])
  exact h
theorem leaf_6779_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6779.profileLo box_6779.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6779_ok
theorem branch_box_6779_nonnegative : ∀ j, 0 ≤ branch_box_6779.lower j ∧ 0 ≤ branch_box_6779.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6779, Box.profileLo, Box.profileHi, box_6779]
theorem leaf_6779_BranchSafe : CertificateConsequences.BranchSafe branch_box_6779 := by
  left; refine ⟨branch_box_6779_nonnegative, ?_⟩
  intro z hz; exact leaf_6779_sound hz

theorem leaf_6781_ok : checkAt 527 1000 box_6781 cert_6781 = true := by
  have h := List.all_eq_true.mp batch_135_16_ok accepted_6781 (by simp [batch_135_16_values])
  exact h
theorem leaf_6781_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6781.profileLo box_6781.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6781_ok
theorem branch_box_6781_nonnegative : ∀ j, 0 ≤ branch_box_6781.lower j ∧ 0 ≤ branch_box_6781.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6781, Box.profileLo, Box.profileHi, box_6781]
theorem leaf_6781_BranchSafe : CertificateConsequences.BranchSafe branch_box_6781 := by
  left; refine ⟨branch_box_6781_nonnegative, ?_⟩
  intro z hz; exact leaf_6781_sound hz

theorem leaf_6782_ok : checkAt 527 1000 box_6782 cert_6782 = true := by
  have h := List.all_eq_true.mp batch_135_17_ok accepted_6782 (by simp [batch_135_17_values])
  exact h
theorem leaf_6782_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6782.profileLo box_6782.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6782_ok
theorem branch_box_6782_nonnegative : ∀ j, 0 ≤ branch_box_6782.lower j ∧ 0 ≤ branch_box_6782.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6782, Box.profileLo, Box.profileHi, box_6782]
theorem leaf_6782_BranchSafe : CertificateConsequences.BranchSafe branch_box_6782 := by
  left; refine ⟨branch_box_6782_nonnegative, ?_⟩
  intro z hz; exact leaf_6782_sound hz

theorem leaf_6785_ok : checkAt 527 1000 box_6785 cert_6785 = true := by
  have h := List.all_eq_true.mp batch_135_18_ok accepted_6785 (by simp [batch_135_18_values])
  exact h
theorem leaf_6785_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6785.profileLo box_6785.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6785_ok
theorem branch_box_6785_nonnegative : ∀ j, 0 ≤ branch_box_6785.lower j ∧ 0 ≤ branch_box_6785.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6785, Box.profileLo, Box.profileHi, box_6785]
theorem leaf_6785_BranchSafe : CertificateConsequences.BranchSafe branch_box_6785 := by
  left; refine ⟨branch_box_6785_nonnegative, ?_⟩
  intro z hz; exact leaf_6785_sound hz

theorem leaf_6786_ok : checkAt 527 1000 box_6786 cert_6786 = true := by
  have h := List.all_eq_true.mp batch_135_19_ok accepted_6786 (by simp [batch_135_19_values])
  exact h
theorem leaf_6786_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6786.profileLo box_6786.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6786_ok
theorem branch_box_6786_nonnegative : ∀ j, 0 ≤ branch_box_6786.lower j ∧ 0 ≤ branch_box_6786.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6786, Box.profileLo, Box.profileHi, box_6786]
theorem leaf_6786_BranchSafe : CertificateConsequences.BranchSafe branch_box_6786 := by
  left; refine ⟨branch_box_6786_nonnegative, ?_⟩
  intro z hz; exact leaf_6786_sound hz

theorem leaf_6791_ok : checkAt 527 1000 box_6791 cert_6791 = true := by
  have h := List.all_eq_true.mp batch_135_20_ok accepted_6791 (by simp [batch_135_20_values])
  exact h
theorem leaf_6791_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6791.profileLo box_6791.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6791_ok
theorem branch_box_6791_nonnegative : ∀ j, 0 ≤ branch_box_6791.lower j ∧ 0 ≤ branch_box_6791.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6791, Box.profileLo, Box.profileHi, box_6791]
theorem leaf_6791_BranchSafe : CertificateConsequences.BranchSafe branch_box_6791 := by
  left; refine ⟨branch_box_6791_nonnegative, ?_⟩
  intro z hz; exact leaf_6791_sound hz

theorem leaf_6792_ok : checkAt 527 1000 box_6792 cert_6792 = true := by
  have h := List.all_eq_true.mp batch_135_21_ok accepted_6792 (by simp [batch_135_21_values])
  exact h
theorem leaf_6792_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6792.profileLo box_6792.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6792_ok
theorem branch_box_6792_nonnegative : ∀ j, 0 ≤ branch_box_6792.lower j ∧ 0 ≤ branch_box_6792.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6792, Box.profileLo, Box.profileHi, box_6792]
theorem leaf_6792_BranchSafe : CertificateConsequences.BranchSafe branch_box_6792 := by
  left; refine ⟨branch_box_6792_nonnegative, ?_⟩
  intro z hz; exact leaf_6792_sound hz

theorem leaf_6794_ok : checkAt 527 1000 box_6794 cert_6794 = true := by
  have h := List.all_eq_true.mp batch_135_22_ok accepted_6794 (by simp [batch_135_22_values])
  exact h
theorem leaf_6794_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6794.profileLo box_6794.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6794_ok
theorem branch_box_6794_nonnegative : ∀ j, 0 ≤ branch_box_6794.lower j ∧ 0 ≤ branch_box_6794.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6794, Box.profileLo, Box.profileHi, box_6794]
theorem leaf_6794_BranchSafe : CertificateConsequences.BranchSafe branch_box_6794 := by
  left; refine ⟨branch_box_6794_nonnegative, ?_⟩
  intro z hz; exact leaf_6794_sound hz

theorem leaf_6795_ok : checkAt 527 1000 box_6795 cert_6795 = true := by
  have h := List.all_eq_true.mp batch_135_23_ok accepted_6795 (by simp [batch_135_23_values])
  exact h
theorem leaf_6795_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6795.profileLo box_6795.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6795_ok
theorem branch_box_6795_nonnegative : ∀ j, 0 ≤ branch_box_6795.lower j ∧ 0 ≤ branch_box_6795.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6795, Box.profileLo, Box.profileHi, box_6795]
theorem leaf_6795_BranchSafe : CertificateConsequences.BranchSafe branch_box_6795 := by
  left; refine ⟨branch_box_6795_nonnegative, ?_⟩
  intro z hz; exact leaf_6795_sound hz

theorem leaf_6797_ok : checkAt 527 1000 box_6797 cert_6797 = true := by
  have h := List.all_eq_true.mp batch_135_24_ok accepted_6797 (by simp [batch_135_24_values])
  exact h
theorem leaf_6797_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6797.profileLo box_6797.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6797_ok
theorem branch_box_6797_nonnegative : ∀ j, 0 ≤ branch_box_6797.lower j ∧ 0 ≤ branch_box_6797.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6797, Box.profileLo, Box.profileHi, box_6797]
theorem leaf_6797_BranchSafe : CertificateConsequences.BranchSafe branch_box_6797 := by
  left; refine ⟨branch_box_6797_nonnegative, ?_⟩
  intro z hz; exact leaf_6797_sound hz

theorem leaf_6798_ok : checkAt 527 1000 box_6798 cert_6798 = true := by
  have h := List.all_eq_true.mp batch_135_25_ok accepted_6798 (by simp [batch_135_25_values])
  exact h
theorem leaf_6798_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6798.profileLo box_6798.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6798_ok
theorem branch_box_6798_nonnegative : ∀ j, 0 ≤ branch_box_6798.lower j ∧ 0 ≤ branch_box_6798.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6798, Box.profileLo, Box.profileHi, box_6798]
theorem leaf_6798_BranchSafe : CertificateConsequences.BranchSafe branch_box_6798 := by
  left; refine ⟨branch_box_6798_nonnegative, ?_⟩
  intro z hz; exact leaf_6798_sound hz

theorem leaf_6799_ok : checkAt 527 1000 box_6799 cert_6799 = true := by
  have h := List.all_eq_true.mp batch_135_26_ok accepted_6799 (by simp [batch_135_26_values])
  exact h
theorem leaf_6799_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6799.profileLo box_6799.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6799_ok
theorem branch_box_6799_nonnegative : ∀ j, 0 ≤ branch_box_6799.lower j ∧ 0 ≤ branch_box_6799.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6799, Box.profileLo, Box.profileHi, box_6799]
theorem leaf_6799_BranchSafe : CertificateConsequences.BranchSafe branch_box_6799 := by
  left; refine ⟨branch_box_6799_nonnegative, ?_⟩
  intro z hz; exact leaf_6799_sound hz

#print axioms batch_135_00_ok
#print axioms leaf_6750_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
