import PeaceableQueens.UpperBound.Generated.Even.C527Scaled95Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_95_00_values : List Bool := [accepted_4750]
theorem batch_95_00_ok : batch_95_00_values.all id = true := by decide

def batch_95_01_values : List Bool := [accepted_4757]
theorem batch_95_01_ok : batch_95_01_values.all id = true := by decide

def batch_95_02_values : List Bool := [accepted_4759]
theorem batch_95_02_ok : batch_95_02_values.all id = true := by decide

def batch_95_03_values : List Bool := [accepted_4760]
theorem batch_95_03_ok : batch_95_03_values.all id = true := by decide

def batch_95_04_values : List Bool := [accepted_4763]
theorem batch_95_04_ok : batch_95_04_values.all id = true := by decide

def batch_95_05_values : List Bool := [accepted_4764]
theorem batch_95_05_ok : batch_95_05_values.all id = true := by decide

def batch_95_06_values : List Bool := [accepted_4765]
theorem batch_95_06_ok : batch_95_06_values.all id = true := by decide

def batch_95_07_values : List Bool := [accepted_4769]
theorem batch_95_07_ok : batch_95_07_values.all id = true := by decide

def batch_95_08_values : List Bool := [accepted_4773]
theorem batch_95_08_ok : batch_95_08_values.all id = true := by decide

def batch_95_09_values : List Bool := [accepted_4774]
theorem batch_95_09_ok : batch_95_09_values.all id = true := by decide

def batch_95_10_values : List Bool := [accepted_4777]
theorem batch_95_10_ok : batch_95_10_values.all id = true := by decide

def batch_95_11_values : List Bool := [accepted_4778]
theorem batch_95_11_ok : batch_95_11_values.all id = true := by decide

def batch_95_12_values : List Bool := [accepted_4779]
theorem batch_95_12_ok : batch_95_12_values.all id = true := by decide

def batch_95_13_values : List Bool := [accepted_4780]
theorem batch_95_13_ok : batch_95_13_values.all id = true := by decide

def batch_95_14_values : List Bool := [accepted_4783]
theorem batch_95_14_ok : batch_95_14_values.all id = true := by decide

def batch_95_15_values : List Bool := [accepted_4785]
theorem batch_95_15_ok : batch_95_15_values.all id = true := by decide

def batch_95_16_values : List Bool := [accepted_4786]
theorem batch_95_16_ok : batch_95_16_values.all id = true := by decide

def batch_95_17_values : List Bool := [accepted_4787]
theorem batch_95_17_ok : batch_95_17_values.all id = true := by decide

def batch_95_18_values : List Bool := [accepted_4788]
theorem batch_95_18_ok : batch_95_18_values.all id = true := by decide

def batch_95_19_values : List Bool := [accepted_4789]
theorem batch_95_19_ok : batch_95_19_values.all id = true := by decide

def batch_95_20_values : List Bool := [accepted_4791]
theorem batch_95_20_ok : batch_95_20_values.all id = true := by decide

def batch_95_21_values : List Bool := [accepted_4792]
theorem batch_95_21_ok : batch_95_21_values.all id = true := by decide

def batch_95_22_values : List Bool := [accepted_4795]
theorem batch_95_22_ok : batch_95_22_values.all id = true := by decide

def batch_95_23_values : List Bool := [accepted_4799]
theorem batch_95_23_ok : batch_95_23_values.all id = true := by decide

theorem leaf_4750_ok : checkAt 527 1000 box_4750 cert_4750 = true := by
  have h := List.all_eq_true.mp batch_95_00_ok accepted_4750 (by simp [batch_95_00_values])
  exact h
theorem leaf_4750_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4750.profileLo box_4750.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4750_ok
theorem branch_box_4750_nonnegative : ∀ j, 0 ≤ branch_box_4750.lower j ∧ 0 ≤ branch_box_4750.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4750, Box.profileLo, Box.profileHi, box_4750]
theorem leaf_4750_BranchSafe : CertificateConsequences.BranchSafe branch_box_4750 := by
  left; refine ⟨branch_box_4750_nonnegative, ?_⟩
  intro z hz; exact leaf_4750_sound hz

theorem leaf_4757_ok : checkAt 527 1000 box_4757 cert_4757 = true := by
  have h := List.all_eq_true.mp batch_95_01_ok accepted_4757 (by simp [batch_95_01_values])
  exact h
theorem leaf_4757_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4757.profileLo box_4757.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4757_ok
theorem branch_box_4757_nonnegative : ∀ j, 0 ≤ branch_box_4757.lower j ∧ 0 ≤ branch_box_4757.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4757, Box.profileLo, Box.profileHi, box_4757]
theorem leaf_4757_BranchSafe : CertificateConsequences.BranchSafe branch_box_4757 := by
  left; refine ⟨branch_box_4757_nonnegative, ?_⟩
  intro z hz; exact leaf_4757_sound hz

theorem leaf_4759_ok : checkAt 527 1000 box_4759 cert_4759 = true := by
  have h := List.all_eq_true.mp batch_95_02_ok accepted_4759 (by simp [batch_95_02_values])
  exact h
theorem leaf_4759_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4759.profileLo box_4759.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4759_ok
theorem branch_box_4759_nonnegative : ∀ j, 0 ≤ branch_box_4759.lower j ∧ 0 ≤ branch_box_4759.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4759, Box.profileLo, Box.profileHi, box_4759]
theorem leaf_4759_BranchSafe : CertificateConsequences.BranchSafe branch_box_4759 := by
  left; refine ⟨branch_box_4759_nonnegative, ?_⟩
  intro z hz; exact leaf_4759_sound hz

theorem leaf_4760_ok : checkAt 527 1000 box_4760 cert_4760 = true := by
  have h := List.all_eq_true.mp batch_95_03_ok accepted_4760 (by simp [batch_95_03_values])
  exact h
theorem leaf_4760_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4760.profileLo box_4760.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4760_ok
theorem branch_box_4760_nonnegative : ∀ j, 0 ≤ branch_box_4760.lower j ∧ 0 ≤ branch_box_4760.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4760, Box.profileLo, Box.profileHi, box_4760]
theorem leaf_4760_BranchSafe : CertificateConsequences.BranchSafe branch_box_4760 := by
  left; refine ⟨branch_box_4760_nonnegative, ?_⟩
  intro z hz; exact leaf_4760_sound hz

theorem leaf_4763_ok : checkAt 527 1000 box_4763 cert_4763 = true := by
  have h := List.all_eq_true.mp batch_95_04_ok accepted_4763 (by simp [batch_95_04_values])
  exact h
theorem leaf_4763_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4763.profileLo box_4763.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4763_ok
theorem branch_box_4763_nonnegative : ∀ j, 0 ≤ branch_box_4763.lower j ∧ 0 ≤ branch_box_4763.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4763, Box.profileLo, Box.profileHi, box_4763]
theorem leaf_4763_BranchSafe : CertificateConsequences.BranchSafe branch_box_4763 := by
  left; refine ⟨branch_box_4763_nonnegative, ?_⟩
  intro z hz; exact leaf_4763_sound hz

theorem leaf_4764_ok : checkAt 527 1000 box_4764 cert_4764 = true := by
  have h := List.all_eq_true.mp batch_95_05_ok accepted_4764 (by simp [batch_95_05_values])
  exact h
theorem leaf_4764_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4764.profileLo box_4764.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4764_ok
theorem branch_box_4764_nonnegative : ∀ j, 0 ≤ branch_box_4764.lower j ∧ 0 ≤ branch_box_4764.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4764, Box.profileLo, Box.profileHi, box_4764]
theorem leaf_4764_BranchSafe : CertificateConsequences.BranchSafe branch_box_4764 := by
  left; refine ⟨branch_box_4764_nonnegative, ?_⟩
  intro z hz; exact leaf_4764_sound hz

theorem leaf_4765_ok : checkAt 527 1000 box_4765 cert_4765 = true := by
  have h := List.all_eq_true.mp batch_95_06_ok accepted_4765 (by simp [batch_95_06_values])
  exact h
theorem leaf_4765_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4765.profileLo box_4765.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4765_ok
theorem branch_box_4765_nonnegative : ∀ j, 0 ≤ branch_box_4765.lower j ∧ 0 ≤ branch_box_4765.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4765, Box.profileLo, Box.profileHi, box_4765]
theorem leaf_4765_BranchSafe : CertificateConsequences.BranchSafe branch_box_4765 := by
  left; refine ⟨branch_box_4765_nonnegative, ?_⟩
  intro z hz; exact leaf_4765_sound hz

theorem leaf_4769_ok : checkAt 527 1000 box_4769 cert_4769 = true := by
  have h := List.all_eq_true.mp batch_95_07_ok accepted_4769 (by simp [batch_95_07_values])
  exact h
theorem leaf_4769_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4769.profileLo box_4769.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4769_ok
theorem branch_box_4769_nonnegative : ∀ j, 0 ≤ branch_box_4769.lower j ∧ 0 ≤ branch_box_4769.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4769, Box.profileLo, Box.profileHi, box_4769]
theorem leaf_4769_BranchSafe : CertificateConsequences.BranchSafe branch_box_4769 := by
  left; refine ⟨branch_box_4769_nonnegative, ?_⟩
  intro z hz; exact leaf_4769_sound hz

theorem leaf_4773_ok : checkAt 527 1000 box_4773 cert_4773 = true := by
  have h := List.all_eq_true.mp batch_95_08_ok accepted_4773 (by simp [batch_95_08_values])
  exact h
theorem leaf_4773_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4773.profileLo box_4773.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4773_ok
theorem branch_box_4773_nonnegative : ∀ j, 0 ≤ branch_box_4773.lower j ∧ 0 ≤ branch_box_4773.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4773, Box.profileLo, Box.profileHi, box_4773]
theorem leaf_4773_BranchSafe : CertificateConsequences.BranchSafe branch_box_4773 := by
  left; refine ⟨branch_box_4773_nonnegative, ?_⟩
  intro z hz; exact leaf_4773_sound hz

theorem leaf_4774_ok : checkAt 527 1000 box_4774 cert_4774 = true := by
  have h := List.all_eq_true.mp batch_95_09_ok accepted_4774 (by simp [batch_95_09_values])
  exact h
theorem leaf_4774_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4774.profileLo box_4774.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4774_ok
theorem branch_box_4774_nonnegative : ∀ j, 0 ≤ branch_box_4774.lower j ∧ 0 ≤ branch_box_4774.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4774, Box.profileLo, Box.profileHi, box_4774]
theorem leaf_4774_BranchSafe : CertificateConsequences.BranchSafe branch_box_4774 := by
  left; refine ⟨branch_box_4774_nonnegative, ?_⟩
  intro z hz; exact leaf_4774_sound hz

theorem leaf_4777_ok : checkAt 527 1000 box_4777 cert_4777 = true := by
  have h := List.all_eq_true.mp batch_95_10_ok accepted_4777 (by simp [batch_95_10_values])
  exact h
theorem leaf_4777_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4777.profileLo box_4777.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4777_ok
theorem branch_box_4777_nonnegative : ∀ j, 0 ≤ branch_box_4777.lower j ∧ 0 ≤ branch_box_4777.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4777, Box.profileLo, Box.profileHi, box_4777]
theorem leaf_4777_BranchSafe : CertificateConsequences.BranchSafe branch_box_4777 := by
  left; refine ⟨branch_box_4777_nonnegative, ?_⟩
  intro z hz; exact leaf_4777_sound hz

theorem leaf_4778_ok : checkAt 527 1000 box_4778 cert_4778 = true := by
  have h := List.all_eq_true.mp batch_95_11_ok accepted_4778 (by simp [batch_95_11_values])
  exact h
theorem leaf_4778_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4778.profileLo box_4778.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4778_ok
theorem branch_box_4778_nonnegative : ∀ j, 0 ≤ branch_box_4778.lower j ∧ 0 ≤ branch_box_4778.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4778, Box.profileLo, Box.profileHi, box_4778]
theorem leaf_4778_BranchSafe : CertificateConsequences.BranchSafe branch_box_4778 := by
  left; refine ⟨branch_box_4778_nonnegative, ?_⟩
  intro z hz; exact leaf_4778_sound hz

theorem leaf_4779_ok : checkAt 527 1000 box_4779 cert_4779 = true := by
  have h := List.all_eq_true.mp batch_95_12_ok accepted_4779 (by simp [batch_95_12_values])
  exact h
theorem leaf_4779_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4779.profileLo box_4779.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4779_ok
theorem branch_box_4779_nonnegative : ∀ j, 0 ≤ branch_box_4779.lower j ∧ 0 ≤ branch_box_4779.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4779, Box.profileLo, Box.profileHi, box_4779]
theorem leaf_4779_BranchSafe : CertificateConsequences.BranchSafe branch_box_4779 := by
  left; refine ⟨branch_box_4779_nonnegative, ?_⟩
  intro z hz; exact leaf_4779_sound hz

theorem leaf_4780_ok : checkAt 527 1000 box_4780 cert_4780 = true := by
  have h := List.all_eq_true.mp batch_95_13_ok accepted_4780 (by simp [batch_95_13_values])
  exact h
theorem leaf_4780_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4780.profileLo box_4780.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4780_ok
theorem branch_box_4780_nonnegative : ∀ j, 0 ≤ branch_box_4780.lower j ∧ 0 ≤ branch_box_4780.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4780, Box.profileLo, Box.profileHi, box_4780]
theorem leaf_4780_BranchSafe : CertificateConsequences.BranchSafe branch_box_4780 := by
  left; refine ⟨branch_box_4780_nonnegative, ?_⟩
  intro z hz; exact leaf_4780_sound hz

theorem leaf_4783_ok : checkAt 527 1000 box_4783 cert_4783 = true := by
  have h := List.all_eq_true.mp batch_95_14_ok accepted_4783 (by simp [batch_95_14_values])
  exact h
theorem leaf_4783_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4783.profileLo box_4783.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4783_ok
theorem branch_box_4783_nonnegative : ∀ j, 0 ≤ branch_box_4783.lower j ∧ 0 ≤ branch_box_4783.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4783, Box.profileLo, Box.profileHi, box_4783]
theorem leaf_4783_BranchSafe : CertificateConsequences.BranchSafe branch_box_4783 := by
  left; refine ⟨branch_box_4783_nonnegative, ?_⟩
  intro z hz; exact leaf_4783_sound hz

theorem leaf_4785_ok : checkAt 527 1000 box_4785 cert_4785 = true := by
  have h := List.all_eq_true.mp batch_95_15_ok accepted_4785 (by simp [batch_95_15_values])
  exact h
theorem leaf_4785_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4785.profileLo box_4785.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4785_ok
theorem branch_box_4785_nonnegative : ∀ j, 0 ≤ branch_box_4785.lower j ∧ 0 ≤ branch_box_4785.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4785, Box.profileLo, Box.profileHi, box_4785]
theorem leaf_4785_BranchSafe : CertificateConsequences.BranchSafe branch_box_4785 := by
  left; refine ⟨branch_box_4785_nonnegative, ?_⟩
  intro z hz; exact leaf_4785_sound hz

theorem leaf_4786_ok : checkAt 527 1000 box_4786 cert_4786 = true := by
  have h := List.all_eq_true.mp batch_95_16_ok accepted_4786 (by simp [batch_95_16_values])
  exact h
theorem leaf_4786_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4786.profileLo box_4786.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4786_ok
theorem branch_box_4786_nonnegative : ∀ j, 0 ≤ branch_box_4786.lower j ∧ 0 ≤ branch_box_4786.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4786, Box.profileLo, Box.profileHi, box_4786]
theorem leaf_4786_BranchSafe : CertificateConsequences.BranchSafe branch_box_4786 := by
  left; refine ⟨branch_box_4786_nonnegative, ?_⟩
  intro z hz; exact leaf_4786_sound hz

theorem leaf_4787_ok : checkAt 527 1000 box_4787 cert_4787 = true := by
  have h := List.all_eq_true.mp batch_95_17_ok accepted_4787 (by simp [batch_95_17_values])
  exact h
theorem leaf_4787_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4787.profileLo box_4787.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4787_ok
theorem branch_box_4787_nonnegative : ∀ j, 0 ≤ branch_box_4787.lower j ∧ 0 ≤ branch_box_4787.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4787, Box.profileLo, Box.profileHi, box_4787]
theorem leaf_4787_BranchSafe : CertificateConsequences.BranchSafe branch_box_4787 := by
  left; refine ⟨branch_box_4787_nonnegative, ?_⟩
  intro z hz; exact leaf_4787_sound hz

theorem leaf_4788_ok : checkAt 527 1000 box_4788 cert_4788 = true := by
  have h := List.all_eq_true.mp batch_95_18_ok accepted_4788 (by simp [batch_95_18_values])
  exact h
theorem leaf_4788_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4788.profileLo box_4788.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4788_ok
theorem branch_box_4788_nonnegative : ∀ j, 0 ≤ branch_box_4788.lower j ∧ 0 ≤ branch_box_4788.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4788, Box.profileLo, Box.profileHi, box_4788]
theorem leaf_4788_BranchSafe : CertificateConsequences.BranchSafe branch_box_4788 := by
  left; refine ⟨branch_box_4788_nonnegative, ?_⟩
  intro z hz; exact leaf_4788_sound hz

theorem leaf_4789_ok : checkAt 527 1000 box_4789 cert_4789 = true := by
  have h := List.all_eq_true.mp batch_95_19_ok accepted_4789 (by simp [batch_95_19_values])
  exact h
theorem leaf_4789_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4789.profileLo box_4789.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4789_ok
theorem branch_box_4789_nonnegative : ∀ j, 0 ≤ branch_box_4789.lower j ∧ 0 ≤ branch_box_4789.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4789, Box.profileLo, Box.profileHi, box_4789]
theorem leaf_4789_BranchSafe : CertificateConsequences.BranchSafe branch_box_4789 := by
  left; refine ⟨branch_box_4789_nonnegative, ?_⟩
  intro z hz; exact leaf_4789_sound hz

theorem leaf_4791_ok : checkAt 527 1000 box_4791 cert_4791 = true := by
  have h := List.all_eq_true.mp batch_95_20_ok accepted_4791 (by simp [batch_95_20_values])
  exact h
theorem leaf_4791_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4791.profileLo box_4791.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4791_ok
theorem branch_box_4791_nonnegative : ∀ j, 0 ≤ branch_box_4791.lower j ∧ 0 ≤ branch_box_4791.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4791, Box.profileLo, Box.profileHi, box_4791]
theorem leaf_4791_BranchSafe : CertificateConsequences.BranchSafe branch_box_4791 := by
  left; refine ⟨branch_box_4791_nonnegative, ?_⟩
  intro z hz; exact leaf_4791_sound hz

theorem leaf_4792_ok : checkAt 527 1000 box_4792 cert_4792 = true := by
  have h := List.all_eq_true.mp batch_95_21_ok accepted_4792 (by simp [batch_95_21_values])
  exact h
theorem leaf_4792_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4792.profileLo box_4792.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4792_ok
theorem branch_box_4792_nonnegative : ∀ j, 0 ≤ branch_box_4792.lower j ∧ 0 ≤ branch_box_4792.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4792, Box.profileLo, Box.profileHi, box_4792]
theorem leaf_4792_BranchSafe : CertificateConsequences.BranchSafe branch_box_4792 := by
  left; refine ⟨branch_box_4792_nonnegative, ?_⟩
  intro z hz; exact leaf_4792_sound hz

theorem leaf_4795_ok : checkAt 527 1000 box_4795 cert_4795 = true := by
  have h := List.all_eq_true.mp batch_95_22_ok accepted_4795 (by simp [batch_95_22_values])
  exact h
theorem leaf_4795_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4795.profileLo box_4795.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4795_ok
theorem branch_box_4795_nonnegative : ∀ j, 0 ≤ branch_box_4795.lower j ∧ 0 ≤ branch_box_4795.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4795, Box.profileLo, Box.profileHi, box_4795]
theorem leaf_4795_BranchSafe : CertificateConsequences.BranchSafe branch_box_4795 := by
  left; refine ⟨branch_box_4795_nonnegative, ?_⟩
  intro z hz; exact leaf_4795_sound hz

theorem leaf_4799_ok : checkAt 527 1000 box_4799 cert_4799 = true := by
  have h := List.all_eq_true.mp batch_95_23_ok accepted_4799 (by simp [batch_95_23_values])
  exact h
theorem leaf_4799_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4799.profileLo box_4799.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4799_ok
theorem branch_box_4799_nonnegative : ∀ j, 0 ≤ branch_box_4799.lower j ∧ 0 ≤ branch_box_4799.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4799, Box.profileLo, Box.profileHi, box_4799]
theorem leaf_4799_BranchSafe : CertificateConsequences.BranchSafe branch_box_4799 := by
  left; refine ⟨branch_box_4799_nonnegative, ?_⟩
  intro z hz; exact leaf_4799_sound hz

#print axioms batch_95_00_ok
#print axioms leaf_4750_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
