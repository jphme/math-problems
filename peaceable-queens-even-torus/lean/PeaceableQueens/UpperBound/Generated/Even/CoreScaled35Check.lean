import PeaceableQueens.UpperBound.Generated.Even.CoreScaled35Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_35_00_values : List Bool := [accepted_1751]
theorem batch_35_00_ok : batch_35_00_values.all id = true := by decide

def batch_35_01_values : List Bool := [accepted_1753]
theorem batch_35_01_ok : batch_35_01_values.all id = true := by decide

def batch_35_02_values : List Bool := [accepted_1755]
theorem batch_35_02_ok : batch_35_02_values.all id = true := by decide

def batch_35_03_values : List Bool := [accepted_1759]
theorem batch_35_03_ok : batch_35_03_values.all id = true := by decide

def batch_35_04_values : List Bool := [accepted_1761]
theorem batch_35_04_ok : batch_35_04_values.all id = true := by decide

def batch_35_05_values : List Bool := [accepted_1763]
theorem batch_35_05_ok : batch_35_05_values.all id = true := by decide

def batch_35_06_values : List Bool := [accepted_1765]
theorem batch_35_06_ok : batch_35_06_values.all id = true := by decide

def batch_35_07_values : List Bool := [accepted_1767]
theorem batch_35_07_ok : batch_35_07_values.all id = true := by decide

def batch_35_08_values : List Bool := [accepted_1769]
theorem batch_35_08_ok : batch_35_08_values.all id = true := by decide

def batch_35_09_values : List Bool := [accepted_1772]
theorem batch_35_09_ok : batch_35_09_values.all id = true := by decide

def batch_35_10_values : List Bool := [accepted_1777]
theorem batch_35_10_ok : batch_35_10_values.all id = true := by decide

def batch_35_11_values : List Bool := [accepted_1781]
theorem batch_35_11_ok : batch_35_11_values.all id = true := by decide

def batch_35_12_values : List Bool := [accepted_1783]
theorem batch_35_12_ok : batch_35_12_values.all id = true := by decide

def batch_35_13_values : List Bool := [accepted_1786]
theorem batch_35_13_ok : batch_35_13_values.all id = true := by decide

def batch_35_14_values : List Bool := [accepted_1787]
theorem batch_35_14_ok : batch_35_14_values.all id = true := by decide

def batch_35_15_values : List Bool := [accepted_1789]
theorem batch_35_15_ok : batch_35_15_values.all id = true := by decide

def batch_35_16_values : List Bool := [accepted_1791]
theorem batch_35_16_ok : batch_35_16_values.all id = true := by decide

def batch_35_17_values : List Bool := [accepted_1796]
theorem batch_35_17_ok : batch_35_17_values.all id = true := by decide

def batch_35_18_values : List Bool := [accepted_1798]
theorem batch_35_18_ok : batch_35_18_values.all id = true := by decide

def batch_35_19_values : List Bool := [accepted_1799]
theorem batch_35_19_ok : batch_35_19_values.all id = true := by decide

theorem leaf_1751_ok : checkAt 527 1000 box_1751 cert_1751 = true := by
  have h := List.all_eq_true.mp batch_35_00_ok accepted_1751 (by simp [batch_35_00_values])
  exact h
theorem leaf_1751_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1751.profileLo box_1751.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1751_ok
theorem branch_box_1751_nonnegative : ∀ j, 0 ≤ branch_box_1751.lower j ∧ 0 ≤ branch_box_1751.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1751, Box.profileLo, Box.profileHi, box_1751]
theorem leaf_1751_BranchSafe : CertificateConsequences.BranchSafe branch_box_1751 := by
  left; refine ⟨branch_box_1751_nonnegative, ?_⟩
  intro z hz; exact leaf_1751_sound hz

theorem leaf_1753_ok : checkAt 527 1000 box_1753 cert_1753 = true := by
  have h := List.all_eq_true.mp batch_35_01_ok accepted_1753 (by simp [batch_35_01_values])
  exact h
theorem leaf_1753_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1753.profileLo box_1753.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1753_ok
theorem branch_box_1753_nonnegative : ∀ j, 0 ≤ branch_box_1753.lower j ∧ 0 ≤ branch_box_1753.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1753, Box.profileLo, Box.profileHi, box_1753]
theorem leaf_1753_BranchSafe : CertificateConsequences.BranchSafe branch_box_1753 := by
  left; refine ⟨branch_box_1753_nonnegative, ?_⟩
  intro z hz; exact leaf_1753_sound hz

theorem leaf_1755_ok : checkAt 527 1000 box_1755 cert_1755 = true := by
  have h := List.all_eq_true.mp batch_35_02_ok accepted_1755 (by simp [batch_35_02_values])
  exact h
theorem leaf_1755_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1755.profileLo box_1755.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1755_ok
theorem branch_box_1755_nonnegative : ∀ j, 0 ≤ branch_box_1755.lower j ∧ 0 ≤ branch_box_1755.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1755, Box.profileLo, Box.profileHi, box_1755]
theorem leaf_1755_BranchSafe : CertificateConsequences.BranchSafe branch_box_1755 := by
  left; refine ⟨branch_box_1755_nonnegative, ?_⟩
  intro z hz; exact leaf_1755_sound hz

theorem leaf_1759_ok : checkAt 527 1000 box_1759 cert_1759 = true := by
  have h := List.all_eq_true.mp batch_35_03_ok accepted_1759 (by simp [batch_35_03_values])
  exact h
theorem leaf_1759_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1759.profileLo box_1759.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1759_ok
theorem branch_box_1759_nonnegative : ∀ j, 0 ≤ branch_box_1759.lower j ∧ 0 ≤ branch_box_1759.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1759, Box.profileLo, Box.profileHi, box_1759]
theorem leaf_1759_BranchSafe : CertificateConsequences.BranchSafe branch_box_1759 := by
  left; refine ⟨branch_box_1759_nonnegative, ?_⟩
  intro z hz; exact leaf_1759_sound hz

theorem leaf_1761_ok : checkAt 527 1000 box_1761 cert_1761 = true := by
  have h := List.all_eq_true.mp batch_35_04_ok accepted_1761 (by simp [batch_35_04_values])
  exact h
theorem leaf_1761_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1761.profileLo box_1761.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1761_ok
theorem branch_box_1761_nonnegative : ∀ j, 0 ≤ branch_box_1761.lower j ∧ 0 ≤ branch_box_1761.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1761, Box.profileLo, Box.profileHi, box_1761]
theorem leaf_1761_BranchSafe : CertificateConsequences.BranchSafe branch_box_1761 := by
  left; refine ⟨branch_box_1761_nonnegative, ?_⟩
  intro z hz; exact leaf_1761_sound hz

theorem leaf_1763_ok : checkAt 527 1000 box_1763 cert_1763 = true := by
  have h := List.all_eq_true.mp batch_35_05_ok accepted_1763 (by simp [batch_35_05_values])
  exact h
theorem leaf_1763_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1763.profileLo box_1763.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1763_ok
theorem branch_box_1763_nonnegative : ∀ j, 0 ≤ branch_box_1763.lower j ∧ 0 ≤ branch_box_1763.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1763, Box.profileLo, Box.profileHi, box_1763]
theorem leaf_1763_BranchSafe : CertificateConsequences.BranchSafe branch_box_1763 := by
  left; refine ⟨branch_box_1763_nonnegative, ?_⟩
  intro z hz; exact leaf_1763_sound hz

theorem leaf_1765_ok : checkAt 527 1000 box_1765 cert_1765 = true := by
  have h := List.all_eq_true.mp batch_35_06_ok accepted_1765 (by simp [batch_35_06_values])
  exact h
theorem leaf_1765_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1765.profileLo box_1765.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1765_ok
theorem branch_box_1765_nonnegative : ∀ j, 0 ≤ branch_box_1765.lower j ∧ 0 ≤ branch_box_1765.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1765, Box.profileLo, Box.profileHi, box_1765]
theorem leaf_1765_BranchSafe : CertificateConsequences.BranchSafe branch_box_1765 := by
  left; refine ⟨branch_box_1765_nonnegative, ?_⟩
  intro z hz; exact leaf_1765_sound hz

theorem leaf_1767_ok : checkAt 527 1000 box_1767 cert_1767 = true := by
  have h := List.all_eq_true.mp batch_35_07_ok accepted_1767 (by simp [batch_35_07_values])
  exact h
theorem leaf_1767_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1767.profileLo box_1767.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1767_ok
theorem branch_box_1767_nonnegative : ∀ j, 0 ≤ branch_box_1767.lower j ∧ 0 ≤ branch_box_1767.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1767, Box.profileLo, Box.profileHi, box_1767]
theorem leaf_1767_BranchSafe : CertificateConsequences.BranchSafe branch_box_1767 := by
  left; refine ⟨branch_box_1767_nonnegative, ?_⟩
  intro z hz; exact leaf_1767_sound hz

theorem leaf_1769_ok : checkAt 527 1000 box_1769 cert_1769 = true := by
  have h := List.all_eq_true.mp batch_35_08_ok accepted_1769 (by simp [batch_35_08_values])
  exact h
theorem leaf_1769_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1769.profileLo box_1769.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1769_ok
theorem branch_box_1769_nonnegative : ∀ j, 0 ≤ branch_box_1769.lower j ∧ 0 ≤ branch_box_1769.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1769, Box.profileLo, Box.profileHi, box_1769]
theorem leaf_1769_BranchSafe : CertificateConsequences.BranchSafe branch_box_1769 := by
  left; refine ⟨branch_box_1769_nonnegative, ?_⟩
  intro z hz; exact leaf_1769_sound hz

theorem leaf_1772_ok : checkAt 527 1000 box_1772 cert_1772 = true := by
  have h := List.all_eq_true.mp batch_35_09_ok accepted_1772 (by simp [batch_35_09_values])
  exact h
theorem leaf_1772_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1772.profileLo box_1772.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1772_ok
theorem branch_box_1772_nonnegative : ∀ j, 0 ≤ branch_box_1772.lower j ∧ 0 ≤ branch_box_1772.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1772, Box.profileLo, Box.profileHi, box_1772]
theorem leaf_1772_BranchSafe : CertificateConsequences.BranchSafe branch_box_1772 := by
  left; refine ⟨branch_box_1772_nonnegative, ?_⟩
  intro z hz; exact leaf_1772_sound hz

theorem leaf_1777_ok : checkAt 527 1000 box_1777 cert_1777 = true := by
  have h := List.all_eq_true.mp batch_35_10_ok accepted_1777 (by simp [batch_35_10_values])
  exact h
theorem leaf_1777_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1777.profileLo box_1777.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1777_ok
theorem branch_box_1777_nonnegative : ∀ j, 0 ≤ branch_box_1777.lower j ∧ 0 ≤ branch_box_1777.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1777, Box.profileLo, Box.profileHi, box_1777]
theorem leaf_1777_BranchSafe : CertificateConsequences.BranchSafe branch_box_1777 := by
  left; refine ⟨branch_box_1777_nonnegative, ?_⟩
  intro z hz; exact leaf_1777_sound hz

theorem leaf_1781_ok : checkAt 527 1000 box_1781 cert_1781 = true := by
  have h := List.all_eq_true.mp batch_35_11_ok accepted_1781 (by simp [batch_35_11_values])
  exact h
theorem leaf_1781_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1781.profileLo box_1781.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1781_ok
theorem branch_box_1781_nonnegative : ∀ j, 0 ≤ branch_box_1781.lower j ∧ 0 ≤ branch_box_1781.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1781, Box.profileLo, Box.profileHi, box_1781]
theorem leaf_1781_BranchSafe : CertificateConsequences.BranchSafe branch_box_1781 := by
  left; refine ⟨branch_box_1781_nonnegative, ?_⟩
  intro z hz; exact leaf_1781_sound hz

theorem leaf_1783_ok : checkAt 527 1000 box_1783 cert_1783 = true := by
  have h := List.all_eq_true.mp batch_35_12_ok accepted_1783 (by simp [batch_35_12_values])
  exact h
theorem leaf_1783_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1783.profileLo box_1783.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1783_ok
theorem branch_box_1783_nonnegative : ∀ j, 0 ≤ branch_box_1783.lower j ∧ 0 ≤ branch_box_1783.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1783, Box.profileLo, Box.profileHi, box_1783]
theorem leaf_1783_BranchSafe : CertificateConsequences.BranchSafe branch_box_1783 := by
  left; refine ⟨branch_box_1783_nonnegative, ?_⟩
  intro z hz; exact leaf_1783_sound hz

theorem leaf_1786_ok : checkAt 527 1000 box_1786 cert_1786 = true := by
  have h := List.all_eq_true.mp batch_35_13_ok accepted_1786 (by simp [batch_35_13_values])
  exact h
theorem leaf_1786_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1786.profileLo box_1786.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1786_ok
theorem branch_box_1786_nonnegative : ∀ j, 0 ≤ branch_box_1786.lower j ∧ 0 ≤ branch_box_1786.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1786, Box.profileLo, Box.profileHi, box_1786]
theorem leaf_1786_BranchSafe : CertificateConsequences.BranchSafe branch_box_1786 := by
  left; refine ⟨branch_box_1786_nonnegative, ?_⟩
  intro z hz; exact leaf_1786_sound hz

theorem leaf_1787_ok : checkAt 527 1000 box_1787 cert_1787 = true := by
  have h := List.all_eq_true.mp batch_35_14_ok accepted_1787 (by simp [batch_35_14_values])
  exact h
theorem leaf_1787_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1787.profileLo box_1787.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1787_ok
theorem branch_box_1787_nonnegative : ∀ j, 0 ≤ branch_box_1787.lower j ∧ 0 ≤ branch_box_1787.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1787, Box.profileLo, Box.profileHi, box_1787]
theorem leaf_1787_BranchSafe : CertificateConsequences.BranchSafe branch_box_1787 := by
  left; refine ⟨branch_box_1787_nonnegative, ?_⟩
  intro z hz; exact leaf_1787_sound hz

theorem leaf_1789_ok : checkAt 527 1000 box_1789 cert_1789 = true := by
  have h := List.all_eq_true.mp batch_35_15_ok accepted_1789 (by simp [batch_35_15_values])
  exact h
theorem leaf_1789_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1789.profileLo box_1789.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1789_ok
theorem branch_box_1789_nonnegative : ∀ j, 0 ≤ branch_box_1789.lower j ∧ 0 ≤ branch_box_1789.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1789, Box.profileLo, Box.profileHi, box_1789]
theorem leaf_1789_BranchSafe : CertificateConsequences.BranchSafe branch_box_1789 := by
  left; refine ⟨branch_box_1789_nonnegative, ?_⟩
  intro z hz; exact leaf_1789_sound hz

theorem leaf_1791_ok : checkAt 527 1000 box_1791 cert_1791 = true := by
  have h := List.all_eq_true.mp batch_35_16_ok accepted_1791 (by simp [batch_35_16_values])
  exact h
theorem leaf_1791_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1791.profileLo box_1791.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1791_ok
theorem branch_box_1791_nonnegative : ∀ j, 0 ≤ branch_box_1791.lower j ∧ 0 ≤ branch_box_1791.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1791, Box.profileLo, Box.profileHi, box_1791]
theorem leaf_1791_BranchSafe : CertificateConsequences.BranchSafe branch_box_1791 := by
  left; refine ⟨branch_box_1791_nonnegative, ?_⟩
  intro z hz; exact leaf_1791_sound hz

theorem leaf_1796_ok : checkAt 527 1000 box_1796 cert_1796 = true := by
  have h := List.all_eq_true.mp batch_35_17_ok accepted_1796 (by simp [batch_35_17_values])
  exact h
theorem leaf_1796_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1796.profileLo box_1796.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1796_ok
theorem branch_box_1796_nonnegative : ∀ j, 0 ≤ branch_box_1796.lower j ∧ 0 ≤ branch_box_1796.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1796, Box.profileLo, Box.profileHi, box_1796]
theorem leaf_1796_BranchSafe : CertificateConsequences.BranchSafe branch_box_1796 := by
  left; refine ⟨branch_box_1796_nonnegative, ?_⟩
  intro z hz; exact leaf_1796_sound hz

theorem leaf_1798_ok : checkAt 527 1000 box_1798 cert_1798 = true := by
  have h := List.all_eq_true.mp batch_35_18_ok accepted_1798 (by simp [batch_35_18_values])
  exact h
theorem leaf_1798_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1798.profileLo box_1798.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1798_ok
theorem branch_box_1798_nonnegative : ∀ j, 0 ≤ branch_box_1798.lower j ∧ 0 ≤ branch_box_1798.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1798, Box.profileLo, Box.profileHi, box_1798]
theorem leaf_1798_BranchSafe : CertificateConsequences.BranchSafe branch_box_1798 := by
  left; refine ⟨branch_box_1798_nonnegative, ?_⟩
  intro z hz; exact leaf_1798_sound hz

theorem leaf_1799_ok : checkAt 527 1000 box_1799 cert_1799 = true := by
  have h := List.all_eq_true.mp batch_35_19_ok accepted_1799 (by simp [batch_35_19_values])
  exact h
theorem leaf_1799_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1799.profileLo box_1799.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1799_ok
theorem branch_box_1799_nonnegative : ∀ j, 0 ≤ branch_box_1799.lower j ∧ 0 ≤ branch_box_1799.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1799, Box.profileLo, Box.profileHi, box_1799]
theorem leaf_1799_BranchSafe : CertificateConsequences.BranchSafe branch_box_1799 := by
  left; refine ⟨branch_box_1799_nonnegative, ?_⟩
  intro z hz; exact leaf_1799_sound hz

#print axioms batch_35_00_ok
#print axioms leaf_1751_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
