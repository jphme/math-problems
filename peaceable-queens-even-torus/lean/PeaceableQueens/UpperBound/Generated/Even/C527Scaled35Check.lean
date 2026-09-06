import PeaceableQueens.UpperBound.Generated.Even.C527Scaled35Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_35_00_values : List Bool := [accepted_1750]
theorem batch_35_00_ok : batch_35_00_values.all id = true := by decide

def batch_35_01_values : List Bool := [accepted_1752]
theorem batch_35_01_ok : batch_35_01_values.all id = true := by decide

def batch_35_02_values : List Bool := [accepted_1753]
theorem batch_35_02_ok : batch_35_02_values.all id = true := by decide

def batch_35_03_values : List Bool := [accepted_1754]
theorem batch_35_03_ok : batch_35_03_values.all id = true := by decide

def batch_35_04_values : List Bool := [accepted_1761]
theorem batch_35_04_ok : batch_35_04_values.all id = true := by decide

def batch_35_05_values : List Bool := [accepted_1763]
theorem batch_35_05_ok : batch_35_05_values.all id = true := by decide

def batch_35_06_values : List Bool := [accepted_1768]
theorem batch_35_06_ok : batch_35_06_values.all id = true := by decide

def batch_35_07_values : List Bool := [accepted_1769]
theorem batch_35_07_ok : batch_35_07_values.all id = true := by decide

def batch_35_08_values : List Bool := [accepted_1770]
theorem batch_35_08_ok : batch_35_08_values.all id = true := by decide

def batch_35_09_values : List Bool := [accepted_1771]
theorem batch_35_09_ok : batch_35_09_values.all id = true := by decide

def batch_35_10_values : List Bool := [accepted_1772]
theorem batch_35_10_ok : batch_35_10_values.all id = true := by decide

def batch_35_11_values : List Bool := [accepted_1773]
theorem batch_35_11_ok : batch_35_11_values.all id = true := by decide

def batch_35_12_values : List Bool := [accepted_1775]
theorem batch_35_12_ok : batch_35_12_values.all id = true := by decide

def batch_35_13_values : List Bool := [accepted_1777]
theorem batch_35_13_ok : batch_35_13_values.all id = true := by decide

def batch_35_14_values : List Bool := [accepted_1778]
theorem batch_35_14_ok : batch_35_14_values.all id = true := by decide

def batch_35_15_values : List Bool := [accepted_1781]
theorem batch_35_15_ok : batch_35_15_values.all id = true := by decide

def batch_35_16_values : List Bool := [accepted_1782]
theorem batch_35_16_ok : batch_35_16_values.all id = true := by decide

def batch_35_17_values : List Bool := [accepted_1783]
theorem batch_35_17_ok : batch_35_17_values.all id = true := by decide

def batch_35_18_values : List Bool := [accepted_1785]
theorem batch_35_18_ok : batch_35_18_values.all id = true := by decide

def batch_35_19_values : List Bool := [accepted_1786]
theorem batch_35_19_ok : batch_35_19_values.all id = true := by decide

def batch_35_20_values : List Bool := [accepted_1792]
theorem batch_35_20_ok : batch_35_20_values.all id = true := by decide

def batch_35_21_values : List Bool := [accepted_1793]
theorem batch_35_21_ok : batch_35_21_values.all id = true := by decide

def batch_35_22_values : List Bool := [accepted_1794]
theorem batch_35_22_ok : batch_35_22_values.all id = true := by decide

theorem leaf_1750_ok : checkAt 527 1000 box_1750 cert_1750 = true := by
  have h := List.all_eq_true.mp batch_35_00_ok accepted_1750 (by simp [batch_35_00_values])
  exact h
theorem leaf_1750_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1750.profileLo box_1750.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1750_ok
theorem branch_box_1750_nonnegative : ∀ j, 0 ≤ branch_box_1750.lower j ∧ 0 ≤ branch_box_1750.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1750, Box.profileLo, Box.profileHi, box_1750]
theorem leaf_1750_BranchSafe : CertificateConsequences.BranchSafe branch_box_1750 := by
  left; refine ⟨branch_box_1750_nonnegative, ?_⟩
  intro z hz; exact leaf_1750_sound hz

theorem leaf_1752_ok : checkAt 527 1000 box_1752 cert_1752 = true := by
  have h := List.all_eq_true.mp batch_35_01_ok accepted_1752 (by simp [batch_35_01_values])
  exact h
theorem leaf_1752_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1752.profileLo box_1752.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1752_ok
theorem branch_box_1752_nonnegative : ∀ j, 0 ≤ branch_box_1752.lower j ∧ 0 ≤ branch_box_1752.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1752, Box.profileLo, Box.profileHi, box_1752]
theorem leaf_1752_BranchSafe : CertificateConsequences.BranchSafe branch_box_1752 := by
  left; refine ⟨branch_box_1752_nonnegative, ?_⟩
  intro z hz; exact leaf_1752_sound hz

theorem leaf_1753_ok : checkAt 527 1000 box_1753 cert_1753 = true := by
  have h := List.all_eq_true.mp batch_35_02_ok accepted_1753 (by simp [batch_35_02_values])
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

theorem leaf_1754_ok : checkAt 527 1000 box_1754 cert_1754 = true := by
  have h := List.all_eq_true.mp batch_35_03_ok accepted_1754 (by simp [batch_35_03_values])
  exact h
theorem leaf_1754_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1754.profileLo box_1754.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1754_ok
theorem branch_box_1754_nonnegative : ∀ j, 0 ≤ branch_box_1754.lower j ∧ 0 ≤ branch_box_1754.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1754, Box.profileLo, Box.profileHi, box_1754]
theorem leaf_1754_BranchSafe : CertificateConsequences.BranchSafe branch_box_1754 := by
  left; refine ⟨branch_box_1754_nonnegative, ?_⟩
  intro z hz; exact leaf_1754_sound hz

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

theorem leaf_1768_ok : checkAt 527 1000 box_1768 cert_1768 = true := by
  have h := List.all_eq_true.mp batch_35_06_ok accepted_1768 (by simp [batch_35_06_values])
  exact h
theorem leaf_1768_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1768.profileLo box_1768.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1768_ok
theorem branch_box_1768_nonnegative : ∀ j, 0 ≤ branch_box_1768.lower j ∧ 0 ≤ branch_box_1768.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1768, Box.profileLo, Box.profileHi, box_1768]
theorem leaf_1768_BranchSafe : CertificateConsequences.BranchSafe branch_box_1768 := by
  left; refine ⟨branch_box_1768_nonnegative, ?_⟩
  intro z hz; exact leaf_1768_sound hz

theorem leaf_1769_ok : checkAt 527 1000 box_1769 cert_1769 = true := by
  have h := List.all_eq_true.mp batch_35_07_ok accepted_1769 (by simp [batch_35_07_values])
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

theorem leaf_1770_ok : checkAt 527 1000 box_1770 cert_1770 = true := by
  have h := List.all_eq_true.mp batch_35_08_ok accepted_1770 (by simp [batch_35_08_values])
  exact h
theorem leaf_1770_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1770.profileLo box_1770.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1770_ok
theorem branch_box_1770_nonnegative : ∀ j, 0 ≤ branch_box_1770.lower j ∧ 0 ≤ branch_box_1770.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1770, Box.profileLo, Box.profileHi, box_1770]
theorem leaf_1770_BranchSafe : CertificateConsequences.BranchSafe branch_box_1770 := by
  left; refine ⟨branch_box_1770_nonnegative, ?_⟩
  intro z hz; exact leaf_1770_sound hz

theorem leaf_1771_ok : checkAt 527 1000 box_1771 cert_1771 = true := by
  have h := List.all_eq_true.mp batch_35_09_ok accepted_1771 (by simp [batch_35_09_values])
  exact h
theorem leaf_1771_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1771.profileLo box_1771.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1771_ok
theorem branch_box_1771_nonnegative : ∀ j, 0 ≤ branch_box_1771.lower j ∧ 0 ≤ branch_box_1771.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1771, Box.profileLo, Box.profileHi, box_1771]
theorem leaf_1771_BranchSafe : CertificateConsequences.BranchSafe branch_box_1771 := by
  left; refine ⟨branch_box_1771_nonnegative, ?_⟩
  intro z hz; exact leaf_1771_sound hz

theorem leaf_1772_ok : checkAt 527 1000 box_1772 cert_1772 = true := by
  have h := List.all_eq_true.mp batch_35_10_ok accepted_1772 (by simp [batch_35_10_values])
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

theorem leaf_1773_ok : checkAt 527 1000 box_1773 cert_1773 = true := by
  have h := List.all_eq_true.mp batch_35_11_ok accepted_1773 (by simp [batch_35_11_values])
  exact h
theorem leaf_1773_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1773.profileLo box_1773.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1773_ok
theorem branch_box_1773_nonnegative : ∀ j, 0 ≤ branch_box_1773.lower j ∧ 0 ≤ branch_box_1773.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1773, Box.profileLo, Box.profileHi, box_1773]
theorem leaf_1773_BranchSafe : CertificateConsequences.BranchSafe branch_box_1773 := by
  left; refine ⟨branch_box_1773_nonnegative, ?_⟩
  intro z hz; exact leaf_1773_sound hz

theorem leaf_1775_ok : checkAt 527 1000 box_1775 cert_1775 = true := by
  have h := List.all_eq_true.mp batch_35_12_ok accepted_1775 (by simp [batch_35_12_values])
  exact h
theorem leaf_1775_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1775.profileLo box_1775.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1775_ok
theorem branch_box_1775_nonnegative : ∀ j, 0 ≤ branch_box_1775.lower j ∧ 0 ≤ branch_box_1775.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1775, Box.profileLo, Box.profileHi, box_1775]
theorem leaf_1775_BranchSafe : CertificateConsequences.BranchSafe branch_box_1775 := by
  left; refine ⟨branch_box_1775_nonnegative, ?_⟩
  intro z hz; exact leaf_1775_sound hz

theorem leaf_1777_ok : checkAt 527 1000 box_1777 cert_1777 = true := by
  have h := List.all_eq_true.mp batch_35_13_ok accepted_1777 (by simp [batch_35_13_values])
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

theorem leaf_1778_ok : checkAt 527 1000 box_1778 cert_1778 = true := by
  have h := List.all_eq_true.mp batch_35_14_ok accepted_1778 (by simp [batch_35_14_values])
  exact h
theorem leaf_1778_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1778.profileLo box_1778.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1778_ok
theorem branch_box_1778_nonnegative : ∀ j, 0 ≤ branch_box_1778.lower j ∧ 0 ≤ branch_box_1778.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1778, Box.profileLo, Box.profileHi, box_1778]
theorem leaf_1778_BranchSafe : CertificateConsequences.BranchSafe branch_box_1778 := by
  left; refine ⟨branch_box_1778_nonnegative, ?_⟩
  intro z hz; exact leaf_1778_sound hz

theorem leaf_1781_ok : checkAt 527 1000 box_1781 cert_1781 = true := by
  have h := List.all_eq_true.mp batch_35_15_ok accepted_1781 (by simp [batch_35_15_values])
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

theorem leaf_1782_ok : checkAt 527 1000 box_1782 cert_1782 = true := by
  have h := List.all_eq_true.mp batch_35_16_ok accepted_1782 (by simp [batch_35_16_values])
  exact h
theorem leaf_1782_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1782.profileLo box_1782.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1782_ok
theorem branch_box_1782_nonnegative : ∀ j, 0 ≤ branch_box_1782.lower j ∧ 0 ≤ branch_box_1782.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1782, Box.profileLo, Box.profileHi, box_1782]
theorem leaf_1782_BranchSafe : CertificateConsequences.BranchSafe branch_box_1782 := by
  left; refine ⟨branch_box_1782_nonnegative, ?_⟩
  intro z hz; exact leaf_1782_sound hz

theorem leaf_1783_ok : checkAt 527 1000 box_1783 cert_1783 = true := by
  have h := List.all_eq_true.mp batch_35_17_ok accepted_1783 (by simp [batch_35_17_values])
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

theorem leaf_1785_ok : checkAt 527 1000 box_1785 cert_1785 = true := by
  have h := List.all_eq_true.mp batch_35_18_ok accepted_1785 (by simp [batch_35_18_values])
  exact h
theorem leaf_1785_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1785.profileLo box_1785.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1785_ok
theorem branch_box_1785_nonnegative : ∀ j, 0 ≤ branch_box_1785.lower j ∧ 0 ≤ branch_box_1785.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1785, Box.profileLo, Box.profileHi, box_1785]
theorem leaf_1785_BranchSafe : CertificateConsequences.BranchSafe branch_box_1785 := by
  left; refine ⟨branch_box_1785_nonnegative, ?_⟩
  intro z hz; exact leaf_1785_sound hz

theorem leaf_1786_ok : checkAt 527 1000 box_1786 cert_1786 = true := by
  have h := List.all_eq_true.mp batch_35_19_ok accepted_1786 (by simp [batch_35_19_values])
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

theorem leaf_1792_ok : checkAt 527 1000 box_1792 cert_1792 = true := by
  have h := List.all_eq_true.mp batch_35_20_ok accepted_1792 (by simp [batch_35_20_values])
  exact h
theorem leaf_1792_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1792.profileLo box_1792.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1792_ok
theorem branch_box_1792_nonnegative : ∀ j, 0 ≤ branch_box_1792.lower j ∧ 0 ≤ branch_box_1792.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1792, Box.profileLo, Box.profileHi, box_1792]
theorem leaf_1792_BranchSafe : CertificateConsequences.BranchSafe branch_box_1792 := by
  left; refine ⟨branch_box_1792_nonnegative, ?_⟩
  intro z hz; exact leaf_1792_sound hz

theorem leaf_1793_ok : checkAt 527 1000 box_1793 cert_1793 = true := by
  have h := List.all_eq_true.mp batch_35_21_ok accepted_1793 (by simp [batch_35_21_values])
  exact h
theorem leaf_1793_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1793.profileLo box_1793.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1793_ok
theorem branch_box_1793_nonnegative : ∀ j, 0 ≤ branch_box_1793.lower j ∧ 0 ≤ branch_box_1793.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1793, Box.profileLo, Box.profileHi, box_1793]
theorem leaf_1793_BranchSafe : CertificateConsequences.BranchSafe branch_box_1793 := by
  left; refine ⟨branch_box_1793_nonnegative, ?_⟩
  intro z hz; exact leaf_1793_sound hz

theorem leaf_1794_ok : checkAt 527 1000 box_1794 cert_1794 = true := by
  have h := List.all_eq_true.mp batch_35_22_ok accepted_1794 (by simp [batch_35_22_values])
  exact h
theorem leaf_1794_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1794.profileLo box_1794.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1794_ok
theorem branch_box_1794_nonnegative : ∀ j, 0 ≤ branch_box_1794.lower j ∧ 0 ≤ branch_box_1794.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1794, Box.profileLo, Box.profileHi, box_1794]
theorem leaf_1794_BranchSafe : CertificateConsequences.BranchSafe branch_box_1794 := by
  left; refine ⟨branch_box_1794_nonnegative, ?_⟩
  intro z hz; exact leaf_1794_sound hz

#print axioms batch_35_00_ok
#print axioms leaf_1750_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
