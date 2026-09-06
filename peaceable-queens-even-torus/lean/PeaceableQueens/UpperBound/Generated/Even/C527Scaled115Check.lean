import PeaceableQueens.UpperBound.Generated.Even.C527Scaled115Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_115_00_values : List Bool := [accepted_5750]
theorem batch_115_00_ok : batch_115_00_values.all id = true := by decide

def batch_115_01_values : List Bool := [accepted_5753]
theorem batch_115_01_ok : batch_115_01_values.all id = true := by decide

def batch_115_02_values : List Bool := [accepted_5755]
theorem batch_115_02_ok : batch_115_02_values.all id = true := by decide

def batch_115_03_values : List Bool := [accepted_5756]
theorem batch_115_03_ok : batch_115_03_values.all id = true := by decide

def batch_115_04_values : List Bool := [accepted_5757]
theorem batch_115_04_ok : batch_115_04_values.all id = true := by decide

def batch_115_05_values : List Bool := [accepted_5758]
theorem batch_115_05_ok : batch_115_05_values.all id = true := by decide

def batch_115_06_values : List Bool := [accepted_5761]
theorem batch_115_06_ok : batch_115_06_values.all id = true := by decide

def batch_115_07_values : List Bool := [accepted_5763]
theorem batch_115_07_ok : batch_115_07_values.all id = true := by decide

def batch_115_08_values : List Bool := [accepted_5764]
theorem batch_115_08_ok : batch_115_08_values.all id = true := by decide

def batch_115_09_values : List Bool := [accepted_5768]
theorem batch_115_09_ok : batch_115_09_values.all id = true := by decide

def batch_115_10_values : List Bool := [accepted_5769]
theorem batch_115_10_ok : batch_115_10_values.all id = true := by decide

def batch_115_11_values : List Bool := [accepted_5770]
theorem batch_115_11_ok : batch_115_11_values.all id = true := by decide

def batch_115_12_values : List Bool := [accepted_5773]
theorem batch_115_12_ok : batch_115_12_values.all id = true := by decide

def batch_115_13_values : List Bool := [accepted_5774]
theorem batch_115_13_ok : batch_115_13_values.all id = true := by decide

def batch_115_14_values : List Bool := [accepted_5775]
theorem batch_115_14_ok : batch_115_14_values.all id = true := by decide

def batch_115_15_values : List Bool := [accepted_5776]
theorem batch_115_15_ok : batch_115_15_values.all id = true := by decide

def batch_115_16_values : List Bool := [accepted_5783]
theorem batch_115_16_ok : batch_115_16_values.all id = true := by decide

def batch_115_17_values : List Bool := [accepted_5784]
theorem batch_115_17_ok : batch_115_17_values.all id = true := by decide

def batch_115_18_values : List Bool := [accepted_5786]
theorem batch_115_18_ok : batch_115_18_values.all id = true := by decide

def batch_115_19_values : List Bool := [accepted_5787]
theorem batch_115_19_ok : batch_115_19_values.all id = true := by decide

def batch_115_20_values : List Bool := [accepted_5788]
theorem batch_115_20_ok : batch_115_20_values.all id = true := by decide

def batch_115_21_values : List Bool := [accepted_5795]
theorem batch_115_21_ok : batch_115_21_values.all id = true := by decide

def batch_115_22_values : List Bool := [accepted_5796]
theorem batch_115_22_ok : batch_115_22_values.all id = true := by decide

def batch_115_23_values : List Bool := [accepted_5797]
theorem batch_115_23_ok : batch_115_23_values.all id = true := by decide

def batch_115_24_values : List Bool := [accepted_5798]
theorem batch_115_24_ok : batch_115_24_values.all id = true := by decide

def batch_115_25_values : List Bool := [accepted_5799]
theorem batch_115_25_ok : batch_115_25_values.all id = true := by decide

theorem leaf_5750_ok : checkAt 527 1000 box_5750 cert_5750 = true := by
  have h := List.all_eq_true.mp batch_115_00_ok accepted_5750 (by simp [batch_115_00_values])
  exact h
theorem leaf_5750_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5750.profileLo box_5750.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5750_ok
theorem branch_box_5750_nonnegative : ∀ j, 0 ≤ branch_box_5750.lower j ∧ 0 ≤ branch_box_5750.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5750, Box.profileLo, Box.profileHi, box_5750]
theorem leaf_5750_BranchSafe : CertificateConsequences.BranchSafe branch_box_5750 := by
  left; refine ⟨branch_box_5750_nonnegative, ?_⟩
  intro z hz; exact leaf_5750_sound hz

theorem leaf_5753_ok : checkAt 527 1000 box_5753 cert_5753 = true := by
  have h := List.all_eq_true.mp batch_115_01_ok accepted_5753 (by simp [batch_115_01_values])
  exact h
theorem leaf_5753_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5753.profileLo box_5753.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5753_ok
theorem branch_box_5753_nonnegative : ∀ j, 0 ≤ branch_box_5753.lower j ∧ 0 ≤ branch_box_5753.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5753, Box.profileLo, Box.profileHi, box_5753]
theorem leaf_5753_BranchSafe : CertificateConsequences.BranchSafe branch_box_5753 := by
  left; refine ⟨branch_box_5753_nonnegative, ?_⟩
  intro z hz; exact leaf_5753_sound hz

theorem leaf_5755_ok : checkAt 527 1000 box_5755 cert_5755 = true := by
  have h := List.all_eq_true.mp batch_115_02_ok accepted_5755 (by simp [batch_115_02_values])
  exact h
theorem leaf_5755_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5755.profileLo box_5755.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5755_ok
theorem branch_box_5755_nonnegative : ∀ j, 0 ≤ branch_box_5755.lower j ∧ 0 ≤ branch_box_5755.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5755, Box.profileLo, Box.profileHi, box_5755]
theorem leaf_5755_BranchSafe : CertificateConsequences.BranchSafe branch_box_5755 := by
  left; refine ⟨branch_box_5755_nonnegative, ?_⟩
  intro z hz; exact leaf_5755_sound hz

theorem leaf_5756_ok : checkAt 527 1000 box_5756 cert_5756 = true := by
  have h := List.all_eq_true.mp batch_115_03_ok accepted_5756 (by simp [batch_115_03_values])
  exact h
theorem leaf_5756_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5756.profileLo box_5756.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5756_ok
theorem branch_box_5756_nonnegative : ∀ j, 0 ≤ branch_box_5756.lower j ∧ 0 ≤ branch_box_5756.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5756, Box.profileLo, Box.profileHi, box_5756]
theorem leaf_5756_BranchSafe : CertificateConsequences.BranchSafe branch_box_5756 := by
  left; refine ⟨branch_box_5756_nonnegative, ?_⟩
  intro z hz; exact leaf_5756_sound hz

theorem leaf_5757_ok : checkAt 527 1000 box_5757 cert_5757 = true := by
  have h := List.all_eq_true.mp batch_115_04_ok accepted_5757 (by simp [batch_115_04_values])
  exact h
theorem leaf_5757_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5757.profileLo box_5757.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5757_ok
theorem branch_box_5757_nonnegative : ∀ j, 0 ≤ branch_box_5757.lower j ∧ 0 ≤ branch_box_5757.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5757, Box.profileLo, Box.profileHi, box_5757]
theorem leaf_5757_BranchSafe : CertificateConsequences.BranchSafe branch_box_5757 := by
  left; refine ⟨branch_box_5757_nonnegative, ?_⟩
  intro z hz; exact leaf_5757_sound hz

theorem leaf_5758_ok : checkAt 527 1000 box_5758 cert_5758 = true := by
  have h := List.all_eq_true.mp batch_115_05_ok accepted_5758 (by simp [batch_115_05_values])
  exact h
theorem leaf_5758_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5758.profileLo box_5758.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5758_ok
theorem branch_box_5758_nonnegative : ∀ j, 0 ≤ branch_box_5758.lower j ∧ 0 ≤ branch_box_5758.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5758, Box.profileLo, Box.profileHi, box_5758]
theorem leaf_5758_BranchSafe : CertificateConsequences.BranchSafe branch_box_5758 := by
  left; refine ⟨branch_box_5758_nonnegative, ?_⟩
  intro z hz; exact leaf_5758_sound hz

theorem leaf_5761_ok : checkAt 527 1000 box_5761 cert_5761 = true := by
  have h := List.all_eq_true.mp batch_115_06_ok accepted_5761 (by simp [batch_115_06_values])
  exact h
theorem leaf_5761_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5761.profileLo box_5761.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5761_ok
theorem branch_box_5761_nonnegative : ∀ j, 0 ≤ branch_box_5761.lower j ∧ 0 ≤ branch_box_5761.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5761, Box.profileLo, Box.profileHi, box_5761]
theorem leaf_5761_BranchSafe : CertificateConsequences.BranchSafe branch_box_5761 := by
  left; refine ⟨branch_box_5761_nonnegative, ?_⟩
  intro z hz; exact leaf_5761_sound hz

theorem leaf_5763_ok : checkAt 527 1000 box_5763 cert_5763 = true := by
  have h := List.all_eq_true.mp batch_115_07_ok accepted_5763 (by simp [batch_115_07_values])
  exact h
theorem leaf_5763_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5763.profileLo box_5763.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5763_ok
theorem branch_box_5763_nonnegative : ∀ j, 0 ≤ branch_box_5763.lower j ∧ 0 ≤ branch_box_5763.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5763, Box.profileLo, Box.profileHi, box_5763]
theorem leaf_5763_BranchSafe : CertificateConsequences.BranchSafe branch_box_5763 := by
  left; refine ⟨branch_box_5763_nonnegative, ?_⟩
  intro z hz; exact leaf_5763_sound hz

theorem leaf_5764_ok : checkAt 527 1000 box_5764 cert_5764 = true := by
  have h := List.all_eq_true.mp batch_115_08_ok accepted_5764 (by simp [batch_115_08_values])
  exact h
theorem leaf_5764_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5764.profileLo box_5764.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5764_ok
theorem branch_box_5764_nonnegative : ∀ j, 0 ≤ branch_box_5764.lower j ∧ 0 ≤ branch_box_5764.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5764, Box.profileLo, Box.profileHi, box_5764]
theorem leaf_5764_BranchSafe : CertificateConsequences.BranchSafe branch_box_5764 := by
  left; refine ⟨branch_box_5764_nonnegative, ?_⟩
  intro z hz; exact leaf_5764_sound hz

theorem leaf_5768_ok : checkAt 527 1000 box_5768 cert_5768 = true := by
  have h := List.all_eq_true.mp batch_115_09_ok accepted_5768 (by simp [batch_115_09_values])
  exact h
theorem leaf_5768_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5768.profileLo box_5768.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5768_ok
theorem branch_box_5768_nonnegative : ∀ j, 0 ≤ branch_box_5768.lower j ∧ 0 ≤ branch_box_5768.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5768, Box.profileLo, Box.profileHi, box_5768]
theorem leaf_5768_BranchSafe : CertificateConsequences.BranchSafe branch_box_5768 := by
  left; refine ⟨branch_box_5768_nonnegative, ?_⟩
  intro z hz; exact leaf_5768_sound hz

theorem leaf_5769_ok : checkAt 527 1000 box_5769 cert_5769 = true := by
  have h := List.all_eq_true.mp batch_115_10_ok accepted_5769 (by simp [batch_115_10_values])
  exact h
theorem leaf_5769_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5769.profileLo box_5769.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5769_ok
theorem branch_box_5769_nonnegative : ∀ j, 0 ≤ branch_box_5769.lower j ∧ 0 ≤ branch_box_5769.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5769, Box.profileLo, Box.profileHi, box_5769]
theorem leaf_5769_BranchSafe : CertificateConsequences.BranchSafe branch_box_5769 := by
  left; refine ⟨branch_box_5769_nonnegative, ?_⟩
  intro z hz; exact leaf_5769_sound hz

theorem leaf_5770_ok : checkAt 527 1000 box_5770 cert_5770 = true := by
  have h := List.all_eq_true.mp batch_115_11_ok accepted_5770 (by simp [batch_115_11_values])
  exact h
theorem leaf_5770_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5770.profileLo box_5770.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5770_ok
theorem branch_box_5770_nonnegative : ∀ j, 0 ≤ branch_box_5770.lower j ∧ 0 ≤ branch_box_5770.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5770, Box.profileLo, Box.profileHi, box_5770]
theorem leaf_5770_BranchSafe : CertificateConsequences.BranchSafe branch_box_5770 := by
  left; refine ⟨branch_box_5770_nonnegative, ?_⟩
  intro z hz; exact leaf_5770_sound hz

theorem leaf_5773_ok : checkAt 527 1000 box_5773 cert_5773 = true := by
  have h := List.all_eq_true.mp batch_115_12_ok accepted_5773 (by simp [batch_115_12_values])
  exact h
theorem leaf_5773_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5773.profileLo box_5773.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5773_ok
theorem branch_box_5773_nonnegative : ∀ j, 0 ≤ branch_box_5773.lower j ∧ 0 ≤ branch_box_5773.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5773, Box.profileLo, Box.profileHi, box_5773]
theorem leaf_5773_BranchSafe : CertificateConsequences.BranchSafe branch_box_5773 := by
  left; refine ⟨branch_box_5773_nonnegative, ?_⟩
  intro z hz; exact leaf_5773_sound hz

theorem leaf_5774_ok : checkAt 527 1000 box_5774 cert_5774 = true := by
  have h := List.all_eq_true.mp batch_115_13_ok accepted_5774 (by simp [batch_115_13_values])
  exact h
theorem leaf_5774_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5774.profileLo box_5774.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5774_ok
theorem branch_box_5774_nonnegative : ∀ j, 0 ≤ branch_box_5774.lower j ∧ 0 ≤ branch_box_5774.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5774, Box.profileLo, Box.profileHi, box_5774]
theorem leaf_5774_BranchSafe : CertificateConsequences.BranchSafe branch_box_5774 := by
  left; refine ⟨branch_box_5774_nonnegative, ?_⟩
  intro z hz; exact leaf_5774_sound hz

theorem leaf_5775_ok : checkAt 527 1000 box_5775 cert_5775 = true := by
  have h := List.all_eq_true.mp batch_115_14_ok accepted_5775 (by simp [batch_115_14_values])
  exact h
theorem leaf_5775_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5775.profileLo box_5775.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5775_ok
theorem branch_box_5775_nonnegative : ∀ j, 0 ≤ branch_box_5775.lower j ∧ 0 ≤ branch_box_5775.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5775, Box.profileLo, Box.profileHi, box_5775]
theorem leaf_5775_BranchSafe : CertificateConsequences.BranchSafe branch_box_5775 := by
  left; refine ⟨branch_box_5775_nonnegative, ?_⟩
  intro z hz; exact leaf_5775_sound hz

theorem leaf_5776_ok : checkAt 527 1000 box_5776 cert_5776 = true := by
  have h := List.all_eq_true.mp batch_115_15_ok accepted_5776 (by simp [batch_115_15_values])
  exact h
theorem leaf_5776_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5776.profileLo box_5776.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5776_ok
theorem branch_box_5776_nonnegative : ∀ j, 0 ≤ branch_box_5776.lower j ∧ 0 ≤ branch_box_5776.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5776, Box.profileLo, Box.profileHi, box_5776]
theorem leaf_5776_BranchSafe : CertificateConsequences.BranchSafe branch_box_5776 := by
  left; refine ⟨branch_box_5776_nonnegative, ?_⟩
  intro z hz; exact leaf_5776_sound hz

theorem leaf_5783_ok : checkAt 527 1000 box_5783 cert_5783 = true := by
  have h := List.all_eq_true.mp batch_115_16_ok accepted_5783 (by simp [batch_115_16_values])
  exact h
theorem leaf_5783_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5783.profileLo box_5783.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5783_ok
theorem branch_box_5783_nonnegative : ∀ j, 0 ≤ branch_box_5783.lower j ∧ 0 ≤ branch_box_5783.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5783, Box.profileLo, Box.profileHi, box_5783]
theorem leaf_5783_BranchSafe : CertificateConsequences.BranchSafe branch_box_5783 := by
  left; refine ⟨branch_box_5783_nonnegative, ?_⟩
  intro z hz; exact leaf_5783_sound hz

theorem leaf_5784_ok : checkAt 527 1000 box_5784 cert_5784 = true := by
  have h := List.all_eq_true.mp batch_115_17_ok accepted_5784 (by simp [batch_115_17_values])
  exact h
theorem leaf_5784_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5784.profileLo box_5784.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5784_ok
theorem branch_box_5784_nonnegative : ∀ j, 0 ≤ branch_box_5784.lower j ∧ 0 ≤ branch_box_5784.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5784, Box.profileLo, Box.profileHi, box_5784]
theorem leaf_5784_BranchSafe : CertificateConsequences.BranchSafe branch_box_5784 := by
  left; refine ⟨branch_box_5784_nonnegative, ?_⟩
  intro z hz; exact leaf_5784_sound hz

theorem leaf_5786_ok : checkAt 527 1000 box_5786 cert_5786 = true := by
  have h := List.all_eq_true.mp batch_115_18_ok accepted_5786 (by simp [batch_115_18_values])
  exact h
theorem leaf_5786_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5786.profileLo box_5786.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5786_ok
theorem branch_box_5786_nonnegative : ∀ j, 0 ≤ branch_box_5786.lower j ∧ 0 ≤ branch_box_5786.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5786, Box.profileLo, Box.profileHi, box_5786]
theorem leaf_5786_BranchSafe : CertificateConsequences.BranchSafe branch_box_5786 := by
  left; refine ⟨branch_box_5786_nonnegative, ?_⟩
  intro z hz; exact leaf_5786_sound hz

theorem leaf_5787_ok : checkAt 527 1000 box_5787 cert_5787 = true := by
  have h := List.all_eq_true.mp batch_115_19_ok accepted_5787 (by simp [batch_115_19_values])
  exact h
theorem leaf_5787_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5787.profileLo box_5787.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5787_ok
theorem branch_box_5787_nonnegative : ∀ j, 0 ≤ branch_box_5787.lower j ∧ 0 ≤ branch_box_5787.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5787, Box.profileLo, Box.profileHi, box_5787]
theorem leaf_5787_BranchSafe : CertificateConsequences.BranchSafe branch_box_5787 := by
  left; refine ⟨branch_box_5787_nonnegative, ?_⟩
  intro z hz; exact leaf_5787_sound hz

theorem leaf_5788_ok : checkAt 527 1000 box_5788 cert_5788 = true := by
  have h := List.all_eq_true.mp batch_115_20_ok accepted_5788 (by simp [batch_115_20_values])
  exact h
theorem leaf_5788_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5788.profileLo box_5788.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5788_ok
theorem branch_box_5788_nonnegative : ∀ j, 0 ≤ branch_box_5788.lower j ∧ 0 ≤ branch_box_5788.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5788, Box.profileLo, Box.profileHi, box_5788]
theorem leaf_5788_BranchSafe : CertificateConsequences.BranchSafe branch_box_5788 := by
  left; refine ⟨branch_box_5788_nonnegative, ?_⟩
  intro z hz; exact leaf_5788_sound hz

theorem leaf_5795_ok : checkAt 527 1000 box_5795 cert_5795 = true := by
  have h := List.all_eq_true.mp batch_115_21_ok accepted_5795 (by simp [batch_115_21_values])
  exact h
theorem leaf_5795_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5795.profileLo box_5795.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5795_ok
theorem branch_box_5795_nonnegative : ∀ j, 0 ≤ branch_box_5795.lower j ∧ 0 ≤ branch_box_5795.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5795, Box.profileLo, Box.profileHi, box_5795]
theorem leaf_5795_BranchSafe : CertificateConsequences.BranchSafe branch_box_5795 := by
  left; refine ⟨branch_box_5795_nonnegative, ?_⟩
  intro z hz; exact leaf_5795_sound hz

theorem leaf_5796_ok : checkAt 527 1000 box_5796 cert_5796 = true := by
  have h := List.all_eq_true.mp batch_115_22_ok accepted_5796 (by simp [batch_115_22_values])
  exact h
theorem leaf_5796_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5796.profileLo box_5796.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5796_ok
theorem branch_box_5796_nonnegative : ∀ j, 0 ≤ branch_box_5796.lower j ∧ 0 ≤ branch_box_5796.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5796, Box.profileLo, Box.profileHi, box_5796]
theorem leaf_5796_BranchSafe : CertificateConsequences.BranchSafe branch_box_5796 := by
  left; refine ⟨branch_box_5796_nonnegative, ?_⟩
  intro z hz; exact leaf_5796_sound hz

theorem leaf_5797_ok : checkAt 527 1000 box_5797 cert_5797 = true := by
  have h := List.all_eq_true.mp batch_115_23_ok accepted_5797 (by simp [batch_115_23_values])
  exact h
theorem leaf_5797_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5797.profileLo box_5797.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5797_ok
theorem branch_box_5797_nonnegative : ∀ j, 0 ≤ branch_box_5797.lower j ∧ 0 ≤ branch_box_5797.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5797, Box.profileLo, Box.profileHi, box_5797]
theorem leaf_5797_BranchSafe : CertificateConsequences.BranchSafe branch_box_5797 := by
  left; refine ⟨branch_box_5797_nonnegative, ?_⟩
  intro z hz; exact leaf_5797_sound hz

theorem leaf_5798_ok : checkAt 527 1000 box_5798 cert_5798 = true := by
  have h := List.all_eq_true.mp batch_115_24_ok accepted_5798 (by simp [batch_115_24_values])
  exact h
theorem leaf_5798_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5798.profileLo box_5798.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5798_ok
theorem branch_box_5798_nonnegative : ∀ j, 0 ≤ branch_box_5798.lower j ∧ 0 ≤ branch_box_5798.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5798, Box.profileLo, Box.profileHi, box_5798]
theorem leaf_5798_BranchSafe : CertificateConsequences.BranchSafe branch_box_5798 := by
  left; refine ⟨branch_box_5798_nonnegative, ?_⟩
  intro z hz; exact leaf_5798_sound hz

theorem leaf_5799_ok : checkAt 527 1000 box_5799 cert_5799 = true := by
  have h := List.all_eq_true.mp batch_115_25_ok accepted_5799 (by simp [batch_115_25_values])
  exact h
theorem leaf_5799_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5799.profileLo box_5799.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5799_ok
theorem branch_box_5799_nonnegative : ∀ j, 0 ≤ branch_box_5799.lower j ∧ 0 ≤ branch_box_5799.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5799, Box.profileLo, Box.profileHi, box_5799]
theorem leaf_5799_BranchSafe : CertificateConsequences.BranchSafe branch_box_5799 := by
  left; refine ⟨branch_box_5799_nonnegative, ?_⟩
  intro z hz; exact leaf_5799_sound hz

#print axioms batch_115_00_ok
#print axioms leaf_5750_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
