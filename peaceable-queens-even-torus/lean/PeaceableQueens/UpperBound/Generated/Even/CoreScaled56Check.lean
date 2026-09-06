import PeaceableQueens.UpperBound.Generated.Even.CoreScaled56Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_56_00_values : List Bool := [accepted_2803]
theorem batch_56_00_ok : batch_56_00_values.all id = true := by decide

def batch_56_01_values : List Bool := [accepted_2805]
theorem batch_56_01_ok : batch_56_01_values.all id = true := by decide

def batch_56_02_values : List Bool := [accepted_2808]
theorem batch_56_02_ok : batch_56_02_values.all id = true := by decide

def batch_56_03_values : List Bool := [accepted_2809]
theorem batch_56_03_ok : batch_56_03_values.all id = true := by decide

def batch_56_04_values : List Bool := [accepted_2811]
theorem batch_56_04_ok : batch_56_04_values.all id = true := by decide

def batch_56_05_values : List Bool := [accepted_2813]
theorem batch_56_05_ok : batch_56_05_values.all id = true := by decide

def batch_56_06_values : List Bool := [accepted_2818]
theorem batch_56_06_ok : batch_56_06_values.all id = true := by decide

def batch_56_07_values : List Bool := [accepted_2826]
theorem batch_56_07_ok : batch_56_07_values.all id = true := by decide

def batch_56_08_values : List Bool := [accepted_2828]
theorem batch_56_08_ok : batch_56_08_values.all id = true := by decide

def batch_56_09_values : List Bool := [accepted_2832]
theorem batch_56_09_ok : batch_56_09_values.all id = true := by decide

def batch_56_10_values : List Bool := [accepted_2840]
theorem batch_56_10_ok : batch_56_10_values.all id = true := by decide

def batch_56_11_values : List Bool := [accepted_2842]
theorem batch_56_11_ok : batch_56_11_values.all id = true := by decide

def batch_56_12_values : List Bool := [accepted_2846]
theorem batch_56_12_ok : batch_56_12_values.all id = true := by decide

theorem leaf_2803_ok : checkAt 527 1000 box_2803 cert_2803 = true := by
  have h := List.all_eq_true.mp batch_56_00_ok accepted_2803 (by simp [batch_56_00_values])
  exact h
theorem leaf_2803_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2803.profileLo box_2803.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2803_ok
theorem branch_box_2803_nonnegative : ∀ j, 0 ≤ branch_box_2803.lower j ∧ 0 ≤ branch_box_2803.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2803, Box.profileLo, Box.profileHi, box_2803]
theorem leaf_2803_BranchSafe : CertificateConsequences.BranchSafe branch_box_2803 := by
  left; refine ⟨branch_box_2803_nonnegative, ?_⟩
  intro z hz; exact leaf_2803_sound hz

theorem leaf_2805_ok : checkAt 527 1000 box_2805 cert_2805 = true := by
  have h := List.all_eq_true.mp batch_56_01_ok accepted_2805 (by simp [batch_56_01_values])
  exact h
theorem leaf_2805_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2805.profileLo box_2805.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2805_ok
theorem branch_box_2805_nonnegative : ∀ j, 0 ≤ branch_box_2805.lower j ∧ 0 ≤ branch_box_2805.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2805, Box.profileLo, Box.profileHi, box_2805]
theorem leaf_2805_BranchSafe : CertificateConsequences.BranchSafe branch_box_2805 := by
  left; refine ⟨branch_box_2805_nonnegative, ?_⟩
  intro z hz; exact leaf_2805_sound hz

theorem leaf_2808_ok : checkAt 527 1000 box_2808 cert_2808 = true := by
  have h := List.all_eq_true.mp batch_56_02_ok accepted_2808 (by simp [batch_56_02_values])
  exact h
theorem leaf_2808_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2808.profileLo box_2808.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2808_ok
theorem branch_box_2808_nonnegative : ∀ j, 0 ≤ branch_box_2808.lower j ∧ 0 ≤ branch_box_2808.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2808, Box.profileLo, Box.profileHi, box_2808]
theorem leaf_2808_BranchSafe : CertificateConsequences.BranchSafe branch_box_2808 := by
  left; refine ⟨branch_box_2808_nonnegative, ?_⟩
  intro z hz; exact leaf_2808_sound hz

theorem leaf_2809_ok : checkAt 527 1000 box_2809 cert_2809 = true := by
  have h := List.all_eq_true.mp batch_56_03_ok accepted_2809 (by simp [batch_56_03_values])
  exact h
theorem leaf_2809_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2809.profileLo box_2809.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2809_ok
theorem branch_box_2809_nonnegative : ∀ j, 0 ≤ branch_box_2809.lower j ∧ 0 ≤ branch_box_2809.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2809, Box.profileLo, Box.profileHi, box_2809]
theorem leaf_2809_BranchSafe : CertificateConsequences.BranchSafe branch_box_2809 := by
  left; refine ⟨branch_box_2809_nonnegative, ?_⟩
  intro z hz; exact leaf_2809_sound hz

theorem leaf_2811_ok : checkAt 527 1000 box_2811 cert_2811 = true := by
  have h := List.all_eq_true.mp batch_56_04_ok accepted_2811 (by simp [batch_56_04_values])
  exact h
theorem leaf_2811_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2811.profileLo box_2811.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2811_ok
theorem branch_box_2811_nonnegative : ∀ j, 0 ≤ branch_box_2811.lower j ∧ 0 ≤ branch_box_2811.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2811, Box.profileLo, Box.profileHi, box_2811]
theorem leaf_2811_BranchSafe : CertificateConsequences.BranchSafe branch_box_2811 := by
  left; refine ⟨branch_box_2811_nonnegative, ?_⟩
  intro z hz; exact leaf_2811_sound hz

theorem leaf_2813_ok : checkAt 527 1000 box_2813 cert_2813 = true := by
  have h := List.all_eq_true.mp batch_56_05_ok accepted_2813 (by simp [batch_56_05_values])
  exact h
theorem leaf_2813_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2813.profileLo box_2813.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2813_ok
theorem branch_box_2813_nonnegative : ∀ j, 0 ≤ branch_box_2813.lower j ∧ 0 ≤ branch_box_2813.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2813, Box.profileLo, Box.profileHi, box_2813]
theorem leaf_2813_BranchSafe : CertificateConsequences.BranchSafe branch_box_2813 := by
  left; refine ⟨branch_box_2813_nonnegative, ?_⟩
  intro z hz; exact leaf_2813_sound hz

theorem leaf_2818_ok : checkAt 527 1000 box_2818 cert_2818 = true := by
  have h := List.all_eq_true.mp batch_56_06_ok accepted_2818 (by simp [batch_56_06_values])
  exact h
theorem leaf_2818_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2818.profileLo box_2818.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2818_ok
theorem branch_box_2818_nonnegative : ∀ j, 0 ≤ branch_box_2818.lower j ∧ 0 ≤ branch_box_2818.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2818, Box.profileLo, Box.profileHi, box_2818]
theorem leaf_2818_BranchSafe : CertificateConsequences.BranchSafe branch_box_2818 := by
  left; refine ⟨branch_box_2818_nonnegative, ?_⟩
  intro z hz; exact leaf_2818_sound hz

theorem leaf_2826_ok : checkAt 527 1000 box_2826 cert_2826 = true := by
  have h := List.all_eq_true.mp batch_56_07_ok accepted_2826 (by simp [batch_56_07_values])
  exact h
theorem leaf_2826_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2826.profileLo box_2826.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2826_ok
theorem branch_box_2826_nonnegative : ∀ j, 0 ≤ branch_box_2826.lower j ∧ 0 ≤ branch_box_2826.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2826, Box.profileLo, Box.profileHi, box_2826]
theorem leaf_2826_BranchSafe : CertificateConsequences.BranchSafe branch_box_2826 := by
  left; refine ⟨branch_box_2826_nonnegative, ?_⟩
  intro z hz; exact leaf_2826_sound hz

theorem leaf_2828_ok : checkAt 527 1000 box_2828 cert_2828 = true := by
  have h := List.all_eq_true.mp batch_56_08_ok accepted_2828 (by simp [batch_56_08_values])
  exact h
theorem leaf_2828_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2828.profileLo box_2828.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2828_ok
theorem branch_box_2828_nonnegative : ∀ j, 0 ≤ branch_box_2828.lower j ∧ 0 ≤ branch_box_2828.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2828, Box.profileLo, Box.profileHi, box_2828]
theorem leaf_2828_BranchSafe : CertificateConsequences.BranchSafe branch_box_2828 := by
  left; refine ⟨branch_box_2828_nonnegative, ?_⟩
  intro z hz; exact leaf_2828_sound hz

theorem leaf_2832_ok : checkAt 527 1000 box_2832 cert_2832 = true := by
  have h := List.all_eq_true.mp batch_56_09_ok accepted_2832 (by simp [batch_56_09_values])
  exact h
theorem leaf_2832_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2832.profileLo box_2832.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2832_ok
theorem branch_box_2832_nonnegative : ∀ j, 0 ≤ branch_box_2832.lower j ∧ 0 ≤ branch_box_2832.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2832, Box.profileLo, Box.profileHi, box_2832]
theorem leaf_2832_BranchSafe : CertificateConsequences.BranchSafe branch_box_2832 := by
  left; refine ⟨branch_box_2832_nonnegative, ?_⟩
  intro z hz; exact leaf_2832_sound hz

theorem leaf_2840_ok : checkAt 527 1000 box_2840 cert_2840 = true := by
  have h := List.all_eq_true.mp batch_56_10_ok accepted_2840 (by simp [batch_56_10_values])
  exact h
theorem leaf_2840_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2840.profileLo box_2840.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2840_ok
theorem branch_box_2840_nonnegative : ∀ j, 0 ≤ branch_box_2840.lower j ∧ 0 ≤ branch_box_2840.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2840, Box.profileLo, Box.profileHi, box_2840]
theorem leaf_2840_BranchSafe : CertificateConsequences.BranchSafe branch_box_2840 := by
  left; refine ⟨branch_box_2840_nonnegative, ?_⟩
  intro z hz; exact leaf_2840_sound hz

theorem leaf_2842_ok : checkAt 527 1000 box_2842 cert_2842 = true := by
  have h := List.all_eq_true.mp batch_56_11_ok accepted_2842 (by simp [batch_56_11_values])
  exact h
theorem leaf_2842_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2842.profileLo box_2842.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2842_ok
theorem branch_box_2842_nonnegative : ∀ j, 0 ≤ branch_box_2842.lower j ∧ 0 ≤ branch_box_2842.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2842, Box.profileLo, Box.profileHi, box_2842]
theorem leaf_2842_BranchSafe : CertificateConsequences.BranchSafe branch_box_2842 := by
  left; refine ⟨branch_box_2842_nonnegative, ?_⟩
  intro z hz; exact leaf_2842_sound hz

theorem leaf_2846_ok : checkAt 527 1000 box_2846 cert_2846 = true := by
  have h := List.all_eq_true.mp batch_56_12_ok accepted_2846 (by simp [batch_56_12_values])
  exact h
theorem leaf_2846_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2846.profileLo box_2846.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2846_ok
theorem branch_box_2846_nonnegative : ∀ j, 0 ≤ branch_box_2846.lower j ∧ 0 ≤ branch_box_2846.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2846, Box.profileLo, Box.profileHi, box_2846]
theorem leaf_2846_BranchSafe : CertificateConsequences.BranchSafe branch_box_2846 := by
  left; refine ⟨branch_box_2846_nonnegative, ?_⟩
  intro z hz; exact leaf_2846_sound hz

#print axioms batch_56_00_ok
#print axioms leaf_2803_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
