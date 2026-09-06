import PeaceableQueens.UpperBound.Generated.Even.CoreScaled53Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_53_00_values : List Bool := [accepted_2651]
theorem batch_53_00_ok : batch_53_00_values.all id = true := by decide

def batch_53_01_values : List Bool := [accepted_2655]
theorem batch_53_01_ok : batch_53_01_values.all id = true := by decide

def batch_53_02_values : List Bool := [accepted_2657]
theorem batch_53_02_ok : batch_53_02_values.all id = true := by decide

def batch_53_03_values : List Bool := [accepted_2660]
theorem batch_53_03_ok : batch_53_03_values.all id = true := by decide

def batch_53_04_values : List Bool := [accepted_2661]
theorem batch_53_04_ok : batch_53_04_values.all id = true := by decide

def batch_53_05_values : List Bool := [accepted_2663]
theorem batch_53_05_ok : batch_53_05_values.all id = true := by decide

def batch_53_06_values : List Bool := [accepted_2665]
theorem batch_53_06_ok : batch_53_06_values.all id = true := by decide

def batch_53_07_values : List Bool := [accepted_2670]
theorem batch_53_07_ok : batch_53_07_values.all id = true := by decide

def batch_53_08_values : List Bool := [accepted_2672]
theorem batch_53_08_ok : batch_53_08_values.all id = true := by decide

def batch_53_09_values : List Bool := [accepted_2675]
theorem batch_53_09_ok : batch_53_09_values.all id = true := by decide

def batch_53_10_values : List Bool := [accepted_2679]
theorem batch_53_10_ok : batch_53_10_values.all id = true := by decide

def batch_53_11_values : List Bool := [accepted_2681]
theorem batch_53_11_ok : batch_53_11_values.all id = true := by decide

def batch_53_12_values : List Bool := [accepted_2684]
theorem batch_53_12_ok : batch_53_12_values.all id = true := by decide

def batch_53_13_values : List Bool := [accepted_2685]
theorem batch_53_13_ok : batch_53_13_values.all id = true := by decide

def batch_53_14_values : List Bool := [accepted_2687]
theorem batch_53_14_ok : batch_53_14_values.all id = true := by decide

def batch_53_15_values : List Bool := [accepted_2689]
theorem batch_53_15_ok : batch_53_15_values.all id = true := by decide

def batch_53_16_values : List Bool := [accepted_2694]
theorem batch_53_16_ok : batch_53_16_values.all id = true := by decide

theorem leaf_2651_ok : checkAt 527 1000 box_2651 cert_2651 = true := by
  have h := List.all_eq_true.mp batch_53_00_ok accepted_2651 (by simp [batch_53_00_values])
  exact h
theorem leaf_2651_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2651.profileLo box_2651.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2651_ok
theorem branch_box_2651_nonnegative : ∀ j, 0 ≤ branch_box_2651.lower j ∧ 0 ≤ branch_box_2651.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2651, Box.profileLo, Box.profileHi, box_2651]
theorem leaf_2651_BranchSafe : CertificateConsequences.BranchSafe branch_box_2651 := by
  left; refine ⟨branch_box_2651_nonnegative, ?_⟩
  intro z hz; exact leaf_2651_sound hz

theorem leaf_2655_ok : checkAt 527 1000 box_2655 cert_2655 = true := by
  have h := List.all_eq_true.mp batch_53_01_ok accepted_2655 (by simp [batch_53_01_values])
  exact h
theorem leaf_2655_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2655.profileLo box_2655.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2655_ok
theorem branch_box_2655_nonnegative : ∀ j, 0 ≤ branch_box_2655.lower j ∧ 0 ≤ branch_box_2655.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2655, Box.profileLo, Box.profileHi, box_2655]
theorem leaf_2655_BranchSafe : CertificateConsequences.BranchSafe branch_box_2655 := by
  left; refine ⟨branch_box_2655_nonnegative, ?_⟩
  intro z hz; exact leaf_2655_sound hz

theorem leaf_2657_ok : checkAt 527 1000 box_2657 cert_2657 = true := by
  have h := List.all_eq_true.mp batch_53_02_ok accepted_2657 (by simp [batch_53_02_values])
  exact h
theorem leaf_2657_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2657.profileLo box_2657.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2657_ok
theorem branch_box_2657_nonnegative : ∀ j, 0 ≤ branch_box_2657.lower j ∧ 0 ≤ branch_box_2657.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2657, Box.profileLo, Box.profileHi, box_2657]
theorem leaf_2657_BranchSafe : CertificateConsequences.BranchSafe branch_box_2657 := by
  left; refine ⟨branch_box_2657_nonnegative, ?_⟩
  intro z hz; exact leaf_2657_sound hz

theorem leaf_2660_ok : checkAt 527 1000 box_2660 cert_2660 = true := by
  have h := List.all_eq_true.mp batch_53_03_ok accepted_2660 (by simp [batch_53_03_values])
  exact h
theorem leaf_2660_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2660.profileLo box_2660.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2660_ok
theorem branch_box_2660_nonnegative : ∀ j, 0 ≤ branch_box_2660.lower j ∧ 0 ≤ branch_box_2660.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2660, Box.profileLo, Box.profileHi, box_2660]
theorem leaf_2660_BranchSafe : CertificateConsequences.BranchSafe branch_box_2660 := by
  left; refine ⟨branch_box_2660_nonnegative, ?_⟩
  intro z hz; exact leaf_2660_sound hz

theorem leaf_2661_ok : checkAt 527 1000 box_2661 cert_2661 = true := by
  have h := List.all_eq_true.mp batch_53_04_ok accepted_2661 (by simp [batch_53_04_values])
  exact h
theorem leaf_2661_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2661.profileLo box_2661.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2661_ok
theorem branch_box_2661_nonnegative : ∀ j, 0 ≤ branch_box_2661.lower j ∧ 0 ≤ branch_box_2661.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2661, Box.profileLo, Box.profileHi, box_2661]
theorem leaf_2661_BranchSafe : CertificateConsequences.BranchSafe branch_box_2661 := by
  left; refine ⟨branch_box_2661_nonnegative, ?_⟩
  intro z hz; exact leaf_2661_sound hz

theorem leaf_2663_ok : checkAt 527 1000 box_2663 cert_2663 = true := by
  have h := List.all_eq_true.mp batch_53_05_ok accepted_2663 (by simp [batch_53_05_values])
  exact h
theorem leaf_2663_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2663.profileLo box_2663.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2663_ok
theorem branch_box_2663_nonnegative : ∀ j, 0 ≤ branch_box_2663.lower j ∧ 0 ≤ branch_box_2663.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2663, Box.profileLo, Box.profileHi, box_2663]
theorem leaf_2663_BranchSafe : CertificateConsequences.BranchSafe branch_box_2663 := by
  left; refine ⟨branch_box_2663_nonnegative, ?_⟩
  intro z hz; exact leaf_2663_sound hz

theorem leaf_2665_ok : checkAt 527 1000 box_2665 cert_2665 = true := by
  have h := List.all_eq_true.mp batch_53_06_ok accepted_2665 (by simp [batch_53_06_values])
  exact h
theorem leaf_2665_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2665.profileLo box_2665.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2665_ok
theorem branch_box_2665_nonnegative : ∀ j, 0 ≤ branch_box_2665.lower j ∧ 0 ≤ branch_box_2665.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2665, Box.profileLo, Box.profileHi, box_2665]
theorem leaf_2665_BranchSafe : CertificateConsequences.BranchSafe branch_box_2665 := by
  left; refine ⟨branch_box_2665_nonnegative, ?_⟩
  intro z hz; exact leaf_2665_sound hz

theorem leaf_2670_ok : checkAt 527 1000 box_2670 cert_2670 = true := by
  have h := List.all_eq_true.mp batch_53_07_ok accepted_2670 (by simp [batch_53_07_values])
  exact h
theorem leaf_2670_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2670.profileLo box_2670.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2670_ok
theorem branch_box_2670_nonnegative : ∀ j, 0 ≤ branch_box_2670.lower j ∧ 0 ≤ branch_box_2670.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2670, Box.profileLo, Box.profileHi, box_2670]
theorem leaf_2670_BranchSafe : CertificateConsequences.BranchSafe branch_box_2670 := by
  left; refine ⟨branch_box_2670_nonnegative, ?_⟩
  intro z hz; exact leaf_2670_sound hz

theorem leaf_2672_ok : checkAt 527 1000 box_2672 cert_2672 = true := by
  have h := List.all_eq_true.mp batch_53_08_ok accepted_2672 (by simp [batch_53_08_values])
  exact h
theorem leaf_2672_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2672.profileLo box_2672.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2672_ok
theorem branch_box_2672_nonnegative : ∀ j, 0 ≤ branch_box_2672.lower j ∧ 0 ≤ branch_box_2672.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2672, Box.profileLo, Box.profileHi, box_2672]
theorem leaf_2672_BranchSafe : CertificateConsequences.BranchSafe branch_box_2672 := by
  left; refine ⟨branch_box_2672_nonnegative, ?_⟩
  intro z hz; exact leaf_2672_sound hz

theorem leaf_2675_ok : checkAt 527 1000 box_2675 cert_2675 = true := by
  have h := List.all_eq_true.mp batch_53_09_ok accepted_2675 (by simp [batch_53_09_values])
  exact h
theorem leaf_2675_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2675.profileLo box_2675.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2675_ok
theorem branch_box_2675_nonnegative : ∀ j, 0 ≤ branch_box_2675.lower j ∧ 0 ≤ branch_box_2675.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2675, Box.profileLo, Box.profileHi, box_2675]
theorem leaf_2675_BranchSafe : CertificateConsequences.BranchSafe branch_box_2675 := by
  left; refine ⟨branch_box_2675_nonnegative, ?_⟩
  intro z hz; exact leaf_2675_sound hz

theorem leaf_2679_ok : checkAt 527 1000 box_2679 cert_2679 = true := by
  have h := List.all_eq_true.mp batch_53_10_ok accepted_2679 (by simp [batch_53_10_values])
  exact h
theorem leaf_2679_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2679.profileLo box_2679.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2679_ok
theorem branch_box_2679_nonnegative : ∀ j, 0 ≤ branch_box_2679.lower j ∧ 0 ≤ branch_box_2679.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2679, Box.profileLo, Box.profileHi, box_2679]
theorem leaf_2679_BranchSafe : CertificateConsequences.BranchSafe branch_box_2679 := by
  left; refine ⟨branch_box_2679_nonnegative, ?_⟩
  intro z hz; exact leaf_2679_sound hz

theorem leaf_2681_ok : checkAt 527 1000 box_2681 cert_2681 = true := by
  have h := List.all_eq_true.mp batch_53_11_ok accepted_2681 (by simp [batch_53_11_values])
  exact h
theorem leaf_2681_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2681.profileLo box_2681.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2681_ok
theorem branch_box_2681_nonnegative : ∀ j, 0 ≤ branch_box_2681.lower j ∧ 0 ≤ branch_box_2681.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2681, Box.profileLo, Box.profileHi, box_2681]
theorem leaf_2681_BranchSafe : CertificateConsequences.BranchSafe branch_box_2681 := by
  left; refine ⟨branch_box_2681_nonnegative, ?_⟩
  intro z hz; exact leaf_2681_sound hz

theorem leaf_2684_ok : checkAt 527 1000 box_2684 cert_2684 = true := by
  have h := List.all_eq_true.mp batch_53_12_ok accepted_2684 (by simp [batch_53_12_values])
  exact h
theorem leaf_2684_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2684.profileLo box_2684.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2684_ok
theorem branch_box_2684_nonnegative : ∀ j, 0 ≤ branch_box_2684.lower j ∧ 0 ≤ branch_box_2684.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2684, Box.profileLo, Box.profileHi, box_2684]
theorem leaf_2684_BranchSafe : CertificateConsequences.BranchSafe branch_box_2684 := by
  left; refine ⟨branch_box_2684_nonnegative, ?_⟩
  intro z hz; exact leaf_2684_sound hz

theorem leaf_2685_ok : checkAt 527 1000 box_2685 cert_2685 = true := by
  have h := List.all_eq_true.mp batch_53_13_ok accepted_2685 (by simp [batch_53_13_values])
  exact h
theorem leaf_2685_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2685.profileLo box_2685.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2685_ok
theorem branch_box_2685_nonnegative : ∀ j, 0 ≤ branch_box_2685.lower j ∧ 0 ≤ branch_box_2685.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2685, Box.profileLo, Box.profileHi, box_2685]
theorem leaf_2685_BranchSafe : CertificateConsequences.BranchSafe branch_box_2685 := by
  left; refine ⟨branch_box_2685_nonnegative, ?_⟩
  intro z hz; exact leaf_2685_sound hz

theorem leaf_2687_ok : checkAt 527 1000 box_2687 cert_2687 = true := by
  have h := List.all_eq_true.mp batch_53_14_ok accepted_2687 (by simp [batch_53_14_values])
  exact h
theorem leaf_2687_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2687.profileLo box_2687.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2687_ok
theorem branch_box_2687_nonnegative : ∀ j, 0 ≤ branch_box_2687.lower j ∧ 0 ≤ branch_box_2687.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2687, Box.profileLo, Box.profileHi, box_2687]
theorem leaf_2687_BranchSafe : CertificateConsequences.BranchSafe branch_box_2687 := by
  left; refine ⟨branch_box_2687_nonnegative, ?_⟩
  intro z hz; exact leaf_2687_sound hz

theorem leaf_2689_ok : checkAt 527 1000 box_2689 cert_2689 = true := by
  have h := List.all_eq_true.mp batch_53_15_ok accepted_2689 (by simp [batch_53_15_values])
  exact h
theorem leaf_2689_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2689.profileLo box_2689.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2689_ok
theorem branch_box_2689_nonnegative : ∀ j, 0 ≤ branch_box_2689.lower j ∧ 0 ≤ branch_box_2689.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2689, Box.profileLo, Box.profileHi, box_2689]
theorem leaf_2689_BranchSafe : CertificateConsequences.BranchSafe branch_box_2689 := by
  left; refine ⟨branch_box_2689_nonnegative, ?_⟩
  intro z hz; exact leaf_2689_sound hz

theorem leaf_2694_ok : checkAt 527 1000 box_2694 cert_2694 = true := by
  have h := List.all_eq_true.mp batch_53_16_ok accepted_2694 (by simp [batch_53_16_values])
  exact h
theorem leaf_2694_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2694.profileLo box_2694.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2694_ok
theorem branch_box_2694_nonnegative : ∀ j, 0 ≤ branch_box_2694.lower j ∧ 0 ≤ branch_box_2694.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2694, Box.profileLo, Box.profileHi, box_2694]
theorem leaf_2694_BranchSafe : CertificateConsequences.BranchSafe branch_box_2694 := by
  left; refine ⟨branch_box_2694_nonnegative, ?_⟩
  intro z hz; exact leaf_2694_sound hz

#print axioms batch_53_00_ok
#print axioms leaf_2651_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
