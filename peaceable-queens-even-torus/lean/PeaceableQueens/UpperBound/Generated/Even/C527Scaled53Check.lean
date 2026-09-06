import PeaceableQueens.UpperBound.Generated.Even.C527Scaled53Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_53_00_values : List Bool := [accepted_2650]
theorem batch_53_00_ok : batch_53_00_values.all id = true := by decide

def batch_53_01_values : List Bool := [accepted_2653]
theorem batch_53_01_ok : batch_53_01_values.all id = true := by decide

def batch_53_02_values : List Bool := [accepted_2655]
theorem batch_53_02_ok : batch_53_02_values.all id = true := by decide

def batch_53_03_values : List Bool := [accepted_2656]
theorem batch_53_03_ok : batch_53_03_values.all id = true := by decide

def batch_53_04_values : List Bool := [accepted_2657]
theorem batch_53_04_ok : batch_53_04_values.all id = true := by decide

def batch_53_05_values : List Bool := [accepted_2658]
theorem batch_53_05_ok : batch_53_05_values.all id = true := by decide

def batch_53_06_values : List Bool := [accepted_2661]
theorem batch_53_06_ok : batch_53_06_values.all id = true := by decide

def batch_53_07_values : List Bool := [accepted_2662]
theorem batch_53_07_ok : batch_53_07_values.all id = true := by decide

def batch_53_08_values : List Bool := [accepted_2663]
theorem batch_53_08_ok : batch_53_08_values.all id = true := by decide

def batch_53_09_values : List Bool := [accepted_2665]
theorem batch_53_09_ok : batch_53_09_values.all id = true := by decide

def batch_53_10_values : List Bool := [accepted_2666]
theorem batch_53_10_ok : batch_53_10_values.all id = true := by decide

def batch_53_11_values : List Bool := [accepted_2673]
theorem batch_53_11_ok : batch_53_11_values.all id = true := by decide

def batch_53_12_values : List Bool := [accepted_2680]
theorem batch_53_12_ok : batch_53_12_values.all id = true := by decide

def batch_53_13_values : List Bool := [accepted_2681]
theorem batch_53_13_ok : batch_53_13_values.all id = true := by decide

def batch_53_14_values : List Bool := [accepted_2682]
theorem batch_53_14_ok : batch_53_14_values.all id = true := by decide

def batch_53_15_values : List Bool := [accepted_2685]
theorem batch_53_15_ok : batch_53_15_values.all id = true := by decide

def batch_53_16_values : List Bool := [accepted_2686]
theorem batch_53_16_ok : batch_53_16_values.all id = true := by decide

def batch_53_17_values : List Bool := [accepted_2690]
theorem batch_53_17_ok : batch_53_17_values.all id = true := by decide

def batch_53_18_values : List Bool := [accepted_2691]
theorem batch_53_18_ok : batch_53_18_values.all id = true := by decide

def batch_53_19_values : List Bool := [accepted_2692]
theorem batch_53_19_ok : batch_53_19_values.all id = true := by decide

def batch_53_20_values : List Bool := [accepted_2693]
theorem batch_53_20_ok : batch_53_20_values.all id = true := by decide

def batch_53_21_values : List Bool := [accepted_2694]
theorem batch_53_21_ok : batch_53_21_values.all id = true := by decide

def batch_53_22_values : List Bool := [accepted_2699]
theorem batch_53_22_ok : batch_53_22_values.all id = true := by decide

theorem leaf_2650_ok : checkAt 527 1000 box_2650 cert_2650 = true := by
  have h := List.all_eq_true.mp batch_53_00_ok accepted_2650 (by simp [batch_53_00_values])
  exact h
theorem leaf_2650_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2650.profileLo box_2650.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2650_ok
theorem branch_box_2650_nonnegative : ∀ j, 0 ≤ branch_box_2650.lower j ∧ 0 ≤ branch_box_2650.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2650, Box.profileLo, Box.profileHi, box_2650]
theorem leaf_2650_BranchSafe : CertificateConsequences.BranchSafe branch_box_2650 := by
  left; refine ⟨branch_box_2650_nonnegative, ?_⟩
  intro z hz; exact leaf_2650_sound hz

theorem leaf_2653_ok : checkAt 527 1000 box_2653 cert_2653 = true := by
  have h := List.all_eq_true.mp batch_53_01_ok accepted_2653 (by simp [batch_53_01_values])
  exact h
theorem leaf_2653_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2653.profileLo box_2653.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2653_ok
theorem branch_box_2653_nonnegative : ∀ j, 0 ≤ branch_box_2653.lower j ∧ 0 ≤ branch_box_2653.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2653, Box.profileLo, Box.profileHi, box_2653]
theorem leaf_2653_BranchSafe : CertificateConsequences.BranchSafe branch_box_2653 := by
  left; refine ⟨branch_box_2653_nonnegative, ?_⟩
  intro z hz; exact leaf_2653_sound hz

theorem leaf_2655_ok : checkAt 527 1000 box_2655 cert_2655 = true := by
  have h := List.all_eq_true.mp batch_53_02_ok accepted_2655 (by simp [batch_53_02_values])
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

theorem leaf_2656_ok : checkAt 527 1000 box_2656 cert_2656 = true := by
  have h := List.all_eq_true.mp batch_53_03_ok accepted_2656 (by simp [batch_53_03_values])
  exact h
theorem leaf_2656_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2656.profileLo box_2656.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2656_ok
theorem branch_box_2656_nonnegative : ∀ j, 0 ≤ branch_box_2656.lower j ∧ 0 ≤ branch_box_2656.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2656, Box.profileLo, Box.profileHi, box_2656]
theorem leaf_2656_BranchSafe : CertificateConsequences.BranchSafe branch_box_2656 := by
  left; refine ⟨branch_box_2656_nonnegative, ?_⟩
  intro z hz; exact leaf_2656_sound hz

theorem leaf_2657_ok : checkAt 527 1000 box_2657 cert_2657 = true := by
  have h := List.all_eq_true.mp batch_53_04_ok accepted_2657 (by simp [batch_53_04_values])
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

theorem leaf_2658_ok : checkAt 527 1000 box_2658 cert_2658 = true := by
  have h := List.all_eq_true.mp batch_53_05_ok accepted_2658 (by simp [batch_53_05_values])
  exact h
theorem leaf_2658_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2658.profileLo box_2658.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2658_ok
theorem branch_box_2658_nonnegative : ∀ j, 0 ≤ branch_box_2658.lower j ∧ 0 ≤ branch_box_2658.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2658, Box.profileLo, Box.profileHi, box_2658]
theorem leaf_2658_BranchSafe : CertificateConsequences.BranchSafe branch_box_2658 := by
  left; refine ⟨branch_box_2658_nonnegative, ?_⟩
  intro z hz; exact leaf_2658_sound hz

theorem leaf_2661_ok : checkAt 527 1000 box_2661 cert_2661 = true := by
  have h := List.all_eq_true.mp batch_53_06_ok accepted_2661 (by simp [batch_53_06_values])
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

theorem leaf_2662_ok : checkAt 527 1000 box_2662 cert_2662 = true := by
  have h := List.all_eq_true.mp batch_53_07_ok accepted_2662 (by simp [batch_53_07_values])
  exact h
theorem leaf_2662_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2662.profileLo box_2662.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2662_ok
theorem branch_box_2662_nonnegative : ∀ j, 0 ≤ branch_box_2662.lower j ∧ 0 ≤ branch_box_2662.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2662, Box.profileLo, Box.profileHi, box_2662]
theorem leaf_2662_BranchSafe : CertificateConsequences.BranchSafe branch_box_2662 := by
  left; refine ⟨branch_box_2662_nonnegative, ?_⟩
  intro z hz; exact leaf_2662_sound hz

theorem leaf_2663_ok : checkAt 527 1000 box_2663 cert_2663 = true := by
  have h := List.all_eq_true.mp batch_53_08_ok accepted_2663 (by simp [batch_53_08_values])
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
  have h := List.all_eq_true.mp batch_53_09_ok accepted_2665 (by simp [batch_53_09_values])
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

theorem leaf_2666_ok : checkAt 527 1000 box_2666 cert_2666 = true := by
  have h := List.all_eq_true.mp batch_53_10_ok accepted_2666 (by simp [batch_53_10_values])
  exact h
theorem leaf_2666_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2666.profileLo box_2666.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2666_ok
theorem branch_box_2666_nonnegative : ∀ j, 0 ≤ branch_box_2666.lower j ∧ 0 ≤ branch_box_2666.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2666, Box.profileLo, Box.profileHi, box_2666]
theorem leaf_2666_BranchSafe : CertificateConsequences.BranchSafe branch_box_2666 := by
  left; refine ⟨branch_box_2666_nonnegative, ?_⟩
  intro z hz; exact leaf_2666_sound hz

theorem leaf_2673_ok : checkAt 527 1000 box_2673 cert_2673 = true := by
  have h := List.all_eq_true.mp batch_53_11_ok accepted_2673 (by simp [batch_53_11_values])
  exact h
theorem leaf_2673_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2673.profileLo box_2673.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2673_ok
theorem branch_box_2673_nonnegative : ∀ j, 0 ≤ branch_box_2673.lower j ∧ 0 ≤ branch_box_2673.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2673, Box.profileLo, Box.profileHi, box_2673]
theorem leaf_2673_BranchSafe : CertificateConsequences.BranchSafe branch_box_2673 := by
  left; refine ⟨branch_box_2673_nonnegative, ?_⟩
  intro z hz; exact leaf_2673_sound hz

theorem leaf_2680_ok : checkAt 527 1000 box_2680 cert_2680 = true := by
  have h := List.all_eq_true.mp batch_53_12_ok accepted_2680 (by simp [batch_53_12_values])
  exact h
theorem leaf_2680_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2680.profileLo box_2680.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2680_ok
theorem branch_box_2680_nonnegative : ∀ j, 0 ≤ branch_box_2680.lower j ∧ 0 ≤ branch_box_2680.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2680, Box.profileLo, Box.profileHi, box_2680]
theorem leaf_2680_BranchSafe : CertificateConsequences.BranchSafe branch_box_2680 := by
  left; refine ⟨branch_box_2680_nonnegative, ?_⟩
  intro z hz; exact leaf_2680_sound hz

theorem leaf_2681_ok : checkAt 527 1000 box_2681 cert_2681 = true := by
  have h := List.all_eq_true.mp batch_53_13_ok accepted_2681 (by simp [batch_53_13_values])
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

theorem leaf_2682_ok : checkAt 527 1000 box_2682 cert_2682 = true := by
  have h := List.all_eq_true.mp batch_53_14_ok accepted_2682 (by simp [batch_53_14_values])
  exact h
theorem leaf_2682_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2682.profileLo box_2682.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2682_ok
theorem branch_box_2682_nonnegative : ∀ j, 0 ≤ branch_box_2682.lower j ∧ 0 ≤ branch_box_2682.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2682, Box.profileLo, Box.profileHi, box_2682]
theorem leaf_2682_BranchSafe : CertificateConsequences.BranchSafe branch_box_2682 := by
  left; refine ⟨branch_box_2682_nonnegative, ?_⟩
  intro z hz; exact leaf_2682_sound hz

theorem leaf_2685_ok : checkAt 527 1000 box_2685 cert_2685 = true := by
  have h := List.all_eq_true.mp batch_53_15_ok accepted_2685 (by simp [batch_53_15_values])
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

theorem leaf_2686_ok : checkAt 527 1000 box_2686 cert_2686 = true := by
  have h := List.all_eq_true.mp batch_53_16_ok accepted_2686 (by simp [batch_53_16_values])
  exact h
theorem leaf_2686_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2686.profileLo box_2686.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2686_ok
theorem branch_box_2686_nonnegative : ∀ j, 0 ≤ branch_box_2686.lower j ∧ 0 ≤ branch_box_2686.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2686, Box.profileLo, Box.profileHi, box_2686]
theorem leaf_2686_BranchSafe : CertificateConsequences.BranchSafe branch_box_2686 := by
  left; refine ⟨branch_box_2686_nonnegative, ?_⟩
  intro z hz; exact leaf_2686_sound hz

theorem leaf_2690_ok : checkAt 527 1000 box_2690 cert_2690 = true := by
  have h := List.all_eq_true.mp batch_53_17_ok accepted_2690 (by simp [batch_53_17_values])
  exact h
theorem leaf_2690_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2690.profileLo box_2690.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2690_ok
theorem branch_box_2690_nonnegative : ∀ j, 0 ≤ branch_box_2690.lower j ∧ 0 ≤ branch_box_2690.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2690, Box.profileLo, Box.profileHi, box_2690]
theorem leaf_2690_BranchSafe : CertificateConsequences.BranchSafe branch_box_2690 := by
  left; refine ⟨branch_box_2690_nonnegative, ?_⟩
  intro z hz; exact leaf_2690_sound hz

theorem leaf_2691_ok : checkAt 527 1000 box_2691 cert_2691 = true := by
  have h := List.all_eq_true.mp batch_53_18_ok accepted_2691 (by simp [batch_53_18_values])
  exact h
theorem leaf_2691_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2691.profileLo box_2691.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2691_ok
theorem branch_box_2691_nonnegative : ∀ j, 0 ≤ branch_box_2691.lower j ∧ 0 ≤ branch_box_2691.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2691, Box.profileLo, Box.profileHi, box_2691]
theorem leaf_2691_BranchSafe : CertificateConsequences.BranchSafe branch_box_2691 := by
  left; refine ⟨branch_box_2691_nonnegative, ?_⟩
  intro z hz; exact leaf_2691_sound hz

theorem leaf_2692_ok : checkAt 527 1000 box_2692 cert_2692 = true := by
  have h := List.all_eq_true.mp batch_53_19_ok accepted_2692 (by simp [batch_53_19_values])
  exact h
theorem leaf_2692_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2692.profileLo box_2692.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2692_ok
theorem branch_box_2692_nonnegative : ∀ j, 0 ≤ branch_box_2692.lower j ∧ 0 ≤ branch_box_2692.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2692, Box.profileLo, Box.profileHi, box_2692]
theorem leaf_2692_BranchSafe : CertificateConsequences.BranchSafe branch_box_2692 := by
  left; refine ⟨branch_box_2692_nonnegative, ?_⟩
  intro z hz; exact leaf_2692_sound hz

theorem leaf_2693_ok : checkAt 527 1000 box_2693 cert_2693 = true := by
  have h := List.all_eq_true.mp batch_53_20_ok accepted_2693 (by simp [batch_53_20_values])
  exact h
theorem leaf_2693_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2693.profileLo box_2693.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2693_ok
theorem branch_box_2693_nonnegative : ∀ j, 0 ≤ branch_box_2693.lower j ∧ 0 ≤ branch_box_2693.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2693, Box.profileLo, Box.profileHi, box_2693]
theorem leaf_2693_BranchSafe : CertificateConsequences.BranchSafe branch_box_2693 := by
  left; refine ⟨branch_box_2693_nonnegative, ?_⟩
  intro z hz; exact leaf_2693_sound hz

theorem leaf_2694_ok : checkAt 527 1000 box_2694 cert_2694 = true := by
  have h := List.all_eq_true.mp batch_53_21_ok accepted_2694 (by simp [batch_53_21_values])
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

theorem leaf_2699_ok : checkAt 527 1000 box_2699 cert_2699 = true := by
  have h := List.all_eq_true.mp batch_53_22_ok accepted_2699 (by simp [batch_53_22_values])
  exact h
theorem leaf_2699_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2699.profileLo box_2699.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2699_ok
theorem branch_box_2699_nonnegative : ∀ j, 0 ≤ branch_box_2699.lower j ∧ 0 ≤ branch_box_2699.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2699, Box.profileLo, Box.profileHi, box_2699]
theorem leaf_2699_BranchSafe : CertificateConsequences.BranchSafe branch_box_2699 := by
  left; refine ⟨branch_box_2699_nonnegative, ?_⟩
  intro z hz; exact leaf_2699_sound hz

#print axioms batch_53_00_ok
#print axioms leaf_2650_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
