import PeaceableQueens.UpperBound.Generated.Even.C527Scaled52Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_52_00_values : List Bool := [accepted_2600]
theorem batch_52_00_ok : batch_52_00_values.all id = true := by decide

def batch_52_01_values : List Bool := [accepted_2601]
theorem batch_52_01_ok : batch_52_01_values.all id = true := by decide

def batch_52_02_values : List Bool := [accepted_2603]
theorem batch_52_02_ok : batch_52_02_values.all id = true := by decide

def batch_52_03_values : List Bool := [accepted_2604]
theorem batch_52_03_ok : batch_52_03_values.all id = true := by decide

def batch_52_04_values : List Bool := [accepted_2606]
theorem batch_52_04_ok : batch_52_04_values.all id = true := by decide

def batch_52_05_values : List Bool := [accepted_2607]
theorem batch_52_05_ok : batch_52_05_values.all id = true := by decide

def batch_52_06_values : List Bool := [accepted_2608]
theorem batch_52_06_ok : batch_52_06_values.all id = true := by decide

def batch_52_07_values : List Bool := [accepted_2609]
theorem batch_52_07_ok : batch_52_07_values.all id = true := by decide

def batch_52_08_values : List Bool := [accepted_2611]
theorem batch_52_08_ok : batch_52_08_values.all id = true := by decide

def batch_52_09_values : List Bool := [accepted_2612]
theorem batch_52_09_ok : batch_52_09_values.all id = true := by decide

def batch_52_10_values : List Bool := [accepted_2619]
theorem batch_52_10_ok : batch_52_10_values.all id = true := by decide

def batch_52_11_values : List Bool := [accepted_2620]
theorem batch_52_11_ok : batch_52_11_values.all id = true := by decide

def batch_52_12_values : List Bool := [accepted_2621]
theorem batch_52_12_ok : batch_52_12_values.all id = true := by decide

def batch_52_13_values : List Bool := [accepted_2623]
theorem batch_52_13_ok : batch_52_13_values.all id = true := by decide

def batch_52_14_values : List Bool := [accepted_2624]
theorem batch_52_14_ok : batch_52_14_values.all id = true := by decide

def batch_52_15_values : List Bool := [accepted_2625]
theorem batch_52_15_ok : batch_52_15_values.all id = true := by decide

def batch_52_16_values : List Bool := [accepted_2626]
theorem batch_52_16_ok : batch_52_16_values.all id = true := by decide

def batch_52_17_values : List Bool := [accepted_2627]
theorem batch_52_17_ok : batch_52_17_values.all id = true := by decide

def batch_52_18_values : List Bool := [accepted_2629]
theorem batch_52_18_ok : batch_52_18_values.all id = true := by decide

def batch_52_19_values : List Bool := [accepted_2631]
theorem batch_52_19_ok : batch_52_19_values.all id = true := by decide

def batch_52_20_values : List Bool := [accepted_2632]
theorem batch_52_20_ok : batch_52_20_values.all id = true := by decide

def batch_52_21_values : List Bool := [accepted_2641]
theorem batch_52_21_ok : batch_52_21_values.all id = true := by decide

def batch_52_22_values : List Bool := [accepted_2642]
theorem batch_52_22_ok : batch_52_22_values.all id = true := by decide

def batch_52_23_values : List Bool := [accepted_2645]
theorem batch_52_23_ok : batch_52_23_values.all id = true := by decide

def batch_52_24_values : List Bool := [accepted_2646]
theorem batch_52_24_ok : batch_52_24_values.all id = true := by decide

def batch_52_25_values : List Bool := [accepted_2647]
theorem batch_52_25_ok : batch_52_25_values.all id = true := by decide

def batch_52_26_values : List Bool := [accepted_2648]
theorem batch_52_26_ok : batch_52_26_values.all id = true := by decide

def batch_52_27_values : List Bool := [accepted_2649]
theorem batch_52_27_ok : batch_52_27_values.all id = true := by decide

theorem leaf_2600_ok : checkAt 527 1000 box_2600 cert_2600 = true := by
  have h := List.all_eq_true.mp batch_52_00_ok accepted_2600 (by simp [batch_52_00_values])
  exact h
theorem leaf_2600_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2600.profileLo box_2600.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2600_ok
theorem branch_box_2600_nonnegative : ∀ j, 0 ≤ branch_box_2600.lower j ∧ 0 ≤ branch_box_2600.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2600, Box.profileLo, Box.profileHi, box_2600]
theorem leaf_2600_BranchSafe : CertificateConsequences.BranchSafe branch_box_2600 := by
  left; refine ⟨branch_box_2600_nonnegative, ?_⟩
  intro z hz; exact leaf_2600_sound hz

theorem leaf_2601_ok : checkAt 527 1000 box_2601 cert_2601 = true := by
  have h := List.all_eq_true.mp batch_52_01_ok accepted_2601 (by simp [batch_52_01_values])
  exact h
theorem leaf_2601_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2601.profileLo box_2601.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2601_ok
theorem branch_box_2601_nonnegative : ∀ j, 0 ≤ branch_box_2601.lower j ∧ 0 ≤ branch_box_2601.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2601, Box.profileLo, Box.profileHi, box_2601]
theorem leaf_2601_BranchSafe : CertificateConsequences.BranchSafe branch_box_2601 := by
  left; refine ⟨branch_box_2601_nonnegative, ?_⟩
  intro z hz; exact leaf_2601_sound hz

theorem leaf_2603_ok : checkAt 527 1000 box_2603 cert_2603 = true := by
  have h := List.all_eq_true.mp batch_52_02_ok accepted_2603 (by simp [batch_52_02_values])
  exact h
theorem leaf_2603_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2603.profileLo box_2603.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2603_ok
theorem branch_box_2603_nonnegative : ∀ j, 0 ≤ branch_box_2603.lower j ∧ 0 ≤ branch_box_2603.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2603, Box.profileLo, Box.profileHi, box_2603]
theorem leaf_2603_BranchSafe : CertificateConsequences.BranchSafe branch_box_2603 := by
  left; refine ⟨branch_box_2603_nonnegative, ?_⟩
  intro z hz; exact leaf_2603_sound hz

theorem leaf_2604_ok : checkAt 527 1000 box_2604 cert_2604 = true := by
  have h := List.all_eq_true.mp batch_52_03_ok accepted_2604 (by simp [batch_52_03_values])
  exact h
theorem leaf_2604_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2604.profileLo box_2604.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2604_ok
theorem branch_box_2604_nonnegative : ∀ j, 0 ≤ branch_box_2604.lower j ∧ 0 ≤ branch_box_2604.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2604, Box.profileLo, Box.profileHi, box_2604]
theorem leaf_2604_BranchSafe : CertificateConsequences.BranchSafe branch_box_2604 := by
  left; refine ⟨branch_box_2604_nonnegative, ?_⟩
  intro z hz; exact leaf_2604_sound hz

theorem leaf_2606_ok : checkAt 527 1000 box_2606 cert_2606 = true := by
  have h := List.all_eq_true.mp batch_52_04_ok accepted_2606 (by simp [batch_52_04_values])
  exact h
theorem leaf_2606_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2606.profileLo box_2606.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2606_ok
theorem branch_box_2606_nonnegative : ∀ j, 0 ≤ branch_box_2606.lower j ∧ 0 ≤ branch_box_2606.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2606, Box.profileLo, Box.profileHi, box_2606]
theorem leaf_2606_BranchSafe : CertificateConsequences.BranchSafe branch_box_2606 := by
  left; refine ⟨branch_box_2606_nonnegative, ?_⟩
  intro z hz; exact leaf_2606_sound hz

theorem leaf_2607_ok : checkAt 527 1000 box_2607 cert_2607 = true := by
  have h := List.all_eq_true.mp batch_52_05_ok accepted_2607 (by simp [batch_52_05_values])
  exact h
theorem leaf_2607_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2607.profileLo box_2607.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2607_ok
theorem branch_box_2607_nonnegative : ∀ j, 0 ≤ branch_box_2607.lower j ∧ 0 ≤ branch_box_2607.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2607, Box.profileLo, Box.profileHi, box_2607]
theorem leaf_2607_BranchSafe : CertificateConsequences.BranchSafe branch_box_2607 := by
  left; refine ⟨branch_box_2607_nonnegative, ?_⟩
  intro z hz; exact leaf_2607_sound hz

theorem leaf_2608_ok : checkAt 527 1000 box_2608 cert_2608 = true := by
  have h := List.all_eq_true.mp batch_52_06_ok accepted_2608 (by simp [batch_52_06_values])
  exact h
theorem leaf_2608_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2608.profileLo box_2608.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2608_ok
theorem branch_box_2608_nonnegative : ∀ j, 0 ≤ branch_box_2608.lower j ∧ 0 ≤ branch_box_2608.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2608, Box.profileLo, Box.profileHi, box_2608]
theorem leaf_2608_BranchSafe : CertificateConsequences.BranchSafe branch_box_2608 := by
  left; refine ⟨branch_box_2608_nonnegative, ?_⟩
  intro z hz; exact leaf_2608_sound hz

theorem leaf_2609_ok : checkAt 527 1000 box_2609 cert_2609 = true := by
  have h := List.all_eq_true.mp batch_52_07_ok accepted_2609 (by simp [batch_52_07_values])
  exact h
theorem leaf_2609_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2609.profileLo box_2609.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2609_ok
theorem branch_box_2609_nonnegative : ∀ j, 0 ≤ branch_box_2609.lower j ∧ 0 ≤ branch_box_2609.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2609, Box.profileLo, Box.profileHi, box_2609]
theorem leaf_2609_BranchSafe : CertificateConsequences.BranchSafe branch_box_2609 := by
  left; refine ⟨branch_box_2609_nonnegative, ?_⟩
  intro z hz; exact leaf_2609_sound hz

theorem leaf_2611_ok : checkAt 527 1000 box_2611 cert_2611 = true := by
  have h := List.all_eq_true.mp batch_52_08_ok accepted_2611 (by simp [batch_52_08_values])
  exact h
theorem leaf_2611_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2611.profileLo box_2611.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2611_ok
theorem branch_box_2611_nonnegative : ∀ j, 0 ≤ branch_box_2611.lower j ∧ 0 ≤ branch_box_2611.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2611, Box.profileLo, Box.profileHi, box_2611]
theorem leaf_2611_BranchSafe : CertificateConsequences.BranchSafe branch_box_2611 := by
  left; refine ⟨branch_box_2611_nonnegative, ?_⟩
  intro z hz; exact leaf_2611_sound hz

theorem leaf_2612_ok : checkAt 527 1000 box_2612 cert_2612 = true := by
  have h := List.all_eq_true.mp batch_52_09_ok accepted_2612 (by simp [batch_52_09_values])
  exact h
theorem leaf_2612_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2612.profileLo box_2612.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2612_ok
theorem branch_box_2612_nonnegative : ∀ j, 0 ≤ branch_box_2612.lower j ∧ 0 ≤ branch_box_2612.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2612, Box.profileLo, Box.profileHi, box_2612]
theorem leaf_2612_BranchSafe : CertificateConsequences.BranchSafe branch_box_2612 := by
  left; refine ⟨branch_box_2612_nonnegative, ?_⟩
  intro z hz; exact leaf_2612_sound hz

theorem leaf_2619_ok : checkAt 527 1000 box_2619 cert_2619 = true := by
  have h := List.all_eq_true.mp batch_52_10_ok accepted_2619 (by simp [batch_52_10_values])
  exact h
theorem leaf_2619_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2619.profileLo box_2619.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2619_ok
theorem branch_box_2619_nonnegative : ∀ j, 0 ≤ branch_box_2619.lower j ∧ 0 ≤ branch_box_2619.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2619, Box.profileLo, Box.profileHi, box_2619]
theorem leaf_2619_BranchSafe : CertificateConsequences.BranchSafe branch_box_2619 := by
  left; refine ⟨branch_box_2619_nonnegative, ?_⟩
  intro z hz; exact leaf_2619_sound hz

theorem leaf_2620_ok : checkAt 527 1000 box_2620 cert_2620 = true := by
  have h := List.all_eq_true.mp batch_52_11_ok accepted_2620 (by simp [batch_52_11_values])
  exact h
theorem leaf_2620_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2620.profileLo box_2620.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2620_ok
theorem branch_box_2620_nonnegative : ∀ j, 0 ≤ branch_box_2620.lower j ∧ 0 ≤ branch_box_2620.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2620, Box.profileLo, Box.profileHi, box_2620]
theorem leaf_2620_BranchSafe : CertificateConsequences.BranchSafe branch_box_2620 := by
  left; refine ⟨branch_box_2620_nonnegative, ?_⟩
  intro z hz; exact leaf_2620_sound hz

theorem leaf_2621_ok : checkAt 527 1000 box_2621 cert_2621 = true := by
  have h := List.all_eq_true.mp batch_52_12_ok accepted_2621 (by simp [batch_52_12_values])
  exact h
theorem leaf_2621_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2621.profileLo box_2621.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2621_ok
theorem branch_box_2621_nonnegative : ∀ j, 0 ≤ branch_box_2621.lower j ∧ 0 ≤ branch_box_2621.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2621, Box.profileLo, Box.profileHi, box_2621]
theorem leaf_2621_BranchSafe : CertificateConsequences.BranchSafe branch_box_2621 := by
  left; refine ⟨branch_box_2621_nonnegative, ?_⟩
  intro z hz; exact leaf_2621_sound hz

theorem leaf_2623_ok : checkAt 527 1000 box_2623 cert_2623 = true := by
  have h := List.all_eq_true.mp batch_52_13_ok accepted_2623 (by simp [batch_52_13_values])
  exact h
theorem leaf_2623_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2623.profileLo box_2623.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2623_ok
theorem branch_box_2623_nonnegative : ∀ j, 0 ≤ branch_box_2623.lower j ∧ 0 ≤ branch_box_2623.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2623, Box.profileLo, Box.profileHi, box_2623]
theorem leaf_2623_BranchSafe : CertificateConsequences.BranchSafe branch_box_2623 := by
  left; refine ⟨branch_box_2623_nonnegative, ?_⟩
  intro z hz; exact leaf_2623_sound hz

theorem leaf_2624_ok : checkAt 527 1000 box_2624 cert_2624 = true := by
  have h := List.all_eq_true.mp batch_52_14_ok accepted_2624 (by simp [batch_52_14_values])
  exact h
theorem leaf_2624_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2624.profileLo box_2624.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2624_ok
theorem branch_box_2624_nonnegative : ∀ j, 0 ≤ branch_box_2624.lower j ∧ 0 ≤ branch_box_2624.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2624, Box.profileLo, Box.profileHi, box_2624]
theorem leaf_2624_BranchSafe : CertificateConsequences.BranchSafe branch_box_2624 := by
  left; refine ⟨branch_box_2624_nonnegative, ?_⟩
  intro z hz; exact leaf_2624_sound hz

theorem leaf_2625_ok : checkAt 527 1000 box_2625 cert_2625 = true := by
  have h := List.all_eq_true.mp batch_52_15_ok accepted_2625 (by simp [batch_52_15_values])
  exact h
theorem leaf_2625_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2625.profileLo box_2625.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2625_ok
theorem branch_box_2625_nonnegative : ∀ j, 0 ≤ branch_box_2625.lower j ∧ 0 ≤ branch_box_2625.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2625, Box.profileLo, Box.profileHi, box_2625]
theorem leaf_2625_BranchSafe : CertificateConsequences.BranchSafe branch_box_2625 := by
  left; refine ⟨branch_box_2625_nonnegative, ?_⟩
  intro z hz; exact leaf_2625_sound hz

theorem leaf_2626_ok : checkAt 527 1000 box_2626 cert_2626 = true := by
  have h := List.all_eq_true.mp batch_52_16_ok accepted_2626 (by simp [batch_52_16_values])
  exact h
theorem leaf_2626_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2626.profileLo box_2626.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2626_ok
theorem branch_box_2626_nonnegative : ∀ j, 0 ≤ branch_box_2626.lower j ∧ 0 ≤ branch_box_2626.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2626, Box.profileLo, Box.profileHi, box_2626]
theorem leaf_2626_BranchSafe : CertificateConsequences.BranchSafe branch_box_2626 := by
  left; refine ⟨branch_box_2626_nonnegative, ?_⟩
  intro z hz; exact leaf_2626_sound hz

theorem leaf_2627_ok : checkAt 527 1000 box_2627 cert_2627 = true := by
  have h := List.all_eq_true.mp batch_52_17_ok accepted_2627 (by simp [batch_52_17_values])
  exact h
theorem leaf_2627_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2627.profileLo box_2627.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2627_ok
theorem branch_box_2627_nonnegative : ∀ j, 0 ≤ branch_box_2627.lower j ∧ 0 ≤ branch_box_2627.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2627, Box.profileLo, Box.profileHi, box_2627]
theorem leaf_2627_BranchSafe : CertificateConsequences.BranchSafe branch_box_2627 := by
  left; refine ⟨branch_box_2627_nonnegative, ?_⟩
  intro z hz; exact leaf_2627_sound hz

theorem leaf_2629_ok : checkAt 527 1000 box_2629 cert_2629 = true := by
  have h := List.all_eq_true.mp batch_52_18_ok accepted_2629 (by simp [batch_52_18_values])
  exact h
theorem leaf_2629_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2629.profileLo box_2629.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2629_ok
theorem branch_box_2629_nonnegative : ∀ j, 0 ≤ branch_box_2629.lower j ∧ 0 ≤ branch_box_2629.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2629, Box.profileLo, Box.profileHi, box_2629]
theorem leaf_2629_BranchSafe : CertificateConsequences.BranchSafe branch_box_2629 := by
  left; refine ⟨branch_box_2629_nonnegative, ?_⟩
  intro z hz; exact leaf_2629_sound hz

theorem leaf_2631_ok : checkAt 527 1000 box_2631 cert_2631 = true := by
  have h := List.all_eq_true.mp batch_52_19_ok accepted_2631 (by simp [batch_52_19_values])
  exact h
theorem leaf_2631_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2631.profileLo box_2631.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2631_ok
theorem branch_box_2631_nonnegative : ∀ j, 0 ≤ branch_box_2631.lower j ∧ 0 ≤ branch_box_2631.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2631, Box.profileLo, Box.profileHi, box_2631]
theorem leaf_2631_BranchSafe : CertificateConsequences.BranchSafe branch_box_2631 := by
  left; refine ⟨branch_box_2631_nonnegative, ?_⟩
  intro z hz; exact leaf_2631_sound hz

theorem leaf_2632_ok : checkAt 527 1000 box_2632 cert_2632 = true := by
  have h := List.all_eq_true.mp batch_52_20_ok accepted_2632 (by simp [batch_52_20_values])
  exact h
theorem leaf_2632_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2632.profileLo box_2632.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2632_ok
theorem branch_box_2632_nonnegative : ∀ j, 0 ≤ branch_box_2632.lower j ∧ 0 ≤ branch_box_2632.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2632, Box.profileLo, Box.profileHi, box_2632]
theorem leaf_2632_BranchSafe : CertificateConsequences.BranchSafe branch_box_2632 := by
  left; refine ⟨branch_box_2632_nonnegative, ?_⟩
  intro z hz; exact leaf_2632_sound hz

theorem leaf_2641_ok : checkAt 527 1000 box_2641 cert_2641 = true := by
  have h := List.all_eq_true.mp batch_52_21_ok accepted_2641 (by simp [batch_52_21_values])
  exact h
theorem leaf_2641_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2641.profileLo box_2641.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2641_ok
theorem branch_box_2641_nonnegative : ∀ j, 0 ≤ branch_box_2641.lower j ∧ 0 ≤ branch_box_2641.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2641, Box.profileLo, Box.profileHi, box_2641]
theorem leaf_2641_BranchSafe : CertificateConsequences.BranchSafe branch_box_2641 := by
  left; refine ⟨branch_box_2641_nonnegative, ?_⟩
  intro z hz; exact leaf_2641_sound hz

theorem leaf_2642_ok : checkAt 527 1000 box_2642 cert_2642 = true := by
  have h := List.all_eq_true.mp batch_52_22_ok accepted_2642 (by simp [batch_52_22_values])
  exact h
theorem leaf_2642_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2642.profileLo box_2642.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2642_ok
theorem branch_box_2642_nonnegative : ∀ j, 0 ≤ branch_box_2642.lower j ∧ 0 ≤ branch_box_2642.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2642, Box.profileLo, Box.profileHi, box_2642]
theorem leaf_2642_BranchSafe : CertificateConsequences.BranchSafe branch_box_2642 := by
  left; refine ⟨branch_box_2642_nonnegative, ?_⟩
  intro z hz; exact leaf_2642_sound hz

theorem leaf_2645_ok : checkAt 527 1000 box_2645 cert_2645 = true := by
  have h := List.all_eq_true.mp batch_52_23_ok accepted_2645 (by simp [batch_52_23_values])
  exact h
theorem leaf_2645_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2645.profileLo box_2645.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2645_ok
theorem branch_box_2645_nonnegative : ∀ j, 0 ≤ branch_box_2645.lower j ∧ 0 ≤ branch_box_2645.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2645, Box.profileLo, Box.profileHi, box_2645]
theorem leaf_2645_BranchSafe : CertificateConsequences.BranchSafe branch_box_2645 := by
  left; refine ⟨branch_box_2645_nonnegative, ?_⟩
  intro z hz; exact leaf_2645_sound hz

theorem leaf_2646_ok : checkAt 527 1000 box_2646 cert_2646 = true := by
  have h := List.all_eq_true.mp batch_52_24_ok accepted_2646 (by simp [batch_52_24_values])
  exact h
theorem leaf_2646_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2646.profileLo box_2646.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2646_ok
theorem branch_box_2646_nonnegative : ∀ j, 0 ≤ branch_box_2646.lower j ∧ 0 ≤ branch_box_2646.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2646, Box.profileLo, Box.profileHi, box_2646]
theorem leaf_2646_BranchSafe : CertificateConsequences.BranchSafe branch_box_2646 := by
  left; refine ⟨branch_box_2646_nonnegative, ?_⟩
  intro z hz; exact leaf_2646_sound hz

theorem leaf_2647_ok : checkAt 527 1000 box_2647 cert_2647 = true := by
  have h := List.all_eq_true.mp batch_52_25_ok accepted_2647 (by simp [batch_52_25_values])
  exact h
theorem leaf_2647_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2647.profileLo box_2647.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2647_ok
theorem branch_box_2647_nonnegative : ∀ j, 0 ≤ branch_box_2647.lower j ∧ 0 ≤ branch_box_2647.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2647, Box.profileLo, Box.profileHi, box_2647]
theorem leaf_2647_BranchSafe : CertificateConsequences.BranchSafe branch_box_2647 := by
  left; refine ⟨branch_box_2647_nonnegative, ?_⟩
  intro z hz; exact leaf_2647_sound hz

theorem leaf_2648_ok : checkAt 527 1000 box_2648 cert_2648 = true := by
  have h := List.all_eq_true.mp batch_52_26_ok accepted_2648 (by simp [batch_52_26_values])
  exact h
theorem leaf_2648_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2648.profileLo box_2648.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2648_ok
theorem branch_box_2648_nonnegative : ∀ j, 0 ≤ branch_box_2648.lower j ∧ 0 ≤ branch_box_2648.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2648, Box.profileLo, Box.profileHi, box_2648]
theorem leaf_2648_BranchSafe : CertificateConsequences.BranchSafe branch_box_2648 := by
  left; refine ⟨branch_box_2648_nonnegative, ?_⟩
  intro z hz; exact leaf_2648_sound hz

theorem leaf_2649_ok : checkAt 527 1000 box_2649 cert_2649 = true := by
  have h := List.all_eq_true.mp batch_52_27_ok accepted_2649 (by simp [batch_52_27_values])
  exact h
theorem leaf_2649_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2649.profileLo box_2649.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2649_ok
theorem branch_box_2649_nonnegative : ∀ j, 0 ≤ branch_box_2649.lower j ∧ 0 ≤ branch_box_2649.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2649, Box.profileLo, Box.profileHi, box_2649]
theorem leaf_2649_BranchSafe : CertificateConsequences.BranchSafe branch_box_2649 := by
  left; refine ⟨branch_box_2649_nonnegative, ?_⟩
  intro z hz; exact leaf_2649_sound hz

#print axioms batch_52_00_ok
#print axioms leaf_2600_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
