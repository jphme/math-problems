import PeaceableQueens.UpperBound.Generated.Even.CoreScaled52Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_52_00_values : List Bool := [accepted_2605]
theorem batch_52_00_ok : batch_52_00_values.all id = true := by decide

def batch_52_01_values : List Bool := [accepted_2607]
theorem batch_52_01_ok : batch_52_01_values.all id = true := by decide

def batch_52_02_values : List Bool := [accepted_2609]
theorem batch_52_02_ok : batch_52_02_values.all id = true := by decide

def batch_52_03_values : List Bool := [accepted_2611]
theorem batch_52_03_ok : batch_52_03_values.all id = true := by decide

def batch_52_04_values : List Bool := [accepted_2617]
theorem batch_52_04_ok : batch_52_04_values.all id = true := by decide

def batch_52_05_values : List Bool := [accepted_2619]
theorem batch_52_05_ok : batch_52_05_values.all id = true := by decide

def batch_52_06_values : List Bool := [accepted_2626]
theorem batch_52_06_ok : batch_52_06_values.all id = true := by decide

def batch_52_07_values : List Bool := [accepted_2628]
theorem batch_52_07_ok : batch_52_07_values.all id = true := by decide

def batch_52_08_values : List Bool := [accepted_2641]
theorem batch_52_08_ok : batch_52_08_values.all id = true := by decide

def batch_52_09_values : List Bool := [accepted_2643]
theorem batch_52_09_ok : batch_52_09_values.all id = true := by decide

def batch_52_10_values : List Bool := [accepted_2645]
theorem batch_52_10_ok : batch_52_10_values.all id = true := by decide

def batch_52_11_values : List Bool := [accepted_2647]
theorem batch_52_11_ok : batch_52_11_values.all id = true := by decide

theorem leaf_2605_ok : checkAt 527 1000 box_2605 cert_2605 = true := by
  have h := List.all_eq_true.mp batch_52_00_ok accepted_2605 (by simp [batch_52_00_values])
  exact h
theorem leaf_2605_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2605.profileLo box_2605.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2605_ok
theorem branch_box_2605_nonnegative : ∀ j, 0 ≤ branch_box_2605.lower j ∧ 0 ≤ branch_box_2605.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2605, Box.profileLo, Box.profileHi, box_2605]
theorem leaf_2605_BranchSafe : CertificateConsequences.BranchSafe branch_box_2605 := by
  left; refine ⟨branch_box_2605_nonnegative, ?_⟩
  intro z hz; exact leaf_2605_sound hz

theorem leaf_2607_ok : checkAt 527 1000 box_2607 cert_2607 = true := by
  have h := List.all_eq_true.mp batch_52_01_ok accepted_2607 (by simp [batch_52_01_values])
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

theorem leaf_2609_ok : checkAt 527 1000 box_2609 cert_2609 = true := by
  have h := List.all_eq_true.mp batch_52_02_ok accepted_2609 (by simp [batch_52_02_values])
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
  have h := List.all_eq_true.mp batch_52_03_ok accepted_2611 (by simp [batch_52_03_values])
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

theorem leaf_2617_ok : checkAt 527 1000 box_2617 cert_2617 = true := by
  have h := List.all_eq_true.mp batch_52_04_ok accepted_2617 (by simp [batch_52_04_values])
  exact h
theorem leaf_2617_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2617.profileLo box_2617.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2617_ok
theorem branch_box_2617_nonnegative : ∀ j, 0 ≤ branch_box_2617.lower j ∧ 0 ≤ branch_box_2617.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2617, Box.profileLo, Box.profileHi, box_2617]
theorem leaf_2617_BranchSafe : CertificateConsequences.BranchSafe branch_box_2617 := by
  left; refine ⟨branch_box_2617_nonnegative, ?_⟩
  intro z hz; exact leaf_2617_sound hz

theorem leaf_2619_ok : checkAt 527 1000 box_2619 cert_2619 = true := by
  have h := List.all_eq_true.mp batch_52_05_ok accepted_2619 (by simp [batch_52_05_values])
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

theorem leaf_2626_ok : checkAt 527 1000 box_2626 cert_2626 = true := by
  have h := List.all_eq_true.mp batch_52_06_ok accepted_2626 (by simp [batch_52_06_values])
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

theorem leaf_2628_ok : checkAt 527 1000 box_2628 cert_2628 = true := by
  have h := List.all_eq_true.mp batch_52_07_ok accepted_2628 (by simp [batch_52_07_values])
  exact h
theorem leaf_2628_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2628.profileLo box_2628.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2628_ok
theorem branch_box_2628_nonnegative : ∀ j, 0 ≤ branch_box_2628.lower j ∧ 0 ≤ branch_box_2628.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2628, Box.profileLo, Box.profileHi, box_2628]
theorem leaf_2628_BranchSafe : CertificateConsequences.BranchSafe branch_box_2628 := by
  left; refine ⟨branch_box_2628_nonnegative, ?_⟩
  intro z hz; exact leaf_2628_sound hz

theorem leaf_2641_ok : checkAt 527 1000 box_2641 cert_2641 = true := by
  have h := List.all_eq_true.mp batch_52_08_ok accepted_2641 (by simp [batch_52_08_values])
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

theorem leaf_2643_ok : checkAt 527 1000 box_2643 cert_2643 = true := by
  have h := List.all_eq_true.mp batch_52_09_ok accepted_2643 (by simp [batch_52_09_values])
  exact h
theorem leaf_2643_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2643.profileLo box_2643.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2643_ok
theorem branch_box_2643_nonnegative : ∀ j, 0 ≤ branch_box_2643.lower j ∧ 0 ≤ branch_box_2643.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2643, Box.profileLo, Box.profileHi, box_2643]
theorem leaf_2643_BranchSafe : CertificateConsequences.BranchSafe branch_box_2643 := by
  left; refine ⟨branch_box_2643_nonnegative, ?_⟩
  intro z hz; exact leaf_2643_sound hz

theorem leaf_2645_ok : checkAt 527 1000 box_2645 cert_2645 = true := by
  have h := List.all_eq_true.mp batch_52_10_ok accepted_2645 (by simp [batch_52_10_values])
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

theorem leaf_2647_ok : checkAt 527 1000 box_2647 cert_2647 = true := by
  have h := List.all_eq_true.mp batch_52_11_ok accepted_2647 (by simp [batch_52_11_values])
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

#print axioms batch_52_00_ok
#print axioms leaf_2605_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
