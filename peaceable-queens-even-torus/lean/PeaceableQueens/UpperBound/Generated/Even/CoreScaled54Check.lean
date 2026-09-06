import PeaceableQueens.UpperBound.Generated.Even.CoreScaled54Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_54_00_values : List Bool := [accepted_2702]
theorem batch_54_00_ok : batch_54_00_values.all id = true := by decide

def batch_54_01_values : List Bool := [accepted_2704]
theorem batch_54_01_ok : batch_54_01_values.all id = true := by decide

def batch_54_02_values : List Bool := [accepted_2708]
theorem batch_54_02_ok : batch_54_02_values.all id = true := by decide

def batch_54_03_values : List Bool := [accepted_2716]
theorem batch_54_03_ok : batch_54_03_values.all id = true := by decide

def batch_54_04_values : List Bool := [accepted_2718]
theorem batch_54_04_ok : batch_54_04_values.all id = true := by decide

def batch_54_05_values : List Bool := [accepted_2722]
theorem batch_54_05_ok : batch_54_05_values.all id = true := by decide

def batch_54_06_values : List Bool := [accepted_2727]
theorem batch_54_06_ok : batch_54_06_values.all id = true := by decide

def batch_54_07_values : List Bool := [accepted_2734]
theorem batch_54_07_ok : batch_54_07_values.all id = true := by decide

def batch_54_08_values : List Bool := [accepted_2736]
theorem batch_54_08_ok : batch_54_08_values.all id = true := by decide

def batch_54_09_values : List Bool := [accepted_2738]
theorem batch_54_09_ok : batch_54_09_values.all id = true := by decide

def batch_54_10_values : List Bool := [accepted_2740]
theorem batch_54_10_ok : batch_54_10_values.all id = true := by decide

def batch_54_11_values : List Bool := [accepted_2742]
theorem batch_54_11_ok : batch_54_11_values.all id = true := by decide

def batch_54_12_values : List Bool := [accepted_2743]
theorem batch_54_12_ok : batch_54_12_values.all id = true := by decide

def batch_54_13_values : List Bool := [accepted_2746]
theorem batch_54_13_ok : batch_54_13_values.all id = true := by decide

def batch_54_14_values : List Bool := [accepted_2748]
theorem batch_54_14_ok : batch_54_14_values.all id = true := by decide

theorem leaf_2702_ok : checkAt 527 1000 box_2702 cert_2702 = true := by
  have h := List.all_eq_true.mp batch_54_00_ok accepted_2702 (by simp [batch_54_00_values])
  exact h
theorem leaf_2702_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2702.profileLo box_2702.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2702_ok
theorem branch_box_2702_nonnegative : ∀ j, 0 ≤ branch_box_2702.lower j ∧ 0 ≤ branch_box_2702.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2702, Box.profileLo, Box.profileHi, box_2702]
theorem leaf_2702_BranchSafe : CertificateConsequences.BranchSafe branch_box_2702 := by
  left; refine ⟨branch_box_2702_nonnegative, ?_⟩
  intro z hz; exact leaf_2702_sound hz

theorem leaf_2704_ok : checkAt 527 1000 box_2704 cert_2704 = true := by
  have h := List.all_eq_true.mp batch_54_01_ok accepted_2704 (by simp [batch_54_01_values])
  exact h
theorem leaf_2704_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2704.profileLo box_2704.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2704_ok
theorem branch_box_2704_nonnegative : ∀ j, 0 ≤ branch_box_2704.lower j ∧ 0 ≤ branch_box_2704.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2704, Box.profileLo, Box.profileHi, box_2704]
theorem leaf_2704_BranchSafe : CertificateConsequences.BranchSafe branch_box_2704 := by
  left; refine ⟨branch_box_2704_nonnegative, ?_⟩
  intro z hz; exact leaf_2704_sound hz

theorem leaf_2708_ok : checkAt 527 1000 box_2708 cert_2708 = true := by
  have h := List.all_eq_true.mp batch_54_02_ok accepted_2708 (by simp [batch_54_02_values])
  exact h
theorem leaf_2708_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2708.profileLo box_2708.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2708_ok
theorem branch_box_2708_nonnegative : ∀ j, 0 ≤ branch_box_2708.lower j ∧ 0 ≤ branch_box_2708.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2708, Box.profileLo, Box.profileHi, box_2708]
theorem leaf_2708_BranchSafe : CertificateConsequences.BranchSafe branch_box_2708 := by
  left; refine ⟨branch_box_2708_nonnegative, ?_⟩
  intro z hz; exact leaf_2708_sound hz

theorem leaf_2716_ok : checkAt 527 1000 box_2716 cert_2716 = true := by
  have h := List.all_eq_true.mp batch_54_03_ok accepted_2716 (by simp [batch_54_03_values])
  exact h
theorem leaf_2716_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2716.profileLo box_2716.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2716_ok
theorem branch_box_2716_nonnegative : ∀ j, 0 ≤ branch_box_2716.lower j ∧ 0 ≤ branch_box_2716.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2716, Box.profileLo, Box.profileHi, box_2716]
theorem leaf_2716_BranchSafe : CertificateConsequences.BranchSafe branch_box_2716 := by
  left; refine ⟨branch_box_2716_nonnegative, ?_⟩
  intro z hz; exact leaf_2716_sound hz

theorem leaf_2718_ok : checkAt 527 1000 box_2718 cert_2718 = true := by
  have h := List.all_eq_true.mp batch_54_04_ok accepted_2718 (by simp [batch_54_04_values])
  exact h
theorem leaf_2718_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2718.profileLo box_2718.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2718_ok
theorem branch_box_2718_nonnegative : ∀ j, 0 ≤ branch_box_2718.lower j ∧ 0 ≤ branch_box_2718.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2718, Box.profileLo, Box.profileHi, box_2718]
theorem leaf_2718_BranchSafe : CertificateConsequences.BranchSafe branch_box_2718 := by
  left; refine ⟨branch_box_2718_nonnegative, ?_⟩
  intro z hz; exact leaf_2718_sound hz

theorem leaf_2722_ok : checkAt 527 1000 box_2722 cert_2722 = true := by
  have h := List.all_eq_true.mp batch_54_05_ok accepted_2722 (by simp [batch_54_05_values])
  exact h
theorem leaf_2722_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2722.profileLo box_2722.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2722_ok
theorem branch_box_2722_nonnegative : ∀ j, 0 ≤ branch_box_2722.lower j ∧ 0 ≤ branch_box_2722.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2722, Box.profileLo, Box.profileHi, box_2722]
theorem leaf_2722_BranchSafe : CertificateConsequences.BranchSafe branch_box_2722 := by
  left; refine ⟨branch_box_2722_nonnegative, ?_⟩
  intro z hz; exact leaf_2722_sound hz

theorem leaf_2727_ok : checkAt 527 1000 box_2727 cert_2727 = true := by
  have h := List.all_eq_true.mp batch_54_06_ok accepted_2727 (by simp [batch_54_06_values])
  exact h
theorem leaf_2727_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2727.profileLo box_2727.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2727_ok
theorem branch_box_2727_nonnegative : ∀ j, 0 ≤ branch_box_2727.lower j ∧ 0 ≤ branch_box_2727.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2727, Box.profileLo, Box.profileHi, box_2727]
theorem leaf_2727_BranchSafe : CertificateConsequences.BranchSafe branch_box_2727 := by
  left; refine ⟨branch_box_2727_nonnegative, ?_⟩
  intro z hz; exact leaf_2727_sound hz

theorem leaf_2734_ok : checkAt 527 1000 box_2734 cert_2734 = true := by
  have h := List.all_eq_true.mp batch_54_07_ok accepted_2734 (by simp [batch_54_07_values])
  exact h
theorem leaf_2734_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2734.profileLo box_2734.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2734_ok
theorem branch_box_2734_nonnegative : ∀ j, 0 ≤ branch_box_2734.lower j ∧ 0 ≤ branch_box_2734.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2734, Box.profileLo, Box.profileHi, box_2734]
theorem leaf_2734_BranchSafe : CertificateConsequences.BranchSafe branch_box_2734 := by
  left; refine ⟨branch_box_2734_nonnegative, ?_⟩
  intro z hz; exact leaf_2734_sound hz

theorem leaf_2736_ok : checkAt 527 1000 box_2736 cert_2736 = true := by
  have h := List.all_eq_true.mp batch_54_08_ok accepted_2736 (by simp [batch_54_08_values])
  exact h
theorem leaf_2736_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2736.profileLo box_2736.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2736_ok
theorem branch_box_2736_nonnegative : ∀ j, 0 ≤ branch_box_2736.lower j ∧ 0 ≤ branch_box_2736.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2736, Box.profileLo, Box.profileHi, box_2736]
theorem leaf_2736_BranchSafe : CertificateConsequences.BranchSafe branch_box_2736 := by
  left; refine ⟨branch_box_2736_nonnegative, ?_⟩
  intro z hz; exact leaf_2736_sound hz

theorem leaf_2738_ok : checkAt 527 1000 box_2738 cert_2738 = true := by
  have h := List.all_eq_true.mp batch_54_09_ok accepted_2738 (by simp [batch_54_09_values])
  exact h
theorem leaf_2738_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2738.profileLo box_2738.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2738_ok
theorem branch_box_2738_nonnegative : ∀ j, 0 ≤ branch_box_2738.lower j ∧ 0 ≤ branch_box_2738.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2738, Box.profileLo, Box.profileHi, box_2738]
theorem leaf_2738_BranchSafe : CertificateConsequences.BranchSafe branch_box_2738 := by
  left; refine ⟨branch_box_2738_nonnegative, ?_⟩
  intro z hz; exact leaf_2738_sound hz

theorem leaf_2740_ok : checkAt 527 1000 box_2740 cert_2740 = true := by
  have h := List.all_eq_true.mp batch_54_10_ok accepted_2740 (by simp [batch_54_10_values])
  exact h
theorem leaf_2740_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2740.profileLo box_2740.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2740_ok
theorem branch_box_2740_nonnegative : ∀ j, 0 ≤ branch_box_2740.lower j ∧ 0 ≤ branch_box_2740.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2740, Box.profileLo, Box.profileHi, box_2740]
theorem leaf_2740_BranchSafe : CertificateConsequences.BranchSafe branch_box_2740 := by
  left; refine ⟨branch_box_2740_nonnegative, ?_⟩
  intro z hz; exact leaf_2740_sound hz

theorem leaf_2742_ok : checkAt 527 1000 box_2742 cert_2742 = true := by
  have h := List.all_eq_true.mp batch_54_11_ok accepted_2742 (by simp [batch_54_11_values])
  exact h
theorem leaf_2742_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2742.profileLo box_2742.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2742_ok
theorem branch_box_2742_nonnegative : ∀ j, 0 ≤ branch_box_2742.lower j ∧ 0 ≤ branch_box_2742.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2742, Box.profileLo, Box.profileHi, box_2742]
theorem leaf_2742_BranchSafe : CertificateConsequences.BranchSafe branch_box_2742 := by
  left; refine ⟨branch_box_2742_nonnegative, ?_⟩
  intro z hz; exact leaf_2742_sound hz

theorem leaf_2743_ok : checkAt 527 1000 box_2743 cert_2743 = true := by
  have h := List.all_eq_true.mp batch_54_12_ok accepted_2743 (by simp [batch_54_12_values])
  exact h
theorem leaf_2743_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2743.profileLo box_2743.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2743_ok
theorem branch_box_2743_nonnegative : ∀ j, 0 ≤ branch_box_2743.lower j ∧ 0 ≤ branch_box_2743.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2743, Box.profileLo, Box.profileHi, box_2743]
theorem leaf_2743_BranchSafe : CertificateConsequences.BranchSafe branch_box_2743 := by
  left; refine ⟨branch_box_2743_nonnegative, ?_⟩
  intro z hz; exact leaf_2743_sound hz

theorem leaf_2746_ok : checkAt 527 1000 box_2746 cert_2746 = true := by
  have h := List.all_eq_true.mp batch_54_13_ok accepted_2746 (by simp [batch_54_13_values])
  exact h
theorem leaf_2746_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2746.profileLo box_2746.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2746_ok
theorem branch_box_2746_nonnegative : ∀ j, 0 ≤ branch_box_2746.lower j ∧ 0 ≤ branch_box_2746.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2746, Box.profileLo, Box.profileHi, box_2746]
theorem leaf_2746_BranchSafe : CertificateConsequences.BranchSafe branch_box_2746 := by
  left; refine ⟨branch_box_2746_nonnegative, ?_⟩
  intro z hz; exact leaf_2746_sound hz

theorem leaf_2748_ok : checkAt 527 1000 box_2748 cert_2748 = true := by
  have h := List.all_eq_true.mp batch_54_14_ok accepted_2748 (by simp [batch_54_14_values])
  exact h
theorem leaf_2748_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2748.profileLo box_2748.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2748_ok
theorem branch_box_2748_nonnegative : ∀ j, 0 ≤ branch_box_2748.lower j ∧ 0 ≤ branch_box_2748.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2748, Box.profileLo, Box.profileHi, box_2748]
theorem leaf_2748_BranchSafe : CertificateConsequences.BranchSafe branch_box_2748 := by
  left; refine ⟨branch_box_2748_nonnegative, ?_⟩
  intro z hz; exact leaf_2748_sound hz

#print axioms batch_54_00_ok
#print axioms leaf_2702_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
