import PeaceableQueens.UpperBound.Generated.Even.CoreScaled51Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_51_00_values : List Bool := [accepted_2554]
theorem batch_51_00_ok : batch_51_00_values.all id = true := by decide

def batch_51_01_values : List Bool := [accepted_2556]
theorem batch_51_01_ok : batch_51_01_values.all id = true := by decide

def batch_51_02_values : List Bool := [accepted_2559]
theorem batch_51_02_ok : batch_51_02_values.all id = true := by decide

def batch_51_03_values : List Bool := [accepted_2563]
theorem batch_51_03_ok : batch_51_03_values.all id = true := by decide

def batch_51_04_values : List Bool := [accepted_2565]
theorem batch_51_04_ok : batch_51_04_values.all id = true := by decide

def batch_51_05_values : List Bool := [accepted_2568]
theorem batch_51_05_ok : batch_51_05_values.all id = true := by decide

def batch_51_06_values : List Bool := [accepted_2569]
theorem batch_51_06_ok : batch_51_06_values.all id = true := by decide

def batch_51_07_values : List Bool := [accepted_2571]
theorem batch_51_07_ok : batch_51_07_values.all id = true := by decide

def batch_51_08_values : List Bool := [accepted_2577]
theorem batch_51_08_ok : batch_51_08_values.all id = true := by decide

def batch_51_09_values : List Bool := [accepted_2579]
theorem batch_51_09_ok : batch_51_09_values.all id = true := by decide

def batch_51_10_values : List Bool := [accepted_2582]
theorem batch_51_10_ok : batch_51_10_values.all id = true := by decide

def batch_51_11_values : List Bool := [accepted_2583]
theorem batch_51_11_ok : batch_51_11_values.all id = true := by decide

def batch_51_12_values : List Bool := [accepted_2585]
theorem batch_51_12_ok : batch_51_12_values.all id = true := by decide

def batch_51_13_values : List Bool := [accepted_2590]
theorem batch_51_13_ok : batch_51_13_values.all id = true := by decide

def batch_51_14_values : List Bool := [accepted_2591]
theorem batch_51_14_ok : batch_51_14_values.all id = true := by decide

theorem leaf_2554_ok : checkAt 527 1000 box_2554 cert_2554 = true := by
  have h := List.all_eq_true.mp batch_51_00_ok accepted_2554 (by simp [batch_51_00_values])
  exact h
theorem leaf_2554_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2554.profileLo box_2554.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2554_ok
theorem branch_box_2554_nonnegative : ∀ j, 0 ≤ branch_box_2554.lower j ∧ 0 ≤ branch_box_2554.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2554, Box.profileLo, Box.profileHi, box_2554]
theorem leaf_2554_BranchSafe : CertificateConsequences.BranchSafe branch_box_2554 := by
  left; refine ⟨branch_box_2554_nonnegative, ?_⟩
  intro z hz; exact leaf_2554_sound hz

theorem leaf_2556_ok : checkAt 527 1000 box_2556 cert_2556 = true := by
  have h := List.all_eq_true.mp batch_51_01_ok accepted_2556 (by simp [batch_51_01_values])
  exact h
theorem leaf_2556_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2556.profileLo box_2556.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2556_ok
theorem branch_box_2556_nonnegative : ∀ j, 0 ≤ branch_box_2556.lower j ∧ 0 ≤ branch_box_2556.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2556, Box.profileLo, Box.profileHi, box_2556]
theorem leaf_2556_BranchSafe : CertificateConsequences.BranchSafe branch_box_2556 := by
  left; refine ⟨branch_box_2556_nonnegative, ?_⟩
  intro z hz; exact leaf_2556_sound hz

theorem leaf_2559_ok : checkAt 527 1000 box_2559 cert_2559 = true := by
  have h := List.all_eq_true.mp batch_51_02_ok accepted_2559 (by simp [batch_51_02_values])
  exact h
theorem leaf_2559_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2559.profileLo box_2559.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2559_ok
theorem branch_box_2559_nonnegative : ∀ j, 0 ≤ branch_box_2559.lower j ∧ 0 ≤ branch_box_2559.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2559, Box.profileLo, Box.profileHi, box_2559]
theorem leaf_2559_BranchSafe : CertificateConsequences.BranchSafe branch_box_2559 := by
  left; refine ⟨branch_box_2559_nonnegative, ?_⟩
  intro z hz; exact leaf_2559_sound hz

theorem leaf_2563_ok : checkAt 527 1000 box_2563 cert_2563 = true := by
  have h := List.all_eq_true.mp batch_51_03_ok accepted_2563 (by simp [batch_51_03_values])
  exact h
theorem leaf_2563_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2563.profileLo box_2563.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2563_ok
theorem branch_box_2563_nonnegative : ∀ j, 0 ≤ branch_box_2563.lower j ∧ 0 ≤ branch_box_2563.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2563, Box.profileLo, Box.profileHi, box_2563]
theorem leaf_2563_BranchSafe : CertificateConsequences.BranchSafe branch_box_2563 := by
  left; refine ⟨branch_box_2563_nonnegative, ?_⟩
  intro z hz; exact leaf_2563_sound hz

theorem leaf_2565_ok : checkAt 527 1000 box_2565 cert_2565 = true := by
  have h := List.all_eq_true.mp batch_51_04_ok accepted_2565 (by simp [batch_51_04_values])
  exact h
theorem leaf_2565_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2565.profileLo box_2565.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2565_ok
theorem branch_box_2565_nonnegative : ∀ j, 0 ≤ branch_box_2565.lower j ∧ 0 ≤ branch_box_2565.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2565, Box.profileLo, Box.profileHi, box_2565]
theorem leaf_2565_BranchSafe : CertificateConsequences.BranchSafe branch_box_2565 := by
  left; refine ⟨branch_box_2565_nonnegative, ?_⟩
  intro z hz; exact leaf_2565_sound hz

theorem leaf_2568_ok : checkAt 527 1000 box_2568 cert_2568 = true := by
  have h := List.all_eq_true.mp batch_51_05_ok accepted_2568 (by simp [batch_51_05_values])
  exact h
theorem leaf_2568_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2568.profileLo box_2568.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2568_ok
theorem branch_box_2568_nonnegative : ∀ j, 0 ≤ branch_box_2568.lower j ∧ 0 ≤ branch_box_2568.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2568, Box.profileLo, Box.profileHi, box_2568]
theorem leaf_2568_BranchSafe : CertificateConsequences.BranchSafe branch_box_2568 := by
  left; refine ⟨branch_box_2568_nonnegative, ?_⟩
  intro z hz; exact leaf_2568_sound hz

theorem leaf_2569_ok : checkAt 527 1000 box_2569 cert_2569 = true := by
  have h := List.all_eq_true.mp batch_51_06_ok accepted_2569 (by simp [batch_51_06_values])
  exact h
theorem leaf_2569_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2569.profileLo box_2569.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2569_ok
theorem branch_box_2569_nonnegative : ∀ j, 0 ≤ branch_box_2569.lower j ∧ 0 ≤ branch_box_2569.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2569, Box.profileLo, Box.profileHi, box_2569]
theorem leaf_2569_BranchSafe : CertificateConsequences.BranchSafe branch_box_2569 := by
  left; refine ⟨branch_box_2569_nonnegative, ?_⟩
  intro z hz; exact leaf_2569_sound hz

theorem leaf_2571_ok : checkAt 527 1000 box_2571 cert_2571 = true := by
  have h := List.all_eq_true.mp batch_51_07_ok accepted_2571 (by simp [batch_51_07_values])
  exact h
theorem leaf_2571_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2571.profileLo box_2571.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2571_ok
theorem branch_box_2571_nonnegative : ∀ j, 0 ≤ branch_box_2571.lower j ∧ 0 ≤ branch_box_2571.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2571, Box.profileLo, Box.profileHi, box_2571]
theorem leaf_2571_BranchSafe : CertificateConsequences.BranchSafe branch_box_2571 := by
  left; refine ⟨branch_box_2571_nonnegative, ?_⟩
  intro z hz; exact leaf_2571_sound hz

theorem leaf_2577_ok : checkAt 527 1000 box_2577 cert_2577 = true := by
  have h := List.all_eq_true.mp batch_51_08_ok accepted_2577 (by simp [batch_51_08_values])
  exact h
theorem leaf_2577_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2577.profileLo box_2577.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2577_ok
theorem branch_box_2577_nonnegative : ∀ j, 0 ≤ branch_box_2577.lower j ∧ 0 ≤ branch_box_2577.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2577, Box.profileLo, Box.profileHi, box_2577]
theorem leaf_2577_BranchSafe : CertificateConsequences.BranchSafe branch_box_2577 := by
  left; refine ⟨branch_box_2577_nonnegative, ?_⟩
  intro z hz; exact leaf_2577_sound hz

theorem leaf_2579_ok : checkAt 527 1000 box_2579 cert_2579 = true := by
  have h := List.all_eq_true.mp batch_51_09_ok accepted_2579 (by simp [batch_51_09_values])
  exact h
theorem leaf_2579_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2579.profileLo box_2579.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2579_ok
theorem branch_box_2579_nonnegative : ∀ j, 0 ≤ branch_box_2579.lower j ∧ 0 ≤ branch_box_2579.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2579, Box.profileLo, Box.profileHi, box_2579]
theorem leaf_2579_BranchSafe : CertificateConsequences.BranchSafe branch_box_2579 := by
  left; refine ⟨branch_box_2579_nonnegative, ?_⟩
  intro z hz; exact leaf_2579_sound hz

theorem leaf_2582_ok : checkAt 527 1000 box_2582 cert_2582 = true := by
  have h := List.all_eq_true.mp batch_51_10_ok accepted_2582 (by simp [batch_51_10_values])
  exact h
theorem leaf_2582_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2582.profileLo box_2582.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2582_ok
theorem branch_box_2582_nonnegative : ∀ j, 0 ≤ branch_box_2582.lower j ∧ 0 ≤ branch_box_2582.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2582, Box.profileLo, Box.profileHi, box_2582]
theorem leaf_2582_BranchSafe : CertificateConsequences.BranchSafe branch_box_2582 := by
  left; refine ⟨branch_box_2582_nonnegative, ?_⟩
  intro z hz; exact leaf_2582_sound hz

theorem leaf_2583_ok : checkAt 527 1000 box_2583 cert_2583 = true := by
  have h := List.all_eq_true.mp batch_51_11_ok accepted_2583 (by simp [batch_51_11_values])
  exact h
theorem leaf_2583_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2583.profileLo box_2583.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2583_ok
theorem branch_box_2583_nonnegative : ∀ j, 0 ≤ branch_box_2583.lower j ∧ 0 ≤ branch_box_2583.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2583, Box.profileLo, Box.profileHi, box_2583]
theorem leaf_2583_BranchSafe : CertificateConsequences.BranchSafe branch_box_2583 := by
  left; refine ⟨branch_box_2583_nonnegative, ?_⟩
  intro z hz; exact leaf_2583_sound hz

theorem leaf_2585_ok : checkAt 527 1000 box_2585 cert_2585 = true := by
  have h := List.all_eq_true.mp batch_51_12_ok accepted_2585 (by simp [batch_51_12_values])
  exact h
theorem leaf_2585_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2585.profileLo box_2585.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2585_ok
theorem branch_box_2585_nonnegative : ∀ j, 0 ≤ branch_box_2585.lower j ∧ 0 ≤ branch_box_2585.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2585, Box.profileLo, Box.profileHi, box_2585]
theorem leaf_2585_BranchSafe : CertificateConsequences.BranchSafe branch_box_2585 := by
  left; refine ⟨branch_box_2585_nonnegative, ?_⟩
  intro z hz; exact leaf_2585_sound hz

theorem leaf_2590_ok : checkAt 527 1000 box_2590 cert_2590 = true := by
  have h := List.all_eq_true.mp batch_51_13_ok accepted_2590 (by simp [batch_51_13_values])
  exact h
theorem leaf_2590_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2590.profileLo box_2590.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2590_ok
theorem branch_box_2590_nonnegative : ∀ j, 0 ≤ branch_box_2590.lower j ∧ 0 ≤ branch_box_2590.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2590, Box.profileLo, Box.profileHi, box_2590]
theorem leaf_2590_BranchSafe : CertificateConsequences.BranchSafe branch_box_2590 := by
  left; refine ⟨branch_box_2590_nonnegative, ?_⟩
  intro z hz; exact leaf_2590_sound hz

theorem leaf_2591_ok : checkAt 527 1000 box_2591 cert_2591 = true := by
  have h := List.all_eq_true.mp batch_51_14_ok accepted_2591 (by simp [batch_51_14_values])
  exact h
theorem leaf_2591_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2591.profileLo box_2591.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2591_ok
theorem branch_box_2591_nonnegative : ∀ j, 0 ≤ branch_box_2591.lower j ∧ 0 ≤ branch_box_2591.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2591, Box.profileLo, Box.profileHi, box_2591]
theorem leaf_2591_BranchSafe : CertificateConsequences.BranchSafe branch_box_2591 := by
  left; refine ⟨branch_box_2591_nonnegative, ?_⟩
  intro z hz; exact leaf_2591_sound hz

#print axioms batch_51_00_ok
#print axioms leaf_2554_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
