import PeaceableQueens.UpperBound.Generated.Even.C527Scaled51Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_51_00_values : List Bool := [accepted_2553]
theorem batch_51_00_ok : batch_51_00_values.all id = true := by decide

def batch_51_01_values : List Bool := [accepted_2554]
theorem batch_51_01_ok : batch_51_01_values.all id = true := by decide

def batch_51_02_values : List Bool := [accepted_2556]
theorem batch_51_02_ok : batch_51_02_values.all id = true := by decide

def batch_51_03_values : List Bool := [accepted_2558]
theorem batch_51_03_ok : batch_51_03_values.all id = true := by decide

def batch_51_04_values : List Bool := [accepted_2559]
theorem batch_51_04_ok : batch_51_04_values.all id = true := by decide

def batch_51_05_values : List Bool := [accepted_2560]
theorem batch_51_05_ok : batch_51_05_values.all id = true := by decide

def batch_51_06_values : List Bool := [accepted_2561]
theorem batch_51_06_ok : batch_51_06_values.all id = true := by decide

def batch_51_07_values : List Bool := [accepted_2563]
theorem batch_51_07_ok : batch_51_07_values.all id = true := by decide

def batch_51_08_values : List Bool := [accepted_2564]
theorem batch_51_08_ok : batch_51_08_values.all id = true := by decide

def batch_51_09_values : List Bool := [accepted_2574]
theorem batch_51_09_ok : batch_51_09_values.all id = true := by decide

def batch_51_10_values : List Bool := [accepted_2575]
theorem batch_51_10_ok : batch_51_10_values.all id = true := by decide

def batch_51_11_values : List Bool := [accepted_2576]
theorem batch_51_11_ok : batch_51_11_values.all id = true := by decide

def batch_51_12_values : List Bool := [accepted_2577]
theorem batch_51_12_ok : batch_51_12_values.all id = true := by decide

def batch_51_13_values : List Bool := [accepted_2578]
theorem batch_51_13_ok : batch_51_13_values.all id = true := by decide

def batch_51_14_values : List Bool := [accepted_2581]
theorem batch_51_14_ok : batch_51_14_values.all id = true := by decide

def batch_51_15_values : List Bool := [accepted_2582]
theorem batch_51_15_ok : batch_51_15_values.all id = true := by decide

def batch_51_16_values : List Bool := [accepted_2583]
theorem batch_51_16_ok : batch_51_16_values.all id = true := by decide

def batch_51_17_values : List Bool := [accepted_2585]
theorem batch_51_17_ok : batch_51_17_values.all id = true := by decide

def batch_51_18_values : List Bool := [accepted_2586]
theorem batch_51_18_ok : batch_51_18_values.all id = true := by decide

def batch_51_19_values : List Bool := [accepted_2587]
theorem batch_51_19_ok : batch_51_19_values.all id = true := by decide

def batch_51_20_values : List Bool := [accepted_2589]
theorem batch_51_20_ok : batch_51_20_values.all id = true := by decide

def batch_51_21_values : List Bool := [accepted_2590]
theorem batch_51_21_ok : batch_51_21_values.all id = true := by decide

def batch_51_22_values : List Bool := [accepted_2595]
theorem batch_51_22_ok : batch_51_22_values.all id = true := by decide

def batch_51_23_values : List Bool := [accepted_2596]
theorem batch_51_23_ok : batch_51_23_values.all id = true := by decide

theorem leaf_2553_ok : checkAt 527 1000 box_2553 cert_2553 = true := by
  have h := List.all_eq_true.mp batch_51_00_ok accepted_2553 (by simp [batch_51_00_values])
  exact h
theorem leaf_2553_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2553.profileLo box_2553.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2553_ok
theorem branch_box_2553_nonnegative : ∀ j, 0 ≤ branch_box_2553.lower j ∧ 0 ≤ branch_box_2553.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2553, Box.profileLo, Box.profileHi, box_2553]
theorem leaf_2553_BranchSafe : CertificateConsequences.BranchSafe branch_box_2553 := by
  left; refine ⟨branch_box_2553_nonnegative, ?_⟩
  intro z hz; exact leaf_2553_sound hz

theorem leaf_2554_ok : checkAt 527 1000 box_2554 cert_2554 = true := by
  have h := List.all_eq_true.mp batch_51_01_ok accepted_2554 (by simp [batch_51_01_values])
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
  have h := List.all_eq_true.mp batch_51_02_ok accepted_2556 (by simp [batch_51_02_values])
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

theorem leaf_2558_ok : checkAt 527 1000 box_2558 cert_2558 = true := by
  have h := List.all_eq_true.mp batch_51_03_ok accepted_2558 (by simp [batch_51_03_values])
  exact h
theorem leaf_2558_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2558.profileLo box_2558.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2558_ok
theorem branch_box_2558_nonnegative : ∀ j, 0 ≤ branch_box_2558.lower j ∧ 0 ≤ branch_box_2558.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2558, Box.profileLo, Box.profileHi, box_2558]
theorem leaf_2558_BranchSafe : CertificateConsequences.BranchSafe branch_box_2558 := by
  left; refine ⟨branch_box_2558_nonnegative, ?_⟩
  intro z hz; exact leaf_2558_sound hz

theorem leaf_2559_ok : checkAt 527 1000 box_2559 cert_2559 = true := by
  have h := List.all_eq_true.mp batch_51_04_ok accepted_2559 (by simp [batch_51_04_values])
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

theorem leaf_2560_ok : checkAt 527 1000 box_2560 cert_2560 = true := by
  have h := List.all_eq_true.mp batch_51_05_ok accepted_2560 (by simp [batch_51_05_values])
  exact h
theorem leaf_2560_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2560.profileLo box_2560.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2560_ok
theorem branch_box_2560_nonnegative : ∀ j, 0 ≤ branch_box_2560.lower j ∧ 0 ≤ branch_box_2560.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2560, Box.profileLo, Box.profileHi, box_2560]
theorem leaf_2560_BranchSafe : CertificateConsequences.BranchSafe branch_box_2560 := by
  left; refine ⟨branch_box_2560_nonnegative, ?_⟩
  intro z hz; exact leaf_2560_sound hz

theorem leaf_2561_ok : checkAt 527 1000 box_2561 cert_2561 = true := by
  have h := List.all_eq_true.mp batch_51_06_ok accepted_2561 (by simp [batch_51_06_values])
  exact h
theorem leaf_2561_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2561.profileLo box_2561.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2561_ok
theorem branch_box_2561_nonnegative : ∀ j, 0 ≤ branch_box_2561.lower j ∧ 0 ≤ branch_box_2561.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2561, Box.profileLo, Box.profileHi, box_2561]
theorem leaf_2561_BranchSafe : CertificateConsequences.BranchSafe branch_box_2561 := by
  left; refine ⟨branch_box_2561_nonnegative, ?_⟩
  intro z hz; exact leaf_2561_sound hz

theorem leaf_2563_ok : checkAt 527 1000 box_2563 cert_2563 = true := by
  have h := List.all_eq_true.mp batch_51_07_ok accepted_2563 (by simp [batch_51_07_values])
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

theorem leaf_2564_ok : checkAt 527 1000 box_2564 cert_2564 = true := by
  have h := List.all_eq_true.mp batch_51_08_ok accepted_2564 (by simp [batch_51_08_values])
  exact h
theorem leaf_2564_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2564.profileLo box_2564.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2564_ok
theorem branch_box_2564_nonnegative : ∀ j, 0 ≤ branch_box_2564.lower j ∧ 0 ≤ branch_box_2564.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2564, Box.profileLo, Box.profileHi, box_2564]
theorem leaf_2564_BranchSafe : CertificateConsequences.BranchSafe branch_box_2564 := by
  left; refine ⟨branch_box_2564_nonnegative, ?_⟩
  intro z hz; exact leaf_2564_sound hz

theorem leaf_2574_ok : checkAt 527 1000 box_2574 cert_2574 = true := by
  have h := List.all_eq_true.mp batch_51_09_ok accepted_2574 (by simp [batch_51_09_values])
  exact h
theorem leaf_2574_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2574.profileLo box_2574.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2574_ok
theorem branch_box_2574_nonnegative : ∀ j, 0 ≤ branch_box_2574.lower j ∧ 0 ≤ branch_box_2574.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2574, Box.profileLo, Box.profileHi, box_2574]
theorem leaf_2574_BranchSafe : CertificateConsequences.BranchSafe branch_box_2574 := by
  left; refine ⟨branch_box_2574_nonnegative, ?_⟩
  intro z hz; exact leaf_2574_sound hz

theorem leaf_2575_ok : checkAt 527 1000 box_2575 cert_2575 = true := by
  have h := List.all_eq_true.mp batch_51_10_ok accepted_2575 (by simp [batch_51_10_values])
  exact h
theorem leaf_2575_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2575.profileLo box_2575.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2575_ok
theorem branch_box_2575_nonnegative : ∀ j, 0 ≤ branch_box_2575.lower j ∧ 0 ≤ branch_box_2575.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2575, Box.profileLo, Box.profileHi, box_2575]
theorem leaf_2575_BranchSafe : CertificateConsequences.BranchSafe branch_box_2575 := by
  left; refine ⟨branch_box_2575_nonnegative, ?_⟩
  intro z hz; exact leaf_2575_sound hz

theorem leaf_2576_ok : checkAt 527 1000 box_2576 cert_2576 = true := by
  have h := List.all_eq_true.mp batch_51_11_ok accepted_2576 (by simp [batch_51_11_values])
  exact h
theorem leaf_2576_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2576.profileLo box_2576.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2576_ok
theorem branch_box_2576_nonnegative : ∀ j, 0 ≤ branch_box_2576.lower j ∧ 0 ≤ branch_box_2576.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2576, Box.profileLo, Box.profileHi, box_2576]
theorem leaf_2576_BranchSafe : CertificateConsequences.BranchSafe branch_box_2576 := by
  left; refine ⟨branch_box_2576_nonnegative, ?_⟩
  intro z hz; exact leaf_2576_sound hz

theorem leaf_2577_ok : checkAt 527 1000 box_2577 cert_2577 = true := by
  have h := List.all_eq_true.mp batch_51_12_ok accepted_2577 (by simp [batch_51_12_values])
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

theorem leaf_2578_ok : checkAt 527 1000 box_2578 cert_2578 = true := by
  have h := List.all_eq_true.mp batch_51_13_ok accepted_2578 (by simp [batch_51_13_values])
  exact h
theorem leaf_2578_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2578.profileLo box_2578.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2578_ok
theorem branch_box_2578_nonnegative : ∀ j, 0 ≤ branch_box_2578.lower j ∧ 0 ≤ branch_box_2578.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2578, Box.profileLo, Box.profileHi, box_2578]
theorem leaf_2578_BranchSafe : CertificateConsequences.BranchSafe branch_box_2578 := by
  left; refine ⟨branch_box_2578_nonnegative, ?_⟩
  intro z hz; exact leaf_2578_sound hz

theorem leaf_2581_ok : checkAt 527 1000 box_2581 cert_2581 = true := by
  have h := List.all_eq_true.mp batch_51_14_ok accepted_2581 (by simp [batch_51_14_values])
  exact h
theorem leaf_2581_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2581.profileLo box_2581.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2581_ok
theorem branch_box_2581_nonnegative : ∀ j, 0 ≤ branch_box_2581.lower j ∧ 0 ≤ branch_box_2581.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2581, Box.profileLo, Box.profileHi, box_2581]
theorem leaf_2581_BranchSafe : CertificateConsequences.BranchSafe branch_box_2581 := by
  left; refine ⟨branch_box_2581_nonnegative, ?_⟩
  intro z hz; exact leaf_2581_sound hz

theorem leaf_2582_ok : checkAt 527 1000 box_2582 cert_2582 = true := by
  have h := List.all_eq_true.mp batch_51_15_ok accepted_2582 (by simp [batch_51_15_values])
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
  have h := List.all_eq_true.mp batch_51_16_ok accepted_2583 (by simp [batch_51_16_values])
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
  have h := List.all_eq_true.mp batch_51_17_ok accepted_2585 (by simp [batch_51_17_values])
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

theorem leaf_2586_ok : checkAt 527 1000 box_2586 cert_2586 = true := by
  have h := List.all_eq_true.mp batch_51_18_ok accepted_2586 (by simp [batch_51_18_values])
  exact h
theorem leaf_2586_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2586.profileLo box_2586.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2586_ok
theorem branch_box_2586_nonnegative : ∀ j, 0 ≤ branch_box_2586.lower j ∧ 0 ≤ branch_box_2586.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2586, Box.profileLo, Box.profileHi, box_2586]
theorem leaf_2586_BranchSafe : CertificateConsequences.BranchSafe branch_box_2586 := by
  left; refine ⟨branch_box_2586_nonnegative, ?_⟩
  intro z hz; exact leaf_2586_sound hz

theorem leaf_2587_ok : checkAt 527 1000 box_2587 cert_2587 = true := by
  have h := List.all_eq_true.mp batch_51_19_ok accepted_2587 (by simp [batch_51_19_values])
  exact h
theorem leaf_2587_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2587.profileLo box_2587.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2587_ok
theorem branch_box_2587_nonnegative : ∀ j, 0 ≤ branch_box_2587.lower j ∧ 0 ≤ branch_box_2587.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2587, Box.profileLo, Box.profileHi, box_2587]
theorem leaf_2587_BranchSafe : CertificateConsequences.BranchSafe branch_box_2587 := by
  left; refine ⟨branch_box_2587_nonnegative, ?_⟩
  intro z hz; exact leaf_2587_sound hz

theorem leaf_2589_ok : checkAt 527 1000 box_2589 cert_2589 = true := by
  have h := List.all_eq_true.mp batch_51_20_ok accepted_2589 (by simp [batch_51_20_values])
  exact h
theorem leaf_2589_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2589.profileLo box_2589.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2589_ok
theorem branch_box_2589_nonnegative : ∀ j, 0 ≤ branch_box_2589.lower j ∧ 0 ≤ branch_box_2589.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2589, Box.profileLo, Box.profileHi, box_2589]
theorem leaf_2589_BranchSafe : CertificateConsequences.BranchSafe branch_box_2589 := by
  left; refine ⟨branch_box_2589_nonnegative, ?_⟩
  intro z hz; exact leaf_2589_sound hz

theorem leaf_2590_ok : checkAt 527 1000 box_2590 cert_2590 = true := by
  have h := List.all_eq_true.mp batch_51_21_ok accepted_2590 (by simp [batch_51_21_values])
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

theorem leaf_2595_ok : checkAt 527 1000 box_2595 cert_2595 = true := by
  have h := List.all_eq_true.mp batch_51_22_ok accepted_2595 (by simp [batch_51_22_values])
  exact h
theorem leaf_2595_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2595.profileLo box_2595.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2595_ok
theorem branch_box_2595_nonnegative : ∀ j, 0 ≤ branch_box_2595.lower j ∧ 0 ≤ branch_box_2595.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2595, Box.profileLo, Box.profileHi, box_2595]
theorem leaf_2595_BranchSafe : CertificateConsequences.BranchSafe branch_box_2595 := by
  left; refine ⟨branch_box_2595_nonnegative, ?_⟩
  intro z hz; exact leaf_2595_sound hz

theorem leaf_2596_ok : checkAt 527 1000 box_2596 cert_2596 = true := by
  have h := List.all_eq_true.mp batch_51_23_ok accepted_2596 (by simp [batch_51_23_values])
  exact h
theorem leaf_2596_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2596.profileLo box_2596.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2596_ok
theorem branch_box_2596_nonnegative : ∀ j, 0 ≤ branch_box_2596.lower j ∧ 0 ≤ branch_box_2596.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2596, Box.profileLo, Box.profileHi, box_2596]
theorem leaf_2596_BranchSafe : CertificateConsequences.BranchSafe branch_box_2596 := by
  left; refine ⟨branch_box_2596_nonnegative, ?_⟩
  intro z hz; exact leaf_2596_sound hz

#print axioms batch_51_00_ok
#print axioms leaf_2553_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
