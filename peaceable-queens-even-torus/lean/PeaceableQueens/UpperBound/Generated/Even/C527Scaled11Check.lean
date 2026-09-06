import PeaceableQueens.UpperBound.Generated.Even.C527Scaled11Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_11_00_values : List Bool := [accepted_552]
theorem batch_11_00_ok : batch_11_00_values.all id = true := by decide

def batch_11_01_values : List Bool := [accepted_553]
theorem batch_11_01_ok : batch_11_01_values.all id = true := by decide

def batch_11_02_values : List Bool := [accepted_555]
theorem batch_11_02_ok : batch_11_02_values.all id = true := by decide

def batch_11_03_values : List Bool := [accepted_557]
theorem batch_11_03_ok : batch_11_03_values.all id = true := by decide

def batch_11_04_values : List Bool := [accepted_558]
theorem batch_11_04_ok : batch_11_04_values.all id = true := by decide

def batch_11_05_values : List Bool := [accepted_559]
theorem batch_11_05_ok : batch_11_05_values.all id = true := by decide

def batch_11_06_values : List Bool := [accepted_560]
theorem batch_11_06_ok : batch_11_06_values.all id = true := by decide

def batch_11_07_values : List Bool := [accepted_561]
theorem batch_11_07_ok : batch_11_07_values.all id = true := by decide

def batch_11_08_values : List Bool := [accepted_562]
theorem batch_11_08_ok : batch_11_08_values.all id = true := by decide

def batch_11_09_values : List Bool := [accepted_564]
theorem batch_11_09_ok : batch_11_09_values.all id = true := by decide

def batch_11_10_values : List Bool := [accepted_569]
theorem batch_11_10_ok : batch_11_10_values.all id = true := by decide

def batch_11_11_values : List Bool := [accepted_570]
theorem batch_11_11_ok : batch_11_11_values.all id = true := by decide

def batch_11_12_values : List Bool := [accepted_571]
theorem batch_11_12_ok : batch_11_12_values.all id = true := by decide

def batch_11_13_values : List Bool := [accepted_574]
theorem batch_11_13_ok : batch_11_13_values.all id = true := by decide

def batch_11_14_values : List Bool := [accepted_575]
theorem batch_11_14_ok : batch_11_14_values.all id = true := by decide

def batch_11_15_values : List Bool := [accepted_576]
theorem batch_11_15_ok : batch_11_15_values.all id = true := by decide

def batch_11_16_values : List Bool := [accepted_578]
theorem batch_11_16_ok : batch_11_16_values.all id = true := by decide

def batch_11_17_values : List Bool := [accepted_579]
theorem batch_11_17_ok : batch_11_17_values.all id = true := by decide

def batch_11_18_values : List Bool := [accepted_581]
theorem batch_11_18_ok : batch_11_18_values.all id = true := by decide

def batch_11_19_values : List Bool := [accepted_582]
theorem batch_11_19_ok : batch_11_19_values.all id = true := by decide

def batch_11_20_values : List Bool := [accepted_589]
theorem batch_11_20_ok : batch_11_20_values.all id = true := by decide

def batch_11_21_values : List Bool := [accepted_590]
theorem batch_11_21_ok : batch_11_21_values.all id = true := by decide

def batch_11_22_values : List Bool := [accepted_591]
theorem batch_11_22_ok : batch_11_22_values.all id = true := by decide

def batch_11_23_values : List Bool := [accepted_593]
theorem batch_11_23_ok : batch_11_23_values.all id = true := by decide

def batch_11_24_values : List Bool := [accepted_594]
theorem batch_11_24_ok : batch_11_24_values.all id = true := by decide

def batch_11_25_values : List Bool := [accepted_597]
theorem batch_11_25_ok : batch_11_25_values.all id = true := by decide

def batch_11_26_values : List Bool := [accepted_599]
theorem batch_11_26_ok : batch_11_26_values.all id = true := by decide

theorem leaf_552_ok : checkAt 527 1000 box_552 cert_552 = true := by
  have h := List.all_eq_true.mp batch_11_00_ok accepted_552 (by simp [batch_11_00_values])
  exact h
theorem leaf_552_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_552.profileLo box_552.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_552_ok
theorem branch_box_552_nonnegative : ∀ j, 0 ≤ branch_box_552.lower j ∧ 0 ≤ branch_box_552.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_552, Box.profileLo, Box.profileHi, box_552]
theorem leaf_552_BranchSafe : CertificateConsequences.BranchSafe branch_box_552 := by
  left; refine ⟨branch_box_552_nonnegative, ?_⟩
  intro z hz; exact leaf_552_sound hz

theorem leaf_553_ok : checkAt 527 1000 box_553 cert_553 = true := by
  have h := List.all_eq_true.mp batch_11_01_ok accepted_553 (by simp [batch_11_01_values])
  exact h
theorem leaf_553_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_553.profileLo box_553.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_553_ok
theorem branch_box_553_nonnegative : ∀ j, 0 ≤ branch_box_553.lower j ∧ 0 ≤ branch_box_553.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_553, Box.profileLo, Box.profileHi, box_553]
theorem leaf_553_BranchSafe : CertificateConsequences.BranchSafe branch_box_553 := by
  left; refine ⟨branch_box_553_nonnegative, ?_⟩
  intro z hz; exact leaf_553_sound hz

theorem leaf_555_ok : checkAt 527 1000 box_555 cert_555 = true := by
  have h := List.all_eq_true.mp batch_11_02_ok accepted_555 (by simp [batch_11_02_values])
  exact h
theorem leaf_555_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_555.profileLo box_555.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_555_ok
theorem branch_box_555_nonnegative : ∀ j, 0 ≤ branch_box_555.lower j ∧ 0 ≤ branch_box_555.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_555, Box.profileLo, Box.profileHi, box_555]
theorem leaf_555_BranchSafe : CertificateConsequences.BranchSafe branch_box_555 := by
  left; refine ⟨branch_box_555_nonnegative, ?_⟩
  intro z hz; exact leaf_555_sound hz

theorem leaf_557_ok : checkAt 527 1000 box_557 cert_557 = true := by
  have h := List.all_eq_true.mp batch_11_03_ok accepted_557 (by simp [batch_11_03_values])
  exact h
theorem leaf_557_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_557.profileLo box_557.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_557_ok
theorem branch_box_557_nonnegative : ∀ j, 0 ≤ branch_box_557.lower j ∧ 0 ≤ branch_box_557.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_557, Box.profileLo, Box.profileHi, box_557]
theorem leaf_557_BranchSafe : CertificateConsequences.BranchSafe branch_box_557 := by
  left; refine ⟨branch_box_557_nonnegative, ?_⟩
  intro z hz; exact leaf_557_sound hz

theorem leaf_558_ok : checkAt 527 1000 box_558 cert_558 = true := by
  have h := List.all_eq_true.mp batch_11_04_ok accepted_558 (by simp [batch_11_04_values])
  exact h
theorem leaf_558_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_558.profileLo box_558.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_558_ok
theorem branch_box_558_nonnegative : ∀ j, 0 ≤ branch_box_558.lower j ∧ 0 ≤ branch_box_558.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_558, Box.profileLo, Box.profileHi, box_558]
theorem leaf_558_BranchSafe : CertificateConsequences.BranchSafe branch_box_558 := by
  left; refine ⟨branch_box_558_nonnegative, ?_⟩
  intro z hz; exact leaf_558_sound hz

theorem leaf_559_ok : checkAt 527 1000 box_559 cert_559 = true := by
  have h := List.all_eq_true.mp batch_11_05_ok accepted_559 (by simp [batch_11_05_values])
  exact h
theorem leaf_559_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_559.profileLo box_559.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_559_ok
theorem branch_box_559_nonnegative : ∀ j, 0 ≤ branch_box_559.lower j ∧ 0 ≤ branch_box_559.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_559, Box.profileLo, Box.profileHi, box_559]
theorem leaf_559_BranchSafe : CertificateConsequences.BranchSafe branch_box_559 := by
  left; refine ⟨branch_box_559_nonnegative, ?_⟩
  intro z hz; exact leaf_559_sound hz

theorem leaf_560_ok : checkAt 527 1000 box_560 cert_560 = true := by
  have h := List.all_eq_true.mp batch_11_06_ok accepted_560 (by simp [batch_11_06_values])
  exact h
theorem leaf_560_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_560.profileLo box_560.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_560_ok
theorem branch_box_560_nonnegative : ∀ j, 0 ≤ branch_box_560.lower j ∧ 0 ≤ branch_box_560.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_560, Box.profileLo, Box.profileHi, box_560]
theorem leaf_560_BranchSafe : CertificateConsequences.BranchSafe branch_box_560 := by
  left; refine ⟨branch_box_560_nonnegative, ?_⟩
  intro z hz; exact leaf_560_sound hz

theorem leaf_561_ok : checkAt 527 1000 box_561 cert_561 = true := by
  have h := List.all_eq_true.mp batch_11_07_ok accepted_561 (by simp [batch_11_07_values])
  exact h
theorem leaf_561_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_561.profileLo box_561.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_561_ok
theorem branch_box_561_nonnegative : ∀ j, 0 ≤ branch_box_561.lower j ∧ 0 ≤ branch_box_561.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_561, Box.profileLo, Box.profileHi, box_561]
theorem leaf_561_BranchSafe : CertificateConsequences.BranchSafe branch_box_561 := by
  left; refine ⟨branch_box_561_nonnegative, ?_⟩
  intro z hz; exact leaf_561_sound hz

theorem leaf_562_ok : checkAt 527 1000 box_562 cert_562 = true := by
  have h := List.all_eq_true.mp batch_11_08_ok accepted_562 (by simp [batch_11_08_values])
  exact h
theorem leaf_562_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_562.profileLo box_562.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_562_ok
theorem branch_box_562_nonnegative : ∀ j, 0 ≤ branch_box_562.lower j ∧ 0 ≤ branch_box_562.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_562, Box.profileLo, Box.profileHi, box_562]
theorem leaf_562_BranchSafe : CertificateConsequences.BranchSafe branch_box_562 := by
  left; refine ⟨branch_box_562_nonnegative, ?_⟩
  intro z hz; exact leaf_562_sound hz

theorem leaf_564_ok : checkAt 527 1000 box_564 cert_564 = true := by
  have h := List.all_eq_true.mp batch_11_09_ok accepted_564 (by simp [batch_11_09_values])
  exact h
theorem leaf_564_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_564.profileLo box_564.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_564_ok
theorem branch_box_564_nonnegative : ∀ j, 0 ≤ branch_box_564.lower j ∧ 0 ≤ branch_box_564.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_564, Box.profileLo, Box.profileHi, box_564]
theorem leaf_564_BranchSafe : CertificateConsequences.BranchSafe branch_box_564 := by
  left; refine ⟨branch_box_564_nonnegative, ?_⟩
  intro z hz; exact leaf_564_sound hz

theorem leaf_569_ok : checkAt 527 1000 box_569 cert_569 = true := by
  have h := List.all_eq_true.mp batch_11_10_ok accepted_569 (by simp [batch_11_10_values])
  exact h
theorem leaf_569_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_569.profileLo box_569.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_569_ok
theorem branch_box_569_nonnegative : ∀ j, 0 ≤ branch_box_569.lower j ∧ 0 ≤ branch_box_569.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_569, Box.profileLo, Box.profileHi, box_569]
theorem leaf_569_BranchSafe : CertificateConsequences.BranchSafe branch_box_569 := by
  left; refine ⟨branch_box_569_nonnegative, ?_⟩
  intro z hz; exact leaf_569_sound hz

theorem leaf_570_ok : checkAt 527 1000 box_570 cert_570 = true := by
  have h := List.all_eq_true.mp batch_11_11_ok accepted_570 (by simp [batch_11_11_values])
  exact h
theorem leaf_570_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_570.profileLo box_570.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_570_ok
theorem branch_box_570_nonnegative : ∀ j, 0 ≤ branch_box_570.lower j ∧ 0 ≤ branch_box_570.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_570, Box.profileLo, Box.profileHi, box_570]
theorem leaf_570_BranchSafe : CertificateConsequences.BranchSafe branch_box_570 := by
  left; refine ⟨branch_box_570_nonnegative, ?_⟩
  intro z hz; exact leaf_570_sound hz

theorem leaf_571_ok : checkAt 527 1000 box_571 cert_571 = true := by
  have h := List.all_eq_true.mp batch_11_12_ok accepted_571 (by simp [batch_11_12_values])
  exact h
theorem leaf_571_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_571.profileLo box_571.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_571_ok
theorem branch_box_571_nonnegative : ∀ j, 0 ≤ branch_box_571.lower j ∧ 0 ≤ branch_box_571.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_571, Box.profileLo, Box.profileHi, box_571]
theorem leaf_571_BranchSafe : CertificateConsequences.BranchSafe branch_box_571 := by
  left; refine ⟨branch_box_571_nonnegative, ?_⟩
  intro z hz; exact leaf_571_sound hz

theorem leaf_574_ok : checkAt 527 1000 box_574 cert_574 = true := by
  have h := List.all_eq_true.mp batch_11_13_ok accepted_574 (by simp [batch_11_13_values])
  exact h
theorem leaf_574_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_574.profileLo box_574.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_574_ok
theorem branch_box_574_nonnegative : ∀ j, 0 ≤ branch_box_574.lower j ∧ 0 ≤ branch_box_574.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_574, Box.profileLo, Box.profileHi, box_574]
theorem leaf_574_BranchSafe : CertificateConsequences.BranchSafe branch_box_574 := by
  left; refine ⟨branch_box_574_nonnegative, ?_⟩
  intro z hz; exact leaf_574_sound hz

theorem leaf_575_ok : checkAt 527 1000 box_575 cert_575 = true := by
  have h := List.all_eq_true.mp batch_11_14_ok accepted_575 (by simp [batch_11_14_values])
  exact h
theorem leaf_575_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_575.profileLo box_575.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_575_ok
theorem branch_box_575_nonnegative : ∀ j, 0 ≤ branch_box_575.lower j ∧ 0 ≤ branch_box_575.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_575, Box.profileLo, Box.profileHi, box_575]
theorem leaf_575_BranchSafe : CertificateConsequences.BranchSafe branch_box_575 := by
  left; refine ⟨branch_box_575_nonnegative, ?_⟩
  intro z hz; exact leaf_575_sound hz

theorem leaf_576_ok : checkAt 527 1000 box_576 cert_576 = true := by
  have h := List.all_eq_true.mp batch_11_15_ok accepted_576 (by simp [batch_11_15_values])
  exact h
theorem leaf_576_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_576.profileLo box_576.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_576_ok
theorem branch_box_576_nonnegative : ∀ j, 0 ≤ branch_box_576.lower j ∧ 0 ≤ branch_box_576.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_576, Box.profileLo, Box.profileHi, box_576]
theorem leaf_576_BranchSafe : CertificateConsequences.BranchSafe branch_box_576 := by
  left; refine ⟨branch_box_576_nonnegative, ?_⟩
  intro z hz; exact leaf_576_sound hz

theorem leaf_578_ok : checkAt 527 1000 box_578 cert_578 = true := by
  have h := List.all_eq_true.mp batch_11_16_ok accepted_578 (by simp [batch_11_16_values])
  exact h
theorem leaf_578_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_578.profileLo box_578.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_578_ok
theorem branch_box_578_nonnegative : ∀ j, 0 ≤ branch_box_578.lower j ∧ 0 ≤ branch_box_578.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_578, Box.profileLo, Box.profileHi, box_578]
theorem leaf_578_BranchSafe : CertificateConsequences.BranchSafe branch_box_578 := by
  left; refine ⟨branch_box_578_nonnegative, ?_⟩
  intro z hz; exact leaf_578_sound hz

theorem leaf_579_ok : checkAt 527 1000 box_579 cert_579 = true := by
  have h := List.all_eq_true.mp batch_11_17_ok accepted_579 (by simp [batch_11_17_values])
  exact h
theorem leaf_579_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_579.profileLo box_579.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_579_ok
theorem branch_box_579_nonnegative : ∀ j, 0 ≤ branch_box_579.lower j ∧ 0 ≤ branch_box_579.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_579, Box.profileLo, Box.profileHi, box_579]
theorem leaf_579_BranchSafe : CertificateConsequences.BranchSafe branch_box_579 := by
  left; refine ⟨branch_box_579_nonnegative, ?_⟩
  intro z hz; exact leaf_579_sound hz

theorem leaf_581_ok : checkAt 527 1000 box_581 cert_581 = true := by
  have h := List.all_eq_true.mp batch_11_18_ok accepted_581 (by simp [batch_11_18_values])
  exact h
theorem leaf_581_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_581.profileLo box_581.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_581_ok
theorem branch_box_581_nonnegative : ∀ j, 0 ≤ branch_box_581.lower j ∧ 0 ≤ branch_box_581.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_581, Box.profileLo, Box.profileHi, box_581]
theorem leaf_581_BranchSafe : CertificateConsequences.BranchSafe branch_box_581 := by
  left; refine ⟨branch_box_581_nonnegative, ?_⟩
  intro z hz; exact leaf_581_sound hz

theorem leaf_582_ok : checkAt 527 1000 box_582 cert_582 = true := by
  have h := List.all_eq_true.mp batch_11_19_ok accepted_582 (by simp [batch_11_19_values])
  exact h
theorem leaf_582_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_582.profileLo box_582.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_582_ok
theorem branch_box_582_nonnegative : ∀ j, 0 ≤ branch_box_582.lower j ∧ 0 ≤ branch_box_582.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_582, Box.profileLo, Box.profileHi, box_582]
theorem leaf_582_BranchSafe : CertificateConsequences.BranchSafe branch_box_582 := by
  left; refine ⟨branch_box_582_nonnegative, ?_⟩
  intro z hz; exact leaf_582_sound hz

theorem leaf_589_ok : checkAt 527 1000 box_589 cert_589 = true := by
  have h := List.all_eq_true.mp batch_11_20_ok accepted_589 (by simp [batch_11_20_values])
  exact h
theorem leaf_589_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_589.profileLo box_589.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_589_ok
theorem branch_box_589_nonnegative : ∀ j, 0 ≤ branch_box_589.lower j ∧ 0 ≤ branch_box_589.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_589, Box.profileLo, Box.profileHi, box_589]
theorem leaf_589_BranchSafe : CertificateConsequences.BranchSafe branch_box_589 := by
  left; refine ⟨branch_box_589_nonnegative, ?_⟩
  intro z hz; exact leaf_589_sound hz

theorem leaf_590_ok : checkAt 527 1000 box_590 cert_590 = true := by
  have h := List.all_eq_true.mp batch_11_21_ok accepted_590 (by simp [batch_11_21_values])
  exact h
theorem leaf_590_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_590.profileLo box_590.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_590_ok
theorem branch_box_590_nonnegative : ∀ j, 0 ≤ branch_box_590.lower j ∧ 0 ≤ branch_box_590.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_590, Box.profileLo, Box.profileHi, box_590]
theorem leaf_590_BranchSafe : CertificateConsequences.BranchSafe branch_box_590 := by
  left; refine ⟨branch_box_590_nonnegative, ?_⟩
  intro z hz; exact leaf_590_sound hz

theorem leaf_591_ok : checkAt 527 1000 box_591 cert_591 = true := by
  have h := List.all_eq_true.mp batch_11_22_ok accepted_591 (by simp [batch_11_22_values])
  exact h
theorem leaf_591_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_591.profileLo box_591.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_591_ok
theorem branch_box_591_nonnegative : ∀ j, 0 ≤ branch_box_591.lower j ∧ 0 ≤ branch_box_591.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_591, Box.profileLo, Box.profileHi, box_591]
theorem leaf_591_BranchSafe : CertificateConsequences.BranchSafe branch_box_591 := by
  left; refine ⟨branch_box_591_nonnegative, ?_⟩
  intro z hz; exact leaf_591_sound hz

theorem leaf_593_ok : checkAt 527 1000 box_593 cert_593 = true := by
  have h := List.all_eq_true.mp batch_11_23_ok accepted_593 (by simp [batch_11_23_values])
  exact h
theorem leaf_593_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_593.profileLo box_593.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_593_ok
theorem branch_box_593_nonnegative : ∀ j, 0 ≤ branch_box_593.lower j ∧ 0 ≤ branch_box_593.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_593, Box.profileLo, Box.profileHi, box_593]
theorem leaf_593_BranchSafe : CertificateConsequences.BranchSafe branch_box_593 := by
  left; refine ⟨branch_box_593_nonnegative, ?_⟩
  intro z hz; exact leaf_593_sound hz

theorem leaf_594_ok : checkAt 527 1000 box_594 cert_594 = true := by
  have h := List.all_eq_true.mp batch_11_24_ok accepted_594 (by simp [batch_11_24_values])
  exact h
theorem leaf_594_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_594.profileLo box_594.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_594_ok
theorem branch_box_594_nonnegative : ∀ j, 0 ≤ branch_box_594.lower j ∧ 0 ≤ branch_box_594.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_594, Box.profileLo, Box.profileHi, box_594]
theorem leaf_594_BranchSafe : CertificateConsequences.BranchSafe branch_box_594 := by
  left; refine ⟨branch_box_594_nonnegative, ?_⟩
  intro z hz; exact leaf_594_sound hz

theorem leaf_597_ok : checkAt 527 1000 box_597 cert_597 = true := by
  have h := List.all_eq_true.mp batch_11_25_ok accepted_597 (by simp [batch_11_25_values])
  exact h
theorem leaf_597_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_597.profileLo box_597.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_597_ok
theorem branch_box_597_nonnegative : ∀ j, 0 ≤ branch_box_597.lower j ∧ 0 ≤ branch_box_597.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_597, Box.profileLo, Box.profileHi, box_597]
theorem leaf_597_BranchSafe : CertificateConsequences.BranchSafe branch_box_597 := by
  left; refine ⟨branch_box_597_nonnegative, ?_⟩
  intro z hz; exact leaf_597_sound hz

theorem leaf_599_ok : checkAt 527 1000 box_599 cert_599 = true := by
  have h := List.all_eq_true.mp batch_11_26_ok accepted_599 (by simp [batch_11_26_values])
  exact h
theorem leaf_599_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_599.profileLo box_599.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_599_ok
theorem branch_box_599_nonnegative : ∀ j, 0 ≤ branch_box_599.lower j ∧ 0 ≤ branch_box_599.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_599, Box.profileLo, Box.profileHi, box_599]
theorem leaf_599_BranchSafe : CertificateConsequences.BranchSafe branch_box_599 := by
  left; refine ⟨branch_box_599_nonnegative, ?_⟩
  intro z hz; exact leaf_599_sound hz

#print axioms batch_11_00_ok
#print axioms leaf_552_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
