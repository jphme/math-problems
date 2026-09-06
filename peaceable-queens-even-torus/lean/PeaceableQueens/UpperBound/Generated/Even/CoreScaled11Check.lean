import PeaceableQueens.UpperBound.Generated.Even.CoreScaled11Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
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

def batch_11_04_values : List Bool := [accepted_560]
theorem batch_11_04_ok : batch_11_04_values.all id = true := by decide

def batch_11_05_values : List Bool := [accepted_561]
theorem batch_11_05_ok : batch_11_05_values.all id = true := by decide

def batch_11_06_values : List Bool := [accepted_563]
theorem batch_11_06_ok : batch_11_06_values.all id = true := by decide

def batch_11_07_values : List Bool := [accepted_565]
theorem batch_11_07_ok : batch_11_07_values.all id = true := by decide

def batch_11_08_values : List Bool := [accepted_572]
theorem batch_11_08_ok : batch_11_08_values.all id = true := by decide

def batch_11_09_values : List Bool := [accepted_574]
theorem batch_11_09_ok : batch_11_09_values.all id = true := by decide

def batch_11_10_values : List Bool := [accepted_576]
theorem batch_11_10_ok : batch_11_10_values.all id = true := by decide

def batch_11_11_values : List Bool := [accepted_580]
theorem batch_11_11_ok : batch_11_11_values.all id = true := by decide

def batch_11_12_values : List Bool := [accepted_582]
theorem batch_11_12_ok : batch_11_12_values.all id = true := by decide

def batch_11_13_values : List Bool := [accepted_584]
theorem batch_11_13_ok : batch_11_13_values.all id = true := by decide

def batch_11_14_values : List Bool := [accepted_588]
theorem batch_11_14_ok : batch_11_14_values.all id = true := by decide

def batch_11_15_values : List Bool := [accepted_591]
theorem batch_11_15_ok : batch_11_15_values.all id = true := by decide

def batch_11_16_values : List Bool := [accepted_596]
theorem batch_11_16_ok : batch_11_16_values.all id = true := by decide

def batch_11_17_values : List Bool := [accepted_597]
theorem batch_11_17_ok : batch_11_17_values.all id = true := by decide

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

theorem leaf_560_ok : checkAt 527 1000 box_560 cert_560 = true := by
  have h := List.all_eq_true.mp batch_11_04_ok accepted_560 (by simp [batch_11_04_values])
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
  have h := List.all_eq_true.mp batch_11_05_ok accepted_561 (by simp [batch_11_05_values])
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

theorem leaf_563_ok : checkAt 527 1000 box_563 cert_563 = true := by
  have h := List.all_eq_true.mp batch_11_06_ok accepted_563 (by simp [batch_11_06_values])
  exact h
theorem leaf_563_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_563.profileLo box_563.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_563_ok
theorem branch_box_563_nonnegative : ∀ j, 0 ≤ branch_box_563.lower j ∧ 0 ≤ branch_box_563.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_563, Box.profileLo, Box.profileHi, box_563]
theorem leaf_563_BranchSafe : CertificateConsequences.BranchSafe branch_box_563 := by
  left; refine ⟨branch_box_563_nonnegative, ?_⟩
  intro z hz; exact leaf_563_sound hz

theorem leaf_565_ok : checkAt 527 1000 box_565 cert_565 = true := by
  have h := List.all_eq_true.mp batch_11_07_ok accepted_565 (by simp [batch_11_07_values])
  exact h
theorem leaf_565_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_565.profileLo box_565.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_565_ok
theorem branch_box_565_nonnegative : ∀ j, 0 ≤ branch_box_565.lower j ∧ 0 ≤ branch_box_565.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_565, Box.profileLo, Box.profileHi, box_565]
theorem leaf_565_BranchSafe : CertificateConsequences.BranchSafe branch_box_565 := by
  left; refine ⟨branch_box_565_nonnegative, ?_⟩
  intro z hz; exact leaf_565_sound hz

theorem leaf_572_ok : checkAt 527 1000 box_572 cert_572 = true := by
  have h := List.all_eq_true.mp batch_11_08_ok accepted_572 (by simp [batch_11_08_values])
  exact h
theorem leaf_572_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_572.profileLo box_572.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_572_ok
theorem branch_box_572_nonnegative : ∀ j, 0 ≤ branch_box_572.lower j ∧ 0 ≤ branch_box_572.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_572, Box.profileLo, Box.profileHi, box_572]
theorem leaf_572_BranchSafe : CertificateConsequences.BranchSafe branch_box_572 := by
  left; refine ⟨branch_box_572_nonnegative, ?_⟩
  intro z hz; exact leaf_572_sound hz

theorem leaf_574_ok : checkAt 527 1000 box_574 cert_574 = true := by
  have h := List.all_eq_true.mp batch_11_09_ok accepted_574 (by simp [batch_11_09_values])
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

theorem leaf_576_ok : checkAt 527 1000 box_576 cert_576 = true := by
  have h := List.all_eq_true.mp batch_11_10_ok accepted_576 (by simp [batch_11_10_values])
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

theorem leaf_580_ok : checkAt 527 1000 box_580 cert_580 = true := by
  have h := List.all_eq_true.mp batch_11_11_ok accepted_580 (by simp [batch_11_11_values])
  exact h
theorem leaf_580_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_580.profileLo box_580.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_580_ok
theorem branch_box_580_nonnegative : ∀ j, 0 ≤ branch_box_580.lower j ∧ 0 ≤ branch_box_580.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_580, Box.profileLo, Box.profileHi, box_580]
theorem leaf_580_BranchSafe : CertificateConsequences.BranchSafe branch_box_580 := by
  left; refine ⟨branch_box_580_nonnegative, ?_⟩
  intro z hz; exact leaf_580_sound hz

theorem leaf_582_ok : checkAt 527 1000 box_582 cert_582 = true := by
  have h := List.all_eq_true.mp batch_11_12_ok accepted_582 (by simp [batch_11_12_values])
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

theorem leaf_584_ok : checkAt 527 1000 box_584 cert_584 = true := by
  have h := List.all_eq_true.mp batch_11_13_ok accepted_584 (by simp [batch_11_13_values])
  exact h
theorem leaf_584_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_584.profileLo box_584.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_584_ok
theorem branch_box_584_nonnegative : ∀ j, 0 ≤ branch_box_584.lower j ∧ 0 ≤ branch_box_584.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_584, Box.profileLo, Box.profileHi, box_584]
theorem leaf_584_BranchSafe : CertificateConsequences.BranchSafe branch_box_584 := by
  left; refine ⟨branch_box_584_nonnegative, ?_⟩
  intro z hz; exact leaf_584_sound hz

theorem leaf_588_ok : checkAt 527 1000 box_588 cert_588 = true := by
  have h := List.all_eq_true.mp batch_11_14_ok accepted_588 (by simp [batch_11_14_values])
  exact h
theorem leaf_588_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_588.profileLo box_588.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_588_ok
theorem branch_box_588_nonnegative : ∀ j, 0 ≤ branch_box_588.lower j ∧ 0 ≤ branch_box_588.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_588, Box.profileLo, Box.profileHi, box_588]
theorem leaf_588_BranchSafe : CertificateConsequences.BranchSafe branch_box_588 := by
  left; refine ⟨branch_box_588_nonnegative, ?_⟩
  intro z hz; exact leaf_588_sound hz

theorem leaf_591_ok : checkAt 527 1000 box_591 cert_591 = true := by
  have h := List.all_eq_true.mp batch_11_15_ok accepted_591 (by simp [batch_11_15_values])
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

theorem leaf_596_ok : checkAt 527 1000 box_596 cert_596 = true := by
  have h := List.all_eq_true.mp batch_11_16_ok accepted_596 (by simp [batch_11_16_values])
  exact h
theorem leaf_596_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_596.profileLo box_596.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_596_ok
theorem branch_box_596_nonnegative : ∀ j, 0 ≤ branch_box_596.lower j ∧ 0 ≤ branch_box_596.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_596, Box.profileLo, Box.profileHi, box_596]
theorem leaf_596_BranchSafe : CertificateConsequences.BranchSafe branch_box_596 := by
  left; refine ⟨branch_box_596_nonnegative, ?_⟩
  intro z hz; exact leaf_596_sound hz

theorem leaf_597_ok : checkAt 527 1000 box_597 cert_597 = true := by
  have h := List.all_eq_true.mp batch_11_17_ok accepted_597 (by simp [batch_11_17_values])
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

#print axioms batch_11_00_ok
#print axioms leaf_552_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
