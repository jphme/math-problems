import PeaceableQueens.UpperBound.Generated.Even.CoreScaled31Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_31_00_values : List Bool := [accepted_1551]
theorem batch_31_00_ok : batch_31_00_values.all id = true := by decide

def batch_31_01_values : List Bool := [accepted_1553]
theorem batch_31_01_ok : batch_31_01_values.all id = true := by decide

def batch_31_02_values : List Bool := [accepted_1555]
theorem batch_31_02_ok : batch_31_02_values.all id = true := by decide

def batch_31_03_values : List Bool := [accepted_1557]
theorem batch_31_03_ok : batch_31_03_values.all id = true := by decide

def batch_31_04_values : List Bool := [accepted_1559]
theorem batch_31_04_ok : batch_31_04_values.all id = true := by decide

def batch_31_05_values : List Bool := [accepted_1561]
theorem batch_31_05_ok : batch_31_05_values.all id = true := by decide

def batch_31_06_values : List Bool := [accepted_1564]
theorem batch_31_06_ok : batch_31_06_values.all id = true := by decide

def batch_31_07_values : List Bool := [accepted_1569]
theorem batch_31_07_ok : batch_31_07_values.all id = true := by decide

def batch_31_08_values : List Bool := [accepted_1571]
theorem batch_31_08_ok : batch_31_08_values.all id = true := by decide

def batch_31_09_values : List Bool := [accepted_1573]
theorem batch_31_09_ok : batch_31_09_values.all id = true := by decide

def batch_31_10_values : List Bool := [accepted_1577]
theorem batch_31_10_ok : batch_31_10_values.all id = true := by decide

def batch_31_11_values : List Bool := [accepted_1579]
theorem batch_31_11_ok : batch_31_11_values.all id = true := by decide

def batch_31_12_values : List Bool := [accepted_1581]
theorem batch_31_12_ok : batch_31_12_values.all id = true := by decide

def batch_31_13_values : List Bool := [accepted_1583]
theorem batch_31_13_ok : batch_31_13_values.all id = true := by decide

def batch_31_14_values : List Bool := [accepted_1585]
theorem batch_31_14_ok : batch_31_14_values.all id = true := by decide

def batch_31_15_values : List Bool := [accepted_1587]
theorem batch_31_15_ok : batch_31_15_values.all id = true := by decide

def batch_31_16_values : List Bool := [accepted_1594]
theorem batch_31_16_ok : batch_31_16_values.all id = true := by decide

def batch_31_17_values : List Bool := [accepted_1596]
theorem batch_31_17_ok : batch_31_17_values.all id = true := by decide

theorem leaf_1551_ok : checkAt 527 1000 box_1551 cert_1551 = true := by
  have h := List.all_eq_true.mp batch_31_00_ok accepted_1551 (by simp [batch_31_00_values])
  exact h
theorem leaf_1551_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1551.profileLo box_1551.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1551_ok
theorem branch_box_1551_nonnegative : ∀ j, 0 ≤ branch_box_1551.lower j ∧ 0 ≤ branch_box_1551.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1551, Box.profileLo, Box.profileHi, box_1551]
theorem leaf_1551_BranchSafe : CertificateConsequences.BranchSafe branch_box_1551 := by
  left; refine ⟨branch_box_1551_nonnegative, ?_⟩
  intro z hz; exact leaf_1551_sound hz

theorem leaf_1553_ok : checkAt 527 1000 box_1553 cert_1553 = true := by
  have h := List.all_eq_true.mp batch_31_01_ok accepted_1553 (by simp [batch_31_01_values])
  exact h
theorem leaf_1553_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1553.profileLo box_1553.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1553_ok
theorem branch_box_1553_nonnegative : ∀ j, 0 ≤ branch_box_1553.lower j ∧ 0 ≤ branch_box_1553.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1553, Box.profileLo, Box.profileHi, box_1553]
theorem leaf_1553_BranchSafe : CertificateConsequences.BranchSafe branch_box_1553 := by
  left; refine ⟨branch_box_1553_nonnegative, ?_⟩
  intro z hz; exact leaf_1553_sound hz

theorem leaf_1555_ok : checkAt 527 1000 box_1555 cert_1555 = true := by
  have h := List.all_eq_true.mp batch_31_02_ok accepted_1555 (by simp [batch_31_02_values])
  exact h
theorem leaf_1555_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1555.profileLo box_1555.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1555_ok
theorem branch_box_1555_nonnegative : ∀ j, 0 ≤ branch_box_1555.lower j ∧ 0 ≤ branch_box_1555.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1555, Box.profileLo, Box.profileHi, box_1555]
theorem leaf_1555_BranchSafe : CertificateConsequences.BranchSafe branch_box_1555 := by
  left; refine ⟨branch_box_1555_nonnegative, ?_⟩
  intro z hz; exact leaf_1555_sound hz

theorem leaf_1557_ok : checkAt 527 1000 box_1557 cert_1557 = true := by
  have h := List.all_eq_true.mp batch_31_03_ok accepted_1557 (by simp [batch_31_03_values])
  exact h
theorem leaf_1557_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1557.profileLo box_1557.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1557_ok
theorem branch_box_1557_nonnegative : ∀ j, 0 ≤ branch_box_1557.lower j ∧ 0 ≤ branch_box_1557.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1557, Box.profileLo, Box.profileHi, box_1557]
theorem leaf_1557_BranchSafe : CertificateConsequences.BranchSafe branch_box_1557 := by
  left; refine ⟨branch_box_1557_nonnegative, ?_⟩
  intro z hz; exact leaf_1557_sound hz

theorem leaf_1559_ok : checkAt 527 1000 box_1559 cert_1559 = true := by
  have h := List.all_eq_true.mp batch_31_04_ok accepted_1559 (by simp [batch_31_04_values])
  exact h
theorem leaf_1559_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1559.profileLo box_1559.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1559_ok
theorem branch_box_1559_nonnegative : ∀ j, 0 ≤ branch_box_1559.lower j ∧ 0 ≤ branch_box_1559.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1559, Box.profileLo, Box.profileHi, box_1559]
theorem leaf_1559_BranchSafe : CertificateConsequences.BranchSafe branch_box_1559 := by
  left; refine ⟨branch_box_1559_nonnegative, ?_⟩
  intro z hz; exact leaf_1559_sound hz

theorem leaf_1561_ok : checkAt 527 1000 box_1561 cert_1561 = true := by
  have h := List.all_eq_true.mp batch_31_05_ok accepted_1561 (by simp [batch_31_05_values])
  exact h
theorem leaf_1561_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1561.profileLo box_1561.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1561_ok
theorem branch_box_1561_nonnegative : ∀ j, 0 ≤ branch_box_1561.lower j ∧ 0 ≤ branch_box_1561.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1561, Box.profileLo, Box.profileHi, box_1561]
theorem leaf_1561_BranchSafe : CertificateConsequences.BranchSafe branch_box_1561 := by
  left; refine ⟨branch_box_1561_nonnegative, ?_⟩
  intro z hz; exact leaf_1561_sound hz

theorem leaf_1564_ok : checkAt 527 1000 box_1564 cert_1564 = true := by
  have h := List.all_eq_true.mp batch_31_06_ok accepted_1564 (by simp [batch_31_06_values])
  exact h
theorem leaf_1564_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1564.profileLo box_1564.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1564_ok
theorem branch_box_1564_nonnegative : ∀ j, 0 ≤ branch_box_1564.lower j ∧ 0 ≤ branch_box_1564.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1564, Box.profileLo, Box.profileHi, box_1564]
theorem leaf_1564_BranchSafe : CertificateConsequences.BranchSafe branch_box_1564 := by
  left; refine ⟨branch_box_1564_nonnegative, ?_⟩
  intro z hz; exact leaf_1564_sound hz

theorem leaf_1569_ok : checkAt 527 1000 box_1569 cert_1569 = true := by
  have h := List.all_eq_true.mp batch_31_07_ok accepted_1569 (by simp [batch_31_07_values])
  exact h
theorem leaf_1569_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1569.profileLo box_1569.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1569_ok
theorem branch_box_1569_nonnegative : ∀ j, 0 ≤ branch_box_1569.lower j ∧ 0 ≤ branch_box_1569.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1569, Box.profileLo, Box.profileHi, box_1569]
theorem leaf_1569_BranchSafe : CertificateConsequences.BranchSafe branch_box_1569 := by
  left; refine ⟨branch_box_1569_nonnegative, ?_⟩
  intro z hz; exact leaf_1569_sound hz

theorem leaf_1571_ok : checkAt 527 1000 box_1571 cert_1571 = true := by
  have h := List.all_eq_true.mp batch_31_08_ok accepted_1571 (by simp [batch_31_08_values])
  exact h
theorem leaf_1571_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1571.profileLo box_1571.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1571_ok
theorem branch_box_1571_nonnegative : ∀ j, 0 ≤ branch_box_1571.lower j ∧ 0 ≤ branch_box_1571.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1571, Box.profileLo, Box.profileHi, box_1571]
theorem leaf_1571_BranchSafe : CertificateConsequences.BranchSafe branch_box_1571 := by
  left; refine ⟨branch_box_1571_nonnegative, ?_⟩
  intro z hz; exact leaf_1571_sound hz

theorem leaf_1573_ok : checkAt 527 1000 box_1573 cert_1573 = true := by
  have h := List.all_eq_true.mp batch_31_09_ok accepted_1573 (by simp [batch_31_09_values])
  exact h
theorem leaf_1573_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1573.profileLo box_1573.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1573_ok
theorem branch_box_1573_nonnegative : ∀ j, 0 ≤ branch_box_1573.lower j ∧ 0 ≤ branch_box_1573.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1573, Box.profileLo, Box.profileHi, box_1573]
theorem leaf_1573_BranchSafe : CertificateConsequences.BranchSafe branch_box_1573 := by
  left; refine ⟨branch_box_1573_nonnegative, ?_⟩
  intro z hz; exact leaf_1573_sound hz

theorem leaf_1577_ok : checkAt 527 1000 box_1577 cert_1577 = true := by
  have h := List.all_eq_true.mp batch_31_10_ok accepted_1577 (by simp [batch_31_10_values])
  exact h
theorem leaf_1577_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1577.profileLo box_1577.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1577_ok
theorem branch_box_1577_nonnegative : ∀ j, 0 ≤ branch_box_1577.lower j ∧ 0 ≤ branch_box_1577.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1577, Box.profileLo, Box.profileHi, box_1577]
theorem leaf_1577_BranchSafe : CertificateConsequences.BranchSafe branch_box_1577 := by
  left; refine ⟨branch_box_1577_nonnegative, ?_⟩
  intro z hz; exact leaf_1577_sound hz

theorem leaf_1579_ok : checkAt 527 1000 box_1579 cert_1579 = true := by
  have h := List.all_eq_true.mp batch_31_11_ok accepted_1579 (by simp [batch_31_11_values])
  exact h
theorem leaf_1579_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1579.profileLo box_1579.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1579_ok
theorem branch_box_1579_nonnegative : ∀ j, 0 ≤ branch_box_1579.lower j ∧ 0 ≤ branch_box_1579.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1579, Box.profileLo, Box.profileHi, box_1579]
theorem leaf_1579_BranchSafe : CertificateConsequences.BranchSafe branch_box_1579 := by
  left; refine ⟨branch_box_1579_nonnegative, ?_⟩
  intro z hz; exact leaf_1579_sound hz

theorem leaf_1581_ok : checkAt 527 1000 box_1581 cert_1581 = true := by
  have h := List.all_eq_true.mp batch_31_12_ok accepted_1581 (by simp [batch_31_12_values])
  exact h
theorem leaf_1581_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1581.profileLo box_1581.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1581_ok
theorem branch_box_1581_nonnegative : ∀ j, 0 ≤ branch_box_1581.lower j ∧ 0 ≤ branch_box_1581.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1581, Box.profileLo, Box.profileHi, box_1581]
theorem leaf_1581_BranchSafe : CertificateConsequences.BranchSafe branch_box_1581 := by
  left; refine ⟨branch_box_1581_nonnegative, ?_⟩
  intro z hz; exact leaf_1581_sound hz

theorem leaf_1583_ok : checkAt 527 1000 box_1583 cert_1583 = true := by
  have h := List.all_eq_true.mp batch_31_13_ok accepted_1583 (by simp [batch_31_13_values])
  exact h
theorem leaf_1583_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1583.profileLo box_1583.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1583_ok
theorem branch_box_1583_nonnegative : ∀ j, 0 ≤ branch_box_1583.lower j ∧ 0 ≤ branch_box_1583.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1583, Box.profileLo, Box.profileHi, box_1583]
theorem leaf_1583_BranchSafe : CertificateConsequences.BranchSafe branch_box_1583 := by
  left; refine ⟨branch_box_1583_nonnegative, ?_⟩
  intro z hz; exact leaf_1583_sound hz

theorem leaf_1585_ok : checkAt 527 1000 box_1585 cert_1585 = true := by
  have h := List.all_eq_true.mp batch_31_14_ok accepted_1585 (by simp [batch_31_14_values])
  exact h
theorem leaf_1585_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1585.profileLo box_1585.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1585_ok
theorem branch_box_1585_nonnegative : ∀ j, 0 ≤ branch_box_1585.lower j ∧ 0 ≤ branch_box_1585.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1585, Box.profileLo, Box.profileHi, box_1585]
theorem leaf_1585_BranchSafe : CertificateConsequences.BranchSafe branch_box_1585 := by
  left; refine ⟨branch_box_1585_nonnegative, ?_⟩
  intro z hz; exact leaf_1585_sound hz

theorem leaf_1587_ok : checkAt 527 1000 box_1587 cert_1587 = true := by
  have h := List.all_eq_true.mp batch_31_15_ok accepted_1587 (by simp [batch_31_15_values])
  exact h
theorem leaf_1587_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1587.profileLo box_1587.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1587_ok
theorem branch_box_1587_nonnegative : ∀ j, 0 ≤ branch_box_1587.lower j ∧ 0 ≤ branch_box_1587.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1587, Box.profileLo, Box.profileHi, box_1587]
theorem leaf_1587_BranchSafe : CertificateConsequences.BranchSafe branch_box_1587 := by
  left; refine ⟨branch_box_1587_nonnegative, ?_⟩
  intro z hz; exact leaf_1587_sound hz

theorem leaf_1594_ok : checkAt 527 1000 box_1594 cert_1594 = true := by
  have h := List.all_eq_true.mp batch_31_16_ok accepted_1594 (by simp [batch_31_16_values])
  exact h
theorem leaf_1594_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1594.profileLo box_1594.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1594_ok
theorem branch_box_1594_nonnegative : ∀ j, 0 ≤ branch_box_1594.lower j ∧ 0 ≤ branch_box_1594.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1594, Box.profileLo, Box.profileHi, box_1594]
theorem leaf_1594_BranchSafe : CertificateConsequences.BranchSafe branch_box_1594 := by
  left; refine ⟨branch_box_1594_nonnegative, ?_⟩
  intro z hz; exact leaf_1594_sound hz

theorem leaf_1596_ok : checkAt 527 1000 box_1596 cert_1596 = true := by
  have h := List.all_eq_true.mp batch_31_17_ok accepted_1596 (by simp [batch_31_17_values])
  exact h
theorem leaf_1596_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1596.profileLo box_1596.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1596_ok
theorem branch_box_1596_nonnegative : ∀ j, 0 ≤ branch_box_1596.lower j ∧ 0 ≤ branch_box_1596.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1596, Box.profileLo, Box.profileHi, box_1596]
theorem leaf_1596_BranchSafe : CertificateConsequences.BranchSafe branch_box_1596 := by
  left; refine ⟨branch_box_1596_nonnegative, ?_⟩
  intro z hz; exact leaf_1596_sound hz

#print axioms batch_31_00_ok
#print axioms leaf_1551_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
