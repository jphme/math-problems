import PeaceableQueens.UpperBound.Generated.Even.C527Scaled31Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_31_00_values : List Bool := [accepted_1552]
theorem batch_31_00_ok : batch_31_00_values.all id = true := by decide

def batch_31_01_values : List Bool := [accepted_1553]
theorem batch_31_01_ok : batch_31_01_values.all id = true := by decide

def batch_31_02_values : List Bool := [accepted_1554]
theorem batch_31_02_ok : batch_31_02_values.all id = true := by decide

def batch_31_03_values : List Bool := [accepted_1559]
theorem batch_31_03_ok : batch_31_03_values.all id = true := by decide

def batch_31_04_values : List Bool := [accepted_1561]
theorem batch_31_04_ok : batch_31_04_values.all id = true := by decide

def batch_31_05_values : List Bool := [accepted_1562]
theorem batch_31_05_ok : batch_31_05_values.all id = true := by decide

def batch_31_06_values : List Bool := [accepted_1563]
theorem batch_31_06_ok : batch_31_06_values.all id = true := by decide

def batch_31_07_values : List Bool := [accepted_1566]
theorem batch_31_07_ok : batch_31_07_values.all id = true := by decide

def batch_31_08_values : List Bool := [accepted_1567]
theorem batch_31_08_ok : batch_31_08_values.all id = true := by decide

def batch_31_09_values : List Bool := [accepted_1568]
theorem batch_31_09_ok : batch_31_09_values.all id = true := by decide

def batch_31_10_values : List Bool := [accepted_1570]
theorem batch_31_10_ok : batch_31_10_values.all id = true := by decide

def batch_31_11_values : List Bool := [accepted_1571]
theorem batch_31_11_ok : batch_31_11_values.all id = true := by decide

def batch_31_12_values : List Bool := [accepted_1572]
theorem batch_31_12_ok : batch_31_12_values.all id = true := by decide

def batch_31_13_values : List Bool := [accepted_1574]
theorem batch_31_13_ok : batch_31_13_values.all id = true := by decide

def batch_31_14_values : List Bool := [accepted_1575]
theorem batch_31_14_ok : batch_31_14_values.all id = true := by decide

def batch_31_15_values : List Bool := [accepted_1578]
theorem batch_31_15_ok : batch_31_15_values.all id = true := by decide

def batch_31_16_values : List Bool := [accepted_1579]
theorem batch_31_16_ok : batch_31_16_values.all id = true := by decide

def batch_31_17_values : List Bool := [accepted_1580]
theorem batch_31_17_ok : batch_31_17_values.all id = true := by decide

def batch_31_18_values : List Bool := [accepted_1593]
theorem batch_31_18_ok : batch_31_18_values.all id = true := by decide

def batch_31_19_values : List Bool := [accepted_1594]
theorem batch_31_19_ok : batch_31_19_values.all id = true := by decide

def batch_31_20_values : List Bool := [accepted_1597]
theorem batch_31_20_ok : batch_31_20_values.all id = true := by decide

def batch_31_21_values : List Bool := [accepted_1598]
theorem batch_31_21_ok : batch_31_21_values.all id = true := by decide

def batch_31_22_values : List Bool := [accepted_1599]
theorem batch_31_22_ok : batch_31_22_values.all id = true := by decide

theorem leaf_1552_ok : checkAt 527 1000 box_1552 cert_1552 = true := by
  have h := List.all_eq_true.mp batch_31_00_ok accepted_1552 (by simp [batch_31_00_values])
  exact h
theorem leaf_1552_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1552.profileLo box_1552.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1552_ok
theorem branch_box_1552_nonnegative : ∀ j, 0 ≤ branch_box_1552.lower j ∧ 0 ≤ branch_box_1552.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1552, Box.profileLo, Box.profileHi, box_1552]
theorem leaf_1552_BranchSafe : CertificateConsequences.BranchSafe branch_box_1552 := by
  left; refine ⟨branch_box_1552_nonnegative, ?_⟩
  intro z hz; exact leaf_1552_sound hz

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

theorem leaf_1554_ok : checkAt 527 1000 box_1554 cert_1554 = true := by
  have h := List.all_eq_true.mp batch_31_02_ok accepted_1554 (by simp [batch_31_02_values])
  exact h
theorem leaf_1554_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1554.profileLo box_1554.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1554_ok
theorem branch_box_1554_nonnegative : ∀ j, 0 ≤ branch_box_1554.lower j ∧ 0 ≤ branch_box_1554.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1554, Box.profileLo, Box.profileHi, box_1554]
theorem leaf_1554_BranchSafe : CertificateConsequences.BranchSafe branch_box_1554 := by
  left; refine ⟨branch_box_1554_nonnegative, ?_⟩
  intro z hz; exact leaf_1554_sound hz

theorem leaf_1559_ok : checkAt 527 1000 box_1559 cert_1559 = true := by
  have h := List.all_eq_true.mp batch_31_03_ok accepted_1559 (by simp [batch_31_03_values])
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
  have h := List.all_eq_true.mp batch_31_04_ok accepted_1561 (by simp [batch_31_04_values])
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

theorem leaf_1562_ok : checkAt 527 1000 box_1562 cert_1562 = true := by
  have h := List.all_eq_true.mp batch_31_05_ok accepted_1562 (by simp [batch_31_05_values])
  exact h
theorem leaf_1562_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1562.profileLo box_1562.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1562_ok
theorem branch_box_1562_nonnegative : ∀ j, 0 ≤ branch_box_1562.lower j ∧ 0 ≤ branch_box_1562.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1562, Box.profileLo, Box.profileHi, box_1562]
theorem leaf_1562_BranchSafe : CertificateConsequences.BranchSafe branch_box_1562 := by
  left; refine ⟨branch_box_1562_nonnegative, ?_⟩
  intro z hz; exact leaf_1562_sound hz

theorem leaf_1563_ok : checkAt 527 1000 box_1563 cert_1563 = true := by
  have h := List.all_eq_true.mp batch_31_06_ok accepted_1563 (by simp [batch_31_06_values])
  exact h
theorem leaf_1563_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1563.profileLo box_1563.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1563_ok
theorem branch_box_1563_nonnegative : ∀ j, 0 ≤ branch_box_1563.lower j ∧ 0 ≤ branch_box_1563.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1563, Box.profileLo, Box.profileHi, box_1563]
theorem leaf_1563_BranchSafe : CertificateConsequences.BranchSafe branch_box_1563 := by
  left; refine ⟨branch_box_1563_nonnegative, ?_⟩
  intro z hz; exact leaf_1563_sound hz

theorem leaf_1566_ok : checkAt 527 1000 box_1566 cert_1566 = true := by
  have h := List.all_eq_true.mp batch_31_07_ok accepted_1566 (by simp [batch_31_07_values])
  exact h
theorem leaf_1566_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1566.profileLo box_1566.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1566_ok
theorem branch_box_1566_nonnegative : ∀ j, 0 ≤ branch_box_1566.lower j ∧ 0 ≤ branch_box_1566.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1566, Box.profileLo, Box.profileHi, box_1566]
theorem leaf_1566_BranchSafe : CertificateConsequences.BranchSafe branch_box_1566 := by
  left; refine ⟨branch_box_1566_nonnegative, ?_⟩
  intro z hz; exact leaf_1566_sound hz

theorem leaf_1567_ok : checkAt 527 1000 box_1567 cert_1567 = true := by
  have h := List.all_eq_true.mp batch_31_08_ok accepted_1567 (by simp [batch_31_08_values])
  exact h
theorem leaf_1567_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1567.profileLo box_1567.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1567_ok
theorem branch_box_1567_nonnegative : ∀ j, 0 ≤ branch_box_1567.lower j ∧ 0 ≤ branch_box_1567.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1567, Box.profileLo, Box.profileHi, box_1567]
theorem leaf_1567_BranchSafe : CertificateConsequences.BranchSafe branch_box_1567 := by
  left; refine ⟨branch_box_1567_nonnegative, ?_⟩
  intro z hz; exact leaf_1567_sound hz

theorem leaf_1568_ok : checkAt 527 1000 box_1568 cert_1568 = true := by
  have h := List.all_eq_true.mp batch_31_09_ok accepted_1568 (by simp [batch_31_09_values])
  exact h
theorem leaf_1568_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1568.profileLo box_1568.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1568_ok
theorem branch_box_1568_nonnegative : ∀ j, 0 ≤ branch_box_1568.lower j ∧ 0 ≤ branch_box_1568.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1568, Box.profileLo, Box.profileHi, box_1568]
theorem leaf_1568_BranchSafe : CertificateConsequences.BranchSafe branch_box_1568 := by
  left; refine ⟨branch_box_1568_nonnegative, ?_⟩
  intro z hz; exact leaf_1568_sound hz

theorem leaf_1570_ok : checkAt 527 1000 box_1570 cert_1570 = true := by
  have h := List.all_eq_true.mp batch_31_10_ok accepted_1570 (by simp [batch_31_10_values])
  exact h
theorem leaf_1570_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1570.profileLo box_1570.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1570_ok
theorem branch_box_1570_nonnegative : ∀ j, 0 ≤ branch_box_1570.lower j ∧ 0 ≤ branch_box_1570.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1570, Box.profileLo, Box.profileHi, box_1570]
theorem leaf_1570_BranchSafe : CertificateConsequences.BranchSafe branch_box_1570 := by
  left; refine ⟨branch_box_1570_nonnegative, ?_⟩
  intro z hz; exact leaf_1570_sound hz

theorem leaf_1571_ok : checkAt 527 1000 box_1571 cert_1571 = true := by
  have h := List.all_eq_true.mp batch_31_11_ok accepted_1571 (by simp [batch_31_11_values])
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

theorem leaf_1572_ok : checkAt 527 1000 box_1572 cert_1572 = true := by
  have h := List.all_eq_true.mp batch_31_12_ok accepted_1572 (by simp [batch_31_12_values])
  exact h
theorem leaf_1572_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1572.profileLo box_1572.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1572_ok
theorem branch_box_1572_nonnegative : ∀ j, 0 ≤ branch_box_1572.lower j ∧ 0 ≤ branch_box_1572.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1572, Box.profileLo, Box.profileHi, box_1572]
theorem leaf_1572_BranchSafe : CertificateConsequences.BranchSafe branch_box_1572 := by
  left; refine ⟨branch_box_1572_nonnegative, ?_⟩
  intro z hz; exact leaf_1572_sound hz

theorem leaf_1574_ok : checkAt 527 1000 box_1574 cert_1574 = true := by
  have h := List.all_eq_true.mp batch_31_13_ok accepted_1574 (by simp [batch_31_13_values])
  exact h
theorem leaf_1574_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1574.profileLo box_1574.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1574_ok
theorem branch_box_1574_nonnegative : ∀ j, 0 ≤ branch_box_1574.lower j ∧ 0 ≤ branch_box_1574.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1574, Box.profileLo, Box.profileHi, box_1574]
theorem leaf_1574_BranchSafe : CertificateConsequences.BranchSafe branch_box_1574 := by
  left; refine ⟨branch_box_1574_nonnegative, ?_⟩
  intro z hz; exact leaf_1574_sound hz

theorem leaf_1575_ok : checkAt 527 1000 box_1575 cert_1575 = true := by
  have h := List.all_eq_true.mp batch_31_14_ok accepted_1575 (by simp [batch_31_14_values])
  exact h
theorem leaf_1575_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1575.profileLo box_1575.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1575_ok
theorem branch_box_1575_nonnegative : ∀ j, 0 ≤ branch_box_1575.lower j ∧ 0 ≤ branch_box_1575.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1575, Box.profileLo, Box.profileHi, box_1575]
theorem leaf_1575_BranchSafe : CertificateConsequences.BranchSafe branch_box_1575 := by
  left; refine ⟨branch_box_1575_nonnegative, ?_⟩
  intro z hz; exact leaf_1575_sound hz

theorem leaf_1578_ok : checkAt 527 1000 box_1578 cert_1578 = true := by
  have h := List.all_eq_true.mp batch_31_15_ok accepted_1578 (by simp [batch_31_15_values])
  exact h
theorem leaf_1578_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1578.profileLo box_1578.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1578_ok
theorem branch_box_1578_nonnegative : ∀ j, 0 ≤ branch_box_1578.lower j ∧ 0 ≤ branch_box_1578.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1578, Box.profileLo, Box.profileHi, box_1578]
theorem leaf_1578_BranchSafe : CertificateConsequences.BranchSafe branch_box_1578 := by
  left; refine ⟨branch_box_1578_nonnegative, ?_⟩
  intro z hz; exact leaf_1578_sound hz

theorem leaf_1579_ok : checkAt 527 1000 box_1579 cert_1579 = true := by
  have h := List.all_eq_true.mp batch_31_16_ok accepted_1579 (by simp [batch_31_16_values])
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

theorem leaf_1580_ok : checkAt 527 1000 box_1580 cert_1580 = true := by
  have h := List.all_eq_true.mp batch_31_17_ok accepted_1580 (by simp [batch_31_17_values])
  exact h
theorem leaf_1580_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1580.profileLo box_1580.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1580_ok
theorem branch_box_1580_nonnegative : ∀ j, 0 ≤ branch_box_1580.lower j ∧ 0 ≤ branch_box_1580.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1580, Box.profileLo, Box.profileHi, box_1580]
theorem leaf_1580_BranchSafe : CertificateConsequences.BranchSafe branch_box_1580 := by
  left; refine ⟨branch_box_1580_nonnegative, ?_⟩
  intro z hz; exact leaf_1580_sound hz

theorem leaf_1593_ok : checkAt 527 1000 box_1593 cert_1593 = true := by
  have h := List.all_eq_true.mp batch_31_18_ok accepted_1593 (by simp [batch_31_18_values])
  exact h
theorem leaf_1593_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1593.profileLo box_1593.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1593_ok
theorem branch_box_1593_nonnegative : ∀ j, 0 ≤ branch_box_1593.lower j ∧ 0 ≤ branch_box_1593.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1593, Box.profileLo, Box.profileHi, box_1593]
theorem leaf_1593_BranchSafe : CertificateConsequences.BranchSafe branch_box_1593 := by
  left; refine ⟨branch_box_1593_nonnegative, ?_⟩
  intro z hz; exact leaf_1593_sound hz

theorem leaf_1594_ok : checkAt 527 1000 box_1594 cert_1594 = true := by
  have h := List.all_eq_true.mp batch_31_19_ok accepted_1594 (by simp [batch_31_19_values])
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

theorem leaf_1597_ok : checkAt 527 1000 box_1597 cert_1597 = true := by
  have h := List.all_eq_true.mp batch_31_20_ok accepted_1597 (by simp [batch_31_20_values])
  exact h
theorem leaf_1597_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1597.profileLo box_1597.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1597_ok
theorem branch_box_1597_nonnegative : ∀ j, 0 ≤ branch_box_1597.lower j ∧ 0 ≤ branch_box_1597.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1597, Box.profileLo, Box.profileHi, box_1597]
theorem leaf_1597_BranchSafe : CertificateConsequences.BranchSafe branch_box_1597 := by
  left; refine ⟨branch_box_1597_nonnegative, ?_⟩
  intro z hz; exact leaf_1597_sound hz

theorem leaf_1598_ok : checkAt 527 1000 box_1598 cert_1598 = true := by
  have h := List.all_eq_true.mp batch_31_21_ok accepted_1598 (by simp [batch_31_21_values])
  exact h
theorem leaf_1598_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1598.profileLo box_1598.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1598_ok
theorem branch_box_1598_nonnegative : ∀ j, 0 ≤ branch_box_1598.lower j ∧ 0 ≤ branch_box_1598.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1598, Box.profileLo, Box.profileHi, box_1598]
theorem leaf_1598_BranchSafe : CertificateConsequences.BranchSafe branch_box_1598 := by
  left; refine ⟨branch_box_1598_nonnegative, ?_⟩
  intro z hz; exact leaf_1598_sound hz

theorem leaf_1599_ok : checkAt 527 1000 box_1599 cert_1599 = true := by
  have h := List.all_eq_true.mp batch_31_22_ok accepted_1599 (by simp [batch_31_22_values])
  exact h
theorem leaf_1599_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1599.profileLo box_1599.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1599_ok
theorem branch_box_1599_nonnegative : ∀ j, 0 ≤ branch_box_1599.lower j ∧ 0 ≤ branch_box_1599.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1599, Box.profileLo, Box.profileHi, box_1599]
theorem leaf_1599_BranchSafe : CertificateConsequences.BranchSafe branch_box_1599 := by
  left; refine ⟨branch_box_1599_nonnegative, ?_⟩
  intro z hz; exact leaf_1599_sound hz

#print axioms batch_31_00_ok
#print axioms leaf_1552_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
