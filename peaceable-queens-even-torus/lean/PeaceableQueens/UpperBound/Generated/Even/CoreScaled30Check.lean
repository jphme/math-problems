import PeaceableQueens.UpperBound.Generated.Even.CoreScaled30Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_30_00_values : List Bool := [accepted_1504]
theorem batch_30_00_ok : batch_30_00_values.all id = true := by decide

def batch_30_01_values : List Bool := [accepted_1506]
theorem batch_30_01_ok : batch_30_01_values.all id = true := by decide

def batch_30_02_values : List Bool := [accepted_1514]
theorem batch_30_02_ok : batch_30_02_values.all id = true := by decide

def batch_30_03_values : List Bool := [accepted_1519]
theorem batch_30_03_ok : batch_30_03_values.all id = true := by decide

def batch_30_04_values : List Bool := [accepted_1521]
theorem batch_30_04_ok : batch_30_04_values.all id = true := by decide

def batch_30_05_values : List Bool := [accepted_1523]
theorem batch_30_05_ok : batch_30_05_values.all id = true := by decide

def batch_30_06_values : List Bool := [accepted_1526]
theorem batch_30_06_ok : batch_30_06_values.all id = true := by decide

def batch_30_07_values : List Bool := [accepted_1527]
theorem batch_30_07_ok : batch_30_07_values.all id = true := by decide

def batch_30_08_values : List Bool := [accepted_1529]
theorem batch_30_08_ok : batch_30_08_values.all id = true := by decide

def batch_30_09_values : List Bool := [accepted_1531]
theorem batch_30_09_ok : batch_30_09_values.all id = true := by decide

def batch_30_10_values : List Bool := [accepted_1533]
theorem batch_30_10_ok : batch_30_10_values.all id = true := by decide

def batch_30_11_values : List Bool := [accepted_1535]
theorem batch_30_11_ok : batch_30_11_values.all id = true := by decide

def batch_30_12_values : List Bool := [accepted_1539]
theorem batch_30_12_ok : batch_30_12_values.all id = true := by decide

def batch_30_13_values : List Bool := [accepted_1543]
theorem batch_30_13_ok : batch_30_13_values.all id = true := by decide

def batch_30_14_values : List Bool := [accepted_1545]
theorem batch_30_14_ok : batch_30_14_values.all id = true := by decide

def batch_30_15_values : List Bool := [accepted_1547]
theorem batch_30_15_ok : batch_30_15_values.all id = true := by decide

theorem leaf_1504_ok : checkAt 527 1000 box_1504 cert_1504 = true := by
  have h := List.all_eq_true.mp batch_30_00_ok accepted_1504 (by simp [batch_30_00_values])
  exact h
theorem leaf_1504_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1504.profileLo box_1504.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1504_ok
theorem branch_box_1504_nonnegative : ∀ j, 0 ≤ branch_box_1504.lower j ∧ 0 ≤ branch_box_1504.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1504, Box.profileLo, Box.profileHi, box_1504]
theorem leaf_1504_BranchSafe : CertificateConsequences.BranchSafe branch_box_1504 := by
  left; refine ⟨branch_box_1504_nonnegative, ?_⟩
  intro z hz; exact leaf_1504_sound hz

theorem leaf_1506_ok : checkAt 527 1000 box_1506 cert_1506 = true := by
  have h := List.all_eq_true.mp batch_30_01_ok accepted_1506 (by simp [batch_30_01_values])
  exact h
theorem leaf_1506_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1506.profileLo box_1506.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1506_ok
theorem branch_box_1506_nonnegative : ∀ j, 0 ≤ branch_box_1506.lower j ∧ 0 ≤ branch_box_1506.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1506, Box.profileLo, Box.profileHi, box_1506]
theorem leaf_1506_BranchSafe : CertificateConsequences.BranchSafe branch_box_1506 := by
  left; refine ⟨branch_box_1506_nonnegative, ?_⟩
  intro z hz; exact leaf_1506_sound hz

theorem leaf_1514_ok : checkAt 527 1000 box_1514 cert_1514 = true := by
  have h := List.all_eq_true.mp batch_30_02_ok accepted_1514 (by simp [batch_30_02_values])
  exact h
theorem leaf_1514_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1514.profileLo box_1514.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1514_ok
theorem branch_box_1514_nonnegative : ∀ j, 0 ≤ branch_box_1514.lower j ∧ 0 ≤ branch_box_1514.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1514, Box.profileLo, Box.profileHi, box_1514]
theorem leaf_1514_BranchSafe : CertificateConsequences.BranchSafe branch_box_1514 := by
  left; refine ⟨branch_box_1514_nonnegative, ?_⟩
  intro z hz; exact leaf_1514_sound hz

theorem leaf_1519_ok : checkAt 527 1000 box_1519 cert_1519 = true := by
  have h := List.all_eq_true.mp batch_30_03_ok accepted_1519 (by simp [batch_30_03_values])
  exact h
theorem leaf_1519_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1519.profileLo box_1519.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1519_ok
theorem branch_box_1519_nonnegative : ∀ j, 0 ≤ branch_box_1519.lower j ∧ 0 ≤ branch_box_1519.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1519, Box.profileLo, Box.profileHi, box_1519]
theorem leaf_1519_BranchSafe : CertificateConsequences.BranchSafe branch_box_1519 := by
  left; refine ⟨branch_box_1519_nonnegative, ?_⟩
  intro z hz; exact leaf_1519_sound hz

theorem leaf_1521_ok : checkAt 527 1000 box_1521 cert_1521 = true := by
  have h := List.all_eq_true.mp batch_30_04_ok accepted_1521 (by simp [batch_30_04_values])
  exact h
theorem leaf_1521_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1521.profileLo box_1521.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1521_ok
theorem branch_box_1521_nonnegative : ∀ j, 0 ≤ branch_box_1521.lower j ∧ 0 ≤ branch_box_1521.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1521, Box.profileLo, Box.profileHi, box_1521]
theorem leaf_1521_BranchSafe : CertificateConsequences.BranchSafe branch_box_1521 := by
  left; refine ⟨branch_box_1521_nonnegative, ?_⟩
  intro z hz; exact leaf_1521_sound hz

theorem leaf_1523_ok : checkAt 527 1000 box_1523 cert_1523 = true := by
  have h := List.all_eq_true.mp batch_30_05_ok accepted_1523 (by simp [batch_30_05_values])
  exact h
theorem leaf_1523_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1523.profileLo box_1523.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1523_ok
theorem branch_box_1523_nonnegative : ∀ j, 0 ≤ branch_box_1523.lower j ∧ 0 ≤ branch_box_1523.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1523, Box.profileLo, Box.profileHi, box_1523]
theorem leaf_1523_BranchSafe : CertificateConsequences.BranchSafe branch_box_1523 := by
  left; refine ⟨branch_box_1523_nonnegative, ?_⟩
  intro z hz; exact leaf_1523_sound hz

theorem leaf_1526_ok : checkAt 527 1000 box_1526 cert_1526 = true := by
  have h := List.all_eq_true.mp batch_30_06_ok accepted_1526 (by simp [batch_30_06_values])
  exact h
theorem leaf_1526_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1526.profileLo box_1526.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1526_ok
theorem branch_box_1526_nonnegative : ∀ j, 0 ≤ branch_box_1526.lower j ∧ 0 ≤ branch_box_1526.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1526, Box.profileLo, Box.profileHi, box_1526]
theorem leaf_1526_BranchSafe : CertificateConsequences.BranchSafe branch_box_1526 := by
  left; refine ⟨branch_box_1526_nonnegative, ?_⟩
  intro z hz; exact leaf_1526_sound hz

theorem leaf_1527_ok : checkAt 527 1000 box_1527 cert_1527 = true := by
  have h := List.all_eq_true.mp batch_30_07_ok accepted_1527 (by simp [batch_30_07_values])
  exact h
theorem leaf_1527_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1527.profileLo box_1527.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1527_ok
theorem branch_box_1527_nonnegative : ∀ j, 0 ≤ branch_box_1527.lower j ∧ 0 ≤ branch_box_1527.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1527, Box.profileLo, Box.profileHi, box_1527]
theorem leaf_1527_BranchSafe : CertificateConsequences.BranchSafe branch_box_1527 := by
  left; refine ⟨branch_box_1527_nonnegative, ?_⟩
  intro z hz; exact leaf_1527_sound hz

theorem leaf_1529_ok : checkAt 527 1000 box_1529 cert_1529 = true := by
  have h := List.all_eq_true.mp batch_30_08_ok accepted_1529 (by simp [batch_30_08_values])
  exact h
theorem leaf_1529_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1529.profileLo box_1529.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1529_ok
theorem branch_box_1529_nonnegative : ∀ j, 0 ≤ branch_box_1529.lower j ∧ 0 ≤ branch_box_1529.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1529, Box.profileLo, Box.profileHi, box_1529]
theorem leaf_1529_BranchSafe : CertificateConsequences.BranchSafe branch_box_1529 := by
  left; refine ⟨branch_box_1529_nonnegative, ?_⟩
  intro z hz; exact leaf_1529_sound hz

theorem leaf_1531_ok : checkAt 527 1000 box_1531 cert_1531 = true := by
  have h := List.all_eq_true.mp batch_30_09_ok accepted_1531 (by simp [batch_30_09_values])
  exact h
theorem leaf_1531_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1531.profileLo box_1531.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1531_ok
theorem branch_box_1531_nonnegative : ∀ j, 0 ≤ branch_box_1531.lower j ∧ 0 ≤ branch_box_1531.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1531, Box.profileLo, Box.profileHi, box_1531]
theorem leaf_1531_BranchSafe : CertificateConsequences.BranchSafe branch_box_1531 := by
  left; refine ⟨branch_box_1531_nonnegative, ?_⟩
  intro z hz; exact leaf_1531_sound hz

theorem leaf_1533_ok : checkAt 527 1000 box_1533 cert_1533 = true := by
  have h := List.all_eq_true.mp batch_30_10_ok accepted_1533 (by simp [batch_30_10_values])
  exact h
theorem leaf_1533_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1533.profileLo box_1533.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1533_ok
theorem branch_box_1533_nonnegative : ∀ j, 0 ≤ branch_box_1533.lower j ∧ 0 ≤ branch_box_1533.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1533, Box.profileLo, Box.profileHi, box_1533]
theorem leaf_1533_BranchSafe : CertificateConsequences.BranchSafe branch_box_1533 := by
  left; refine ⟨branch_box_1533_nonnegative, ?_⟩
  intro z hz; exact leaf_1533_sound hz

theorem leaf_1535_ok : checkAt 527 1000 box_1535 cert_1535 = true := by
  have h := List.all_eq_true.mp batch_30_11_ok accepted_1535 (by simp [batch_30_11_values])
  exact h
theorem leaf_1535_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1535.profileLo box_1535.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1535_ok
theorem branch_box_1535_nonnegative : ∀ j, 0 ≤ branch_box_1535.lower j ∧ 0 ≤ branch_box_1535.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1535, Box.profileLo, Box.profileHi, box_1535]
theorem leaf_1535_BranchSafe : CertificateConsequences.BranchSafe branch_box_1535 := by
  left; refine ⟨branch_box_1535_nonnegative, ?_⟩
  intro z hz; exact leaf_1535_sound hz

theorem leaf_1539_ok : checkAt 527 1000 box_1539 cert_1539 = true := by
  have h := List.all_eq_true.mp batch_30_12_ok accepted_1539 (by simp [batch_30_12_values])
  exact h
theorem leaf_1539_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1539.profileLo box_1539.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1539_ok
theorem branch_box_1539_nonnegative : ∀ j, 0 ≤ branch_box_1539.lower j ∧ 0 ≤ branch_box_1539.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1539, Box.profileLo, Box.profileHi, box_1539]
theorem leaf_1539_BranchSafe : CertificateConsequences.BranchSafe branch_box_1539 := by
  left; refine ⟨branch_box_1539_nonnegative, ?_⟩
  intro z hz; exact leaf_1539_sound hz

theorem leaf_1543_ok : checkAt 527 1000 box_1543 cert_1543 = true := by
  have h := List.all_eq_true.mp batch_30_13_ok accepted_1543 (by simp [batch_30_13_values])
  exact h
theorem leaf_1543_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1543.profileLo box_1543.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1543_ok
theorem branch_box_1543_nonnegative : ∀ j, 0 ≤ branch_box_1543.lower j ∧ 0 ≤ branch_box_1543.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1543, Box.profileLo, Box.profileHi, box_1543]
theorem leaf_1543_BranchSafe : CertificateConsequences.BranchSafe branch_box_1543 := by
  left; refine ⟨branch_box_1543_nonnegative, ?_⟩
  intro z hz; exact leaf_1543_sound hz

theorem leaf_1545_ok : checkAt 527 1000 box_1545 cert_1545 = true := by
  have h := List.all_eq_true.mp batch_30_14_ok accepted_1545 (by simp [batch_30_14_values])
  exact h
theorem leaf_1545_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1545.profileLo box_1545.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1545_ok
theorem branch_box_1545_nonnegative : ∀ j, 0 ≤ branch_box_1545.lower j ∧ 0 ≤ branch_box_1545.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1545, Box.profileLo, Box.profileHi, box_1545]
theorem leaf_1545_BranchSafe : CertificateConsequences.BranchSafe branch_box_1545 := by
  left; refine ⟨branch_box_1545_nonnegative, ?_⟩
  intro z hz; exact leaf_1545_sound hz

theorem leaf_1547_ok : checkAt 527 1000 box_1547 cert_1547 = true := by
  have h := List.all_eq_true.mp batch_30_15_ok accepted_1547 (by simp [batch_30_15_values])
  exact h
theorem leaf_1547_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1547.profileLo box_1547.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1547_ok
theorem branch_box_1547_nonnegative : ∀ j, 0 ≤ branch_box_1547.lower j ∧ 0 ≤ branch_box_1547.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1547, Box.profileLo, Box.profileHi, box_1547]
theorem leaf_1547_BranchSafe : CertificateConsequences.BranchSafe branch_box_1547 := by
  left; refine ⟨branch_box_1547_nonnegative, ?_⟩
  intro z hz; exact leaf_1547_sound hz

#print axioms batch_30_00_ok
#print axioms leaf_1504_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
