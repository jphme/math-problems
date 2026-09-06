import PeaceableQueens.UpperBound.Generated.Even.CoreScaled29Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_29_00_values : List Bool := [accepted_1456]
theorem batch_29_00_ok : batch_29_00_values.all id = true := by decide

def batch_29_01_values : List Bool := [accepted_1457]
theorem batch_29_01_ok : batch_29_01_values.all id = true := by decide

def batch_29_02_values : List Bool := [accepted_1460]
theorem batch_29_02_ok : batch_29_02_values.all id = true := by decide

def batch_29_03_values : List Bool := [accepted_1462]
theorem batch_29_03_ok : batch_29_03_values.all id = true := by decide

def batch_29_04_values : List Bool := [accepted_1463]
theorem batch_29_04_ok : batch_29_04_values.all id = true := by decide

def batch_29_05_values : List Bool := [accepted_1466]
theorem batch_29_05_ok : batch_29_05_values.all id = true := by decide

def batch_29_06_values : List Bool := [accepted_1468]
theorem batch_29_06_ok : batch_29_06_values.all id = true := by decide

def batch_29_07_values : List Bool := [accepted_1469]
theorem batch_29_07_ok : batch_29_07_values.all id = true := by decide

def batch_29_08_values : List Bool := [accepted_1472]
theorem batch_29_08_ok : batch_29_08_values.all id = true := by decide

def batch_29_09_values : List Bool := [accepted_1474]
theorem batch_29_09_ok : batch_29_09_values.all id = true := by decide

def batch_29_10_values : List Bool := [accepted_1476]
theorem batch_29_10_ok : batch_29_10_values.all id = true := by decide

def batch_29_11_values : List Bool := [accepted_1480]
theorem batch_29_11_ok : batch_29_11_values.all id = true := by decide

def batch_29_12_values : List Bool := [accepted_1481]
theorem batch_29_12_ok : batch_29_12_values.all id = true := by decide

def batch_29_13_values : List Bool := [accepted_1484]
theorem batch_29_13_ok : batch_29_13_values.all id = true := by decide

def batch_29_14_values : List Bool := [accepted_1486]
theorem batch_29_14_ok : batch_29_14_values.all id = true := by decide

def batch_29_15_values : List Bool := [accepted_1488]
theorem batch_29_15_ok : batch_29_15_values.all id = true := by decide

def batch_29_16_values : List Bool := [accepted_1490]
theorem batch_29_16_ok : batch_29_16_values.all id = true := by decide

def batch_29_17_values : List Bool := [accepted_1491]
theorem batch_29_17_ok : batch_29_17_values.all id = true := by decide

def batch_29_18_values : List Bool := [accepted_1494]
theorem batch_29_18_ok : batch_29_18_values.all id = true := by decide

def batch_29_19_values : List Bool := [accepted_1496]
theorem batch_29_19_ok : batch_29_19_values.all id = true := by decide

def batch_29_20_values : List Bool := [accepted_1498]
theorem batch_29_20_ok : batch_29_20_values.all id = true := by decide

theorem leaf_1456_ok : checkAt 527 1000 box_1456 cert_1456 = true := by
  have h := List.all_eq_true.mp batch_29_00_ok accepted_1456 (by simp [batch_29_00_values])
  exact h
theorem leaf_1456_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1456.profileLo box_1456.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1456_ok
theorem branch_box_1456_nonnegative : ∀ j, 0 ≤ branch_box_1456.lower j ∧ 0 ≤ branch_box_1456.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1456, Box.profileLo, Box.profileHi, box_1456]
theorem leaf_1456_BranchSafe : CertificateConsequences.BranchSafe branch_box_1456 := by
  left; refine ⟨branch_box_1456_nonnegative, ?_⟩
  intro z hz; exact leaf_1456_sound hz

theorem leaf_1457_ok : checkAt 527 1000 box_1457 cert_1457 = true := by
  have h := List.all_eq_true.mp batch_29_01_ok accepted_1457 (by simp [batch_29_01_values])
  exact h
theorem leaf_1457_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1457.profileLo box_1457.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1457_ok
theorem branch_box_1457_nonnegative : ∀ j, 0 ≤ branch_box_1457.lower j ∧ 0 ≤ branch_box_1457.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1457, Box.profileLo, Box.profileHi, box_1457]
theorem leaf_1457_BranchSafe : CertificateConsequences.BranchSafe branch_box_1457 := by
  left; refine ⟨branch_box_1457_nonnegative, ?_⟩
  intro z hz; exact leaf_1457_sound hz

theorem leaf_1460_ok : checkAt 527 1000 box_1460 cert_1460 = true := by
  have h := List.all_eq_true.mp batch_29_02_ok accepted_1460 (by simp [batch_29_02_values])
  exact h
theorem leaf_1460_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1460.profileLo box_1460.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1460_ok
theorem branch_box_1460_nonnegative : ∀ j, 0 ≤ branch_box_1460.lower j ∧ 0 ≤ branch_box_1460.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1460, Box.profileLo, Box.profileHi, box_1460]
theorem leaf_1460_BranchSafe : CertificateConsequences.BranchSafe branch_box_1460 := by
  left; refine ⟨branch_box_1460_nonnegative, ?_⟩
  intro z hz; exact leaf_1460_sound hz

theorem leaf_1462_ok : checkAt 527 1000 box_1462 cert_1462 = true := by
  have h := List.all_eq_true.mp batch_29_03_ok accepted_1462 (by simp [batch_29_03_values])
  exact h
theorem leaf_1462_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1462.profileLo box_1462.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1462_ok
theorem branch_box_1462_nonnegative : ∀ j, 0 ≤ branch_box_1462.lower j ∧ 0 ≤ branch_box_1462.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1462, Box.profileLo, Box.profileHi, box_1462]
theorem leaf_1462_BranchSafe : CertificateConsequences.BranchSafe branch_box_1462 := by
  left; refine ⟨branch_box_1462_nonnegative, ?_⟩
  intro z hz; exact leaf_1462_sound hz

theorem leaf_1463_ok : checkAt 527 1000 box_1463 cert_1463 = true := by
  have h := List.all_eq_true.mp batch_29_04_ok accepted_1463 (by simp [batch_29_04_values])
  exact h
theorem leaf_1463_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1463.profileLo box_1463.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1463_ok
theorem branch_box_1463_nonnegative : ∀ j, 0 ≤ branch_box_1463.lower j ∧ 0 ≤ branch_box_1463.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1463, Box.profileLo, Box.profileHi, box_1463]
theorem leaf_1463_BranchSafe : CertificateConsequences.BranchSafe branch_box_1463 := by
  left; refine ⟨branch_box_1463_nonnegative, ?_⟩
  intro z hz; exact leaf_1463_sound hz

theorem leaf_1466_ok : checkAt 527 1000 box_1466 cert_1466 = true := by
  have h := List.all_eq_true.mp batch_29_05_ok accepted_1466 (by simp [batch_29_05_values])
  exact h
theorem leaf_1466_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1466.profileLo box_1466.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1466_ok
theorem branch_box_1466_nonnegative : ∀ j, 0 ≤ branch_box_1466.lower j ∧ 0 ≤ branch_box_1466.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1466, Box.profileLo, Box.profileHi, box_1466]
theorem leaf_1466_BranchSafe : CertificateConsequences.BranchSafe branch_box_1466 := by
  left; refine ⟨branch_box_1466_nonnegative, ?_⟩
  intro z hz; exact leaf_1466_sound hz

theorem leaf_1468_ok : checkAt 527 1000 box_1468 cert_1468 = true := by
  have h := List.all_eq_true.mp batch_29_06_ok accepted_1468 (by simp [batch_29_06_values])
  exact h
theorem leaf_1468_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1468.profileLo box_1468.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1468_ok
theorem branch_box_1468_nonnegative : ∀ j, 0 ≤ branch_box_1468.lower j ∧ 0 ≤ branch_box_1468.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1468, Box.profileLo, Box.profileHi, box_1468]
theorem leaf_1468_BranchSafe : CertificateConsequences.BranchSafe branch_box_1468 := by
  left; refine ⟨branch_box_1468_nonnegative, ?_⟩
  intro z hz; exact leaf_1468_sound hz

theorem leaf_1469_ok : checkAt 527 1000 box_1469 cert_1469 = true := by
  have h := List.all_eq_true.mp batch_29_07_ok accepted_1469 (by simp [batch_29_07_values])
  exact h
theorem leaf_1469_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1469.profileLo box_1469.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1469_ok
theorem branch_box_1469_nonnegative : ∀ j, 0 ≤ branch_box_1469.lower j ∧ 0 ≤ branch_box_1469.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1469, Box.profileLo, Box.profileHi, box_1469]
theorem leaf_1469_BranchSafe : CertificateConsequences.BranchSafe branch_box_1469 := by
  left; refine ⟨branch_box_1469_nonnegative, ?_⟩
  intro z hz; exact leaf_1469_sound hz

theorem leaf_1472_ok : checkAt 527 1000 box_1472 cert_1472 = true := by
  have h := List.all_eq_true.mp batch_29_08_ok accepted_1472 (by simp [batch_29_08_values])
  exact h
theorem leaf_1472_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1472.profileLo box_1472.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1472_ok
theorem branch_box_1472_nonnegative : ∀ j, 0 ≤ branch_box_1472.lower j ∧ 0 ≤ branch_box_1472.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1472, Box.profileLo, Box.profileHi, box_1472]
theorem leaf_1472_BranchSafe : CertificateConsequences.BranchSafe branch_box_1472 := by
  left; refine ⟨branch_box_1472_nonnegative, ?_⟩
  intro z hz; exact leaf_1472_sound hz

theorem leaf_1474_ok : checkAt 527 1000 box_1474 cert_1474 = true := by
  have h := List.all_eq_true.mp batch_29_09_ok accepted_1474 (by simp [batch_29_09_values])
  exact h
theorem leaf_1474_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1474.profileLo box_1474.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1474_ok
theorem branch_box_1474_nonnegative : ∀ j, 0 ≤ branch_box_1474.lower j ∧ 0 ≤ branch_box_1474.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1474, Box.profileLo, Box.profileHi, box_1474]
theorem leaf_1474_BranchSafe : CertificateConsequences.BranchSafe branch_box_1474 := by
  left; refine ⟨branch_box_1474_nonnegative, ?_⟩
  intro z hz; exact leaf_1474_sound hz

theorem leaf_1476_ok : checkAt 527 1000 box_1476 cert_1476 = true := by
  have h := List.all_eq_true.mp batch_29_10_ok accepted_1476 (by simp [batch_29_10_values])
  exact h
theorem leaf_1476_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1476.profileLo box_1476.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1476_ok
theorem branch_box_1476_nonnegative : ∀ j, 0 ≤ branch_box_1476.lower j ∧ 0 ≤ branch_box_1476.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1476, Box.profileLo, Box.profileHi, box_1476]
theorem leaf_1476_BranchSafe : CertificateConsequences.BranchSafe branch_box_1476 := by
  left; refine ⟨branch_box_1476_nonnegative, ?_⟩
  intro z hz; exact leaf_1476_sound hz

theorem leaf_1480_ok : checkAt 527 1000 box_1480 cert_1480 = true := by
  have h := List.all_eq_true.mp batch_29_11_ok accepted_1480 (by simp [batch_29_11_values])
  exact h
theorem leaf_1480_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1480.profileLo box_1480.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1480_ok
theorem branch_box_1480_nonnegative : ∀ j, 0 ≤ branch_box_1480.lower j ∧ 0 ≤ branch_box_1480.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1480, Box.profileLo, Box.profileHi, box_1480]
theorem leaf_1480_BranchSafe : CertificateConsequences.BranchSafe branch_box_1480 := by
  left; refine ⟨branch_box_1480_nonnegative, ?_⟩
  intro z hz; exact leaf_1480_sound hz

theorem leaf_1481_ok : checkAt 527 1000 box_1481 cert_1481 = true := by
  have h := List.all_eq_true.mp batch_29_12_ok accepted_1481 (by simp [batch_29_12_values])
  exact h
theorem leaf_1481_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1481.profileLo box_1481.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1481_ok
theorem branch_box_1481_nonnegative : ∀ j, 0 ≤ branch_box_1481.lower j ∧ 0 ≤ branch_box_1481.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1481, Box.profileLo, Box.profileHi, box_1481]
theorem leaf_1481_BranchSafe : CertificateConsequences.BranchSafe branch_box_1481 := by
  left; refine ⟨branch_box_1481_nonnegative, ?_⟩
  intro z hz; exact leaf_1481_sound hz

theorem leaf_1484_ok : checkAt 527 1000 box_1484 cert_1484 = true := by
  have h := List.all_eq_true.mp batch_29_13_ok accepted_1484 (by simp [batch_29_13_values])
  exact h
theorem leaf_1484_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1484.profileLo box_1484.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1484_ok
theorem branch_box_1484_nonnegative : ∀ j, 0 ≤ branch_box_1484.lower j ∧ 0 ≤ branch_box_1484.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1484, Box.profileLo, Box.profileHi, box_1484]
theorem leaf_1484_BranchSafe : CertificateConsequences.BranchSafe branch_box_1484 := by
  left; refine ⟨branch_box_1484_nonnegative, ?_⟩
  intro z hz; exact leaf_1484_sound hz

theorem leaf_1486_ok : checkAt 527 1000 box_1486 cert_1486 = true := by
  have h := List.all_eq_true.mp batch_29_14_ok accepted_1486 (by simp [batch_29_14_values])
  exact h
theorem leaf_1486_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1486.profileLo box_1486.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1486_ok
theorem branch_box_1486_nonnegative : ∀ j, 0 ≤ branch_box_1486.lower j ∧ 0 ≤ branch_box_1486.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1486, Box.profileLo, Box.profileHi, box_1486]
theorem leaf_1486_BranchSafe : CertificateConsequences.BranchSafe branch_box_1486 := by
  left; refine ⟨branch_box_1486_nonnegative, ?_⟩
  intro z hz; exact leaf_1486_sound hz

theorem leaf_1488_ok : checkAt 527 1000 box_1488 cert_1488 = true := by
  have h := List.all_eq_true.mp batch_29_15_ok accepted_1488 (by simp [batch_29_15_values])
  exact h
theorem leaf_1488_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1488.profileLo box_1488.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1488_ok
theorem branch_box_1488_nonnegative : ∀ j, 0 ≤ branch_box_1488.lower j ∧ 0 ≤ branch_box_1488.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1488, Box.profileLo, Box.profileHi, box_1488]
theorem leaf_1488_BranchSafe : CertificateConsequences.BranchSafe branch_box_1488 := by
  left; refine ⟨branch_box_1488_nonnegative, ?_⟩
  intro z hz; exact leaf_1488_sound hz

theorem leaf_1490_ok : checkAt 527 1000 box_1490 cert_1490 = true := by
  have h := List.all_eq_true.mp batch_29_16_ok accepted_1490 (by simp [batch_29_16_values])
  exact h
theorem leaf_1490_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1490.profileLo box_1490.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1490_ok
theorem branch_box_1490_nonnegative : ∀ j, 0 ≤ branch_box_1490.lower j ∧ 0 ≤ branch_box_1490.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1490, Box.profileLo, Box.profileHi, box_1490]
theorem leaf_1490_BranchSafe : CertificateConsequences.BranchSafe branch_box_1490 := by
  left; refine ⟨branch_box_1490_nonnegative, ?_⟩
  intro z hz; exact leaf_1490_sound hz

theorem leaf_1491_ok : checkAt 527 1000 box_1491 cert_1491 = true := by
  have h := List.all_eq_true.mp batch_29_17_ok accepted_1491 (by simp [batch_29_17_values])
  exact h
theorem leaf_1491_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1491.profileLo box_1491.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1491_ok
theorem branch_box_1491_nonnegative : ∀ j, 0 ≤ branch_box_1491.lower j ∧ 0 ≤ branch_box_1491.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1491, Box.profileLo, Box.profileHi, box_1491]
theorem leaf_1491_BranchSafe : CertificateConsequences.BranchSafe branch_box_1491 := by
  left; refine ⟨branch_box_1491_nonnegative, ?_⟩
  intro z hz; exact leaf_1491_sound hz

theorem leaf_1494_ok : checkAt 527 1000 box_1494 cert_1494 = true := by
  have h := List.all_eq_true.mp batch_29_18_ok accepted_1494 (by simp [batch_29_18_values])
  exact h
theorem leaf_1494_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1494.profileLo box_1494.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1494_ok
theorem branch_box_1494_nonnegative : ∀ j, 0 ≤ branch_box_1494.lower j ∧ 0 ≤ branch_box_1494.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1494, Box.profileLo, Box.profileHi, box_1494]
theorem leaf_1494_BranchSafe : CertificateConsequences.BranchSafe branch_box_1494 := by
  left; refine ⟨branch_box_1494_nonnegative, ?_⟩
  intro z hz; exact leaf_1494_sound hz

theorem leaf_1496_ok : checkAt 527 1000 box_1496 cert_1496 = true := by
  have h := List.all_eq_true.mp batch_29_19_ok accepted_1496 (by simp [batch_29_19_values])
  exact h
theorem leaf_1496_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1496.profileLo box_1496.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1496_ok
theorem branch_box_1496_nonnegative : ∀ j, 0 ≤ branch_box_1496.lower j ∧ 0 ≤ branch_box_1496.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1496, Box.profileLo, Box.profileHi, box_1496]
theorem leaf_1496_BranchSafe : CertificateConsequences.BranchSafe branch_box_1496 := by
  left; refine ⟨branch_box_1496_nonnegative, ?_⟩
  intro z hz; exact leaf_1496_sound hz

theorem leaf_1498_ok : checkAt 527 1000 box_1498 cert_1498 = true := by
  have h := List.all_eq_true.mp batch_29_20_ok accepted_1498 (by simp [batch_29_20_values])
  exact h
theorem leaf_1498_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1498.profileLo box_1498.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1498_ok
theorem branch_box_1498_nonnegative : ∀ j, 0 ≤ branch_box_1498.lower j ∧ 0 ≤ branch_box_1498.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1498, Box.profileLo, Box.profileHi, box_1498]
theorem leaf_1498_BranchSafe : CertificateConsequences.BranchSafe branch_box_1498 := by
  left; refine ⟨branch_box_1498_nonnegative, ?_⟩
  intro z hz; exact leaf_1498_sound hz

#print axioms batch_29_00_ok
#print axioms leaf_1456_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
