import PeaceableQueens.UpperBound.Generated.Even.C527Scaled29Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_29_00_values : List Bool := [accepted_1450]
theorem batch_29_00_ok : batch_29_00_values.all id = true := by decide

def batch_29_01_values : List Bool := [accepted_1452]
theorem batch_29_01_ok : batch_29_01_values.all id = true := by decide

def batch_29_02_values : List Bool := [accepted_1453]
theorem batch_29_02_ok : batch_29_02_values.all id = true := by decide

def batch_29_03_values : List Bool := [accepted_1455]
theorem batch_29_03_ok : batch_29_03_values.all id = true := by decide

def batch_29_04_values : List Bool := [accepted_1457]
theorem batch_29_04_ok : batch_29_04_values.all id = true := by decide

def batch_29_05_values : List Bool := [accepted_1458]
theorem batch_29_05_ok : batch_29_05_values.all id = true := by decide

def batch_29_06_values : List Bool := [accepted_1465]
theorem batch_29_06_ok : batch_29_06_values.all id = true := by decide

def batch_29_07_values : List Bool := [accepted_1468]
theorem batch_29_07_ok : batch_29_07_values.all id = true := by decide

def batch_29_08_values : List Bool := [accepted_1469]
theorem batch_29_08_ok : batch_29_08_values.all id = true := by decide

def batch_29_09_values : List Bool := [accepted_1470]
theorem batch_29_09_ok : batch_29_09_values.all id = true := by decide

def batch_29_10_values : List Bool := [accepted_1471]
theorem batch_29_10_ok : batch_29_10_values.all id = true := by decide

def batch_29_11_values : List Bool := [accepted_1472]
theorem batch_29_11_ok : batch_29_11_values.all id = true := by decide

def batch_29_12_values : List Bool := [accepted_1476]
theorem batch_29_12_ok : batch_29_12_values.all id = true := by decide

def batch_29_13_values : List Bool := [accepted_1477]
theorem batch_29_13_ok : batch_29_13_values.all id = true := by decide

def batch_29_14_values : List Bool := [accepted_1478]
theorem batch_29_14_ok : batch_29_14_values.all id = true := by decide

def batch_29_15_values : List Bool := [accepted_1479]
theorem batch_29_15_ok : batch_29_15_values.all id = true := by decide

def batch_29_16_values : List Bool := [accepted_1484]
theorem batch_29_16_ok : batch_29_16_values.all id = true := by decide

def batch_29_17_values : List Bool := [accepted_1486]
theorem batch_29_17_ok : batch_29_17_values.all id = true := by decide

def batch_29_18_values : List Bool := [accepted_1487]
theorem batch_29_18_ok : batch_29_18_values.all id = true := by decide

def batch_29_19_values : List Bool := [accepted_1489]
theorem batch_29_19_ok : batch_29_19_values.all id = true := by decide

def batch_29_20_values : List Bool := [accepted_1490]
theorem batch_29_20_ok : batch_29_20_values.all id = true := by decide

def batch_29_21_values : List Bool := [accepted_1491]
theorem batch_29_21_ok : batch_29_21_values.all id = true := by decide

def batch_29_22_values : List Bool := [accepted_1492]
theorem batch_29_22_ok : batch_29_22_values.all id = true := by decide

theorem leaf_1450_ok : checkAt 527 1000 box_1450 cert_1450 = true := by
  have h := List.all_eq_true.mp batch_29_00_ok accepted_1450 (by simp [batch_29_00_values])
  exact h
theorem leaf_1450_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1450.profileLo box_1450.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1450_ok
theorem branch_box_1450_nonnegative : ∀ j, 0 ≤ branch_box_1450.lower j ∧ 0 ≤ branch_box_1450.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1450, Box.profileLo, Box.profileHi, box_1450]
theorem leaf_1450_BranchSafe : CertificateConsequences.BranchSafe branch_box_1450 := by
  left; refine ⟨branch_box_1450_nonnegative, ?_⟩
  intro z hz; exact leaf_1450_sound hz

theorem leaf_1452_ok : checkAt 527 1000 box_1452 cert_1452 = true := by
  have h := List.all_eq_true.mp batch_29_01_ok accepted_1452 (by simp [batch_29_01_values])
  exact h
theorem leaf_1452_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1452.profileLo box_1452.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1452_ok
theorem branch_box_1452_nonnegative : ∀ j, 0 ≤ branch_box_1452.lower j ∧ 0 ≤ branch_box_1452.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1452, Box.profileLo, Box.profileHi, box_1452]
theorem leaf_1452_BranchSafe : CertificateConsequences.BranchSafe branch_box_1452 := by
  left; refine ⟨branch_box_1452_nonnegative, ?_⟩
  intro z hz; exact leaf_1452_sound hz

theorem leaf_1453_ok : checkAt 527 1000 box_1453 cert_1453 = true := by
  have h := List.all_eq_true.mp batch_29_02_ok accepted_1453 (by simp [batch_29_02_values])
  exact h
theorem leaf_1453_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1453.profileLo box_1453.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1453_ok
theorem branch_box_1453_nonnegative : ∀ j, 0 ≤ branch_box_1453.lower j ∧ 0 ≤ branch_box_1453.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1453, Box.profileLo, Box.profileHi, box_1453]
theorem leaf_1453_BranchSafe : CertificateConsequences.BranchSafe branch_box_1453 := by
  left; refine ⟨branch_box_1453_nonnegative, ?_⟩
  intro z hz; exact leaf_1453_sound hz

theorem leaf_1455_ok : checkAt 527 1000 box_1455 cert_1455 = true := by
  have h := List.all_eq_true.mp batch_29_03_ok accepted_1455 (by simp [batch_29_03_values])
  exact h
theorem leaf_1455_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1455.profileLo box_1455.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1455_ok
theorem branch_box_1455_nonnegative : ∀ j, 0 ≤ branch_box_1455.lower j ∧ 0 ≤ branch_box_1455.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1455, Box.profileLo, Box.profileHi, box_1455]
theorem leaf_1455_BranchSafe : CertificateConsequences.BranchSafe branch_box_1455 := by
  left; refine ⟨branch_box_1455_nonnegative, ?_⟩
  intro z hz; exact leaf_1455_sound hz

theorem leaf_1457_ok : checkAt 527 1000 box_1457 cert_1457 = true := by
  have h := List.all_eq_true.mp batch_29_04_ok accepted_1457 (by simp [batch_29_04_values])
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

theorem leaf_1458_ok : checkAt 527 1000 box_1458 cert_1458 = true := by
  have h := List.all_eq_true.mp batch_29_05_ok accepted_1458 (by simp [batch_29_05_values])
  exact h
theorem leaf_1458_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1458.profileLo box_1458.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1458_ok
theorem branch_box_1458_nonnegative : ∀ j, 0 ≤ branch_box_1458.lower j ∧ 0 ≤ branch_box_1458.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1458, Box.profileLo, Box.profileHi, box_1458]
theorem leaf_1458_BranchSafe : CertificateConsequences.BranchSafe branch_box_1458 := by
  left; refine ⟨branch_box_1458_nonnegative, ?_⟩
  intro z hz; exact leaf_1458_sound hz

theorem leaf_1465_ok : checkAt 527 1000 box_1465 cert_1465 = true := by
  have h := List.all_eq_true.mp batch_29_06_ok accepted_1465 (by simp [batch_29_06_values])
  exact h
theorem leaf_1465_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1465.profileLo box_1465.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1465_ok
theorem branch_box_1465_nonnegative : ∀ j, 0 ≤ branch_box_1465.lower j ∧ 0 ≤ branch_box_1465.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1465, Box.profileLo, Box.profileHi, box_1465]
theorem leaf_1465_BranchSafe : CertificateConsequences.BranchSafe branch_box_1465 := by
  left; refine ⟨branch_box_1465_nonnegative, ?_⟩
  intro z hz; exact leaf_1465_sound hz

theorem leaf_1468_ok : checkAt 527 1000 box_1468 cert_1468 = true := by
  have h := List.all_eq_true.mp batch_29_07_ok accepted_1468 (by simp [batch_29_07_values])
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
  have h := List.all_eq_true.mp batch_29_08_ok accepted_1469 (by simp [batch_29_08_values])
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

theorem leaf_1470_ok : checkAt 527 1000 box_1470 cert_1470 = true := by
  have h := List.all_eq_true.mp batch_29_09_ok accepted_1470 (by simp [batch_29_09_values])
  exact h
theorem leaf_1470_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1470.profileLo box_1470.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1470_ok
theorem branch_box_1470_nonnegative : ∀ j, 0 ≤ branch_box_1470.lower j ∧ 0 ≤ branch_box_1470.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1470, Box.profileLo, Box.profileHi, box_1470]
theorem leaf_1470_BranchSafe : CertificateConsequences.BranchSafe branch_box_1470 := by
  left; refine ⟨branch_box_1470_nonnegative, ?_⟩
  intro z hz; exact leaf_1470_sound hz

theorem leaf_1471_ok : checkAt 527 1000 box_1471 cert_1471 = true := by
  have h := List.all_eq_true.mp batch_29_10_ok accepted_1471 (by simp [batch_29_10_values])
  exact h
theorem leaf_1471_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1471.profileLo box_1471.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1471_ok
theorem branch_box_1471_nonnegative : ∀ j, 0 ≤ branch_box_1471.lower j ∧ 0 ≤ branch_box_1471.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1471, Box.profileLo, Box.profileHi, box_1471]
theorem leaf_1471_BranchSafe : CertificateConsequences.BranchSafe branch_box_1471 := by
  left; refine ⟨branch_box_1471_nonnegative, ?_⟩
  intro z hz; exact leaf_1471_sound hz

theorem leaf_1472_ok : checkAt 527 1000 box_1472 cert_1472 = true := by
  have h := List.all_eq_true.mp batch_29_11_ok accepted_1472 (by simp [batch_29_11_values])
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

theorem leaf_1476_ok : checkAt 527 1000 box_1476 cert_1476 = true := by
  have h := List.all_eq_true.mp batch_29_12_ok accepted_1476 (by simp [batch_29_12_values])
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

theorem leaf_1477_ok : checkAt 527 1000 box_1477 cert_1477 = true := by
  have h := List.all_eq_true.mp batch_29_13_ok accepted_1477 (by simp [batch_29_13_values])
  exact h
theorem leaf_1477_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1477.profileLo box_1477.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1477_ok
theorem branch_box_1477_nonnegative : ∀ j, 0 ≤ branch_box_1477.lower j ∧ 0 ≤ branch_box_1477.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1477, Box.profileLo, Box.profileHi, box_1477]
theorem leaf_1477_BranchSafe : CertificateConsequences.BranchSafe branch_box_1477 := by
  left; refine ⟨branch_box_1477_nonnegative, ?_⟩
  intro z hz; exact leaf_1477_sound hz

theorem leaf_1478_ok : checkAt 527 1000 box_1478 cert_1478 = true := by
  have h := List.all_eq_true.mp batch_29_14_ok accepted_1478 (by simp [batch_29_14_values])
  exact h
theorem leaf_1478_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1478.profileLo box_1478.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1478_ok
theorem branch_box_1478_nonnegative : ∀ j, 0 ≤ branch_box_1478.lower j ∧ 0 ≤ branch_box_1478.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1478, Box.profileLo, Box.profileHi, box_1478]
theorem leaf_1478_BranchSafe : CertificateConsequences.BranchSafe branch_box_1478 := by
  left; refine ⟨branch_box_1478_nonnegative, ?_⟩
  intro z hz; exact leaf_1478_sound hz

theorem leaf_1479_ok : checkAt 527 1000 box_1479 cert_1479 = true := by
  have h := List.all_eq_true.mp batch_29_15_ok accepted_1479 (by simp [batch_29_15_values])
  exact h
theorem leaf_1479_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1479.profileLo box_1479.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1479_ok
theorem branch_box_1479_nonnegative : ∀ j, 0 ≤ branch_box_1479.lower j ∧ 0 ≤ branch_box_1479.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1479, Box.profileLo, Box.profileHi, box_1479]
theorem leaf_1479_BranchSafe : CertificateConsequences.BranchSafe branch_box_1479 := by
  left; refine ⟨branch_box_1479_nonnegative, ?_⟩
  intro z hz; exact leaf_1479_sound hz

theorem leaf_1484_ok : checkAt 527 1000 box_1484 cert_1484 = true := by
  have h := List.all_eq_true.mp batch_29_16_ok accepted_1484 (by simp [batch_29_16_values])
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
  have h := List.all_eq_true.mp batch_29_17_ok accepted_1486 (by simp [batch_29_17_values])
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

theorem leaf_1487_ok : checkAt 527 1000 box_1487 cert_1487 = true := by
  have h := List.all_eq_true.mp batch_29_18_ok accepted_1487 (by simp [batch_29_18_values])
  exact h
theorem leaf_1487_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1487.profileLo box_1487.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1487_ok
theorem branch_box_1487_nonnegative : ∀ j, 0 ≤ branch_box_1487.lower j ∧ 0 ≤ branch_box_1487.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1487, Box.profileLo, Box.profileHi, box_1487]
theorem leaf_1487_BranchSafe : CertificateConsequences.BranchSafe branch_box_1487 := by
  left; refine ⟨branch_box_1487_nonnegative, ?_⟩
  intro z hz; exact leaf_1487_sound hz

theorem leaf_1489_ok : checkAt 527 1000 box_1489 cert_1489 = true := by
  have h := List.all_eq_true.mp batch_29_19_ok accepted_1489 (by simp [batch_29_19_values])
  exact h
theorem leaf_1489_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1489.profileLo box_1489.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1489_ok
theorem branch_box_1489_nonnegative : ∀ j, 0 ≤ branch_box_1489.lower j ∧ 0 ≤ branch_box_1489.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1489, Box.profileLo, Box.profileHi, box_1489]
theorem leaf_1489_BranchSafe : CertificateConsequences.BranchSafe branch_box_1489 := by
  left; refine ⟨branch_box_1489_nonnegative, ?_⟩
  intro z hz; exact leaf_1489_sound hz

theorem leaf_1490_ok : checkAt 527 1000 box_1490 cert_1490 = true := by
  have h := List.all_eq_true.mp batch_29_20_ok accepted_1490 (by simp [batch_29_20_values])
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
  have h := List.all_eq_true.mp batch_29_21_ok accepted_1491 (by simp [batch_29_21_values])
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

theorem leaf_1492_ok : checkAt 527 1000 box_1492 cert_1492 = true := by
  have h := List.all_eq_true.mp batch_29_22_ok accepted_1492 (by simp [batch_29_22_values])
  exact h
theorem leaf_1492_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1492.profileLo box_1492.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1492_ok
theorem branch_box_1492_nonnegative : ∀ j, 0 ≤ branch_box_1492.lower j ∧ 0 ≤ branch_box_1492.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1492, Box.profileLo, Box.profileHi, box_1492]
theorem leaf_1492_BranchSafe : CertificateConsequences.BranchSafe branch_box_1492 := by
  left; refine ⟨branch_box_1492_nonnegative, ?_⟩
  intro z hz; exact leaf_1492_sound hz

#print axioms batch_29_00_ok
#print axioms leaf_1450_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
