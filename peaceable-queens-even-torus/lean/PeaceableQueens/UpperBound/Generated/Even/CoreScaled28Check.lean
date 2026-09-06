import PeaceableQueens.UpperBound.Generated.Even.CoreScaled28Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_28_00_values : List Bool := [accepted_1400]
theorem batch_28_00_ok : batch_28_00_values.all id = true := by decide

def batch_28_01_values : List Bool := [accepted_1401]
theorem batch_28_01_ok : batch_28_01_values.all id = true := by decide

def batch_28_02_values : List Bool := [accepted_1403]
theorem batch_28_02_ok : batch_28_02_values.all id = true := by decide

def batch_28_03_values : List Bool := [accepted_1408]
theorem batch_28_03_ok : batch_28_03_values.all id = true := by decide

def batch_28_04_values : List Bool := [accepted_1410]
theorem batch_28_04_ok : batch_28_04_values.all id = true := by decide

def batch_28_05_values : List Bool := [accepted_1412]
theorem batch_28_05_ok : batch_28_05_values.all id = true := by decide

def batch_28_06_values : List Bool := [accepted_1413]
theorem batch_28_06_ok : batch_28_06_values.all id = true := by decide

def batch_28_07_values : List Bool := [accepted_1416]
theorem batch_28_07_ok : batch_28_07_values.all id = true := by decide

def batch_28_08_values : List Bool := [accepted_1418]
theorem batch_28_08_ok : batch_28_08_values.all id = true := by decide

def batch_28_09_values : List Bool := [accepted_1420]
theorem batch_28_09_ok : batch_28_09_values.all id = true := by decide

def batch_28_10_values : List Bool := [accepted_1421]
theorem batch_28_10_ok : batch_28_10_values.all id = true := by decide

def batch_28_11_values : List Bool := [accepted_1424]
theorem batch_28_11_ok : batch_28_11_values.all id = true := by decide

def batch_28_12_values : List Bool := [accepted_1426]
theorem batch_28_12_ok : batch_28_12_values.all id = true := by decide

def batch_28_13_values : List Bool := [accepted_1428]
theorem batch_28_13_ok : batch_28_13_values.all id = true := by decide

def batch_28_14_values : List Bool := [accepted_1430]
theorem batch_28_14_ok : batch_28_14_values.all id = true := by decide

def batch_28_15_values : List Bool := [accepted_1432]
theorem batch_28_15_ok : batch_28_15_values.all id = true := by decide

def batch_28_16_values : List Bool := [accepted_1433]
theorem batch_28_16_ok : batch_28_16_values.all id = true := by decide

def batch_28_17_values : List Bool := [accepted_1436]
theorem batch_28_17_ok : batch_28_17_values.all id = true := by decide

def batch_28_18_values : List Bool := [accepted_1438]
theorem batch_28_18_ok : batch_28_18_values.all id = true := by decide

def batch_28_19_values : List Bool := [accepted_1440]
theorem batch_28_19_ok : batch_28_19_values.all id = true := by decide

def batch_28_20_values : List Bool := [accepted_1442]
theorem batch_28_20_ok : batch_28_20_values.all id = true := by decide

def batch_28_21_values : List Bool := [accepted_1444]
theorem batch_28_21_ok : batch_28_21_values.all id = true := by decide

def batch_28_22_values : List Bool := [accepted_1445]
theorem batch_28_22_ok : batch_28_22_values.all id = true := by decide

def batch_28_23_values : List Bool := [accepted_1447]
theorem batch_28_23_ok : batch_28_23_values.all id = true := by decide

theorem leaf_1400_ok : checkAt 527 1000 box_1400 cert_1400 = true := by
  have h := List.all_eq_true.mp batch_28_00_ok accepted_1400 (by simp [batch_28_00_values])
  exact h
theorem leaf_1400_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1400.profileLo box_1400.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1400_ok
theorem branch_box_1400_nonnegative : ∀ j, 0 ≤ branch_box_1400.lower j ∧ 0 ≤ branch_box_1400.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1400, Box.profileLo, Box.profileHi, box_1400]
theorem leaf_1400_BranchSafe : CertificateConsequences.BranchSafe branch_box_1400 := by
  left; refine ⟨branch_box_1400_nonnegative, ?_⟩
  intro z hz; exact leaf_1400_sound hz

theorem leaf_1401_ok : checkAt 527 1000 box_1401 cert_1401 = true := by
  have h := List.all_eq_true.mp batch_28_01_ok accepted_1401 (by simp [batch_28_01_values])
  exact h
theorem leaf_1401_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1401.profileLo box_1401.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1401_ok
theorem branch_box_1401_nonnegative : ∀ j, 0 ≤ branch_box_1401.lower j ∧ 0 ≤ branch_box_1401.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1401, Box.profileLo, Box.profileHi, box_1401]
theorem leaf_1401_BranchSafe : CertificateConsequences.BranchSafe branch_box_1401 := by
  left; refine ⟨branch_box_1401_nonnegative, ?_⟩
  intro z hz; exact leaf_1401_sound hz

theorem leaf_1403_ok : checkAt 527 1000 box_1403 cert_1403 = true := by
  have h := List.all_eq_true.mp batch_28_02_ok accepted_1403 (by simp [batch_28_02_values])
  exact h
theorem leaf_1403_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1403.profileLo box_1403.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1403_ok
theorem branch_box_1403_nonnegative : ∀ j, 0 ≤ branch_box_1403.lower j ∧ 0 ≤ branch_box_1403.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1403, Box.profileLo, Box.profileHi, box_1403]
theorem leaf_1403_BranchSafe : CertificateConsequences.BranchSafe branch_box_1403 := by
  left; refine ⟨branch_box_1403_nonnegative, ?_⟩
  intro z hz; exact leaf_1403_sound hz

theorem leaf_1408_ok : checkAt 527 1000 box_1408 cert_1408 = true := by
  have h := List.all_eq_true.mp batch_28_03_ok accepted_1408 (by simp [batch_28_03_values])
  exact h
theorem leaf_1408_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1408.profileLo box_1408.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1408_ok
theorem branch_box_1408_nonnegative : ∀ j, 0 ≤ branch_box_1408.lower j ∧ 0 ≤ branch_box_1408.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1408, Box.profileLo, Box.profileHi, box_1408]
theorem leaf_1408_BranchSafe : CertificateConsequences.BranchSafe branch_box_1408 := by
  left; refine ⟨branch_box_1408_nonnegative, ?_⟩
  intro z hz; exact leaf_1408_sound hz

theorem leaf_1410_ok : checkAt 527 1000 box_1410 cert_1410 = true := by
  have h := List.all_eq_true.mp batch_28_04_ok accepted_1410 (by simp [batch_28_04_values])
  exact h
theorem leaf_1410_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1410.profileLo box_1410.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1410_ok
theorem branch_box_1410_nonnegative : ∀ j, 0 ≤ branch_box_1410.lower j ∧ 0 ≤ branch_box_1410.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1410, Box.profileLo, Box.profileHi, box_1410]
theorem leaf_1410_BranchSafe : CertificateConsequences.BranchSafe branch_box_1410 := by
  left; refine ⟨branch_box_1410_nonnegative, ?_⟩
  intro z hz; exact leaf_1410_sound hz

theorem leaf_1412_ok : checkAt 527 1000 box_1412 cert_1412 = true := by
  have h := List.all_eq_true.mp batch_28_05_ok accepted_1412 (by simp [batch_28_05_values])
  exact h
theorem leaf_1412_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1412.profileLo box_1412.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1412_ok
theorem branch_box_1412_nonnegative : ∀ j, 0 ≤ branch_box_1412.lower j ∧ 0 ≤ branch_box_1412.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1412, Box.profileLo, Box.profileHi, box_1412]
theorem leaf_1412_BranchSafe : CertificateConsequences.BranchSafe branch_box_1412 := by
  left; refine ⟨branch_box_1412_nonnegative, ?_⟩
  intro z hz; exact leaf_1412_sound hz

theorem leaf_1413_ok : checkAt 527 1000 box_1413 cert_1413 = true := by
  have h := List.all_eq_true.mp batch_28_06_ok accepted_1413 (by simp [batch_28_06_values])
  exact h
theorem leaf_1413_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1413.profileLo box_1413.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1413_ok
theorem branch_box_1413_nonnegative : ∀ j, 0 ≤ branch_box_1413.lower j ∧ 0 ≤ branch_box_1413.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1413, Box.profileLo, Box.profileHi, box_1413]
theorem leaf_1413_BranchSafe : CertificateConsequences.BranchSafe branch_box_1413 := by
  left; refine ⟨branch_box_1413_nonnegative, ?_⟩
  intro z hz; exact leaf_1413_sound hz

theorem leaf_1416_ok : checkAt 527 1000 box_1416 cert_1416 = true := by
  have h := List.all_eq_true.mp batch_28_07_ok accepted_1416 (by simp [batch_28_07_values])
  exact h
theorem leaf_1416_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1416.profileLo box_1416.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1416_ok
theorem branch_box_1416_nonnegative : ∀ j, 0 ≤ branch_box_1416.lower j ∧ 0 ≤ branch_box_1416.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1416, Box.profileLo, Box.profileHi, box_1416]
theorem leaf_1416_BranchSafe : CertificateConsequences.BranchSafe branch_box_1416 := by
  left; refine ⟨branch_box_1416_nonnegative, ?_⟩
  intro z hz; exact leaf_1416_sound hz

theorem leaf_1418_ok : checkAt 527 1000 box_1418 cert_1418 = true := by
  have h := List.all_eq_true.mp batch_28_08_ok accepted_1418 (by simp [batch_28_08_values])
  exact h
theorem leaf_1418_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1418.profileLo box_1418.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1418_ok
theorem branch_box_1418_nonnegative : ∀ j, 0 ≤ branch_box_1418.lower j ∧ 0 ≤ branch_box_1418.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1418, Box.profileLo, Box.profileHi, box_1418]
theorem leaf_1418_BranchSafe : CertificateConsequences.BranchSafe branch_box_1418 := by
  left; refine ⟨branch_box_1418_nonnegative, ?_⟩
  intro z hz; exact leaf_1418_sound hz

theorem leaf_1420_ok : checkAt 527 1000 box_1420 cert_1420 = true := by
  have h := List.all_eq_true.mp batch_28_09_ok accepted_1420 (by simp [batch_28_09_values])
  exact h
theorem leaf_1420_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1420.profileLo box_1420.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1420_ok
theorem branch_box_1420_nonnegative : ∀ j, 0 ≤ branch_box_1420.lower j ∧ 0 ≤ branch_box_1420.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1420, Box.profileLo, Box.profileHi, box_1420]
theorem leaf_1420_BranchSafe : CertificateConsequences.BranchSafe branch_box_1420 := by
  left; refine ⟨branch_box_1420_nonnegative, ?_⟩
  intro z hz; exact leaf_1420_sound hz

theorem leaf_1421_ok : checkAt 527 1000 box_1421 cert_1421 = true := by
  have h := List.all_eq_true.mp batch_28_10_ok accepted_1421 (by simp [batch_28_10_values])
  exact h
theorem leaf_1421_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1421.profileLo box_1421.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1421_ok
theorem branch_box_1421_nonnegative : ∀ j, 0 ≤ branch_box_1421.lower j ∧ 0 ≤ branch_box_1421.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1421, Box.profileLo, Box.profileHi, box_1421]
theorem leaf_1421_BranchSafe : CertificateConsequences.BranchSafe branch_box_1421 := by
  left; refine ⟨branch_box_1421_nonnegative, ?_⟩
  intro z hz; exact leaf_1421_sound hz

theorem leaf_1424_ok : checkAt 527 1000 box_1424 cert_1424 = true := by
  have h := List.all_eq_true.mp batch_28_11_ok accepted_1424 (by simp [batch_28_11_values])
  exact h
theorem leaf_1424_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1424.profileLo box_1424.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1424_ok
theorem branch_box_1424_nonnegative : ∀ j, 0 ≤ branch_box_1424.lower j ∧ 0 ≤ branch_box_1424.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1424, Box.profileLo, Box.profileHi, box_1424]
theorem leaf_1424_BranchSafe : CertificateConsequences.BranchSafe branch_box_1424 := by
  left; refine ⟨branch_box_1424_nonnegative, ?_⟩
  intro z hz; exact leaf_1424_sound hz

theorem leaf_1426_ok : checkAt 527 1000 box_1426 cert_1426 = true := by
  have h := List.all_eq_true.mp batch_28_12_ok accepted_1426 (by simp [batch_28_12_values])
  exact h
theorem leaf_1426_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1426.profileLo box_1426.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1426_ok
theorem branch_box_1426_nonnegative : ∀ j, 0 ≤ branch_box_1426.lower j ∧ 0 ≤ branch_box_1426.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1426, Box.profileLo, Box.profileHi, box_1426]
theorem leaf_1426_BranchSafe : CertificateConsequences.BranchSafe branch_box_1426 := by
  left; refine ⟨branch_box_1426_nonnegative, ?_⟩
  intro z hz; exact leaf_1426_sound hz

theorem leaf_1428_ok : checkAt 527 1000 box_1428 cert_1428 = true := by
  have h := List.all_eq_true.mp batch_28_13_ok accepted_1428 (by simp [batch_28_13_values])
  exact h
theorem leaf_1428_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1428.profileLo box_1428.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1428_ok
theorem branch_box_1428_nonnegative : ∀ j, 0 ≤ branch_box_1428.lower j ∧ 0 ≤ branch_box_1428.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1428, Box.profileLo, Box.profileHi, box_1428]
theorem leaf_1428_BranchSafe : CertificateConsequences.BranchSafe branch_box_1428 := by
  left; refine ⟨branch_box_1428_nonnegative, ?_⟩
  intro z hz; exact leaf_1428_sound hz

theorem leaf_1430_ok : checkAt 527 1000 box_1430 cert_1430 = true := by
  have h := List.all_eq_true.mp batch_28_14_ok accepted_1430 (by simp [batch_28_14_values])
  exact h
theorem leaf_1430_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1430.profileLo box_1430.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1430_ok
theorem branch_box_1430_nonnegative : ∀ j, 0 ≤ branch_box_1430.lower j ∧ 0 ≤ branch_box_1430.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1430, Box.profileLo, Box.profileHi, box_1430]
theorem leaf_1430_BranchSafe : CertificateConsequences.BranchSafe branch_box_1430 := by
  left; refine ⟨branch_box_1430_nonnegative, ?_⟩
  intro z hz; exact leaf_1430_sound hz

theorem leaf_1432_ok : checkAt 527 1000 box_1432 cert_1432 = true := by
  have h := List.all_eq_true.mp batch_28_15_ok accepted_1432 (by simp [batch_28_15_values])
  exact h
theorem leaf_1432_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1432.profileLo box_1432.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1432_ok
theorem branch_box_1432_nonnegative : ∀ j, 0 ≤ branch_box_1432.lower j ∧ 0 ≤ branch_box_1432.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1432, Box.profileLo, Box.profileHi, box_1432]
theorem leaf_1432_BranchSafe : CertificateConsequences.BranchSafe branch_box_1432 := by
  left; refine ⟨branch_box_1432_nonnegative, ?_⟩
  intro z hz; exact leaf_1432_sound hz

theorem leaf_1433_ok : checkAt 527 1000 box_1433 cert_1433 = true := by
  have h := List.all_eq_true.mp batch_28_16_ok accepted_1433 (by simp [batch_28_16_values])
  exact h
theorem leaf_1433_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1433.profileLo box_1433.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1433_ok
theorem branch_box_1433_nonnegative : ∀ j, 0 ≤ branch_box_1433.lower j ∧ 0 ≤ branch_box_1433.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1433, Box.profileLo, Box.profileHi, box_1433]
theorem leaf_1433_BranchSafe : CertificateConsequences.BranchSafe branch_box_1433 := by
  left; refine ⟨branch_box_1433_nonnegative, ?_⟩
  intro z hz; exact leaf_1433_sound hz

theorem leaf_1436_ok : checkAt 527 1000 box_1436 cert_1436 = true := by
  have h := List.all_eq_true.mp batch_28_17_ok accepted_1436 (by simp [batch_28_17_values])
  exact h
theorem leaf_1436_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1436.profileLo box_1436.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1436_ok
theorem branch_box_1436_nonnegative : ∀ j, 0 ≤ branch_box_1436.lower j ∧ 0 ≤ branch_box_1436.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1436, Box.profileLo, Box.profileHi, box_1436]
theorem leaf_1436_BranchSafe : CertificateConsequences.BranchSafe branch_box_1436 := by
  left; refine ⟨branch_box_1436_nonnegative, ?_⟩
  intro z hz; exact leaf_1436_sound hz

theorem leaf_1438_ok : checkAt 527 1000 box_1438 cert_1438 = true := by
  have h := List.all_eq_true.mp batch_28_18_ok accepted_1438 (by simp [batch_28_18_values])
  exact h
theorem leaf_1438_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1438.profileLo box_1438.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1438_ok
theorem branch_box_1438_nonnegative : ∀ j, 0 ≤ branch_box_1438.lower j ∧ 0 ≤ branch_box_1438.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1438, Box.profileLo, Box.profileHi, box_1438]
theorem leaf_1438_BranchSafe : CertificateConsequences.BranchSafe branch_box_1438 := by
  left; refine ⟨branch_box_1438_nonnegative, ?_⟩
  intro z hz; exact leaf_1438_sound hz

theorem leaf_1440_ok : checkAt 527 1000 box_1440 cert_1440 = true := by
  have h := List.all_eq_true.mp batch_28_19_ok accepted_1440 (by simp [batch_28_19_values])
  exact h
theorem leaf_1440_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1440.profileLo box_1440.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1440_ok
theorem branch_box_1440_nonnegative : ∀ j, 0 ≤ branch_box_1440.lower j ∧ 0 ≤ branch_box_1440.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1440, Box.profileLo, Box.profileHi, box_1440]
theorem leaf_1440_BranchSafe : CertificateConsequences.BranchSafe branch_box_1440 := by
  left; refine ⟨branch_box_1440_nonnegative, ?_⟩
  intro z hz; exact leaf_1440_sound hz

theorem leaf_1442_ok : checkAt 527 1000 box_1442 cert_1442 = true := by
  have h := List.all_eq_true.mp batch_28_20_ok accepted_1442 (by simp [batch_28_20_values])
  exact h
theorem leaf_1442_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1442.profileLo box_1442.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1442_ok
theorem branch_box_1442_nonnegative : ∀ j, 0 ≤ branch_box_1442.lower j ∧ 0 ≤ branch_box_1442.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1442, Box.profileLo, Box.profileHi, box_1442]
theorem leaf_1442_BranchSafe : CertificateConsequences.BranchSafe branch_box_1442 := by
  left; refine ⟨branch_box_1442_nonnegative, ?_⟩
  intro z hz; exact leaf_1442_sound hz

theorem leaf_1444_ok : checkAt 527 1000 box_1444 cert_1444 = true := by
  have h := List.all_eq_true.mp batch_28_21_ok accepted_1444 (by simp [batch_28_21_values])
  exact h
theorem leaf_1444_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1444.profileLo box_1444.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1444_ok
theorem branch_box_1444_nonnegative : ∀ j, 0 ≤ branch_box_1444.lower j ∧ 0 ≤ branch_box_1444.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1444, Box.profileLo, Box.profileHi, box_1444]
theorem leaf_1444_BranchSafe : CertificateConsequences.BranchSafe branch_box_1444 := by
  left; refine ⟨branch_box_1444_nonnegative, ?_⟩
  intro z hz; exact leaf_1444_sound hz

theorem leaf_1445_ok : checkAt 527 1000 box_1445 cert_1445 = true := by
  have h := List.all_eq_true.mp batch_28_22_ok accepted_1445 (by simp [batch_28_22_values])
  exact h
theorem leaf_1445_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1445.profileLo box_1445.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1445_ok
theorem branch_box_1445_nonnegative : ∀ j, 0 ≤ branch_box_1445.lower j ∧ 0 ≤ branch_box_1445.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1445, Box.profileLo, Box.profileHi, box_1445]
theorem leaf_1445_BranchSafe : CertificateConsequences.BranchSafe branch_box_1445 := by
  left; refine ⟨branch_box_1445_nonnegative, ?_⟩
  intro z hz; exact leaf_1445_sound hz

theorem leaf_1447_ok : checkAt 527 1000 box_1447 cert_1447 = true := by
  have h := List.all_eq_true.mp batch_28_23_ok accepted_1447 (by simp [batch_28_23_values])
  exact h
theorem leaf_1447_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1447.profileLo box_1447.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1447_ok
theorem branch_box_1447_nonnegative : ∀ j, 0 ≤ branch_box_1447.lower j ∧ 0 ≤ branch_box_1447.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1447, Box.profileLo, Box.profileHi, box_1447]
theorem leaf_1447_BranchSafe : CertificateConsequences.BranchSafe branch_box_1447 := by
  left; refine ⟨branch_box_1447_nonnegative, ?_⟩
  intro z hz; exact leaf_1447_sound hz

#print axioms batch_28_00_ok
#print axioms leaf_1400_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
