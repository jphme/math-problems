import PeaceableQueens.UpperBound.Generated.Even.C527Scaled28Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_28_00_values : List Bool := [accepted_1400]
theorem batch_28_00_ok : batch_28_00_values.all id = true := by decide

def batch_28_01_values : List Bool := [accepted_1402]
theorem batch_28_01_ok : batch_28_01_values.all id = true := by decide

def batch_28_02_values : List Bool := [accepted_1403]
theorem batch_28_02_ok : batch_28_02_values.all id = true := by decide

def batch_28_03_values : List Bool := [accepted_1404]
theorem batch_28_03_ok : batch_28_03_values.all id = true := by decide

def batch_28_04_values : List Bool := [accepted_1410]
theorem batch_28_04_ok : batch_28_04_values.all id = true := by decide

def batch_28_05_values : List Bool := [accepted_1411]
theorem batch_28_05_ok : batch_28_05_values.all id = true := by decide

def batch_28_06_values : List Bool := [accepted_1412]
theorem batch_28_06_ok : batch_28_06_values.all id = true := by decide

def batch_28_07_values : List Bool := [accepted_1414]
theorem batch_28_07_ok : batch_28_07_values.all id = true := by decide

def batch_28_08_values : List Bool := [accepted_1417]
theorem batch_28_08_ok : batch_28_08_values.all id = true := by decide

def batch_28_09_values : List Bool := [accepted_1419]
theorem batch_28_09_ok : batch_28_09_values.all id = true := by decide

def batch_28_10_values : List Bool := [accepted_1420]
theorem batch_28_10_ok : batch_28_10_values.all id = true := by decide

def batch_28_11_values : List Bool := [accepted_1421]
theorem batch_28_11_ok : batch_28_11_values.all id = true := by decide

def batch_28_12_values : List Bool := [accepted_1422]
theorem batch_28_12_ok : batch_28_12_values.all id = true := by decide

def batch_28_13_values : List Bool := [accepted_1427]
theorem batch_28_13_ok : batch_28_13_values.all id = true := by decide

def batch_28_14_values : List Bool := [accepted_1429]
theorem batch_28_14_ok : batch_28_14_values.all id = true := by decide

def batch_28_15_values : List Bool := [accepted_1430]
theorem batch_28_15_ok : batch_28_15_values.all id = true := by decide

def batch_28_16_values : List Bool := [accepted_1432]
theorem batch_28_16_ok : batch_28_16_values.all id = true := by decide

def batch_28_17_values : List Bool := [accepted_1436]
theorem batch_28_17_ok : batch_28_17_values.all id = true := by decide

def batch_28_18_values : List Bool := [accepted_1437]
theorem batch_28_18_ok : batch_28_18_values.all id = true := by decide

def batch_28_19_values : List Bool := [accepted_1438]
theorem batch_28_19_ok : batch_28_19_values.all id = true := by decide

def batch_28_20_values : List Bool := [accepted_1439]
theorem batch_28_20_ok : batch_28_20_values.all id = true := by decide

def batch_28_21_values : List Bool := [accepted_1443]
theorem batch_28_21_ok : batch_28_21_values.all id = true := by decide

def batch_28_22_values : List Bool := [accepted_1444]
theorem batch_28_22_ok : batch_28_22_values.all id = true := by decide

def batch_28_23_values : List Bool := [accepted_1445]
theorem batch_28_23_ok : batch_28_23_values.all id = true := by decide

def batch_28_24_values : List Bool := [accepted_1446]
theorem batch_28_24_ok : batch_28_24_values.all id = true := by decide

def batch_28_25_values : List Bool := [accepted_1449]
theorem batch_28_25_ok : batch_28_25_values.all id = true := by decide

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

theorem leaf_1402_ok : checkAt 527 1000 box_1402 cert_1402 = true := by
  have h := List.all_eq_true.mp batch_28_01_ok accepted_1402 (by simp [batch_28_01_values])
  exact h
theorem leaf_1402_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1402.profileLo box_1402.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1402_ok
theorem branch_box_1402_nonnegative : ∀ j, 0 ≤ branch_box_1402.lower j ∧ 0 ≤ branch_box_1402.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1402, Box.profileLo, Box.profileHi, box_1402]
theorem leaf_1402_BranchSafe : CertificateConsequences.BranchSafe branch_box_1402 := by
  left; refine ⟨branch_box_1402_nonnegative, ?_⟩
  intro z hz; exact leaf_1402_sound hz

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

theorem leaf_1404_ok : checkAt 527 1000 box_1404 cert_1404 = true := by
  have h := List.all_eq_true.mp batch_28_03_ok accepted_1404 (by simp [batch_28_03_values])
  exact h
theorem leaf_1404_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1404.profileLo box_1404.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1404_ok
theorem branch_box_1404_nonnegative : ∀ j, 0 ≤ branch_box_1404.lower j ∧ 0 ≤ branch_box_1404.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1404, Box.profileLo, Box.profileHi, box_1404]
theorem leaf_1404_BranchSafe : CertificateConsequences.BranchSafe branch_box_1404 := by
  left; refine ⟨branch_box_1404_nonnegative, ?_⟩
  intro z hz; exact leaf_1404_sound hz

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

theorem leaf_1411_ok : checkAt 527 1000 box_1411 cert_1411 = true := by
  have h := List.all_eq_true.mp batch_28_05_ok accepted_1411 (by simp [batch_28_05_values])
  exact h
theorem leaf_1411_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1411.profileLo box_1411.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1411_ok
theorem branch_box_1411_nonnegative : ∀ j, 0 ≤ branch_box_1411.lower j ∧ 0 ≤ branch_box_1411.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1411, Box.profileLo, Box.profileHi, box_1411]
theorem leaf_1411_BranchSafe : CertificateConsequences.BranchSafe branch_box_1411 := by
  left; refine ⟨branch_box_1411_nonnegative, ?_⟩
  intro z hz; exact leaf_1411_sound hz

theorem leaf_1412_ok : checkAt 527 1000 box_1412 cert_1412 = true := by
  have h := List.all_eq_true.mp batch_28_06_ok accepted_1412 (by simp [batch_28_06_values])
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

theorem leaf_1414_ok : checkAt 527 1000 box_1414 cert_1414 = true := by
  have h := List.all_eq_true.mp batch_28_07_ok accepted_1414 (by simp [batch_28_07_values])
  exact h
theorem leaf_1414_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1414.profileLo box_1414.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1414_ok
theorem branch_box_1414_nonnegative : ∀ j, 0 ≤ branch_box_1414.lower j ∧ 0 ≤ branch_box_1414.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1414, Box.profileLo, Box.profileHi, box_1414]
theorem leaf_1414_BranchSafe : CertificateConsequences.BranchSafe branch_box_1414 := by
  left; refine ⟨branch_box_1414_nonnegative, ?_⟩
  intro z hz; exact leaf_1414_sound hz

theorem leaf_1417_ok : checkAt 527 1000 box_1417 cert_1417 = true := by
  have h := List.all_eq_true.mp batch_28_08_ok accepted_1417 (by simp [batch_28_08_values])
  exact h
theorem leaf_1417_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1417.profileLo box_1417.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1417_ok
theorem branch_box_1417_nonnegative : ∀ j, 0 ≤ branch_box_1417.lower j ∧ 0 ≤ branch_box_1417.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1417, Box.profileLo, Box.profileHi, box_1417]
theorem leaf_1417_BranchSafe : CertificateConsequences.BranchSafe branch_box_1417 := by
  left; refine ⟨branch_box_1417_nonnegative, ?_⟩
  intro z hz; exact leaf_1417_sound hz

theorem leaf_1419_ok : checkAt 527 1000 box_1419 cert_1419 = true := by
  have h := List.all_eq_true.mp batch_28_09_ok accepted_1419 (by simp [batch_28_09_values])
  exact h
theorem leaf_1419_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1419.profileLo box_1419.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1419_ok
theorem branch_box_1419_nonnegative : ∀ j, 0 ≤ branch_box_1419.lower j ∧ 0 ≤ branch_box_1419.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1419, Box.profileLo, Box.profileHi, box_1419]
theorem leaf_1419_BranchSafe : CertificateConsequences.BranchSafe branch_box_1419 := by
  left; refine ⟨branch_box_1419_nonnegative, ?_⟩
  intro z hz; exact leaf_1419_sound hz

theorem leaf_1420_ok : checkAt 527 1000 box_1420 cert_1420 = true := by
  have h := List.all_eq_true.mp batch_28_10_ok accepted_1420 (by simp [batch_28_10_values])
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
  have h := List.all_eq_true.mp batch_28_11_ok accepted_1421 (by simp [batch_28_11_values])
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

theorem leaf_1422_ok : checkAt 527 1000 box_1422 cert_1422 = true := by
  have h := List.all_eq_true.mp batch_28_12_ok accepted_1422 (by simp [batch_28_12_values])
  exact h
theorem leaf_1422_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1422.profileLo box_1422.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1422_ok
theorem branch_box_1422_nonnegative : ∀ j, 0 ≤ branch_box_1422.lower j ∧ 0 ≤ branch_box_1422.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1422, Box.profileLo, Box.profileHi, box_1422]
theorem leaf_1422_BranchSafe : CertificateConsequences.BranchSafe branch_box_1422 := by
  left; refine ⟨branch_box_1422_nonnegative, ?_⟩
  intro z hz; exact leaf_1422_sound hz

theorem leaf_1427_ok : checkAt 527 1000 box_1427 cert_1427 = true := by
  have h := List.all_eq_true.mp batch_28_13_ok accepted_1427 (by simp [batch_28_13_values])
  exact h
theorem leaf_1427_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1427.profileLo box_1427.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1427_ok
theorem branch_box_1427_nonnegative : ∀ j, 0 ≤ branch_box_1427.lower j ∧ 0 ≤ branch_box_1427.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1427, Box.profileLo, Box.profileHi, box_1427]
theorem leaf_1427_BranchSafe : CertificateConsequences.BranchSafe branch_box_1427 := by
  left; refine ⟨branch_box_1427_nonnegative, ?_⟩
  intro z hz; exact leaf_1427_sound hz

theorem leaf_1429_ok : checkAt 527 1000 box_1429 cert_1429 = true := by
  have h := List.all_eq_true.mp batch_28_14_ok accepted_1429 (by simp [batch_28_14_values])
  exact h
theorem leaf_1429_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1429.profileLo box_1429.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1429_ok
theorem branch_box_1429_nonnegative : ∀ j, 0 ≤ branch_box_1429.lower j ∧ 0 ≤ branch_box_1429.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1429, Box.profileLo, Box.profileHi, box_1429]
theorem leaf_1429_BranchSafe : CertificateConsequences.BranchSafe branch_box_1429 := by
  left; refine ⟨branch_box_1429_nonnegative, ?_⟩
  intro z hz; exact leaf_1429_sound hz

theorem leaf_1430_ok : checkAt 527 1000 box_1430 cert_1430 = true := by
  have h := List.all_eq_true.mp batch_28_15_ok accepted_1430 (by simp [batch_28_15_values])
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
  have h := List.all_eq_true.mp batch_28_16_ok accepted_1432 (by simp [batch_28_16_values])
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

theorem leaf_1437_ok : checkAt 527 1000 box_1437 cert_1437 = true := by
  have h := List.all_eq_true.mp batch_28_18_ok accepted_1437 (by simp [batch_28_18_values])
  exact h
theorem leaf_1437_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1437.profileLo box_1437.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1437_ok
theorem branch_box_1437_nonnegative : ∀ j, 0 ≤ branch_box_1437.lower j ∧ 0 ≤ branch_box_1437.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1437, Box.profileLo, Box.profileHi, box_1437]
theorem leaf_1437_BranchSafe : CertificateConsequences.BranchSafe branch_box_1437 := by
  left; refine ⟨branch_box_1437_nonnegative, ?_⟩
  intro z hz; exact leaf_1437_sound hz

theorem leaf_1438_ok : checkAt 527 1000 box_1438 cert_1438 = true := by
  have h := List.all_eq_true.mp batch_28_19_ok accepted_1438 (by simp [batch_28_19_values])
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

theorem leaf_1439_ok : checkAt 527 1000 box_1439 cert_1439 = true := by
  have h := List.all_eq_true.mp batch_28_20_ok accepted_1439 (by simp [batch_28_20_values])
  exact h
theorem leaf_1439_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1439.profileLo box_1439.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1439_ok
theorem branch_box_1439_nonnegative : ∀ j, 0 ≤ branch_box_1439.lower j ∧ 0 ≤ branch_box_1439.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1439, Box.profileLo, Box.profileHi, box_1439]
theorem leaf_1439_BranchSafe : CertificateConsequences.BranchSafe branch_box_1439 := by
  left; refine ⟨branch_box_1439_nonnegative, ?_⟩
  intro z hz; exact leaf_1439_sound hz

theorem leaf_1443_ok : checkAt 527 1000 box_1443 cert_1443 = true := by
  have h := List.all_eq_true.mp batch_28_21_ok accepted_1443 (by simp [batch_28_21_values])
  exact h
theorem leaf_1443_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1443.profileLo box_1443.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1443_ok
theorem branch_box_1443_nonnegative : ∀ j, 0 ≤ branch_box_1443.lower j ∧ 0 ≤ branch_box_1443.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1443, Box.profileLo, Box.profileHi, box_1443]
theorem leaf_1443_BranchSafe : CertificateConsequences.BranchSafe branch_box_1443 := by
  left; refine ⟨branch_box_1443_nonnegative, ?_⟩
  intro z hz; exact leaf_1443_sound hz

theorem leaf_1444_ok : checkAt 527 1000 box_1444 cert_1444 = true := by
  have h := List.all_eq_true.mp batch_28_22_ok accepted_1444 (by simp [batch_28_22_values])
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
  have h := List.all_eq_true.mp batch_28_23_ok accepted_1445 (by simp [batch_28_23_values])
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

theorem leaf_1446_ok : checkAt 527 1000 box_1446 cert_1446 = true := by
  have h := List.all_eq_true.mp batch_28_24_ok accepted_1446 (by simp [batch_28_24_values])
  exact h
theorem leaf_1446_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1446.profileLo box_1446.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1446_ok
theorem branch_box_1446_nonnegative : ∀ j, 0 ≤ branch_box_1446.lower j ∧ 0 ≤ branch_box_1446.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1446, Box.profileLo, Box.profileHi, box_1446]
theorem leaf_1446_BranchSafe : CertificateConsequences.BranchSafe branch_box_1446 := by
  left; refine ⟨branch_box_1446_nonnegative, ?_⟩
  intro z hz; exact leaf_1446_sound hz

theorem leaf_1449_ok : checkAt 527 1000 box_1449 cert_1449 = true := by
  have h := List.all_eq_true.mp batch_28_25_ok accepted_1449 (by simp [batch_28_25_values])
  exact h
theorem leaf_1449_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1449.profileLo box_1449.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1449_ok
theorem branch_box_1449_nonnegative : ∀ j, 0 ≤ branch_box_1449.lower j ∧ 0 ≤ branch_box_1449.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1449, Box.profileLo, Box.profileHi, box_1449]
theorem leaf_1449_BranchSafe : CertificateConsequences.BranchSafe branch_box_1449 := by
  left; refine ⟨branch_box_1449_nonnegative, ?_⟩
  intro z hz; exact leaf_1449_sound hz

#print axioms batch_28_00_ok
#print axioms leaf_1400_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
