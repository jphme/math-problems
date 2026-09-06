import PeaceableQueens.UpperBound.Generated.Even.C527Scaled27Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_27_00_values : List Bool := [accepted_1350]
theorem batch_27_00_ok : batch_27_00_values.all id = true := by decide

def batch_27_01_values : List Bool := [accepted_1351]
theorem batch_27_01_ok : batch_27_01_values.all id = true := by decide

def batch_27_02_values : List Bool := [accepted_1352]
theorem batch_27_02_ok : batch_27_02_values.all id = true := by decide

def batch_27_03_values : List Bool := [accepted_1354]
theorem batch_27_03_ok : batch_27_03_values.all id = true := by decide

def batch_27_04_values : List Bool := [accepted_1355]
theorem batch_27_04_ok : batch_27_04_values.all id = true := by decide

def batch_27_05_values : List Bool := [accepted_1360]
theorem batch_27_05_ok : batch_27_05_values.all id = true := by decide

def batch_27_06_values : List Bool := [accepted_1361]
theorem batch_27_06_ok : batch_27_06_values.all id = true := by decide

def batch_27_07_values : List Bool := [accepted_1362]
theorem batch_27_07_ok : batch_27_07_values.all id = true := by decide

def batch_27_08_values : List Bool := [accepted_1364]
theorem batch_27_08_ok : batch_27_08_values.all id = true := by decide

def batch_27_09_values : List Bool := [accepted_1365]
theorem batch_27_09_ok : batch_27_09_values.all id = true := by decide

def batch_27_10_values : List Bool := [accepted_1366]
theorem batch_27_10_ok : batch_27_10_values.all id = true := by decide

def batch_27_11_values : List Bool := [accepted_1370]
theorem batch_27_11_ok : batch_27_11_values.all id = true := by decide

def batch_27_12_values : List Bool := [accepted_1377]
theorem batch_27_12_ok : batch_27_12_values.all id = true := by decide

def batch_27_13_values : List Bool := [accepted_1378]
theorem batch_27_13_ok : batch_27_13_values.all id = true := by decide

def batch_27_14_values : List Bool := [accepted_1379]
theorem batch_27_14_ok : batch_27_14_values.all id = true := by decide

def batch_27_15_values : List Bool := [accepted_1380]
theorem batch_27_15_ok : batch_27_15_values.all id = true := by decide

def batch_27_16_values : List Bool := [accepted_1381]
theorem batch_27_16_ok : batch_27_16_values.all id = true := by decide

def batch_27_17_values : List Bool := [accepted_1382]
theorem batch_27_17_ok : batch_27_17_values.all id = true := by decide

def batch_27_18_values : List Bool := [accepted_1384]
theorem batch_27_18_ok : batch_27_18_values.all id = true := by decide

def batch_27_19_values : List Bool := [accepted_1385]
theorem batch_27_19_ok : batch_27_19_values.all id = true := by decide

def batch_27_20_values : List Bool := [accepted_1386]
theorem batch_27_20_ok : batch_27_20_values.all id = true := by decide

def batch_27_21_values : List Bool := [accepted_1388]
theorem batch_27_21_ok : batch_27_21_values.all id = true := by decide

def batch_27_22_values : List Bool := [accepted_1391]
theorem batch_27_22_ok : batch_27_22_values.all id = true := by decide

def batch_27_23_values : List Bool := [accepted_1392]
theorem batch_27_23_ok : batch_27_23_values.all id = true := by decide

def batch_27_24_values : List Bool := [accepted_1396]
theorem batch_27_24_ok : batch_27_24_values.all id = true := by decide

def batch_27_25_values : List Bool := [accepted_1397]
theorem batch_27_25_ok : batch_27_25_values.all id = true := by decide

def batch_27_26_values : List Bool := [accepted_1399]
theorem batch_27_26_ok : batch_27_26_values.all id = true := by decide

theorem leaf_1350_ok : checkAt 527 1000 box_1350 cert_1350 = true := by
  have h := List.all_eq_true.mp batch_27_00_ok accepted_1350 (by simp [batch_27_00_values])
  exact h
theorem leaf_1350_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1350.profileLo box_1350.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1350_ok
theorem branch_box_1350_nonnegative : ∀ j, 0 ≤ branch_box_1350.lower j ∧ 0 ≤ branch_box_1350.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1350, Box.profileLo, Box.profileHi, box_1350]
theorem leaf_1350_BranchSafe : CertificateConsequences.BranchSafe branch_box_1350 := by
  left; refine ⟨branch_box_1350_nonnegative, ?_⟩
  intro z hz; exact leaf_1350_sound hz

theorem leaf_1351_ok : checkAt 527 1000 box_1351 cert_1351 = true := by
  have h := List.all_eq_true.mp batch_27_01_ok accepted_1351 (by simp [batch_27_01_values])
  exact h
theorem leaf_1351_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1351.profileLo box_1351.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1351_ok
theorem branch_box_1351_nonnegative : ∀ j, 0 ≤ branch_box_1351.lower j ∧ 0 ≤ branch_box_1351.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1351, Box.profileLo, Box.profileHi, box_1351]
theorem leaf_1351_BranchSafe : CertificateConsequences.BranchSafe branch_box_1351 := by
  left; refine ⟨branch_box_1351_nonnegative, ?_⟩
  intro z hz; exact leaf_1351_sound hz

theorem leaf_1352_ok : checkAt 527 1000 box_1352 cert_1352 = true := by
  have h := List.all_eq_true.mp batch_27_02_ok accepted_1352 (by simp [batch_27_02_values])
  exact h
theorem leaf_1352_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1352.profileLo box_1352.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1352_ok
theorem branch_box_1352_nonnegative : ∀ j, 0 ≤ branch_box_1352.lower j ∧ 0 ≤ branch_box_1352.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1352, Box.profileLo, Box.profileHi, box_1352]
theorem leaf_1352_BranchSafe : CertificateConsequences.BranchSafe branch_box_1352 := by
  left; refine ⟨branch_box_1352_nonnegative, ?_⟩
  intro z hz; exact leaf_1352_sound hz

theorem leaf_1354_ok : checkAt 527 1000 box_1354 cert_1354 = true := by
  have h := List.all_eq_true.mp batch_27_03_ok accepted_1354 (by simp [batch_27_03_values])
  exact h
theorem leaf_1354_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1354.profileLo box_1354.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1354_ok
theorem branch_box_1354_nonnegative : ∀ j, 0 ≤ branch_box_1354.lower j ∧ 0 ≤ branch_box_1354.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1354, Box.profileLo, Box.profileHi, box_1354]
theorem leaf_1354_BranchSafe : CertificateConsequences.BranchSafe branch_box_1354 := by
  left; refine ⟨branch_box_1354_nonnegative, ?_⟩
  intro z hz; exact leaf_1354_sound hz

theorem leaf_1355_ok : checkAt 527 1000 box_1355 cert_1355 = true := by
  have h := List.all_eq_true.mp batch_27_04_ok accepted_1355 (by simp [batch_27_04_values])
  exact h
theorem leaf_1355_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1355.profileLo box_1355.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1355_ok
theorem branch_box_1355_nonnegative : ∀ j, 0 ≤ branch_box_1355.lower j ∧ 0 ≤ branch_box_1355.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1355, Box.profileLo, Box.profileHi, box_1355]
theorem leaf_1355_BranchSafe : CertificateConsequences.BranchSafe branch_box_1355 := by
  left; refine ⟨branch_box_1355_nonnegative, ?_⟩
  intro z hz; exact leaf_1355_sound hz

theorem leaf_1360_ok : checkAt 527 1000 box_1360 cert_1360 = true := by
  have h := List.all_eq_true.mp batch_27_05_ok accepted_1360 (by simp [batch_27_05_values])
  exact h
theorem leaf_1360_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1360.profileLo box_1360.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1360_ok
theorem branch_box_1360_nonnegative : ∀ j, 0 ≤ branch_box_1360.lower j ∧ 0 ≤ branch_box_1360.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1360, Box.profileLo, Box.profileHi, box_1360]
theorem leaf_1360_BranchSafe : CertificateConsequences.BranchSafe branch_box_1360 := by
  left; refine ⟨branch_box_1360_nonnegative, ?_⟩
  intro z hz; exact leaf_1360_sound hz

theorem leaf_1361_ok : checkAt 527 1000 box_1361 cert_1361 = true := by
  have h := List.all_eq_true.mp batch_27_06_ok accepted_1361 (by simp [batch_27_06_values])
  exact h
theorem leaf_1361_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1361.profileLo box_1361.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1361_ok
theorem branch_box_1361_nonnegative : ∀ j, 0 ≤ branch_box_1361.lower j ∧ 0 ≤ branch_box_1361.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1361, Box.profileLo, Box.profileHi, box_1361]
theorem leaf_1361_BranchSafe : CertificateConsequences.BranchSafe branch_box_1361 := by
  left; refine ⟨branch_box_1361_nonnegative, ?_⟩
  intro z hz; exact leaf_1361_sound hz

theorem leaf_1362_ok : checkAt 527 1000 box_1362 cert_1362 = true := by
  have h := List.all_eq_true.mp batch_27_07_ok accepted_1362 (by simp [batch_27_07_values])
  exact h
theorem leaf_1362_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1362.profileLo box_1362.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1362_ok
theorem branch_box_1362_nonnegative : ∀ j, 0 ≤ branch_box_1362.lower j ∧ 0 ≤ branch_box_1362.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1362, Box.profileLo, Box.profileHi, box_1362]
theorem leaf_1362_BranchSafe : CertificateConsequences.BranchSafe branch_box_1362 := by
  left; refine ⟨branch_box_1362_nonnegative, ?_⟩
  intro z hz; exact leaf_1362_sound hz

theorem leaf_1364_ok : checkAt 527 1000 box_1364 cert_1364 = true := by
  have h := List.all_eq_true.mp batch_27_08_ok accepted_1364 (by simp [batch_27_08_values])
  exact h
theorem leaf_1364_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1364.profileLo box_1364.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1364_ok
theorem branch_box_1364_nonnegative : ∀ j, 0 ≤ branch_box_1364.lower j ∧ 0 ≤ branch_box_1364.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1364, Box.profileLo, Box.profileHi, box_1364]
theorem leaf_1364_BranchSafe : CertificateConsequences.BranchSafe branch_box_1364 := by
  left; refine ⟨branch_box_1364_nonnegative, ?_⟩
  intro z hz; exact leaf_1364_sound hz

theorem leaf_1365_ok : checkAt 527 1000 box_1365 cert_1365 = true := by
  have h := List.all_eq_true.mp batch_27_09_ok accepted_1365 (by simp [batch_27_09_values])
  exact h
theorem leaf_1365_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1365.profileLo box_1365.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1365_ok
theorem branch_box_1365_nonnegative : ∀ j, 0 ≤ branch_box_1365.lower j ∧ 0 ≤ branch_box_1365.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1365, Box.profileLo, Box.profileHi, box_1365]
theorem leaf_1365_BranchSafe : CertificateConsequences.BranchSafe branch_box_1365 := by
  left; refine ⟨branch_box_1365_nonnegative, ?_⟩
  intro z hz; exact leaf_1365_sound hz

theorem leaf_1366_ok : checkAt 527 1000 box_1366 cert_1366 = true := by
  have h := List.all_eq_true.mp batch_27_10_ok accepted_1366 (by simp [batch_27_10_values])
  exact h
theorem leaf_1366_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1366.profileLo box_1366.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1366_ok
theorem branch_box_1366_nonnegative : ∀ j, 0 ≤ branch_box_1366.lower j ∧ 0 ≤ branch_box_1366.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1366, Box.profileLo, Box.profileHi, box_1366]
theorem leaf_1366_BranchSafe : CertificateConsequences.BranchSafe branch_box_1366 := by
  left; refine ⟨branch_box_1366_nonnegative, ?_⟩
  intro z hz; exact leaf_1366_sound hz

theorem leaf_1370_ok : checkAt 527 1000 box_1370 cert_1370 = true := by
  have h := List.all_eq_true.mp batch_27_11_ok accepted_1370 (by simp [batch_27_11_values])
  exact h
theorem leaf_1370_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1370.profileLo box_1370.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1370_ok
theorem branch_box_1370_nonnegative : ∀ j, 0 ≤ branch_box_1370.lower j ∧ 0 ≤ branch_box_1370.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1370, Box.profileLo, Box.profileHi, box_1370]
theorem leaf_1370_BranchSafe : CertificateConsequences.BranchSafe branch_box_1370 := by
  left; refine ⟨branch_box_1370_nonnegative, ?_⟩
  intro z hz; exact leaf_1370_sound hz

theorem leaf_1377_ok : checkAt 527 1000 box_1377 cert_1377 = true := by
  have h := List.all_eq_true.mp batch_27_12_ok accepted_1377 (by simp [batch_27_12_values])
  exact h
theorem leaf_1377_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1377.profileLo box_1377.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1377_ok
theorem branch_box_1377_nonnegative : ∀ j, 0 ≤ branch_box_1377.lower j ∧ 0 ≤ branch_box_1377.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1377, Box.profileLo, Box.profileHi, box_1377]
theorem leaf_1377_BranchSafe : CertificateConsequences.BranchSafe branch_box_1377 := by
  left; refine ⟨branch_box_1377_nonnegative, ?_⟩
  intro z hz; exact leaf_1377_sound hz

theorem leaf_1378_ok : checkAt 527 1000 box_1378 cert_1378 = true := by
  have h := List.all_eq_true.mp batch_27_13_ok accepted_1378 (by simp [batch_27_13_values])
  exact h
theorem leaf_1378_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1378.profileLo box_1378.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1378_ok
theorem branch_box_1378_nonnegative : ∀ j, 0 ≤ branch_box_1378.lower j ∧ 0 ≤ branch_box_1378.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1378, Box.profileLo, Box.profileHi, box_1378]
theorem leaf_1378_BranchSafe : CertificateConsequences.BranchSafe branch_box_1378 := by
  left; refine ⟨branch_box_1378_nonnegative, ?_⟩
  intro z hz; exact leaf_1378_sound hz

theorem leaf_1379_ok : checkAt 527 1000 box_1379 cert_1379 = true := by
  have h := List.all_eq_true.mp batch_27_14_ok accepted_1379 (by simp [batch_27_14_values])
  exact h
theorem leaf_1379_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1379.profileLo box_1379.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1379_ok
theorem branch_box_1379_nonnegative : ∀ j, 0 ≤ branch_box_1379.lower j ∧ 0 ≤ branch_box_1379.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1379, Box.profileLo, Box.profileHi, box_1379]
theorem leaf_1379_BranchSafe : CertificateConsequences.BranchSafe branch_box_1379 := by
  left; refine ⟨branch_box_1379_nonnegative, ?_⟩
  intro z hz; exact leaf_1379_sound hz

theorem leaf_1380_ok : checkAt 527 1000 box_1380 cert_1380 = true := by
  have h := List.all_eq_true.mp batch_27_15_ok accepted_1380 (by simp [batch_27_15_values])
  exact h
theorem leaf_1380_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1380.profileLo box_1380.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1380_ok
theorem branch_box_1380_nonnegative : ∀ j, 0 ≤ branch_box_1380.lower j ∧ 0 ≤ branch_box_1380.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1380, Box.profileLo, Box.profileHi, box_1380]
theorem leaf_1380_BranchSafe : CertificateConsequences.BranchSafe branch_box_1380 := by
  left; refine ⟨branch_box_1380_nonnegative, ?_⟩
  intro z hz; exact leaf_1380_sound hz

theorem leaf_1381_ok : checkAt 527 1000 box_1381 cert_1381 = true := by
  have h := List.all_eq_true.mp batch_27_16_ok accepted_1381 (by simp [batch_27_16_values])
  exact h
theorem leaf_1381_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1381.profileLo box_1381.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1381_ok
theorem branch_box_1381_nonnegative : ∀ j, 0 ≤ branch_box_1381.lower j ∧ 0 ≤ branch_box_1381.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1381, Box.profileLo, Box.profileHi, box_1381]
theorem leaf_1381_BranchSafe : CertificateConsequences.BranchSafe branch_box_1381 := by
  left; refine ⟨branch_box_1381_nonnegative, ?_⟩
  intro z hz; exact leaf_1381_sound hz

theorem leaf_1382_ok : checkAt 527 1000 box_1382 cert_1382 = true := by
  have h := List.all_eq_true.mp batch_27_17_ok accepted_1382 (by simp [batch_27_17_values])
  exact h
theorem leaf_1382_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1382.profileLo box_1382.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1382_ok
theorem branch_box_1382_nonnegative : ∀ j, 0 ≤ branch_box_1382.lower j ∧ 0 ≤ branch_box_1382.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1382, Box.profileLo, Box.profileHi, box_1382]
theorem leaf_1382_BranchSafe : CertificateConsequences.BranchSafe branch_box_1382 := by
  left; refine ⟨branch_box_1382_nonnegative, ?_⟩
  intro z hz; exact leaf_1382_sound hz

theorem leaf_1384_ok : checkAt 527 1000 box_1384 cert_1384 = true := by
  have h := List.all_eq_true.mp batch_27_18_ok accepted_1384 (by simp [batch_27_18_values])
  exact h
theorem leaf_1384_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1384.profileLo box_1384.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1384_ok
theorem branch_box_1384_nonnegative : ∀ j, 0 ≤ branch_box_1384.lower j ∧ 0 ≤ branch_box_1384.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1384, Box.profileLo, Box.profileHi, box_1384]
theorem leaf_1384_BranchSafe : CertificateConsequences.BranchSafe branch_box_1384 := by
  left; refine ⟨branch_box_1384_nonnegative, ?_⟩
  intro z hz; exact leaf_1384_sound hz

theorem leaf_1385_ok : checkAt 527 1000 box_1385 cert_1385 = true := by
  have h := List.all_eq_true.mp batch_27_19_ok accepted_1385 (by simp [batch_27_19_values])
  exact h
theorem leaf_1385_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1385.profileLo box_1385.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1385_ok
theorem branch_box_1385_nonnegative : ∀ j, 0 ≤ branch_box_1385.lower j ∧ 0 ≤ branch_box_1385.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1385, Box.profileLo, Box.profileHi, box_1385]
theorem leaf_1385_BranchSafe : CertificateConsequences.BranchSafe branch_box_1385 := by
  left; refine ⟨branch_box_1385_nonnegative, ?_⟩
  intro z hz; exact leaf_1385_sound hz

theorem leaf_1386_ok : checkAt 527 1000 box_1386 cert_1386 = true := by
  have h := List.all_eq_true.mp batch_27_20_ok accepted_1386 (by simp [batch_27_20_values])
  exact h
theorem leaf_1386_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1386.profileLo box_1386.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1386_ok
theorem branch_box_1386_nonnegative : ∀ j, 0 ≤ branch_box_1386.lower j ∧ 0 ≤ branch_box_1386.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1386, Box.profileLo, Box.profileHi, box_1386]
theorem leaf_1386_BranchSafe : CertificateConsequences.BranchSafe branch_box_1386 := by
  left; refine ⟨branch_box_1386_nonnegative, ?_⟩
  intro z hz; exact leaf_1386_sound hz

theorem leaf_1388_ok : checkAt 527 1000 box_1388 cert_1388 = true := by
  have h := List.all_eq_true.mp batch_27_21_ok accepted_1388 (by simp [batch_27_21_values])
  exact h
theorem leaf_1388_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1388.profileLo box_1388.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1388_ok
theorem branch_box_1388_nonnegative : ∀ j, 0 ≤ branch_box_1388.lower j ∧ 0 ≤ branch_box_1388.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1388, Box.profileLo, Box.profileHi, box_1388]
theorem leaf_1388_BranchSafe : CertificateConsequences.BranchSafe branch_box_1388 := by
  left; refine ⟨branch_box_1388_nonnegative, ?_⟩
  intro z hz; exact leaf_1388_sound hz

theorem leaf_1391_ok : checkAt 527 1000 box_1391 cert_1391 = true := by
  have h := List.all_eq_true.mp batch_27_22_ok accepted_1391 (by simp [batch_27_22_values])
  exact h
theorem leaf_1391_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1391.profileLo box_1391.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1391_ok
theorem branch_box_1391_nonnegative : ∀ j, 0 ≤ branch_box_1391.lower j ∧ 0 ≤ branch_box_1391.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1391, Box.profileLo, Box.profileHi, box_1391]
theorem leaf_1391_BranchSafe : CertificateConsequences.BranchSafe branch_box_1391 := by
  left; refine ⟨branch_box_1391_nonnegative, ?_⟩
  intro z hz; exact leaf_1391_sound hz

theorem leaf_1392_ok : checkAt 527 1000 box_1392 cert_1392 = true := by
  have h := List.all_eq_true.mp batch_27_23_ok accepted_1392 (by simp [batch_27_23_values])
  exact h
theorem leaf_1392_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1392.profileLo box_1392.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1392_ok
theorem branch_box_1392_nonnegative : ∀ j, 0 ≤ branch_box_1392.lower j ∧ 0 ≤ branch_box_1392.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1392, Box.profileLo, Box.profileHi, box_1392]
theorem leaf_1392_BranchSafe : CertificateConsequences.BranchSafe branch_box_1392 := by
  left; refine ⟨branch_box_1392_nonnegative, ?_⟩
  intro z hz; exact leaf_1392_sound hz

theorem leaf_1396_ok : checkAt 527 1000 box_1396 cert_1396 = true := by
  have h := List.all_eq_true.mp batch_27_24_ok accepted_1396 (by simp [batch_27_24_values])
  exact h
theorem leaf_1396_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1396.profileLo box_1396.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1396_ok
theorem branch_box_1396_nonnegative : ∀ j, 0 ≤ branch_box_1396.lower j ∧ 0 ≤ branch_box_1396.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1396, Box.profileLo, Box.profileHi, box_1396]
theorem leaf_1396_BranchSafe : CertificateConsequences.BranchSafe branch_box_1396 := by
  left; refine ⟨branch_box_1396_nonnegative, ?_⟩
  intro z hz; exact leaf_1396_sound hz

theorem leaf_1397_ok : checkAt 527 1000 box_1397 cert_1397 = true := by
  have h := List.all_eq_true.mp batch_27_25_ok accepted_1397 (by simp [batch_27_25_values])
  exact h
theorem leaf_1397_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1397.profileLo box_1397.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1397_ok
theorem branch_box_1397_nonnegative : ∀ j, 0 ≤ branch_box_1397.lower j ∧ 0 ≤ branch_box_1397.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1397, Box.profileLo, Box.profileHi, box_1397]
theorem leaf_1397_BranchSafe : CertificateConsequences.BranchSafe branch_box_1397 := by
  left; refine ⟨branch_box_1397_nonnegative, ?_⟩
  intro z hz; exact leaf_1397_sound hz

theorem leaf_1399_ok : checkAt 527 1000 box_1399 cert_1399 = true := by
  have h := List.all_eq_true.mp batch_27_26_ok accepted_1399 (by simp [batch_27_26_values])
  exact h
theorem leaf_1399_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1399.profileLo box_1399.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1399_ok
theorem branch_box_1399_nonnegative : ∀ j, 0 ≤ branch_box_1399.lower j ∧ 0 ≤ branch_box_1399.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1399, Box.profileLo, Box.profileHi, box_1399]
theorem leaf_1399_BranchSafe : CertificateConsequences.BranchSafe branch_box_1399 := by
  left; refine ⟨branch_box_1399_nonnegative, ?_⟩
  intro z hz; exact leaf_1399_sound hz

#print axioms batch_27_00_ok
#print axioms leaf_1350_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
