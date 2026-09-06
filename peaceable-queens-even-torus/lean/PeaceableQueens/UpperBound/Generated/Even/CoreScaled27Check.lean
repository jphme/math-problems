import PeaceableQueens.UpperBound.Generated.Even.CoreScaled27Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_27_00_values : List Bool := [accepted_1354]
theorem batch_27_00_ok : batch_27_00_values.all id = true := by decide

def batch_27_01_values : List Bool := [accepted_1355]
theorem batch_27_01_ok : batch_27_01_values.all id = true := by decide

def batch_27_02_values : List Bool := [accepted_1358]
theorem batch_27_02_ok : batch_27_02_values.all id = true := by decide

def batch_27_03_values : List Bool := [accepted_1359]
theorem batch_27_03_ok : batch_27_03_values.all id = true := by decide

def batch_27_04_values : List Bool := [accepted_1366]
theorem batch_27_04_ok : batch_27_04_values.all id = true := by decide

def batch_27_05_values : List Bool := [accepted_1368]
theorem batch_27_05_ok : batch_27_05_values.all id = true := by decide

def batch_27_06_values : List Bool := [accepted_1370]
theorem batch_27_06_ok : batch_27_06_values.all id = true := by decide

def batch_27_07_values : List Bool := [accepted_1372]
theorem batch_27_07_ok : batch_27_07_values.all id = true := by decide

def batch_27_08_values : List Bool := [accepted_1374]
theorem batch_27_08_ok : batch_27_08_values.all id = true := by decide

def batch_27_09_values : List Bool := [accepted_1377]
theorem batch_27_09_ok : batch_27_09_values.all id = true := by decide

def batch_27_10_values : List Bool := [accepted_1382]
theorem batch_27_10_ok : batch_27_10_values.all id = true := by decide

def batch_27_11_values : List Bool := [accepted_1384]
theorem batch_27_11_ok : batch_27_11_values.all id = true := by decide

def batch_27_12_values : List Bool := [accepted_1386]
theorem batch_27_12_ok : batch_27_12_values.all id = true := by decide

def batch_27_13_values : List Bool := [accepted_1392]
theorem batch_27_13_ok : batch_27_13_values.all id = true := by decide

def batch_27_14_values : List Bool := [accepted_1394]
theorem batch_27_14_ok : batch_27_14_values.all id = true := by decide

def batch_27_15_values : List Bool := [accepted_1396]
theorem batch_27_15_ok : batch_27_15_values.all id = true := by decide

def batch_27_16_values : List Bool := [accepted_1398]
theorem batch_27_16_ok : batch_27_16_values.all id = true := by decide

theorem leaf_1354_ok : checkAt 527 1000 box_1354 cert_1354 = true := by
  have h := List.all_eq_true.mp batch_27_00_ok accepted_1354 (by simp [batch_27_00_values])
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
  have h := List.all_eq_true.mp batch_27_01_ok accepted_1355 (by simp [batch_27_01_values])
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

theorem leaf_1358_ok : checkAt 527 1000 box_1358 cert_1358 = true := by
  have h := List.all_eq_true.mp batch_27_02_ok accepted_1358 (by simp [batch_27_02_values])
  exact h
theorem leaf_1358_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1358.profileLo box_1358.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1358_ok
theorem branch_box_1358_nonnegative : ∀ j, 0 ≤ branch_box_1358.lower j ∧ 0 ≤ branch_box_1358.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1358, Box.profileLo, Box.profileHi, box_1358]
theorem leaf_1358_BranchSafe : CertificateConsequences.BranchSafe branch_box_1358 := by
  left; refine ⟨branch_box_1358_nonnegative, ?_⟩
  intro z hz; exact leaf_1358_sound hz

theorem leaf_1359_ok : checkAt 527 1000 box_1359 cert_1359 = true := by
  have h := List.all_eq_true.mp batch_27_03_ok accepted_1359 (by simp [batch_27_03_values])
  exact h
theorem leaf_1359_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1359.profileLo box_1359.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1359_ok
theorem branch_box_1359_nonnegative : ∀ j, 0 ≤ branch_box_1359.lower j ∧ 0 ≤ branch_box_1359.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1359, Box.profileLo, Box.profileHi, box_1359]
theorem leaf_1359_BranchSafe : CertificateConsequences.BranchSafe branch_box_1359 := by
  left; refine ⟨branch_box_1359_nonnegative, ?_⟩
  intro z hz; exact leaf_1359_sound hz

theorem leaf_1366_ok : checkAt 527 1000 box_1366 cert_1366 = true := by
  have h := List.all_eq_true.mp batch_27_04_ok accepted_1366 (by simp [batch_27_04_values])
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

theorem leaf_1368_ok : checkAt 527 1000 box_1368 cert_1368 = true := by
  have h := List.all_eq_true.mp batch_27_05_ok accepted_1368 (by simp [batch_27_05_values])
  exact h
theorem leaf_1368_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1368.profileLo box_1368.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1368_ok
theorem branch_box_1368_nonnegative : ∀ j, 0 ≤ branch_box_1368.lower j ∧ 0 ≤ branch_box_1368.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1368, Box.profileLo, Box.profileHi, box_1368]
theorem leaf_1368_BranchSafe : CertificateConsequences.BranchSafe branch_box_1368 := by
  left; refine ⟨branch_box_1368_nonnegative, ?_⟩
  intro z hz; exact leaf_1368_sound hz

theorem leaf_1370_ok : checkAt 527 1000 box_1370 cert_1370 = true := by
  have h := List.all_eq_true.mp batch_27_06_ok accepted_1370 (by simp [batch_27_06_values])
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

theorem leaf_1372_ok : checkAt 527 1000 box_1372 cert_1372 = true := by
  have h := List.all_eq_true.mp batch_27_07_ok accepted_1372 (by simp [batch_27_07_values])
  exact h
theorem leaf_1372_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1372.profileLo box_1372.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1372_ok
theorem branch_box_1372_nonnegative : ∀ j, 0 ≤ branch_box_1372.lower j ∧ 0 ≤ branch_box_1372.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1372, Box.profileLo, Box.profileHi, box_1372]
theorem leaf_1372_BranchSafe : CertificateConsequences.BranchSafe branch_box_1372 := by
  left; refine ⟨branch_box_1372_nonnegative, ?_⟩
  intro z hz; exact leaf_1372_sound hz

theorem leaf_1374_ok : checkAt 527 1000 box_1374 cert_1374 = true := by
  have h := List.all_eq_true.mp batch_27_08_ok accepted_1374 (by simp [batch_27_08_values])
  exact h
theorem leaf_1374_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1374.profileLo box_1374.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1374_ok
theorem branch_box_1374_nonnegative : ∀ j, 0 ≤ branch_box_1374.lower j ∧ 0 ≤ branch_box_1374.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1374, Box.profileLo, Box.profileHi, box_1374]
theorem leaf_1374_BranchSafe : CertificateConsequences.BranchSafe branch_box_1374 := by
  left; refine ⟨branch_box_1374_nonnegative, ?_⟩
  intro z hz; exact leaf_1374_sound hz

theorem leaf_1377_ok : checkAt 527 1000 box_1377 cert_1377 = true := by
  have h := List.all_eq_true.mp batch_27_09_ok accepted_1377 (by simp [batch_27_09_values])
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

theorem leaf_1382_ok : checkAt 527 1000 box_1382 cert_1382 = true := by
  have h := List.all_eq_true.mp batch_27_10_ok accepted_1382 (by simp [batch_27_10_values])
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
  have h := List.all_eq_true.mp batch_27_11_ok accepted_1384 (by simp [batch_27_11_values])
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

theorem leaf_1386_ok : checkAt 527 1000 box_1386 cert_1386 = true := by
  have h := List.all_eq_true.mp batch_27_12_ok accepted_1386 (by simp [batch_27_12_values])
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

theorem leaf_1392_ok : checkAt 527 1000 box_1392 cert_1392 = true := by
  have h := List.all_eq_true.mp batch_27_13_ok accepted_1392 (by simp [batch_27_13_values])
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

theorem leaf_1394_ok : checkAt 527 1000 box_1394 cert_1394 = true := by
  have h := List.all_eq_true.mp batch_27_14_ok accepted_1394 (by simp [batch_27_14_values])
  exact h
theorem leaf_1394_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1394.profileLo box_1394.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1394_ok
theorem branch_box_1394_nonnegative : ∀ j, 0 ≤ branch_box_1394.lower j ∧ 0 ≤ branch_box_1394.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1394, Box.profileLo, Box.profileHi, box_1394]
theorem leaf_1394_BranchSafe : CertificateConsequences.BranchSafe branch_box_1394 := by
  left; refine ⟨branch_box_1394_nonnegative, ?_⟩
  intro z hz; exact leaf_1394_sound hz

theorem leaf_1396_ok : checkAt 527 1000 box_1396 cert_1396 = true := by
  have h := List.all_eq_true.mp batch_27_15_ok accepted_1396 (by simp [batch_27_15_values])
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

theorem leaf_1398_ok : checkAt 527 1000 box_1398 cert_1398 = true := by
  have h := List.all_eq_true.mp batch_27_16_ok accepted_1398 (by simp [batch_27_16_values])
  exact h
theorem leaf_1398_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1398.profileLo box_1398.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1398_ok
theorem branch_box_1398_nonnegative : ∀ j, 0 ≤ branch_box_1398.lower j ∧ 0 ≤ branch_box_1398.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1398, Box.profileLo, Box.profileHi, box_1398]
theorem leaf_1398_BranchSafe : CertificateConsequences.BranchSafe branch_box_1398 := by
  left; refine ⟨branch_box_1398_nonnegative, ?_⟩
  intro z hz; exact leaf_1398_sound hz

#print axioms batch_27_00_ok
#print axioms leaf_1354_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
