import PeaceableQueens.UpperBound.Generated.Even.CoreScaled26Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_26_00_values : List Bool := [accepted_1302]
theorem batch_26_00_ok : batch_26_00_values.all id = true := by decide

def batch_26_01_values : List Bool := [accepted_1304]
theorem batch_26_01_ok : batch_26_01_values.all id = true := by decide

def batch_26_02_values : List Bool := [accepted_1306]
theorem batch_26_02_ok : batch_26_02_values.all id = true := by decide

def batch_26_03_values : List Bool := [accepted_1309]
theorem batch_26_03_ok : batch_26_03_values.all id = true := by decide

def batch_26_04_values : List Bool := [accepted_1318]
theorem batch_26_04_ok : batch_26_04_values.all id = true := by decide

def batch_26_05_values : List Bool := [accepted_1320]
theorem batch_26_05_ok : batch_26_05_values.all id = true := by decide

def batch_26_06_values : List Bool := [accepted_1324]
theorem batch_26_06_ok : batch_26_06_values.all id = true := by decide

def batch_26_07_values : List Bool := [accepted_1332]
theorem batch_26_07_ok : batch_26_07_values.all id = true := by decide

def batch_26_08_values : List Bool := [accepted_1334]
theorem batch_26_08_ok : batch_26_08_values.all id = true := by decide

def batch_26_09_values : List Bool := [accepted_1338]
theorem batch_26_09_ok : batch_26_09_values.all id = true := by decide

def batch_26_10_values : List Bool := [accepted_1342]
theorem batch_26_10_ok : batch_26_10_values.all id = true := by decide

def batch_26_11_values : List Bool := [accepted_1344]
theorem batch_26_11_ok : batch_26_11_values.all id = true := by decide

def batch_26_12_values : List Bool := [accepted_1345]
theorem batch_26_12_ok : batch_26_12_values.all id = true := by decide

def batch_26_13_values : List Bool := [accepted_1347]
theorem batch_26_13_ok : batch_26_13_values.all id = true := by decide

theorem leaf_1302_ok : checkAt 527 1000 box_1302 cert_1302 = true := by
  have h := List.all_eq_true.mp batch_26_00_ok accepted_1302 (by simp [batch_26_00_values])
  exact h
theorem leaf_1302_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1302.profileLo box_1302.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1302_ok
theorem branch_box_1302_nonnegative : ∀ j, 0 ≤ branch_box_1302.lower j ∧ 0 ≤ branch_box_1302.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1302, Box.profileLo, Box.profileHi, box_1302]
theorem leaf_1302_BranchSafe : CertificateConsequences.BranchSafe branch_box_1302 := by
  left; refine ⟨branch_box_1302_nonnegative, ?_⟩
  intro z hz; exact leaf_1302_sound hz

theorem leaf_1304_ok : checkAt 527 1000 box_1304 cert_1304 = true := by
  have h := List.all_eq_true.mp batch_26_01_ok accepted_1304 (by simp [batch_26_01_values])
  exact h
theorem leaf_1304_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1304.profileLo box_1304.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1304_ok
theorem branch_box_1304_nonnegative : ∀ j, 0 ≤ branch_box_1304.lower j ∧ 0 ≤ branch_box_1304.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1304, Box.profileLo, Box.profileHi, box_1304]
theorem leaf_1304_BranchSafe : CertificateConsequences.BranchSafe branch_box_1304 := by
  left; refine ⟨branch_box_1304_nonnegative, ?_⟩
  intro z hz; exact leaf_1304_sound hz

theorem leaf_1306_ok : checkAt 527 1000 box_1306 cert_1306 = true := by
  have h := List.all_eq_true.mp batch_26_02_ok accepted_1306 (by simp [batch_26_02_values])
  exact h
theorem leaf_1306_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1306.profileLo box_1306.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1306_ok
theorem branch_box_1306_nonnegative : ∀ j, 0 ≤ branch_box_1306.lower j ∧ 0 ≤ branch_box_1306.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1306, Box.profileLo, Box.profileHi, box_1306]
theorem leaf_1306_BranchSafe : CertificateConsequences.BranchSafe branch_box_1306 := by
  left; refine ⟨branch_box_1306_nonnegative, ?_⟩
  intro z hz; exact leaf_1306_sound hz

theorem leaf_1309_ok : checkAt 527 1000 box_1309 cert_1309 = true := by
  have h := List.all_eq_true.mp batch_26_03_ok accepted_1309 (by simp [batch_26_03_values])
  exact h
theorem leaf_1309_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1309.profileLo box_1309.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1309_ok
theorem branch_box_1309_nonnegative : ∀ j, 0 ≤ branch_box_1309.lower j ∧ 0 ≤ branch_box_1309.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1309, Box.profileLo, Box.profileHi, box_1309]
theorem leaf_1309_BranchSafe : CertificateConsequences.BranchSafe branch_box_1309 := by
  left; refine ⟨branch_box_1309_nonnegative, ?_⟩
  intro z hz; exact leaf_1309_sound hz

theorem leaf_1318_ok : checkAt 527 1000 box_1318 cert_1318 = true := by
  have h := List.all_eq_true.mp batch_26_04_ok accepted_1318 (by simp [batch_26_04_values])
  exact h
theorem leaf_1318_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1318.profileLo box_1318.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1318_ok
theorem branch_box_1318_nonnegative : ∀ j, 0 ≤ branch_box_1318.lower j ∧ 0 ≤ branch_box_1318.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1318, Box.profileLo, Box.profileHi, box_1318]
theorem leaf_1318_BranchSafe : CertificateConsequences.BranchSafe branch_box_1318 := by
  left; refine ⟨branch_box_1318_nonnegative, ?_⟩
  intro z hz; exact leaf_1318_sound hz

theorem leaf_1320_ok : checkAt 527 1000 box_1320 cert_1320 = true := by
  have h := List.all_eq_true.mp batch_26_05_ok accepted_1320 (by simp [batch_26_05_values])
  exact h
theorem leaf_1320_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1320.profileLo box_1320.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1320_ok
theorem branch_box_1320_nonnegative : ∀ j, 0 ≤ branch_box_1320.lower j ∧ 0 ≤ branch_box_1320.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1320, Box.profileLo, Box.profileHi, box_1320]
theorem leaf_1320_BranchSafe : CertificateConsequences.BranchSafe branch_box_1320 := by
  left; refine ⟨branch_box_1320_nonnegative, ?_⟩
  intro z hz; exact leaf_1320_sound hz

theorem leaf_1324_ok : checkAt 527 1000 box_1324 cert_1324 = true := by
  have h := List.all_eq_true.mp batch_26_06_ok accepted_1324 (by simp [batch_26_06_values])
  exact h
theorem leaf_1324_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1324.profileLo box_1324.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1324_ok
theorem branch_box_1324_nonnegative : ∀ j, 0 ≤ branch_box_1324.lower j ∧ 0 ≤ branch_box_1324.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1324, Box.profileLo, Box.profileHi, box_1324]
theorem leaf_1324_BranchSafe : CertificateConsequences.BranchSafe branch_box_1324 := by
  left; refine ⟨branch_box_1324_nonnegative, ?_⟩
  intro z hz; exact leaf_1324_sound hz

theorem leaf_1332_ok : checkAt 527 1000 box_1332 cert_1332 = true := by
  have h := List.all_eq_true.mp batch_26_07_ok accepted_1332 (by simp [batch_26_07_values])
  exact h
theorem leaf_1332_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1332.profileLo box_1332.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1332_ok
theorem branch_box_1332_nonnegative : ∀ j, 0 ≤ branch_box_1332.lower j ∧ 0 ≤ branch_box_1332.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1332, Box.profileLo, Box.profileHi, box_1332]
theorem leaf_1332_BranchSafe : CertificateConsequences.BranchSafe branch_box_1332 := by
  left; refine ⟨branch_box_1332_nonnegative, ?_⟩
  intro z hz; exact leaf_1332_sound hz

theorem leaf_1334_ok : checkAt 527 1000 box_1334 cert_1334 = true := by
  have h := List.all_eq_true.mp batch_26_08_ok accepted_1334 (by simp [batch_26_08_values])
  exact h
theorem leaf_1334_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1334.profileLo box_1334.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1334_ok
theorem branch_box_1334_nonnegative : ∀ j, 0 ≤ branch_box_1334.lower j ∧ 0 ≤ branch_box_1334.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1334, Box.profileLo, Box.profileHi, box_1334]
theorem leaf_1334_BranchSafe : CertificateConsequences.BranchSafe branch_box_1334 := by
  left; refine ⟨branch_box_1334_nonnegative, ?_⟩
  intro z hz; exact leaf_1334_sound hz

theorem leaf_1338_ok : checkAt 527 1000 box_1338 cert_1338 = true := by
  have h := List.all_eq_true.mp batch_26_09_ok accepted_1338 (by simp [batch_26_09_values])
  exact h
theorem leaf_1338_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1338.profileLo box_1338.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1338_ok
theorem branch_box_1338_nonnegative : ∀ j, 0 ≤ branch_box_1338.lower j ∧ 0 ≤ branch_box_1338.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1338, Box.profileLo, Box.profileHi, box_1338]
theorem leaf_1338_BranchSafe : CertificateConsequences.BranchSafe branch_box_1338 := by
  left; refine ⟨branch_box_1338_nonnegative, ?_⟩
  intro z hz; exact leaf_1338_sound hz

theorem leaf_1342_ok : checkAt 527 1000 box_1342 cert_1342 = true := by
  have h := List.all_eq_true.mp batch_26_10_ok accepted_1342 (by simp [batch_26_10_values])
  exact h
theorem leaf_1342_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1342.profileLo box_1342.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1342_ok
theorem branch_box_1342_nonnegative : ∀ j, 0 ≤ branch_box_1342.lower j ∧ 0 ≤ branch_box_1342.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1342, Box.profileLo, Box.profileHi, box_1342]
theorem leaf_1342_BranchSafe : CertificateConsequences.BranchSafe branch_box_1342 := by
  left; refine ⟨branch_box_1342_nonnegative, ?_⟩
  intro z hz; exact leaf_1342_sound hz

theorem leaf_1344_ok : checkAt 527 1000 box_1344 cert_1344 = true := by
  have h := List.all_eq_true.mp batch_26_11_ok accepted_1344 (by simp [batch_26_11_values])
  exact h
theorem leaf_1344_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1344.profileLo box_1344.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1344_ok
theorem branch_box_1344_nonnegative : ∀ j, 0 ≤ branch_box_1344.lower j ∧ 0 ≤ branch_box_1344.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1344, Box.profileLo, Box.profileHi, box_1344]
theorem leaf_1344_BranchSafe : CertificateConsequences.BranchSafe branch_box_1344 := by
  left; refine ⟨branch_box_1344_nonnegative, ?_⟩
  intro z hz; exact leaf_1344_sound hz

theorem leaf_1345_ok : checkAt 527 1000 box_1345 cert_1345 = true := by
  have h := List.all_eq_true.mp batch_26_12_ok accepted_1345 (by simp [batch_26_12_values])
  exact h
theorem leaf_1345_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1345.profileLo box_1345.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1345_ok
theorem branch_box_1345_nonnegative : ∀ j, 0 ≤ branch_box_1345.lower j ∧ 0 ≤ branch_box_1345.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1345, Box.profileLo, Box.profileHi, box_1345]
theorem leaf_1345_BranchSafe : CertificateConsequences.BranchSafe branch_box_1345 := by
  left; refine ⟨branch_box_1345_nonnegative, ?_⟩
  intro z hz; exact leaf_1345_sound hz

theorem leaf_1347_ok : checkAt 527 1000 box_1347 cert_1347 = true := by
  have h := List.all_eq_true.mp batch_26_13_ok accepted_1347 (by simp [batch_26_13_values])
  exact h
theorem leaf_1347_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1347.profileLo box_1347.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1347_ok
theorem branch_box_1347_nonnegative : ∀ j, 0 ≤ branch_box_1347.lower j ∧ 0 ≤ branch_box_1347.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1347, Box.profileLo, Box.profileHi, box_1347]
theorem leaf_1347_BranchSafe : CertificateConsequences.BranchSafe branch_box_1347 := by
  left; refine ⟨branch_box_1347_nonnegative, ?_⟩
  intro z hz; exact leaf_1347_sound hz

#print axioms batch_26_00_ok
#print axioms leaf_1302_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
