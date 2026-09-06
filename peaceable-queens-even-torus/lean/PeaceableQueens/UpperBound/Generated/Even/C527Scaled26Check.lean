import PeaceableQueens.UpperBound.Generated.Even.C527Scaled26Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_26_00_values : List Bool := [accepted_1300]
theorem batch_26_00_ok : batch_26_00_values.all id = true := by decide

def batch_26_01_values : List Bool := [accepted_1301]
theorem batch_26_01_ok : batch_26_01_values.all id = true := by decide

def batch_26_02_values : List Bool := [accepted_1303]
theorem batch_26_02_ok : batch_26_02_values.all id = true := by decide

def batch_26_03_values : List Bool := [accepted_1304]
theorem batch_26_03_ok : batch_26_03_values.all id = true := by decide

def batch_26_04_values : List Bool := [accepted_1306]
theorem batch_26_04_ok : batch_26_04_values.all id = true := by decide

def batch_26_05_values : List Bool := [accepted_1307]
theorem batch_26_05_ok : batch_26_05_values.all id = true := by decide

def batch_26_06_values : List Bool := [accepted_1308]
theorem batch_26_06_ok : batch_26_06_values.all id = true := by decide

def batch_26_07_values : List Bool := [accepted_1315]
theorem batch_26_07_ok : batch_26_07_values.all id = true := by decide

def batch_26_08_values : List Bool := [accepted_1316]
theorem batch_26_08_ok : batch_26_08_values.all id = true := by decide

def batch_26_09_values : List Bool := [accepted_1319]
theorem batch_26_09_ok : batch_26_09_values.all id = true := by decide

def batch_26_10_values : List Bool := [accepted_1320]
theorem batch_26_10_ok : batch_26_10_values.all id = true := by decide

def batch_26_11_values : List Bool := [accepted_1321]
theorem batch_26_11_ok : batch_26_11_values.all id = true := by decide

def batch_26_12_values : List Bool := [accepted_1322]
theorem batch_26_12_ok : batch_26_12_values.all id = true := by decide

def batch_26_13_values : List Bool := [accepted_1323]
theorem batch_26_13_ok : batch_26_13_values.all id = true := by decide

def batch_26_14_values : List Bool := [accepted_1326]
theorem batch_26_14_ok : batch_26_14_values.all id = true := by decide

def batch_26_15_values : List Bool := [accepted_1327]
theorem batch_26_15_ok : batch_26_15_values.all id = true := by decide

def batch_26_16_values : List Bool := [accepted_1328]
theorem batch_26_16_ok : batch_26_16_values.all id = true := by decide

def batch_26_17_values : List Bool := [accepted_1330]
theorem batch_26_17_ok : batch_26_17_values.all id = true := by decide

def batch_26_18_values : List Bool := [accepted_1332]
theorem batch_26_18_ok : batch_26_18_values.all id = true := by decide

def batch_26_19_values : List Bool := [accepted_1333]
theorem batch_26_19_ok : batch_26_19_values.all id = true := by decide

def batch_26_20_values : List Bool := [accepted_1334]
theorem batch_26_20_ok : batch_26_20_values.all id = true := by decide

def batch_26_21_values : List Bool := [accepted_1338]
theorem batch_26_21_ok : batch_26_21_values.all id = true := by decide

def batch_26_22_values : List Bool := [accepted_1339]
theorem batch_26_22_ok : batch_26_22_values.all id = true := by decide

def batch_26_23_values : List Bool := [accepted_1341]
theorem batch_26_23_ok : batch_26_23_values.all id = true := by decide

def batch_26_24_values : List Bool := [accepted_1342]
theorem batch_26_24_ok : batch_26_24_values.all id = true := by decide

def batch_26_25_values : List Bool := [accepted_1348]
theorem batch_26_25_ok : batch_26_25_values.all id = true := by decide

theorem leaf_1300_ok : checkAt 527 1000 box_1300 cert_1300 = true := by
  have h := List.all_eq_true.mp batch_26_00_ok accepted_1300 (by simp [batch_26_00_values])
  exact h
theorem leaf_1300_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1300.profileLo box_1300.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1300_ok
theorem branch_box_1300_nonnegative : ∀ j, 0 ≤ branch_box_1300.lower j ∧ 0 ≤ branch_box_1300.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1300, Box.profileLo, Box.profileHi, box_1300]
theorem leaf_1300_BranchSafe : CertificateConsequences.BranchSafe branch_box_1300 := by
  left; refine ⟨branch_box_1300_nonnegative, ?_⟩
  intro z hz; exact leaf_1300_sound hz

theorem leaf_1301_ok : checkAt 527 1000 box_1301 cert_1301 = true := by
  have h := List.all_eq_true.mp batch_26_01_ok accepted_1301 (by simp [batch_26_01_values])
  exact h
theorem leaf_1301_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1301.profileLo box_1301.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1301_ok
theorem branch_box_1301_nonnegative : ∀ j, 0 ≤ branch_box_1301.lower j ∧ 0 ≤ branch_box_1301.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1301, Box.profileLo, Box.profileHi, box_1301]
theorem leaf_1301_BranchSafe : CertificateConsequences.BranchSafe branch_box_1301 := by
  left; refine ⟨branch_box_1301_nonnegative, ?_⟩
  intro z hz; exact leaf_1301_sound hz

theorem leaf_1303_ok : checkAt 527 1000 box_1303 cert_1303 = true := by
  have h := List.all_eq_true.mp batch_26_02_ok accepted_1303 (by simp [batch_26_02_values])
  exact h
theorem leaf_1303_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1303.profileLo box_1303.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1303_ok
theorem branch_box_1303_nonnegative : ∀ j, 0 ≤ branch_box_1303.lower j ∧ 0 ≤ branch_box_1303.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1303, Box.profileLo, Box.profileHi, box_1303]
theorem leaf_1303_BranchSafe : CertificateConsequences.BranchSafe branch_box_1303 := by
  left; refine ⟨branch_box_1303_nonnegative, ?_⟩
  intro z hz; exact leaf_1303_sound hz

theorem leaf_1304_ok : checkAt 527 1000 box_1304 cert_1304 = true := by
  have h := List.all_eq_true.mp batch_26_03_ok accepted_1304 (by simp [batch_26_03_values])
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
  have h := List.all_eq_true.mp batch_26_04_ok accepted_1306 (by simp [batch_26_04_values])
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

theorem leaf_1307_ok : checkAt 527 1000 box_1307 cert_1307 = true := by
  have h := List.all_eq_true.mp batch_26_05_ok accepted_1307 (by simp [batch_26_05_values])
  exact h
theorem leaf_1307_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1307.profileLo box_1307.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1307_ok
theorem branch_box_1307_nonnegative : ∀ j, 0 ≤ branch_box_1307.lower j ∧ 0 ≤ branch_box_1307.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1307, Box.profileLo, Box.profileHi, box_1307]
theorem leaf_1307_BranchSafe : CertificateConsequences.BranchSafe branch_box_1307 := by
  left; refine ⟨branch_box_1307_nonnegative, ?_⟩
  intro z hz; exact leaf_1307_sound hz

theorem leaf_1308_ok : checkAt 527 1000 box_1308 cert_1308 = true := by
  have h := List.all_eq_true.mp batch_26_06_ok accepted_1308 (by simp [batch_26_06_values])
  exact h
theorem leaf_1308_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1308.profileLo box_1308.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1308_ok
theorem branch_box_1308_nonnegative : ∀ j, 0 ≤ branch_box_1308.lower j ∧ 0 ≤ branch_box_1308.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1308, Box.profileLo, Box.profileHi, box_1308]
theorem leaf_1308_BranchSafe : CertificateConsequences.BranchSafe branch_box_1308 := by
  left; refine ⟨branch_box_1308_nonnegative, ?_⟩
  intro z hz; exact leaf_1308_sound hz

theorem leaf_1315_ok : checkAt 527 1000 box_1315 cert_1315 = true := by
  have h := List.all_eq_true.mp batch_26_07_ok accepted_1315 (by simp [batch_26_07_values])
  exact h
theorem leaf_1315_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1315.profileLo box_1315.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1315_ok
theorem branch_box_1315_nonnegative : ∀ j, 0 ≤ branch_box_1315.lower j ∧ 0 ≤ branch_box_1315.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1315, Box.profileLo, Box.profileHi, box_1315]
theorem leaf_1315_BranchSafe : CertificateConsequences.BranchSafe branch_box_1315 := by
  left; refine ⟨branch_box_1315_nonnegative, ?_⟩
  intro z hz; exact leaf_1315_sound hz

theorem leaf_1316_ok : checkAt 527 1000 box_1316 cert_1316 = true := by
  have h := List.all_eq_true.mp batch_26_08_ok accepted_1316 (by simp [batch_26_08_values])
  exact h
theorem leaf_1316_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1316.profileLo box_1316.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1316_ok
theorem branch_box_1316_nonnegative : ∀ j, 0 ≤ branch_box_1316.lower j ∧ 0 ≤ branch_box_1316.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1316, Box.profileLo, Box.profileHi, box_1316]
theorem leaf_1316_BranchSafe : CertificateConsequences.BranchSafe branch_box_1316 := by
  left; refine ⟨branch_box_1316_nonnegative, ?_⟩
  intro z hz; exact leaf_1316_sound hz

theorem leaf_1319_ok : checkAt 527 1000 box_1319 cert_1319 = true := by
  have h := List.all_eq_true.mp batch_26_09_ok accepted_1319 (by simp [batch_26_09_values])
  exact h
theorem leaf_1319_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1319.profileLo box_1319.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1319_ok
theorem branch_box_1319_nonnegative : ∀ j, 0 ≤ branch_box_1319.lower j ∧ 0 ≤ branch_box_1319.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1319, Box.profileLo, Box.profileHi, box_1319]
theorem leaf_1319_BranchSafe : CertificateConsequences.BranchSafe branch_box_1319 := by
  left; refine ⟨branch_box_1319_nonnegative, ?_⟩
  intro z hz; exact leaf_1319_sound hz

theorem leaf_1320_ok : checkAt 527 1000 box_1320 cert_1320 = true := by
  have h := List.all_eq_true.mp batch_26_10_ok accepted_1320 (by simp [batch_26_10_values])
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

theorem leaf_1321_ok : checkAt 527 1000 box_1321 cert_1321 = true := by
  have h := List.all_eq_true.mp batch_26_11_ok accepted_1321 (by simp [batch_26_11_values])
  exact h
theorem leaf_1321_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1321.profileLo box_1321.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1321_ok
theorem branch_box_1321_nonnegative : ∀ j, 0 ≤ branch_box_1321.lower j ∧ 0 ≤ branch_box_1321.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1321, Box.profileLo, Box.profileHi, box_1321]
theorem leaf_1321_BranchSafe : CertificateConsequences.BranchSafe branch_box_1321 := by
  left; refine ⟨branch_box_1321_nonnegative, ?_⟩
  intro z hz; exact leaf_1321_sound hz

theorem leaf_1322_ok : checkAt 527 1000 box_1322 cert_1322 = true := by
  have h := List.all_eq_true.mp batch_26_12_ok accepted_1322 (by simp [batch_26_12_values])
  exact h
theorem leaf_1322_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1322.profileLo box_1322.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1322_ok
theorem branch_box_1322_nonnegative : ∀ j, 0 ≤ branch_box_1322.lower j ∧ 0 ≤ branch_box_1322.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1322, Box.profileLo, Box.profileHi, box_1322]
theorem leaf_1322_BranchSafe : CertificateConsequences.BranchSafe branch_box_1322 := by
  left; refine ⟨branch_box_1322_nonnegative, ?_⟩
  intro z hz; exact leaf_1322_sound hz

theorem leaf_1323_ok : checkAt 527 1000 box_1323 cert_1323 = true := by
  have h := List.all_eq_true.mp batch_26_13_ok accepted_1323 (by simp [batch_26_13_values])
  exact h
theorem leaf_1323_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1323.profileLo box_1323.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1323_ok
theorem branch_box_1323_nonnegative : ∀ j, 0 ≤ branch_box_1323.lower j ∧ 0 ≤ branch_box_1323.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1323, Box.profileLo, Box.profileHi, box_1323]
theorem leaf_1323_BranchSafe : CertificateConsequences.BranchSafe branch_box_1323 := by
  left; refine ⟨branch_box_1323_nonnegative, ?_⟩
  intro z hz; exact leaf_1323_sound hz

theorem leaf_1326_ok : checkAt 527 1000 box_1326 cert_1326 = true := by
  have h := List.all_eq_true.mp batch_26_14_ok accepted_1326 (by simp [batch_26_14_values])
  exact h
theorem leaf_1326_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1326.profileLo box_1326.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1326_ok
theorem branch_box_1326_nonnegative : ∀ j, 0 ≤ branch_box_1326.lower j ∧ 0 ≤ branch_box_1326.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1326, Box.profileLo, Box.profileHi, box_1326]
theorem leaf_1326_BranchSafe : CertificateConsequences.BranchSafe branch_box_1326 := by
  left; refine ⟨branch_box_1326_nonnegative, ?_⟩
  intro z hz; exact leaf_1326_sound hz

theorem leaf_1327_ok : checkAt 527 1000 box_1327 cert_1327 = true := by
  have h := List.all_eq_true.mp batch_26_15_ok accepted_1327 (by simp [batch_26_15_values])
  exact h
theorem leaf_1327_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1327.profileLo box_1327.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1327_ok
theorem branch_box_1327_nonnegative : ∀ j, 0 ≤ branch_box_1327.lower j ∧ 0 ≤ branch_box_1327.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1327, Box.profileLo, Box.profileHi, box_1327]
theorem leaf_1327_BranchSafe : CertificateConsequences.BranchSafe branch_box_1327 := by
  left; refine ⟨branch_box_1327_nonnegative, ?_⟩
  intro z hz; exact leaf_1327_sound hz

theorem leaf_1328_ok : checkAt 527 1000 box_1328 cert_1328 = true := by
  have h := List.all_eq_true.mp batch_26_16_ok accepted_1328 (by simp [batch_26_16_values])
  exact h
theorem leaf_1328_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1328.profileLo box_1328.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1328_ok
theorem branch_box_1328_nonnegative : ∀ j, 0 ≤ branch_box_1328.lower j ∧ 0 ≤ branch_box_1328.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1328, Box.profileLo, Box.profileHi, box_1328]
theorem leaf_1328_BranchSafe : CertificateConsequences.BranchSafe branch_box_1328 := by
  left; refine ⟨branch_box_1328_nonnegative, ?_⟩
  intro z hz; exact leaf_1328_sound hz

theorem leaf_1330_ok : checkAt 527 1000 box_1330 cert_1330 = true := by
  have h := List.all_eq_true.mp batch_26_17_ok accepted_1330 (by simp [batch_26_17_values])
  exact h
theorem leaf_1330_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1330.profileLo box_1330.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1330_ok
theorem branch_box_1330_nonnegative : ∀ j, 0 ≤ branch_box_1330.lower j ∧ 0 ≤ branch_box_1330.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1330, Box.profileLo, Box.profileHi, box_1330]
theorem leaf_1330_BranchSafe : CertificateConsequences.BranchSafe branch_box_1330 := by
  left; refine ⟨branch_box_1330_nonnegative, ?_⟩
  intro z hz; exact leaf_1330_sound hz

theorem leaf_1332_ok : checkAt 527 1000 box_1332 cert_1332 = true := by
  have h := List.all_eq_true.mp batch_26_18_ok accepted_1332 (by simp [batch_26_18_values])
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

theorem leaf_1333_ok : checkAt 527 1000 box_1333 cert_1333 = true := by
  have h := List.all_eq_true.mp batch_26_19_ok accepted_1333 (by simp [batch_26_19_values])
  exact h
theorem leaf_1333_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1333.profileLo box_1333.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1333_ok
theorem branch_box_1333_nonnegative : ∀ j, 0 ≤ branch_box_1333.lower j ∧ 0 ≤ branch_box_1333.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1333, Box.profileLo, Box.profileHi, box_1333]
theorem leaf_1333_BranchSafe : CertificateConsequences.BranchSafe branch_box_1333 := by
  left; refine ⟨branch_box_1333_nonnegative, ?_⟩
  intro z hz; exact leaf_1333_sound hz

theorem leaf_1334_ok : checkAt 527 1000 box_1334 cert_1334 = true := by
  have h := List.all_eq_true.mp batch_26_20_ok accepted_1334 (by simp [batch_26_20_values])
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
  have h := List.all_eq_true.mp batch_26_21_ok accepted_1338 (by simp [batch_26_21_values])
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

theorem leaf_1339_ok : checkAt 527 1000 box_1339 cert_1339 = true := by
  have h := List.all_eq_true.mp batch_26_22_ok accepted_1339 (by simp [batch_26_22_values])
  exact h
theorem leaf_1339_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1339.profileLo box_1339.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1339_ok
theorem branch_box_1339_nonnegative : ∀ j, 0 ≤ branch_box_1339.lower j ∧ 0 ≤ branch_box_1339.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1339, Box.profileLo, Box.profileHi, box_1339]
theorem leaf_1339_BranchSafe : CertificateConsequences.BranchSafe branch_box_1339 := by
  left; refine ⟨branch_box_1339_nonnegative, ?_⟩
  intro z hz; exact leaf_1339_sound hz

theorem leaf_1341_ok : checkAt 527 1000 box_1341 cert_1341 = true := by
  have h := List.all_eq_true.mp batch_26_23_ok accepted_1341 (by simp [batch_26_23_values])
  exact h
theorem leaf_1341_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1341.profileLo box_1341.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1341_ok
theorem branch_box_1341_nonnegative : ∀ j, 0 ≤ branch_box_1341.lower j ∧ 0 ≤ branch_box_1341.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1341, Box.profileLo, Box.profileHi, box_1341]
theorem leaf_1341_BranchSafe : CertificateConsequences.BranchSafe branch_box_1341 := by
  left; refine ⟨branch_box_1341_nonnegative, ?_⟩
  intro z hz; exact leaf_1341_sound hz

theorem leaf_1342_ok : checkAt 527 1000 box_1342 cert_1342 = true := by
  have h := List.all_eq_true.mp batch_26_24_ok accepted_1342 (by simp [batch_26_24_values])
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

theorem leaf_1348_ok : checkAt 527 1000 box_1348 cert_1348 = true := by
  have h := List.all_eq_true.mp batch_26_25_ok accepted_1348 (by simp [batch_26_25_values])
  exact h
theorem leaf_1348_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1348.profileLo box_1348.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1348_ok
theorem branch_box_1348_nonnegative : ∀ j, 0 ≤ branch_box_1348.lower j ∧ 0 ≤ branch_box_1348.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1348, Box.profileLo, Box.profileHi, box_1348]
theorem leaf_1348_BranchSafe : CertificateConsequences.BranchSafe branch_box_1348 := by
  left; refine ⟨branch_box_1348_nonnegative, ?_⟩
  intro z hz; exact leaf_1348_sound hz

#print axioms batch_26_00_ok
#print axioms leaf_1300_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
