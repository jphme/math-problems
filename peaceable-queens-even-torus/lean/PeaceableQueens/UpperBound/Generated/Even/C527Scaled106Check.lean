import PeaceableQueens.UpperBound.Generated.Even.C527Scaled106Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_106_00_values : List Bool := [accepted_5300]
theorem batch_106_00_ok : batch_106_00_values.all id = true := by decide

def batch_106_01_values : List Bool := [accepted_5301]
theorem batch_106_01_ok : batch_106_01_values.all id = true := by decide

def batch_106_02_values : List Bool := [accepted_5303]
theorem batch_106_02_ok : batch_106_02_values.all id = true := by decide

def batch_106_03_values : List Bool := [accepted_5304]
theorem batch_106_03_ok : batch_106_03_values.all id = true := by decide

def batch_106_04_values : List Bool := [accepted_5305]
theorem batch_106_04_ok : batch_106_04_values.all id = true := by decide

def batch_106_05_values : List Bool := [accepted_5307]
theorem batch_106_05_ok : batch_106_05_values.all id = true := by decide

def batch_106_06_values : List Bool := [accepted_5308]
theorem batch_106_06_ok : batch_106_06_values.all id = true := by decide

def batch_106_07_values : List Bool := [accepted_5311]
theorem batch_106_07_ok : batch_106_07_values.all id = true := by decide

def batch_106_08_values : List Bool := [accepted_5313]
theorem batch_106_08_ok : batch_106_08_values.all id = true := by decide

def batch_106_09_values : List Bool := [accepted_5314]
theorem batch_106_09_ok : batch_106_09_values.all id = true := by decide

def batch_106_10_values : List Bool := [accepted_5318]
theorem batch_106_10_ok : batch_106_10_values.all id = true := by decide

def batch_106_11_values : List Bool := [accepted_5319]
theorem batch_106_11_ok : batch_106_11_values.all id = true := by decide

def batch_106_12_values : List Bool := [accepted_5320]
theorem batch_106_12_ok : batch_106_12_values.all id = true := by decide

def batch_106_13_values : List Bool := [accepted_5323]
theorem batch_106_13_ok : batch_106_13_values.all id = true := by decide

def batch_106_14_values : List Bool := [accepted_5324]
theorem batch_106_14_ok : batch_106_14_values.all id = true := by decide

def batch_106_15_values : List Bool := [accepted_5325]
theorem batch_106_15_ok : batch_106_15_values.all id = true := by decide

def batch_106_16_values : List Bool := [accepted_5326]
theorem batch_106_16_ok : batch_106_16_values.all id = true := by decide

def batch_106_17_values : List Bool := [accepted_5330]
theorem batch_106_17_ok : batch_106_17_values.all id = true := by decide

def batch_106_18_values : List Bool := [accepted_5331]
theorem batch_106_18_ok : batch_106_18_values.all id = true := by decide

def batch_106_19_values : List Bool := [accepted_5333]
theorem batch_106_19_ok : batch_106_19_values.all id = true := by decide

def batch_106_20_values : List Bool := [accepted_5334]
theorem batch_106_20_ok : batch_106_20_values.all id = true := by decide

def batch_106_21_values : List Bool := [accepted_5337]
theorem batch_106_21_ok : batch_106_21_values.all id = true := by decide

def batch_106_22_values : List Bool := [accepted_5340]
theorem batch_106_22_ok : batch_106_22_values.all id = true := by decide

def batch_106_23_values : List Bool := [accepted_5342]
theorem batch_106_23_ok : batch_106_23_values.all id = true := by decide

def batch_106_24_values : List Bool := [accepted_5343]
theorem batch_106_24_ok : batch_106_24_values.all id = true := by decide

def batch_106_25_values : List Bool := [accepted_5344]
theorem batch_106_25_ok : batch_106_25_values.all id = true := by decide

def batch_106_26_values : List Bool := [accepted_5347]
theorem batch_106_26_ok : batch_106_26_values.all id = true := by decide

def batch_106_27_values : List Bool := [accepted_5348]
theorem batch_106_27_ok : batch_106_27_values.all id = true := by decide

theorem leaf_5300_ok : checkAt 527 1000 box_5300 cert_5300 = true := by
  have h := List.all_eq_true.mp batch_106_00_ok accepted_5300 (by simp [batch_106_00_values])
  exact h
theorem leaf_5300_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5300.profileLo box_5300.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5300_ok
theorem branch_box_5300_nonnegative : ∀ j, 0 ≤ branch_box_5300.lower j ∧ 0 ≤ branch_box_5300.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5300, Box.profileLo, Box.profileHi, box_5300]
theorem leaf_5300_BranchSafe : CertificateConsequences.BranchSafe branch_box_5300 := by
  left; refine ⟨branch_box_5300_nonnegative, ?_⟩
  intro z hz; exact leaf_5300_sound hz

theorem leaf_5301_ok : checkAt 527 1000 box_5301 cert_5301 = true := by
  have h := List.all_eq_true.mp batch_106_01_ok accepted_5301 (by simp [batch_106_01_values])
  exact h
theorem leaf_5301_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5301.profileLo box_5301.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5301_ok
theorem branch_box_5301_nonnegative : ∀ j, 0 ≤ branch_box_5301.lower j ∧ 0 ≤ branch_box_5301.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5301, Box.profileLo, Box.profileHi, box_5301]
theorem leaf_5301_BranchSafe : CertificateConsequences.BranchSafe branch_box_5301 := by
  left; refine ⟨branch_box_5301_nonnegative, ?_⟩
  intro z hz; exact leaf_5301_sound hz

theorem leaf_5303_ok : checkAt 527 1000 box_5303 cert_5303 = true := by
  have h := List.all_eq_true.mp batch_106_02_ok accepted_5303 (by simp [batch_106_02_values])
  exact h
theorem leaf_5303_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5303.profileLo box_5303.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5303_ok
theorem branch_box_5303_nonnegative : ∀ j, 0 ≤ branch_box_5303.lower j ∧ 0 ≤ branch_box_5303.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5303, Box.profileLo, Box.profileHi, box_5303]
theorem leaf_5303_BranchSafe : CertificateConsequences.BranchSafe branch_box_5303 := by
  left; refine ⟨branch_box_5303_nonnegative, ?_⟩
  intro z hz; exact leaf_5303_sound hz

theorem leaf_5304_ok : checkAt 527 1000 box_5304 cert_5304 = true := by
  have h := List.all_eq_true.mp batch_106_03_ok accepted_5304 (by simp [batch_106_03_values])
  exact h
theorem leaf_5304_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5304.profileLo box_5304.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5304_ok
theorem branch_box_5304_nonnegative : ∀ j, 0 ≤ branch_box_5304.lower j ∧ 0 ≤ branch_box_5304.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5304, Box.profileLo, Box.profileHi, box_5304]
theorem leaf_5304_BranchSafe : CertificateConsequences.BranchSafe branch_box_5304 := by
  left; refine ⟨branch_box_5304_nonnegative, ?_⟩
  intro z hz; exact leaf_5304_sound hz

theorem leaf_5305_ok : checkAt 527 1000 box_5305 cert_5305 = true := by
  have h := List.all_eq_true.mp batch_106_04_ok accepted_5305 (by simp [batch_106_04_values])
  exact h
theorem leaf_5305_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5305.profileLo box_5305.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5305_ok
theorem branch_box_5305_nonnegative : ∀ j, 0 ≤ branch_box_5305.lower j ∧ 0 ≤ branch_box_5305.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5305, Box.profileLo, Box.profileHi, box_5305]
theorem leaf_5305_BranchSafe : CertificateConsequences.BranchSafe branch_box_5305 := by
  left; refine ⟨branch_box_5305_nonnegative, ?_⟩
  intro z hz; exact leaf_5305_sound hz

theorem leaf_5307_ok : checkAt 527 1000 box_5307 cert_5307 = true := by
  have h := List.all_eq_true.mp batch_106_05_ok accepted_5307 (by simp [batch_106_05_values])
  exact h
theorem leaf_5307_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5307.profileLo box_5307.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5307_ok
theorem branch_box_5307_nonnegative : ∀ j, 0 ≤ branch_box_5307.lower j ∧ 0 ≤ branch_box_5307.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5307, Box.profileLo, Box.profileHi, box_5307]
theorem leaf_5307_BranchSafe : CertificateConsequences.BranchSafe branch_box_5307 := by
  left; refine ⟨branch_box_5307_nonnegative, ?_⟩
  intro z hz; exact leaf_5307_sound hz

theorem leaf_5308_ok : checkAt 527 1000 box_5308 cert_5308 = true := by
  have h := List.all_eq_true.mp batch_106_06_ok accepted_5308 (by simp [batch_106_06_values])
  exact h
theorem leaf_5308_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5308.profileLo box_5308.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5308_ok
theorem branch_box_5308_nonnegative : ∀ j, 0 ≤ branch_box_5308.lower j ∧ 0 ≤ branch_box_5308.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5308, Box.profileLo, Box.profileHi, box_5308]
theorem leaf_5308_BranchSafe : CertificateConsequences.BranchSafe branch_box_5308 := by
  left; refine ⟨branch_box_5308_nonnegative, ?_⟩
  intro z hz; exact leaf_5308_sound hz

theorem leaf_5311_ok : checkAt 527 1000 box_5311 cert_5311 = true := by
  have h := List.all_eq_true.mp batch_106_07_ok accepted_5311 (by simp [batch_106_07_values])
  exact h
theorem leaf_5311_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5311.profileLo box_5311.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5311_ok
theorem branch_box_5311_nonnegative : ∀ j, 0 ≤ branch_box_5311.lower j ∧ 0 ≤ branch_box_5311.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5311, Box.profileLo, Box.profileHi, box_5311]
theorem leaf_5311_BranchSafe : CertificateConsequences.BranchSafe branch_box_5311 := by
  left; refine ⟨branch_box_5311_nonnegative, ?_⟩
  intro z hz; exact leaf_5311_sound hz

theorem leaf_5313_ok : checkAt 527 1000 box_5313 cert_5313 = true := by
  have h := List.all_eq_true.mp batch_106_08_ok accepted_5313 (by simp [batch_106_08_values])
  exact h
theorem leaf_5313_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5313.profileLo box_5313.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5313_ok
theorem branch_box_5313_nonnegative : ∀ j, 0 ≤ branch_box_5313.lower j ∧ 0 ≤ branch_box_5313.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5313, Box.profileLo, Box.profileHi, box_5313]
theorem leaf_5313_BranchSafe : CertificateConsequences.BranchSafe branch_box_5313 := by
  left; refine ⟨branch_box_5313_nonnegative, ?_⟩
  intro z hz; exact leaf_5313_sound hz

theorem leaf_5314_ok : checkAt 527 1000 box_5314 cert_5314 = true := by
  have h := List.all_eq_true.mp batch_106_09_ok accepted_5314 (by simp [batch_106_09_values])
  exact h
theorem leaf_5314_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5314.profileLo box_5314.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5314_ok
theorem branch_box_5314_nonnegative : ∀ j, 0 ≤ branch_box_5314.lower j ∧ 0 ≤ branch_box_5314.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5314, Box.profileLo, Box.profileHi, box_5314]
theorem leaf_5314_BranchSafe : CertificateConsequences.BranchSafe branch_box_5314 := by
  left; refine ⟨branch_box_5314_nonnegative, ?_⟩
  intro z hz; exact leaf_5314_sound hz

theorem leaf_5318_ok : checkAt 527 1000 box_5318 cert_5318 = true := by
  have h := List.all_eq_true.mp batch_106_10_ok accepted_5318 (by simp [batch_106_10_values])
  exact h
theorem leaf_5318_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5318.profileLo box_5318.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5318_ok
theorem branch_box_5318_nonnegative : ∀ j, 0 ≤ branch_box_5318.lower j ∧ 0 ≤ branch_box_5318.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5318, Box.profileLo, Box.profileHi, box_5318]
theorem leaf_5318_BranchSafe : CertificateConsequences.BranchSafe branch_box_5318 := by
  left; refine ⟨branch_box_5318_nonnegative, ?_⟩
  intro z hz; exact leaf_5318_sound hz

theorem leaf_5319_ok : checkAt 527 1000 box_5319 cert_5319 = true := by
  have h := List.all_eq_true.mp batch_106_11_ok accepted_5319 (by simp [batch_106_11_values])
  exact h
theorem leaf_5319_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5319.profileLo box_5319.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5319_ok
theorem branch_box_5319_nonnegative : ∀ j, 0 ≤ branch_box_5319.lower j ∧ 0 ≤ branch_box_5319.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5319, Box.profileLo, Box.profileHi, box_5319]
theorem leaf_5319_BranchSafe : CertificateConsequences.BranchSafe branch_box_5319 := by
  left; refine ⟨branch_box_5319_nonnegative, ?_⟩
  intro z hz; exact leaf_5319_sound hz

theorem leaf_5320_ok : checkAt 527 1000 box_5320 cert_5320 = true := by
  have h := List.all_eq_true.mp batch_106_12_ok accepted_5320 (by simp [batch_106_12_values])
  exact h
theorem leaf_5320_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5320.profileLo box_5320.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5320_ok
theorem branch_box_5320_nonnegative : ∀ j, 0 ≤ branch_box_5320.lower j ∧ 0 ≤ branch_box_5320.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5320, Box.profileLo, Box.profileHi, box_5320]
theorem leaf_5320_BranchSafe : CertificateConsequences.BranchSafe branch_box_5320 := by
  left; refine ⟨branch_box_5320_nonnegative, ?_⟩
  intro z hz; exact leaf_5320_sound hz

theorem leaf_5323_ok : checkAt 527 1000 box_5323 cert_5323 = true := by
  have h := List.all_eq_true.mp batch_106_13_ok accepted_5323 (by simp [batch_106_13_values])
  exact h
theorem leaf_5323_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5323.profileLo box_5323.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5323_ok
theorem branch_box_5323_nonnegative : ∀ j, 0 ≤ branch_box_5323.lower j ∧ 0 ≤ branch_box_5323.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5323, Box.profileLo, Box.profileHi, box_5323]
theorem leaf_5323_BranchSafe : CertificateConsequences.BranchSafe branch_box_5323 := by
  left; refine ⟨branch_box_5323_nonnegative, ?_⟩
  intro z hz; exact leaf_5323_sound hz

theorem leaf_5324_ok : checkAt 527 1000 box_5324 cert_5324 = true := by
  have h := List.all_eq_true.mp batch_106_14_ok accepted_5324 (by simp [batch_106_14_values])
  exact h
theorem leaf_5324_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5324.profileLo box_5324.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5324_ok
theorem branch_box_5324_nonnegative : ∀ j, 0 ≤ branch_box_5324.lower j ∧ 0 ≤ branch_box_5324.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5324, Box.profileLo, Box.profileHi, box_5324]
theorem leaf_5324_BranchSafe : CertificateConsequences.BranchSafe branch_box_5324 := by
  left; refine ⟨branch_box_5324_nonnegative, ?_⟩
  intro z hz; exact leaf_5324_sound hz

theorem leaf_5325_ok : checkAt 527 1000 box_5325 cert_5325 = true := by
  have h := List.all_eq_true.mp batch_106_15_ok accepted_5325 (by simp [batch_106_15_values])
  exact h
theorem leaf_5325_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5325.profileLo box_5325.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5325_ok
theorem branch_box_5325_nonnegative : ∀ j, 0 ≤ branch_box_5325.lower j ∧ 0 ≤ branch_box_5325.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5325, Box.profileLo, Box.profileHi, box_5325]
theorem leaf_5325_BranchSafe : CertificateConsequences.BranchSafe branch_box_5325 := by
  left; refine ⟨branch_box_5325_nonnegative, ?_⟩
  intro z hz; exact leaf_5325_sound hz

theorem leaf_5326_ok : checkAt 527 1000 box_5326 cert_5326 = true := by
  have h := List.all_eq_true.mp batch_106_16_ok accepted_5326 (by simp [batch_106_16_values])
  exact h
theorem leaf_5326_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5326.profileLo box_5326.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5326_ok
theorem branch_box_5326_nonnegative : ∀ j, 0 ≤ branch_box_5326.lower j ∧ 0 ≤ branch_box_5326.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5326, Box.profileLo, Box.profileHi, box_5326]
theorem leaf_5326_BranchSafe : CertificateConsequences.BranchSafe branch_box_5326 := by
  left; refine ⟨branch_box_5326_nonnegative, ?_⟩
  intro z hz; exact leaf_5326_sound hz

theorem leaf_5330_ok : checkAt 527 1000 box_5330 cert_5330 = true := by
  have h := List.all_eq_true.mp batch_106_17_ok accepted_5330 (by simp [batch_106_17_values])
  exact h
theorem leaf_5330_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5330.profileLo box_5330.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5330_ok
theorem branch_box_5330_nonnegative : ∀ j, 0 ≤ branch_box_5330.lower j ∧ 0 ≤ branch_box_5330.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5330, Box.profileLo, Box.profileHi, box_5330]
theorem leaf_5330_BranchSafe : CertificateConsequences.BranchSafe branch_box_5330 := by
  left; refine ⟨branch_box_5330_nonnegative, ?_⟩
  intro z hz; exact leaf_5330_sound hz

theorem leaf_5331_ok : checkAt 527 1000 box_5331 cert_5331 = true := by
  have h := List.all_eq_true.mp batch_106_18_ok accepted_5331 (by simp [batch_106_18_values])
  exact h
theorem leaf_5331_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5331.profileLo box_5331.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5331_ok
theorem branch_box_5331_nonnegative : ∀ j, 0 ≤ branch_box_5331.lower j ∧ 0 ≤ branch_box_5331.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5331, Box.profileLo, Box.profileHi, box_5331]
theorem leaf_5331_BranchSafe : CertificateConsequences.BranchSafe branch_box_5331 := by
  left; refine ⟨branch_box_5331_nonnegative, ?_⟩
  intro z hz; exact leaf_5331_sound hz

theorem leaf_5333_ok : checkAt 527 1000 box_5333 cert_5333 = true := by
  have h := List.all_eq_true.mp batch_106_19_ok accepted_5333 (by simp [batch_106_19_values])
  exact h
theorem leaf_5333_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5333.profileLo box_5333.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5333_ok
theorem branch_box_5333_nonnegative : ∀ j, 0 ≤ branch_box_5333.lower j ∧ 0 ≤ branch_box_5333.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5333, Box.profileLo, Box.profileHi, box_5333]
theorem leaf_5333_BranchSafe : CertificateConsequences.BranchSafe branch_box_5333 := by
  left; refine ⟨branch_box_5333_nonnegative, ?_⟩
  intro z hz; exact leaf_5333_sound hz

theorem leaf_5334_ok : checkAt 527 1000 box_5334 cert_5334 = true := by
  have h := List.all_eq_true.mp batch_106_20_ok accepted_5334 (by simp [batch_106_20_values])
  exact h
theorem leaf_5334_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5334.profileLo box_5334.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5334_ok
theorem branch_box_5334_nonnegative : ∀ j, 0 ≤ branch_box_5334.lower j ∧ 0 ≤ branch_box_5334.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5334, Box.profileLo, Box.profileHi, box_5334]
theorem leaf_5334_BranchSafe : CertificateConsequences.BranchSafe branch_box_5334 := by
  left; refine ⟨branch_box_5334_nonnegative, ?_⟩
  intro z hz; exact leaf_5334_sound hz

theorem leaf_5337_ok : checkAt 527 1000 box_5337 cert_5337 = true := by
  have h := List.all_eq_true.mp batch_106_21_ok accepted_5337 (by simp [batch_106_21_values])
  exact h
theorem leaf_5337_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5337.profileLo box_5337.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5337_ok
theorem branch_box_5337_nonnegative : ∀ j, 0 ≤ branch_box_5337.lower j ∧ 0 ≤ branch_box_5337.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5337, Box.profileLo, Box.profileHi, box_5337]
theorem leaf_5337_BranchSafe : CertificateConsequences.BranchSafe branch_box_5337 := by
  left; refine ⟨branch_box_5337_nonnegative, ?_⟩
  intro z hz; exact leaf_5337_sound hz

theorem leaf_5340_ok : checkAt 527 1000 box_5340 cert_5340 = true := by
  have h := List.all_eq_true.mp batch_106_22_ok accepted_5340 (by simp [batch_106_22_values])
  exact h
theorem leaf_5340_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5340.profileLo box_5340.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5340_ok
theorem branch_box_5340_nonnegative : ∀ j, 0 ≤ branch_box_5340.lower j ∧ 0 ≤ branch_box_5340.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5340, Box.profileLo, Box.profileHi, box_5340]
theorem leaf_5340_BranchSafe : CertificateConsequences.BranchSafe branch_box_5340 := by
  left; refine ⟨branch_box_5340_nonnegative, ?_⟩
  intro z hz; exact leaf_5340_sound hz

theorem leaf_5342_ok : checkAt 527 1000 box_5342 cert_5342 = true := by
  have h := List.all_eq_true.mp batch_106_23_ok accepted_5342 (by simp [batch_106_23_values])
  exact h
theorem leaf_5342_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5342.profileLo box_5342.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5342_ok
theorem branch_box_5342_nonnegative : ∀ j, 0 ≤ branch_box_5342.lower j ∧ 0 ≤ branch_box_5342.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5342, Box.profileLo, Box.profileHi, box_5342]
theorem leaf_5342_BranchSafe : CertificateConsequences.BranchSafe branch_box_5342 := by
  left; refine ⟨branch_box_5342_nonnegative, ?_⟩
  intro z hz; exact leaf_5342_sound hz

theorem leaf_5343_ok : checkAt 527 1000 box_5343 cert_5343 = true := by
  have h := List.all_eq_true.mp batch_106_24_ok accepted_5343 (by simp [batch_106_24_values])
  exact h
theorem leaf_5343_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5343.profileLo box_5343.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5343_ok
theorem branch_box_5343_nonnegative : ∀ j, 0 ≤ branch_box_5343.lower j ∧ 0 ≤ branch_box_5343.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5343, Box.profileLo, Box.profileHi, box_5343]
theorem leaf_5343_BranchSafe : CertificateConsequences.BranchSafe branch_box_5343 := by
  left; refine ⟨branch_box_5343_nonnegative, ?_⟩
  intro z hz; exact leaf_5343_sound hz

theorem leaf_5344_ok : checkAt 527 1000 box_5344 cert_5344 = true := by
  have h := List.all_eq_true.mp batch_106_25_ok accepted_5344 (by simp [batch_106_25_values])
  exact h
theorem leaf_5344_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5344.profileLo box_5344.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5344_ok
theorem branch_box_5344_nonnegative : ∀ j, 0 ≤ branch_box_5344.lower j ∧ 0 ≤ branch_box_5344.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5344, Box.profileLo, Box.profileHi, box_5344]
theorem leaf_5344_BranchSafe : CertificateConsequences.BranchSafe branch_box_5344 := by
  left; refine ⟨branch_box_5344_nonnegative, ?_⟩
  intro z hz; exact leaf_5344_sound hz

theorem leaf_5347_ok : checkAt 527 1000 box_5347 cert_5347 = true := by
  have h := List.all_eq_true.mp batch_106_26_ok accepted_5347 (by simp [batch_106_26_values])
  exact h
theorem leaf_5347_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5347.profileLo box_5347.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5347_ok
theorem branch_box_5347_nonnegative : ∀ j, 0 ≤ branch_box_5347.lower j ∧ 0 ≤ branch_box_5347.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5347, Box.profileLo, Box.profileHi, box_5347]
theorem leaf_5347_BranchSafe : CertificateConsequences.BranchSafe branch_box_5347 := by
  left; refine ⟨branch_box_5347_nonnegative, ?_⟩
  intro z hz; exact leaf_5347_sound hz

theorem leaf_5348_ok : checkAt 527 1000 box_5348 cert_5348 = true := by
  have h := List.all_eq_true.mp batch_106_27_ok accepted_5348 (by simp [batch_106_27_values])
  exact h
theorem leaf_5348_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5348.profileLo box_5348.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5348_ok
theorem branch_box_5348_nonnegative : ∀ j, 0 ≤ branch_box_5348.lower j ∧ 0 ≤ branch_box_5348.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5348, Box.profileLo, Box.profileHi, box_5348]
theorem leaf_5348_BranchSafe : CertificateConsequences.BranchSafe branch_box_5348 := by
  left; refine ⟨branch_box_5348_nonnegative, ?_⟩
  intro z hz; exact leaf_5348_sound hz

#print axioms batch_106_00_ok
#print axioms leaf_5300_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
