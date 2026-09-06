import PeaceableQueens.UpperBound.Generated.Even.C527Scaled06Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_06_00_values : List Bool := [accepted_300]
theorem batch_06_00_ok : batch_06_00_values.all id = true := by decide

def batch_06_01_values : List Bool := [accepted_301]
theorem batch_06_01_ok : batch_06_01_values.all id = true := by decide

def batch_06_02_values : List Bool := [accepted_302]
theorem batch_06_02_ok : batch_06_02_values.all id = true := by decide

def batch_06_03_values : List Bool := [accepted_305]
theorem batch_06_03_ok : batch_06_03_values.all id = true := by decide

def batch_06_04_values : List Bool := [accepted_306]
theorem batch_06_04_ok : batch_06_04_values.all id = true := by decide

def batch_06_05_values : List Bool := [accepted_307]
theorem batch_06_05_ok : batch_06_05_values.all id = true := by decide

def batch_06_06_values : List Bool := [accepted_309]
theorem batch_06_06_ok : batch_06_06_values.all id = true := by decide

def batch_06_07_values : List Bool := [accepted_311]
theorem batch_06_07_ok : batch_06_07_values.all id = true := by decide

def batch_06_08_values : List Bool := [accepted_314]
theorem batch_06_08_ok : batch_06_08_values.all id = true := by decide

def batch_06_09_values : List Bool := [accepted_315]
theorem batch_06_09_ok : batch_06_09_values.all id = true := by decide

def batch_06_10_values : List Bool := [accepted_316]
theorem batch_06_10_ok : batch_06_10_values.all id = true := by decide

def batch_06_11_values : List Bool := [accepted_327]
theorem batch_06_11_ok : batch_06_11_values.all id = true := by decide

def batch_06_12_values : List Bool := [accepted_328]
theorem batch_06_12_ok : batch_06_12_values.all id = true := by decide

def batch_06_13_values : List Bool := [accepted_329]
theorem batch_06_13_ok : batch_06_13_values.all id = true := by decide

def batch_06_14_values : List Bool := [accepted_333]
theorem batch_06_14_ok : batch_06_14_values.all id = true := by decide

def batch_06_15_values : List Bool := [accepted_334]
theorem batch_06_15_ok : batch_06_15_values.all id = true := by decide

def batch_06_16_values : List Bool := [accepted_335]
theorem batch_06_16_ok : batch_06_16_values.all id = true := by decide

def batch_06_17_values : List Bool := [accepted_336]
theorem batch_06_17_ok : batch_06_17_values.all id = true := by decide

def batch_06_18_values : List Bool := [accepted_342]
theorem batch_06_18_ok : batch_06_18_values.all id = true := by decide

def batch_06_19_values : List Bool := [accepted_343]
theorem batch_06_19_ok : batch_06_19_values.all id = true := by decide

def batch_06_20_values : List Bool := [accepted_345]
theorem batch_06_20_ok : batch_06_20_values.all id = true := by decide

def batch_06_21_values : List Bool := [accepted_346]
theorem batch_06_21_ok : batch_06_21_values.all id = true := by decide

def batch_06_22_values : List Bool := [accepted_347]
theorem batch_06_22_ok : batch_06_22_values.all id = true := by decide

def batch_06_23_values : List Bool := [accepted_349]
theorem batch_06_23_ok : batch_06_23_values.all id = true := by decide

theorem leaf_300_ok : checkAt 527 1000 box_300 cert_300 = true := by
  have h := List.all_eq_true.mp batch_06_00_ok accepted_300 (by simp [batch_06_00_values])
  exact h
theorem leaf_300_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_300.profileLo box_300.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_300_ok
theorem branch_box_300_nonnegative : ∀ j, 0 ≤ branch_box_300.lower j ∧ 0 ≤ branch_box_300.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_300, Box.profileLo, Box.profileHi, box_300]
theorem leaf_300_BranchSafe : CertificateConsequences.BranchSafe branch_box_300 := by
  left; refine ⟨branch_box_300_nonnegative, ?_⟩
  intro z hz; exact leaf_300_sound hz

theorem leaf_301_ok : checkAt 527 1000 box_301 cert_301 = true := by
  have h := List.all_eq_true.mp batch_06_01_ok accepted_301 (by simp [batch_06_01_values])
  exact h
theorem leaf_301_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_301.profileLo box_301.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_301_ok
theorem branch_box_301_nonnegative : ∀ j, 0 ≤ branch_box_301.lower j ∧ 0 ≤ branch_box_301.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_301, Box.profileLo, Box.profileHi, box_301]
theorem leaf_301_BranchSafe : CertificateConsequences.BranchSafe branch_box_301 := by
  left; refine ⟨branch_box_301_nonnegative, ?_⟩
  intro z hz; exact leaf_301_sound hz

theorem leaf_302_ok : checkAt 527 1000 box_302 cert_302 = true := by
  have h := List.all_eq_true.mp batch_06_02_ok accepted_302 (by simp [batch_06_02_values])
  exact h
theorem leaf_302_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_302.profileLo box_302.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_302_ok
theorem branch_box_302_nonnegative : ∀ j, 0 ≤ branch_box_302.lower j ∧ 0 ≤ branch_box_302.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_302, Box.profileLo, Box.profileHi, box_302]
theorem leaf_302_BranchSafe : CertificateConsequences.BranchSafe branch_box_302 := by
  left; refine ⟨branch_box_302_nonnegative, ?_⟩
  intro z hz; exact leaf_302_sound hz

theorem leaf_305_ok : checkAt 527 1000 box_305 cert_305 = true := by
  have h := List.all_eq_true.mp batch_06_03_ok accepted_305 (by simp [batch_06_03_values])
  exact h
theorem leaf_305_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_305.profileLo box_305.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_305_ok
theorem branch_box_305_nonnegative : ∀ j, 0 ≤ branch_box_305.lower j ∧ 0 ≤ branch_box_305.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_305, Box.profileLo, Box.profileHi, box_305]
theorem leaf_305_BranchSafe : CertificateConsequences.BranchSafe branch_box_305 := by
  left; refine ⟨branch_box_305_nonnegative, ?_⟩
  intro z hz; exact leaf_305_sound hz

theorem leaf_306_ok : checkAt 527 1000 box_306 cert_306 = true := by
  have h := List.all_eq_true.mp batch_06_04_ok accepted_306 (by simp [batch_06_04_values])
  exact h
theorem leaf_306_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_306.profileLo box_306.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_306_ok
theorem branch_box_306_nonnegative : ∀ j, 0 ≤ branch_box_306.lower j ∧ 0 ≤ branch_box_306.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_306, Box.profileLo, Box.profileHi, box_306]
theorem leaf_306_BranchSafe : CertificateConsequences.BranchSafe branch_box_306 := by
  left; refine ⟨branch_box_306_nonnegative, ?_⟩
  intro z hz; exact leaf_306_sound hz

theorem leaf_307_ok : checkAt 527 1000 box_307 cert_307 = true := by
  have h := List.all_eq_true.mp batch_06_05_ok accepted_307 (by simp [batch_06_05_values])
  exact h
theorem leaf_307_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_307.profileLo box_307.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_307_ok
theorem branch_box_307_nonnegative : ∀ j, 0 ≤ branch_box_307.lower j ∧ 0 ≤ branch_box_307.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_307, Box.profileLo, Box.profileHi, box_307]
theorem leaf_307_BranchSafe : CertificateConsequences.BranchSafe branch_box_307 := by
  left; refine ⟨branch_box_307_nonnegative, ?_⟩
  intro z hz; exact leaf_307_sound hz

theorem leaf_309_ok : checkAt 527 1000 box_309 cert_309 = true := by
  have h := List.all_eq_true.mp batch_06_06_ok accepted_309 (by simp [batch_06_06_values])
  exact h
theorem leaf_309_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_309.profileLo box_309.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_309_ok
theorem branch_box_309_nonnegative : ∀ j, 0 ≤ branch_box_309.lower j ∧ 0 ≤ branch_box_309.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_309, Box.profileLo, Box.profileHi, box_309]
theorem leaf_309_BranchSafe : CertificateConsequences.BranchSafe branch_box_309 := by
  left; refine ⟨branch_box_309_nonnegative, ?_⟩
  intro z hz; exact leaf_309_sound hz

theorem leaf_311_ok : checkAt 527 1000 box_311 cert_311 = true := by
  have h := List.all_eq_true.mp batch_06_07_ok accepted_311 (by simp [batch_06_07_values])
  exact h
theorem leaf_311_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_311.profileLo box_311.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_311_ok
theorem branch_box_311_nonnegative : ∀ j, 0 ≤ branch_box_311.lower j ∧ 0 ≤ branch_box_311.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_311, Box.profileLo, Box.profileHi, box_311]
theorem leaf_311_BranchSafe : CertificateConsequences.BranchSafe branch_box_311 := by
  left; refine ⟨branch_box_311_nonnegative, ?_⟩
  intro z hz; exact leaf_311_sound hz

theorem leaf_314_ok : checkAt 527 1000 box_314 cert_314 = true := by
  have h := List.all_eq_true.mp batch_06_08_ok accepted_314 (by simp [batch_06_08_values])
  exact h
theorem leaf_314_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_314.profileLo box_314.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_314_ok
theorem branch_box_314_nonnegative : ∀ j, 0 ≤ branch_box_314.lower j ∧ 0 ≤ branch_box_314.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_314, Box.profileLo, Box.profileHi, box_314]
theorem leaf_314_BranchSafe : CertificateConsequences.BranchSafe branch_box_314 := by
  left; refine ⟨branch_box_314_nonnegative, ?_⟩
  intro z hz; exact leaf_314_sound hz

theorem leaf_315_ok : checkAt 527 1000 box_315 cert_315 = true := by
  have h := List.all_eq_true.mp batch_06_09_ok accepted_315 (by simp [batch_06_09_values])
  exact h
theorem leaf_315_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_315.profileLo box_315.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_315_ok
theorem branch_box_315_nonnegative : ∀ j, 0 ≤ branch_box_315.lower j ∧ 0 ≤ branch_box_315.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_315, Box.profileLo, Box.profileHi, box_315]
theorem leaf_315_BranchSafe : CertificateConsequences.BranchSafe branch_box_315 := by
  left; refine ⟨branch_box_315_nonnegative, ?_⟩
  intro z hz; exact leaf_315_sound hz

theorem leaf_316_ok : checkAt 527 1000 box_316 cert_316 = true := by
  have h := List.all_eq_true.mp batch_06_10_ok accepted_316 (by simp [batch_06_10_values])
  exact h
theorem leaf_316_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_316.profileLo box_316.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_316_ok
theorem branch_box_316_nonnegative : ∀ j, 0 ≤ branch_box_316.lower j ∧ 0 ≤ branch_box_316.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_316, Box.profileLo, Box.profileHi, box_316]
theorem leaf_316_BranchSafe : CertificateConsequences.BranchSafe branch_box_316 := by
  left; refine ⟨branch_box_316_nonnegative, ?_⟩
  intro z hz; exact leaf_316_sound hz

theorem leaf_327_ok : checkAt 527 1000 box_327 cert_327 = true := by
  have h := List.all_eq_true.mp batch_06_11_ok accepted_327 (by simp [batch_06_11_values])
  exact h
theorem leaf_327_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_327.profileLo box_327.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_327_ok
theorem branch_box_327_nonnegative : ∀ j, 0 ≤ branch_box_327.lower j ∧ 0 ≤ branch_box_327.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_327, Box.profileLo, Box.profileHi, box_327]
theorem leaf_327_BranchSafe : CertificateConsequences.BranchSafe branch_box_327 := by
  left; refine ⟨branch_box_327_nonnegative, ?_⟩
  intro z hz; exact leaf_327_sound hz

theorem leaf_328_ok : checkAt 527 1000 box_328 cert_328 = true := by
  have h := List.all_eq_true.mp batch_06_12_ok accepted_328 (by simp [batch_06_12_values])
  exact h
theorem leaf_328_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_328.profileLo box_328.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_328_ok
theorem branch_box_328_nonnegative : ∀ j, 0 ≤ branch_box_328.lower j ∧ 0 ≤ branch_box_328.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_328, Box.profileLo, Box.profileHi, box_328]
theorem leaf_328_BranchSafe : CertificateConsequences.BranchSafe branch_box_328 := by
  left; refine ⟨branch_box_328_nonnegative, ?_⟩
  intro z hz; exact leaf_328_sound hz

theorem leaf_329_ok : checkAt 527 1000 box_329 cert_329 = true := by
  have h := List.all_eq_true.mp batch_06_13_ok accepted_329 (by simp [batch_06_13_values])
  exact h
theorem leaf_329_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_329.profileLo box_329.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_329_ok
theorem branch_box_329_nonnegative : ∀ j, 0 ≤ branch_box_329.lower j ∧ 0 ≤ branch_box_329.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_329, Box.profileLo, Box.profileHi, box_329]
theorem leaf_329_BranchSafe : CertificateConsequences.BranchSafe branch_box_329 := by
  left; refine ⟨branch_box_329_nonnegative, ?_⟩
  intro z hz; exact leaf_329_sound hz

theorem leaf_333_ok : checkAt 527 1000 box_333 cert_333 = true := by
  have h := List.all_eq_true.mp batch_06_14_ok accepted_333 (by simp [batch_06_14_values])
  exact h
theorem leaf_333_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_333.profileLo box_333.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_333_ok
theorem branch_box_333_nonnegative : ∀ j, 0 ≤ branch_box_333.lower j ∧ 0 ≤ branch_box_333.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_333, Box.profileLo, Box.profileHi, box_333]
theorem leaf_333_BranchSafe : CertificateConsequences.BranchSafe branch_box_333 := by
  left; refine ⟨branch_box_333_nonnegative, ?_⟩
  intro z hz; exact leaf_333_sound hz

theorem leaf_334_ok : checkAt 527 1000 box_334 cert_334 = true := by
  have h := List.all_eq_true.mp batch_06_15_ok accepted_334 (by simp [batch_06_15_values])
  exact h
theorem leaf_334_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_334.profileLo box_334.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_334_ok
theorem branch_box_334_nonnegative : ∀ j, 0 ≤ branch_box_334.lower j ∧ 0 ≤ branch_box_334.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_334, Box.profileLo, Box.profileHi, box_334]
theorem leaf_334_BranchSafe : CertificateConsequences.BranchSafe branch_box_334 := by
  left; refine ⟨branch_box_334_nonnegative, ?_⟩
  intro z hz; exact leaf_334_sound hz

theorem leaf_335_ok : checkAt 527 1000 box_335 cert_335 = true := by
  have h := List.all_eq_true.mp batch_06_16_ok accepted_335 (by simp [batch_06_16_values])
  exact h
theorem leaf_335_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_335.profileLo box_335.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_335_ok
theorem branch_box_335_nonnegative : ∀ j, 0 ≤ branch_box_335.lower j ∧ 0 ≤ branch_box_335.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_335, Box.profileLo, Box.profileHi, box_335]
theorem leaf_335_BranchSafe : CertificateConsequences.BranchSafe branch_box_335 := by
  left; refine ⟨branch_box_335_nonnegative, ?_⟩
  intro z hz; exact leaf_335_sound hz

theorem leaf_336_ok : checkAt 527 1000 box_336 cert_336 = true := by
  have h := List.all_eq_true.mp batch_06_17_ok accepted_336 (by simp [batch_06_17_values])
  exact h
theorem leaf_336_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_336.profileLo box_336.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_336_ok
theorem branch_box_336_nonnegative : ∀ j, 0 ≤ branch_box_336.lower j ∧ 0 ≤ branch_box_336.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_336, Box.profileLo, Box.profileHi, box_336]
theorem leaf_336_BranchSafe : CertificateConsequences.BranchSafe branch_box_336 := by
  left; refine ⟨branch_box_336_nonnegative, ?_⟩
  intro z hz; exact leaf_336_sound hz

theorem leaf_342_ok : checkAt 527 1000 box_342 cert_342 = true := by
  have h := List.all_eq_true.mp batch_06_18_ok accepted_342 (by simp [batch_06_18_values])
  exact h
theorem leaf_342_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_342.profileLo box_342.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_342_ok
theorem branch_box_342_nonnegative : ∀ j, 0 ≤ branch_box_342.lower j ∧ 0 ≤ branch_box_342.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_342, Box.profileLo, Box.profileHi, box_342]
theorem leaf_342_BranchSafe : CertificateConsequences.BranchSafe branch_box_342 := by
  left; refine ⟨branch_box_342_nonnegative, ?_⟩
  intro z hz; exact leaf_342_sound hz

theorem leaf_343_ok : checkAt 527 1000 box_343 cert_343 = true := by
  have h := List.all_eq_true.mp batch_06_19_ok accepted_343 (by simp [batch_06_19_values])
  exact h
theorem leaf_343_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_343.profileLo box_343.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_343_ok
theorem branch_box_343_nonnegative : ∀ j, 0 ≤ branch_box_343.lower j ∧ 0 ≤ branch_box_343.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_343, Box.profileLo, Box.profileHi, box_343]
theorem leaf_343_BranchSafe : CertificateConsequences.BranchSafe branch_box_343 := by
  left; refine ⟨branch_box_343_nonnegative, ?_⟩
  intro z hz; exact leaf_343_sound hz

theorem leaf_345_ok : checkAt 527 1000 box_345 cert_345 = true := by
  have h := List.all_eq_true.mp batch_06_20_ok accepted_345 (by simp [batch_06_20_values])
  exact h
theorem leaf_345_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_345.profileLo box_345.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_345_ok
theorem branch_box_345_nonnegative : ∀ j, 0 ≤ branch_box_345.lower j ∧ 0 ≤ branch_box_345.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_345, Box.profileLo, Box.profileHi, box_345]
theorem leaf_345_BranchSafe : CertificateConsequences.BranchSafe branch_box_345 := by
  left; refine ⟨branch_box_345_nonnegative, ?_⟩
  intro z hz; exact leaf_345_sound hz

theorem leaf_346_ok : checkAt 527 1000 box_346 cert_346 = true := by
  have h := List.all_eq_true.mp batch_06_21_ok accepted_346 (by simp [batch_06_21_values])
  exact h
theorem leaf_346_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_346.profileLo box_346.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_346_ok
theorem branch_box_346_nonnegative : ∀ j, 0 ≤ branch_box_346.lower j ∧ 0 ≤ branch_box_346.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_346, Box.profileLo, Box.profileHi, box_346]
theorem leaf_346_BranchSafe : CertificateConsequences.BranchSafe branch_box_346 := by
  left; refine ⟨branch_box_346_nonnegative, ?_⟩
  intro z hz; exact leaf_346_sound hz

theorem leaf_347_ok : checkAt 527 1000 box_347 cert_347 = true := by
  have h := List.all_eq_true.mp batch_06_22_ok accepted_347 (by simp [batch_06_22_values])
  exact h
theorem leaf_347_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_347.profileLo box_347.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_347_ok
theorem branch_box_347_nonnegative : ∀ j, 0 ≤ branch_box_347.lower j ∧ 0 ≤ branch_box_347.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_347, Box.profileLo, Box.profileHi, box_347]
theorem leaf_347_BranchSafe : CertificateConsequences.BranchSafe branch_box_347 := by
  left; refine ⟨branch_box_347_nonnegative, ?_⟩
  intro z hz; exact leaf_347_sound hz

theorem leaf_349_ok : checkAt 527 1000 box_349 cert_349 = true := by
  have h := List.all_eq_true.mp batch_06_23_ok accepted_349 (by simp [batch_06_23_values])
  exact h
theorem leaf_349_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_349.profileLo box_349.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_349_ok
theorem branch_box_349_nonnegative : ∀ j, 0 ≤ branch_box_349.lower j ∧ 0 ≤ branch_box_349.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_349, Box.profileLo, Box.profileHi, box_349]
theorem leaf_349_BranchSafe : CertificateConsequences.BranchSafe branch_box_349 := by
  left; refine ⟨branch_box_349_nonnegative, ?_⟩
  intro z hz; exact leaf_349_sound hz

#print axioms batch_06_00_ok
#print axioms leaf_300_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
