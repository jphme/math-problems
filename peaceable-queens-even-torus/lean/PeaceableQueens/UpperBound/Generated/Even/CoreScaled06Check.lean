import PeaceableQueens.UpperBound.Generated.Even.CoreScaled06Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_06_00_values : List Bool := [accepted_302]
theorem batch_06_00_ok : batch_06_00_values.all id = true := by decide

def batch_06_01_values : List Bool := [accepted_305]
theorem batch_06_01_ok : batch_06_01_values.all id = true := by decide

def batch_06_02_values : List Bool := [accepted_307]
theorem batch_06_02_ok : batch_06_02_values.all id = true := by decide

def batch_06_03_values : List Bool := [accepted_309]
theorem batch_06_03_ok : batch_06_03_values.all id = true := by decide

def batch_06_04_values : List Bool := [accepted_312]
theorem batch_06_04_ok : batch_06_04_values.all id = true := by decide

def batch_06_05_values : List Bool := [accepted_313]
theorem batch_06_05_ok : batch_06_05_values.all id = true := by decide

def batch_06_06_values : List Bool := [accepted_316]
theorem batch_06_06_ok : batch_06_06_values.all id = true := by decide

def batch_06_07_values : List Bool := [accepted_318]
theorem batch_06_07_ok : batch_06_07_values.all id = true := by decide

def batch_06_08_values : List Bool := [accepted_319]
theorem batch_06_08_ok : batch_06_08_values.all id = true := by decide

def batch_06_09_values : List Bool := [accepted_321]
theorem batch_06_09_ok : batch_06_09_values.all id = true := by decide

def batch_06_10_values : List Bool := [accepted_323]
theorem batch_06_10_ok : batch_06_10_values.all id = true := by decide

def batch_06_11_values : List Bool := [accepted_326]
theorem batch_06_11_ok : batch_06_11_values.all id = true := by decide

def batch_06_12_values : List Bool := [accepted_328]
theorem batch_06_12_ok : batch_06_12_values.all id = true := by decide

def batch_06_13_values : List Bool := [accepted_330]
theorem batch_06_13_ok : batch_06_13_values.all id = true := by decide

def batch_06_14_values : List Bool := [accepted_331]
theorem batch_06_14_ok : batch_06_14_values.all id = true := by decide

def batch_06_15_values : List Bool := [accepted_333]
theorem batch_06_15_ok : batch_06_15_values.all id = true := by decide

def batch_06_16_values : List Bool := [accepted_337]
theorem batch_06_16_ok : batch_06_16_values.all id = true := by decide

def batch_06_17_values : List Bool := [accepted_342]
theorem batch_06_17_ok : batch_06_17_values.all id = true := by decide

def batch_06_18_values : List Bool := [accepted_343]
theorem batch_06_18_ok : batch_06_18_values.all id = true := by decide

def batch_06_19_values : List Bool := [accepted_345]
theorem batch_06_19_ok : batch_06_19_values.all id = true := by decide

def batch_06_20_values : List Bool := [accepted_347]
theorem batch_06_20_ok : batch_06_20_values.all id = true := by decide

theorem leaf_302_ok : checkAt 527 1000 box_302 cert_302 = true := by
  have h := List.all_eq_true.mp batch_06_00_ok accepted_302 (by simp [batch_06_00_values])
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
  have h := List.all_eq_true.mp batch_06_01_ok accepted_305 (by simp [batch_06_01_values])
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

theorem leaf_307_ok : checkAt 527 1000 box_307 cert_307 = true := by
  have h := List.all_eq_true.mp batch_06_02_ok accepted_307 (by simp [batch_06_02_values])
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
  have h := List.all_eq_true.mp batch_06_03_ok accepted_309 (by simp [batch_06_03_values])
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

theorem leaf_312_ok : checkAt 527 1000 box_312 cert_312 = true := by
  have h := List.all_eq_true.mp batch_06_04_ok accepted_312 (by simp [batch_06_04_values])
  exact h
theorem leaf_312_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_312.profileLo box_312.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_312_ok
theorem branch_box_312_nonnegative : ∀ j, 0 ≤ branch_box_312.lower j ∧ 0 ≤ branch_box_312.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_312, Box.profileLo, Box.profileHi, box_312]
theorem leaf_312_BranchSafe : CertificateConsequences.BranchSafe branch_box_312 := by
  left; refine ⟨branch_box_312_nonnegative, ?_⟩
  intro z hz; exact leaf_312_sound hz

theorem leaf_313_ok : checkAt 527 1000 box_313 cert_313 = true := by
  have h := List.all_eq_true.mp batch_06_05_ok accepted_313 (by simp [batch_06_05_values])
  exact h
theorem leaf_313_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_313.profileLo box_313.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_313_ok
theorem branch_box_313_nonnegative : ∀ j, 0 ≤ branch_box_313.lower j ∧ 0 ≤ branch_box_313.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_313, Box.profileLo, Box.profileHi, box_313]
theorem leaf_313_BranchSafe : CertificateConsequences.BranchSafe branch_box_313 := by
  left; refine ⟨branch_box_313_nonnegative, ?_⟩
  intro z hz; exact leaf_313_sound hz

theorem leaf_316_ok : checkAt 527 1000 box_316 cert_316 = true := by
  have h := List.all_eq_true.mp batch_06_06_ok accepted_316 (by simp [batch_06_06_values])
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

theorem leaf_318_ok : checkAt 527 1000 box_318 cert_318 = true := by
  have h := List.all_eq_true.mp batch_06_07_ok accepted_318 (by simp [batch_06_07_values])
  exact h
theorem leaf_318_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_318.profileLo box_318.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_318_ok
theorem branch_box_318_nonnegative : ∀ j, 0 ≤ branch_box_318.lower j ∧ 0 ≤ branch_box_318.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_318, Box.profileLo, Box.profileHi, box_318]
theorem leaf_318_BranchSafe : CertificateConsequences.BranchSafe branch_box_318 := by
  left; refine ⟨branch_box_318_nonnegative, ?_⟩
  intro z hz; exact leaf_318_sound hz

theorem leaf_319_ok : checkAt 527 1000 box_319 cert_319 = true := by
  have h := List.all_eq_true.mp batch_06_08_ok accepted_319 (by simp [batch_06_08_values])
  exact h
theorem leaf_319_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_319.profileLo box_319.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_319_ok
theorem branch_box_319_nonnegative : ∀ j, 0 ≤ branch_box_319.lower j ∧ 0 ≤ branch_box_319.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_319, Box.profileLo, Box.profileHi, box_319]
theorem leaf_319_BranchSafe : CertificateConsequences.BranchSafe branch_box_319 := by
  left; refine ⟨branch_box_319_nonnegative, ?_⟩
  intro z hz; exact leaf_319_sound hz

theorem leaf_321_ok : checkAt 527 1000 box_321 cert_321 = true := by
  have h := List.all_eq_true.mp batch_06_09_ok accepted_321 (by simp [batch_06_09_values])
  exact h
theorem leaf_321_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_321.profileLo box_321.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_321_ok
theorem branch_box_321_nonnegative : ∀ j, 0 ≤ branch_box_321.lower j ∧ 0 ≤ branch_box_321.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_321, Box.profileLo, Box.profileHi, box_321]
theorem leaf_321_BranchSafe : CertificateConsequences.BranchSafe branch_box_321 := by
  left; refine ⟨branch_box_321_nonnegative, ?_⟩
  intro z hz; exact leaf_321_sound hz

theorem leaf_323_ok : checkAt 527 1000 box_323 cert_323 = true := by
  have h := List.all_eq_true.mp batch_06_10_ok accepted_323 (by simp [batch_06_10_values])
  exact h
theorem leaf_323_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_323.profileLo box_323.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_323_ok
theorem branch_box_323_nonnegative : ∀ j, 0 ≤ branch_box_323.lower j ∧ 0 ≤ branch_box_323.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_323, Box.profileLo, Box.profileHi, box_323]
theorem leaf_323_BranchSafe : CertificateConsequences.BranchSafe branch_box_323 := by
  left; refine ⟨branch_box_323_nonnegative, ?_⟩
  intro z hz; exact leaf_323_sound hz

theorem leaf_326_ok : checkAt 527 1000 box_326 cert_326 = true := by
  have h := List.all_eq_true.mp batch_06_11_ok accepted_326 (by simp [batch_06_11_values])
  exact h
theorem leaf_326_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_326.profileLo box_326.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_326_ok
theorem branch_box_326_nonnegative : ∀ j, 0 ≤ branch_box_326.lower j ∧ 0 ≤ branch_box_326.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_326, Box.profileLo, Box.profileHi, box_326]
theorem leaf_326_BranchSafe : CertificateConsequences.BranchSafe branch_box_326 := by
  left; refine ⟨branch_box_326_nonnegative, ?_⟩
  intro z hz; exact leaf_326_sound hz

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

theorem leaf_330_ok : checkAt 527 1000 box_330 cert_330 = true := by
  have h := List.all_eq_true.mp batch_06_13_ok accepted_330 (by simp [batch_06_13_values])
  exact h
theorem leaf_330_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_330.profileLo box_330.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_330_ok
theorem branch_box_330_nonnegative : ∀ j, 0 ≤ branch_box_330.lower j ∧ 0 ≤ branch_box_330.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_330, Box.profileLo, Box.profileHi, box_330]
theorem leaf_330_BranchSafe : CertificateConsequences.BranchSafe branch_box_330 := by
  left; refine ⟨branch_box_330_nonnegative, ?_⟩
  intro z hz; exact leaf_330_sound hz

theorem leaf_331_ok : checkAt 527 1000 box_331 cert_331 = true := by
  have h := List.all_eq_true.mp batch_06_14_ok accepted_331 (by simp [batch_06_14_values])
  exact h
theorem leaf_331_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_331.profileLo box_331.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_331_ok
theorem branch_box_331_nonnegative : ∀ j, 0 ≤ branch_box_331.lower j ∧ 0 ≤ branch_box_331.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_331, Box.profileLo, Box.profileHi, box_331]
theorem leaf_331_BranchSafe : CertificateConsequences.BranchSafe branch_box_331 := by
  left; refine ⟨branch_box_331_nonnegative, ?_⟩
  intro z hz; exact leaf_331_sound hz

theorem leaf_333_ok : checkAt 527 1000 box_333 cert_333 = true := by
  have h := List.all_eq_true.mp batch_06_15_ok accepted_333 (by simp [batch_06_15_values])
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

theorem leaf_337_ok : checkAt 527 1000 box_337 cert_337 = true := by
  have h := List.all_eq_true.mp batch_06_16_ok accepted_337 (by simp [batch_06_16_values])
  exact h
theorem leaf_337_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_337.profileLo box_337.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_337_ok
theorem branch_box_337_nonnegative : ∀ j, 0 ≤ branch_box_337.lower j ∧ 0 ≤ branch_box_337.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_337, Box.profileLo, Box.profileHi, box_337]
theorem leaf_337_BranchSafe : CertificateConsequences.BranchSafe branch_box_337 := by
  left; refine ⟨branch_box_337_nonnegative, ?_⟩
  intro z hz; exact leaf_337_sound hz

theorem leaf_342_ok : checkAt 527 1000 box_342 cert_342 = true := by
  have h := List.all_eq_true.mp batch_06_17_ok accepted_342 (by simp [batch_06_17_values])
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
  have h := List.all_eq_true.mp batch_06_18_ok accepted_343 (by simp [batch_06_18_values])
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
  have h := List.all_eq_true.mp batch_06_19_ok accepted_345 (by simp [batch_06_19_values])
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

theorem leaf_347_ok : checkAt 527 1000 box_347 cert_347 = true := by
  have h := List.all_eq_true.mp batch_06_20_ok accepted_347 (by simp [batch_06_20_values])
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

#print axioms batch_06_00_ok
#print axioms leaf_302_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
