import PeaceableQueens.UpperBound.Generated.Even.C527Scaled66Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_66_00_values : List Bool := [accepted_3301]
theorem batch_66_00_ok : batch_66_00_values.all id = true := by decide

def batch_66_01_values : List Bool := [accepted_3302]
theorem batch_66_01_ok : batch_66_01_values.all id = true := by decide

def batch_66_02_values : List Bool := [accepted_3303]
theorem batch_66_02_ok : batch_66_02_values.all id = true := by decide

def batch_66_03_values : List Bool := [accepted_3304]
theorem batch_66_03_ok : batch_66_03_values.all id = true := by decide

def batch_66_04_values : List Bool := [accepted_3314]
theorem batch_66_04_ok : batch_66_04_values.all id = true := by decide

def batch_66_05_values : List Bool := [accepted_3315]
theorem batch_66_05_ok : batch_66_05_values.all id = true := by decide

def batch_66_06_values : List Bool := [accepted_3316]
theorem batch_66_06_ok : batch_66_06_values.all id = true := by decide

def batch_66_07_values : List Bool := [accepted_3317]
theorem batch_66_07_ok : batch_66_07_values.all id = true := by decide

def batch_66_08_values : List Bool := [accepted_3319]
theorem batch_66_08_ok : batch_66_08_values.all id = true := by decide

def batch_66_09_values : List Bool := [accepted_3320]
theorem batch_66_09_ok : batch_66_09_values.all id = true := by decide

def batch_66_10_values : List Bool := [accepted_3321]
theorem batch_66_10_ok : batch_66_10_values.all id = true := by decide

def batch_66_11_values : List Bool := [accepted_3323]
theorem batch_66_11_ok : batch_66_11_values.all id = true := by decide

def batch_66_12_values : List Bool := [accepted_3324]
theorem batch_66_12_ok : batch_66_12_values.all id = true := by decide

def batch_66_13_values : List Bool := [accepted_3330]
theorem batch_66_13_ok : batch_66_13_values.all id = true := by decide

def batch_66_14_values : List Bool := [accepted_3331]
theorem batch_66_14_ok : batch_66_14_values.all id = true := by decide

def batch_66_15_values : List Bool := [accepted_3332]
theorem batch_66_15_ok : batch_66_15_values.all id = true := by decide

def batch_66_16_values : List Bool := [accepted_3336]
theorem batch_66_16_ok : batch_66_16_values.all id = true := by decide

def batch_66_17_values : List Bool := [accepted_3338]
theorem batch_66_17_ok : batch_66_17_values.all id = true := by decide

def batch_66_18_values : List Bool := [accepted_3339]
theorem batch_66_18_ok : batch_66_18_values.all id = true := by decide

def batch_66_19_values : List Bool := [accepted_3340]
theorem batch_66_19_ok : batch_66_19_values.all id = true := by decide

def batch_66_20_values : List Bool := [accepted_3341]
theorem batch_66_20_ok : batch_66_20_values.all id = true := by decide

def batch_66_21_values : List Bool := [accepted_3342]
theorem batch_66_21_ok : batch_66_21_values.all id = true := by decide

theorem leaf_3301_ok : checkAt 527 1000 box_3301 cert_3301 = true := by
  have h := List.all_eq_true.mp batch_66_00_ok accepted_3301 (by simp [batch_66_00_values])
  exact h
theorem leaf_3301_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3301.profileLo box_3301.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3301_ok
theorem branch_box_3301_nonnegative : ∀ j, 0 ≤ branch_box_3301.lower j ∧ 0 ≤ branch_box_3301.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3301, Box.profileLo, Box.profileHi, box_3301]
theorem leaf_3301_BranchSafe : CertificateConsequences.BranchSafe branch_box_3301 := by
  left; refine ⟨branch_box_3301_nonnegative, ?_⟩
  intro z hz; exact leaf_3301_sound hz

theorem leaf_3302_ok : checkAt 527 1000 box_3302 cert_3302 = true := by
  have h := List.all_eq_true.mp batch_66_01_ok accepted_3302 (by simp [batch_66_01_values])
  exact h
theorem leaf_3302_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3302.profileLo box_3302.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3302_ok
theorem branch_box_3302_nonnegative : ∀ j, 0 ≤ branch_box_3302.lower j ∧ 0 ≤ branch_box_3302.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3302, Box.profileLo, Box.profileHi, box_3302]
theorem leaf_3302_BranchSafe : CertificateConsequences.BranchSafe branch_box_3302 := by
  left; refine ⟨branch_box_3302_nonnegative, ?_⟩
  intro z hz; exact leaf_3302_sound hz

theorem leaf_3303_ok : checkAt 527 1000 box_3303 cert_3303 = true := by
  have h := List.all_eq_true.mp batch_66_02_ok accepted_3303 (by simp [batch_66_02_values])
  exact h
theorem leaf_3303_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3303.profileLo box_3303.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3303_ok
theorem branch_box_3303_nonnegative : ∀ j, 0 ≤ branch_box_3303.lower j ∧ 0 ≤ branch_box_3303.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3303, Box.profileLo, Box.profileHi, box_3303]
theorem leaf_3303_BranchSafe : CertificateConsequences.BranchSafe branch_box_3303 := by
  left; refine ⟨branch_box_3303_nonnegative, ?_⟩
  intro z hz; exact leaf_3303_sound hz

theorem leaf_3304_ok : checkAt 527 1000 box_3304 cert_3304 = true := by
  have h := List.all_eq_true.mp batch_66_03_ok accepted_3304 (by simp [batch_66_03_values])
  exact h
theorem leaf_3304_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3304.profileLo box_3304.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3304_ok
theorem branch_box_3304_nonnegative : ∀ j, 0 ≤ branch_box_3304.lower j ∧ 0 ≤ branch_box_3304.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3304, Box.profileLo, Box.profileHi, box_3304]
theorem leaf_3304_BranchSafe : CertificateConsequences.BranchSafe branch_box_3304 := by
  left; refine ⟨branch_box_3304_nonnegative, ?_⟩
  intro z hz; exact leaf_3304_sound hz

theorem leaf_3314_ok : checkAt 527 1000 box_3314 cert_3314 = true := by
  have h := List.all_eq_true.mp batch_66_04_ok accepted_3314 (by simp [batch_66_04_values])
  exact h
theorem leaf_3314_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3314.profileLo box_3314.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3314_ok
theorem branch_box_3314_nonnegative : ∀ j, 0 ≤ branch_box_3314.lower j ∧ 0 ≤ branch_box_3314.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3314, Box.profileLo, Box.profileHi, box_3314]
theorem leaf_3314_BranchSafe : CertificateConsequences.BranchSafe branch_box_3314 := by
  left; refine ⟨branch_box_3314_nonnegative, ?_⟩
  intro z hz; exact leaf_3314_sound hz

theorem leaf_3315_ok : checkAt 527 1000 box_3315 cert_3315 = true := by
  have h := List.all_eq_true.mp batch_66_05_ok accepted_3315 (by simp [batch_66_05_values])
  exact h
theorem leaf_3315_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3315.profileLo box_3315.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3315_ok
theorem branch_box_3315_nonnegative : ∀ j, 0 ≤ branch_box_3315.lower j ∧ 0 ≤ branch_box_3315.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3315, Box.profileLo, Box.profileHi, box_3315]
theorem leaf_3315_BranchSafe : CertificateConsequences.BranchSafe branch_box_3315 := by
  left; refine ⟨branch_box_3315_nonnegative, ?_⟩
  intro z hz; exact leaf_3315_sound hz

theorem leaf_3316_ok : checkAt 527 1000 box_3316 cert_3316 = true := by
  have h := List.all_eq_true.mp batch_66_06_ok accepted_3316 (by simp [batch_66_06_values])
  exact h
theorem leaf_3316_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3316.profileLo box_3316.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3316_ok
theorem branch_box_3316_nonnegative : ∀ j, 0 ≤ branch_box_3316.lower j ∧ 0 ≤ branch_box_3316.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3316, Box.profileLo, Box.profileHi, box_3316]
theorem leaf_3316_BranchSafe : CertificateConsequences.BranchSafe branch_box_3316 := by
  left; refine ⟨branch_box_3316_nonnegative, ?_⟩
  intro z hz; exact leaf_3316_sound hz

theorem leaf_3317_ok : checkAt 527 1000 box_3317 cert_3317 = true := by
  have h := List.all_eq_true.mp batch_66_07_ok accepted_3317 (by simp [batch_66_07_values])
  exact h
theorem leaf_3317_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3317.profileLo box_3317.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3317_ok
theorem branch_box_3317_nonnegative : ∀ j, 0 ≤ branch_box_3317.lower j ∧ 0 ≤ branch_box_3317.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3317, Box.profileLo, Box.profileHi, box_3317]
theorem leaf_3317_BranchSafe : CertificateConsequences.BranchSafe branch_box_3317 := by
  left; refine ⟨branch_box_3317_nonnegative, ?_⟩
  intro z hz; exact leaf_3317_sound hz

theorem leaf_3319_ok : checkAt 527 1000 box_3319 cert_3319 = true := by
  have h := List.all_eq_true.mp batch_66_08_ok accepted_3319 (by simp [batch_66_08_values])
  exact h
theorem leaf_3319_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3319.profileLo box_3319.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3319_ok
theorem branch_box_3319_nonnegative : ∀ j, 0 ≤ branch_box_3319.lower j ∧ 0 ≤ branch_box_3319.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3319, Box.profileLo, Box.profileHi, box_3319]
theorem leaf_3319_BranchSafe : CertificateConsequences.BranchSafe branch_box_3319 := by
  left; refine ⟨branch_box_3319_nonnegative, ?_⟩
  intro z hz; exact leaf_3319_sound hz

theorem leaf_3320_ok : checkAt 527 1000 box_3320 cert_3320 = true := by
  have h := List.all_eq_true.mp batch_66_09_ok accepted_3320 (by simp [batch_66_09_values])
  exact h
theorem leaf_3320_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3320.profileLo box_3320.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3320_ok
theorem branch_box_3320_nonnegative : ∀ j, 0 ≤ branch_box_3320.lower j ∧ 0 ≤ branch_box_3320.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3320, Box.profileLo, Box.profileHi, box_3320]
theorem leaf_3320_BranchSafe : CertificateConsequences.BranchSafe branch_box_3320 := by
  left; refine ⟨branch_box_3320_nonnegative, ?_⟩
  intro z hz; exact leaf_3320_sound hz

theorem leaf_3321_ok : checkAt 527 1000 box_3321 cert_3321 = true := by
  have h := List.all_eq_true.mp batch_66_10_ok accepted_3321 (by simp [batch_66_10_values])
  exact h
theorem leaf_3321_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3321.profileLo box_3321.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3321_ok
theorem branch_box_3321_nonnegative : ∀ j, 0 ≤ branch_box_3321.lower j ∧ 0 ≤ branch_box_3321.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3321, Box.profileLo, Box.profileHi, box_3321]
theorem leaf_3321_BranchSafe : CertificateConsequences.BranchSafe branch_box_3321 := by
  left; refine ⟨branch_box_3321_nonnegative, ?_⟩
  intro z hz; exact leaf_3321_sound hz

theorem leaf_3323_ok : checkAt 527 1000 box_3323 cert_3323 = true := by
  have h := List.all_eq_true.mp batch_66_11_ok accepted_3323 (by simp [batch_66_11_values])
  exact h
theorem leaf_3323_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3323.profileLo box_3323.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3323_ok
theorem branch_box_3323_nonnegative : ∀ j, 0 ≤ branch_box_3323.lower j ∧ 0 ≤ branch_box_3323.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3323, Box.profileLo, Box.profileHi, box_3323]
theorem leaf_3323_BranchSafe : CertificateConsequences.BranchSafe branch_box_3323 := by
  left; refine ⟨branch_box_3323_nonnegative, ?_⟩
  intro z hz; exact leaf_3323_sound hz

theorem leaf_3324_ok : checkAt 527 1000 box_3324 cert_3324 = true := by
  have h := List.all_eq_true.mp batch_66_12_ok accepted_3324 (by simp [batch_66_12_values])
  exact h
theorem leaf_3324_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3324.profileLo box_3324.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3324_ok
theorem branch_box_3324_nonnegative : ∀ j, 0 ≤ branch_box_3324.lower j ∧ 0 ≤ branch_box_3324.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3324, Box.profileLo, Box.profileHi, box_3324]
theorem leaf_3324_BranchSafe : CertificateConsequences.BranchSafe branch_box_3324 := by
  left; refine ⟨branch_box_3324_nonnegative, ?_⟩
  intro z hz; exact leaf_3324_sound hz

theorem leaf_3330_ok : checkAt 527 1000 box_3330 cert_3330 = true := by
  have h := List.all_eq_true.mp batch_66_13_ok accepted_3330 (by simp [batch_66_13_values])
  exact h
theorem leaf_3330_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3330.profileLo box_3330.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3330_ok
theorem branch_box_3330_nonnegative : ∀ j, 0 ≤ branch_box_3330.lower j ∧ 0 ≤ branch_box_3330.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3330, Box.profileLo, Box.profileHi, box_3330]
theorem leaf_3330_BranchSafe : CertificateConsequences.BranchSafe branch_box_3330 := by
  left; refine ⟨branch_box_3330_nonnegative, ?_⟩
  intro z hz; exact leaf_3330_sound hz

theorem leaf_3331_ok : checkAt 527 1000 box_3331 cert_3331 = true := by
  have h := List.all_eq_true.mp batch_66_14_ok accepted_3331 (by simp [batch_66_14_values])
  exact h
theorem leaf_3331_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3331.profileLo box_3331.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3331_ok
theorem branch_box_3331_nonnegative : ∀ j, 0 ≤ branch_box_3331.lower j ∧ 0 ≤ branch_box_3331.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3331, Box.profileLo, Box.profileHi, box_3331]
theorem leaf_3331_BranchSafe : CertificateConsequences.BranchSafe branch_box_3331 := by
  left; refine ⟨branch_box_3331_nonnegative, ?_⟩
  intro z hz; exact leaf_3331_sound hz

theorem leaf_3332_ok : checkAt 527 1000 box_3332 cert_3332 = true := by
  have h := List.all_eq_true.mp batch_66_15_ok accepted_3332 (by simp [batch_66_15_values])
  exact h
theorem leaf_3332_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3332.profileLo box_3332.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3332_ok
theorem branch_box_3332_nonnegative : ∀ j, 0 ≤ branch_box_3332.lower j ∧ 0 ≤ branch_box_3332.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3332, Box.profileLo, Box.profileHi, box_3332]
theorem leaf_3332_BranchSafe : CertificateConsequences.BranchSafe branch_box_3332 := by
  left; refine ⟨branch_box_3332_nonnegative, ?_⟩
  intro z hz; exact leaf_3332_sound hz

theorem leaf_3336_ok : checkAt 527 1000 box_3336 cert_3336 = true := by
  have h := List.all_eq_true.mp batch_66_16_ok accepted_3336 (by simp [batch_66_16_values])
  exact h
theorem leaf_3336_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3336.profileLo box_3336.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3336_ok
theorem branch_box_3336_nonnegative : ∀ j, 0 ≤ branch_box_3336.lower j ∧ 0 ≤ branch_box_3336.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3336, Box.profileLo, Box.profileHi, box_3336]
theorem leaf_3336_BranchSafe : CertificateConsequences.BranchSafe branch_box_3336 := by
  left; refine ⟨branch_box_3336_nonnegative, ?_⟩
  intro z hz; exact leaf_3336_sound hz

theorem leaf_3338_ok : checkAt 527 1000 box_3338 cert_3338 = true := by
  have h := List.all_eq_true.mp batch_66_17_ok accepted_3338 (by simp [batch_66_17_values])
  exact h
theorem leaf_3338_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3338.profileLo box_3338.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3338_ok
theorem branch_box_3338_nonnegative : ∀ j, 0 ≤ branch_box_3338.lower j ∧ 0 ≤ branch_box_3338.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3338, Box.profileLo, Box.profileHi, box_3338]
theorem leaf_3338_BranchSafe : CertificateConsequences.BranchSafe branch_box_3338 := by
  left; refine ⟨branch_box_3338_nonnegative, ?_⟩
  intro z hz; exact leaf_3338_sound hz

theorem leaf_3339_ok : checkAt 527 1000 box_3339 cert_3339 = true := by
  have h := List.all_eq_true.mp batch_66_18_ok accepted_3339 (by simp [batch_66_18_values])
  exact h
theorem leaf_3339_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3339.profileLo box_3339.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3339_ok
theorem branch_box_3339_nonnegative : ∀ j, 0 ≤ branch_box_3339.lower j ∧ 0 ≤ branch_box_3339.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3339, Box.profileLo, Box.profileHi, box_3339]
theorem leaf_3339_BranchSafe : CertificateConsequences.BranchSafe branch_box_3339 := by
  left; refine ⟨branch_box_3339_nonnegative, ?_⟩
  intro z hz; exact leaf_3339_sound hz

theorem leaf_3340_ok : checkAt 527 1000 box_3340 cert_3340 = true := by
  have h := List.all_eq_true.mp batch_66_19_ok accepted_3340 (by simp [batch_66_19_values])
  exact h
theorem leaf_3340_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3340.profileLo box_3340.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3340_ok
theorem branch_box_3340_nonnegative : ∀ j, 0 ≤ branch_box_3340.lower j ∧ 0 ≤ branch_box_3340.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3340, Box.profileLo, Box.profileHi, box_3340]
theorem leaf_3340_BranchSafe : CertificateConsequences.BranchSafe branch_box_3340 := by
  left; refine ⟨branch_box_3340_nonnegative, ?_⟩
  intro z hz; exact leaf_3340_sound hz

theorem leaf_3341_ok : checkAt 527 1000 box_3341 cert_3341 = true := by
  have h := List.all_eq_true.mp batch_66_20_ok accepted_3341 (by simp [batch_66_20_values])
  exact h
theorem leaf_3341_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3341.profileLo box_3341.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3341_ok
theorem branch_box_3341_nonnegative : ∀ j, 0 ≤ branch_box_3341.lower j ∧ 0 ≤ branch_box_3341.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3341, Box.profileLo, Box.profileHi, box_3341]
theorem leaf_3341_BranchSafe : CertificateConsequences.BranchSafe branch_box_3341 := by
  left; refine ⟨branch_box_3341_nonnegative, ?_⟩
  intro z hz; exact leaf_3341_sound hz

theorem leaf_3342_ok : checkAt 527 1000 box_3342 cert_3342 = true := by
  have h := List.all_eq_true.mp batch_66_21_ok accepted_3342 (by simp [batch_66_21_values])
  exact h
theorem leaf_3342_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3342.profileLo box_3342.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3342_ok
theorem branch_box_3342_nonnegative : ∀ j, 0 ≤ branch_box_3342.lower j ∧ 0 ≤ branch_box_3342.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3342, Box.profileLo, Box.profileHi, box_3342]
theorem leaf_3342_BranchSafe : CertificateConsequences.BranchSafe branch_box_3342 := by
  left; refine ⟨branch_box_3342_nonnegative, ?_⟩
  intro z hz; exact leaf_3342_sound hz

#print axioms batch_66_00_ok
#print axioms leaf_3301_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
