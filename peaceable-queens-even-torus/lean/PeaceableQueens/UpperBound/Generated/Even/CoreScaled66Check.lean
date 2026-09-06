import PeaceableQueens.UpperBound.Generated.Even.CoreScaled66Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_66_00_values : List Bool := [accepted_3302]
theorem batch_66_00_ok : batch_66_00_values.all id = true := by decide

def batch_66_01_values : List Bool := [accepted_3303]
theorem batch_66_01_ok : batch_66_01_values.all id = true := by decide

def batch_66_02_values : List Bool := [accepted_3306]
theorem batch_66_02_ok : batch_66_02_values.all id = true := by decide

def batch_66_03_values : List Bool := [accepted_3307]
theorem batch_66_03_ok : batch_66_03_values.all id = true := by decide

def batch_66_04_values : List Bool := [accepted_3310]
theorem batch_66_04_ok : batch_66_04_values.all id = true := by decide

def batch_66_05_values : List Bool := [accepted_3312]
theorem batch_66_05_ok : batch_66_05_values.all id = true := by decide

def batch_66_06_values : List Bool := [accepted_3314]
theorem batch_66_06_ok : batch_66_06_values.all id = true := by decide

def batch_66_07_values : List Bool := [accepted_3316]
theorem batch_66_07_ok : batch_66_07_values.all id = true := by decide

def batch_66_08_values : List Bool := [accepted_3317]
theorem batch_66_08_ok : batch_66_08_values.all id = true := by decide

def batch_66_09_values : List Bool := [accepted_3320]
theorem batch_66_09_ok : batch_66_09_values.all id = true := by decide

def batch_66_10_values : List Bool := [accepted_3322]
theorem batch_66_10_ok : batch_66_10_values.all id = true := by decide

def batch_66_11_values : List Bool := [accepted_3324]
theorem batch_66_11_ok : batch_66_11_values.all id = true := by decide

def batch_66_12_values : List Bool := [accepted_3326]
theorem batch_66_12_ok : batch_66_12_values.all id = true := by decide

def batch_66_13_values : List Bool := [accepted_3328]
theorem batch_66_13_ok : batch_66_13_values.all id = true := by decide

def batch_66_14_values : List Bool := [accepted_3329]
theorem batch_66_14_ok : batch_66_14_values.all id = true := by decide

def batch_66_15_values : List Bool := [accepted_3332]
theorem batch_66_15_ok : batch_66_15_values.all id = true := by decide

def batch_66_16_values : List Bool := [accepted_3334]
theorem batch_66_16_ok : batch_66_16_values.all id = true := by decide

def batch_66_17_values : List Bool := [accepted_3336]
theorem batch_66_17_ok : batch_66_17_values.all id = true := by decide

def batch_66_18_values : List Bool := [accepted_3338]
theorem batch_66_18_ok : batch_66_18_values.all id = true := by decide

def batch_66_19_values : List Bool := [accepted_3340]
theorem batch_66_19_ok : batch_66_19_values.all id = true := by decide

def batch_66_20_values : List Bool := [accepted_3341]
theorem batch_66_20_ok : batch_66_20_values.all id = true := by decide

def batch_66_21_values : List Bool := [accepted_3343]
theorem batch_66_21_ok : batch_66_21_values.all id = true := by decide

def batch_66_22_values : List Bool := [accepted_3346]
theorem batch_66_22_ok : batch_66_22_values.all id = true := by decide

def batch_66_23_values : List Bool := [accepted_3348]
theorem batch_66_23_ok : batch_66_23_values.all id = true := by decide

theorem leaf_3302_ok : checkAt 527 1000 box_3302 cert_3302 = true := by
  have h := List.all_eq_true.mp batch_66_00_ok accepted_3302 (by simp [batch_66_00_values])
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
  have h := List.all_eq_true.mp batch_66_01_ok accepted_3303 (by simp [batch_66_01_values])
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

theorem leaf_3306_ok : checkAt 527 1000 box_3306 cert_3306 = true := by
  have h := List.all_eq_true.mp batch_66_02_ok accepted_3306 (by simp [batch_66_02_values])
  exact h
theorem leaf_3306_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3306.profileLo box_3306.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3306_ok
theorem branch_box_3306_nonnegative : ∀ j, 0 ≤ branch_box_3306.lower j ∧ 0 ≤ branch_box_3306.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3306, Box.profileLo, Box.profileHi, box_3306]
theorem leaf_3306_BranchSafe : CertificateConsequences.BranchSafe branch_box_3306 := by
  left; refine ⟨branch_box_3306_nonnegative, ?_⟩
  intro z hz; exact leaf_3306_sound hz

theorem leaf_3307_ok : checkAt 527 1000 box_3307 cert_3307 = true := by
  have h := List.all_eq_true.mp batch_66_03_ok accepted_3307 (by simp [batch_66_03_values])
  exact h
theorem leaf_3307_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3307.profileLo box_3307.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3307_ok
theorem branch_box_3307_nonnegative : ∀ j, 0 ≤ branch_box_3307.lower j ∧ 0 ≤ branch_box_3307.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3307, Box.profileLo, Box.profileHi, box_3307]
theorem leaf_3307_BranchSafe : CertificateConsequences.BranchSafe branch_box_3307 := by
  left; refine ⟨branch_box_3307_nonnegative, ?_⟩
  intro z hz; exact leaf_3307_sound hz

theorem leaf_3310_ok : checkAt 527 1000 box_3310 cert_3310 = true := by
  have h := List.all_eq_true.mp batch_66_04_ok accepted_3310 (by simp [batch_66_04_values])
  exact h
theorem leaf_3310_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3310.profileLo box_3310.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3310_ok
theorem branch_box_3310_nonnegative : ∀ j, 0 ≤ branch_box_3310.lower j ∧ 0 ≤ branch_box_3310.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3310, Box.profileLo, Box.profileHi, box_3310]
theorem leaf_3310_BranchSafe : CertificateConsequences.BranchSafe branch_box_3310 := by
  left; refine ⟨branch_box_3310_nonnegative, ?_⟩
  intro z hz; exact leaf_3310_sound hz

theorem leaf_3312_ok : checkAt 527 1000 box_3312 cert_3312 = true := by
  have h := List.all_eq_true.mp batch_66_05_ok accepted_3312 (by simp [batch_66_05_values])
  exact h
theorem leaf_3312_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3312.profileLo box_3312.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3312_ok
theorem branch_box_3312_nonnegative : ∀ j, 0 ≤ branch_box_3312.lower j ∧ 0 ≤ branch_box_3312.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3312, Box.profileLo, Box.profileHi, box_3312]
theorem leaf_3312_BranchSafe : CertificateConsequences.BranchSafe branch_box_3312 := by
  left; refine ⟨branch_box_3312_nonnegative, ?_⟩
  intro z hz; exact leaf_3312_sound hz

theorem leaf_3314_ok : checkAt 527 1000 box_3314 cert_3314 = true := by
  have h := List.all_eq_true.mp batch_66_06_ok accepted_3314 (by simp [batch_66_06_values])
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

theorem leaf_3316_ok : checkAt 527 1000 box_3316 cert_3316 = true := by
  have h := List.all_eq_true.mp batch_66_07_ok accepted_3316 (by simp [batch_66_07_values])
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
  have h := List.all_eq_true.mp batch_66_08_ok accepted_3317 (by simp [batch_66_08_values])
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

theorem leaf_3322_ok : checkAt 527 1000 box_3322 cert_3322 = true := by
  have h := List.all_eq_true.mp batch_66_10_ok accepted_3322 (by simp [batch_66_10_values])
  exact h
theorem leaf_3322_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3322.profileLo box_3322.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3322_ok
theorem branch_box_3322_nonnegative : ∀ j, 0 ≤ branch_box_3322.lower j ∧ 0 ≤ branch_box_3322.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3322, Box.profileLo, Box.profileHi, box_3322]
theorem leaf_3322_BranchSafe : CertificateConsequences.BranchSafe branch_box_3322 := by
  left; refine ⟨branch_box_3322_nonnegative, ?_⟩
  intro z hz; exact leaf_3322_sound hz

theorem leaf_3324_ok : checkAt 527 1000 box_3324 cert_3324 = true := by
  have h := List.all_eq_true.mp batch_66_11_ok accepted_3324 (by simp [batch_66_11_values])
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

theorem leaf_3326_ok : checkAt 527 1000 box_3326 cert_3326 = true := by
  have h := List.all_eq_true.mp batch_66_12_ok accepted_3326 (by simp [batch_66_12_values])
  exact h
theorem leaf_3326_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3326.profileLo box_3326.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3326_ok
theorem branch_box_3326_nonnegative : ∀ j, 0 ≤ branch_box_3326.lower j ∧ 0 ≤ branch_box_3326.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3326, Box.profileLo, Box.profileHi, box_3326]
theorem leaf_3326_BranchSafe : CertificateConsequences.BranchSafe branch_box_3326 := by
  left; refine ⟨branch_box_3326_nonnegative, ?_⟩
  intro z hz; exact leaf_3326_sound hz

theorem leaf_3328_ok : checkAt 527 1000 box_3328 cert_3328 = true := by
  have h := List.all_eq_true.mp batch_66_13_ok accepted_3328 (by simp [batch_66_13_values])
  exact h
theorem leaf_3328_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3328.profileLo box_3328.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3328_ok
theorem branch_box_3328_nonnegative : ∀ j, 0 ≤ branch_box_3328.lower j ∧ 0 ≤ branch_box_3328.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3328, Box.profileLo, Box.profileHi, box_3328]
theorem leaf_3328_BranchSafe : CertificateConsequences.BranchSafe branch_box_3328 := by
  left; refine ⟨branch_box_3328_nonnegative, ?_⟩
  intro z hz; exact leaf_3328_sound hz

theorem leaf_3329_ok : checkAt 527 1000 box_3329 cert_3329 = true := by
  have h := List.all_eq_true.mp batch_66_14_ok accepted_3329 (by simp [batch_66_14_values])
  exact h
theorem leaf_3329_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3329.profileLo box_3329.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3329_ok
theorem branch_box_3329_nonnegative : ∀ j, 0 ≤ branch_box_3329.lower j ∧ 0 ≤ branch_box_3329.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3329, Box.profileLo, Box.profileHi, box_3329]
theorem leaf_3329_BranchSafe : CertificateConsequences.BranchSafe branch_box_3329 := by
  left; refine ⟨branch_box_3329_nonnegative, ?_⟩
  intro z hz; exact leaf_3329_sound hz

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

theorem leaf_3334_ok : checkAt 527 1000 box_3334 cert_3334 = true := by
  have h := List.all_eq_true.mp batch_66_16_ok accepted_3334 (by simp [batch_66_16_values])
  exact h
theorem leaf_3334_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3334.profileLo box_3334.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3334_ok
theorem branch_box_3334_nonnegative : ∀ j, 0 ≤ branch_box_3334.lower j ∧ 0 ≤ branch_box_3334.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3334, Box.profileLo, Box.profileHi, box_3334]
theorem leaf_3334_BranchSafe : CertificateConsequences.BranchSafe branch_box_3334 := by
  left; refine ⟨branch_box_3334_nonnegative, ?_⟩
  intro z hz; exact leaf_3334_sound hz

theorem leaf_3336_ok : checkAt 527 1000 box_3336 cert_3336 = true := by
  have h := List.all_eq_true.mp batch_66_17_ok accepted_3336 (by simp [batch_66_17_values])
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
  have h := List.all_eq_true.mp batch_66_18_ok accepted_3338 (by simp [batch_66_18_values])
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

theorem leaf_3343_ok : checkAt 527 1000 box_3343 cert_3343 = true := by
  have h := List.all_eq_true.mp batch_66_21_ok accepted_3343 (by simp [batch_66_21_values])
  exact h
theorem leaf_3343_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3343.profileLo box_3343.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3343_ok
theorem branch_box_3343_nonnegative : ∀ j, 0 ≤ branch_box_3343.lower j ∧ 0 ≤ branch_box_3343.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3343, Box.profileLo, Box.profileHi, box_3343]
theorem leaf_3343_BranchSafe : CertificateConsequences.BranchSafe branch_box_3343 := by
  left; refine ⟨branch_box_3343_nonnegative, ?_⟩
  intro z hz; exact leaf_3343_sound hz

theorem leaf_3346_ok : checkAt 527 1000 box_3346 cert_3346 = true := by
  have h := List.all_eq_true.mp batch_66_22_ok accepted_3346 (by simp [batch_66_22_values])
  exact h
theorem leaf_3346_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3346.profileLo box_3346.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3346_ok
theorem branch_box_3346_nonnegative : ∀ j, 0 ≤ branch_box_3346.lower j ∧ 0 ≤ branch_box_3346.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3346, Box.profileLo, Box.profileHi, box_3346]
theorem leaf_3346_BranchSafe : CertificateConsequences.BranchSafe branch_box_3346 := by
  left; refine ⟨branch_box_3346_nonnegative, ?_⟩
  intro z hz; exact leaf_3346_sound hz

theorem leaf_3348_ok : checkAt 527 1000 box_3348 cert_3348 = true := by
  have h := List.all_eq_true.mp batch_66_23_ok accepted_3348 (by simp [batch_66_23_values])
  exact h
theorem leaf_3348_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3348.profileLo box_3348.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3348_ok
theorem branch_box_3348_nonnegative : ∀ j, 0 ≤ branch_box_3348.lower j ∧ 0 ≤ branch_box_3348.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3348, Box.profileLo, Box.profileHi, box_3348]
theorem leaf_3348_BranchSafe : CertificateConsequences.BranchSafe branch_box_3348 := by
  left; refine ⟨branch_box_3348_nonnegative, ?_⟩
  intro z hz; exact leaf_3348_sound hz

#print axioms batch_66_00_ok
#print axioms leaf_3302_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
