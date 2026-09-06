import PeaceableQueens.UpperBound.Generated.Even.C527Scaled86Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_86_00_values : List Bool := [accepted_4301]
theorem batch_86_00_ok : batch_86_00_values.all id = true := by decide

def batch_86_01_values : List Bool := [accepted_4302]
theorem batch_86_01_ok : batch_86_01_values.all id = true := by decide

def batch_86_02_values : List Bool := [accepted_4305]
theorem batch_86_02_ok : batch_86_02_values.all id = true := by decide

def batch_86_03_values : List Bool := [accepted_4306]
theorem batch_86_03_ok : batch_86_03_values.all id = true := by decide

def batch_86_04_values : List Bool := [accepted_4307]
theorem batch_86_04_ok : batch_86_04_values.all id = true := by decide

def batch_86_05_values : List Bool := [accepted_4308]
theorem batch_86_05_ok : batch_86_05_values.all id = true := by decide

def batch_86_06_values : List Bool := [accepted_4311]
theorem batch_86_06_ok : batch_86_06_values.all id = true := by decide

def batch_86_07_values : List Bool := [accepted_4313]
theorem batch_86_07_ok : batch_86_07_values.all id = true := by decide

def batch_86_08_values : List Bool := [accepted_4314]
theorem batch_86_08_ok : batch_86_08_values.all id = true := by decide

def batch_86_09_values : List Bool := [accepted_4318]
theorem batch_86_09_ok : batch_86_09_values.all id = true := by decide

def batch_86_10_values : List Bool := [accepted_4319]
theorem batch_86_10_ok : batch_86_10_values.all id = true := by decide

def batch_86_11_values : List Bool := [accepted_4320]
theorem batch_86_11_ok : batch_86_11_values.all id = true := by decide

def batch_86_12_values : List Bool := [accepted_4321]
theorem batch_86_12_ok : batch_86_12_values.all id = true := by decide

def batch_86_13_values : List Bool := [accepted_4323]
theorem batch_86_13_ok : batch_86_13_values.all id = true := by decide

def batch_86_14_values : List Bool := [accepted_4325]
theorem batch_86_14_ok : batch_86_14_values.all id = true := by decide

def batch_86_15_values : List Bool := [accepted_4326]
theorem batch_86_15_ok : batch_86_15_values.all id = true := by decide

def batch_86_16_values : List Bool := [accepted_4334]
theorem batch_86_16_ok : batch_86_16_values.all id = true := by decide

def batch_86_17_values : List Bool := [accepted_4335]
theorem batch_86_17_ok : batch_86_17_values.all id = true := by decide

def batch_86_18_values : List Bool := [accepted_4336]
theorem batch_86_18_ok : batch_86_18_values.all id = true := by decide

def batch_86_19_values : List Bool := [accepted_4337]
theorem batch_86_19_ok : batch_86_19_values.all id = true := by decide

def batch_86_20_values : List Bool := [accepted_4338]
theorem batch_86_20_ok : batch_86_20_values.all id = true := by decide

def batch_86_21_values : List Bool := [accepted_4347]
theorem batch_86_21_ok : batch_86_21_values.all id = true := by decide

def batch_86_22_values : List Bool := [accepted_4348]
theorem batch_86_22_ok : batch_86_22_values.all id = true := by decide

def batch_86_23_values : List Bool := [accepted_4349]
theorem batch_86_23_ok : batch_86_23_values.all id = true := by decide

theorem leaf_4301_ok : checkAt 527 1000 box_4301 cert_4301 = true := by
  have h := List.all_eq_true.mp batch_86_00_ok accepted_4301 (by simp [batch_86_00_values])
  exact h
theorem leaf_4301_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4301.profileLo box_4301.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4301_ok
theorem branch_box_4301_nonnegative : ∀ j, 0 ≤ branch_box_4301.lower j ∧ 0 ≤ branch_box_4301.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4301, Box.profileLo, Box.profileHi, box_4301]
theorem leaf_4301_BranchSafe : CertificateConsequences.BranchSafe branch_box_4301 := by
  left; refine ⟨branch_box_4301_nonnegative, ?_⟩
  intro z hz; exact leaf_4301_sound hz

theorem leaf_4302_ok : checkAt 527 1000 box_4302 cert_4302 = true := by
  have h := List.all_eq_true.mp batch_86_01_ok accepted_4302 (by simp [batch_86_01_values])
  exact h
theorem leaf_4302_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4302.profileLo box_4302.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4302_ok
theorem branch_box_4302_nonnegative : ∀ j, 0 ≤ branch_box_4302.lower j ∧ 0 ≤ branch_box_4302.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4302, Box.profileLo, Box.profileHi, box_4302]
theorem leaf_4302_BranchSafe : CertificateConsequences.BranchSafe branch_box_4302 := by
  left; refine ⟨branch_box_4302_nonnegative, ?_⟩
  intro z hz; exact leaf_4302_sound hz

theorem leaf_4305_ok : checkAt 527 1000 box_4305 cert_4305 = true := by
  have h := List.all_eq_true.mp batch_86_02_ok accepted_4305 (by simp [batch_86_02_values])
  exact h
theorem leaf_4305_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4305.profileLo box_4305.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4305_ok
theorem branch_box_4305_nonnegative : ∀ j, 0 ≤ branch_box_4305.lower j ∧ 0 ≤ branch_box_4305.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4305, Box.profileLo, Box.profileHi, box_4305]
theorem leaf_4305_BranchSafe : CertificateConsequences.BranchSafe branch_box_4305 := by
  left; refine ⟨branch_box_4305_nonnegative, ?_⟩
  intro z hz; exact leaf_4305_sound hz

theorem leaf_4306_ok : checkAt 527 1000 box_4306 cert_4306 = true := by
  have h := List.all_eq_true.mp batch_86_03_ok accepted_4306 (by simp [batch_86_03_values])
  exact h
theorem leaf_4306_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4306.profileLo box_4306.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4306_ok
theorem branch_box_4306_nonnegative : ∀ j, 0 ≤ branch_box_4306.lower j ∧ 0 ≤ branch_box_4306.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4306, Box.profileLo, Box.profileHi, box_4306]
theorem leaf_4306_BranchSafe : CertificateConsequences.BranchSafe branch_box_4306 := by
  left; refine ⟨branch_box_4306_nonnegative, ?_⟩
  intro z hz; exact leaf_4306_sound hz

theorem leaf_4307_ok : checkAt 527 1000 box_4307 cert_4307 = true := by
  have h := List.all_eq_true.mp batch_86_04_ok accepted_4307 (by simp [batch_86_04_values])
  exact h
theorem leaf_4307_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4307.profileLo box_4307.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4307_ok
theorem branch_box_4307_nonnegative : ∀ j, 0 ≤ branch_box_4307.lower j ∧ 0 ≤ branch_box_4307.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4307, Box.profileLo, Box.profileHi, box_4307]
theorem leaf_4307_BranchSafe : CertificateConsequences.BranchSafe branch_box_4307 := by
  left; refine ⟨branch_box_4307_nonnegative, ?_⟩
  intro z hz; exact leaf_4307_sound hz

theorem leaf_4308_ok : checkAt 527 1000 box_4308 cert_4308 = true := by
  have h := List.all_eq_true.mp batch_86_05_ok accepted_4308 (by simp [batch_86_05_values])
  exact h
theorem leaf_4308_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4308.profileLo box_4308.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4308_ok
theorem branch_box_4308_nonnegative : ∀ j, 0 ≤ branch_box_4308.lower j ∧ 0 ≤ branch_box_4308.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4308, Box.profileLo, Box.profileHi, box_4308]
theorem leaf_4308_BranchSafe : CertificateConsequences.BranchSafe branch_box_4308 := by
  left; refine ⟨branch_box_4308_nonnegative, ?_⟩
  intro z hz; exact leaf_4308_sound hz

theorem leaf_4311_ok : checkAt 527 1000 box_4311 cert_4311 = true := by
  have h := List.all_eq_true.mp batch_86_06_ok accepted_4311 (by simp [batch_86_06_values])
  exact h
theorem leaf_4311_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4311.profileLo box_4311.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4311_ok
theorem branch_box_4311_nonnegative : ∀ j, 0 ≤ branch_box_4311.lower j ∧ 0 ≤ branch_box_4311.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4311, Box.profileLo, Box.profileHi, box_4311]
theorem leaf_4311_BranchSafe : CertificateConsequences.BranchSafe branch_box_4311 := by
  left; refine ⟨branch_box_4311_nonnegative, ?_⟩
  intro z hz; exact leaf_4311_sound hz

theorem leaf_4313_ok : checkAt 527 1000 box_4313 cert_4313 = true := by
  have h := List.all_eq_true.mp batch_86_07_ok accepted_4313 (by simp [batch_86_07_values])
  exact h
theorem leaf_4313_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4313.profileLo box_4313.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4313_ok
theorem branch_box_4313_nonnegative : ∀ j, 0 ≤ branch_box_4313.lower j ∧ 0 ≤ branch_box_4313.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4313, Box.profileLo, Box.profileHi, box_4313]
theorem leaf_4313_BranchSafe : CertificateConsequences.BranchSafe branch_box_4313 := by
  left; refine ⟨branch_box_4313_nonnegative, ?_⟩
  intro z hz; exact leaf_4313_sound hz

theorem leaf_4314_ok : checkAt 527 1000 box_4314 cert_4314 = true := by
  have h := List.all_eq_true.mp batch_86_08_ok accepted_4314 (by simp [batch_86_08_values])
  exact h
theorem leaf_4314_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4314.profileLo box_4314.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4314_ok
theorem branch_box_4314_nonnegative : ∀ j, 0 ≤ branch_box_4314.lower j ∧ 0 ≤ branch_box_4314.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4314, Box.profileLo, Box.profileHi, box_4314]
theorem leaf_4314_BranchSafe : CertificateConsequences.BranchSafe branch_box_4314 := by
  left; refine ⟨branch_box_4314_nonnegative, ?_⟩
  intro z hz; exact leaf_4314_sound hz

theorem leaf_4318_ok : checkAt 527 1000 box_4318 cert_4318 = true := by
  have h := List.all_eq_true.mp batch_86_09_ok accepted_4318 (by simp [batch_86_09_values])
  exact h
theorem leaf_4318_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4318.profileLo box_4318.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4318_ok
theorem branch_box_4318_nonnegative : ∀ j, 0 ≤ branch_box_4318.lower j ∧ 0 ≤ branch_box_4318.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4318, Box.profileLo, Box.profileHi, box_4318]
theorem leaf_4318_BranchSafe : CertificateConsequences.BranchSafe branch_box_4318 := by
  left; refine ⟨branch_box_4318_nonnegative, ?_⟩
  intro z hz; exact leaf_4318_sound hz

theorem leaf_4319_ok : checkAt 527 1000 box_4319 cert_4319 = true := by
  have h := List.all_eq_true.mp batch_86_10_ok accepted_4319 (by simp [batch_86_10_values])
  exact h
theorem leaf_4319_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4319.profileLo box_4319.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4319_ok
theorem branch_box_4319_nonnegative : ∀ j, 0 ≤ branch_box_4319.lower j ∧ 0 ≤ branch_box_4319.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4319, Box.profileLo, Box.profileHi, box_4319]
theorem leaf_4319_BranchSafe : CertificateConsequences.BranchSafe branch_box_4319 := by
  left; refine ⟨branch_box_4319_nonnegative, ?_⟩
  intro z hz; exact leaf_4319_sound hz

theorem leaf_4320_ok : checkAt 527 1000 box_4320 cert_4320 = true := by
  have h := List.all_eq_true.mp batch_86_11_ok accepted_4320 (by simp [batch_86_11_values])
  exact h
theorem leaf_4320_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4320.profileLo box_4320.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4320_ok
theorem branch_box_4320_nonnegative : ∀ j, 0 ≤ branch_box_4320.lower j ∧ 0 ≤ branch_box_4320.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4320, Box.profileLo, Box.profileHi, box_4320]
theorem leaf_4320_BranchSafe : CertificateConsequences.BranchSafe branch_box_4320 := by
  left; refine ⟨branch_box_4320_nonnegative, ?_⟩
  intro z hz; exact leaf_4320_sound hz

theorem leaf_4321_ok : checkAt 527 1000 box_4321 cert_4321 = true := by
  have h := List.all_eq_true.mp batch_86_12_ok accepted_4321 (by simp [batch_86_12_values])
  exact h
theorem leaf_4321_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4321.profileLo box_4321.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4321_ok
theorem branch_box_4321_nonnegative : ∀ j, 0 ≤ branch_box_4321.lower j ∧ 0 ≤ branch_box_4321.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4321, Box.profileLo, Box.profileHi, box_4321]
theorem leaf_4321_BranchSafe : CertificateConsequences.BranchSafe branch_box_4321 := by
  left; refine ⟨branch_box_4321_nonnegative, ?_⟩
  intro z hz; exact leaf_4321_sound hz

theorem leaf_4323_ok : checkAt 527 1000 box_4323 cert_4323 = true := by
  have h := List.all_eq_true.mp batch_86_13_ok accepted_4323 (by simp [batch_86_13_values])
  exact h
theorem leaf_4323_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4323.profileLo box_4323.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4323_ok
theorem branch_box_4323_nonnegative : ∀ j, 0 ≤ branch_box_4323.lower j ∧ 0 ≤ branch_box_4323.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4323, Box.profileLo, Box.profileHi, box_4323]
theorem leaf_4323_BranchSafe : CertificateConsequences.BranchSafe branch_box_4323 := by
  left; refine ⟨branch_box_4323_nonnegative, ?_⟩
  intro z hz; exact leaf_4323_sound hz

theorem leaf_4325_ok : checkAt 527 1000 box_4325 cert_4325 = true := by
  have h := List.all_eq_true.mp batch_86_14_ok accepted_4325 (by simp [batch_86_14_values])
  exact h
theorem leaf_4325_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4325.profileLo box_4325.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4325_ok
theorem branch_box_4325_nonnegative : ∀ j, 0 ≤ branch_box_4325.lower j ∧ 0 ≤ branch_box_4325.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4325, Box.profileLo, Box.profileHi, box_4325]
theorem leaf_4325_BranchSafe : CertificateConsequences.BranchSafe branch_box_4325 := by
  left; refine ⟨branch_box_4325_nonnegative, ?_⟩
  intro z hz; exact leaf_4325_sound hz

theorem leaf_4326_ok : checkAt 527 1000 box_4326 cert_4326 = true := by
  have h := List.all_eq_true.mp batch_86_15_ok accepted_4326 (by simp [batch_86_15_values])
  exact h
theorem leaf_4326_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4326.profileLo box_4326.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4326_ok
theorem branch_box_4326_nonnegative : ∀ j, 0 ≤ branch_box_4326.lower j ∧ 0 ≤ branch_box_4326.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4326, Box.profileLo, Box.profileHi, box_4326]
theorem leaf_4326_BranchSafe : CertificateConsequences.BranchSafe branch_box_4326 := by
  left; refine ⟨branch_box_4326_nonnegative, ?_⟩
  intro z hz; exact leaf_4326_sound hz

theorem leaf_4334_ok : checkAt 527 1000 box_4334 cert_4334 = true := by
  have h := List.all_eq_true.mp batch_86_16_ok accepted_4334 (by simp [batch_86_16_values])
  exact h
theorem leaf_4334_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4334.profileLo box_4334.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4334_ok
theorem branch_box_4334_nonnegative : ∀ j, 0 ≤ branch_box_4334.lower j ∧ 0 ≤ branch_box_4334.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4334, Box.profileLo, Box.profileHi, box_4334]
theorem leaf_4334_BranchSafe : CertificateConsequences.BranchSafe branch_box_4334 := by
  left; refine ⟨branch_box_4334_nonnegative, ?_⟩
  intro z hz; exact leaf_4334_sound hz

theorem leaf_4335_ok : checkAt 527 1000 box_4335 cert_4335 = true := by
  have h := List.all_eq_true.mp batch_86_17_ok accepted_4335 (by simp [batch_86_17_values])
  exact h
theorem leaf_4335_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4335.profileLo box_4335.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4335_ok
theorem branch_box_4335_nonnegative : ∀ j, 0 ≤ branch_box_4335.lower j ∧ 0 ≤ branch_box_4335.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4335, Box.profileLo, Box.profileHi, box_4335]
theorem leaf_4335_BranchSafe : CertificateConsequences.BranchSafe branch_box_4335 := by
  left; refine ⟨branch_box_4335_nonnegative, ?_⟩
  intro z hz; exact leaf_4335_sound hz

theorem leaf_4336_ok : checkAt 527 1000 box_4336 cert_4336 = true := by
  have h := List.all_eq_true.mp batch_86_18_ok accepted_4336 (by simp [batch_86_18_values])
  exact h
theorem leaf_4336_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4336.profileLo box_4336.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4336_ok
theorem branch_box_4336_nonnegative : ∀ j, 0 ≤ branch_box_4336.lower j ∧ 0 ≤ branch_box_4336.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4336, Box.profileLo, Box.profileHi, box_4336]
theorem leaf_4336_BranchSafe : CertificateConsequences.BranchSafe branch_box_4336 := by
  left; refine ⟨branch_box_4336_nonnegative, ?_⟩
  intro z hz; exact leaf_4336_sound hz

theorem leaf_4337_ok : checkAt 527 1000 box_4337 cert_4337 = true := by
  have h := List.all_eq_true.mp batch_86_19_ok accepted_4337 (by simp [batch_86_19_values])
  exact h
theorem leaf_4337_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4337.profileLo box_4337.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4337_ok
theorem branch_box_4337_nonnegative : ∀ j, 0 ≤ branch_box_4337.lower j ∧ 0 ≤ branch_box_4337.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4337, Box.profileLo, Box.profileHi, box_4337]
theorem leaf_4337_BranchSafe : CertificateConsequences.BranchSafe branch_box_4337 := by
  left; refine ⟨branch_box_4337_nonnegative, ?_⟩
  intro z hz; exact leaf_4337_sound hz

theorem leaf_4338_ok : checkAt 527 1000 box_4338 cert_4338 = true := by
  have h := List.all_eq_true.mp batch_86_20_ok accepted_4338 (by simp [batch_86_20_values])
  exact h
theorem leaf_4338_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4338.profileLo box_4338.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4338_ok
theorem branch_box_4338_nonnegative : ∀ j, 0 ≤ branch_box_4338.lower j ∧ 0 ≤ branch_box_4338.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4338, Box.profileLo, Box.profileHi, box_4338]
theorem leaf_4338_BranchSafe : CertificateConsequences.BranchSafe branch_box_4338 := by
  left; refine ⟨branch_box_4338_nonnegative, ?_⟩
  intro z hz; exact leaf_4338_sound hz

theorem leaf_4347_ok : checkAt 527 1000 box_4347 cert_4347 = true := by
  have h := List.all_eq_true.mp batch_86_21_ok accepted_4347 (by simp [batch_86_21_values])
  exact h
theorem leaf_4347_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4347.profileLo box_4347.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4347_ok
theorem branch_box_4347_nonnegative : ∀ j, 0 ≤ branch_box_4347.lower j ∧ 0 ≤ branch_box_4347.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4347, Box.profileLo, Box.profileHi, box_4347]
theorem leaf_4347_BranchSafe : CertificateConsequences.BranchSafe branch_box_4347 := by
  left; refine ⟨branch_box_4347_nonnegative, ?_⟩
  intro z hz; exact leaf_4347_sound hz

theorem leaf_4348_ok : checkAt 527 1000 box_4348 cert_4348 = true := by
  have h := List.all_eq_true.mp batch_86_22_ok accepted_4348 (by simp [batch_86_22_values])
  exact h
theorem leaf_4348_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4348.profileLo box_4348.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4348_ok
theorem branch_box_4348_nonnegative : ∀ j, 0 ≤ branch_box_4348.lower j ∧ 0 ≤ branch_box_4348.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4348, Box.profileLo, Box.profileHi, box_4348]
theorem leaf_4348_BranchSafe : CertificateConsequences.BranchSafe branch_box_4348 := by
  left; refine ⟨branch_box_4348_nonnegative, ?_⟩
  intro z hz; exact leaf_4348_sound hz

theorem leaf_4349_ok : checkAt 527 1000 box_4349 cert_4349 = true := by
  have h := List.all_eq_true.mp batch_86_23_ok accepted_4349 (by simp [batch_86_23_values])
  exact h
theorem leaf_4349_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4349.profileLo box_4349.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4349_ok
theorem branch_box_4349_nonnegative : ∀ j, 0 ≤ branch_box_4349.lower j ∧ 0 ≤ branch_box_4349.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4349, Box.profileLo, Box.profileHi, box_4349]
theorem leaf_4349_BranchSafe : CertificateConsequences.BranchSafe branch_box_4349 := by
  left; refine ⟨branch_box_4349_nonnegative, ?_⟩
  intro z hz; exact leaf_4349_sound hz

#print axioms batch_86_00_ok
#print axioms leaf_4301_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
