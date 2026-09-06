import PeaceableQueens.UpperBound.Generated.Even.CoreScaled86Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_86_00_values : List Bool := [accepted_4302]
theorem batch_86_00_ok : batch_86_00_values.all id = true := by decide

def batch_86_01_values : List Bool := [accepted_4304]
theorem batch_86_01_ok : batch_86_01_values.all id = true := by decide

def batch_86_02_values : List Bool := [accepted_4306]
theorem batch_86_02_ok : batch_86_02_values.all id = true := by decide

def batch_86_03_values : List Bool := [accepted_4308]
theorem batch_86_03_ok : batch_86_03_values.all id = true := by decide

def batch_86_04_values : List Bool := [accepted_4314]
theorem batch_86_04_ok : batch_86_04_values.all id = true := by decide

def batch_86_05_values : List Bool := [accepted_4316]
theorem batch_86_05_ok : batch_86_05_values.all id = true := by decide

def batch_86_06_values : List Bool := [accepted_4318]
theorem batch_86_06_ok : batch_86_06_values.all id = true := by decide

def batch_86_07_values : List Bool := [accepted_4320]
theorem batch_86_07_ok : batch_86_07_values.all id = true := by decide

def batch_86_08_values : List Bool := [accepted_4322]
theorem batch_86_08_ok : batch_86_08_values.all id = true := by decide

def batch_86_09_values : List Bool := [accepted_4325]
theorem batch_86_09_ok : batch_86_09_values.all id = true := by decide

def batch_86_10_values : List Bool := [accepted_4328]
theorem batch_86_10_ok : batch_86_10_values.all id = true := by decide

def batch_86_11_values : List Bool := [accepted_4330]
theorem batch_86_11_ok : batch_86_11_values.all id = true := by decide

def batch_86_12_values : List Bool := [accepted_4332]
theorem batch_86_12_ok : batch_86_12_values.all id = true := by decide

def batch_86_13_values : List Bool := [accepted_4334]
theorem batch_86_13_ok : batch_86_13_values.all id = true := by decide

def batch_86_14_values : List Bool := [accepted_4336]
theorem batch_86_14_ok : batch_86_14_values.all id = true := by decide

def batch_86_15_values : List Bool := [accepted_4338]
theorem batch_86_15_ok : batch_86_15_values.all id = true := by decide

def batch_86_16_values : List Bool := [accepted_4340]
theorem batch_86_16_ok : batch_86_16_values.all id = true := by decide

def batch_86_17_values : List Bool := [accepted_4343]
theorem batch_86_17_ok : batch_86_17_values.all id = true := by decide

def batch_86_18_values : List Bool := [accepted_4346]
theorem batch_86_18_ok : batch_86_18_values.all id = true := by decide

def batch_86_19_values : List Bool := [accepted_4348]
theorem batch_86_19_ok : batch_86_19_values.all id = true := by decide

theorem leaf_4302_ok : checkAt 527 1000 box_4302 cert_4302 = true := by
  have h := List.all_eq_true.mp batch_86_00_ok accepted_4302 (by simp [batch_86_00_values])
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

theorem leaf_4304_ok : checkAt 527 1000 box_4304 cert_4304 = true := by
  have h := List.all_eq_true.mp batch_86_01_ok accepted_4304 (by simp [batch_86_01_values])
  exact h
theorem leaf_4304_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4304.profileLo box_4304.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4304_ok
theorem branch_box_4304_nonnegative : ∀ j, 0 ≤ branch_box_4304.lower j ∧ 0 ≤ branch_box_4304.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4304, Box.profileLo, Box.profileHi, box_4304]
theorem leaf_4304_BranchSafe : CertificateConsequences.BranchSafe branch_box_4304 := by
  left; refine ⟨branch_box_4304_nonnegative, ?_⟩
  intro z hz; exact leaf_4304_sound hz

theorem leaf_4306_ok : checkAt 527 1000 box_4306 cert_4306 = true := by
  have h := List.all_eq_true.mp batch_86_02_ok accepted_4306 (by simp [batch_86_02_values])
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

theorem leaf_4308_ok : checkAt 527 1000 box_4308 cert_4308 = true := by
  have h := List.all_eq_true.mp batch_86_03_ok accepted_4308 (by simp [batch_86_03_values])
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

theorem leaf_4314_ok : checkAt 527 1000 box_4314 cert_4314 = true := by
  have h := List.all_eq_true.mp batch_86_04_ok accepted_4314 (by simp [batch_86_04_values])
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

theorem leaf_4316_ok : checkAt 527 1000 box_4316 cert_4316 = true := by
  have h := List.all_eq_true.mp batch_86_05_ok accepted_4316 (by simp [batch_86_05_values])
  exact h
theorem leaf_4316_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4316.profileLo box_4316.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4316_ok
theorem branch_box_4316_nonnegative : ∀ j, 0 ≤ branch_box_4316.lower j ∧ 0 ≤ branch_box_4316.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4316, Box.profileLo, Box.profileHi, box_4316]
theorem leaf_4316_BranchSafe : CertificateConsequences.BranchSafe branch_box_4316 := by
  left; refine ⟨branch_box_4316_nonnegative, ?_⟩
  intro z hz; exact leaf_4316_sound hz

theorem leaf_4318_ok : checkAt 527 1000 box_4318 cert_4318 = true := by
  have h := List.all_eq_true.mp batch_86_06_ok accepted_4318 (by simp [batch_86_06_values])
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

theorem leaf_4320_ok : checkAt 527 1000 box_4320 cert_4320 = true := by
  have h := List.all_eq_true.mp batch_86_07_ok accepted_4320 (by simp [batch_86_07_values])
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

theorem leaf_4322_ok : checkAt 527 1000 box_4322 cert_4322 = true := by
  have h := List.all_eq_true.mp batch_86_08_ok accepted_4322 (by simp [batch_86_08_values])
  exact h
theorem leaf_4322_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4322.profileLo box_4322.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4322_ok
theorem branch_box_4322_nonnegative : ∀ j, 0 ≤ branch_box_4322.lower j ∧ 0 ≤ branch_box_4322.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4322, Box.profileLo, Box.profileHi, box_4322]
theorem leaf_4322_BranchSafe : CertificateConsequences.BranchSafe branch_box_4322 := by
  left; refine ⟨branch_box_4322_nonnegative, ?_⟩
  intro z hz; exact leaf_4322_sound hz

theorem leaf_4325_ok : checkAt 527 1000 box_4325 cert_4325 = true := by
  have h := List.all_eq_true.mp batch_86_09_ok accepted_4325 (by simp [batch_86_09_values])
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

theorem leaf_4328_ok : checkAt 527 1000 box_4328 cert_4328 = true := by
  have h := List.all_eq_true.mp batch_86_10_ok accepted_4328 (by simp [batch_86_10_values])
  exact h
theorem leaf_4328_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4328.profileLo box_4328.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4328_ok
theorem branch_box_4328_nonnegative : ∀ j, 0 ≤ branch_box_4328.lower j ∧ 0 ≤ branch_box_4328.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4328, Box.profileLo, Box.profileHi, box_4328]
theorem leaf_4328_BranchSafe : CertificateConsequences.BranchSafe branch_box_4328 := by
  left; refine ⟨branch_box_4328_nonnegative, ?_⟩
  intro z hz; exact leaf_4328_sound hz

theorem leaf_4330_ok : checkAt 527 1000 box_4330 cert_4330 = true := by
  have h := List.all_eq_true.mp batch_86_11_ok accepted_4330 (by simp [batch_86_11_values])
  exact h
theorem leaf_4330_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4330.profileLo box_4330.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4330_ok
theorem branch_box_4330_nonnegative : ∀ j, 0 ≤ branch_box_4330.lower j ∧ 0 ≤ branch_box_4330.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4330, Box.profileLo, Box.profileHi, box_4330]
theorem leaf_4330_BranchSafe : CertificateConsequences.BranchSafe branch_box_4330 := by
  left; refine ⟨branch_box_4330_nonnegative, ?_⟩
  intro z hz; exact leaf_4330_sound hz

theorem leaf_4332_ok : checkAt 527 1000 box_4332 cert_4332 = true := by
  have h := List.all_eq_true.mp batch_86_12_ok accepted_4332 (by simp [batch_86_12_values])
  exact h
theorem leaf_4332_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4332.profileLo box_4332.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4332_ok
theorem branch_box_4332_nonnegative : ∀ j, 0 ≤ branch_box_4332.lower j ∧ 0 ≤ branch_box_4332.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4332, Box.profileLo, Box.profileHi, box_4332]
theorem leaf_4332_BranchSafe : CertificateConsequences.BranchSafe branch_box_4332 := by
  left; refine ⟨branch_box_4332_nonnegative, ?_⟩
  intro z hz; exact leaf_4332_sound hz

theorem leaf_4334_ok : checkAt 527 1000 box_4334 cert_4334 = true := by
  have h := List.all_eq_true.mp batch_86_13_ok accepted_4334 (by simp [batch_86_13_values])
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

theorem leaf_4336_ok : checkAt 527 1000 box_4336 cert_4336 = true := by
  have h := List.all_eq_true.mp batch_86_14_ok accepted_4336 (by simp [batch_86_14_values])
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

theorem leaf_4338_ok : checkAt 527 1000 box_4338 cert_4338 = true := by
  have h := List.all_eq_true.mp batch_86_15_ok accepted_4338 (by simp [batch_86_15_values])
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

theorem leaf_4340_ok : checkAt 527 1000 box_4340 cert_4340 = true := by
  have h := List.all_eq_true.mp batch_86_16_ok accepted_4340 (by simp [batch_86_16_values])
  exact h
theorem leaf_4340_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4340.profileLo box_4340.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4340_ok
theorem branch_box_4340_nonnegative : ∀ j, 0 ≤ branch_box_4340.lower j ∧ 0 ≤ branch_box_4340.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4340, Box.profileLo, Box.profileHi, box_4340]
theorem leaf_4340_BranchSafe : CertificateConsequences.BranchSafe branch_box_4340 := by
  left; refine ⟨branch_box_4340_nonnegative, ?_⟩
  intro z hz; exact leaf_4340_sound hz

theorem leaf_4343_ok : checkAt 527 1000 box_4343 cert_4343 = true := by
  have h := List.all_eq_true.mp batch_86_17_ok accepted_4343 (by simp [batch_86_17_values])
  exact h
theorem leaf_4343_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4343.profileLo box_4343.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4343_ok
theorem branch_box_4343_nonnegative : ∀ j, 0 ≤ branch_box_4343.lower j ∧ 0 ≤ branch_box_4343.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4343, Box.profileLo, Box.profileHi, box_4343]
theorem leaf_4343_BranchSafe : CertificateConsequences.BranchSafe branch_box_4343 := by
  left; refine ⟨branch_box_4343_nonnegative, ?_⟩
  intro z hz; exact leaf_4343_sound hz

theorem leaf_4346_ok : checkAt 527 1000 box_4346 cert_4346 = true := by
  have h := List.all_eq_true.mp batch_86_18_ok accepted_4346 (by simp [batch_86_18_values])
  exact h
theorem leaf_4346_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4346.profileLo box_4346.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4346_ok
theorem branch_box_4346_nonnegative : ∀ j, 0 ≤ branch_box_4346.lower j ∧ 0 ≤ branch_box_4346.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4346, Box.profileLo, Box.profileHi, box_4346]
theorem leaf_4346_BranchSafe : CertificateConsequences.BranchSafe branch_box_4346 := by
  left; refine ⟨branch_box_4346_nonnegative, ?_⟩
  intro z hz; exact leaf_4346_sound hz

theorem leaf_4348_ok : checkAt 527 1000 box_4348 cert_4348 = true := by
  have h := List.all_eq_true.mp batch_86_19_ok accepted_4348 (by simp [batch_86_19_values])
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

#print axioms batch_86_00_ok
#print axioms leaf_4302_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
