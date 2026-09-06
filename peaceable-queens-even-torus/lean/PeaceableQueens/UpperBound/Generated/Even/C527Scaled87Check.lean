import PeaceableQueens.UpperBound.Generated.Even.C527Scaled87Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_87_00_values : List Bool := [accepted_4350]
theorem batch_87_00_ok : batch_87_00_values.all id = true := by decide

def batch_87_01_values : List Bool := [accepted_4351]
theorem batch_87_01_ok : batch_87_01_values.all id = true := by decide

def batch_87_02_values : List Bool := [accepted_4353]
theorem batch_87_02_ok : batch_87_02_values.all id = true := by decide

def batch_87_03_values : List Bool := [accepted_4354]
theorem batch_87_03_ok : batch_87_03_values.all id = true := by decide

def batch_87_04_values : List Bool := [accepted_4359]
theorem batch_87_04_ok : batch_87_04_values.all id = true := by decide

def batch_87_05_values : List Bool := [accepted_4360]
theorem batch_87_05_ok : batch_87_05_values.all id = true := by decide

def batch_87_06_values : List Bool := [accepted_4361]
theorem batch_87_06_ok : batch_87_06_values.all id = true := by decide

def batch_87_07_values : List Bool := [accepted_4363]
theorem batch_87_07_ok : batch_87_07_values.all id = true := by decide

def batch_87_08_values : List Bool := [accepted_4364]
theorem batch_87_08_ok : batch_87_08_values.all id = true := by decide

def batch_87_09_values : List Bool := [accepted_4365]
theorem batch_87_09_ok : batch_87_09_values.all id = true := by decide

def batch_87_10_values : List Bool := [accepted_4368]
theorem batch_87_10_ok : batch_87_10_values.all id = true := by decide

def batch_87_11_values : List Bool := [accepted_4369]
theorem batch_87_11_ok : batch_87_11_values.all id = true := by decide

def batch_87_12_values : List Bool := [accepted_4370]
theorem batch_87_12_ok : batch_87_12_values.all id = true := by decide

def batch_87_13_values : List Bool := [accepted_4377]
theorem batch_87_13_ok : batch_87_13_values.all id = true := by decide

def batch_87_14_values : List Bool := [accepted_4378]
theorem batch_87_14_ok : batch_87_14_values.all id = true := by decide

def batch_87_15_values : List Bool := [accepted_4382]
theorem batch_87_15_ok : batch_87_15_values.all id = true := by decide

def batch_87_16_values : List Bool := [accepted_4383]
theorem batch_87_16_ok : batch_87_16_values.all id = true := by decide

def batch_87_17_values : List Bool := [accepted_4384]
theorem batch_87_17_ok : batch_87_17_values.all id = true := by decide

def batch_87_18_values : List Bool := [accepted_4385]
theorem batch_87_18_ok : batch_87_18_values.all id = true := by decide

def batch_87_19_values : List Bool := [accepted_4386]
theorem batch_87_19_ok : batch_87_19_values.all id = true := by decide

def batch_87_20_values : List Bool := [accepted_4387]
theorem batch_87_20_ok : batch_87_20_values.all id = true := by decide

def batch_87_21_values : List Bool := [accepted_4389]
theorem batch_87_21_ok : batch_87_21_values.all id = true := by decide

def batch_87_22_values : List Bool := [accepted_4391]
theorem batch_87_22_ok : batch_87_22_values.all id = true := by decide

def batch_87_23_values : List Bool := [accepted_4392]
theorem batch_87_23_ok : batch_87_23_values.all id = true := by decide

def batch_87_24_values : List Bool := [accepted_4399]
theorem batch_87_24_ok : batch_87_24_values.all id = true := by decide

theorem leaf_4350_ok : checkAt 527 1000 box_4350 cert_4350 = true := by
  have h := List.all_eq_true.mp batch_87_00_ok accepted_4350 (by simp [batch_87_00_values])
  exact h
theorem leaf_4350_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4350.profileLo box_4350.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4350_ok
theorem branch_box_4350_nonnegative : ∀ j, 0 ≤ branch_box_4350.lower j ∧ 0 ≤ branch_box_4350.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4350, Box.profileLo, Box.profileHi, box_4350]
theorem leaf_4350_BranchSafe : CertificateConsequences.BranchSafe branch_box_4350 := by
  left; refine ⟨branch_box_4350_nonnegative, ?_⟩
  intro z hz; exact leaf_4350_sound hz

theorem leaf_4351_ok : checkAt 527 1000 box_4351 cert_4351 = true := by
  have h := List.all_eq_true.mp batch_87_01_ok accepted_4351 (by simp [batch_87_01_values])
  exact h
theorem leaf_4351_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4351.profileLo box_4351.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4351_ok
theorem branch_box_4351_nonnegative : ∀ j, 0 ≤ branch_box_4351.lower j ∧ 0 ≤ branch_box_4351.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4351, Box.profileLo, Box.profileHi, box_4351]
theorem leaf_4351_BranchSafe : CertificateConsequences.BranchSafe branch_box_4351 := by
  left; refine ⟨branch_box_4351_nonnegative, ?_⟩
  intro z hz; exact leaf_4351_sound hz

theorem leaf_4353_ok : checkAt 527 1000 box_4353 cert_4353 = true := by
  have h := List.all_eq_true.mp batch_87_02_ok accepted_4353 (by simp [batch_87_02_values])
  exact h
theorem leaf_4353_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4353.profileLo box_4353.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4353_ok
theorem branch_box_4353_nonnegative : ∀ j, 0 ≤ branch_box_4353.lower j ∧ 0 ≤ branch_box_4353.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4353, Box.profileLo, Box.profileHi, box_4353]
theorem leaf_4353_BranchSafe : CertificateConsequences.BranchSafe branch_box_4353 := by
  left; refine ⟨branch_box_4353_nonnegative, ?_⟩
  intro z hz; exact leaf_4353_sound hz

theorem leaf_4354_ok : checkAt 527 1000 box_4354 cert_4354 = true := by
  have h := List.all_eq_true.mp batch_87_03_ok accepted_4354 (by simp [batch_87_03_values])
  exact h
theorem leaf_4354_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4354.profileLo box_4354.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4354_ok
theorem branch_box_4354_nonnegative : ∀ j, 0 ≤ branch_box_4354.lower j ∧ 0 ≤ branch_box_4354.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4354, Box.profileLo, Box.profileHi, box_4354]
theorem leaf_4354_BranchSafe : CertificateConsequences.BranchSafe branch_box_4354 := by
  left; refine ⟨branch_box_4354_nonnegative, ?_⟩
  intro z hz; exact leaf_4354_sound hz

theorem leaf_4359_ok : checkAt 527 1000 box_4359 cert_4359 = true := by
  have h := List.all_eq_true.mp batch_87_04_ok accepted_4359 (by simp [batch_87_04_values])
  exact h
theorem leaf_4359_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4359.profileLo box_4359.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4359_ok
theorem branch_box_4359_nonnegative : ∀ j, 0 ≤ branch_box_4359.lower j ∧ 0 ≤ branch_box_4359.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4359, Box.profileLo, Box.profileHi, box_4359]
theorem leaf_4359_BranchSafe : CertificateConsequences.BranchSafe branch_box_4359 := by
  left; refine ⟨branch_box_4359_nonnegative, ?_⟩
  intro z hz; exact leaf_4359_sound hz

theorem leaf_4360_ok : checkAt 527 1000 box_4360 cert_4360 = true := by
  have h := List.all_eq_true.mp batch_87_05_ok accepted_4360 (by simp [batch_87_05_values])
  exact h
theorem leaf_4360_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4360.profileLo box_4360.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4360_ok
theorem branch_box_4360_nonnegative : ∀ j, 0 ≤ branch_box_4360.lower j ∧ 0 ≤ branch_box_4360.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4360, Box.profileLo, Box.profileHi, box_4360]
theorem leaf_4360_BranchSafe : CertificateConsequences.BranchSafe branch_box_4360 := by
  left; refine ⟨branch_box_4360_nonnegative, ?_⟩
  intro z hz; exact leaf_4360_sound hz

theorem leaf_4361_ok : checkAt 527 1000 box_4361 cert_4361 = true := by
  have h := List.all_eq_true.mp batch_87_06_ok accepted_4361 (by simp [batch_87_06_values])
  exact h
theorem leaf_4361_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4361.profileLo box_4361.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4361_ok
theorem branch_box_4361_nonnegative : ∀ j, 0 ≤ branch_box_4361.lower j ∧ 0 ≤ branch_box_4361.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4361, Box.profileLo, Box.profileHi, box_4361]
theorem leaf_4361_BranchSafe : CertificateConsequences.BranchSafe branch_box_4361 := by
  left; refine ⟨branch_box_4361_nonnegative, ?_⟩
  intro z hz; exact leaf_4361_sound hz

theorem leaf_4363_ok : checkAt 527 1000 box_4363 cert_4363 = true := by
  have h := List.all_eq_true.mp batch_87_07_ok accepted_4363 (by simp [batch_87_07_values])
  exact h
theorem leaf_4363_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4363.profileLo box_4363.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4363_ok
theorem branch_box_4363_nonnegative : ∀ j, 0 ≤ branch_box_4363.lower j ∧ 0 ≤ branch_box_4363.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4363, Box.profileLo, Box.profileHi, box_4363]
theorem leaf_4363_BranchSafe : CertificateConsequences.BranchSafe branch_box_4363 := by
  left; refine ⟨branch_box_4363_nonnegative, ?_⟩
  intro z hz; exact leaf_4363_sound hz

theorem leaf_4364_ok : checkAt 527 1000 box_4364 cert_4364 = true := by
  have h := List.all_eq_true.mp batch_87_08_ok accepted_4364 (by simp [batch_87_08_values])
  exact h
theorem leaf_4364_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4364.profileLo box_4364.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4364_ok
theorem branch_box_4364_nonnegative : ∀ j, 0 ≤ branch_box_4364.lower j ∧ 0 ≤ branch_box_4364.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4364, Box.profileLo, Box.profileHi, box_4364]
theorem leaf_4364_BranchSafe : CertificateConsequences.BranchSafe branch_box_4364 := by
  left; refine ⟨branch_box_4364_nonnegative, ?_⟩
  intro z hz; exact leaf_4364_sound hz

theorem leaf_4365_ok : checkAt 527 1000 box_4365 cert_4365 = true := by
  have h := List.all_eq_true.mp batch_87_09_ok accepted_4365 (by simp [batch_87_09_values])
  exact h
theorem leaf_4365_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4365.profileLo box_4365.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4365_ok
theorem branch_box_4365_nonnegative : ∀ j, 0 ≤ branch_box_4365.lower j ∧ 0 ≤ branch_box_4365.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4365, Box.profileLo, Box.profileHi, box_4365]
theorem leaf_4365_BranchSafe : CertificateConsequences.BranchSafe branch_box_4365 := by
  left; refine ⟨branch_box_4365_nonnegative, ?_⟩
  intro z hz; exact leaf_4365_sound hz

theorem leaf_4368_ok : checkAt 527 1000 box_4368 cert_4368 = true := by
  have h := List.all_eq_true.mp batch_87_10_ok accepted_4368 (by simp [batch_87_10_values])
  exact h
theorem leaf_4368_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4368.profileLo box_4368.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4368_ok
theorem branch_box_4368_nonnegative : ∀ j, 0 ≤ branch_box_4368.lower j ∧ 0 ≤ branch_box_4368.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4368, Box.profileLo, Box.profileHi, box_4368]
theorem leaf_4368_BranchSafe : CertificateConsequences.BranchSafe branch_box_4368 := by
  left; refine ⟨branch_box_4368_nonnegative, ?_⟩
  intro z hz; exact leaf_4368_sound hz

theorem leaf_4369_ok : checkAt 527 1000 box_4369 cert_4369 = true := by
  have h := List.all_eq_true.mp batch_87_11_ok accepted_4369 (by simp [batch_87_11_values])
  exact h
theorem leaf_4369_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4369.profileLo box_4369.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4369_ok
theorem branch_box_4369_nonnegative : ∀ j, 0 ≤ branch_box_4369.lower j ∧ 0 ≤ branch_box_4369.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4369, Box.profileLo, Box.profileHi, box_4369]
theorem leaf_4369_BranchSafe : CertificateConsequences.BranchSafe branch_box_4369 := by
  left; refine ⟨branch_box_4369_nonnegative, ?_⟩
  intro z hz; exact leaf_4369_sound hz

theorem leaf_4370_ok : checkAt 527 1000 box_4370 cert_4370 = true := by
  have h := List.all_eq_true.mp batch_87_12_ok accepted_4370 (by simp [batch_87_12_values])
  exact h
theorem leaf_4370_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4370.profileLo box_4370.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4370_ok
theorem branch_box_4370_nonnegative : ∀ j, 0 ≤ branch_box_4370.lower j ∧ 0 ≤ branch_box_4370.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4370, Box.profileLo, Box.profileHi, box_4370]
theorem leaf_4370_BranchSafe : CertificateConsequences.BranchSafe branch_box_4370 := by
  left; refine ⟨branch_box_4370_nonnegative, ?_⟩
  intro z hz; exact leaf_4370_sound hz

theorem leaf_4377_ok : checkAt 527 1000 box_4377 cert_4377 = true := by
  have h := List.all_eq_true.mp batch_87_13_ok accepted_4377 (by simp [batch_87_13_values])
  exact h
theorem leaf_4377_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4377.profileLo box_4377.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4377_ok
theorem branch_box_4377_nonnegative : ∀ j, 0 ≤ branch_box_4377.lower j ∧ 0 ≤ branch_box_4377.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4377, Box.profileLo, Box.profileHi, box_4377]
theorem leaf_4377_BranchSafe : CertificateConsequences.BranchSafe branch_box_4377 := by
  left; refine ⟨branch_box_4377_nonnegative, ?_⟩
  intro z hz; exact leaf_4377_sound hz

theorem leaf_4378_ok : checkAt 527 1000 box_4378 cert_4378 = true := by
  have h := List.all_eq_true.mp batch_87_14_ok accepted_4378 (by simp [batch_87_14_values])
  exact h
theorem leaf_4378_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4378.profileLo box_4378.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4378_ok
theorem branch_box_4378_nonnegative : ∀ j, 0 ≤ branch_box_4378.lower j ∧ 0 ≤ branch_box_4378.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4378, Box.profileLo, Box.profileHi, box_4378]
theorem leaf_4378_BranchSafe : CertificateConsequences.BranchSafe branch_box_4378 := by
  left; refine ⟨branch_box_4378_nonnegative, ?_⟩
  intro z hz; exact leaf_4378_sound hz

theorem leaf_4382_ok : checkAt 527 1000 box_4382 cert_4382 = true := by
  have h := List.all_eq_true.mp batch_87_15_ok accepted_4382 (by simp [batch_87_15_values])
  exact h
theorem leaf_4382_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4382.profileLo box_4382.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4382_ok
theorem branch_box_4382_nonnegative : ∀ j, 0 ≤ branch_box_4382.lower j ∧ 0 ≤ branch_box_4382.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4382, Box.profileLo, Box.profileHi, box_4382]
theorem leaf_4382_BranchSafe : CertificateConsequences.BranchSafe branch_box_4382 := by
  left; refine ⟨branch_box_4382_nonnegative, ?_⟩
  intro z hz; exact leaf_4382_sound hz

theorem leaf_4383_ok : checkAt 527 1000 box_4383 cert_4383 = true := by
  have h := List.all_eq_true.mp batch_87_16_ok accepted_4383 (by simp [batch_87_16_values])
  exact h
theorem leaf_4383_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4383.profileLo box_4383.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4383_ok
theorem branch_box_4383_nonnegative : ∀ j, 0 ≤ branch_box_4383.lower j ∧ 0 ≤ branch_box_4383.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4383, Box.profileLo, Box.profileHi, box_4383]
theorem leaf_4383_BranchSafe : CertificateConsequences.BranchSafe branch_box_4383 := by
  left; refine ⟨branch_box_4383_nonnegative, ?_⟩
  intro z hz; exact leaf_4383_sound hz

theorem leaf_4384_ok : checkAt 527 1000 box_4384 cert_4384 = true := by
  have h := List.all_eq_true.mp batch_87_17_ok accepted_4384 (by simp [batch_87_17_values])
  exact h
theorem leaf_4384_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4384.profileLo box_4384.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4384_ok
theorem branch_box_4384_nonnegative : ∀ j, 0 ≤ branch_box_4384.lower j ∧ 0 ≤ branch_box_4384.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4384, Box.profileLo, Box.profileHi, box_4384]
theorem leaf_4384_BranchSafe : CertificateConsequences.BranchSafe branch_box_4384 := by
  left; refine ⟨branch_box_4384_nonnegative, ?_⟩
  intro z hz; exact leaf_4384_sound hz

theorem leaf_4385_ok : checkAt 527 1000 box_4385 cert_4385 = true := by
  have h := List.all_eq_true.mp batch_87_18_ok accepted_4385 (by simp [batch_87_18_values])
  exact h
theorem leaf_4385_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4385.profileLo box_4385.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4385_ok
theorem branch_box_4385_nonnegative : ∀ j, 0 ≤ branch_box_4385.lower j ∧ 0 ≤ branch_box_4385.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4385, Box.profileLo, Box.profileHi, box_4385]
theorem leaf_4385_BranchSafe : CertificateConsequences.BranchSafe branch_box_4385 := by
  left; refine ⟨branch_box_4385_nonnegative, ?_⟩
  intro z hz; exact leaf_4385_sound hz

theorem leaf_4386_ok : checkAt 527 1000 box_4386 cert_4386 = true := by
  have h := List.all_eq_true.mp batch_87_19_ok accepted_4386 (by simp [batch_87_19_values])
  exact h
theorem leaf_4386_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4386.profileLo box_4386.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4386_ok
theorem branch_box_4386_nonnegative : ∀ j, 0 ≤ branch_box_4386.lower j ∧ 0 ≤ branch_box_4386.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4386, Box.profileLo, Box.profileHi, box_4386]
theorem leaf_4386_BranchSafe : CertificateConsequences.BranchSafe branch_box_4386 := by
  left; refine ⟨branch_box_4386_nonnegative, ?_⟩
  intro z hz; exact leaf_4386_sound hz

theorem leaf_4387_ok : checkAt 527 1000 box_4387 cert_4387 = true := by
  have h := List.all_eq_true.mp batch_87_20_ok accepted_4387 (by simp [batch_87_20_values])
  exact h
theorem leaf_4387_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4387.profileLo box_4387.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4387_ok
theorem branch_box_4387_nonnegative : ∀ j, 0 ≤ branch_box_4387.lower j ∧ 0 ≤ branch_box_4387.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4387, Box.profileLo, Box.profileHi, box_4387]
theorem leaf_4387_BranchSafe : CertificateConsequences.BranchSafe branch_box_4387 := by
  left; refine ⟨branch_box_4387_nonnegative, ?_⟩
  intro z hz; exact leaf_4387_sound hz

theorem leaf_4389_ok : checkAt 527 1000 box_4389 cert_4389 = true := by
  have h := List.all_eq_true.mp batch_87_21_ok accepted_4389 (by simp [batch_87_21_values])
  exact h
theorem leaf_4389_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4389.profileLo box_4389.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4389_ok
theorem branch_box_4389_nonnegative : ∀ j, 0 ≤ branch_box_4389.lower j ∧ 0 ≤ branch_box_4389.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4389, Box.profileLo, Box.profileHi, box_4389]
theorem leaf_4389_BranchSafe : CertificateConsequences.BranchSafe branch_box_4389 := by
  left; refine ⟨branch_box_4389_nonnegative, ?_⟩
  intro z hz; exact leaf_4389_sound hz

theorem leaf_4391_ok : checkAt 527 1000 box_4391 cert_4391 = true := by
  have h := List.all_eq_true.mp batch_87_22_ok accepted_4391 (by simp [batch_87_22_values])
  exact h
theorem leaf_4391_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4391.profileLo box_4391.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4391_ok
theorem branch_box_4391_nonnegative : ∀ j, 0 ≤ branch_box_4391.lower j ∧ 0 ≤ branch_box_4391.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4391, Box.profileLo, Box.profileHi, box_4391]
theorem leaf_4391_BranchSafe : CertificateConsequences.BranchSafe branch_box_4391 := by
  left; refine ⟨branch_box_4391_nonnegative, ?_⟩
  intro z hz; exact leaf_4391_sound hz

theorem leaf_4392_ok : checkAt 527 1000 box_4392 cert_4392 = true := by
  have h := List.all_eq_true.mp batch_87_23_ok accepted_4392 (by simp [batch_87_23_values])
  exact h
theorem leaf_4392_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4392.profileLo box_4392.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4392_ok
theorem branch_box_4392_nonnegative : ∀ j, 0 ≤ branch_box_4392.lower j ∧ 0 ≤ branch_box_4392.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4392, Box.profileLo, Box.profileHi, box_4392]
theorem leaf_4392_BranchSafe : CertificateConsequences.BranchSafe branch_box_4392 := by
  left; refine ⟨branch_box_4392_nonnegative, ?_⟩
  intro z hz; exact leaf_4392_sound hz

theorem leaf_4399_ok : checkAt 527 1000 box_4399 cert_4399 = true := by
  have h := List.all_eq_true.mp batch_87_24_ok accepted_4399 (by simp [batch_87_24_values])
  exact h
theorem leaf_4399_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4399.profileLo box_4399.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4399_ok
theorem branch_box_4399_nonnegative : ∀ j, 0 ≤ branch_box_4399.lower j ∧ 0 ≤ branch_box_4399.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4399, Box.profileLo, Box.profileHi, box_4399]
theorem leaf_4399_BranchSafe : CertificateConsequences.BranchSafe branch_box_4399 := by
  left; refine ⟨branch_box_4399_nonnegative, ?_⟩
  intro z hz; exact leaf_4399_sound hz

#print axioms batch_87_00_ok
#print axioms leaf_4350_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
