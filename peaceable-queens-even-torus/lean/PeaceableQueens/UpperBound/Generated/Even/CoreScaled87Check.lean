import PeaceableQueens.UpperBound.Generated.Even.CoreScaled87Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_87_00_values : List Bool := [accepted_4350]
theorem batch_87_00_ok : batch_87_00_values.all id = true := by decide

def batch_87_01_values : List Bool := [accepted_4352]
theorem batch_87_01_ok : batch_87_01_values.all id = true := by decide

def batch_87_02_values : List Bool := [accepted_4354]
theorem batch_87_02_ok : batch_87_02_values.all id = true := by decide

def batch_87_03_values : List Bool := [accepted_4356]
theorem batch_87_03_ok : batch_87_03_values.all id = true := by decide

def batch_87_04_values : List Bool := [accepted_4357]
theorem batch_87_04_ok : batch_87_04_values.all id = true := by decide

def batch_87_05_values : List Bool := [accepted_4359]
theorem batch_87_05_ok : batch_87_05_values.all id = true := by decide

def batch_87_06_values : List Bool := [accepted_4362]
theorem batch_87_06_ok : batch_87_06_values.all id = true := by decide

def batch_87_07_values : List Bool := [accepted_4364]
theorem batch_87_07_ok : batch_87_07_values.all id = true := by decide

def batch_87_08_values : List Bool := [accepted_4366]
theorem batch_87_08_ok : batch_87_08_values.all id = true := by decide

def batch_87_09_values : List Bool := [accepted_4368]
theorem batch_87_09_ok : batch_87_09_values.all id = true := by decide

def batch_87_10_values : List Bool := [accepted_4370]
theorem batch_87_10_ok : batch_87_10_values.all id = true := by decide

def batch_87_11_values : List Bool := [accepted_4371]
theorem batch_87_11_ok : batch_87_11_values.all id = true := by decide

def batch_87_12_values : List Bool := [accepted_4378]
theorem batch_87_12_ok : batch_87_12_values.all id = true := by decide

def batch_87_13_values : List Bool := [accepted_4380]
theorem batch_87_13_ok : batch_87_13_values.all id = true := by decide

def batch_87_14_values : List Bool := [accepted_4382]
theorem batch_87_14_ok : batch_87_14_values.all id = true := by decide

def batch_87_15_values : List Bool := [accepted_4384]
theorem batch_87_15_ok : batch_87_15_values.all id = true := by decide

def batch_87_16_values : List Bool := [accepted_4386]
theorem batch_87_16_ok : batch_87_16_values.all id = true := by decide

def batch_87_17_values : List Bool := [accepted_4388]
theorem batch_87_17_ok : batch_87_17_values.all id = true := by decide

def batch_87_18_values : List Bool := [accepted_4390]
theorem batch_87_18_ok : batch_87_18_values.all id = true := by decide

def batch_87_19_values : List Bool := [accepted_4392]
theorem batch_87_19_ok : batch_87_19_values.all id = true := by decide

def batch_87_20_values : List Bool := [accepted_4393]
theorem batch_87_20_ok : batch_87_20_values.all id = true := by decide

def batch_87_21_values : List Bool := [accepted_4395]
theorem batch_87_21_ok : batch_87_21_values.all id = true := by decide

def batch_87_22_values : List Bool := [accepted_4398]
theorem batch_87_22_ok : batch_87_22_values.all id = true := by decide

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

theorem leaf_4352_ok : checkAt 527 1000 box_4352 cert_4352 = true := by
  have h := List.all_eq_true.mp batch_87_01_ok accepted_4352 (by simp [batch_87_01_values])
  exact h
theorem leaf_4352_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4352.profileLo box_4352.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4352_ok
theorem branch_box_4352_nonnegative : ∀ j, 0 ≤ branch_box_4352.lower j ∧ 0 ≤ branch_box_4352.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4352, Box.profileLo, Box.profileHi, box_4352]
theorem leaf_4352_BranchSafe : CertificateConsequences.BranchSafe branch_box_4352 := by
  left; refine ⟨branch_box_4352_nonnegative, ?_⟩
  intro z hz; exact leaf_4352_sound hz

theorem leaf_4354_ok : checkAt 527 1000 box_4354 cert_4354 = true := by
  have h := List.all_eq_true.mp batch_87_02_ok accepted_4354 (by simp [batch_87_02_values])
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

theorem leaf_4356_ok : checkAt 527 1000 box_4356 cert_4356 = true := by
  have h := List.all_eq_true.mp batch_87_03_ok accepted_4356 (by simp [batch_87_03_values])
  exact h
theorem leaf_4356_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4356.profileLo box_4356.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4356_ok
theorem branch_box_4356_nonnegative : ∀ j, 0 ≤ branch_box_4356.lower j ∧ 0 ≤ branch_box_4356.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4356, Box.profileLo, Box.profileHi, box_4356]
theorem leaf_4356_BranchSafe : CertificateConsequences.BranchSafe branch_box_4356 := by
  left; refine ⟨branch_box_4356_nonnegative, ?_⟩
  intro z hz; exact leaf_4356_sound hz

theorem leaf_4357_ok : checkAt 527 1000 box_4357 cert_4357 = true := by
  have h := List.all_eq_true.mp batch_87_04_ok accepted_4357 (by simp [batch_87_04_values])
  exact h
theorem leaf_4357_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4357.profileLo box_4357.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4357_ok
theorem branch_box_4357_nonnegative : ∀ j, 0 ≤ branch_box_4357.lower j ∧ 0 ≤ branch_box_4357.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4357, Box.profileLo, Box.profileHi, box_4357]
theorem leaf_4357_BranchSafe : CertificateConsequences.BranchSafe branch_box_4357 := by
  left; refine ⟨branch_box_4357_nonnegative, ?_⟩
  intro z hz; exact leaf_4357_sound hz

theorem leaf_4359_ok : checkAt 527 1000 box_4359 cert_4359 = true := by
  have h := List.all_eq_true.mp batch_87_05_ok accepted_4359 (by simp [batch_87_05_values])
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

theorem leaf_4362_ok : checkAt 527 1000 box_4362 cert_4362 = true := by
  have h := List.all_eq_true.mp batch_87_06_ok accepted_4362 (by simp [batch_87_06_values])
  exact h
theorem leaf_4362_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4362.profileLo box_4362.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4362_ok
theorem branch_box_4362_nonnegative : ∀ j, 0 ≤ branch_box_4362.lower j ∧ 0 ≤ branch_box_4362.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4362, Box.profileLo, Box.profileHi, box_4362]
theorem leaf_4362_BranchSafe : CertificateConsequences.BranchSafe branch_box_4362 := by
  left; refine ⟨branch_box_4362_nonnegative, ?_⟩
  intro z hz; exact leaf_4362_sound hz

theorem leaf_4364_ok : checkAt 527 1000 box_4364 cert_4364 = true := by
  have h := List.all_eq_true.mp batch_87_07_ok accepted_4364 (by simp [batch_87_07_values])
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

theorem leaf_4366_ok : checkAt 527 1000 box_4366 cert_4366 = true := by
  have h := List.all_eq_true.mp batch_87_08_ok accepted_4366 (by simp [batch_87_08_values])
  exact h
theorem leaf_4366_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4366.profileLo box_4366.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4366_ok
theorem branch_box_4366_nonnegative : ∀ j, 0 ≤ branch_box_4366.lower j ∧ 0 ≤ branch_box_4366.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4366, Box.profileLo, Box.profileHi, box_4366]
theorem leaf_4366_BranchSafe : CertificateConsequences.BranchSafe branch_box_4366 := by
  left; refine ⟨branch_box_4366_nonnegative, ?_⟩
  intro z hz; exact leaf_4366_sound hz

theorem leaf_4368_ok : checkAt 527 1000 box_4368 cert_4368 = true := by
  have h := List.all_eq_true.mp batch_87_09_ok accepted_4368 (by simp [batch_87_09_values])
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

theorem leaf_4370_ok : checkAt 527 1000 box_4370 cert_4370 = true := by
  have h := List.all_eq_true.mp batch_87_10_ok accepted_4370 (by simp [batch_87_10_values])
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

theorem leaf_4371_ok : checkAt 527 1000 box_4371 cert_4371 = true := by
  have h := List.all_eq_true.mp batch_87_11_ok accepted_4371 (by simp [batch_87_11_values])
  exact h
theorem leaf_4371_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4371.profileLo box_4371.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4371_ok
theorem branch_box_4371_nonnegative : ∀ j, 0 ≤ branch_box_4371.lower j ∧ 0 ≤ branch_box_4371.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4371, Box.profileLo, Box.profileHi, box_4371]
theorem leaf_4371_BranchSafe : CertificateConsequences.BranchSafe branch_box_4371 := by
  left; refine ⟨branch_box_4371_nonnegative, ?_⟩
  intro z hz; exact leaf_4371_sound hz

theorem leaf_4378_ok : checkAt 527 1000 box_4378 cert_4378 = true := by
  have h := List.all_eq_true.mp batch_87_12_ok accepted_4378 (by simp [batch_87_12_values])
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

theorem leaf_4380_ok : checkAt 527 1000 box_4380 cert_4380 = true := by
  have h := List.all_eq_true.mp batch_87_13_ok accepted_4380 (by simp [batch_87_13_values])
  exact h
theorem leaf_4380_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4380.profileLo box_4380.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4380_ok
theorem branch_box_4380_nonnegative : ∀ j, 0 ≤ branch_box_4380.lower j ∧ 0 ≤ branch_box_4380.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4380, Box.profileLo, Box.profileHi, box_4380]
theorem leaf_4380_BranchSafe : CertificateConsequences.BranchSafe branch_box_4380 := by
  left; refine ⟨branch_box_4380_nonnegative, ?_⟩
  intro z hz; exact leaf_4380_sound hz

theorem leaf_4382_ok : checkAt 527 1000 box_4382 cert_4382 = true := by
  have h := List.all_eq_true.mp batch_87_14_ok accepted_4382 (by simp [batch_87_14_values])
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

theorem leaf_4384_ok : checkAt 527 1000 box_4384 cert_4384 = true := by
  have h := List.all_eq_true.mp batch_87_15_ok accepted_4384 (by simp [batch_87_15_values])
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

theorem leaf_4386_ok : checkAt 527 1000 box_4386 cert_4386 = true := by
  have h := List.all_eq_true.mp batch_87_16_ok accepted_4386 (by simp [batch_87_16_values])
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

theorem leaf_4388_ok : checkAt 527 1000 box_4388 cert_4388 = true := by
  have h := List.all_eq_true.mp batch_87_17_ok accepted_4388 (by simp [batch_87_17_values])
  exact h
theorem leaf_4388_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4388.profileLo box_4388.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4388_ok
theorem branch_box_4388_nonnegative : ∀ j, 0 ≤ branch_box_4388.lower j ∧ 0 ≤ branch_box_4388.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4388, Box.profileLo, Box.profileHi, box_4388]
theorem leaf_4388_BranchSafe : CertificateConsequences.BranchSafe branch_box_4388 := by
  left; refine ⟨branch_box_4388_nonnegative, ?_⟩
  intro z hz; exact leaf_4388_sound hz

theorem leaf_4390_ok : checkAt 527 1000 box_4390 cert_4390 = true := by
  have h := List.all_eq_true.mp batch_87_18_ok accepted_4390 (by simp [batch_87_18_values])
  exact h
theorem leaf_4390_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4390.profileLo box_4390.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4390_ok
theorem branch_box_4390_nonnegative : ∀ j, 0 ≤ branch_box_4390.lower j ∧ 0 ≤ branch_box_4390.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4390, Box.profileLo, Box.profileHi, box_4390]
theorem leaf_4390_BranchSafe : CertificateConsequences.BranchSafe branch_box_4390 := by
  left; refine ⟨branch_box_4390_nonnegative, ?_⟩
  intro z hz; exact leaf_4390_sound hz

theorem leaf_4392_ok : checkAt 527 1000 box_4392 cert_4392 = true := by
  have h := List.all_eq_true.mp batch_87_19_ok accepted_4392 (by simp [batch_87_19_values])
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

theorem leaf_4393_ok : checkAt 527 1000 box_4393 cert_4393 = true := by
  have h := List.all_eq_true.mp batch_87_20_ok accepted_4393 (by simp [batch_87_20_values])
  exact h
theorem leaf_4393_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4393.profileLo box_4393.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4393_ok
theorem branch_box_4393_nonnegative : ∀ j, 0 ≤ branch_box_4393.lower j ∧ 0 ≤ branch_box_4393.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4393, Box.profileLo, Box.profileHi, box_4393]
theorem leaf_4393_BranchSafe : CertificateConsequences.BranchSafe branch_box_4393 := by
  left; refine ⟨branch_box_4393_nonnegative, ?_⟩
  intro z hz; exact leaf_4393_sound hz

theorem leaf_4395_ok : checkAt 527 1000 box_4395 cert_4395 = true := by
  have h := List.all_eq_true.mp batch_87_21_ok accepted_4395 (by simp [batch_87_21_values])
  exact h
theorem leaf_4395_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4395.profileLo box_4395.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4395_ok
theorem branch_box_4395_nonnegative : ∀ j, 0 ≤ branch_box_4395.lower j ∧ 0 ≤ branch_box_4395.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4395, Box.profileLo, Box.profileHi, box_4395]
theorem leaf_4395_BranchSafe : CertificateConsequences.BranchSafe branch_box_4395 := by
  left; refine ⟨branch_box_4395_nonnegative, ?_⟩
  intro z hz; exact leaf_4395_sound hz

theorem leaf_4398_ok : checkAt 527 1000 box_4398 cert_4398 = true := by
  have h := List.all_eq_true.mp batch_87_22_ok accepted_4398 (by simp [batch_87_22_values])
  exact h
theorem leaf_4398_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4398.profileLo box_4398.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4398_ok
theorem branch_box_4398_nonnegative : ∀ j, 0 ≤ branch_box_4398.lower j ∧ 0 ≤ branch_box_4398.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4398, Box.profileLo, Box.profileHi, box_4398]
theorem leaf_4398_BranchSafe : CertificateConsequences.BranchSafe branch_box_4398 := by
  left; refine ⟨branch_box_4398_nonnegative, ?_⟩
  intro z hz; exact leaf_4398_sound hz

#print axioms batch_87_00_ok
#print axioms leaf_4350_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
