import PeaceableQueens.UpperBound.Generated.Even.CoreScaled84Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_84_00_values : List Bool := [accepted_4200]
theorem batch_84_00_ok : batch_84_00_values.all id = true := by decide

def batch_84_01_values : List Bool := [accepted_4202]
theorem batch_84_01_ok : batch_84_01_values.all id = true := by decide

def batch_84_02_values : List Bool := [accepted_4203]
theorem batch_84_02_ok : batch_84_02_values.all id = true := by decide

def batch_84_03_values : List Bool := [accepted_4205]
theorem batch_84_03_ok : batch_84_03_values.all id = true := by decide

def batch_84_04_values : List Bool := [accepted_4209]
theorem batch_84_04_ok : batch_84_04_values.all id = true := by decide

def batch_84_05_values : List Bool := [accepted_4212]
theorem batch_84_05_ok : batch_84_05_values.all id = true := by decide

def batch_84_06_values : List Bool := [accepted_4214]
theorem batch_84_06_ok : batch_84_06_values.all id = true := by decide

def batch_84_07_values : List Bool := [accepted_4216]
theorem batch_84_07_ok : batch_84_07_values.all id = true := by decide

def batch_84_08_values : List Bool := [accepted_4217]
theorem batch_84_08_ok : batch_84_08_values.all id = true := by decide

def batch_84_09_values : List Bool := [accepted_4219]
theorem batch_84_09_ok : batch_84_09_values.all id = true := by decide

def batch_84_10_values : List Bool := [accepted_4221]
theorem batch_84_10_ok : batch_84_10_values.all id = true := by decide

def batch_84_11_values : List Bool := [accepted_4228]
theorem batch_84_11_ok : batch_84_11_values.all id = true := by decide

def batch_84_12_values : List Bool := [accepted_4230]
theorem batch_84_12_ok : batch_84_12_values.all id = true := by decide

def batch_84_13_values : List Bool := [accepted_4232]
theorem batch_84_13_ok : batch_84_13_values.all id = true := by decide

def batch_84_14_values : List Bool := [accepted_4234]
theorem batch_84_14_ok : batch_84_14_values.all id = true := by decide

def batch_84_15_values : List Bool := [accepted_4236]
theorem batch_84_15_ok : batch_84_15_values.all id = true := by decide

def batch_84_16_values : List Bool := [accepted_4237]
theorem batch_84_16_ok : batch_84_16_values.all id = true := by decide

def batch_84_17_values : List Bool := [accepted_4240]
theorem batch_84_17_ok : batch_84_17_values.all id = true := by decide

def batch_84_18_values : List Bool := [accepted_4242]
theorem batch_84_18_ok : batch_84_18_values.all id = true := by decide

def batch_84_19_values : List Bool := [accepted_4244]
theorem batch_84_19_ok : batch_84_19_values.all id = true := by decide

def batch_84_20_values : List Bool := [accepted_4245]
theorem batch_84_20_ok : batch_84_20_values.all id = true := by decide

theorem leaf_4200_ok : checkAt 527 1000 box_4200 cert_4200 = true := by
  have h := List.all_eq_true.mp batch_84_00_ok accepted_4200 (by simp [batch_84_00_values])
  exact h
theorem leaf_4200_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4200.profileLo box_4200.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4200_ok
theorem branch_box_4200_nonnegative : ∀ j, 0 ≤ branch_box_4200.lower j ∧ 0 ≤ branch_box_4200.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4200, Box.profileLo, Box.profileHi, box_4200]
theorem leaf_4200_BranchSafe : CertificateConsequences.BranchSafe branch_box_4200 := by
  left; refine ⟨branch_box_4200_nonnegative, ?_⟩
  intro z hz; exact leaf_4200_sound hz

theorem leaf_4202_ok : checkAt 527 1000 box_4202 cert_4202 = true := by
  have h := List.all_eq_true.mp batch_84_01_ok accepted_4202 (by simp [batch_84_01_values])
  exact h
theorem leaf_4202_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4202.profileLo box_4202.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4202_ok
theorem branch_box_4202_nonnegative : ∀ j, 0 ≤ branch_box_4202.lower j ∧ 0 ≤ branch_box_4202.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4202, Box.profileLo, Box.profileHi, box_4202]
theorem leaf_4202_BranchSafe : CertificateConsequences.BranchSafe branch_box_4202 := by
  left; refine ⟨branch_box_4202_nonnegative, ?_⟩
  intro z hz; exact leaf_4202_sound hz

theorem leaf_4203_ok : checkAt 527 1000 box_4203 cert_4203 = true := by
  have h := List.all_eq_true.mp batch_84_02_ok accepted_4203 (by simp [batch_84_02_values])
  exact h
theorem leaf_4203_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4203.profileLo box_4203.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4203_ok
theorem branch_box_4203_nonnegative : ∀ j, 0 ≤ branch_box_4203.lower j ∧ 0 ≤ branch_box_4203.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4203, Box.profileLo, Box.profileHi, box_4203]
theorem leaf_4203_BranchSafe : CertificateConsequences.BranchSafe branch_box_4203 := by
  left; refine ⟨branch_box_4203_nonnegative, ?_⟩
  intro z hz; exact leaf_4203_sound hz

theorem leaf_4205_ok : checkAt 527 1000 box_4205 cert_4205 = true := by
  have h := List.all_eq_true.mp batch_84_03_ok accepted_4205 (by simp [batch_84_03_values])
  exact h
theorem leaf_4205_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4205.profileLo box_4205.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4205_ok
theorem branch_box_4205_nonnegative : ∀ j, 0 ≤ branch_box_4205.lower j ∧ 0 ≤ branch_box_4205.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4205, Box.profileLo, Box.profileHi, box_4205]
theorem leaf_4205_BranchSafe : CertificateConsequences.BranchSafe branch_box_4205 := by
  left; refine ⟨branch_box_4205_nonnegative, ?_⟩
  intro z hz; exact leaf_4205_sound hz

theorem leaf_4209_ok : checkAt 527 1000 box_4209 cert_4209 = true := by
  have h := List.all_eq_true.mp batch_84_04_ok accepted_4209 (by simp [batch_84_04_values])
  exact h
theorem leaf_4209_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4209.profileLo box_4209.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4209_ok
theorem branch_box_4209_nonnegative : ∀ j, 0 ≤ branch_box_4209.lower j ∧ 0 ≤ branch_box_4209.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4209, Box.profileLo, Box.profileHi, box_4209]
theorem leaf_4209_BranchSafe : CertificateConsequences.BranchSafe branch_box_4209 := by
  left; refine ⟨branch_box_4209_nonnegative, ?_⟩
  intro z hz; exact leaf_4209_sound hz

theorem leaf_4212_ok : checkAt 527 1000 box_4212 cert_4212 = true := by
  have h := List.all_eq_true.mp batch_84_05_ok accepted_4212 (by simp [batch_84_05_values])
  exact h
theorem leaf_4212_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4212.profileLo box_4212.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4212_ok
theorem branch_box_4212_nonnegative : ∀ j, 0 ≤ branch_box_4212.lower j ∧ 0 ≤ branch_box_4212.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4212, Box.profileLo, Box.profileHi, box_4212]
theorem leaf_4212_BranchSafe : CertificateConsequences.BranchSafe branch_box_4212 := by
  left; refine ⟨branch_box_4212_nonnegative, ?_⟩
  intro z hz; exact leaf_4212_sound hz

theorem leaf_4214_ok : checkAt 527 1000 box_4214 cert_4214 = true := by
  have h := List.all_eq_true.mp batch_84_06_ok accepted_4214 (by simp [batch_84_06_values])
  exact h
theorem leaf_4214_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4214.profileLo box_4214.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4214_ok
theorem branch_box_4214_nonnegative : ∀ j, 0 ≤ branch_box_4214.lower j ∧ 0 ≤ branch_box_4214.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4214, Box.profileLo, Box.profileHi, box_4214]
theorem leaf_4214_BranchSafe : CertificateConsequences.BranchSafe branch_box_4214 := by
  left; refine ⟨branch_box_4214_nonnegative, ?_⟩
  intro z hz; exact leaf_4214_sound hz

theorem leaf_4216_ok : checkAt 527 1000 box_4216 cert_4216 = true := by
  have h := List.all_eq_true.mp batch_84_07_ok accepted_4216 (by simp [batch_84_07_values])
  exact h
theorem leaf_4216_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4216.profileLo box_4216.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4216_ok
theorem branch_box_4216_nonnegative : ∀ j, 0 ≤ branch_box_4216.lower j ∧ 0 ≤ branch_box_4216.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4216, Box.profileLo, Box.profileHi, box_4216]
theorem leaf_4216_BranchSafe : CertificateConsequences.BranchSafe branch_box_4216 := by
  left; refine ⟨branch_box_4216_nonnegative, ?_⟩
  intro z hz; exact leaf_4216_sound hz

theorem leaf_4217_ok : checkAt 527 1000 box_4217 cert_4217 = true := by
  have h := List.all_eq_true.mp batch_84_08_ok accepted_4217 (by simp [batch_84_08_values])
  exact h
theorem leaf_4217_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4217.profileLo box_4217.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4217_ok
theorem branch_box_4217_nonnegative : ∀ j, 0 ≤ branch_box_4217.lower j ∧ 0 ≤ branch_box_4217.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4217, Box.profileLo, Box.profileHi, box_4217]
theorem leaf_4217_BranchSafe : CertificateConsequences.BranchSafe branch_box_4217 := by
  left; refine ⟨branch_box_4217_nonnegative, ?_⟩
  intro z hz; exact leaf_4217_sound hz

theorem leaf_4219_ok : checkAt 527 1000 box_4219 cert_4219 = true := by
  have h := List.all_eq_true.mp batch_84_09_ok accepted_4219 (by simp [batch_84_09_values])
  exact h
theorem leaf_4219_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4219.profileLo box_4219.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4219_ok
theorem branch_box_4219_nonnegative : ∀ j, 0 ≤ branch_box_4219.lower j ∧ 0 ≤ branch_box_4219.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4219, Box.profileLo, Box.profileHi, box_4219]
theorem leaf_4219_BranchSafe : CertificateConsequences.BranchSafe branch_box_4219 := by
  left; refine ⟨branch_box_4219_nonnegative, ?_⟩
  intro z hz; exact leaf_4219_sound hz

theorem leaf_4221_ok : checkAt 527 1000 box_4221 cert_4221 = true := by
  have h := List.all_eq_true.mp batch_84_10_ok accepted_4221 (by simp [batch_84_10_values])
  exact h
theorem leaf_4221_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4221.profileLo box_4221.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4221_ok
theorem branch_box_4221_nonnegative : ∀ j, 0 ≤ branch_box_4221.lower j ∧ 0 ≤ branch_box_4221.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4221, Box.profileLo, Box.profileHi, box_4221]
theorem leaf_4221_BranchSafe : CertificateConsequences.BranchSafe branch_box_4221 := by
  left; refine ⟨branch_box_4221_nonnegative, ?_⟩
  intro z hz; exact leaf_4221_sound hz

theorem leaf_4228_ok : checkAt 527 1000 box_4228 cert_4228 = true := by
  have h := List.all_eq_true.mp batch_84_11_ok accepted_4228 (by simp [batch_84_11_values])
  exact h
theorem leaf_4228_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4228.profileLo box_4228.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4228_ok
theorem branch_box_4228_nonnegative : ∀ j, 0 ≤ branch_box_4228.lower j ∧ 0 ≤ branch_box_4228.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4228, Box.profileLo, Box.profileHi, box_4228]
theorem leaf_4228_BranchSafe : CertificateConsequences.BranchSafe branch_box_4228 := by
  left; refine ⟨branch_box_4228_nonnegative, ?_⟩
  intro z hz; exact leaf_4228_sound hz

theorem leaf_4230_ok : checkAt 527 1000 box_4230 cert_4230 = true := by
  have h := List.all_eq_true.mp batch_84_12_ok accepted_4230 (by simp [batch_84_12_values])
  exact h
theorem leaf_4230_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4230.profileLo box_4230.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4230_ok
theorem branch_box_4230_nonnegative : ∀ j, 0 ≤ branch_box_4230.lower j ∧ 0 ≤ branch_box_4230.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4230, Box.profileLo, Box.profileHi, box_4230]
theorem leaf_4230_BranchSafe : CertificateConsequences.BranchSafe branch_box_4230 := by
  left; refine ⟨branch_box_4230_nonnegative, ?_⟩
  intro z hz; exact leaf_4230_sound hz

theorem leaf_4232_ok : checkAt 527 1000 box_4232 cert_4232 = true := by
  have h := List.all_eq_true.mp batch_84_13_ok accepted_4232 (by simp [batch_84_13_values])
  exact h
theorem leaf_4232_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4232.profileLo box_4232.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4232_ok
theorem branch_box_4232_nonnegative : ∀ j, 0 ≤ branch_box_4232.lower j ∧ 0 ≤ branch_box_4232.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4232, Box.profileLo, Box.profileHi, box_4232]
theorem leaf_4232_BranchSafe : CertificateConsequences.BranchSafe branch_box_4232 := by
  left; refine ⟨branch_box_4232_nonnegative, ?_⟩
  intro z hz; exact leaf_4232_sound hz

theorem leaf_4234_ok : checkAt 527 1000 box_4234 cert_4234 = true := by
  have h := List.all_eq_true.mp batch_84_14_ok accepted_4234 (by simp [batch_84_14_values])
  exact h
theorem leaf_4234_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4234.profileLo box_4234.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4234_ok
theorem branch_box_4234_nonnegative : ∀ j, 0 ≤ branch_box_4234.lower j ∧ 0 ≤ branch_box_4234.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4234, Box.profileLo, Box.profileHi, box_4234]
theorem leaf_4234_BranchSafe : CertificateConsequences.BranchSafe branch_box_4234 := by
  left; refine ⟨branch_box_4234_nonnegative, ?_⟩
  intro z hz; exact leaf_4234_sound hz

theorem leaf_4236_ok : checkAt 527 1000 box_4236 cert_4236 = true := by
  have h := List.all_eq_true.mp batch_84_15_ok accepted_4236 (by simp [batch_84_15_values])
  exact h
theorem leaf_4236_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4236.profileLo box_4236.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4236_ok
theorem branch_box_4236_nonnegative : ∀ j, 0 ≤ branch_box_4236.lower j ∧ 0 ≤ branch_box_4236.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4236, Box.profileLo, Box.profileHi, box_4236]
theorem leaf_4236_BranchSafe : CertificateConsequences.BranchSafe branch_box_4236 := by
  left; refine ⟨branch_box_4236_nonnegative, ?_⟩
  intro z hz; exact leaf_4236_sound hz

theorem leaf_4237_ok : checkAt 527 1000 box_4237 cert_4237 = true := by
  have h := List.all_eq_true.mp batch_84_16_ok accepted_4237 (by simp [batch_84_16_values])
  exact h
theorem leaf_4237_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4237.profileLo box_4237.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4237_ok
theorem branch_box_4237_nonnegative : ∀ j, 0 ≤ branch_box_4237.lower j ∧ 0 ≤ branch_box_4237.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4237, Box.profileLo, Box.profileHi, box_4237]
theorem leaf_4237_BranchSafe : CertificateConsequences.BranchSafe branch_box_4237 := by
  left; refine ⟨branch_box_4237_nonnegative, ?_⟩
  intro z hz; exact leaf_4237_sound hz

theorem leaf_4240_ok : checkAt 527 1000 box_4240 cert_4240 = true := by
  have h := List.all_eq_true.mp batch_84_17_ok accepted_4240 (by simp [batch_84_17_values])
  exact h
theorem leaf_4240_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4240.profileLo box_4240.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4240_ok
theorem branch_box_4240_nonnegative : ∀ j, 0 ≤ branch_box_4240.lower j ∧ 0 ≤ branch_box_4240.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4240, Box.profileLo, Box.profileHi, box_4240]
theorem leaf_4240_BranchSafe : CertificateConsequences.BranchSafe branch_box_4240 := by
  left; refine ⟨branch_box_4240_nonnegative, ?_⟩
  intro z hz; exact leaf_4240_sound hz

theorem leaf_4242_ok : checkAt 527 1000 box_4242 cert_4242 = true := by
  have h := List.all_eq_true.mp batch_84_18_ok accepted_4242 (by simp [batch_84_18_values])
  exact h
theorem leaf_4242_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4242.profileLo box_4242.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4242_ok
theorem branch_box_4242_nonnegative : ∀ j, 0 ≤ branch_box_4242.lower j ∧ 0 ≤ branch_box_4242.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4242, Box.profileLo, Box.profileHi, box_4242]
theorem leaf_4242_BranchSafe : CertificateConsequences.BranchSafe branch_box_4242 := by
  left; refine ⟨branch_box_4242_nonnegative, ?_⟩
  intro z hz; exact leaf_4242_sound hz

theorem leaf_4244_ok : checkAt 527 1000 box_4244 cert_4244 = true := by
  have h := List.all_eq_true.mp batch_84_19_ok accepted_4244 (by simp [batch_84_19_values])
  exact h
theorem leaf_4244_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4244.profileLo box_4244.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4244_ok
theorem branch_box_4244_nonnegative : ∀ j, 0 ≤ branch_box_4244.lower j ∧ 0 ≤ branch_box_4244.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4244, Box.profileLo, Box.profileHi, box_4244]
theorem leaf_4244_BranchSafe : CertificateConsequences.BranchSafe branch_box_4244 := by
  left; refine ⟨branch_box_4244_nonnegative, ?_⟩
  intro z hz; exact leaf_4244_sound hz

theorem leaf_4245_ok : checkAt 527 1000 box_4245 cert_4245 = true := by
  have h := List.all_eq_true.mp batch_84_20_ok accepted_4245 (by simp [batch_84_20_values])
  exact h
theorem leaf_4245_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4245.profileLo box_4245.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4245_ok
theorem branch_box_4245_nonnegative : ∀ j, 0 ≤ branch_box_4245.lower j ∧ 0 ≤ branch_box_4245.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4245, Box.profileLo, Box.profileHi, box_4245]
theorem leaf_4245_BranchSafe : CertificateConsequences.BranchSafe branch_box_4245 := by
  left; refine ⟨branch_box_4245_nonnegative, ?_⟩
  intro z hz; exact leaf_4245_sound hz

#print axioms batch_84_00_ok
#print axioms leaf_4200_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
