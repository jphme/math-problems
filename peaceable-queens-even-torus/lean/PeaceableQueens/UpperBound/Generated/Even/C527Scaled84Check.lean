import PeaceableQueens.UpperBound.Generated.Even.C527Scaled84Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_84_00_values : List Bool := [accepted_4200]
theorem batch_84_00_ok : batch_84_00_values.all id = true := by decide

def batch_84_01_values : List Bool := [accepted_4203]
theorem batch_84_01_ok : batch_84_01_values.all id = true := by decide

def batch_84_02_values : List Bool := [accepted_4205]
theorem batch_84_02_ok : batch_84_02_values.all id = true := by decide

def batch_84_03_values : List Bool := [accepted_4206]
theorem batch_84_03_ok : batch_84_03_values.all id = true := by decide

def batch_84_04_values : List Bool := [accepted_4207]
theorem batch_84_04_ok : batch_84_04_values.all id = true := by decide

def batch_84_05_values : List Bool := [accepted_4208]
theorem batch_84_05_ok : batch_84_05_values.all id = true := by decide

def batch_84_06_values : List Bool := [accepted_4215]
theorem batch_84_06_ok : batch_84_06_values.all id = true := by decide

def batch_84_07_values : List Bool := [accepted_4216]
theorem batch_84_07_ok : batch_84_07_values.all id = true := by decide

def batch_84_08_values : List Bool := [accepted_4218]
theorem batch_84_08_ok : batch_84_08_values.all id = true := by decide

def batch_84_09_values : List Bool := [accepted_4219]
theorem batch_84_09_ok : batch_84_09_values.all id = true := by decide

def batch_84_10_values : List Bool := [accepted_4220]
theorem batch_84_10_ok : batch_84_10_values.all id = true := by decide

def batch_84_11_values : List Bool := [accepted_4223]
theorem batch_84_11_ok : batch_84_11_values.all id = true := by decide

def batch_84_12_values : List Bool := [accepted_4225]
theorem batch_84_12_ok : batch_84_12_values.all id = true := by decide

def batch_84_13_values : List Bool := [accepted_4226]
theorem batch_84_13_ok : batch_84_13_values.all id = true := by decide

def batch_84_14_values : List Bool := [accepted_4227]
theorem batch_84_14_ok : batch_84_14_values.all id = true := by decide

def batch_84_15_values : List Bool := [accepted_4231]
theorem batch_84_15_ok : batch_84_15_values.all id = true := by decide

def batch_84_16_values : List Bool := [accepted_4232]
theorem batch_84_16_ok : batch_84_16_values.all id = true := by decide

def batch_84_17_values : List Bool := [accepted_4234]
theorem batch_84_17_ok : batch_84_17_values.all id = true := by decide

def batch_84_18_values : List Bool := [accepted_4235]
theorem batch_84_18_ok : batch_84_18_values.all id = true := by decide

def batch_84_19_values : List Bool := [accepted_4236]
theorem batch_84_19_ok : batch_84_19_values.all id = true := by decide

def batch_84_20_values : List Bool := [accepted_4239]
theorem batch_84_20_ok : batch_84_20_values.all id = true := by decide

def batch_84_21_values : List Bool := [accepted_4240]
theorem batch_84_21_ok : batch_84_21_values.all id = true := by decide

def batch_84_22_values : List Bool := [accepted_4243]
theorem batch_84_22_ok : batch_84_22_values.all id = true := by decide

def batch_84_23_values : List Bool := [accepted_4244]
theorem batch_84_23_ok : batch_84_23_values.all id = true := by decide

def batch_84_24_values : List Bool := [accepted_4245]
theorem batch_84_24_ok : batch_84_24_values.all id = true := by decide

def batch_84_25_values : List Bool := [accepted_4247]
theorem batch_84_25_ok : batch_84_25_values.all id = true := by decide

def batch_84_26_values : List Bool := [accepted_4248]
theorem batch_84_26_ok : batch_84_26_values.all id = true := by decide

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

theorem leaf_4203_ok : checkAt 527 1000 box_4203 cert_4203 = true := by
  have h := List.all_eq_true.mp batch_84_01_ok accepted_4203 (by simp [batch_84_01_values])
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
  have h := List.all_eq_true.mp batch_84_02_ok accepted_4205 (by simp [batch_84_02_values])
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

theorem leaf_4206_ok : checkAt 527 1000 box_4206 cert_4206 = true := by
  have h := List.all_eq_true.mp batch_84_03_ok accepted_4206 (by simp [batch_84_03_values])
  exact h
theorem leaf_4206_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4206.profileLo box_4206.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4206_ok
theorem branch_box_4206_nonnegative : ∀ j, 0 ≤ branch_box_4206.lower j ∧ 0 ≤ branch_box_4206.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4206, Box.profileLo, Box.profileHi, box_4206]
theorem leaf_4206_BranchSafe : CertificateConsequences.BranchSafe branch_box_4206 := by
  left; refine ⟨branch_box_4206_nonnegative, ?_⟩
  intro z hz; exact leaf_4206_sound hz

theorem leaf_4207_ok : checkAt 527 1000 box_4207 cert_4207 = true := by
  have h := List.all_eq_true.mp batch_84_04_ok accepted_4207 (by simp [batch_84_04_values])
  exact h
theorem leaf_4207_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4207.profileLo box_4207.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4207_ok
theorem branch_box_4207_nonnegative : ∀ j, 0 ≤ branch_box_4207.lower j ∧ 0 ≤ branch_box_4207.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4207, Box.profileLo, Box.profileHi, box_4207]
theorem leaf_4207_BranchSafe : CertificateConsequences.BranchSafe branch_box_4207 := by
  left; refine ⟨branch_box_4207_nonnegative, ?_⟩
  intro z hz; exact leaf_4207_sound hz

theorem leaf_4208_ok : checkAt 527 1000 box_4208 cert_4208 = true := by
  have h := List.all_eq_true.mp batch_84_05_ok accepted_4208 (by simp [batch_84_05_values])
  exact h
theorem leaf_4208_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4208.profileLo box_4208.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4208_ok
theorem branch_box_4208_nonnegative : ∀ j, 0 ≤ branch_box_4208.lower j ∧ 0 ≤ branch_box_4208.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4208, Box.profileLo, Box.profileHi, box_4208]
theorem leaf_4208_BranchSafe : CertificateConsequences.BranchSafe branch_box_4208 := by
  left; refine ⟨branch_box_4208_nonnegative, ?_⟩
  intro z hz; exact leaf_4208_sound hz

theorem leaf_4215_ok : checkAt 527 1000 box_4215 cert_4215 = true := by
  have h := List.all_eq_true.mp batch_84_06_ok accepted_4215 (by simp [batch_84_06_values])
  exact h
theorem leaf_4215_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4215.profileLo box_4215.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4215_ok
theorem branch_box_4215_nonnegative : ∀ j, 0 ≤ branch_box_4215.lower j ∧ 0 ≤ branch_box_4215.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4215, Box.profileLo, Box.profileHi, box_4215]
theorem leaf_4215_BranchSafe : CertificateConsequences.BranchSafe branch_box_4215 := by
  left; refine ⟨branch_box_4215_nonnegative, ?_⟩
  intro z hz; exact leaf_4215_sound hz

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

theorem leaf_4218_ok : checkAt 527 1000 box_4218 cert_4218 = true := by
  have h := List.all_eq_true.mp batch_84_08_ok accepted_4218 (by simp [batch_84_08_values])
  exact h
theorem leaf_4218_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4218.profileLo box_4218.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4218_ok
theorem branch_box_4218_nonnegative : ∀ j, 0 ≤ branch_box_4218.lower j ∧ 0 ≤ branch_box_4218.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4218, Box.profileLo, Box.profileHi, box_4218]
theorem leaf_4218_BranchSafe : CertificateConsequences.BranchSafe branch_box_4218 := by
  left; refine ⟨branch_box_4218_nonnegative, ?_⟩
  intro z hz; exact leaf_4218_sound hz

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

theorem leaf_4220_ok : checkAt 527 1000 box_4220 cert_4220 = true := by
  have h := List.all_eq_true.mp batch_84_10_ok accepted_4220 (by simp [batch_84_10_values])
  exact h
theorem leaf_4220_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4220.profileLo box_4220.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4220_ok
theorem branch_box_4220_nonnegative : ∀ j, 0 ≤ branch_box_4220.lower j ∧ 0 ≤ branch_box_4220.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4220, Box.profileLo, Box.profileHi, box_4220]
theorem leaf_4220_BranchSafe : CertificateConsequences.BranchSafe branch_box_4220 := by
  left; refine ⟨branch_box_4220_nonnegative, ?_⟩
  intro z hz; exact leaf_4220_sound hz

theorem leaf_4223_ok : checkAt 527 1000 box_4223 cert_4223 = true := by
  have h := List.all_eq_true.mp batch_84_11_ok accepted_4223 (by simp [batch_84_11_values])
  exact h
theorem leaf_4223_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4223.profileLo box_4223.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4223_ok
theorem branch_box_4223_nonnegative : ∀ j, 0 ≤ branch_box_4223.lower j ∧ 0 ≤ branch_box_4223.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4223, Box.profileLo, Box.profileHi, box_4223]
theorem leaf_4223_BranchSafe : CertificateConsequences.BranchSafe branch_box_4223 := by
  left; refine ⟨branch_box_4223_nonnegative, ?_⟩
  intro z hz; exact leaf_4223_sound hz

theorem leaf_4225_ok : checkAt 527 1000 box_4225 cert_4225 = true := by
  have h := List.all_eq_true.mp batch_84_12_ok accepted_4225 (by simp [batch_84_12_values])
  exact h
theorem leaf_4225_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4225.profileLo box_4225.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4225_ok
theorem branch_box_4225_nonnegative : ∀ j, 0 ≤ branch_box_4225.lower j ∧ 0 ≤ branch_box_4225.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4225, Box.profileLo, Box.profileHi, box_4225]
theorem leaf_4225_BranchSafe : CertificateConsequences.BranchSafe branch_box_4225 := by
  left; refine ⟨branch_box_4225_nonnegative, ?_⟩
  intro z hz; exact leaf_4225_sound hz

theorem leaf_4226_ok : checkAt 527 1000 box_4226 cert_4226 = true := by
  have h := List.all_eq_true.mp batch_84_13_ok accepted_4226 (by simp [batch_84_13_values])
  exact h
theorem leaf_4226_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4226.profileLo box_4226.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4226_ok
theorem branch_box_4226_nonnegative : ∀ j, 0 ≤ branch_box_4226.lower j ∧ 0 ≤ branch_box_4226.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4226, Box.profileLo, Box.profileHi, box_4226]
theorem leaf_4226_BranchSafe : CertificateConsequences.BranchSafe branch_box_4226 := by
  left; refine ⟨branch_box_4226_nonnegative, ?_⟩
  intro z hz; exact leaf_4226_sound hz

theorem leaf_4227_ok : checkAt 527 1000 box_4227 cert_4227 = true := by
  have h := List.all_eq_true.mp batch_84_14_ok accepted_4227 (by simp [batch_84_14_values])
  exact h
theorem leaf_4227_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4227.profileLo box_4227.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4227_ok
theorem branch_box_4227_nonnegative : ∀ j, 0 ≤ branch_box_4227.lower j ∧ 0 ≤ branch_box_4227.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4227, Box.profileLo, Box.profileHi, box_4227]
theorem leaf_4227_BranchSafe : CertificateConsequences.BranchSafe branch_box_4227 := by
  left; refine ⟨branch_box_4227_nonnegative, ?_⟩
  intro z hz; exact leaf_4227_sound hz

theorem leaf_4231_ok : checkAt 527 1000 box_4231 cert_4231 = true := by
  have h := List.all_eq_true.mp batch_84_15_ok accepted_4231 (by simp [batch_84_15_values])
  exact h
theorem leaf_4231_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4231.profileLo box_4231.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4231_ok
theorem branch_box_4231_nonnegative : ∀ j, 0 ≤ branch_box_4231.lower j ∧ 0 ≤ branch_box_4231.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4231, Box.profileLo, Box.profileHi, box_4231]
theorem leaf_4231_BranchSafe : CertificateConsequences.BranchSafe branch_box_4231 := by
  left; refine ⟨branch_box_4231_nonnegative, ?_⟩
  intro z hz; exact leaf_4231_sound hz

theorem leaf_4232_ok : checkAt 527 1000 box_4232 cert_4232 = true := by
  have h := List.all_eq_true.mp batch_84_16_ok accepted_4232 (by simp [batch_84_16_values])
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
  have h := List.all_eq_true.mp batch_84_17_ok accepted_4234 (by simp [batch_84_17_values])
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

theorem leaf_4235_ok : checkAt 527 1000 box_4235 cert_4235 = true := by
  have h := List.all_eq_true.mp batch_84_18_ok accepted_4235 (by simp [batch_84_18_values])
  exact h
theorem leaf_4235_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4235.profileLo box_4235.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4235_ok
theorem branch_box_4235_nonnegative : ∀ j, 0 ≤ branch_box_4235.lower j ∧ 0 ≤ branch_box_4235.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4235, Box.profileLo, Box.profileHi, box_4235]
theorem leaf_4235_BranchSafe : CertificateConsequences.BranchSafe branch_box_4235 := by
  left; refine ⟨branch_box_4235_nonnegative, ?_⟩
  intro z hz; exact leaf_4235_sound hz

theorem leaf_4236_ok : checkAt 527 1000 box_4236 cert_4236 = true := by
  have h := List.all_eq_true.mp batch_84_19_ok accepted_4236 (by simp [batch_84_19_values])
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

theorem leaf_4239_ok : checkAt 527 1000 box_4239 cert_4239 = true := by
  have h := List.all_eq_true.mp batch_84_20_ok accepted_4239 (by simp [batch_84_20_values])
  exact h
theorem leaf_4239_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4239.profileLo box_4239.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4239_ok
theorem branch_box_4239_nonnegative : ∀ j, 0 ≤ branch_box_4239.lower j ∧ 0 ≤ branch_box_4239.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4239, Box.profileLo, Box.profileHi, box_4239]
theorem leaf_4239_BranchSafe : CertificateConsequences.BranchSafe branch_box_4239 := by
  left; refine ⟨branch_box_4239_nonnegative, ?_⟩
  intro z hz; exact leaf_4239_sound hz

theorem leaf_4240_ok : checkAt 527 1000 box_4240 cert_4240 = true := by
  have h := List.all_eq_true.mp batch_84_21_ok accepted_4240 (by simp [batch_84_21_values])
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

theorem leaf_4243_ok : checkAt 527 1000 box_4243 cert_4243 = true := by
  have h := List.all_eq_true.mp batch_84_22_ok accepted_4243 (by simp [batch_84_22_values])
  exact h
theorem leaf_4243_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4243.profileLo box_4243.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4243_ok
theorem branch_box_4243_nonnegative : ∀ j, 0 ≤ branch_box_4243.lower j ∧ 0 ≤ branch_box_4243.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4243, Box.profileLo, Box.profileHi, box_4243]
theorem leaf_4243_BranchSafe : CertificateConsequences.BranchSafe branch_box_4243 := by
  left; refine ⟨branch_box_4243_nonnegative, ?_⟩
  intro z hz; exact leaf_4243_sound hz

theorem leaf_4244_ok : checkAt 527 1000 box_4244 cert_4244 = true := by
  have h := List.all_eq_true.mp batch_84_23_ok accepted_4244 (by simp [batch_84_23_values])
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
  have h := List.all_eq_true.mp batch_84_24_ok accepted_4245 (by simp [batch_84_24_values])
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

theorem leaf_4247_ok : checkAt 527 1000 box_4247 cert_4247 = true := by
  have h := List.all_eq_true.mp batch_84_25_ok accepted_4247 (by simp [batch_84_25_values])
  exact h
theorem leaf_4247_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4247.profileLo box_4247.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4247_ok
theorem branch_box_4247_nonnegative : ∀ j, 0 ≤ branch_box_4247.lower j ∧ 0 ≤ branch_box_4247.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4247, Box.profileLo, Box.profileHi, box_4247]
theorem leaf_4247_BranchSafe : CertificateConsequences.BranchSafe branch_box_4247 := by
  left; refine ⟨branch_box_4247_nonnegative, ?_⟩
  intro z hz; exact leaf_4247_sound hz

theorem leaf_4248_ok : checkAt 527 1000 box_4248 cert_4248 = true := by
  have h := List.all_eq_true.mp batch_84_26_ok accepted_4248 (by simp [batch_84_26_values])
  exact h
theorem leaf_4248_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4248.profileLo box_4248.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4248_ok
theorem branch_box_4248_nonnegative : ∀ j, 0 ≤ branch_box_4248.lower j ∧ 0 ≤ branch_box_4248.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4248, Box.profileLo, Box.profileHi, box_4248]
theorem leaf_4248_BranchSafe : CertificateConsequences.BranchSafe branch_box_4248 := by
  left; refine ⟨branch_box_4248_nonnegative, ?_⟩
  intro z hz; exact leaf_4248_sound hz

#print axioms batch_84_00_ok
#print axioms leaf_4200_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
