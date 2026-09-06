import PeaceableQueens.UpperBound.Generated.Even.CoreScaled80Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_80_00_values : List Bool := [accepted_4004]
theorem batch_80_00_ok : batch_80_00_values.all id = true := by decide

def batch_80_01_values : List Bool := [accepted_4007]
theorem batch_80_01_ok : batch_80_01_values.all id = true := by decide

def batch_80_02_values : List Bool := [accepted_4009]
theorem batch_80_02_ok : batch_80_02_values.all id = true := by decide

def batch_80_03_values : List Bool := [accepted_4013]
theorem batch_80_03_ok : batch_80_03_values.all id = true := by decide

def batch_80_04_values : List Bool := [accepted_4016]
theorem batch_80_04_ok : batch_80_04_values.all id = true := by decide

def batch_80_05_values : List Bool := [accepted_4017]
theorem batch_80_05_ok : batch_80_05_values.all id = true := by decide

def batch_80_06_values : List Bool := [accepted_4019]
theorem batch_80_06_ok : batch_80_06_values.all id = true := by decide

def batch_80_07_values : List Bool := [accepted_4021]
theorem batch_80_07_ok : batch_80_07_values.all id = true := by decide

def batch_80_08_values : List Bool := [accepted_4024]
theorem batch_80_08_ok : batch_80_08_values.all id = true := by decide

def batch_80_09_values : List Bool := [accepted_4030]
theorem batch_80_09_ok : batch_80_09_values.all id = true := by decide

def batch_80_10_values : List Bool := [accepted_4032]
theorem batch_80_10_ok : batch_80_10_values.all id = true := by decide

def batch_80_11_values : List Bool := [accepted_4034]
theorem batch_80_11_ok : batch_80_11_values.all id = true := by decide

def batch_80_12_values : List Bool := [accepted_4040]
theorem batch_80_12_ok : batch_80_12_values.all id = true := by decide

def batch_80_13_values : List Bool := [accepted_4042]
theorem batch_80_13_ok : batch_80_13_values.all id = true := by decide

def batch_80_14_values : List Bool := [accepted_4044]
theorem batch_80_14_ok : batch_80_14_values.all id = true := by decide

def batch_80_15_values : List Bool := [accepted_4046]
theorem batch_80_15_ok : batch_80_15_values.all id = true := by decide

def batch_80_16_values : List Bool := [accepted_4049]
theorem batch_80_16_ok : batch_80_16_values.all id = true := by decide

theorem leaf_4004_ok : checkAt 527 1000 box_4004 cert_4004 = true := by
  have h := List.all_eq_true.mp batch_80_00_ok accepted_4004 (by simp [batch_80_00_values])
  exact h
theorem leaf_4004_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4004.profileLo box_4004.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4004_ok
theorem branch_box_4004_nonnegative : ∀ j, 0 ≤ branch_box_4004.lower j ∧ 0 ≤ branch_box_4004.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4004, Box.profileLo, Box.profileHi, box_4004]
theorem leaf_4004_BranchSafe : CertificateConsequences.BranchSafe branch_box_4004 := by
  left; refine ⟨branch_box_4004_nonnegative, ?_⟩
  intro z hz; exact leaf_4004_sound hz

theorem leaf_4007_ok : checkAt 527 1000 box_4007 cert_4007 = true := by
  have h := List.all_eq_true.mp batch_80_01_ok accepted_4007 (by simp [batch_80_01_values])
  exact h
theorem leaf_4007_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4007.profileLo box_4007.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4007_ok
theorem branch_box_4007_nonnegative : ∀ j, 0 ≤ branch_box_4007.lower j ∧ 0 ≤ branch_box_4007.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4007, Box.profileLo, Box.profileHi, box_4007]
theorem leaf_4007_BranchSafe : CertificateConsequences.BranchSafe branch_box_4007 := by
  left; refine ⟨branch_box_4007_nonnegative, ?_⟩
  intro z hz; exact leaf_4007_sound hz

theorem leaf_4009_ok : checkAt 527 1000 box_4009 cert_4009 = true := by
  have h := List.all_eq_true.mp batch_80_02_ok accepted_4009 (by simp [batch_80_02_values])
  exact h
theorem leaf_4009_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4009.profileLo box_4009.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4009_ok
theorem branch_box_4009_nonnegative : ∀ j, 0 ≤ branch_box_4009.lower j ∧ 0 ≤ branch_box_4009.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4009, Box.profileLo, Box.profileHi, box_4009]
theorem leaf_4009_BranchSafe : CertificateConsequences.BranchSafe branch_box_4009 := by
  left; refine ⟨branch_box_4009_nonnegative, ?_⟩
  intro z hz; exact leaf_4009_sound hz

theorem leaf_4013_ok : checkAt 527 1000 box_4013 cert_4013 = true := by
  have h := List.all_eq_true.mp batch_80_03_ok accepted_4013 (by simp [batch_80_03_values])
  exact h
theorem leaf_4013_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4013.profileLo box_4013.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4013_ok
theorem branch_box_4013_nonnegative : ∀ j, 0 ≤ branch_box_4013.lower j ∧ 0 ≤ branch_box_4013.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4013, Box.profileLo, Box.profileHi, box_4013]
theorem leaf_4013_BranchSafe : CertificateConsequences.BranchSafe branch_box_4013 := by
  left; refine ⟨branch_box_4013_nonnegative, ?_⟩
  intro z hz; exact leaf_4013_sound hz

theorem leaf_4016_ok : checkAt 527 1000 box_4016 cert_4016 = true := by
  have h := List.all_eq_true.mp batch_80_04_ok accepted_4016 (by simp [batch_80_04_values])
  exact h
theorem leaf_4016_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4016.profileLo box_4016.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4016_ok
theorem branch_box_4016_nonnegative : ∀ j, 0 ≤ branch_box_4016.lower j ∧ 0 ≤ branch_box_4016.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4016, Box.profileLo, Box.profileHi, box_4016]
theorem leaf_4016_BranchSafe : CertificateConsequences.BranchSafe branch_box_4016 := by
  left; refine ⟨branch_box_4016_nonnegative, ?_⟩
  intro z hz; exact leaf_4016_sound hz

theorem leaf_4017_ok : checkAt 527 1000 box_4017 cert_4017 = true := by
  have h := List.all_eq_true.mp batch_80_05_ok accepted_4017 (by simp [batch_80_05_values])
  exact h
theorem leaf_4017_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4017.profileLo box_4017.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4017_ok
theorem branch_box_4017_nonnegative : ∀ j, 0 ≤ branch_box_4017.lower j ∧ 0 ≤ branch_box_4017.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4017, Box.profileLo, Box.profileHi, box_4017]
theorem leaf_4017_BranchSafe : CertificateConsequences.BranchSafe branch_box_4017 := by
  left; refine ⟨branch_box_4017_nonnegative, ?_⟩
  intro z hz; exact leaf_4017_sound hz

theorem leaf_4019_ok : checkAt 527 1000 box_4019 cert_4019 = true := by
  have h := List.all_eq_true.mp batch_80_06_ok accepted_4019 (by simp [batch_80_06_values])
  exact h
theorem leaf_4019_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4019.profileLo box_4019.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4019_ok
theorem branch_box_4019_nonnegative : ∀ j, 0 ≤ branch_box_4019.lower j ∧ 0 ≤ branch_box_4019.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4019, Box.profileLo, Box.profileHi, box_4019]
theorem leaf_4019_BranchSafe : CertificateConsequences.BranchSafe branch_box_4019 := by
  left; refine ⟨branch_box_4019_nonnegative, ?_⟩
  intro z hz; exact leaf_4019_sound hz

theorem leaf_4021_ok : checkAt 527 1000 box_4021 cert_4021 = true := by
  have h := List.all_eq_true.mp batch_80_07_ok accepted_4021 (by simp [batch_80_07_values])
  exact h
theorem leaf_4021_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4021.profileLo box_4021.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4021_ok
theorem branch_box_4021_nonnegative : ∀ j, 0 ≤ branch_box_4021.lower j ∧ 0 ≤ branch_box_4021.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4021, Box.profileLo, Box.profileHi, box_4021]
theorem leaf_4021_BranchSafe : CertificateConsequences.BranchSafe branch_box_4021 := by
  left; refine ⟨branch_box_4021_nonnegative, ?_⟩
  intro z hz; exact leaf_4021_sound hz

theorem leaf_4024_ok : checkAt 527 1000 box_4024 cert_4024 = true := by
  have h := List.all_eq_true.mp batch_80_08_ok accepted_4024 (by simp [batch_80_08_values])
  exact h
theorem leaf_4024_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4024.profileLo box_4024.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4024_ok
theorem branch_box_4024_nonnegative : ∀ j, 0 ≤ branch_box_4024.lower j ∧ 0 ≤ branch_box_4024.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4024, Box.profileLo, Box.profileHi, box_4024]
theorem leaf_4024_BranchSafe : CertificateConsequences.BranchSafe branch_box_4024 := by
  left; refine ⟨branch_box_4024_nonnegative, ?_⟩
  intro z hz; exact leaf_4024_sound hz

theorem leaf_4030_ok : checkAt 527 1000 box_4030 cert_4030 = true := by
  have h := List.all_eq_true.mp batch_80_09_ok accepted_4030 (by simp [batch_80_09_values])
  exact h
theorem leaf_4030_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4030.profileLo box_4030.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4030_ok
theorem branch_box_4030_nonnegative : ∀ j, 0 ≤ branch_box_4030.lower j ∧ 0 ≤ branch_box_4030.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4030, Box.profileLo, Box.profileHi, box_4030]
theorem leaf_4030_BranchSafe : CertificateConsequences.BranchSafe branch_box_4030 := by
  left; refine ⟨branch_box_4030_nonnegative, ?_⟩
  intro z hz; exact leaf_4030_sound hz

theorem leaf_4032_ok : checkAt 527 1000 box_4032 cert_4032 = true := by
  have h := List.all_eq_true.mp batch_80_10_ok accepted_4032 (by simp [batch_80_10_values])
  exact h
theorem leaf_4032_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4032.profileLo box_4032.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4032_ok
theorem branch_box_4032_nonnegative : ∀ j, 0 ≤ branch_box_4032.lower j ∧ 0 ≤ branch_box_4032.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4032, Box.profileLo, Box.profileHi, box_4032]
theorem leaf_4032_BranchSafe : CertificateConsequences.BranchSafe branch_box_4032 := by
  left; refine ⟨branch_box_4032_nonnegative, ?_⟩
  intro z hz; exact leaf_4032_sound hz

theorem leaf_4034_ok : checkAt 527 1000 box_4034 cert_4034 = true := by
  have h := List.all_eq_true.mp batch_80_11_ok accepted_4034 (by simp [batch_80_11_values])
  exact h
theorem leaf_4034_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4034.profileLo box_4034.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4034_ok
theorem branch_box_4034_nonnegative : ∀ j, 0 ≤ branch_box_4034.lower j ∧ 0 ≤ branch_box_4034.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4034, Box.profileLo, Box.profileHi, box_4034]
theorem leaf_4034_BranchSafe : CertificateConsequences.BranchSafe branch_box_4034 := by
  left; refine ⟨branch_box_4034_nonnegative, ?_⟩
  intro z hz; exact leaf_4034_sound hz

theorem leaf_4040_ok : checkAt 527 1000 box_4040 cert_4040 = true := by
  have h := List.all_eq_true.mp batch_80_12_ok accepted_4040 (by simp [batch_80_12_values])
  exact h
theorem leaf_4040_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4040.profileLo box_4040.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4040_ok
theorem branch_box_4040_nonnegative : ∀ j, 0 ≤ branch_box_4040.lower j ∧ 0 ≤ branch_box_4040.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4040, Box.profileLo, Box.profileHi, box_4040]
theorem leaf_4040_BranchSafe : CertificateConsequences.BranchSafe branch_box_4040 := by
  left; refine ⟨branch_box_4040_nonnegative, ?_⟩
  intro z hz; exact leaf_4040_sound hz

theorem leaf_4042_ok : checkAt 527 1000 box_4042 cert_4042 = true := by
  have h := List.all_eq_true.mp batch_80_13_ok accepted_4042 (by simp [batch_80_13_values])
  exact h
theorem leaf_4042_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4042.profileLo box_4042.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4042_ok
theorem branch_box_4042_nonnegative : ∀ j, 0 ≤ branch_box_4042.lower j ∧ 0 ≤ branch_box_4042.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4042, Box.profileLo, Box.profileHi, box_4042]
theorem leaf_4042_BranchSafe : CertificateConsequences.BranchSafe branch_box_4042 := by
  left; refine ⟨branch_box_4042_nonnegative, ?_⟩
  intro z hz; exact leaf_4042_sound hz

theorem leaf_4044_ok : checkAt 527 1000 box_4044 cert_4044 = true := by
  have h := List.all_eq_true.mp batch_80_14_ok accepted_4044 (by simp [batch_80_14_values])
  exact h
theorem leaf_4044_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4044.profileLo box_4044.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4044_ok
theorem branch_box_4044_nonnegative : ∀ j, 0 ≤ branch_box_4044.lower j ∧ 0 ≤ branch_box_4044.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4044, Box.profileLo, Box.profileHi, box_4044]
theorem leaf_4044_BranchSafe : CertificateConsequences.BranchSafe branch_box_4044 := by
  left; refine ⟨branch_box_4044_nonnegative, ?_⟩
  intro z hz; exact leaf_4044_sound hz

theorem leaf_4046_ok : checkAt 527 1000 box_4046 cert_4046 = true := by
  have h := List.all_eq_true.mp batch_80_15_ok accepted_4046 (by simp [batch_80_15_values])
  exact h
theorem leaf_4046_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4046.profileLo box_4046.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4046_ok
theorem branch_box_4046_nonnegative : ∀ j, 0 ≤ branch_box_4046.lower j ∧ 0 ≤ branch_box_4046.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4046, Box.profileLo, Box.profileHi, box_4046]
theorem leaf_4046_BranchSafe : CertificateConsequences.BranchSafe branch_box_4046 := by
  left; refine ⟨branch_box_4046_nonnegative, ?_⟩
  intro z hz; exact leaf_4046_sound hz

theorem leaf_4049_ok : checkAt 527 1000 box_4049 cert_4049 = true := by
  have h := List.all_eq_true.mp batch_80_16_ok accepted_4049 (by simp [batch_80_16_values])
  exact h
theorem leaf_4049_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4049.profileLo box_4049.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4049_ok
theorem branch_box_4049_nonnegative : ∀ j, 0 ≤ branch_box_4049.lower j ∧ 0 ≤ branch_box_4049.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4049, Box.profileLo, Box.profileHi, box_4049]
theorem leaf_4049_BranchSafe : CertificateConsequences.BranchSafe branch_box_4049 := by
  left; refine ⟨branch_box_4049_nonnegative, ?_⟩
  intro z hz; exact leaf_4049_sound hz

#print axioms batch_80_00_ok
#print axioms leaf_4004_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
