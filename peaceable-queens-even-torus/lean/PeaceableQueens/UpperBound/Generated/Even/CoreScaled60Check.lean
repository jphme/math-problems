import PeaceableQueens.UpperBound.Generated.Even.CoreScaled60Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_60_00_values : List Bool := [accepted_3000]
theorem batch_60_00_ok : batch_60_00_values.all id = true := by decide

def batch_60_01_values : List Bool := [accepted_3002]
theorem batch_60_01_ok : batch_60_01_values.all id = true := by decide

def batch_60_02_values : List Bool := [accepted_3003]
theorem batch_60_02_ok : batch_60_02_values.all id = true := by decide

def batch_60_03_values : List Bool := [accepted_3006]
theorem batch_60_03_ok : batch_60_03_values.all id = true := by decide

def batch_60_04_values : List Bool := [accepted_3008]
theorem batch_60_04_ok : batch_60_04_values.all id = true := by decide

def batch_60_05_values : List Bool := [accepted_3010]
theorem batch_60_05_ok : batch_60_05_values.all id = true := by decide

def batch_60_06_values : List Bool := [accepted_3012]
theorem batch_60_06_ok : batch_60_06_values.all id = true := by decide

def batch_60_07_values : List Bool := [accepted_3015]
theorem batch_60_07_ok : batch_60_07_values.all id = true := by decide

def batch_60_08_values : List Bool := [accepted_3018]
theorem batch_60_08_ok : batch_60_08_values.all id = true := by decide

def batch_60_09_values : List Bool := [accepted_3022]
theorem batch_60_09_ok : batch_60_09_values.all id = true := by decide

def batch_60_10_values : List Bool := [accepted_3024]
theorem batch_60_10_ok : batch_60_10_values.all id = true := by decide

def batch_60_11_values : List Bool := [accepted_3028]
theorem batch_60_11_ok : batch_60_11_values.all id = true := by decide

def batch_60_12_values : List Bool := [accepted_3029]
theorem batch_60_12_ok : batch_60_12_values.all id = true := by decide

def batch_60_13_values : List Bool := [accepted_3031]
theorem batch_60_13_ok : batch_60_13_values.all id = true := by decide

def batch_60_14_values : List Bool := [accepted_3034]
theorem batch_60_14_ok : batch_60_14_values.all id = true := by decide

def batch_60_15_values : List Bool := [accepted_3036]
theorem batch_60_15_ok : batch_60_15_values.all id = true := by decide

def batch_60_16_values : List Bool := [accepted_3038]
theorem batch_60_16_ok : batch_60_16_values.all id = true := by decide

def batch_60_17_values : List Bool := [accepted_3040]
theorem batch_60_17_ok : batch_60_17_values.all id = true := by decide

def batch_60_18_values : List Bool := [accepted_3041]
theorem batch_60_18_ok : batch_60_18_values.all id = true := by decide

def batch_60_19_values : List Bool := [accepted_3044]
theorem batch_60_19_ok : batch_60_19_values.all id = true := by decide

def batch_60_20_values : List Bool := [accepted_3046]
theorem batch_60_20_ok : batch_60_20_values.all id = true := by decide

def batch_60_21_values : List Bool := [accepted_3048]
theorem batch_60_21_ok : batch_60_21_values.all id = true := by decide

def batch_60_22_values : List Bool := [accepted_3049]
theorem batch_60_22_ok : batch_60_22_values.all id = true := by decide

theorem leaf_3000_ok : checkAt 527 1000 box_3000 cert_3000 = true := by
  have h := List.all_eq_true.mp batch_60_00_ok accepted_3000 (by simp [batch_60_00_values])
  exact h
theorem leaf_3000_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3000.profileLo box_3000.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3000_ok
theorem branch_box_3000_nonnegative : ∀ j, 0 ≤ branch_box_3000.lower j ∧ 0 ≤ branch_box_3000.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3000, Box.profileLo, Box.profileHi, box_3000]
theorem leaf_3000_BranchSafe : CertificateConsequences.BranchSafe branch_box_3000 := by
  left; refine ⟨branch_box_3000_nonnegative, ?_⟩
  intro z hz; exact leaf_3000_sound hz

theorem leaf_3002_ok : checkAt 527 1000 box_3002 cert_3002 = true := by
  have h := List.all_eq_true.mp batch_60_01_ok accepted_3002 (by simp [batch_60_01_values])
  exact h
theorem leaf_3002_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3002.profileLo box_3002.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3002_ok
theorem branch_box_3002_nonnegative : ∀ j, 0 ≤ branch_box_3002.lower j ∧ 0 ≤ branch_box_3002.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3002, Box.profileLo, Box.profileHi, box_3002]
theorem leaf_3002_BranchSafe : CertificateConsequences.BranchSafe branch_box_3002 := by
  left; refine ⟨branch_box_3002_nonnegative, ?_⟩
  intro z hz; exact leaf_3002_sound hz

theorem leaf_3003_ok : checkAt 527 1000 box_3003 cert_3003 = true := by
  have h := List.all_eq_true.mp batch_60_02_ok accepted_3003 (by simp [batch_60_02_values])
  exact h
theorem leaf_3003_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3003.profileLo box_3003.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3003_ok
theorem branch_box_3003_nonnegative : ∀ j, 0 ≤ branch_box_3003.lower j ∧ 0 ≤ branch_box_3003.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3003, Box.profileLo, Box.profileHi, box_3003]
theorem leaf_3003_BranchSafe : CertificateConsequences.BranchSafe branch_box_3003 := by
  left; refine ⟨branch_box_3003_nonnegative, ?_⟩
  intro z hz; exact leaf_3003_sound hz

theorem leaf_3006_ok : checkAt 527 1000 box_3006 cert_3006 = true := by
  have h := List.all_eq_true.mp batch_60_03_ok accepted_3006 (by simp [batch_60_03_values])
  exact h
theorem leaf_3006_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3006.profileLo box_3006.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3006_ok
theorem branch_box_3006_nonnegative : ∀ j, 0 ≤ branch_box_3006.lower j ∧ 0 ≤ branch_box_3006.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3006, Box.profileLo, Box.profileHi, box_3006]
theorem leaf_3006_BranchSafe : CertificateConsequences.BranchSafe branch_box_3006 := by
  left; refine ⟨branch_box_3006_nonnegative, ?_⟩
  intro z hz; exact leaf_3006_sound hz

theorem leaf_3008_ok : checkAt 527 1000 box_3008 cert_3008 = true := by
  have h := List.all_eq_true.mp batch_60_04_ok accepted_3008 (by simp [batch_60_04_values])
  exact h
theorem leaf_3008_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3008.profileLo box_3008.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3008_ok
theorem branch_box_3008_nonnegative : ∀ j, 0 ≤ branch_box_3008.lower j ∧ 0 ≤ branch_box_3008.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3008, Box.profileLo, Box.profileHi, box_3008]
theorem leaf_3008_BranchSafe : CertificateConsequences.BranchSafe branch_box_3008 := by
  left; refine ⟨branch_box_3008_nonnegative, ?_⟩
  intro z hz; exact leaf_3008_sound hz

theorem leaf_3010_ok : checkAt 527 1000 box_3010 cert_3010 = true := by
  have h := List.all_eq_true.mp batch_60_05_ok accepted_3010 (by simp [batch_60_05_values])
  exact h
theorem leaf_3010_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3010.profileLo box_3010.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3010_ok
theorem branch_box_3010_nonnegative : ∀ j, 0 ≤ branch_box_3010.lower j ∧ 0 ≤ branch_box_3010.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3010, Box.profileLo, Box.profileHi, box_3010]
theorem leaf_3010_BranchSafe : CertificateConsequences.BranchSafe branch_box_3010 := by
  left; refine ⟨branch_box_3010_nonnegative, ?_⟩
  intro z hz; exact leaf_3010_sound hz

theorem leaf_3012_ok : checkAt 527 1000 box_3012 cert_3012 = true := by
  have h := List.all_eq_true.mp batch_60_06_ok accepted_3012 (by simp [batch_60_06_values])
  exact h
theorem leaf_3012_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3012.profileLo box_3012.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3012_ok
theorem branch_box_3012_nonnegative : ∀ j, 0 ≤ branch_box_3012.lower j ∧ 0 ≤ branch_box_3012.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3012, Box.profileLo, Box.profileHi, box_3012]
theorem leaf_3012_BranchSafe : CertificateConsequences.BranchSafe branch_box_3012 := by
  left; refine ⟨branch_box_3012_nonnegative, ?_⟩
  intro z hz; exact leaf_3012_sound hz

theorem leaf_3015_ok : checkAt 527 1000 box_3015 cert_3015 = true := by
  have h := List.all_eq_true.mp batch_60_07_ok accepted_3015 (by simp [batch_60_07_values])
  exact h
theorem leaf_3015_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3015.profileLo box_3015.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3015_ok
theorem branch_box_3015_nonnegative : ∀ j, 0 ≤ branch_box_3015.lower j ∧ 0 ≤ branch_box_3015.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3015, Box.profileLo, Box.profileHi, box_3015]
theorem leaf_3015_BranchSafe : CertificateConsequences.BranchSafe branch_box_3015 := by
  left; refine ⟨branch_box_3015_nonnegative, ?_⟩
  intro z hz; exact leaf_3015_sound hz

theorem leaf_3018_ok : checkAt 527 1000 box_3018 cert_3018 = true := by
  have h := List.all_eq_true.mp batch_60_08_ok accepted_3018 (by simp [batch_60_08_values])
  exact h
theorem leaf_3018_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3018.profileLo box_3018.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3018_ok
theorem branch_box_3018_nonnegative : ∀ j, 0 ≤ branch_box_3018.lower j ∧ 0 ≤ branch_box_3018.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3018, Box.profileLo, Box.profileHi, box_3018]
theorem leaf_3018_BranchSafe : CertificateConsequences.BranchSafe branch_box_3018 := by
  left; refine ⟨branch_box_3018_nonnegative, ?_⟩
  intro z hz; exact leaf_3018_sound hz

theorem leaf_3022_ok : checkAt 527 1000 box_3022 cert_3022 = true := by
  have h := List.all_eq_true.mp batch_60_09_ok accepted_3022 (by simp [batch_60_09_values])
  exact h
theorem leaf_3022_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3022.profileLo box_3022.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3022_ok
theorem branch_box_3022_nonnegative : ∀ j, 0 ≤ branch_box_3022.lower j ∧ 0 ≤ branch_box_3022.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3022, Box.profileLo, Box.profileHi, box_3022]
theorem leaf_3022_BranchSafe : CertificateConsequences.BranchSafe branch_box_3022 := by
  left; refine ⟨branch_box_3022_nonnegative, ?_⟩
  intro z hz; exact leaf_3022_sound hz

theorem leaf_3024_ok : checkAt 527 1000 box_3024 cert_3024 = true := by
  have h := List.all_eq_true.mp batch_60_10_ok accepted_3024 (by simp [batch_60_10_values])
  exact h
theorem leaf_3024_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3024.profileLo box_3024.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3024_ok
theorem branch_box_3024_nonnegative : ∀ j, 0 ≤ branch_box_3024.lower j ∧ 0 ≤ branch_box_3024.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3024, Box.profileLo, Box.profileHi, box_3024]
theorem leaf_3024_BranchSafe : CertificateConsequences.BranchSafe branch_box_3024 := by
  left; refine ⟨branch_box_3024_nonnegative, ?_⟩
  intro z hz; exact leaf_3024_sound hz

theorem leaf_3028_ok : checkAt 527 1000 box_3028 cert_3028 = true := by
  have h := List.all_eq_true.mp batch_60_11_ok accepted_3028 (by simp [batch_60_11_values])
  exact h
theorem leaf_3028_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3028.profileLo box_3028.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3028_ok
theorem branch_box_3028_nonnegative : ∀ j, 0 ≤ branch_box_3028.lower j ∧ 0 ≤ branch_box_3028.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3028, Box.profileLo, Box.profileHi, box_3028]
theorem leaf_3028_BranchSafe : CertificateConsequences.BranchSafe branch_box_3028 := by
  left; refine ⟨branch_box_3028_nonnegative, ?_⟩
  intro z hz; exact leaf_3028_sound hz

theorem leaf_3029_ok : checkAt 527 1000 box_3029 cert_3029 = true := by
  have h := List.all_eq_true.mp batch_60_12_ok accepted_3029 (by simp [batch_60_12_values])
  exact h
theorem leaf_3029_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3029.profileLo box_3029.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3029_ok
theorem branch_box_3029_nonnegative : ∀ j, 0 ≤ branch_box_3029.lower j ∧ 0 ≤ branch_box_3029.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3029, Box.profileLo, Box.profileHi, box_3029]
theorem leaf_3029_BranchSafe : CertificateConsequences.BranchSafe branch_box_3029 := by
  left; refine ⟨branch_box_3029_nonnegative, ?_⟩
  intro z hz; exact leaf_3029_sound hz

theorem leaf_3031_ok : checkAt 527 1000 box_3031 cert_3031 = true := by
  have h := List.all_eq_true.mp batch_60_13_ok accepted_3031 (by simp [batch_60_13_values])
  exact h
theorem leaf_3031_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3031.profileLo box_3031.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3031_ok
theorem branch_box_3031_nonnegative : ∀ j, 0 ≤ branch_box_3031.lower j ∧ 0 ≤ branch_box_3031.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3031, Box.profileLo, Box.profileHi, box_3031]
theorem leaf_3031_BranchSafe : CertificateConsequences.BranchSafe branch_box_3031 := by
  left; refine ⟨branch_box_3031_nonnegative, ?_⟩
  intro z hz; exact leaf_3031_sound hz

theorem leaf_3034_ok : checkAt 527 1000 box_3034 cert_3034 = true := by
  have h := List.all_eq_true.mp batch_60_14_ok accepted_3034 (by simp [batch_60_14_values])
  exact h
theorem leaf_3034_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3034.profileLo box_3034.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3034_ok
theorem branch_box_3034_nonnegative : ∀ j, 0 ≤ branch_box_3034.lower j ∧ 0 ≤ branch_box_3034.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3034, Box.profileLo, Box.profileHi, box_3034]
theorem leaf_3034_BranchSafe : CertificateConsequences.BranchSafe branch_box_3034 := by
  left; refine ⟨branch_box_3034_nonnegative, ?_⟩
  intro z hz; exact leaf_3034_sound hz

theorem leaf_3036_ok : checkAt 527 1000 box_3036 cert_3036 = true := by
  have h := List.all_eq_true.mp batch_60_15_ok accepted_3036 (by simp [batch_60_15_values])
  exact h
theorem leaf_3036_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3036.profileLo box_3036.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3036_ok
theorem branch_box_3036_nonnegative : ∀ j, 0 ≤ branch_box_3036.lower j ∧ 0 ≤ branch_box_3036.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3036, Box.profileLo, Box.profileHi, box_3036]
theorem leaf_3036_BranchSafe : CertificateConsequences.BranchSafe branch_box_3036 := by
  left; refine ⟨branch_box_3036_nonnegative, ?_⟩
  intro z hz; exact leaf_3036_sound hz

theorem leaf_3038_ok : checkAt 527 1000 box_3038 cert_3038 = true := by
  have h := List.all_eq_true.mp batch_60_16_ok accepted_3038 (by simp [batch_60_16_values])
  exact h
theorem leaf_3038_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3038.profileLo box_3038.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3038_ok
theorem branch_box_3038_nonnegative : ∀ j, 0 ≤ branch_box_3038.lower j ∧ 0 ≤ branch_box_3038.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3038, Box.profileLo, Box.profileHi, box_3038]
theorem leaf_3038_BranchSafe : CertificateConsequences.BranchSafe branch_box_3038 := by
  left; refine ⟨branch_box_3038_nonnegative, ?_⟩
  intro z hz; exact leaf_3038_sound hz

theorem leaf_3040_ok : checkAt 527 1000 box_3040 cert_3040 = true := by
  have h := List.all_eq_true.mp batch_60_17_ok accepted_3040 (by simp [batch_60_17_values])
  exact h
theorem leaf_3040_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3040.profileLo box_3040.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3040_ok
theorem branch_box_3040_nonnegative : ∀ j, 0 ≤ branch_box_3040.lower j ∧ 0 ≤ branch_box_3040.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3040, Box.profileLo, Box.profileHi, box_3040]
theorem leaf_3040_BranchSafe : CertificateConsequences.BranchSafe branch_box_3040 := by
  left; refine ⟨branch_box_3040_nonnegative, ?_⟩
  intro z hz; exact leaf_3040_sound hz

theorem leaf_3041_ok : checkAt 527 1000 box_3041 cert_3041 = true := by
  have h := List.all_eq_true.mp batch_60_18_ok accepted_3041 (by simp [batch_60_18_values])
  exact h
theorem leaf_3041_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3041.profileLo box_3041.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3041_ok
theorem branch_box_3041_nonnegative : ∀ j, 0 ≤ branch_box_3041.lower j ∧ 0 ≤ branch_box_3041.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3041, Box.profileLo, Box.profileHi, box_3041]
theorem leaf_3041_BranchSafe : CertificateConsequences.BranchSafe branch_box_3041 := by
  left; refine ⟨branch_box_3041_nonnegative, ?_⟩
  intro z hz; exact leaf_3041_sound hz

theorem leaf_3044_ok : checkAt 527 1000 box_3044 cert_3044 = true := by
  have h := List.all_eq_true.mp batch_60_19_ok accepted_3044 (by simp [batch_60_19_values])
  exact h
theorem leaf_3044_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3044.profileLo box_3044.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3044_ok
theorem branch_box_3044_nonnegative : ∀ j, 0 ≤ branch_box_3044.lower j ∧ 0 ≤ branch_box_3044.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3044, Box.profileLo, Box.profileHi, box_3044]
theorem leaf_3044_BranchSafe : CertificateConsequences.BranchSafe branch_box_3044 := by
  left; refine ⟨branch_box_3044_nonnegative, ?_⟩
  intro z hz; exact leaf_3044_sound hz

theorem leaf_3046_ok : checkAt 527 1000 box_3046 cert_3046 = true := by
  have h := List.all_eq_true.mp batch_60_20_ok accepted_3046 (by simp [batch_60_20_values])
  exact h
theorem leaf_3046_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3046.profileLo box_3046.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3046_ok
theorem branch_box_3046_nonnegative : ∀ j, 0 ≤ branch_box_3046.lower j ∧ 0 ≤ branch_box_3046.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3046, Box.profileLo, Box.profileHi, box_3046]
theorem leaf_3046_BranchSafe : CertificateConsequences.BranchSafe branch_box_3046 := by
  left; refine ⟨branch_box_3046_nonnegative, ?_⟩
  intro z hz; exact leaf_3046_sound hz

theorem leaf_3048_ok : checkAt 527 1000 box_3048 cert_3048 = true := by
  have h := List.all_eq_true.mp batch_60_21_ok accepted_3048 (by simp [batch_60_21_values])
  exact h
theorem leaf_3048_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3048.profileLo box_3048.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3048_ok
theorem branch_box_3048_nonnegative : ∀ j, 0 ≤ branch_box_3048.lower j ∧ 0 ≤ branch_box_3048.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3048, Box.profileLo, Box.profileHi, box_3048]
theorem leaf_3048_BranchSafe : CertificateConsequences.BranchSafe branch_box_3048 := by
  left; refine ⟨branch_box_3048_nonnegative, ?_⟩
  intro z hz; exact leaf_3048_sound hz

theorem leaf_3049_ok : checkAt 527 1000 box_3049 cert_3049 = true := by
  have h := List.all_eq_true.mp batch_60_22_ok accepted_3049 (by simp [batch_60_22_values])
  exact h
theorem leaf_3049_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3049.profileLo box_3049.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3049_ok
theorem branch_box_3049_nonnegative : ∀ j, 0 ≤ branch_box_3049.lower j ∧ 0 ≤ branch_box_3049.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3049, Box.profileLo, Box.profileHi, box_3049]
theorem leaf_3049_BranchSafe : CertificateConsequences.BranchSafe branch_box_3049 := by
  left; refine ⟨branch_box_3049_nonnegative, ?_⟩
  intro z hz; exact leaf_3049_sound hz

#print axioms batch_60_00_ok
#print axioms leaf_3000_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
