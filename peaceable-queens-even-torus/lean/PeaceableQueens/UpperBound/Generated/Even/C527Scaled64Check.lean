import PeaceableQueens.UpperBound.Generated.Even.C527Scaled64Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_64_00_values : List Bool := [accepted_3200]
theorem batch_64_00_ok : batch_64_00_values.all id = true := by decide

def batch_64_01_values : List Bool := [accepted_3205]
theorem batch_64_01_ok : batch_64_01_values.all id = true := by decide

def batch_64_02_values : List Bool := [accepted_3206]
theorem batch_64_02_ok : batch_64_02_values.all id = true := by decide

def batch_64_03_values : List Bool := [accepted_3207]
theorem batch_64_03_ok : batch_64_03_values.all id = true := by decide

def batch_64_04_values : List Bool := [accepted_3208]
theorem batch_64_04_ok : batch_64_04_values.all id = true := by decide

def batch_64_05_values : List Bool := [accepted_3213]
theorem batch_64_05_ok : batch_64_05_values.all id = true := by decide

def batch_64_06_values : List Bool := [accepted_3215]
theorem batch_64_06_ok : batch_64_06_values.all id = true := by decide

def batch_64_07_values : List Bool := [accepted_3216]
theorem batch_64_07_ok : batch_64_07_values.all id = true := by decide

def batch_64_08_values : List Bool := [accepted_3217]
theorem batch_64_08_ok : batch_64_08_values.all id = true := by decide

def batch_64_09_values : List Bool := [accepted_3218]
theorem batch_64_09_ok : batch_64_09_values.all id = true := by decide

def batch_64_10_values : List Bool := [accepted_3221]
theorem batch_64_10_ok : batch_64_10_values.all id = true := by decide

def batch_64_11_values : List Bool := [accepted_3222]
theorem batch_64_11_ok : batch_64_11_values.all id = true := by decide

def batch_64_12_values : List Bool := [accepted_3223]
theorem batch_64_12_ok : batch_64_12_values.all id = true := by decide

def batch_64_13_values : List Bool := [accepted_3225]
theorem batch_64_13_ok : batch_64_13_values.all id = true := by decide

def batch_64_14_values : List Bool := [accepted_3226]
theorem batch_64_14_ok : batch_64_14_values.all id = true := by decide

def batch_64_15_values : List Bool := [accepted_3231]
theorem batch_64_15_ok : batch_64_15_values.all id = true := by decide

def batch_64_16_values : List Bool := [accepted_3233]
theorem batch_64_16_ok : batch_64_16_values.all id = true := by decide

def batch_64_17_values : List Bool := [accepted_3234]
theorem batch_64_17_ok : batch_64_17_values.all id = true := by decide

def batch_64_18_values : List Bool := [accepted_3237]
theorem batch_64_18_ok : batch_64_18_values.all id = true := by decide

def batch_64_19_values : List Bool := [accepted_3241]
theorem batch_64_19_ok : batch_64_19_values.all id = true := by decide

def batch_64_20_values : List Bool := [accepted_3243]
theorem batch_64_20_ok : batch_64_20_values.all id = true := by decide

def batch_64_21_values : List Bool := [accepted_3244]
theorem batch_64_21_ok : batch_64_21_values.all id = true := by decide

def batch_64_22_values : List Bool := [accepted_3245]
theorem batch_64_22_ok : batch_64_22_values.all id = true := by decide

def batch_64_23_values : List Bool := [accepted_3246]
theorem batch_64_23_ok : batch_64_23_values.all id = true := by decide

def batch_64_24_values : List Bool := [accepted_3247]
theorem batch_64_24_ok : batch_64_24_values.all id = true := by decide

def batch_64_25_values : List Bool := [accepted_3249]
theorem batch_64_25_ok : batch_64_25_values.all id = true := by decide

theorem leaf_3200_ok : checkAt 527 1000 box_3200 cert_3200 = true := by
  have h := List.all_eq_true.mp batch_64_00_ok accepted_3200 (by simp [batch_64_00_values])
  exact h
theorem leaf_3200_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3200.profileLo box_3200.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3200_ok
theorem branch_box_3200_nonnegative : ∀ j, 0 ≤ branch_box_3200.lower j ∧ 0 ≤ branch_box_3200.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3200, Box.profileLo, Box.profileHi, box_3200]
theorem leaf_3200_BranchSafe : CertificateConsequences.BranchSafe branch_box_3200 := by
  left; refine ⟨branch_box_3200_nonnegative, ?_⟩
  intro z hz; exact leaf_3200_sound hz

theorem leaf_3205_ok : checkAt 527 1000 box_3205 cert_3205 = true := by
  have h := List.all_eq_true.mp batch_64_01_ok accepted_3205 (by simp [batch_64_01_values])
  exact h
theorem leaf_3205_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3205.profileLo box_3205.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3205_ok
theorem branch_box_3205_nonnegative : ∀ j, 0 ≤ branch_box_3205.lower j ∧ 0 ≤ branch_box_3205.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3205, Box.profileLo, Box.profileHi, box_3205]
theorem leaf_3205_BranchSafe : CertificateConsequences.BranchSafe branch_box_3205 := by
  left; refine ⟨branch_box_3205_nonnegative, ?_⟩
  intro z hz; exact leaf_3205_sound hz

theorem leaf_3206_ok : checkAt 527 1000 box_3206 cert_3206 = true := by
  have h := List.all_eq_true.mp batch_64_02_ok accepted_3206 (by simp [batch_64_02_values])
  exact h
theorem leaf_3206_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3206.profileLo box_3206.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3206_ok
theorem branch_box_3206_nonnegative : ∀ j, 0 ≤ branch_box_3206.lower j ∧ 0 ≤ branch_box_3206.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3206, Box.profileLo, Box.profileHi, box_3206]
theorem leaf_3206_BranchSafe : CertificateConsequences.BranchSafe branch_box_3206 := by
  left; refine ⟨branch_box_3206_nonnegative, ?_⟩
  intro z hz; exact leaf_3206_sound hz

theorem leaf_3207_ok : checkAt 527 1000 box_3207 cert_3207 = true := by
  have h := List.all_eq_true.mp batch_64_03_ok accepted_3207 (by simp [batch_64_03_values])
  exact h
theorem leaf_3207_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3207.profileLo box_3207.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3207_ok
theorem branch_box_3207_nonnegative : ∀ j, 0 ≤ branch_box_3207.lower j ∧ 0 ≤ branch_box_3207.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3207, Box.profileLo, Box.profileHi, box_3207]
theorem leaf_3207_BranchSafe : CertificateConsequences.BranchSafe branch_box_3207 := by
  left; refine ⟨branch_box_3207_nonnegative, ?_⟩
  intro z hz; exact leaf_3207_sound hz

theorem leaf_3208_ok : checkAt 527 1000 box_3208 cert_3208 = true := by
  have h := List.all_eq_true.mp batch_64_04_ok accepted_3208 (by simp [batch_64_04_values])
  exact h
theorem leaf_3208_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3208.profileLo box_3208.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3208_ok
theorem branch_box_3208_nonnegative : ∀ j, 0 ≤ branch_box_3208.lower j ∧ 0 ≤ branch_box_3208.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3208, Box.profileLo, Box.profileHi, box_3208]
theorem leaf_3208_BranchSafe : CertificateConsequences.BranchSafe branch_box_3208 := by
  left; refine ⟨branch_box_3208_nonnegative, ?_⟩
  intro z hz; exact leaf_3208_sound hz

theorem leaf_3213_ok : checkAt 527 1000 box_3213 cert_3213 = true := by
  have h := List.all_eq_true.mp batch_64_05_ok accepted_3213 (by simp [batch_64_05_values])
  exact h
theorem leaf_3213_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3213.profileLo box_3213.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3213_ok
theorem branch_box_3213_nonnegative : ∀ j, 0 ≤ branch_box_3213.lower j ∧ 0 ≤ branch_box_3213.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3213, Box.profileLo, Box.profileHi, box_3213]
theorem leaf_3213_BranchSafe : CertificateConsequences.BranchSafe branch_box_3213 := by
  left; refine ⟨branch_box_3213_nonnegative, ?_⟩
  intro z hz; exact leaf_3213_sound hz

theorem leaf_3215_ok : checkAt 527 1000 box_3215 cert_3215 = true := by
  have h := List.all_eq_true.mp batch_64_06_ok accepted_3215 (by simp [batch_64_06_values])
  exact h
theorem leaf_3215_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3215.profileLo box_3215.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3215_ok
theorem branch_box_3215_nonnegative : ∀ j, 0 ≤ branch_box_3215.lower j ∧ 0 ≤ branch_box_3215.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3215, Box.profileLo, Box.profileHi, box_3215]
theorem leaf_3215_BranchSafe : CertificateConsequences.BranchSafe branch_box_3215 := by
  left; refine ⟨branch_box_3215_nonnegative, ?_⟩
  intro z hz; exact leaf_3215_sound hz

theorem leaf_3216_ok : checkAt 527 1000 box_3216 cert_3216 = true := by
  have h := List.all_eq_true.mp batch_64_07_ok accepted_3216 (by simp [batch_64_07_values])
  exact h
theorem leaf_3216_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3216.profileLo box_3216.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3216_ok
theorem branch_box_3216_nonnegative : ∀ j, 0 ≤ branch_box_3216.lower j ∧ 0 ≤ branch_box_3216.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3216, Box.profileLo, Box.profileHi, box_3216]
theorem leaf_3216_BranchSafe : CertificateConsequences.BranchSafe branch_box_3216 := by
  left; refine ⟨branch_box_3216_nonnegative, ?_⟩
  intro z hz; exact leaf_3216_sound hz

theorem leaf_3217_ok : checkAt 527 1000 box_3217 cert_3217 = true := by
  have h := List.all_eq_true.mp batch_64_08_ok accepted_3217 (by simp [batch_64_08_values])
  exact h
theorem leaf_3217_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3217.profileLo box_3217.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3217_ok
theorem branch_box_3217_nonnegative : ∀ j, 0 ≤ branch_box_3217.lower j ∧ 0 ≤ branch_box_3217.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3217, Box.profileLo, Box.profileHi, box_3217]
theorem leaf_3217_BranchSafe : CertificateConsequences.BranchSafe branch_box_3217 := by
  left; refine ⟨branch_box_3217_nonnegative, ?_⟩
  intro z hz; exact leaf_3217_sound hz

theorem leaf_3218_ok : checkAt 527 1000 box_3218 cert_3218 = true := by
  have h := List.all_eq_true.mp batch_64_09_ok accepted_3218 (by simp [batch_64_09_values])
  exact h
theorem leaf_3218_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3218.profileLo box_3218.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3218_ok
theorem branch_box_3218_nonnegative : ∀ j, 0 ≤ branch_box_3218.lower j ∧ 0 ≤ branch_box_3218.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3218, Box.profileLo, Box.profileHi, box_3218]
theorem leaf_3218_BranchSafe : CertificateConsequences.BranchSafe branch_box_3218 := by
  left; refine ⟨branch_box_3218_nonnegative, ?_⟩
  intro z hz; exact leaf_3218_sound hz

theorem leaf_3221_ok : checkAt 527 1000 box_3221 cert_3221 = true := by
  have h := List.all_eq_true.mp batch_64_10_ok accepted_3221 (by simp [batch_64_10_values])
  exact h
theorem leaf_3221_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3221.profileLo box_3221.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3221_ok
theorem branch_box_3221_nonnegative : ∀ j, 0 ≤ branch_box_3221.lower j ∧ 0 ≤ branch_box_3221.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3221, Box.profileLo, Box.profileHi, box_3221]
theorem leaf_3221_BranchSafe : CertificateConsequences.BranchSafe branch_box_3221 := by
  left; refine ⟨branch_box_3221_nonnegative, ?_⟩
  intro z hz; exact leaf_3221_sound hz

theorem leaf_3222_ok : checkAt 527 1000 box_3222 cert_3222 = true := by
  have h := List.all_eq_true.mp batch_64_11_ok accepted_3222 (by simp [batch_64_11_values])
  exact h
theorem leaf_3222_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3222.profileLo box_3222.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3222_ok
theorem branch_box_3222_nonnegative : ∀ j, 0 ≤ branch_box_3222.lower j ∧ 0 ≤ branch_box_3222.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3222, Box.profileLo, Box.profileHi, box_3222]
theorem leaf_3222_BranchSafe : CertificateConsequences.BranchSafe branch_box_3222 := by
  left; refine ⟨branch_box_3222_nonnegative, ?_⟩
  intro z hz; exact leaf_3222_sound hz

theorem leaf_3223_ok : checkAt 527 1000 box_3223 cert_3223 = true := by
  have h := List.all_eq_true.mp batch_64_12_ok accepted_3223 (by simp [batch_64_12_values])
  exact h
theorem leaf_3223_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3223.profileLo box_3223.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3223_ok
theorem branch_box_3223_nonnegative : ∀ j, 0 ≤ branch_box_3223.lower j ∧ 0 ≤ branch_box_3223.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3223, Box.profileLo, Box.profileHi, box_3223]
theorem leaf_3223_BranchSafe : CertificateConsequences.BranchSafe branch_box_3223 := by
  left; refine ⟨branch_box_3223_nonnegative, ?_⟩
  intro z hz; exact leaf_3223_sound hz

theorem leaf_3225_ok : checkAt 527 1000 box_3225 cert_3225 = true := by
  have h := List.all_eq_true.mp batch_64_13_ok accepted_3225 (by simp [batch_64_13_values])
  exact h
theorem leaf_3225_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3225.profileLo box_3225.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3225_ok
theorem branch_box_3225_nonnegative : ∀ j, 0 ≤ branch_box_3225.lower j ∧ 0 ≤ branch_box_3225.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3225, Box.profileLo, Box.profileHi, box_3225]
theorem leaf_3225_BranchSafe : CertificateConsequences.BranchSafe branch_box_3225 := by
  left; refine ⟨branch_box_3225_nonnegative, ?_⟩
  intro z hz; exact leaf_3225_sound hz

theorem leaf_3226_ok : checkAt 527 1000 box_3226 cert_3226 = true := by
  have h := List.all_eq_true.mp batch_64_14_ok accepted_3226 (by simp [batch_64_14_values])
  exact h
theorem leaf_3226_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3226.profileLo box_3226.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3226_ok
theorem branch_box_3226_nonnegative : ∀ j, 0 ≤ branch_box_3226.lower j ∧ 0 ≤ branch_box_3226.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3226, Box.profileLo, Box.profileHi, box_3226]
theorem leaf_3226_BranchSafe : CertificateConsequences.BranchSafe branch_box_3226 := by
  left; refine ⟨branch_box_3226_nonnegative, ?_⟩
  intro z hz; exact leaf_3226_sound hz

theorem leaf_3231_ok : checkAt 527 1000 box_3231 cert_3231 = true := by
  have h := List.all_eq_true.mp batch_64_15_ok accepted_3231 (by simp [batch_64_15_values])
  exact h
theorem leaf_3231_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3231.profileLo box_3231.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3231_ok
theorem branch_box_3231_nonnegative : ∀ j, 0 ≤ branch_box_3231.lower j ∧ 0 ≤ branch_box_3231.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3231, Box.profileLo, Box.profileHi, box_3231]
theorem leaf_3231_BranchSafe : CertificateConsequences.BranchSafe branch_box_3231 := by
  left; refine ⟨branch_box_3231_nonnegative, ?_⟩
  intro z hz; exact leaf_3231_sound hz

theorem leaf_3233_ok : checkAt 527 1000 box_3233 cert_3233 = true := by
  have h := List.all_eq_true.mp batch_64_16_ok accepted_3233 (by simp [batch_64_16_values])
  exact h
theorem leaf_3233_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3233.profileLo box_3233.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3233_ok
theorem branch_box_3233_nonnegative : ∀ j, 0 ≤ branch_box_3233.lower j ∧ 0 ≤ branch_box_3233.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3233, Box.profileLo, Box.profileHi, box_3233]
theorem leaf_3233_BranchSafe : CertificateConsequences.BranchSafe branch_box_3233 := by
  left; refine ⟨branch_box_3233_nonnegative, ?_⟩
  intro z hz; exact leaf_3233_sound hz

theorem leaf_3234_ok : checkAt 527 1000 box_3234 cert_3234 = true := by
  have h := List.all_eq_true.mp batch_64_17_ok accepted_3234 (by simp [batch_64_17_values])
  exact h
theorem leaf_3234_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3234.profileLo box_3234.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3234_ok
theorem branch_box_3234_nonnegative : ∀ j, 0 ≤ branch_box_3234.lower j ∧ 0 ≤ branch_box_3234.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3234, Box.profileLo, Box.profileHi, box_3234]
theorem leaf_3234_BranchSafe : CertificateConsequences.BranchSafe branch_box_3234 := by
  left; refine ⟨branch_box_3234_nonnegative, ?_⟩
  intro z hz; exact leaf_3234_sound hz

theorem leaf_3237_ok : checkAt 527 1000 box_3237 cert_3237 = true := by
  have h := List.all_eq_true.mp batch_64_18_ok accepted_3237 (by simp [batch_64_18_values])
  exact h
theorem leaf_3237_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3237.profileLo box_3237.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3237_ok
theorem branch_box_3237_nonnegative : ∀ j, 0 ≤ branch_box_3237.lower j ∧ 0 ≤ branch_box_3237.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3237, Box.profileLo, Box.profileHi, box_3237]
theorem leaf_3237_BranchSafe : CertificateConsequences.BranchSafe branch_box_3237 := by
  left; refine ⟨branch_box_3237_nonnegative, ?_⟩
  intro z hz; exact leaf_3237_sound hz

theorem leaf_3241_ok : checkAt 527 1000 box_3241 cert_3241 = true := by
  have h := List.all_eq_true.mp batch_64_19_ok accepted_3241 (by simp [batch_64_19_values])
  exact h
theorem leaf_3241_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3241.profileLo box_3241.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3241_ok
theorem branch_box_3241_nonnegative : ∀ j, 0 ≤ branch_box_3241.lower j ∧ 0 ≤ branch_box_3241.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3241, Box.profileLo, Box.profileHi, box_3241]
theorem leaf_3241_BranchSafe : CertificateConsequences.BranchSafe branch_box_3241 := by
  left; refine ⟨branch_box_3241_nonnegative, ?_⟩
  intro z hz; exact leaf_3241_sound hz

theorem leaf_3243_ok : checkAt 527 1000 box_3243 cert_3243 = true := by
  have h := List.all_eq_true.mp batch_64_20_ok accepted_3243 (by simp [batch_64_20_values])
  exact h
theorem leaf_3243_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3243.profileLo box_3243.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3243_ok
theorem branch_box_3243_nonnegative : ∀ j, 0 ≤ branch_box_3243.lower j ∧ 0 ≤ branch_box_3243.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3243, Box.profileLo, Box.profileHi, box_3243]
theorem leaf_3243_BranchSafe : CertificateConsequences.BranchSafe branch_box_3243 := by
  left; refine ⟨branch_box_3243_nonnegative, ?_⟩
  intro z hz; exact leaf_3243_sound hz

theorem leaf_3244_ok : checkAt 527 1000 box_3244 cert_3244 = true := by
  have h := List.all_eq_true.mp batch_64_21_ok accepted_3244 (by simp [batch_64_21_values])
  exact h
theorem leaf_3244_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3244.profileLo box_3244.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3244_ok
theorem branch_box_3244_nonnegative : ∀ j, 0 ≤ branch_box_3244.lower j ∧ 0 ≤ branch_box_3244.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3244, Box.profileLo, Box.profileHi, box_3244]
theorem leaf_3244_BranchSafe : CertificateConsequences.BranchSafe branch_box_3244 := by
  left; refine ⟨branch_box_3244_nonnegative, ?_⟩
  intro z hz; exact leaf_3244_sound hz

theorem leaf_3245_ok : checkAt 527 1000 box_3245 cert_3245 = true := by
  have h := List.all_eq_true.mp batch_64_22_ok accepted_3245 (by simp [batch_64_22_values])
  exact h
theorem leaf_3245_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3245.profileLo box_3245.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3245_ok
theorem branch_box_3245_nonnegative : ∀ j, 0 ≤ branch_box_3245.lower j ∧ 0 ≤ branch_box_3245.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3245, Box.profileLo, Box.profileHi, box_3245]
theorem leaf_3245_BranchSafe : CertificateConsequences.BranchSafe branch_box_3245 := by
  left; refine ⟨branch_box_3245_nonnegative, ?_⟩
  intro z hz; exact leaf_3245_sound hz

theorem leaf_3246_ok : checkAt 527 1000 box_3246 cert_3246 = true := by
  have h := List.all_eq_true.mp batch_64_23_ok accepted_3246 (by simp [batch_64_23_values])
  exact h
theorem leaf_3246_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3246.profileLo box_3246.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3246_ok
theorem branch_box_3246_nonnegative : ∀ j, 0 ≤ branch_box_3246.lower j ∧ 0 ≤ branch_box_3246.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3246, Box.profileLo, Box.profileHi, box_3246]
theorem leaf_3246_BranchSafe : CertificateConsequences.BranchSafe branch_box_3246 := by
  left; refine ⟨branch_box_3246_nonnegative, ?_⟩
  intro z hz; exact leaf_3246_sound hz

theorem leaf_3247_ok : checkAt 527 1000 box_3247 cert_3247 = true := by
  have h := List.all_eq_true.mp batch_64_24_ok accepted_3247 (by simp [batch_64_24_values])
  exact h
theorem leaf_3247_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3247.profileLo box_3247.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3247_ok
theorem branch_box_3247_nonnegative : ∀ j, 0 ≤ branch_box_3247.lower j ∧ 0 ≤ branch_box_3247.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3247, Box.profileLo, Box.profileHi, box_3247]
theorem leaf_3247_BranchSafe : CertificateConsequences.BranchSafe branch_box_3247 := by
  left; refine ⟨branch_box_3247_nonnegative, ?_⟩
  intro z hz; exact leaf_3247_sound hz

theorem leaf_3249_ok : checkAt 527 1000 box_3249 cert_3249 = true := by
  have h := List.all_eq_true.mp batch_64_25_ok accepted_3249 (by simp [batch_64_25_values])
  exact h
theorem leaf_3249_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3249.profileLo box_3249.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3249_ok
theorem branch_box_3249_nonnegative : ∀ j, 0 ≤ branch_box_3249.lower j ∧ 0 ≤ branch_box_3249.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3249, Box.profileLo, Box.profileHi, box_3249]
theorem leaf_3249_BranchSafe : CertificateConsequences.BranchSafe branch_box_3249 := by
  left; refine ⟨branch_box_3249_nonnegative, ?_⟩
  intro z hz; exact leaf_3249_sound hz

#print axioms batch_64_00_ok
#print axioms leaf_3200_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
