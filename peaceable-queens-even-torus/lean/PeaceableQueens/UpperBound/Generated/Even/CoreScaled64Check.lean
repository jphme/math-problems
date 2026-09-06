import PeaceableQueens.UpperBound.Generated.Even.CoreScaled64Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_64_00_values : List Bool := [accepted_3200]
theorem batch_64_00_ok : batch_64_00_values.all id = true := by decide

def batch_64_01_values : List Bool := [accepted_3202]
theorem batch_64_01_ok : batch_64_01_values.all id = true := by decide

def batch_64_02_values : List Bool := [accepted_3203]
theorem batch_64_02_ok : batch_64_02_values.all id = true := by decide

def batch_64_03_values : List Bool := [accepted_3206]
theorem batch_64_03_ok : batch_64_03_values.all id = true := by decide

def batch_64_04_values : List Bool := [accepted_3208]
theorem batch_64_04_ok : batch_64_04_values.all id = true := by decide

def batch_64_05_values : List Bool := [accepted_3210]
theorem batch_64_05_ok : batch_64_05_values.all id = true := by decide

def batch_64_06_values : List Bool := [accepted_3211]
theorem batch_64_06_ok : batch_64_06_values.all id = true := by decide

def batch_64_07_values : List Bool := [accepted_3213]
theorem batch_64_07_ok : batch_64_07_values.all id = true := by decide

def batch_64_08_values : List Bool := [accepted_3215]
theorem batch_64_08_ok : batch_64_08_values.all id = true := by decide

def batch_64_09_values : List Bool := [accepted_3220]
theorem batch_64_09_ok : batch_64_09_values.all id = true := by decide

def batch_64_10_values : List Bool := [accepted_3222]
theorem batch_64_10_ok : batch_64_10_values.all id = true := by decide

def batch_64_11_values : List Bool := [accepted_3224]
theorem batch_64_11_ok : batch_64_11_values.all id = true := by decide

def batch_64_12_values : List Bool := [accepted_3225]
theorem batch_64_12_ok : batch_64_12_values.all id = true := by decide

def batch_64_13_values : List Bool := [accepted_3227]
theorem batch_64_13_ok : batch_64_13_values.all id = true := by decide

def batch_64_14_values : List Bool := [accepted_3229]
theorem batch_64_14_ok : batch_64_14_values.all id = true := by decide

def batch_64_15_values : List Bool := [accepted_3232]
theorem batch_64_15_ok : batch_64_15_values.all id = true := by decide

def batch_64_16_values : List Bool := [accepted_3234]
theorem batch_64_16_ok : batch_64_16_values.all id = true := by decide

def batch_64_17_values : List Bool := [accepted_3236]
theorem batch_64_17_ok : batch_64_17_values.all id = true := by decide

def batch_64_18_values : List Bool := [accepted_3238]
theorem batch_64_18_ok : batch_64_18_values.all id = true := by decide

def batch_64_19_values : List Bool := [accepted_3240]
theorem batch_64_19_ok : batch_64_19_values.all id = true := by decide

def batch_64_20_values : List Bool := [accepted_3241]
theorem batch_64_20_ok : batch_64_20_values.all id = true := by decide

def batch_64_21_values : List Bool := [accepted_3244]
theorem batch_64_21_ok : batch_64_21_values.all id = true := by decide

def batch_64_22_values : List Bool := [accepted_3246]
theorem batch_64_22_ok : batch_64_22_values.all id = true := by decide

def batch_64_23_values : List Bool := [accepted_3248]
theorem batch_64_23_ok : batch_64_23_values.all id = true := by decide

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

theorem leaf_3202_ok : checkAt 527 1000 box_3202 cert_3202 = true := by
  have h := List.all_eq_true.mp batch_64_01_ok accepted_3202 (by simp [batch_64_01_values])
  exact h
theorem leaf_3202_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3202.profileLo box_3202.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3202_ok
theorem branch_box_3202_nonnegative : ∀ j, 0 ≤ branch_box_3202.lower j ∧ 0 ≤ branch_box_3202.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3202, Box.profileLo, Box.profileHi, box_3202]
theorem leaf_3202_BranchSafe : CertificateConsequences.BranchSafe branch_box_3202 := by
  left; refine ⟨branch_box_3202_nonnegative, ?_⟩
  intro z hz; exact leaf_3202_sound hz

theorem leaf_3203_ok : checkAt 527 1000 box_3203 cert_3203 = true := by
  have h := List.all_eq_true.mp batch_64_02_ok accepted_3203 (by simp [batch_64_02_values])
  exact h
theorem leaf_3203_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3203.profileLo box_3203.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3203_ok
theorem branch_box_3203_nonnegative : ∀ j, 0 ≤ branch_box_3203.lower j ∧ 0 ≤ branch_box_3203.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3203, Box.profileLo, Box.profileHi, box_3203]
theorem leaf_3203_BranchSafe : CertificateConsequences.BranchSafe branch_box_3203 := by
  left; refine ⟨branch_box_3203_nonnegative, ?_⟩
  intro z hz; exact leaf_3203_sound hz

theorem leaf_3206_ok : checkAt 527 1000 box_3206 cert_3206 = true := by
  have h := List.all_eq_true.mp batch_64_03_ok accepted_3206 (by simp [batch_64_03_values])
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

theorem leaf_3210_ok : checkAt 527 1000 box_3210 cert_3210 = true := by
  have h := List.all_eq_true.mp batch_64_05_ok accepted_3210 (by simp [batch_64_05_values])
  exact h
theorem leaf_3210_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3210.profileLo box_3210.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3210_ok
theorem branch_box_3210_nonnegative : ∀ j, 0 ≤ branch_box_3210.lower j ∧ 0 ≤ branch_box_3210.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3210, Box.profileLo, Box.profileHi, box_3210]
theorem leaf_3210_BranchSafe : CertificateConsequences.BranchSafe branch_box_3210 := by
  left; refine ⟨branch_box_3210_nonnegative, ?_⟩
  intro z hz; exact leaf_3210_sound hz

theorem leaf_3211_ok : checkAt 527 1000 box_3211 cert_3211 = true := by
  have h := List.all_eq_true.mp batch_64_06_ok accepted_3211 (by simp [batch_64_06_values])
  exact h
theorem leaf_3211_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3211.profileLo box_3211.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3211_ok
theorem branch_box_3211_nonnegative : ∀ j, 0 ≤ branch_box_3211.lower j ∧ 0 ≤ branch_box_3211.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3211, Box.profileLo, Box.profileHi, box_3211]
theorem leaf_3211_BranchSafe : CertificateConsequences.BranchSafe branch_box_3211 := by
  left; refine ⟨branch_box_3211_nonnegative, ?_⟩
  intro z hz; exact leaf_3211_sound hz

theorem leaf_3213_ok : checkAt 527 1000 box_3213 cert_3213 = true := by
  have h := List.all_eq_true.mp batch_64_07_ok accepted_3213 (by simp [batch_64_07_values])
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
  have h := List.all_eq_true.mp batch_64_08_ok accepted_3215 (by simp [batch_64_08_values])
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

theorem leaf_3220_ok : checkAt 527 1000 box_3220 cert_3220 = true := by
  have h := List.all_eq_true.mp batch_64_09_ok accepted_3220 (by simp [batch_64_09_values])
  exact h
theorem leaf_3220_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3220.profileLo box_3220.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3220_ok
theorem branch_box_3220_nonnegative : ∀ j, 0 ≤ branch_box_3220.lower j ∧ 0 ≤ branch_box_3220.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3220, Box.profileLo, Box.profileHi, box_3220]
theorem leaf_3220_BranchSafe : CertificateConsequences.BranchSafe branch_box_3220 := by
  left; refine ⟨branch_box_3220_nonnegative, ?_⟩
  intro z hz; exact leaf_3220_sound hz

theorem leaf_3222_ok : checkAt 527 1000 box_3222 cert_3222 = true := by
  have h := List.all_eq_true.mp batch_64_10_ok accepted_3222 (by simp [batch_64_10_values])
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

theorem leaf_3224_ok : checkAt 527 1000 box_3224 cert_3224 = true := by
  have h := List.all_eq_true.mp batch_64_11_ok accepted_3224 (by simp [batch_64_11_values])
  exact h
theorem leaf_3224_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3224.profileLo box_3224.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3224_ok
theorem branch_box_3224_nonnegative : ∀ j, 0 ≤ branch_box_3224.lower j ∧ 0 ≤ branch_box_3224.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3224, Box.profileLo, Box.profileHi, box_3224]
theorem leaf_3224_BranchSafe : CertificateConsequences.BranchSafe branch_box_3224 := by
  left; refine ⟨branch_box_3224_nonnegative, ?_⟩
  intro z hz; exact leaf_3224_sound hz

theorem leaf_3225_ok : checkAt 527 1000 box_3225 cert_3225 = true := by
  have h := List.all_eq_true.mp batch_64_12_ok accepted_3225 (by simp [batch_64_12_values])
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

theorem leaf_3227_ok : checkAt 527 1000 box_3227 cert_3227 = true := by
  have h := List.all_eq_true.mp batch_64_13_ok accepted_3227 (by simp [batch_64_13_values])
  exact h
theorem leaf_3227_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3227.profileLo box_3227.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3227_ok
theorem branch_box_3227_nonnegative : ∀ j, 0 ≤ branch_box_3227.lower j ∧ 0 ≤ branch_box_3227.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3227, Box.profileLo, Box.profileHi, box_3227]
theorem leaf_3227_BranchSafe : CertificateConsequences.BranchSafe branch_box_3227 := by
  left; refine ⟨branch_box_3227_nonnegative, ?_⟩
  intro z hz; exact leaf_3227_sound hz

theorem leaf_3229_ok : checkAt 527 1000 box_3229 cert_3229 = true := by
  have h := List.all_eq_true.mp batch_64_14_ok accepted_3229 (by simp [batch_64_14_values])
  exact h
theorem leaf_3229_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3229.profileLo box_3229.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3229_ok
theorem branch_box_3229_nonnegative : ∀ j, 0 ≤ branch_box_3229.lower j ∧ 0 ≤ branch_box_3229.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3229, Box.profileLo, Box.profileHi, box_3229]
theorem leaf_3229_BranchSafe : CertificateConsequences.BranchSafe branch_box_3229 := by
  left; refine ⟨branch_box_3229_nonnegative, ?_⟩
  intro z hz; exact leaf_3229_sound hz

theorem leaf_3232_ok : checkAt 527 1000 box_3232 cert_3232 = true := by
  have h := List.all_eq_true.mp batch_64_15_ok accepted_3232 (by simp [batch_64_15_values])
  exact h
theorem leaf_3232_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3232.profileLo box_3232.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3232_ok
theorem branch_box_3232_nonnegative : ∀ j, 0 ≤ branch_box_3232.lower j ∧ 0 ≤ branch_box_3232.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3232, Box.profileLo, Box.profileHi, box_3232]
theorem leaf_3232_BranchSafe : CertificateConsequences.BranchSafe branch_box_3232 := by
  left; refine ⟨branch_box_3232_nonnegative, ?_⟩
  intro z hz; exact leaf_3232_sound hz

theorem leaf_3234_ok : checkAt 527 1000 box_3234 cert_3234 = true := by
  have h := List.all_eq_true.mp batch_64_16_ok accepted_3234 (by simp [batch_64_16_values])
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

theorem leaf_3236_ok : checkAt 527 1000 box_3236 cert_3236 = true := by
  have h := List.all_eq_true.mp batch_64_17_ok accepted_3236 (by simp [batch_64_17_values])
  exact h
theorem leaf_3236_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3236.profileLo box_3236.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3236_ok
theorem branch_box_3236_nonnegative : ∀ j, 0 ≤ branch_box_3236.lower j ∧ 0 ≤ branch_box_3236.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3236, Box.profileLo, Box.profileHi, box_3236]
theorem leaf_3236_BranchSafe : CertificateConsequences.BranchSafe branch_box_3236 := by
  left; refine ⟨branch_box_3236_nonnegative, ?_⟩
  intro z hz; exact leaf_3236_sound hz

theorem leaf_3238_ok : checkAt 527 1000 box_3238 cert_3238 = true := by
  have h := List.all_eq_true.mp batch_64_18_ok accepted_3238 (by simp [batch_64_18_values])
  exact h
theorem leaf_3238_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3238.profileLo box_3238.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3238_ok
theorem branch_box_3238_nonnegative : ∀ j, 0 ≤ branch_box_3238.lower j ∧ 0 ≤ branch_box_3238.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3238, Box.profileLo, Box.profileHi, box_3238]
theorem leaf_3238_BranchSafe : CertificateConsequences.BranchSafe branch_box_3238 := by
  left; refine ⟨branch_box_3238_nonnegative, ?_⟩
  intro z hz; exact leaf_3238_sound hz

theorem leaf_3240_ok : checkAt 527 1000 box_3240 cert_3240 = true := by
  have h := List.all_eq_true.mp batch_64_19_ok accepted_3240 (by simp [batch_64_19_values])
  exact h
theorem leaf_3240_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3240.profileLo box_3240.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3240_ok
theorem branch_box_3240_nonnegative : ∀ j, 0 ≤ branch_box_3240.lower j ∧ 0 ≤ branch_box_3240.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3240, Box.profileLo, Box.profileHi, box_3240]
theorem leaf_3240_BranchSafe : CertificateConsequences.BranchSafe branch_box_3240 := by
  left; refine ⟨branch_box_3240_nonnegative, ?_⟩
  intro z hz; exact leaf_3240_sound hz

theorem leaf_3241_ok : checkAt 527 1000 box_3241 cert_3241 = true := by
  have h := List.all_eq_true.mp batch_64_20_ok accepted_3241 (by simp [batch_64_20_values])
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

theorem leaf_3246_ok : checkAt 527 1000 box_3246 cert_3246 = true := by
  have h := List.all_eq_true.mp batch_64_22_ok accepted_3246 (by simp [batch_64_22_values])
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

theorem leaf_3248_ok : checkAt 527 1000 box_3248 cert_3248 = true := by
  have h := List.all_eq_true.mp batch_64_23_ok accepted_3248 (by simp [batch_64_23_values])
  exact h
theorem leaf_3248_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3248.profileLo box_3248.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3248_ok
theorem branch_box_3248_nonnegative : ∀ j, 0 ≤ branch_box_3248.lower j ∧ 0 ≤ branch_box_3248.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3248, Box.profileLo, Box.profileHi, box_3248]
theorem leaf_3248_BranchSafe : CertificateConsequences.BranchSafe branch_box_3248 := by
  left; refine ⟨branch_box_3248_nonnegative, ?_⟩
  intro z hz; exact leaf_3248_sound hz

#print axioms batch_64_00_ok
#print axioms leaf_3200_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
