import PeaceableQueens.UpperBound.Generated.Even.C527Scaled67Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_67_00_values : List Bool := [accepted_3351]
theorem batch_67_00_ok : batch_67_00_values.all id = true := by decide

def batch_67_01_values : List Bool := [accepted_3353]
theorem batch_67_01_ok : batch_67_01_values.all id = true := by decide

def batch_67_02_values : List Bool := [accepted_3354]
theorem batch_67_02_ok : batch_67_02_values.all id = true := by decide

def batch_67_03_values : List Bool := [accepted_3355]
theorem batch_67_03_ok : batch_67_03_values.all id = true := by decide

def batch_67_04_values : List Bool := [accepted_3357]
theorem batch_67_04_ok : batch_67_04_values.all id = true := by decide

def batch_67_05_values : List Bool := [accepted_3358]
theorem batch_67_05_ok : batch_67_05_values.all id = true := by decide

def batch_67_06_values : List Bool := [accepted_3359]
theorem batch_67_06_ok : batch_67_06_values.all id = true := by decide

def batch_67_07_values : List Bool := [accepted_3361]
theorem batch_67_07_ok : batch_67_07_values.all id = true := by decide

def batch_67_08_values : List Bool := [accepted_3362]
theorem batch_67_08_ok : batch_67_08_values.all id = true := by decide

def batch_67_09_values : List Bool := [accepted_3365]
theorem batch_67_09_ok : batch_67_09_values.all id = true := by decide

def batch_67_10_values : List Bool := [accepted_3366]
theorem batch_67_10_ok : batch_67_10_values.all id = true := by decide

def batch_67_11_values : List Bool := [accepted_3367]
theorem batch_67_11_ok : batch_67_11_values.all id = true := by decide

def batch_67_12_values : List Bool := [accepted_3369]
theorem batch_67_12_ok : batch_67_12_values.all id = true := by decide

def batch_67_13_values : List Bool := [accepted_3371]
theorem batch_67_13_ok : batch_67_13_values.all id = true := by decide

def batch_67_14_values : List Bool := [accepted_3372]
theorem batch_67_14_ok : batch_67_14_values.all id = true := by decide

def batch_67_15_values : List Bool := [accepted_3376]
theorem batch_67_15_ok : batch_67_15_values.all id = true := by decide

def batch_67_16_values : List Bool := [accepted_3380]
theorem batch_67_16_ok : batch_67_16_values.all id = true := by decide

def batch_67_17_values : List Bool := [accepted_3381]
theorem batch_67_17_ok : batch_67_17_values.all id = true := by decide

def batch_67_18_values : List Bool := [accepted_3382]
theorem batch_67_18_ok : batch_67_18_values.all id = true := by decide

def batch_67_19_values : List Bool := [accepted_3383]
theorem batch_67_19_ok : batch_67_19_values.all id = true := by decide

def batch_67_20_values : List Bool := [accepted_3384]
theorem batch_67_20_ok : batch_67_20_values.all id = true := by decide

def batch_67_21_values : List Bool := [accepted_3385]
theorem batch_67_21_ok : batch_67_21_values.all id = true := by decide

def batch_67_22_values : List Bool := [accepted_3386]
theorem batch_67_22_ok : batch_67_22_values.all id = true := by decide

def batch_67_23_values : List Bool := [accepted_3393]
theorem batch_67_23_ok : batch_67_23_values.all id = true := by decide

def batch_67_24_values : List Bool := [accepted_3396]
theorem batch_67_24_ok : batch_67_24_values.all id = true := by decide

def batch_67_25_values : List Bool := [accepted_3397]
theorem batch_67_25_ok : batch_67_25_values.all id = true := by decide

def batch_67_26_values : List Bool := [accepted_3398]
theorem batch_67_26_ok : batch_67_26_values.all id = true := by decide

def batch_67_27_values : List Bool := [accepted_3399]
theorem batch_67_27_ok : batch_67_27_values.all id = true := by decide

theorem leaf_3351_ok : checkAt 527 1000 box_3351 cert_3351 = true := by
  have h := List.all_eq_true.mp batch_67_00_ok accepted_3351 (by simp [batch_67_00_values])
  exact h
theorem leaf_3351_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3351.profileLo box_3351.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3351_ok
theorem branch_box_3351_nonnegative : ∀ j, 0 ≤ branch_box_3351.lower j ∧ 0 ≤ branch_box_3351.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3351, Box.profileLo, Box.profileHi, box_3351]
theorem leaf_3351_BranchSafe : CertificateConsequences.BranchSafe branch_box_3351 := by
  left; refine ⟨branch_box_3351_nonnegative, ?_⟩
  intro z hz; exact leaf_3351_sound hz

theorem leaf_3353_ok : checkAt 527 1000 box_3353 cert_3353 = true := by
  have h := List.all_eq_true.mp batch_67_01_ok accepted_3353 (by simp [batch_67_01_values])
  exact h
theorem leaf_3353_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3353.profileLo box_3353.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3353_ok
theorem branch_box_3353_nonnegative : ∀ j, 0 ≤ branch_box_3353.lower j ∧ 0 ≤ branch_box_3353.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3353, Box.profileLo, Box.profileHi, box_3353]
theorem leaf_3353_BranchSafe : CertificateConsequences.BranchSafe branch_box_3353 := by
  left; refine ⟨branch_box_3353_nonnegative, ?_⟩
  intro z hz; exact leaf_3353_sound hz

theorem leaf_3354_ok : checkAt 527 1000 box_3354 cert_3354 = true := by
  have h := List.all_eq_true.mp batch_67_02_ok accepted_3354 (by simp [batch_67_02_values])
  exact h
theorem leaf_3354_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3354.profileLo box_3354.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3354_ok
theorem branch_box_3354_nonnegative : ∀ j, 0 ≤ branch_box_3354.lower j ∧ 0 ≤ branch_box_3354.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3354, Box.profileLo, Box.profileHi, box_3354]
theorem leaf_3354_BranchSafe : CertificateConsequences.BranchSafe branch_box_3354 := by
  left; refine ⟨branch_box_3354_nonnegative, ?_⟩
  intro z hz; exact leaf_3354_sound hz

theorem leaf_3355_ok : checkAt 527 1000 box_3355 cert_3355 = true := by
  have h := List.all_eq_true.mp batch_67_03_ok accepted_3355 (by simp [batch_67_03_values])
  exact h
theorem leaf_3355_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3355.profileLo box_3355.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3355_ok
theorem branch_box_3355_nonnegative : ∀ j, 0 ≤ branch_box_3355.lower j ∧ 0 ≤ branch_box_3355.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3355, Box.profileLo, Box.profileHi, box_3355]
theorem leaf_3355_BranchSafe : CertificateConsequences.BranchSafe branch_box_3355 := by
  left; refine ⟨branch_box_3355_nonnegative, ?_⟩
  intro z hz; exact leaf_3355_sound hz

theorem leaf_3357_ok : checkAt 527 1000 box_3357 cert_3357 = true := by
  have h := List.all_eq_true.mp batch_67_04_ok accepted_3357 (by simp [batch_67_04_values])
  exact h
theorem leaf_3357_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3357.profileLo box_3357.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3357_ok
theorem branch_box_3357_nonnegative : ∀ j, 0 ≤ branch_box_3357.lower j ∧ 0 ≤ branch_box_3357.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3357, Box.profileLo, Box.profileHi, box_3357]
theorem leaf_3357_BranchSafe : CertificateConsequences.BranchSafe branch_box_3357 := by
  left; refine ⟨branch_box_3357_nonnegative, ?_⟩
  intro z hz; exact leaf_3357_sound hz

theorem leaf_3358_ok : checkAt 527 1000 box_3358 cert_3358 = true := by
  have h := List.all_eq_true.mp batch_67_05_ok accepted_3358 (by simp [batch_67_05_values])
  exact h
theorem leaf_3358_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3358.profileLo box_3358.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3358_ok
theorem branch_box_3358_nonnegative : ∀ j, 0 ≤ branch_box_3358.lower j ∧ 0 ≤ branch_box_3358.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3358, Box.profileLo, Box.profileHi, box_3358]
theorem leaf_3358_BranchSafe : CertificateConsequences.BranchSafe branch_box_3358 := by
  left; refine ⟨branch_box_3358_nonnegative, ?_⟩
  intro z hz; exact leaf_3358_sound hz

theorem leaf_3359_ok : checkAt 527 1000 box_3359 cert_3359 = true := by
  have h := List.all_eq_true.mp batch_67_06_ok accepted_3359 (by simp [batch_67_06_values])
  exact h
theorem leaf_3359_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3359.profileLo box_3359.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3359_ok
theorem branch_box_3359_nonnegative : ∀ j, 0 ≤ branch_box_3359.lower j ∧ 0 ≤ branch_box_3359.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3359, Box.profileLo, Box.profileHi, box_3359]
theorem leaf_3359_BranchSafe : CertificateConsequences.BranchSafe branch_box_3359 := by
  left; refine ⟨branch_box_3359_nonnegative, ?_⟩
  intro z hz; exact leaf_3359_sound hz

theorem leaf_3361_ok : checkAt 527 1000 box_3361 cert_3361 = true := by
  have h := List.all_eq_true.mp batch_67_07_ok accepted_3361 (by simp [batch_67_07_values])
  exact h
theorem leaf_3361_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3361.profileLo box_3361.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3361_ok
theorem branch_box_3361_nonnegative : ∀ j, 0 ≤ branch_box_3361.lower j ∧ 0 ≤ branch_box_3361.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3361, Box.profileLo, Box.profileHi, box_3361]
theorem leaf_3361_BranchSafe : CertificateConsequences.BranchSafe branch_box_3361 := by
  left; refine ⟨branch_box_3361_nonnegative, ?_⟩
  intro z hz; exact leaf_3361_sound hz

theorem leaf_3362_ok : checkAt 527 1000 box_3362 cert_3362 = true := by
  have h := List.all_eq_true.mp batch_67_08_ok accepted_3362 (by simp [batch_67_08_values])
  exact h
theorem leaf_3362_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3362.profileLo box_3362.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3362_ok
theorem branch_box_3362_nonnegative : ∀ j, 0 ≤ branch_box_3362.lower j ∧ 0 ≤ branch_box_3362.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3362, Box.profileLo, Box.profileHi, box_3362]
theorem leaf_3362_BranchSafe : CertificateConsequences.BranchSafe branch_box_3362 := by
  left; refine ⟨branch_box_3362_nonnegative, ?_⟩
  intro z hz; exact leaf_3362_sound hz

theorem leaf_3365_ok : checkAt 527 1000 box_3365 cert_3365 = true := by
  have h := List.all_eq_true.mp batch_67_09_ok accepted_3365 (by simp [batch_67_09_values])
  exact h
theorem leaf_3365_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3365.profileLo box_3365.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3365_ok
theorem branch_box_3365_nonnegative : ∀ j, 0 ≤ branch_box_3365.lower j ∧ 0 ≤ branch_box_3365.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3365, Box.profileLo, Box.profileHi, box_3365]
theorem leaf_3365_BranchSafe : CertificateConsequences.BranchSafe branch_box_3365 := by
  left; refine ⟨branch_box_3365_nonnegative, ?_⟩
  intro z hz; exact leaf_3365_sound hz

theorem leaf_3366_ok : checkAt 527 1000 box_3366 cert_3366 = true := by
  have h := List.all_eq_true.mp batch_67_10_ok accepted_3366 (by simp [batch_67_10_values])
  exact h
theorem leaf_3366_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3366.profileLo box_3366.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3366_ok
theorem branch_box_3366_nonnegative : ∀ j, 0 ≤ branch_box_3366.lower j ∧ 0 ≤ branch_box_3366.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3366, Box.profileLo, Box.profileHi, box_3366]
theorem leaf_3366_BranchSafe : CertificateConsequences.BranchSafe branch_box_3366 := by
  left; refine ⟨branch_box_3366_nonnegative, ?_⟩
  intro z hz; exact leaf_3366_sound hz

theorem leaf_3367_ok : checkAt 527 1000 box_3367 cert_3367 = true := by
  have h := List.all_eq_true.mp batch_67_11_ok accepted_3367 (by simp [batch_67_11_values])
  exact h
theorem leaf_3367_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3367.profileLo box_3367.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3367_ok
theorem branch_box_3367_nonnegative : ∀ j, 0 ≤ branch_box_3367.lower j ∧ 0 ≤ branch_box_3367.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3367, Box.profileLo, Box.profileHi, box_3367]
theorem leaf_3367_BranchSafe : CertificateConsequences.BranchSafe branch_box_3367 := by
  left; refine ⟨branch_box_3367_nonnegative, ?_⟩
  intro z hz; exact leaf_3367_sound hz

theorem leaf_3369_ok : checkAt 527 1000 box_3369 cert_3369 = true := by
  have h := List.all_eq_true.mp batch_67_12_ok accepted_3369 (by simp [batch_67_12_values])
  exact h
theorem leaf_3369_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3369.profileLo box_3369.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3369_ok
theorem branch_box_3369_nonnegative : ∀ j, 0 ≤ branch_box_3369.lower j ∧ 0 ≤ branch_box_3369.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3369, Box.profileLo, Box.profileHi, box_3369]
theorem leaf_3369_BranchSafe : CertificateConsequences.BranchSafe branch_box_3369 := by
  left; refine ⟨branch_box_3369_nonnegative, ?_⟩
  intro z hz; exact leaf_3369_sound hz

theorem leaf_3371_ok : checkAt 527 1000 box_3371 cert_3371 = true := by
  have h := List.all_eq_true.mp batch_67_13_ok accepted_3371 (by simp [batch_67_13_values])
  exact h
theorem leaf_3371_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3371.profileLo box_3371.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3371_ok
theorem branch_box_3371_nonnegative : ∀ j, 0 ≤ branch_box_3371.lower j ∧ 0 ≤ branch_box_3371.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3371, Box.profileLo, Box.profileHi, box_3371]
theorem leaf_3371_BranchSafe : CertificateConsequences.BranchSafe branch_box_3371 := by
  left; refine ⟨branch_box_3371_nonnegative, ?_⟩
  intro z hz; exact leaf_3371_sound hz

theorem leaf_3372_ok : checkAt 527 1000 box_3372 cert_3372 = true := by
  have h := List.all_eq_true.mp batch_67_14_ok accepted_3372 (by simp [batch_67_14_values])
  exact h
theorem leaf_3372_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3372.profileLo box_3372.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3372_ok
theorem branch_box_3372_nonnegative : ∀ j, 0 ≤ branch_box_3372.lower j ∧ 0 ≤ branch_box_3372.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3372, Box.profileLo, Box.profileHi, box_3372]
theorem leaf_3372_BranchSafe : CertificateConsequences.BranchSafe branch_box_3372 := by
  left; refine ⟨branch_box_3372_nonnegative, ?_⟩
  intro z hz; exact leaf_3372_sound hz

theorem leaf_3376_ok : checkAt 527 1000 box_3376 cert_3376 = true := by
  have h := List.all_eq_true.mp batch_67_15_ok accepted_3376 (by simp [batch_67_15_values])
  exact h
theorem leaf_3376_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3376.profileLo box_3376.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3376_ok
theorem branch_box_3376_nonnegative : ∀ j, 0 ≤ branch_box_3376.lower j ∧ 0 ≤ branch_box_3376.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3376, Box.profileLo, Box.profileHi, box_3376]
theorem leaf_3376_BranchSafe : CertificateConsequences.BranchSafe branch_box_3376 := by
  left; refine ⟨branch_box_3376_nonnegative, ?_⟩
  intro z hz; exact leaf_3376_sound hz

theorem leaf_3380_ok : checkAt 527 1000 box_3380 cert_3380 = true := by
  have h := List.all_eq_true.mp batch_67_16_ok accepted_3380 (by simp [batch_67_16_values])
  exact h
theorem leaf_3380_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3380.profileLo box_3380.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3380_ok
theorem branch_box_3380_nonnegative : ∀ j, 0 ≤ branch_box_3380.lower j ∧ 0 ≤ branch_box_3380.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3380, Box.profileLo, Box.profileHi, box_3380]
theorem leaf_3380_BranchSafe : CertificateConsequences.BranchSafe branch_box_3380 := by
  left; refine ⟨branch_box_3380_nonnegative, ?_⟩
  intro z hz; exact leaf_3380_sound hz

theorem leaf_3381_ok : checkAt 527 1000 box_3381 cert_3381 = true := by
  have h := List.all_eq_true.mp batch_67_17_ok accepted_3381 (by simp [batch_67_17_values])
  exact h
theorem leaf_3381_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3381.profileLo box_3381.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3381_ok
theorem branch_box_3381_nonnegative : ∀ j, 0 ≤ branch_box_3381.lower j ∧ 0 ≤ branch_box_3381.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3381, Box.profileLo, Box.profileHi, box_3381]
theorem leaf_3381_BranchSafe : CertificateConsequences.BranchSafe branch_box_3381 := by
  left; refine ⟨branch_box_3381_nonnegative, ?_⟩
  intro z hz; exact leaf_3381_sound hz

theorem leaf_3382_ok : checkAt 527 1000 box_3382 cert_3382 = true := by
  have h := List.all_eq_true.mp batch_67_18_ok accepted_3382 (by simp [batch_67_18_values])
  exact h
theorem leaf_3382_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3382.profileLo box_3382.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3382_ok
theorem branch_box_3382_nonnegative : ∀ j, 0 ≤ branch_box_3382.lower j ∧ 0 ≤ branch_box_3382.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3382, Box.profileLo, Box.profileHi, box_3382]
theorem leaf_3382_BranchSafe : CertificateConsequences.BranchSafe branch_box_3382 := by
  left; refine ⟨branch_box_3382_nonnegative, ?_⟩
  intro z hz; exact leaf_3382_sound hz

theorem leaf_3383_ok : checkAt 527 1000 box_3383 cert_3383 = true := by
  have h := List.all_eq_true.mp batch_67_19_ok accepted_3383 (by simp [batch_67_19_values])
  exact h
theorem leaf_3383_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3383.profileLo box_3383.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3383_ok
theorem branch_box_3383_nonnegative : ∀ j, 0 ≤ branch_box_3383.lower j ∧ 0 ≤ branch_box_3383.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3383, Box.profileLo, Box.profileHi, box_3383]
theorem leaf_3383_BranchSafe : CertificateConsequences.BranchSafe branch_box_3383 := by
  left; refine ⟨branch_box_3383_nonnegative, ?_⟩
  intro z hz; exact leaf_3383_sound hz

theorem leaf_3384_ok : checkAt 527 1000 box_3384 cert_3384 = true := by
  have h := List.all_eq_true.mp batch_67_20_ok accepted_3384 (by simp [batch_67_20_values])
  exact h
theorem leaf_3384_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3384.profileLo box_3384.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3384_ok
theorem branch_box_3384_nonnegative : ∀ j, 0 ≤ branch_box_3384.lower j ∧ 0 ≤ branch_box_3384.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3384, Box.profileLo, Box.profileHi, box_3384]
theorem leaf_3384_BranchSafe : CertificateConsequences.BranchSafe branch_box_3384 := by
  left; refine ⟨branch_box_3384_nonnegative, ?_⟩
  intro z hz; exact leaf_3384_sound hz

theorem leaf_3385_ok : checkAt 527 1000 box_3385 cert_3385 = true := by
  have h := List.all_eq_true.mp batch_67_21_ok accepted_3385 (by simp [batch_67_21_values])
  exact h
theorem leaf_3385_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3385.profileLo box_3385.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3385_ok
theorem branch_box_3385_nonnegative : ∀ j, 0 ≤ branch_box_3385.lower j ∧ 0 ≤ branch_box_3385.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3385, Box.profileLo, Box.profileHi, box_3385]
theorem leaf_3385_BranchSafe : CertificateConsequences.BranchSafe branch_box_3385 := by
  left; refine ⟨branch_box_3385_nonnegative, ?_⟩
  intro z hz; exact leaf_3385_sound hz

theorem leaf_3386_ok : checkAt 527 1000 box_3386 cert_3386 = true := by
  have h := List.all_eq_true.mp batch_67_22_ok accepted_3386 (by simp [batch_67_22_values])
  exact h
theorem leaf_3386_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3386.profileLo box_3386.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3386_ok
theorem branch_box_3386_nonnegative : ∀ j, 0 ≤ branch_box_3386.lower j ∧ 0 ≤ branch_box_3386.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3386, Box.profileLo, Box.profileHi, box_3386]
theorem leaf_3386_BranchSafe : CertificateConsequences.BranchSafe branch_box_3386 := by
  left; refine ⟨branch_box_3386_nonnegative, ?_⟩
  intro z hz; exact leaf_3386_sound hz

theorem leaf_3393_ok : checkAt 527 1000 box_3393 cert_3393 = true := by
  have h := List.all_eq_true.mp batch_67_23_ok accepted_3393 (by simp [batch_67_23_values])
  exact h
theorem leaf_3393_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3393.profileLo box_3393.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3393_ok
theorem branch_box_3393_nonnegative : ∀ j, 0 ≤ branch_box_3393.lower j ∧ 0 ≤ branch_box_3393.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3393, Box.profileLo, Box.profileHi, box_3393]
theorem leaf_3393_BranchSafe : CertificateConsequences.BranchSafe branch_box_3393 := by
  left; refine ⟨branch_box_3393_nonnegative, ?_⟩
  intro z hz; exact leaf_3393_sound hz

theorem leaf_3396_ok : checkAt 527 1000 box_3396 cert_3396 = true := by
  have h := List.all_eq_true.mp batch_67_24_ok accepted_3396 (by simp [batch_67_24_values])
  exact h
theorem leaf_3396_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3396.profileLo box_3396.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3396_ok
theorem branch_box_3396_nonnegative : ∀ j, 0 ≤ branch_box_3396.lower j ∧ 0 ≤ branch_box_3396.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3396, Box.profileLo, Box.profileHi, box_3396]
theorem leaf_3396_BranchSafe : CertificateConsequences.BranchSafe branch_box_3396 := by
  left; refine ⟨branch_box_3396_nonnegative, ?_⟩
  intro z hz; exact leaf_3396_sound hz

theorem leaf_3397_ok : checkAt 527 1000 box_3397 cert_3397 = true := by
  have h := List.all_eq_true.mp batch_67_25_ok accepted_3397 (by simp [batch_67_25_values])
  exact h
theorem leaf_3397_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3397.profileLo box_3397.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3397_ok
theorem branch_box_3397_nonnegative : ∀ j, 0 ≤ branch_box_3397.lower j ∧ 0 ≤ branch_box_3397.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3397, Box.profileLo, Box.profileHi, box_3397]
theorem leaf_3397_BranchSafe : CertificateConsequences.BranchSafe branch_box_3397 := by
  left; refine ⟨branch_box_3397_nonnegative, ?_⟩
  intro z hz; exact leaf_3397_sound hz

theorem leaf_3398_ok : checkAt 527 1000 box_3398 cert_3398 = true := by
  have h := List.all_eq_true.mp batch_67_26_ok accepted_3398 (by simp [batch_67_26_values])
  exact h
theorem leaf_3398_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3398.profileLo box_3398.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3398_ok
theorem branch_box_3398_nonnegative : ∀ j, 0 ≤ branch_box_3398.lower j ∧ 0 ≤ branch_box_3398.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3398, Box.profileLo, Box.profileHi, box_3398]
theorem leaf_3398_BranchSafe : CertificateConsequences.BranchSafe branch_box_3398 := by
  left; refine ⟨branch_box_3398_nonnegative, ?_⟩
  intro z hz; exact leaf_3398_sound hz

theorem leaf_3399_ok : checkAt 527 1000 box_3399 cert_3399 = true := by
  have h := List.all_eq_true.mp batch_67_27_ok accepted_3399 (by simp [batch_67_27_values])
  exact h
theorem leaf_3399_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3399.profileLo box_3399.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3399_ok
theorem branch_box_3399_nonnegative : ∀ j, 0 ≤ branch_box_3399.lower j ∧ 0 ≤ branch_box_3399.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3399, Box.profileLo, Box.profileHi, box_3399]
theorem leaf_3399_BranchSafe : CertificateConsequences.BranchSafe branch_box_3399 := by
  left; refine ⟨branch_box_3399_nonnegative, ?_⟩
  intro z hz; exact leaf_3399_sound hz

#print axioms batch_67_00_ok
#print axioms leaf_3351_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
