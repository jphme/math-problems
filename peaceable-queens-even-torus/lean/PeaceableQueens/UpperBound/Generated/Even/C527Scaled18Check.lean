import PeaceableQueens.UpperBound.Generated.Even.C527Scaled18Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_18_00_values : List Bool := [accepted_900]
theorem batch_18_00_ok : batch_18_00_values.all id = true := by decide

def batch_18_01_values : List Bool := [accepted_903]
theorem batch_18_01_ok : batch_18_01_values.all id = true := by decide

def batch_18_02_values : List Bool := [accepted_904]
theorem batch_18_02_ok : batch_18_02_values.all id = true := by decide

def batch_18_03_values : List Bool := [accepted_915]
theorem batch_18_03_ok : batch_18_03_values.all id = true := by decide

def batch_18_04_values : List Bool := [accepted_917]
theorem batch_18_04_ok : batch_18_04_values.all id = true := by decide

def batch_18_05_values : List Bool := [accepted_918]
theorem batch_18_05_ok : batch_18_05_values.all id = true := by decide

def batch_18_06_values : List Bool := [accepted_920]
theorem batch_18_06_ok : batch_18_06_values.all id = true := by decide

def batch_18_07_values : List Bool := [accepted_922]
theorem batch_18_07_ok : batch_18_07_values.all id = true := by decide

def batch_18_08_values : List Bool := [accepted_926]
theorem batch_18_08_ok : batch_18_08_values.all id = true := by decide

def batch_18_09_values : List Bool := [accepted_928]
theorem batch_18_09_ok : batch_18_09_values.all id = true := by decide

def batch_18_10_values : List Bool := [accepted_930]
theorem batch_18_10_ok : batch_18_10_values.all id = true := by decide

def batch_18_11_values : List Bool := [accepted_931]
theorem batch_18_11_ok : batch_18_11_values.all id = true := by decide

def batch_18_12_values : List Bool := [accepted_932]
theorem batch_18_12_ok : batch_18_12_values.all id = true := by decide

def batch_18_13_values : List Bool := [accepted_933]
theorem batch_18_13_ok : batch_18_13_values.all id = true := by decide

def batch_18_14_values : List Bool := [accepted_935]
theorem batch_18_14_ok : batch_18_14_values.all id = true := by decide

def batch_18_15_values : List Bool := [accepted_936]
theorem batch_18_15_ok : batch_18_15_values.all id = true := by decide

def batch_18_16_values : List Bool := [accepted_937]
theorem batch_18_16_ok : batch_18_16_values.all id = true := by decide

def batch_18_17_values : List Bool := [accepted_939]
theorem batch_18_17_ok : batch_18_17_values.all id = true := by decide

def batch_18_18_values : List Bool := [accepted_940]
theorem batch_18_18_ok : batch_18_18_values.all id = true := by decide

def batch_18_19_values : List Bool := [accepted_943]
theorem batch_18_19_ok : batch_18_19_values.all id = true := by decide

def batch_18_20_values : List Bool := [accepted_945]
theorem batch_18_20_ok : batch_18_20_values.all id = true := by decide

def batch_18_21_values : List Bool := [accepted_946]
theorem batch_18_21_ok : batch_18_21_values.all id = true := by decide

def batch_18_22_values : List Bool := [accepted_947]
theorem batch_18_22_ok : batch_18_22_values.all id = true := by decide

def batch_18_23_values : List Bool := [accepted_949]
theorem batch_18_23_ok : batch_18_23_values.all id = true := by decide

theorem leaf_900_ok : checkAt 527 1000 box_900 cert_900 = true := by
  have h := List.all_eq_true.mp batch_18_00_ok accepted_900 (by simp [batch_18_00_values])
  exact h
theorem leaf_900_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_900.profileLo box_900.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_900_ok
theorem branch_box_900_nonnegative : ∀ j, 0 ≤ branch_box_900.lower j ∧ 0 ≤ branch_box_900.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_900, Box.profileLo, Box.profileHi, box_900]
theorem leaf_900_BranchSafe : CertificateConsequences.BranchSafe branch_box_900 := by
  left; refine ⟨branch_box_900_nonnegative, ?_⟩
  intro z hz; exact leaf_900_sound hz

theorem leaf_903_ok : checkAt 527 1000 box_903 cert_903 = true := by
  have h := List.all_eq_true.mp batch_18_01_ok accepted_903 (by simp [batch_18_01_values])
  exact h
theorem leaf_903_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_903.profileLo box_903.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_903_ok
theorem branch_box_903_nonnegative : ∀ j, 0 ≤ branch_box_903.lower j ∧ 0 ≤ branch_box_903.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_903, Box.profileLo, Box.profileHi, box_903]
theorem leaf_903_BranchSafe : CertificateConsequences.BranchSafe branch_box_903 := by
  left; refine ⟨branch_box_903_nonnegative, ?_⟩
  intro z hz; exact leaf_903_sound hz

theorem leaf_904_ok : checkAt 527 1000 box_904 cert_904 = true := by
  have h := List.all_eq_true.mp batch_18_02_ok accepted_904 (by simp [batch_18_02_values])
  exact h
theorem leaf_904_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_904.profileLo box_904.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_904_ok
theorem branch_box_904_nonnegative : ∀ j, 0 ≤ branch_box_904.lower j ∧ 0 ≤ branch_box_904.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_904, Box.profileLo, Box.profileHi, box_904]
theorem leaf_904_BranchSafe : CertificateConsequences.BranchSafe branch_box_904 := by
  left; refine ⟨branch_box_904_nonnegative, ?_⟩
  intro z hz; exact leaf_904_sound hz

theorem leaf_915_ok : checkAt 527 1000 box_915 cert_915 = true := by
  have h := List.all_eq_true.mp batch_18_03_ok accepted_915 (by simp [batch_18_03_values])
  exact h
theorem leaf_915_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_915.profileLo box_915.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_915_ok
theorem branch_box_915_nonnegative : ∀ j, 0 ≤ branch_box_915.lower j ∧ 0 ≤ branch_box_915.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_915, Box.profileLo, Box.profileHi, box_915]
theorem leaf_915_BranchSafe : CertificateConsequences.BranchSafe branch_box_915 := by
  left; refine ⟨branch_box_915_nonnegative, ?_⟩
  intro z hz; exact leaf_915_sound hz

theorem leaf_917_ok : checkAt 527 1000 box_917 cert_917 = true := by
  have h := List.all_eq_true.mp batch_18_04_ok accepted_917 (by simp [batch_18_04_values])
  exact h
theorem leaf_917_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_917.profileLo box_917.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_917_ok
theorem branch_box_917_nonnegative : ∀ j, 0 ≤ branch_box_917.lower j ∧ 0 ≤ branch_box_917.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_917, Box.profileLo, Box.profileHi, box_917]
theorem leaf_917_BranchSafe : CertificateConsequences.BranchSafe branch_box_917 := by
  left; refine ⟨branch_box_917_nonnegative, ?_⟩
  intro z hz; exact leaf_917_sound hz

theorem leaf_918_ok : checkAt 527 1000 box_918 cert_918 = true := by
  have h := List.all_eq_true.mp batch_18_05_ok accepted_918 (by simp [batch_18_05_values])
  exact h
theorem leaf_918_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_918.profileLo box_918.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_918_ok
theorem branch_box_918_nonnegative : ∀ j, 0 ≤ branch_box_918.lower j ∧ 0 ≤ branch_box_918.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_918, Box.profileLo, Box.profileHi, box_918]
theorem leaf_918_BranchSafe : CertificateConsequences.BranchSafe branch_box_918 := by
  left; refine ⟨branch_box_918_nonnegative, ?_⟩
  intro z hz; exact leaf_918_sound hz

theorem leaf_920_ok : checkAt 527 1000 box_920 cert_920 = true := by
  have h := List.all_eq_true.mp batch_18_06_ok accepted_920 (by simp [batch_18_06_values])
  exact h
theorem leaf_920_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_920.profileLo box_920.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_920_ok
theorem branch_box_920_nonnegative : ∀ j, 0 ≤ branch_box_920.lower j ∧ 0 ≤ branch_box_920.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_920, Box.profileLo, Box.profileHi, box_920]
theorem leaf_920_BranchSafe : CertificateConsequences.BranchSafe branch_box_920 := by
  left; refine ⟨branch_box_920_nonnegative, ?_⟩
  intro z hz; exact leaf_920_sound hz

theorem leaf_922_ok : checkAt 527 1000 box_922 cert_922 = true := by
  have h := List.all_eq_true.mp batch_18_07_ok accepted_922 (by simp [batch_18_07_values])
  exact h
theorem leaf_922_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_922.profileLo box_922.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_922_ok
theorem branch_box_922_nonnegative : ∀ j, 0 ≤ branch_box_922.lower j ∧ 0 ≤ branch_box_922.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_922, Box.profileLo, Box.profileHi, box_922]
theorem leaf_922_BranchSafe : CertificateConsequences.BranchSafe branch_box_922 := by
  left; refine ⟨branch_box_922_nonnegative, ?_⟩
  intro z hz; exact leaf_922_sound hz

theorem leaf_926_ok : checkAt 527 1000 box_926 cert_926 = true := by
  have h := List.all_eq_true.mp batch_18_08_ok accepted_926 (by simp [batch_18_08_values])
  exact h
theorem leaf_926_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_926.profileLo box_926.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_926_ok
theorem branch_box_926_nonnegative : ∀ j, 0 ≤ branch_box_926.lower j ∧ 0 ≤ branch_box_926.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_926, Box.profileLo, Box.profileHi, box_926]
theorem leaf_926_BranchSafe : CertificateConsequences.BranchSafe branch_box_926 := by
  left; refine ⟨branch_box_926_nonnegative, ?_⟩
  intro z hz; exact leaf_926_sound hz

theorem leaf_928_ok : checkAt 527 1000 box_928 cert_928 = true := by
  have h := List.all_eq_true.mp batch_18_09_ok accepted_928 (by simp [batch_18_09_values])
  exact h
theorem leaf_928_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_928.profileLo box_928.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_928_ok
theorem branch_box_928_nonnegative : ∀ j, 0 ≤ branch_box_928.lower j ∧ 0 ≤ branch_box_928.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_928, Box.profileLo, Box.profileHi, box_928]
theorem leaf_928_BranchSafe : CertificateConsequences.BranchSafe branch_box_928 := by
  left; refine ⟨branch_box_928_nonnegative, ?_⟩
  intro z hz; exact leaf_928_sound hz

theorem leaf_930_ok : checkAt 527 1000 box_930 cert_930 = true := by
  have h := List.all_eq_true.mp batch_18_10_ok accepted_930 (by simp [batch_18_10_values])
  exact h
theorem leaf_930_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_930.profileLo box_930.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_930_ok
theorem branch_box_930_nonnegative : ∀ j, 0 ≤ branch_box_930.lower j ∧ 0 ≤ branch_box_930.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_930, Box.profileLo, Box.profileHi, box_930]
theorem leaf_930_BranchSafe : CertificateConsequences.BranchSafe branch_box_930 := by
  left; refine ⟨branch_box_930_nonnegative, ?_⟩
  intro z hz; exact leaf_930_sound hz

theorem leaf_931_ok : checkAt 527 1000 box_931 cert_931 = true := by
  have h := List.all_eq_true.mp batch_18_11_ok accepted_931 (by simp [batch_18_11_values])
  exact h
theorem leaf_931_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_931.profileLo box_931.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_931_ok
theorem branch_box_931_nonnegative : ∀ j, 0 ≤ branch_box_931.lower j ∧ 0 ≤ branch_box_931.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_931, Box.profileLo, Box.profileHi, box_931]
theorem leaf_931_BranchSafe : CertificateConsequences.BranchSafe branch_box_931 := by
  left; refine ⟨branch_box_931_nonnegative, ?_⟩
  intro z hz; exact leaf_931_sound hz

theorem leaf_932_ok : checkAt 527 1000 box_932 cert_932 = true := by
  have h := List.all_eq_true.mp batch_18_12_ok accepted_932 (by simp [batch_18_12_values])
  exact h
theorem leaf_932_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_932.profileLo box_932.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_932_ok
theorem branch_box_932_nonnegative : ∀ j, 0 ≤ branch_box_932.lower j ∧ 0 ≤ branch_box_932.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_932, Box.profileLo, Box.profileHi, box_932]
theorem leaf_932_BranchSafe : CertificateConsequences.BranchSafe branch_box_932 := by
  left; refine ⟨branch_box_932_nonnegative, ?_⟩
  intro z hz; exact leaf_932_sound hz

theorem leaf_933_ok : checkAt 527 1000 box_933 cert_933 = true := by
  have h := List.all_eq_true.mp batch_18_13_ok accepted_933 (by simp [batch_18_13_values])
  exact h
theorem leaf_933_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_933.profileLo box_933.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_933_ok
theorem branch_box_933_nonnegative : ∀ j, 0 ≤ branch_box_933.lower j ∧ 0 ≤ branch_box_933.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_933, Box.profileLo, Box.profileHi, box_933]
theorem leaf_933_BranchSafe : CertificateConsequences.BranchSafe branch_box_933 := by
  left; refine ⟨branch_box_933_nonnegative, ?_⟩
  intro z hz; exact leaf_933_sound hz

theorem leaf_935_ok : checkAt 527 1000 box_935 cert_935 = true := by
  have h := List.all_eq_true.mp batch_18_14_ok accepted_935 (by simp [batch_18_14_values])
  exact h
theorem leaf_935_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_935.profileLo box_935.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_935_ok
theorem branch_box_935_nonnegative : ∀ j, 0 ≤ branch_box_935.lower j ∧ 0 ≤ branch_box_935.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_935, Box.profileLo, Box.profileHi, box_935]
theorem leaf_935_BranchSafe : CertificateConsequences.BranchSafe branch_box_935 := by
  left; refine ⟨branch_box_935_nonnegative, ?_⟩
  intro z hz; exact leaf_935_sound hz

theorem leaf_936_ok : checkAt 527 1000 box_936 cert_936 = true := by
  have h := List.all_eq_true.mp batch_18_15_ok accepted_936 (by simp [batch_18_15_values])
  exact h
theorem leaf_936_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_936.profileLo box_936.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_936_ok
theorem branch_box_936_nonnegative : ∀ j, 0 ≤ branch_box_936.lower j ∧ 0 ≤ branch_box_936.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_936, Box.profileLo, Box.profileHi, box_936]
theorem leaf_936_BranchSafe : CertificateConsequences.BranchSafe branch_box_936 := by
  left; refine ⟨branch_box_936_nonnegative, ?_⟩
  intro z hz; exact leaf_936_sound hz

theorem leaf_937_ok : checkAt 527 1000 box_937 cert_937 = true := by
  have h := List.all_eq_true.mp batch_18_16_ok accepted_937 (by simp [batch_18_16_values])
  exact h
theorem leaf_937_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_937.profileLo box_937.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_937_ok
theorem branch_box_937_nonnegative : ∀ j, 0 ≤ branch_box_937.lower j ∧ 0 ≤ branch_box_937.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_937, Box.profileLo, Box.profileHi, box_937]
theorem leaf_937_BranchSafe : CertificateConsequences.BranchSafe branch_box_937 := by
  left; refine ⟨branch_box_937_nonnegative, ?_⟩
  intro z hz; exact leaf_937_sound hz

theorem leaf_939_ok : checkAt 527 1000 box_939 cert_939 = true := by
  have h := List.all_eq_true.mp batch_18_17_ok accepted_939 (by simp [batch_18_17_values])
  exact h
theorem leaf_939_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_939.profileLo box_939.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_939_ok
theorem branch_box_939_nonnegative : ∀ j, 0 ≤ branch_box_939.lower j ∧ 0 ≤ branch_box_939.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_939, Box.profileLo, Box.profileHi, box_939]
theorem leaf_939_BranchSafe : CertificateConsequences.BranchSafe branch_box_939 := by
  left; refine ⟨branch_box_939_nonnegative, ?_⟩
  intro z hz; exact leaf_939_sound hz

theorem leaf_940_ok : checkAt 527 1000 box_940 cert_940 = true := by
  have h := List.all_eq_true.mp batch_18_18_ok accepted_940 (by simp [batch_18_18_values])
  exact h
theorem leaf_940_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_940.profileLo box_940.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_940_ok
theorem branch_box_940_nonnegative : ∀ j, 0 ≤ branch_box_940.lower j ∧ 0 ≤ branch_box_940.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_940, Box.profileLo, Box.profileHi, box_940]
theorem leaf_940_BranchSafe : CertificateConsequences.BranchSafe branch_box_940 := by
  left; refine ⟨branch_box_940_nonnegative, ?_⟩
  intro z hz; exact leaf_940_sound hz

theorem leaf_943_ok : checkAt 527 1000 box_943 cert_943 = true := by
  have h := List.all_eq_true.mp batch_18_19_ok accepted_943 (by simp [batch_18_19_values])
  exact h
theorem leaf_943_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_943.profileLo box_943.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_943_ok
theorem branch_box_943_nonnegative : ∀ j, 0 ≤ branch_box_943.lower j ∧ 0 ≤ branch_box_943.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_943, Box.profileLo, Box.profileHi, box_943]
theorem leaf_943_BranchSafe : CertificateConsequences.BranchSafe branch_box_943 := by
  left; refine ⟨branch_box_943_nonnegative, ?_⟩
  intro z hz; exact leaf_943_sound hz

theorem leaf_945_ok : checkAt 527 1000 box_945 cert_945 = true := by
  have h := List.all_eq_true.mp batch_18_20_ok accepted_945 (by simp [batch_18_20_values])
  exact h
theorem leaf_945_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_945.profileLo box_945.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_945_ok
theorem branch_box_945_nonnegative : ∀ j, 0 ≤ branch_box_945.lower j ∧ 0 ≤ branch_box_945.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_945, Box.profileLo, Box.profileHi, box_945]
theorem leaf_945_BranchSafe : CertificateConsequences.BranchSafe branch_box_945 := by
  left; refine ⟨branch_box_945_nonnegative, ?_⟩
  intro z hz; exact leaf_945_sound hz

theorem leaf_946_ok : checkAt 527 1000 box_946 cert_946 = true := by
  have h := List.all_eq_true.mp batch_18_21_ok accepted_946 (by simp [batch_18_21_values])
  exact h
theorem leaf_946_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_946.profileLo box_946.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_946_ok
theorem branch_box_946_nonnegative : ∀ j, 0 ≤ branch_box_946.lower j ∧ 0 ≤ branch_box_946.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_946, Box.profileLo, Box.profileHi, box_946]
theorem leaf_946_BranchSafe : CertificateConsequences.BranchSafe branch_box_946 := by
  left; refine ⟨branch_box_946_nonnegative, ?_⟩
  intro z hz; exact leaf_946_sound hz

theorem leaf_947_ok : checkAt 527 1000 box_947 cert_947 = true := by
  have h := List.all_eq_true.mp batch_18_22_ok accepted_947 (by simp [batch_18_22_values])
  exact h
theorem leaf_947_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_947.profileLo box_947.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_947_ok
theorem branch_box_947_nonnegative : ∀ j, 0 ≤ branch_box_947.lower j ∧ 0 ≤ branch_box_947.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_947, Box.profileLo, Box.profileHi, box_947]
theorem leaf_947_BranchSafe : CertificateConsequences.BranchSafe branch_box_947 := by
  left; refine ⟨branch_box_947_nonnegative, ?_⟩
  intro z hz; exact leaf_947_sound hz

theorem leaf_949_ok : checkAt 527 1000 box_949 cert_949 = true := by
  have h := List.all_eq_true.mp batch_18_23_ok accepted_949 (by simp [batch_18_23_values])
  exact h
theorem leaf_949_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_949.profileLo box_949.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_949_ok
theorem branch_box_949_nonnegative : ∀ j, 0 ≤ branch_box_949.lower j ∧ 0 ≤ branch_box_949.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_949, Box.profileLo, Box.profileHi, box_949]
theorem leaf_949_BranchSafe : CertificateConsequences.BranchSafe branch_box_949 := by
  left; refine ⟨branch_box_949_nonnegative, ?_⟩
  intro z hz; exact leaf_949_sound hz

#print axioms batch_18_00_ok
#print axioms leaf_900_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
