import PeaceableQueens.UpperBound.Generated.Even.C527Scaled98Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_98_00_values : List Bool := [accepted_4901]
theorem batch_98_00_ok : batch_98_00_values.all id = true := by decide

def batch_98_01_values : List Bool := [accepted_4903]
theorem batch_98_01_ok : batch_98_01_values.all id = true := by decide

def batch_98_02_values : List Bool := [accepted_4905]
theorem batch_98_02_ok : batch_98_02_values.all id = true := by decide

def batch_98_03_values : List Bool := [accepted_4906]
theorem batch_98_03_ok : batch_98_03_values.all id = true := by decide

def batch_98_04_values : List Bool := [accepted_4909]
theorem batch_98_04_ok : batch_98_04_values.all id = true := by decide

def batch_98_05_values : List Bool := [accepted_4911]
theorem batch_98_05_ok : batch_98_05_values.all id = true := by decide

def batch_98_06_values : List Bool := [accepted_4912]
theorem batch_98_06_ok : batch_98_06_values.all id = true := by decide

def batch_98_07_values : List Bool := [accepted_4915]
theorem batch_98_07_ok : batch_98_07_values.all id = true := by decide

def batch_98_08_values : List Bool := [accepted_4916]
theorem batch_98_08_ok : batch_98_08_values.all id = true := by decide

def batch_98_09_values : List Bool := [accepted_4919]
theorem batch_98_09_ok : batch_98_09_values.all id = true := by decide

def batch_98_10_values : List Bool := [accepted_4920]
theorem batch_98_10_ok : batch_98_10_values.all id = true := by decide

def batch_98_11_values : List Bool := [accepted_4921]
theorem batch_98_11_ok : batch_98_11_values.all id = true := by decide

def batch_98_12_values : List Bool := [accepted_4923]
theorem batch_98_12_ok : batch_98_12_values.all id = true := by decide

def batch_98_13_values : List Bool := [accepted_4924]
theorem batch_98_13_ok : batch_98_13_values.all id = true := by decide

def batch_98_14_values : List Bool := [accepted_4929]
theorem batch_98_14_ok : batch_98_14_values.all id = true := by decide

def batch_98_15_values : List Bool := [accepted_4931]
theorem batch_98_15_ok : batch_98_15_values.all id = true := by decide

def batch_98_16_values : List Bool := [accepted_4932]
theorem batch_98_16_ok : batch_98_16_values.all id = true := by decide

def batch_98_17_values : List Bool := [accepted_4933]
theorem batch_98_17_ok : batch_98_17_values.all id = true := by decide

def batch_98_18_values : List Bool := [accepted_4935]
theorem batch_98_18_ok : batch_98_18_values.all id = true := by decide

def batch_98_19_values : List Bool := [accepted_4936]
theorem batch_98_19_ok : batch_98_19_values.all id = true := by decide

def batch_98_20_values : List Bool := [accepted_4939]
theorem batch_98_20_ok : batch_98_20_values.all id = true := by decide

def batch_98_21_values : List Bool := [accepted_4940]
theorem batch_98_21_ok : batch_98_21_values.all id = true := by decide

def batch_98_22_values : List Bool := [accepted_4945]
theorem batch_98_22_ok : batch_98_22_values.all id = true := by decide

def batch_98_23_values : List Bool := [accepted_4946]
theorem batch_98_23_ok : batch_98_23_values.all id = true := by decide

def batch_98_24_values : List Bool := [accepted_4947]
theorem batch_98_24_ok : batch_98_24_values.all id = true := by decide

def batch_98_25_values : List Bool := [accepted_4949]
theorem batch_98_25_ok : batch_98_25_values.all id = true := by decide

theorem leaf_4901_ok : checkAt 527 1000 box_4901 cert_4901 = true := by
  have h := List.all_eq_true.mp batch_98_00_ok accepted_4901 (by simp [batch_98_00_values])
  exact h
theorem leaf_4901_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4901.profileLo box_4901.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4901_ok
theorem branch_box_4901_nonnegative : ∀ j, 0 ≤ branch_box_4901.lower j ∧ 0 ≤ branch_box_4901.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4901, Box.profileLo, Box.profileHi, box_4901]
theorem leaf_4901_BranchSafe : CertificateConsequences.BranchSafe branch_box_4901 := by
  left; refine ⟨branch_box_4901_nonnegative, ?_⟩
  intro z hz; exact leaf_4901_sound hz

theorem leaf_4903_ok : checkAt 527 1000 box_4903 cert_4903 = true := by
  have h := List.all_eq_true.mp batch_98_01_ok accepted_4903 (by simp [batch_98_01_values])
  exact h
theorem leaf_4903_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4903.profileLo box_4903.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4903_ok
theorem branch_box_4903_nonnegative : ∀ j, 0 ≤ branch_box_4903.lower j ∧ 0 ≤ branch_box_4903.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4903, Box.profileLo, Box.profileHi, box_4903]
theorem leaf_4903_BranchSafe : CertificateConsequences.BranchSafe branch_box_4903 := by
  left; refine ⟨branch_box_4903_nonnegative, ?_⟩
  intro z hz; exact leaf_4903_sound hz

theorem leaf_4905_ok : checkAt 527 1000 box_4905 cert_4905 = true := by
  have h := List.all_eq_true.mp batch_98_02_ok accepted_4905 (by simp [batch_98_02_values])
  exact h
theorem leaf_4905_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4905.profileLo box_4905.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4905_ok
theorem branch_box_4905_nonnegative : ∀ j, 0 ≤ branch_box_4905.lower j ∧ 0 ≤ branch_box_4905.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4905, Box.profileLo, Box.profileHi, box_4905]
theorem leaf_4905_BranchSafe : CertificateConsequences.BranchSafe branch_box_4905 := by
  left; refine ⟨branch_box_4905_nonnegative, ?_⟩
  intro z hz; exact leaf_4905_sound hz

theorem leaf_4906_ok : checkAt 527 1000 box_4906 cert_4906 = true := by
  have h := List.all_eq_true.mp batch_98_03_ok accepted_4906 (by simp [batch_98_03_values])
  exact h
theorem leaf_4906_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4906.profileLo box_4906.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4906_ok
theorem branch_box_4906_nonnegative : ∀ j, 0 ≤ branch_box_4906.lower j ∧ 0 ≤ branch_box_4906.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4906, Box.profileLo, Box.profileHi, box_4906]
theorem leaf_4906_BranchSafe : CertificateConsequences.BranchSafe branch_box_4906 := by
  left; refine ⟨branch_box_4906_nonnegative, ?_⟩
  intro z hz; exact leaf_4906_sound hz

theorem leaf_4909_ok : checkAt 527 1000 box_4909 cert_4909 = true := by
  have h := List.all_eq_true.mp batch_98_04_ok accepted_4909 (by simp [batch_98_04_values])
  exact h
theorem leaf_4909_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4909.profileLo box_4909.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4909_ok
theorem branch_box_4909_nonnegative : ∀ j, 0 ≤ branch_box_4909.lower j ∧ 0 ≤ branch_box_4909.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4909, Box.profileLo, Box.profileHi, box_4909]
theorem leaf_4909_BranchSafe : CertificateConsequences.BranchSafe branch_box_4909 := by
  left; refine ⟨branch_box_4909_nonnegative, ?_⟩
  intro z hz; exact leaf_4909_sound hz

theorem leaf_4911_ok : checkAt 527 1000 box_4911 cert_4911 = true := by
  have h := List.all_eq_true.mp batch_98_05_ok accepted_4911 (by simp [batch_98_05_values])
  exact h
theorem leaf_4911_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4911.profileLo box_4911.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4911_ok
theorem branch_box_4911_nonnegative : ∀ j, 0 ≤ branch_box_4911.lower j ∧ 0 ≤ branch_box_4911.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4911, Box.profileLo, Box.profileHi, box_4911]
theorem leaf_4911_BranchSafe : CertificateConsequences.BranchSafe branch_box_4911 := by
  left; refine ⟨branch_box_4911_nonnegative, ?_⟩
  intro z hz; exact leaf_4911_sound hz

theorem leaf_4912_ok : checkAt 527 1000 box_4912 cert_4912 = true := by
  have h := List.all_eq_true.mp batch_98_06_ok accepted_4912 (by simp [batch_98_06_values])
  exact h
theorem leaf_4912_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4912.profileLo box_4912.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4912_ok
theorem branch_box_4912_nonnegative : ∀ j, 0 ≤ branch_box_4912.lower j ∧ 0 ≤ branch_box_4912.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4912, Box.profileLo, Box.profileHi, box_4912]
theorem leaf_4912_BranchSafe : CertificateConsequences.BranchSafe branch_box_4912 := by
  left; refine ⟨branch_box_4912_nonnegative, ?_⟩
  intro z hz; exact leaf_4912_sound hz

theorem leaf_4915_ok : checkAt 527 1000 box_4915 cert_4915 = true := by
  have h := List.all_eq_true.mp batch_98_07_ok accepted_4915 (by simp [batch_98_07_values])
  exact h
theorem leaf_4915_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4915.profileLo box_4915.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4915_ok
theorem branch_box_4915_nonnegative : ∀ j, 0 ≤ branch_box_4915.lower j ∧ 0 ≤ branch_box_4915.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4915, Box.profileLo, Box.profileHi, box_4915]
theorem leaf_4915_BranchSafe : CertificateConsequences.BranchSafe branch_box_4915 := by
  left; refine ⟨branch_box_4915_nonnegative, ?_⟩
  intro z hz; exact leaf_4915_sound hz

theorem leaf_4916_ok : checkAt 527 1000 box_4916 cert_4916 = true := by
  have h := List.all_eq_true.mp batch_98_08_ok accepted_4916 (by simp [batch_98_08_values])
  exact h
theorem leaf_4916_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4916.profileLo box_4916.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4916_ok
theorem branch_box_4916_nonnegative : ∀ j, 0 ≤ branch_box_4916.lower j ∧ 0 ≤ branch_box_4916.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4916, Box.profileLo, Box.profileHi, box_4916]
theorem leaf_4916_BranchSafe : CertificateConsequences.BranchSafe branch_box_4916 := by
  left; refine ⟨branch_box_4916_nonnegative, ?_⟩
  intro z hz; exact leaf_4916_sound hz

theorem leaf_4919_ok : checkAt 527 1000 box_4919 cert_4919 = true := by
  have h := List.all_eq_true.mp batch_98_09_ok accepted_4919 (by simp [batch_98_09_values])
  exact h
theorem leaf_4919_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4919.profileLo box_4919.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4919_ok
theorem branch_box_4919_nonnegative : ∀ j, 0 ≤ branch_box_4919.lower j ∧ 0 ≤ branch_box_4919.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4919, Box.profileLo, Box.profileHi, box_4919]
theorem leaf_4919_BranchSafe : CertificateConsequences.BranchSafe branch_box_4919 := by
  left; refine ⟨branch_box_4919_nonnegative, ?_⟩
  intro z hz; exact leaf_4919_sound hz

theorem leaf_4920_ok : checkAt 527 1000 box_4920 cert_4920 = true := by
  have h := List.all_eq_true.mp batch_98_10_ok accepted_4920 (by simp [batch_98_10_values])
  exact h
theorem leaf_4920_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4920.profileLo box_4920.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4920_ok
theorem branch_box_4920_nonnegative : ∀ j, 0 ≤ branch_box_4920.lower j ∧ 0 ≤ branch_box_4920.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4920, Box.profileLo, Box.profileHi, box_4920]
theorem leaf_4920_BranchSafe : CertificateConsequences.BranchSafe branch_box_4920 := by
  left; refine ⟨branch_box_4920_nonnegative, ?_⟩
  intro z hz; exact leaf_4920_sound hz

theorem leaf_4921_ok : checkAt 527 1000 box_4921 cert_4921 = true := by
  have h := List.all_eq_true.mp batch_98_11_ok accepted_4921 (by simp [batch_98_11_values])
  exact h
theorem leaf_4921_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4921.profileLo box_4921.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4921_ok
theorem branch_box_4921_nonnegative : ∀ j, 0 ≤ branch_box_4921.lower j ∧ 0 ≤ branch_box_4921.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4921, Box.profileLo, Box.profileHi, box_4921]
theorem leaf_4921_BranchSafe : CertificateConsequences.BranchSafe branch_box_4921 := by
  left; refine ⟨branch_box_4921_nonnegative, ?_⟩
  intro z hz; exact leaf_4921_sound hz

theorem leaf_4923_ok : checkAt 527 1000 box_4923 cert_4923 = true := by
  have h := List.all_eq_true.mp batch_98_12_ok accepted_4923 (by simp [batch_98_12_values])
  exact h
theorem leaf_4923_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4923.profileLo box_4923.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4923_ok
theorem branch_box_4923_nonnegative : ∀ j, 0 ≤ branch_box_4923.lower j ∧ 0 ≤ branch_box_4923.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4923, Box.profileLo, Box.profileHi, box_4923]
theorem leaf_4923_BranchSafe : CertificateConsequences.BranchSafe branch_box_4923 := by
  left; refine ⟨branch_box_4923_nonnegative, ?_⟩
  intro z hz; exact leaf_4923_sound hz

theorem leaf_4924_ok : checkAt 527 1000 box_4924 cert_4924 = true := by
  have h := List.all_eq_true.mp batch_98_13_ok accepted_4924 (by simp [batch_98_13_values])
  exact h
theorem leaf_4924_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4924.profileLo box_4924.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4924_ok
theorem branch_box_4924_nonnegative : ∀ j, 0 ≤ branch_box_4924.lower j ∧ 0 ≤ branch_box_4924.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4924, Box.profileLo, Box.profileHi, box_4924]
theorem leaf_4924_BranchSafe : CertificateConsequences.BranchSafe branch_box_4924 := by
  left; refine ⟨branch_box_4924_nonnegative, ?_⟩
  intro z hz; exact leaf_4924_sound hz

theorem leaf_4929_ok : checkAt 527 1000 box_4929 cert_4929 = true := by
  have h := List.all_eq_true.mp batch_98_14_ok accepted_4929 (by simp [batch_98_14_values])
  exact h
theorem leaf_4929_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4929.profileLo box_4929.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4929_ok
theorem branch_box_4929_nonnegative : ∀ j, 0 ≤ branch_box_4929.lower j ∧ 0 ≤ branch_box_4929.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4929, Box.profileLo, Box.profileHi, box_4929]
theorem leaf_4929_BranchSafe : CertificateConsequences.BranchSafe branch_box_4929 := by
  left; refine ⟨branch_box_4929_nonnegative, ?_⟩
  intro z hz; exact leaf_4929_sound hz

theorem leaf_4931_ok : checkAt 527 1000 box_4931 cert_4931 = true := by
  have h := List.all_eq_true.mp batch_98_15_ok accepted_4931 (by simp [batch_98_15_values])
  exact h
theorem leaf_4931_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4931.profileLo box_4931.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4931_ok
theorem branch_box_4931_nonnegative : ∀ j, 0 ≤ branch_box_4931.lower j ∧ 0 ≤ branch_box_4931.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4931, Box.profileLo, Box.profileHi, box_4931]
theorem leaf_4931_BranchSafe : CertificateConsequences.BranchSafe branch_box_4931 := by
  left; refine ⟨branch_box_4931_nonnegative, ?_⟩
  intro z hz; exact leaf_4931_sound hz

theorem leaf_4932_ok : checkAt 527 1000 box_4932 cert_4932 = true := by
  have h := List.all_eq_true.mp batch_98_16_ok accepted_4932 (by simp [batch_98_16_values])
  exact h
theorem leaf_4932_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4932.profileLo box_4932.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4932_ok
theorem branch_box_4932_nonnegative : ∀ j, 0 ≤ branch_box_4932.lower j ∧ 0 ≤ branch_box_4932.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4932, Box.profileLo, Box.profileHi, box_4932]
theorem leaf_4932_BranchSafe : CertificateConsequences.BranchSafe branch_box_4932 := by
  left; refine ⟨branch_box_4932_nonnegative, ?_⟩
  intro z hz; exact leaf_4932_sound hz

theorem leaf_4933_ok : checkAt 527 1000 box_4933 cert_4933 = true := by
  have h := List.all_eq_true.mp batch_98_17_ok accepted_4933 (by simp [batch_98_17_values])
  exact h
theorem leaf_4933_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4933.profileLo box_4933.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4933_ok
theorem branch_box_4933_nonnegative : ∀ j, 0 ≤ branch_box_4933.lower j ∧ 0 ≤ branch_box_4933.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4933, Box.profileLo, Box.profileHi, box_4933]
theorem leaf_4933_BranchSafe : CertificateConsequences.BranchSafe branch_box_4933 := by
  left; refine ⟨branch_box_4933_nonnegative, ?_⟩
  intro z hz; exact leaf_4933_sound hz

theorem leaf_4935_ok : checkAt 527 1000 box_4935 cert_4935 = true := by
  have h := List.all_eq_true.mp batch_98_18_ok accepted_4935 (by simp [batch_98_18_values])
  exact h
theorem leaf_4935_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4935.profileLo box_4935.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4935_ok
theorem branch_box_4935_nonnegative : ∀ j, 0 ≤ branch_box_4935.lower j ∧ 0 ≤ branch_box_4935.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4935, Box.profileLo, Box.profileHi, box_4935]
theorem leaf_4935_BranchSafe : CertificateConsequences.BranchSafe branch_box_4935 := by
  left; refine ⟨branch_box_4935_nonnegative, ?_⟩
  intro z hz; exact leaf_4935_sound hz

theorem leaf_4936_ok : checkAt 527 1000 box_4936 cert_4936 = true := by
  have h := List.all_eq_true.mp batch_98_19_ok accepted_4936 (by simp [batch_98_19_values])
  exact h
theorem leaf_4936_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4936.profileLo box_4936.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4936_ok
theorem branch_box_4936_nonnegative : ∀ j, 0 ≤ branch_box_4936.lower j ∧ 0 ≤ branch_box_4936.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4936, Box.profileLo, Box.profileHi, box_4936]
theorem leaf_4936_BranchSafe : CertificateConsequences.BranchSafe branch_box_4936 := by
  left; refine ⟨branch_box_4936_nonnegative, ?_⟩
  intro z hz; exact leaf_4936_sound hz

theorem leaf_4939_ok : checkAt 527 1000 box_4939 cert_4939 = true := by
  have h := List.all_eq_true.mp batch_98_20_ok accepted_4939 (by simp [batch_98_20_values])
  exact h
theorem leaf_4939_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4939.profileLo box_4939.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4939_ok
theorem branch_box_4939_nonnegative : ∀ j, 0 ≤ branch_box_4939.lower j ∧ 0 ≤ branch_box_4939.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4939, Box.profileLo, Box.profileHi, box_4939]
theorem leaf_4939_BranchSafe : CertificateConsequences.BranchSafe branch_box_4939 := by
  left; refine ⟨branch_box_4939_nonnegative, ?_⟩
  intro z hz; exact leaf_4939_sound hz

theorem leaf_4940_ok : checkAt 527 1000 box_4940 cert_4940 = true := by
  have h := List.all_eq_true.mp batch_98_21_ok accepted_4940 (by simp [batch_98_21_values])
  exact h
theorem leaf_4940_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4940.profileLo box_4940.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4940_ok
theorem branch_box_4940_nonnegative : ∀ j, 0 ≤ branch_box_4940.lower j ∧ 0 ≤ branch_box_4940.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4940, Box.profileLo, Box.profileHi, box_4940]
theorem leaf_4940_BranchSafe : CertificateConsequences.BranchSafe branch_box_4940 := by
  left; refine ⟨branch_box_4940_nonnegative, ?_⟩
  intro z hz; exact leaf_4940_sound hz

theorem leaf_4945_ok : checkAt 527 1000 box_4945 cert_4945 = true := by
  have h := List.all_eq_true.mp batch_98_22_ok accepted_4945 (by simp [batch_98_22_values])
  exact h
theorem leaf_4945_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4945.profileLo box_4945.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4945_ok
theorem branch_box_4945_nonnegative : ∀ j, 0 ≤ branch_box_4945.lower j ∧ 0 ≤ branch_box_4945.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4945, Box.profileLo, Box.profileHi, box_4945]
theorem leaf_4945_BranchSafe : CertificateConsequences.BranchSafe branch_box_4945 := by
  left; refine ⟨branch_box_4945_nonnegative, ?_⟩
  intro z hz; exact leaf_4945_sound hz

theorem leaf_4946_ok : checkAt 527 1000 box_4946 cert_4946 = true := by
  have h := List.all_eq_true.mp batch_98_23_ok accepted_4946 (by simp [batch_98_23_values])
  exact h
theorem leaf_4946_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4946.profileLo box_4946.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4946_ok
theorem branch_box_4946_nonnegative : ∀ j, 0 ≤ branch_box_4946.lower j ∧ 0 ≤ branch_box_4946.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4946, Box.profileLo, Box.profileHi, box_4946]
theorem leaf_4946_BranchSafe : CertificateConsequences.BranchSafe branch_box_4946 := by
  left; refine ⟨branch_box_4946_nonnegative, ?_⟩
  intro z hz; exact leaf_4946_sound hz

theorem leaf_4947_ok : checkAt 527 1000 box_4947 cert_4947 = true := by
  have h := List.all_eq_true.mp batch_98_24_ok accepted_4947 (by simp [batch_98_24_values])
  exact h
theorem leaf_4947_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4947.profileLo box_4947.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4947_ok
theorem branch_box_4947_nonnegative : ∀ j, 0 ≤ branch_box_4947.lower j ∧ 0 ≤ branch_box_4947.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4947, Box.profileLo, Box.profileHi, box_4947]
theorem leaf_4947_BranchSafe : CertificateConsequences.BranchSafe branch_box_4947 := by
  left; refine ⟨branch_box_4947_nonnegative, ?_⟩
  intro z hz; exact leaf_4947_sound hz

theorem leaf_4949_ok : checkAt 527 1000 box_4949 cert_4949 = true := by
  have h := List.all_eq_true.mp batch_98_25_ok accepted_4949 (by simp [batch_98_25_values])
  exact h
theorem leaf_4949_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4949.profileLo box_4949.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4949_ok
theorem branch_box_4949_nonnegative : ∀ j, 0 ≤ branch_box_4949.lower j ∧ 0 ≤ branch_box_4949.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4949, Box.profileLo, Box.profileHi, box_4949]
theorem leaf_4949_BranchSafe : CertificateConsequences.BranchSafe branch_box_4949 := by
  left; refine ⟨branch_box_4949_nonnegative, ?_⟩
  intro z hz; exact leaf_4949_sound hz

#print axioms batch_98_00_ok
#print axioms leaf_4901_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
