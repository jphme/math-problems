import PeaceableQueens.UpperBound.Generated.Even.CoreScaled18Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_18_00_values : List Bool := [accepted_901]
theorem batch_18_00_ok : batch_18_00_values.all id = true := by decide

def batch_18_01_values : List Bool := [accepted_903]
theorem batch_18_01_ok : batch_18_01_values.all id = true := by decide

def batch_18_02_values : List Bool := [accepted_906]
theorem batch_18_02_ok : batch_18_02_values.all id = true := by decide

def batch_18_03_values : List Bool := [accepted_911]
theorem batch_18_03_ok : batch_18_03_values.all id = true := by decide

def batch_18_04_values : List Bool := [accepted_917]
theorem batch_18_04_ok : batch_18_04_values.all id = true := by decide

def batch_18_05_values : List Bool := [accepted_919]
theorem batch_18_05_ok : batch_18_05_values.all id = true := by decide

def batch_18_06_values : List Bool := [accepted_922]
theorem batch_18_06_ok : batch_18_06_values.all id = true := by decide

def batch_18_07_values : List Bool := [accepted_923]
theorem batch_18_07_ok : batch_18_07_values.all id = true := by decide

def batch_18_08_values : List Bool := [accepted_925]
theorem batch_18_08_ok : batch_18_08_values.all id = true := by decide

def batch_18_09_values : List Bool := [accepted_927]
theorem batch_18_09_ok : batch_18_09_values.all id = true := by decide

def batch_18_10_values : List Bool := [accepted_932]
theorem batch_18_10_ok : batch_18_10_values.all id = true := by decide

def batch_18_11_values : List Bool := [accepted_934]
theorem batch_18_11_ok : batch_18_11_values.all id = true := by decide

def batch_18_12_values : List Bool := [accepted_935]
theorem batch_18_12_ok : batch_18_12_values.all id = true := by decide

def batch_18_13_values : List Bool := [accepted_937]
theorem batch_18_13_ok : batch_18_13_values.all id = true := by decide

def batch_18_14_values : List Bool := [accepted_939]
theorem batch_18_14_ok : batch_18_14_values.all id = true := by decide

def batch_18_15_values : List Bool := [accepted_942]
theorem batch_18_15_ok : batch_18_15_values.all id = true := by decide

def batch_18_16_values : List Bool := [accepted_944]
theorem batch_18_16_ok : batch_18_16_values.all id = true := by decide

def batch_18_17_values : List Bool := [accepted_946]
theorem batch_18_17_ok : batch_18_17_values.all id = true := by decide

def batch_18_18_values : List Bool := [accepted_947]
theorem batch_18_18_ok : batch_18_18_values.all id = true := by decide

theorem leaf_901_ok : checkAt 527 1000 box_901 cert_901 = true := by
  have h := List.all_eq_true.mp batch_18_00_ok accepted_901 (by simp [batch_18_00_values])
  exact h
theorem leaf_901_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_901.profileLo box_901.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_901_ok
theorem branch_box_901_nonnegative : ∀ j, 0 ≤ branch_box_901.lower j ∧ 0 ≤ branch_box_901.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_901, Box.profileLo, Box.profileHi, box_901]
theorem leaf_901_BranchSafe : CertificateConsequences.BranchSafe branch_box_901 := by
  left; refine ⟨branch_box_901_nonnegative, ?_⟩
  intro z hz; exact leaf_901_sound hz

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

theorem leaf_906_ok : checkAt 527 1000 box_906 cert_906 = true := by
  have h := List.all_eq_true.mp batch_18_02_ok accepted_906 (by simp [batch_18_02_values])
  exact h
theorem leaf_906_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_906.profileLo box_906.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_906_ok
theorem branch_box_906_nonnegative : ∀ j, 0 ≤ branch_box_906.lower j ∧ 0 ≤ branch_box_906.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_906, Box.profileLo, Box.profileHi, box_906]
theorem leaf_906_BranchSafe : CertificateConsequences.BranchSafe branch_box_906 := by
  left; refine ⟨branch_box_906_nonnegative, ?_⟩
  intro z hz; exact leaf_906_sound hz

theorem leaf_911_ok : checkAt 527 1000 box_911 cert_911 = true := by
  have h := List.all_eq_true.mp batch_18_03_ok accepted_911 (by simp [batch_18_03_values])
  exact h
theorem leaf_911_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_911.profileLo box_911.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_911_ok
theorem branch_box_911_nonnegative : ∀ j, 0 ≤ branch_box_911.lower j ∧ 0 ≤ branch_box_911.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_911, Box.profileLo, Box.profileHi, box_911]
theorem leaf_911_BranchSafe : CertificateConsequences.BranchSafe branch_box_911 := by
  left; refine ⟨branch_box_911_nonnegative, ?_⟩
  intro z hz; exact leaf_911_sound hz

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

theorem leaf_919_ok : checkAt 527 1000 box_919 cert_919 = true := by
  have h := List.all_eq_true.mp batch_18_05_ok accepted_919 (by simp [batch_18_05_values])
  exact h
theorem leaf_919_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_919.profileLo box_919.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_919_ok
theorem branch_box_919_nonnegative : ∀ j, 0 ≤ branch_box_919.lower j ∧ 0 ≤ branch_box_919.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_919, Box.profileLo, Box.profileHi, box_919]
theorem leaf_919_BranchSafe : CertificateConsequences.BranchSafe branch_box_919 := by
  left; refine ⟨branch_box_919_nonnegative, ?_⟩
  intro z hz; exact leaf_919_sound hz

theorem leaf_922_ok : checkAt 527 1000 box_922 cert_922 = true := by
  have h := List.all_eq_true.mp batch_18_06_ok accepted_922 (by simp [batch_18_06_values])
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

theorem leaf_923_ok : checkAt 527 1000 box_923 cert_923 = true := by
  have h := List.all_eq_true.mp batch_18_07_ok accepted_923 (by simp [batch_18_07_values])
  exact h
theorem leaf_923_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_923.profileLo box_923.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_923_ok
theorem branch_box_923_nonnegative : ∀ j, 0 ≤ branch_box_923.lower j ∧ 0 ≤ branch_box_923.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_923, Box.profileLo, Box.profileHi, box_923]
theorem leaf_923_BranchSafe : CertificateConsequences.BranchSafe branch_box_923 := by
  left; refine ⟨branch_box_923_nonnegative, ?_⟩
  intro z hz; exact leaf_923_sound hz

theorem leaf_925_ok : checkAt 527 1000 box_925 cert_925 = true := by
  have h := List.all_eq_true.mp batch_18_08_ok accepted_925 (by simp [batch_18_08_values])
  exact h
theorem leaf_925_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_925.profileLo box_925.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_925_ok
theorem branch_box_925_nonnegative : ∀ j, 0 ≤ branch_box_925.lower j ∧ 0 ≤ branch_box_925.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_925, Box.profileLo, Box.profileHi, box_925]
theorem leaf_925_BranchSafe : CertificateConsequences.BranchSafe branch_box_925 := by
  left; refine ⟨branch_box_925_nonnegative, ?_⟩
  intro z hz; exact leaf_925_sound hz

theorem leaf_927_ok : checkAt 527 1000 box_927 cert_927 = true := by
  have h := List.all_eq_true.mp batch_18_09_ok accepted_927 (by simp [batch_18_09_values])
  exact h
theorem leaf_927_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_927.profileLo box_927.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_927_ok
theorem branch_box_927_nonnegative : ∀ j, 0 ≤ branch_box_927.lower j ∧ 0 ≤ branch_box_927.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_927, Box.profileLo, Box.profileHi, box_927]
theorem leaf_927_BranchSafe : CertificateConsequences.BranchSafe branch_box_927 := by
  left; refine ⟨branch_box_927_nonnegative, ?_⟩
  intro z hz; exact leaf_927_sound hz

theorem leaf_932_ok : checkAt 527 1000 box_932 cert_932 = true := by
  have h := List.all_eq_true.mp batch_18_10_ok accepted_932 (by simp [batch_18_10_values])
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

theorem leaf_934_ok : checkAt 527 1000 box_934 cert_934 = true := by
  have h := List.all_eq_true.mp batch_18_11_ok accepted_934 (by simp [batch_18_11_values])
  exact h
theorem leaf_934_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_934.profileLo box_934.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_934_ok
theorem branch_box_934_nonnegative : ∀ j, 0 ≤ branch_box_934.lower j ∧ 0 ≤ branch_box_934.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_934, Box.profileLo, Box.profileHi, box_934]
theorem leaf_934_BranchSafe : CertificateConsequences.BranchSafe branch_box_934 := by
  left; refine ⟨branch_box_934_nonnegative, ?_⟩
  intro z hz; exact leaf_934_sound hz

theorem leaf_935_ok : checkAt 527 1000 box_935 cert_935 = true := by
  have h := List.all_eq_true.mp batch_18_12_ok accepted_935 (by simp [batch_18_12_values])
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

theorem leaf_937_ok : checkAt 527 1000 box_937 cert_937 = true := by
  have h := List.all_eq_true.mp batch_18_13_ok accepted_937 (by simp [batch_18_13_values])
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
  have h := List.all_eq_true.mp batch_18_14_ok accepted_939 (by simp [batch_18_14_values])
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

theorem leaf_942_ok : checkAt 527 1000 box_942 cert_942 = true := by
  have h := List.all_eq_true.mp batch_18_15_ok accepted_942 (by simp [batch_18_15_values])
  exact h
theorem leaf_942_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_942.profileLo box_942.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_942_ok
theorem branch_box_942_nonnegative : ∀ j, 0 ≤ branch_box_942.lower j ∧ 0 ≤ branch_box_942.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_942, Box.profileLo, Box.profileHi, box_942]
theorem leaf_942_BranchSafe : CertificateConsequences.BranchSafe branch_box_942 := by
  left; refine ⟨branch_box_942_nonnegative, ?_⟩
  intro z hz; exact leaf_942_sound hz

theorem leaf_944_ok : checkAt 527 1000 box_944 cert_944 = true := by
  have h := List.all_eq_true.mp batch_18_16_ok accepted_944 (by simp [batch_18_16_values])
  exact h
theorem leaf_944_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_944.profileLo box_944.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_944_ok
theorem branch_box_944_nonnegative : ∀ j, 0 ≤ branch_box_944.lower j ∧ 0 ≤ branch_box_944.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_944, Box.profileLo, Box.profileHi, box_944]
theorem leaf_944_BranchSafe : CertificateConsequences.BranchSafe branch_box_944 := by
  left; refine ⟨branch_box_944_nonnegative, ?_⟩
  intro z hz; exact leaf_944_sound hz

theorem leaf_946_ok : checkAt 527 1000 box_946 cert_946 = true := by
  have h := List.all_eq_true.mp batch_18_17_ok accepted_946 (by simp [batch_18_17_values])
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
  have h := List.all_eq_true.mp batch_18_18_ok accepted_947 (by simp [batch_18_18_values])
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

#print axioms batch_18_00_ok
#print axioms leaf_901_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
