import PeaceableQueens.UpperBound.Generated.Even.CoreScaled61Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_61_00_values : List Bool := [accepted_3051]
theorem batch_61_00_ok : batch_61_00_values.all id = true := by decide

def batch_61_01_values : List Bool := [accepted_3060]
theorem batch_61_01_ok : batch_61_01_values.all id = true := by decide

def batch_61_02_values : List Bool := [accepted_3063]
theorem batch_61_02_ok : batch_61_02_values.all id = true := by decide

def batch_61_03_values : List Bool := [accepted_3068]
theorem batch_61_03_ok : batch_61_03_values.all id = true := by decide

def batch_61_04_values : List Bool := [accepted_3069]
theorem batch_61_04_ok : batch_61_04_values.all id = true := by decide

def batch_61_05_values : List Bool := [accepted_3072]
theorem batch_61_05_ok : batch_61_05_values.all id = true := by decide

def batch_61_06_values : List Bool := [accepted_3073]
theorem batch_61_06_ok : batch_61_06_values.all id = true := by decide

def batch_61_07_values : List Bool := [accepted_3082]
theorem batch_61_07_ok : batch_61_07_values.all id = true := by decide

def batch_61_08_values : List Bool := [accepted_3084]
theorem batch_61_08_ok : batch_61_08_values.all id = true := by decide

def batch_61_09_values : List Bool := [accepted_3086]
theorem batch_61_09_ok : batch_61_09_values.all id = true := by decide

def batch_61_10_values : List Bool := [accepted_3088]
theorem batch_61_10_ok : batch_61_10_values.all id = true := by decide

def batch_61_11_values : List Bool := [accepted_3094]
theorem batch_61_11_ok : batch_61_11_values.all id = true := by decide

def batch_61_12_values : List Bool := [accepted_3096]
theorem batch_61_12_ok : batch_61_12_values.all id = true := by decide

def batch_61_13_values : List Bool := [accepted_3098]
theorem batch_61_13_ok : batch_61_13_values.all id = true := by decide

theorem leaf_3051_ok : checkAt 527 1000 box_3051 cert_3051 = true := by
  have h := List.all_eq_true.mp batch_61_00_ok accepted_3051 (by simp [batch_61_00_values])
  exact h
theorem leaf_3051_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3051.profileLo box_3051.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3051_ok
theorem branch_box_3051_nonnegative : ∀ j, 0 ≤ branch_box_3051.lower j ∧ 0 ≤ branch_box_3051.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3051, Box.profileLo, Box.profileHi, box_3051]
theorem leaf_3051_BranchSafe : CertificateConsequences.BranchSafe branch_box_3051 := by
  left; refine ⟨branch_box_3051_nonnegative, ?_⟩
  intro z hz; exact leaf_3051_sound hz

theorem leaf_3060_ok : checkAt 527 1000 box_3060 cert_3060 = true := by
  have h := List.all_eq_true.mp batch_61_01_ok accepted_3060 (by simp [batch_61_01_values])
  exact h
theorem leaf_3060_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3060.profileLo box_3060.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3060_ok
theorem branch_box_3060_nonnegative : ∀ j, 0 ≤ branch_box_3060.lower j ∧ 0 ≤ branch_box_3060.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3060, Box.profileLo, Box.profileHi, box_3060]
theorem leaf_3060_BranchSafe : CertificateConsequences.BranchSafe branch_box_3060 := by
  left; refine ⟨branch_box_3060_nonnegative, ?_⟩
  intro z hz; exact leaf_3060_sound hz

theorem leaf_3063_ok : checkAt 527 1000 box_3063 cert_3063 = true := by
  have h := List.all_eq_true.mp batch_61_02_ok accepted_3063 (by simp [batch_61_02_values])
  exact h
theorem leaf_3063_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3063.profileLo box_3063.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3063_ok
theorem branch_box_3063_nonnegative : ∀ j, 0 ≤ branch_box_3063.lower j ∧ 0 ≤ branch_box_3063.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3063, Box.profileLo, Box.profileHi, box_3063]
theorem leaf_3063_BranchSafe : CertificateConsequences.BranchSafe branch_box_3063 := by
  left; refine ⟨branch_box_3063_nonnegative, ?_⟩
  intro z hz; exact leaf_3063_sound hz

theorem leaf_3068_ok : checkAt 527 1000 box_3068 cert_3068 = true := by
  have h := List.all_eq_true.mp batch_61_03_ok accepted_3068 (by simp [batch_61_03_values])
  exact h
theorem leaf_3068_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3068.profileLo box_3068.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3068_ok
theorem branch_box_3068_nonnegative : ∀ j, 0 ≤ branch_box_3068.lower j ∧ 0 ≤ branch_box_3068.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3068, Box.profileLo, Box.profileHi, box_3068]
theorem leaf_3068_BranchSafe : CertificateConsequences.BranchSafe branch_box_3068 := by
  left; refine ⟨branch_box_3068_nonnegative, ?_⟩
  intro z hz; exact leaf_3068_sound hz

theorem leaf_3069_ok : checkAt 527 1000 box_3069 cert_3069 = true := by
  have h := List.all_eq_true.mp batch_61_04_ok accepted_3069 (by simp [batch_61_04_values])
  exact h
theorem leaf_3069_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3069.profileLo box_3069.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3069_ok
theorem branch_box_3069_nonnegative : ∀ j, 0 ≤ branch_box_3069.lower j ∧ 0 ≤ branch_box_3069.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3069, Box.profileLo, Box.profileHi, box_3069]
theorem leaf_3069_BranchSafe : CertificateConsequences.BranchSafe branch_box_3069 := by
  left; refine ⟨branch_box_3069_nonnegative, ?_⟩
  intro z hz; exact leaf_3069_sound hz

theorem leaf_3072_ok : checkAt 527 1000 box_3072 cert_3072 = true := by
  have h := List.all_eq_true.mp batch_61_05_ok accepted_3072 (by simp [batch_61_05_values])
  exact h
theorem leaf_3072_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3072.profileLo box_3072.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3072_ok
theorem branch_box_3072_nonnegative : ∀ j, 0 ≤ branch_box_3072.lower j ∧ 0 ≤ branch_box_3072.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3072, Box.profileLo, Box.profileHi, box_3072]
theorem leaf_3072_BranchSafe : CertificateConsequences.BranchSafe branch_box_3072 := by
  left; refine ⟨branch_box_3072_nonnegative, ?_⟩
  intro z hz; exact leaf_3072_sound hz

theorem leaf_3073_ok : checkAt 527 1000 box_3073 cert_3073 = true := by
  have h := List.all_eq_true.mp batch_61_06_ok accepted_3073 (by simp [batch_61_06_values])
  exact h
theorem leaf_3073_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3073.profileLo box_3073.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3073_ok
theorem branch_box_3073_nonnegative : ∀ j, 0 ≤ branch_box_3073.lower j ∧ 0 ≤ branch_box_3073.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3073, Box.profileLo, Box.profileHi, box_3073]
theorem leaf_3073_BranchSafe : CertificateConsequences.BranchSafe branch_box_3073 := by
  left; refine ⟨branch_box_3073_nonnegative, ?_⟩
  intro z hz; exact leaf_3073_sound hz

theorem leaf_3082_ok : checkAt 527 1000 box_3082 cert_3082 = true := by
  have h := List.all_eq_true.mp batch_61_07_ok accepted_3082 (by simp [batch_61_07_values])
  exact h
theorem leaf_3082_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3082.profileLo box_3082.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3082_ok
theorem branch_box_3082_nonnegative : ∀ j, 0 ≤ branch_box_3082.lower j ∧ 0 ≤ branch_box_3082.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3082, Box.profileLo, Box.profileHi, box_3082]
theorem leaf_3082_BranchSafe : CertificateConsequences.BranchSafe branch_box_3082 := by
  left; refine ⟨branch_box_3082_nonnegative, ?_⟩
  intro z hz; exact leaf_3082_sound hz

theorem leaf_3084_ok : checkAt 527 1000 box_3084 cert_3084 = true := by
  have h := List.all_eq_true.mp batch_61_08_ok accepted_3084 (by simp [batch_61_08_values])
  exact h
theorem leaf_3084_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3084.profileLo box_3084.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3084_ok
theorem branch_box_3084_nonnegative : ∀ j, 0 ≤ branch_box_3084.lower j ∧ 0 ≤ branch_box_3084.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3084, Box.profileLo, Box.profileHi, box_3084]
theorem leaf_3084_BranchSafe : CertificateConsequences.BranchSafe branch_box_3084 := by
  left; refine ⟨branch_box_3084_nonnegative, ?_⟩
  intro z hz; exact leaf_3084_sound hz

theorem leaf_3086_ok : checkAt 527 1000 box_3086 cert_3086 = true := by
  have h := List.all_eq_true.mp batch_61_09_ok accepted_3086 (by simp [batch_61_09_values])
  exact h
theorem leaf_3086_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3086.profileLo box_3086.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3086_ok
theorem branch_box_3086_nonnegative : ∀ j, 0 ≤ branch_box_3086.lower j ∧ 0 ≤ branch_box_3086.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3086, Box.profileLo, Box.profileHi, box_3086]
theorem leaf_3086_BranchSafe : CertificateConsequences.BranchSafe branch_box_3086 := by
  left; refine ⟨branch_box_3086_nonnegative, ?_⟩
  intro z hz; exact leaf_3086_sound hz

theorem leaf_3088_ok : checkAt 527 1000 box_3088 cert_3088 = true := by
  have h := List.all_eq_true.mp batch_61_10_ok accepted_3088 (by simp [batch_61_10_values])
  exact h
theorem leaf_3088_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3088.profileLo box_3088.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3088_ok
theorem branch_box_3088_nonnegative : ∀ j, 0 ≤ branch_box_3088.lower j ∧ 0 ≤ branch_box_3088.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3088, Box.profileLo, Box.profileHi, box_3088]
theorem leaf_3088_BranchSafe : CertificateConsequences.BranchSafe branch_box_3088 := by
  left; refine ⟨branch_box_3088_nonnegative, ?_⟩
  intro z hz; exact leaf_3088_sound hz

theorem leaf_3094_ok : checkAt 527 1000 box_3094 cert_3094 = true := by
  have h := List.all_eq_true.mp batch_61_11_ok accepted_3094 (by simp [batch_61_11_values])
  exact h
theorem leaf_3094_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3094.profileLo box_3094.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3094_ok
theorem branch_box_3094_nonnegative : ∀ j, 0 ≤ branch_box_3094.lower j ∧ 0 ≤ branch_box_3094.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3094, Box.profileLo, Box.profileHi, box_3094]
theorem leaf_3094_BranchSafe : CertificateConsequences.BranchSafe branch_box_3094 := by
  left; refine ⟨branch_box_3094_nonnegative, ?_⟩
  intro z hz; exact leaf_3094_sound hz

theorem leaf_3096_ok : checkAt 527 1000 box_3096 cert_3096 = true := by
  have h := List.all_eq_true.mp batch_61_12_ok accepted_3096 (by simp [batch_61_12_values])
  exact h
theorem leaf_3096_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3096.profileLo box_3096.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3096_ok
theorem branch_box_3096_nonnegative : ∀ j, 0 ≤ branch_box_3096.lower j ∧ 0 ≤ branch_box_3096.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3096, Box.profileLo, Box.profileHi, box_3096]
theorem leaf_3096_BranchSafe : CertificateConsequences.BranchSafe branch_box_3096 := by
  left; refine ⟨branch_box_3096_nonnegative, ?_⟩
  intro z hz; exact leaf_3096_sound hz

theorem leaf_3098_ok : checkAt 527 1000 box_3098 cert_3098 = true := by
  have h := List.all_eq_true.mp batch_61_13_ok accepted_3098 (by simp [batch_61_13_values])
  exact h
theorem leaf_3098_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3098.profileLo box_3098.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3098_ok
theorem branch_box_3098_nonnegative : ∀ j, 0 ≤ branch_box_3098.lower j ∧ 0 ≤ branch_box_3098.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3098, Box.profileLo, Box.profileHi, box_3098]
theorem leaf_3098_BranchSafe : CertificateConsequences.BranchSafe branch_box_3098 := by
  left; refine ⟨branch_box_3098_nonnegative, ?_⟩
  intro z hz; exact leaf_3098_sound hz

#print axioms batch_61_00_ok
#print axioms leaf_3051_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
