import PeaceableQueens.UpperBound.Generated.Even.CoreScaled59Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_59_00_values : List Bool := [accepted_2951]
theorem batch_59_00_ok : batch_59_00_values.all id = true := by decide

def batch_59_01_values : List Bool := [accepted_2953]
theorem batch_59_01_ok : batch_59_01_values.all id = true := by decide

def batch_59_02_values : List Bool := [accepted_2963]
theorem batch_59_02_ok : batch_59_02_values.all id = true := by decide

def batch_59_03_values : List Bool := [accepted_2969]
theorem batch_59_03_ok : batch_59_03_values.all id = true := by decide

def batch_59_04_values : List Bool := [accepted_2971]
theorem batch_59_04_ok : batch_59_04_values.all id = true := by decide

def batch_59_05_values : List Bool := [accepted_2974]
theorem batch_59_05_ok : batch_59_05_values.all id = true := by decide

def batch_59_06_values : List Bool := [accepted_2979]
theorem batch_59_06_ok : batch_59_06_values.all id = true := by decide

def batch_59_07_values : List Bool := [accepted_2986]
theorem batch_59_07_ok : batch_59_07_values.all id = true := by decide

def batch_59_08_values : List Bool := [accepted_2988]
theorem batch_59_08_ok : batch_59_08_values.all id = true := by decide

def batch_59_09_values : List Bool := [accepted_2990]
theorem batch_59_09_ok : batch_59_09_values.all id = true := by decide

def batch_59_10_values : List Bool := [accepted_2996]
theorem batch_59_10_ok : batch_59_10_values.all id = true := by decide

def batch_59_11_values : List Bool := [accepted_2998]
theorem batch_59_11_ok : batch_59_11_values.all id = true := by decide

theorem leaf_2951_ok : checkAt 527 1000 box_2951 cert_2951 = true := by
  have h := List.all_eq_true.mp batch_59_00_ok accepted_2951 (by simp [batch_59_00_values])
  exact h
theorem leaf_2951_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2951.profileLo box_2951.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2951_ok
theorem branch_box_2951_nonnegative : ∀ j, 0 ≤ branch_box_2951.lower j ∧ 0 ≤ branch_box_2951.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2951, Box.profileLo, Box.profileHi, box_2951]
theorem leaf_2951_BranchSafe : CertificateConsequences.BranchSafe branch_box_2951 := by
  left; refine ⟨branch_box_2951_nonnegative, ?_⟩
  intro z hz; exact leaf_2951_sound hz

theorem leaf_2953_ok : checkAt 527 1000 box_2953 cert_2953 = true := by
  have h := List.all_eq_true.mp batch_59_01_ok accepted_2953 (by simp [batch_59_01_values])
  exact h
theorem leaf_2953_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2953.profileLo box_2953.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2953_ok
theorem branch_box_2953_nonnegative : ∀ j, 0 ≤ branch_box_2953.lower j ∧ 0 ≤ branch_box_2953.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2953, Box.profileLo, Box.profileHi, box_2953]
theorem leaf_2953_BranchSafe : CertificateConsequences.BranchSafe branch_box_2953 := by
  left; refine ⟨branch_box_2953_nonnegative, ?_⟩
  intro z hz; exact leaf_2953_sound hz

theorem leaf_2963_ok : checkAt 527 1000 box_2963 cert_2963 = true := by
  have h := List.all_eq_true.mp batch_59_02_ok accepted_2963 (by simp [batch_59_02_values])
  exact h
theorem leaf_2963_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2963.profileLo box_2963.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2963_ok
theorem branch_box_2963_nonnegative : ∀ j, 0 ≤ branch_box_2963.lower j ∧ 0 ≤ branch_box_2963.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2963, Box.profileLo, Box.profileHi, box_2963]
theorem leaf_2963_BranchSafe : CertificateConsequences.BranchSafe branch_box_2963 := by
  left; refine ⟨branch_box_2963_nonnegative, ?_⟩
  intro z hz; exact leaf_2963_sound hz

theorem leaf_2969_ok : checkAt 527 1000 box_2969 cert_2969 = true := by
  have h := List.all_eq_true.mp batch_59_03_ok accepted_2969 (by simp [batch_59_03_values])
  exact h
theorem leaf_2969_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2969.profileLo box_2969.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2969_ok
theorem branch_box_2969_nonnegative : ∀ j, 0 ≤ branch_box_2969.lower j ∧ 0 ≤ branch_box_2969.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2969, Box.profileLo, Box.profileHi, box_2969]
theorem leaf_2969_BranchSafe : CertificateConsequences.BranchSafe branch_box_2969 := by
  left; refine ⟨branch_box_2969_nonnegative, ?_⟩
  intro z hz; exact leaf_2969_sound hz

theorem leaf_2971_ok : checkAt 527 1000 box_2971 cert_2971 = true := by
  have h := List.all_eq_true.mp batch_59_04_ok accepted_2971 (by simp [batch_59_04_values])
  exact h
theorem leaf_2971_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2971.profileLo box_2971.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2971_ok
theorem branch_box_2971_nonnegative : ∀ j, 0 ≤ branch_box_2971.lower j ∧ 0 ≤ branch_box_2971.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2971, Box.profileLo, Box.profileHi, box_2971]
theorem leaf_2971_BranchSafe : CertificateConsequences.BranchSafe branch_box_2971 := by
  left; refine ⟨branch_box_2971_nonnegative, ?_⟩
  intro z hz; exact leaf_2971_sound hz

theorem leaf_2974_ok : checkAt 527 1000 box_2974 cert_2974 = true := by
  have h := List.all_eq_true.mp batch_59_05_ok accepted_2974 (by simp [batch_59_05_values])
  exact h
theorem leaf_2974_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2974.profileLo box_2974.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2974_ok
theorem branch_box_2974_nonnegative : ∀ j, 0 ≤ branch_box_2974.lower j ∧ 0 ≤ branch_box_2974.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2974, Box.profileLo, Box.profileHi, box_2974]
theorem leaf_2974_BranchSafe : CertificateConsequences.BranchSafe branch_box_2974 := by
  left; refine ⟨branch_box_2974_nonnegative, ?_⟩
  intro z hz; exact leaf_2974_sound hz

theorem leaf_2979_ok : checkAt 527 1000 box_2979 cert_2979 = true := by
  have h := List.all_eq_true.mp batch_59_06_ok accepted_2979 (by simp [batch_59_06_values])
  exact h
theorem leaf_2979_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2979.profileLo box_2979.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2979_ok
theorem branch_box_2979_nonnegative : ∀ j, 0 ≤ branch_box_2979.lower j ∧ 0 ≤ branch_box_2979.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2979, Box.profileLo, Box.profileHi, box_2979]
theorem leaf_2979_BranchSafe : CertificateConsequences.BranchSafe branch_box_2979 := by
  left; refine ⟨branch_box_2979_nonnegative, ?_⟩
  intro z hz; exact leaf_2979_sound hz

theorem leaf_2986_ok : checkAt 527 1000 box_2986 cert_2986 = true := by
  have h := List.all_eq_true.mp batch_59_07_ok accepted_2986 (by simp [batch_59_07_values])
  exact h
theorem leaf_2986_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2986.profileLo box_2986.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2986_ok
theorem branch_box_2986_nonnegative : ∀ j, 0 ≤ branch_box_2986.lower j ∧ 0 ≤ branch_box_2986.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2986, Box.profileLo, Box.profileHi, box_2986]
theorem leaf_2986_BranchSafe : CertificateConsequences.BranchSafe branch_box_2986 := by
  left; refine ⟨branch_box_2986_nonnegative, ?_⟩
  intro z hz; exact leaf_2986_sound hz

theorem leaf_2988_ok : checkAt 527 1000 box_2988 cert_2988 = true := by
  have h := List.all_eq_true.mp batch_59_08_ok accepted_2988 (by simp [batch_59_08_values])
  exact h
theorem leaf_2988_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2988.profileLo box_2988.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2988_ok
theorem branch_box_2988_nonnegative : ∀ j, 0 ≤ branch_box_2988.lower j ∧ 0 ≤ branch_box_2988.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2988, Box.profileLo, Box.profileHi, box_2988]
theorem leaf_2988_BranchSafe : CertificateConsequences.BranchSafe branch_box_2988 := by
  left; refine ⟨branch_box_2988_nonnegative, ?_⟩
  intro z hz; exact leaf_2988_sound hz

theorem leaf_2990_ok : checkAt 527 1000 box_2990 cert_2990 = true := by
  have h := List.all_eq_true.mp batch_59_09_ok accepted_2990 (by simp [batch_59_09_values])
  exact h
theorem leaf_2990_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2990.profileLo box_2990.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2990_ok
theorem branch_box_2990_nonnegative : ∀ j, 0 ≤ branch_box_2990.lower j ∧ 0 ≤ branch_box_2990.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2990, Box.profileLo, Box.profileHi, box_2990]
theorem leaf_2990_BranchSafe : CertificateConsequences.BranchSafe branch_box_2990 := by
  left; refine ⟨branch_box_2990_nonnegative, ?_⟩
  intro z hz; exact leaf_2990_sound hz

theorem leaf_2996_ok : checkAt 527 1000 box_2996 cert_2996 = true := by
  have h := List.all_eq_true.mp batch_59_10_ok accepted_2996 (by simp [batch_59_10_values])
  exact h
theorem leaf_2996_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2996.profileLo box_2996.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2996_ok
theorem branch_box_2996_nonnegative : ∀ j, 0 ≤ branch_box_2996.lower j ∧ 0 ≤ branch_box_2996.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2996, Box.profileLo, Box.profileHi, box_2996]
theorem leaf_2996_BranchSafe : CertificateConsequences.BranchSafe branch_box_2996 := by
  left; refine ⟨branch_box_2996_nonnegative, ?_⟩
  intro z hz; exact leaf_2996_sound hz

theorem leaf_2998_ok : checkAt 527 1000 box_2998 cert_2998 = true := by
  have h := List.all_eq_true.mp batch_59_11_ok accepted_2998 (by simp [batch_59_11_values])
  exact h
theorem leaf_2998_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2998.profileLo box_2998.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2998_ok
theorem branch_box_2998_nonnegative : ∀ j, 0 ≤ branch_box_2998.lower j ∧ 0 ≤ branch_box_2998.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2998, Box.profileLo, Box.profileHi, box_2998]
theorem leaf_2998_BranchSafe : CertificateConsequences.BranchSafe branch_box_2998 := by
  left; refine ⟨branch_box_2998_nonnegative, ?_⟩
  intro z hz; exact leaf_2998_sound hz

#print axioms batch_59_00_ok
#print axioms leaf_2951_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
