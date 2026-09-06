import PeaceableQueens.UpperBound.Generated.Even.C527Scaled138Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_138_00_values : List Bool := [accepted_6901]
theorem batch_138_00_ok : batch_138_00_values.all id = true := by decide

def batch_138_01_values : List Bool := [accepted_6903]
theorem batch_138_01_ok : batch_138_01_values.all id = true := by decide

def batch_138_02_values : List Bool := [accepted_6905]
theorem batch_138_02_ok : batch_138_02_values.all id = true := by decide

def batch_138_03_values : List Bool := [accepted_6912]
theorem batch_138_03_ok : batch_138_03_values.all id = true := by decide

def batch_138_04_values : List Bool := [accepted_6921]
theorem batch_138_04_ok : batch_138_04_values.all id = true := by decide

def batch_138_05_values : List Bool := [accepted_6922]
theorem batch_138_05_ok : batch_138_05_values.all id = true := by decide

def batch_138_06_values : List Bool := [accepted_6923]
theorem batch_138_06_ok : batch_138_06_values.all id = true := by decide

def batch_138_07_values : List Bool := [accepted_6924]
theorem batch_138_07_ok : batch_138_07_values.all id = true := by decide

def batch_138_08_values : List Bool := [accepted_6927]
theorem batch_138_08_ok : batch_138_08_values.all id = true := by decide

def batch_138_09_values : List Bool := [accepted_6928]
theorem batch_138_09_ok : batch_138_09_values.all id = true := by decide

theorem leaf_6901_ok : checkAt 527 1000 box_6901 cert_6901 = true := by
  have h := List.all_eq_true.mp batch_138_00_ok accepted_6901 (by simp [batch_138_00_values])
  exact h
theorem leaf_6901_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6901.profileLo box_6901.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6901_ok
theorem branch_box_6901_nonnegative : ∀ j, 0 ≤ branch_box_6901.lower j ∧ 0 ≤ branch_box_6901.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6901, Box.profileLo, Box.profileHi, box_6901]
theorem leaf_6901_BranchSafe : CertificateConsequences.BranchSafe branch_box_6901 := by
  left; refine ⟨branch_box_6901_nonnegative, ?_⟩
  intro z hz; exact leaf_6901_sound hz

theorem leaf_6903_ok : checkAt 527 1000 box_6903 cert_6903 = true := by
  have h := List.all_eq_true.mp batch_138_01_ok accepted_6903 (by simp [batch_138_01_values])
  exact h
theorem leaf_6903_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6903.profileLo box_6903.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6903_ok
theorem branch_box_6903_nonnegative : ∀ j, 0 ≤ branch_box_6903.lower j ∧ 0 ≤ branch_box_6903.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6903, Box.profileLo, Box.profileHi, box_6903]
theorem leaf_6903_BranchSafe : CertificateConsequences.BranchSafe branch_box_6903 := by
  left; refine ⟨branch_box_6903_nonnegative, ?_⟩
  intro z hz; exact leaf_6903_sound hz

theorem leaf_6905_ok : checkAt 527 1000 box_6905 cert_6905 = true := by
  have h := List.all_eq_true.mp batch_138_02_ok accepted_6905 (by simp [batch_138_02_values])
  exact h
theorem leaf_6905_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6905.profileLo box_6905.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6905_ok
theorem branch_box_6905_nonnegative : ∀ j, 0 ≤ branch_box_6905.lower j ∧ 0 ≤ branch_box_6905.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6905, Box.profileLo, Box.profileHi, box_6905]
theorem leaf_6905_BranchSafe : CertificateConsequences.BranchSafe branch_box_6905 := by
  left; refine ⟨branch_box_6905_nonnegative, ?_⟩
  intro z hz; exact leaf_6905_sound hz

theorem leaf_6912_ok : checkAt 527 1000 box_6912 cert_6912 = true := by
  have h := List.all_eq_true.mp batch_138_03_ok accepted_6912 (by simp [batch_138_03_values])
  exact h
theorem leaf_6912_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6912.profileLo box_6912.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6912_ok
theorem branch_box_6912_nonnegative : ∀ j, 0 ≤ branch_box_6912.lower j ∧ 0 ≤ branch_box_6912.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6912, Box.profileLo, Box.profileHi, box_6912]
theorem leaf_6912_BranchSafe : CertificateConsequences.BranchSafe branch_box_6912 := by
  left; refine ⟨branch_box_6912_nonnegative, ?_⟩
  intro z hz; exact leaf_6912_sound hz

theorem leaf_6921_ok : checkAt 527 1000 box_6921 cert_6921 = true := by
  have h := List.all_eq_true.mp batch_138_04_ok accepted_6921 (by simp [batch_138_04_values])
  exact h
theorem leaf_6921_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6921.profileLo box_6921.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6921_ok
theorem branch_box_6921_nonnegative : ∀ j, 0 ≤ branch_box_6921.lower j ∧ 0 ≤ branch_box_6921.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6921, Box.profileLo, Box.profileHi, box_6921]
theorem leaf_6921_BranchSafe : CertificateConsequences.BranchSafe branch_box_6921 := by
  left; refine ⟨branch_box_6921_nonnegative, ?_⟩
  intro z hz; exact leaf_6921_sound hz

theorem leaf_6922_ok : checkAt 527 1000 box_6922 cert_6922 = true := by
  have h := List.all_eq_true.mp batch_138_05_ok accepted_6922 (by simp [batch_138_05_values])
  exact h
theorem leaf_6922_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6922.profileLo box_6922.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6922_ok
theorem branch_box_6922_nonnegative : ∀ j, 0 ≤ branch_box_6922.lower j ∧ 0 ≤ branch_box_6922.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6922, Box.profileLo, Box.profileHi, box_6922]
theorem leaf_6922_BranchSafe : CertificateConsequences.BranchSafe branch_box_6922 := by
  left; refine ⟨branch_box_6922_nonnegative, ?_⟩
  intro z hz; exact leaf_6922_sound hz

theorem leaf_6923_ok : checkAt 527 1000 box_6923 cert_6923 = true := by
  have h := List.all_eq_true.mp batch_138_06_ok accepted_6923 (by simp [batch_138_06_values])
  exact h
theorem leaf_6923_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6923.profileLo box_6923.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6923_ok
theorem branch_box_6923_nonnegative : ∀ j, 0 ≤ branch_box_6923.lower j ∧ 0 ≤ branch_box_6923.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6923, Box.profileLo, Box.profileHi, box_6923]
theorem leaf_6923_BranchSafe : CertificateConsequences.BranchSafe branch_box_6923 := by
  left; refine ⟨branch_box_6923_nonnegative, ?_⟩
  intro z hz; exact leaf_6923_sound hz

theorem leaf_6924_ok : checkAt 527 1000 box_6924 cert_6924 = true := by
  have h := List.all_eq_true.mp batch_138_07_ok accepted_6924 (by simp [batch_138_07_values])
  exact h
theorem leaf_6924_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6924.profileLo box_6924.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6924_ok
theorem branch_box_6924_nonnegative : ∀ j, 0 ≤ branch_box_6924.lower j ∧ 0 ≤ branch_box_6924.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6924, Box.profileLo, Box.profileHi, box_6924]
theorem leaf_6924_BranchSafe : CertificateConsequences.BranchSafe branch_box_6924 := by
  left; refine ⟨branch_box_6924_nonnegative, ?_⟩
  intro z hz; exact leaf_6924_sound hz

theorem leaf_6927_ok : checkAt 527 1000 box_6927 cert_6927 = true := by
  have h := List.all_eq_true.mp batch_138_08_ok accepted_6927 (by simp [batch_138_08_values])
  exact h
theorem leaf_6927_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6927.profileLo box_6927.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6927_ok
theorem branch_box_6927_nonnegative : ∀ j, 0 ≤ branch_box_6927.lower j ∧ 0 ≤ branch_box_6927.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6927, Box.profileLo, Box.profileHi, box_6927]
theorem leaf_6927_BranchSafe : CertificateConsequences.BranchSafe branch_box_6927 := by
  left; refine ⟨branch_box_6927_nonnegative, ?_⟩
  intro z hz; exact leaf_6927_sound hz

theorem leaf_6928_ok : checkAt 527 1000 box_6928 cert_6928 = true := by
  have h := List.all_eq_true.mp batch_138_09_ok accepted_6928 (by simp [batch_138_09_values])
  exact h
theorem leaf_6928_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6928.profileLo box_6928.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6928_ok
theorem branch_box_6928_nonnegative : ∀ j, 0 ≤ branch_box_6928.lower j ∧ 0 ≤ branch_box_6928.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6928, Box.profileLo, Box.profileHi, box_6928]
theorem leaf_6928_BranchSafe : CertificateConsequences.BranchSafe branch_box_6928 := by
  left; refine ⟨branch_box_6928_nonnegative, ?_⟩
  intro z hz; exact leaf_6928_sound hz

#print axioms batch_138_00_ok
#print axioms leaf_6901_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
