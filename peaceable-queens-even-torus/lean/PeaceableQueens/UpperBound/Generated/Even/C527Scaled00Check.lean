import PeaceableQueens.UpperBound.Generated.Even.C527Scaled00Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_00_00_values : List Bool := [accepted_29]
theorem batch_00_00_ok : batch_00_00_values.all id = true := by decide

def batch_00_01_values : List Bool := [accepted_30]
theorem batch_00_01_ok : batch_00_01_values.all id = true := by decide

def batch_00_02_values : List Bool := [accepted_31]
theorem batch_00_02_ok : batch_00_02_values.all id = true := by decide

def batch_00_03_values : List Bool := [accepted_32]
theorem batch_00_03_ok : batch_00_03_values.all id = true := by decide

def batch_00_04_values : List Bool := [accepted_33]
theorem batch_00_04_ok : batch_00_04_values.all id = true := by decide

def batch_00_05_values : List Bool := [accepted_34]
theorem batch_00_05_ok : batch_00_05_values.all id = true := by decide

def batch_00_06_values : List Bool := [accepted_36]
theorem batch_00_06_ok : batch_00_06_values.all id = true := by decide

def batch_00_07_values : List Bool := [accepted_37]
theorem batch_00_07_ok : batch_00_07_values.all id = true := by decide

def batch_00_08_values : List Bool := [accepted_38]
theorem batch_00_08_ok : batch_00_08_values.all id = true := by decide

def batch_00_09_values : List Bool := [accepted_39]
theorem batch_00_09_ok : batch_00_09_values.all id = true := by decide

def batch_00_10_values : List Bool := [accepted_41]
theorem batch_00_10_ok : batch_00_10_values.all id = true := by decide

def batch_00_11_values : List Bool := [accepted_42]
theorem batch_00_11_ok : batch_00_11_values.all id = true := by decide

def batch_00_12_values : List Bool := [accepted_45]
theorem batch_00_12_ok : batch_00_12_values.all id = true := by decide

def batch_00_13_values : List Bool := [accepted_46]
theorem batch_00_13_ok : batch_00_13_values.all id = true := by decide

def batch_00_14_values : List Bool := [accepted_49]
theorem batch_00_14_ok : batch_00_14_values.all id = true := by decide

theorem leaf_29_ok : checkAt 527 1000 box_29 cert_29 = true := by
  have h := List.all_eq_true.mp batch_00_00_ok accepted_29 (by simp [batch_00_00_values])
  exact h
theorem leaf_29_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_29.profileLo box_29.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_29_ok
theorem branch_box_29_nonnegative : ∀ j, 0 ≤ branch_box_29.lower j ∧ 0 ≤ branch_box_29.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_29, Box.profileLo, Box.profileHi, box_29]
theorem leaf_29_BranchSafe : CertificateConsequences.BranchSafe branch_box_29 := by
  left; refine ⟨branch_box_29_nonnegative, ?_⟩
  intro z hz; exact leaf_29_sound hz

theorem leaf_30_ok : checkAt 527 1000 box_30 cert_30 = true := by
  have h := List.all_eq_true.mp batch_00_01_ok accepted_30 (by simp [batch_00_01_values])
  exact h
theorem leaf_30_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_30.profileLo box_30.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_30_ok
theorem branch_box_30_nonnegative : ∀ j, 0 ≤ branch_box_30.lower j ∧ 0 ≤ branch_box_30.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_30, Box.profileLo, Box.profileHi, box_30]
theorem leaf_30_BranchSafe : CertificateConsequences.BranchSafe branch_box_30 := by
  left; refine ⟨branch_box_30_nonnegative, ?_⟩
  intro z hz; exact leaf_30_sound hz

theorem leaf_31_ok : checkAt 527 1000 box_31 cert_31 = true := by
  have h := List.all_eq_true.mp batch_00_02_ok accepted_31 (by simp [batch_00_02_values])
  exact h
theorem leaf_31_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_31.profileLo box_31.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_31_ok
theorem branch_box_31_nonnegative : ∀ j, 0 ≤ branch_box_31.lower j ∧ 0 ≤ branch_box_31.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_31, Box.profileLo, Box.profileHi, box_31]
theorem leaf_31_BranchSafe : CertificateConsequences.BranchSafe branch_box_31 := by
  left; refine ⟨branch_box_31_nonnegative, ?_⟩
  intro z hz; exact leaf_31_sound hz

theorem leaf_32_ok : checkAt 527 1000 box_32 cert_32 = true := by
  have h := List.all_eq_true.mp batch_00_03_ok accepted_32 (by simp [batch_00_03_values])
  exact h
theorem leaf_32_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_32.profileLo box_32.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_32_ok
theorem branch_box_32_nonnegative : ∀ j, 0 ≤ branch_box_32.lower j ∧ 0 ≤ branch_box_32.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_32, Box.profileLo, Box.profileHi, box_32]
theorem leaf_32_BranchSafe : CertificateConsequences.BranchSafe branch_box_32 := by
  left; refine ⟨branch_box_32_nonnegative, ?_⟩
  intro z hz; exact leaf_32_sound hz

theorem leaf_33_ok : checkAt 527 1000 box_33 cert_33 = true := by
  have h := List.all_eq_true.mp batch_00_04_ok accepted_33 (by simp [batch_00_04_values])
  exact h
theorem leaf_33_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_33.profileLo box_33.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_33_ok
theorem branch_box_33_nonnegative : ∀ j, 0 ≤ branch_box_33.lower j ∧ 0 ≤ branch_box_33.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_33, Box.profileLo, Box.profileHi, box_33]
theorem leaf_33_BranchSafe : CertificateConsequences.BranchSafe branch_box_33 := by
  left; refine ⟨branch_box_33_nonnegative, ?_⟩
  intro z hz; exact leaf_33_sound hz

theorem leaf_34_ok : checkAt 527 1000 box_34 cert_34 = true := by
  have h := List.all_eq_true.mp batch_00_05_ok accepted_34 (by simp [batch_00_05_values])
  exact h
theorem leaf_34_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_34.profileLo box_34.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_34_ok
theorem branch_box_34_nonnegative : ∀ j, 0 ≤ branch_box_34.lower j ∧ 0 ≤ branch_box_34.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_34, Box.profileLo, Box.profileHi, box_34]
theorem leaf_34_BranchSafe : CertificateConsequences.BranchSafe branch_box_34 := by
  left; refine ⟨branch_box_34_nonnegative, ?_⟩
  intro z hz; exact leaf_34_sound hz

theorem leaf_36_ok : checkAt 527 1000 box_36 cert_36 = true := by
  have h := List.all_eq_true.mp batch_00_06_ok accepted_36 (by simp [batch_00_06_values])
  exact h
theorem leaf_36_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_36.profileLo box_36.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_36_ok
theorem branch_box_36_nonnegative : ∀ j, 0 ≤ branch_box_36.lower j ∧ 0 ≤ branch_box_36.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_36, Box.profileLo, Box.profileHi, box_36]
theorem leaf_36_BranchSafe : CertificateConsequences.BranchSafe branch_box_36 := by
  left; refine ⟨branch_box_36_nonnegative, ?_⟩
  intro z hz; exact leaf_36_sound hz

theorem leaf_37_ok : checkAt 527 1000 box_37 cert_37 = true := by
  have h := List.all_eq_true.mp batch_00_07_ok accepted_37 (by simp [batch_00_07_values])
  exact h
theorem leaf_37_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_37.profileLo box_37.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_37_ok
theorem branch_box_37_nonnegative : ∀ j, 0 ≤ branch_box_37.lower j ∧ 0 ≤ branch_box_37.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_37, Box.profileLo, Box.profileHi, box_37]
theorem leaf_37_BranchSafe : CertificateConsequences.BranchSafe branch_box_37 := by
  left; refine ⟨branch_box_37_nonnegative, ?_⟩
  intro z hz; exact leaf_37_sound hz

theorem leaf_38_ok : checkAt 527 1000 box_38 cert_38 = true := by
  have h := List.all_eq_true.mp batch_00_08_ok accepted_38 (by simp [batch_00_08_values])
  exact h
theorem leaf_38_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_38.profileLo box_38.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_38_ok
theorem branch_box_38_nonnegative : ∀ j, 0 ≤ branch_box_38.lower j ∧ 0 ≤ branch_box_38.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_38, Box.profileLo, Box.profileHi, box_38]
theorem leaf_38_BranchSafe : CertificateConsequences.BranchSafe branch_box_38 := by
  left; refine ⟨branch_box_38_nonnegative, ?_⟩
  intro z hz; exact leaf_38_sound hz

theorem leaf_39_ok : checkAt 527 1000 box_39 cert_39 = true := by
  have h := List.all_eq_true.mp batch_00_09_ok accepted_39 (by simp [batch_00_09_values])
  exact h
theorem leaf_39_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_39.profileLo box_39.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_39_ok
theorem branch_box_39_nonnegative : ∀ j, 0 ≤ branch_box_39.lower j ∧ 0 ≤ branch_box_39.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_39, Box.profileLo, Box.profileHi, box_39]
theorem leaf_39_BranchSafe : CertificateConsequences.BranchSafe branch_box_39 := by
  left; refine ⟨branch_box_39_nonnegative, ?_⟩
  intro z hz; exact leaf_39_sound hz

theorem leaf_41_ok : checkAt 527 1000 box_41 cert_41 = true := by
  have h := List.all_eq_true.mp batch_00_10_ok accepted_41 (by simp [batch_00_10_values])
  exact h
theorem leaf_41_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_41.profileLo box_41.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_41_ok
theorem branch_box_41_nonnegative : ∀ j, 0 ≤ branch_box_41.lower j ∧ 0 ≤ branch_box_41.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_41, Box.profileLo, Box.profileHi, box_41]
theorem leaf_41_BranchSafe : CertificateConsequences.BranchSafe branch_box_41 := by
  left; refine ⟨branch_box_41_nonnegative, ?_⟩
  intro z hz; exact leaf_41_sound hz

theorem leaf_42_ok : checkAt 527 1000 box_42 cert_42 = true := by
  have h := List.all_eq_true.mp batch_00_11_ok accepted_42 (by simp [batch_00_11_values])
  exact h
theorem leaf_42_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_42.profileLo box_42.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_42_ok
theorem branch_box_42_nonnegative : ∀ j, 0 ≤ branch_box_42.lower j ∧ 0 ≤ branch_box_42.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_42, Box.profileLo, Box.profileHi, box_42]
theorem leaf_42_BranchSafe : CertificateConsequences.BranchSafe branch_box_42 := by
  left; refine ⟨branch_box_42_nonnegative, ?_⟩
  intro z hz; exact leaf_42_sound hz

theorem leaf_45_ok : checkAt 527 1000 box_45 cert_45 = true := by
  have h := List.all_eq_true.mp batch_00_12_ok accepted_45 (by simp [batch_00_12_values])
  exact h
theorem leaf_45_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_45.profileLo box_45.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_45_ok
theorem branch_box_45_nonnegative : ∀ j, 0 ≤ branch_box_45.lower j ∧ 0 ≤ branch_box_45.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_45, Box.profileLo, Box.profileHi, box_45]
theorem leaf_45_BranchSafe : CertificateConsequences.BranchSafe branch_box_45 := by
  left; refine ⟨branch_box_45_nonnegative, ?_⟩
  intro z hz; exact leaf_45_sound hz

theorem leaf_46_ok : checkAt 527 1000 box_46 cert_46 = true := by
  have h := List.all_eq_true.mp batch_00_13_ok accepted_46 (by simp [batch_00_13_values])
  exact h
theorem leaf_46_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_46.profileLo box_46.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_46_ok
theorem branch_box_46_nonnegative : ∀ j, 0 ≤ branch_box_46.lower j ∧ 0 ≤ branch_box_46.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_46, Box.profileLo, Box.profileHi, box_46]
theorem leaf_46_BranchSafe : CertificateConsequences.BranchSafe branch_box_46 := by
  left; refine ⟨branch_box_46_nonnegative, ?_⟩
  intro z hz; exact leaf_46_sound hz

theorem leaf_49_ok : checkAt 527 1000 box_49 cert_49 = true := by
  have h := List.all_eq_true.mp batch_00_14_ok accepted_49 (by simp [batch_00_14_values])
  exact h
theorem leaf_49_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_49.profileLo box_49.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_49_ok
theorem branch_box_49_nonnegative : ∀ j, 0 ≤ branch_box_49.lower j ∧ 0 ≤ branch_box_49.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_49, Box.profileLo, Box.profileHi, box_49]
theorem leaf_49_BranchSafe : CertificateConsequences.BranchSafe branch_box_49 := by
  left; refine ⟨branch_box_49_nonnegative, ?_⟩
  intro z hz; exact leaf_49_sound hz

#print axioms batch_00_00_ok
#print axioms leaf_29_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
