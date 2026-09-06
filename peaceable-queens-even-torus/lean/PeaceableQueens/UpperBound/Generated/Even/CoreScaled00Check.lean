import PeaceableQueens.UpperBound.Generated.Even.CoreScaled00Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_00_00_values : List Bool := [accepted_5]
theorem batch_00_00_ok : batch_00_00_values.all id = true := by decide

def batch_00_01_values : List Bool := [accepted_7]
theorem batch_00_01_ok : batch_00_01_values.all id = true := by decide

def batch_00_02_values : List Bool := [accepted_14]
theorem batch_00_02_ok : batch_00_02_values.all id = true := by decide

def batch_00_03_values : List Bool := [accepted_16]
theorem batch_00_03_ok : batch_00_03_values.all id = true := by decide

def batch_00_04_values : List Bool := [accepted_17]
theorem batch_00_04_ok : batch_00_04_values.all id = true := by decide

def batch_00_05_values : List Bool := [accepted_19]
theorem batch_00_05_ok : batch_00_05_values.all id = true := by decide

def batch_00_06_values : List Bool := [accepted_24]
theorem batch_00_06_ok : batch_00_06_values.all id = true := by decide

def batch_00_07_values : List Bool := [accepted_29]
theorem batch_00_07_ok : batch_00_07_values.all id = true := by decide

def batch_00_08_values : List Bool := [accepted_31]
theorem batch_00_08_ok : batch_00_08_values.all id = true := by decide

def batch_00_09_values : List Bool := [accepted_33]
theorem batch_00_09_ok : batch_00_09_values.all id = true := by decide

def batch_00_10_values : List Bool := [accepted_36]
theorem batch_00_10_ok : batch_00_10_values.all id = true := by decide

def batch_00_11_values : List Bool := [accepted_37]
theorem batch_00_11_ok : batch_00_11_values.all id = true := by decide

def batch_00_12_values : List Bool := [accepted_39]
theorem batch_00_12_ok : batch_00_12_values.all id = true := by decide

def batch_00_13_values : List Bool := [accepted_43]
theorem batch_00_13_ok : batch_00_13_values.all id = true := by decide

def batch_00_14_values : List Bool := [accepted_45]
theorem batch_00_14_ok : batch_00_14_values.all id = true := by decide

def batch_00_15_values : List Bool := [accepted_47]
theorem batch_00_15_ok : batch_00_15_values.all id = true := by decide

theorem leaf_5_ok : checkAt 527 1000 box_5 cert_5 = true := by
  have h := List.all_eq_true.mp batch_00_00_ok accepted_5 (by simp [batch_00_00_values])
  exact h
theorem leaf_5_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5.profileLo box_5.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5_ok
theorem branch_box_5_nonnegative : ∀ j, 0 ≤ branch_box_5.lower j ∧ 0 ≤ branch_box_5.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5, Box.profileLo, Box.profileHi, box_5]
theorem leaf_5_BranchSafe : CertificateConsequences.BranchSafe branch_box_5 := by
  left; refine ⟨branch_box_5_nonnegative, ?_⟩
  intro z hz; exact leaf_5_sound hz

theorem leaf_7_ok : checkAt 527 1000 box_7 cert_7 = true := by
  have h := List.all_eq_true.mp batch_00_01_ok accepted_7 (by simp [batch_00_01_values])
  exact h
theorem leaf_7_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_7.profileLo box_7.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_7_ok
theorem branch_box_7_nonnegative : ∀ j, 0 ≤ branch_box_7.lower j ∧ 0 ≤ branch_box_7.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_7, Box.profileLo, Box.profileHi, box_7]
theorem leaf_7_BranchSafe : CertificateConsequences.BranchSafe branch_box_7 := by
  left; refine ⟨branch_box_7_nonnegative, ?_⟩
  intro z hz; exact leaf_7_sound hz

theorem leaf_14_ok : checkAt 527 1000 box_14 cert_14 = true := by
  have h := List.all_eq_true.mp batch_00_02_ok accepted_14 (by simp [batch_00_02_values])
  exact h
theorem leaf_14_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_14.profileLo box_14.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_14_ok
theorem branch_box_14_nonnegative : ∀ j, 0 ≤ branch_box_14.lower j ∧ 0 ≤ branch_box_14.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_14, Box.profileLo, Box.profileHi, box_14]
theorem leaf_14_BranchSafe : CertificateConsequences.BranchSafe branch_box_14 := by
  left; refine ⟨branch_box_14_nonnegative, ?_⟩
  intro z hz; exact leaf_14_sound hz

theorem leaf_16_ok : checkAt 527 1000 box_16 cert_16 = true := by
  have h := List.all_eq_true.mp batch_00_03_ok accepted_16 (by simp [batch_00_03_values])
  exact h
theorem leaf_16_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_16.profileLo box_16.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_16_ok
theorem branch_box_16_nonnegative : ∀ j, 0 ≤ branch_box_16.lower j ∧ 0 ≤ branch_box_16.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_16, Box.profileLo, Box.profileHi, box_16]
theorem leaf_16_BranchSafe : CertificateConsequences.BranchSafe branch_box_16 := by
  left; refine ⟨branch_box_16_nonnegative, ?_⟩
  intro z hz; exact leaf_16_sound hz

theorem leaf_17_ok : checkAt 527 1000 box_17 cert_17 = true := by
  have h := List.all_eq_true.mp batch_00_04_ok accepted_17 (by simp [batch_00_04_values])
  exact h
theorem leaf_17_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_17.profileLo box_17.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_17_ok
theorem branch_box_17_nonnegative : ∀ j, 0 ≤ branch_box_17.lower j ∧ 0 ≤ branch_box_17.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_17, Box.profileLo, Box.profileHi, box_17]
theorem leaf_17_BranchSafe : CertificateConsequences.BranchSafe branch_box_17 := by
  left; refine ⟨branch_box_17_nonnegative, ?_⟩
  intro z hz; exact leaf_17_sound hz

theorem leaf_19_ok : checkAt 527 1000 box_19 cert_19 = true := by
  have h := List.all_eq_true.mp batch_00_05_ok accepted_19 (by simp [batch_00_05_values])
  exact h
theorem leaf_19_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_19.profileLo box_19.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_19_ok
theorem branch_box_19_nonnegative : ∀ j, 0 ≤ branch_box_19.lower j ∧ 0 ≤ branch_box_19.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_19, Box.profileLo, Box.profileHi, box_19]
theorem leaf_19_BranchSafe : CertificateConsequences.BranchSafe branch_box_19 := by
  left; refine ⟨branch_box_19_nonnegative, ?_⟩
  intro z hz; exact leaf_19_sound hz

theorem leaf_24_ok : checkAt 527 1000 box_24 cert_24 = true := by
  have h := List.all_eq_true.mp batch_00_06_ok accepted_24 (by simp [batch_00_06_values])
  exact h
theorem leaf_24_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_24.profileLo box_24.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_24_ok
theorem branch_box_24_nonnegative : ∀ j, 0 ≤ branch_box_24.lower j ∧ 0 ≤ branch_box_24.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_24, Box.profileLo, Box.profileHi, box_24]
theorem leaf_24_BranchSafe : CertificateConsequences.BranchSafe branch_box_24 := by
  left; refine ⟨branch_box_24_nonnegative, ?_⟩
  intro z hz; exact leaf_24_sound hz

theorem leaf_29_ok : checkAt 527 1000 box_29 cert_29 = true := by
  have h := List.all_eq_true.mp batch_00_07_ok accepted_29 (by simp [batch_00_07_values])
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

theorem leaf_31_ok : checkAt 527 1000 box_31 cert_31 = true := by
  have h := List.all_eq_true.mp batch_00_08_ok accepted_31 (by simp [batch_00_08_values])
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

theorem leaf_33_ok : checkAt 527 1000 box_33 cert_33 = true := by
  have h := List.all_eq_true.mp batch_00_09_ok accepted_33 (by simp [batch_00_09_values])
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

theorem leaf_36_ok : checkAt 527 1000 box_36 cert_36 = true := by
  have h := List.all_eq_true.mp batch_00_10_ok accepted_36 (by simp [batch_00_10_values])
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
  have h := List.all_eq_true.mp batch_00_11_ok accepted_37 (by simp [batch_00_11_values])
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

theorem leaf_39_ok : checkAt 527 1000 box_39 cert_39 = true := by
  have h := List.all_eq_true.mp batch_00_12_ok accepted_39 (by simp [batch_00_12_values])
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

theorem leaf_43_ok : checkAt 527 1000 box_43 cert_43 = true := by
  have h := List.all_eq_true.mp batch_00_13_ok accepted_43 (by simp [batch_00_13_values])
  exact h
theorem leaf_43_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_43.profileLo box_43.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_43_ok
theorem branch_box_43_nonnegative : ∀ j, 0 ≤ branch_box_43.lower j ∧ 0 ≤ branch_box_43.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_43, Box.profileLo, Box.profileHi, box_43]
theorem leaf_43_BranchSafe : CertificateConsequences.BranchSafe branch_box_43 := by
  left; refine ⟨branch_box_43_nonnegative, ?_⟩
  intro z hz; exact leaf_43_sound hz

theorem leaf_45_ok : checkAt 527 1000 box_45 cert_45 = true := by
  have h := List.all_eq_true.mp batch_00_14_ok accepted_45 (by simp [batch_00_14_values])
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

theorem leaf_47_ok : checkAt 527 1000 box_47 cert_47 = true := by
  have h := List.all_eq_true.mp batch_00_15_ok accepted_47 (by simp [batch_00_15_values])
  exact h
theorem leaf_47_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_47.profileLo box_47.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_47_ok
theorem branch_box_47_nonnegative : ∀ j, 0 ≤ branch_box_47.lower j ∧ 0 ≤ branch_box_47.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_47, Box.profileLo, Box.profileHi, box_47]
theorem leaf_47_BranchSafe : CertificateConsequences.BranchSafe branch_box_47 := by
  left; refine ⟨branch_box_47_nonnegative, ?_⟩
  intro z hz; exact leaf_47_sound hz

#print axioms batch_00_00_ok
#print axioms leaf_5_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
