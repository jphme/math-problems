import PeaceableQueens.UpperBound.Generated.Even.C527Scaled78Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_78_00_values : List Bool := [accepted_3900]
theorem batch_78_00_ok : batch_78_00_values.all id = true := by decide

def batch_78_01_values : List Bool := [accepted_3905]
theorem batch_78_01_ok : batch_78_01_values.all id = true := by decide

def batch_78_02_values : List Bool := [accepted_3909]
theorem batch_78_02_ok : batch_78_02_values.all id = true := by decide

def batch_78_03_values : List Bool := [accepted_3910]
theorem batch_78_03_ok : batch_78_03_values.all id = true := by decide

def batch_78_04_values : List Bool := [accepted_3911]
theorem batch_78_04_ok : batch_78_04_values.all id = true := by decide

def batch_78_05_values : List Bool := [accepted_3913]
theorem batch_78_05_ok : batch_78_05_values.all id = true := by decide

def batch_78_06_values : List Bool := [accepted_3914]
theorem batch_78_06_ok : batch_78_06_values.all id = true := by decide

def batch_78_07_values : List Bool := [accepted_3915]
theorem batch_78_07_ok : batch_78_07_values.all id = true := by decide

def batch_78_08_values : List Bool := [accepted_3919]
theorem batch_78_08_ok : batch_78_08_values.all id = true := by decide

def batch_78_09_values : List Bool := [accepted_3920]
theorem batch_78_09_ok : batch_78_09_values.all id = true := by decide

def batch_78_10_values : List Bool := [accepted_3921]
theorem batch_78_10_ok : batch_78_10_values.all id = true := by decide

def batch_78_11_values : List Bool := [accepted_3925]
theorem batch_78_11_ok : batch_78_11_values.all id = true := by decide

def batch_78_12_values : List Bool := [accepted_3926]
theorem batch_78_12_ok : batch_78_12_values.all id = true := by decide

def batch_78_13_values : List Bool := [accepted_3931]
theorem batch_78_13_ok : batch_78_13_values.all id = true := by decide

def batch_78_14_values : List Bool := [accepted_3932]
theorem batch_78_14_ok : batch_78_14_values.all id = true := by decide

def batch_78_15_values : List Bool := [accepted_3937]
theorem batch_78_15_ok : batch_78_15_values.all id = true := by decide

def batch_78_16_values : List Bool := [accepted_3938]
theorem batch_78_16_ok : batch_78_16_values.all id = true := by decide

def batch_78_17_values : List Bool := [accepted_3941]
theorem batch_78_17_ok : batch_78_17_values.all id = true := by decide

def batch_78_18_values : List Bool := [accepted_3942]
theorem batch_78_18_ok : batch_78_18_values.all id = true := by decide

theorem leaf_3900_ok : checkAt 527 1000 box_3900 cert_3900 = true := by
  have h := List.all_eq_true.mp batch_78_00_ok accepted_3900 (by simp [batch_78_00_values])
  exact h
theorem leaf_3900_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3900.profileLo box_3900.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3900_ok
theorem branch_box_3900_nonnegative : ∀ j, 0 ≤ branch_box_3900.lower j ∧ 0 ≤ branch_box_3900.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3900, Box.profileLo, Box.profileHi, box_3900]
theorem leaf_3900_BranchSafe : CertificateConsequences.BranchSafe branch_box_3900 := by
  left; refine ⟨branch_box_3900_nonnegative, ?_⟩
  intro z hz; exact leaf_3900_sound hz

theorem leaf_3905_ok : checkAt 527 1000 box_3905 cert_3905 = true := by
  have h := List.all_eq_true.mp batch_78_01_ok accepted_3905 (by simp [batch_78_01_values])
  exact h
theorem leaf_3905_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3905.profileLo box_3905.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3905_ok
theorem branch_box_3905_nonnegative : ∀ j, 0 ≤ branch_box_3905.lower j ∧ 0 ≤ branch_box_3905.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3905, Box.profileLo, Box.profileHi, box_3905]
theorem leaf_3905_BranchSafe : CertificateConsequences.BranchSafe branch_box_3905 := by
  left; refine ⟨branch_box_3905_nonnegative, ?_⟩
  intro z hz; exact leaf_3905_sound hz

theorem leaf_3909_ok : checkAt 527 1000 box_3909 cert_3909 = true := by
  have h := List.all_eq_true.mp batch_78_02_ok accepted_3909 (by simp [batch_78_02_values])
  exact h
theorem leaf_3909_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3909.profileLo box_3909.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3909_ok
theorem branch_box_3909_nonnegative : ∀ j, 0 ≤ branch_box_3909.lower j ∧ 0 ≤ branch_box_3909.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3909, Box.profileLo, Box.profileHi, box_3909]
theorem leaf_3909_BranchSafe : CertificateConsequences.BranchSafe branch_box_3909 := by
  left; refine ⟨branch_box_3909_nonnegative, ?_⟩
  intro z hz; exact leaf_3909_sound hz

theorem leaf_3910_ok : checkAt 527 1000 box_3910 cert_3910 = true := by
  have h := List.all_eq_true.mp batch_78_03_ok accepted_3910 (by simp [batch_78_03_values])
  exact h
theorem leaf_3910_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3910.profileLo box_3910.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3910_ok
theorem branch_box_3910_nonnegative : ∀ j, 0 ≤ branch_box_3910.lower j ∧ 0 ≤ branch_box_3910.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3910, Box.profileLo, Box.profileHi, box_3910]
theorem leaf_3910_BranchSafe : CertificateConsequences.BranchSafe branch_box_3910 := by
  left; refine ⟨branch_box_3910_nonnegative, ?_⟩
  intro z hz; exact leaf_3910_sound hz

theorem leaf_3911_ok : checkAt 527 1000 box_3911 cert_3911 = true := by
  have h := List.all_eq_true.mp batch_78_04_ok accepted_3911 (by simp [batch_78_04_values])
  exact h
theorem leaf_3911_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3911.profileLo box_3911.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3911_ok
theorem branch_box_3911_nonnegative : ∀ j, 0 ≤ branch_box_3911.lower j ∧ 0 ≤ branch_box_3911.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3911, Box.profileLo, Box.profileHi, box_3911]
theorem leaf_3911_BranchSafe : CertificateConsequences.BranchSafe branch_box_3911 := by
  left; refine ⟨branch_box_3911_nonnegative, ?_⟩
  intro z hz; exact leaf_3911_sound hz

theorem leaf_3913_ok : checkAt 527 1000 box_3913 cert_3913 = true := by
  have h := List.all_eq_true.mp batch_78_05_ok accepted_3913 (by simp [batch_78_05_values])
  exact h
theorem leaf_3913_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3913.profileLo box_3913.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3913_ok
theorem branch_box_3913_nonnegative : ∀ j, 0 ≤ branch_box_3913.lower j ∧ 0 ≤ branch_box_3913.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3913, Box.profileLo, Box.profileHi, box_3913]
theorem leaf_3913_BranchSafe : CertificateConsequences.BranchSafe branch_box_3913 := by
  left; refine ⟨branch_box_3913_nonnegative, ?_⟩
  intro z hz; exact leaf_3913_sound hz

theorem leaf_3914_ok : checkAt 527 1000 box_3914 cert_3914 = true := by
  have h := List.all_eq_true.mp batch_78_06_ok accepted_3914 (by simp [batch_78_06_values])
  exact h
theorem leaf_3914_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3914.profileLo box_3914.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3914_ok
theorem branch_box_3914_nonnegative : ∀ j, 0 ≤ branch_box_3914.lower j ∧ 0 ≤ branch_box_3914.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3914, Box.profileLo, Box.profileHi, box_3914]
theorem leaf_3914_BranchSafe : CertificateConsequences.BranchSafe branch_box_3914 := by
  left; refine ⟨branch_box_3914_nonnegative, ?_⟩
  intro z hz; exact leaf_3914_sound hz

theorem leaf_3915_ok : checkAt 527 1000 box_3915 cert_3915 = true := by
  have h := List.all_eq_true.mp batch_78_07_ok accepted_3915 (by simp [batch_78_07_values])
  exact h
theorem leaf_3915_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3915.profileLo box_3915.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3915_ok
theorem branch_box_3915_nonnegative : ∀ j, 0 ≤ branch_box_3915.lower j ∧ 0 ≤ branch_box_3915.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3915, Box.profileLo, Box.profileHi, box_3915]
theorem leaf_3915_BranchSafe : CertificateConsequences.BranchSafe branch_box_3915 := by
  left; refine ⟨branch_box_3915_nonnegative, ?_⟩
  intro z hz; exact leaf_3915_sound hz

theorem leaf_3919_ok : checkAt 527 1000 box_3919 cert_3919 = true := by
  have h := List.all_eq_true.mp batch_78_08_ok accepted_3919 (by simp [batch_78_08_values])
  exact h
theorem leaf_3919_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3919.profileLo box_3919.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3919_ok
theorem branch_box_3919_nonnegative : ∀ j, 0 ≤ branch_box_3919.lower j ∧ 0 ≤ branch_box_3919.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3919, Box.profileLo, Box.profileHi, box_3919]
theorem leaf_3919_BranchSafe : CertificateConsequences.BranchSafe branch_box_3919 := by
  left; refine ⟨branch_box_3919_nonnegative, ?_⟩
  intro z hz; exact leaf_3919_sound hz

theorem leaf_3920_ok : checkAt 527 1000 box_3920 cert_3920 = true := by
  have h := List.all_eq_true.mp batch_78_09_ok accepted_3920 (by simp [batch_78_09_values])
  exact h
theorem leaf_3920_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3920.profileLo box_3920.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3920_ok
theorem branch_box_3920_nonnegative : ∀ j, 0 ≤ branch_box_3920.lower j ∧ 0 ≤ branch_box_3920.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3920, Box.profileLo, Box.profileHi, box_3920]
theorem leaf_3920_BranchSafe : CertificateConsequences.BranchSafe branch_box_3920 := by
  left; refine ⟨branch_box_3920_nonnegative, ?_⟩
  intro z hz; exact leaf_3920_sound hz

theorem leaf_3921_ok : checkAt 527 1000 box_3921 cert_3921 = true := by
  have h := List.all_eq_true.mp batch_78_10_ok accepted_3921 (by simp [batch_78_10_values])
  exact h
theorem leaf_3921_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3921.profileLo box_3921.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3921_ok
theorem branch_box_3921_nonnegative : ∀ j, 0 ≤ branch_box_3921.lower j ∧ 0 ≤ branch_box_3921.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3921, Box.profileLo, Box.profileHi, box_3921]
theorem leaf_3921_BranchSafe : CertificateConsequences.BranchSafe branch_box_3921 := by
  left; refine ⟨branch_box_3921_nonnegative, ?_⟩
  intro z hz; exact leaf_3921_sound hz

theorem leaf_3925_ok : checkAt 527 1000 box_3925 cert_3925 = true := by
  have h := List.all_eq_true.mp batch_78_11_ok accepted_3925 (by simp [batch_78_11_values])
  exact h
theorem leaf_3925_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3925.profileLo box_3925.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3925_ok
theorem branch_box_3925_nonnegative : ∀ j, 0 ≤ branch_box_3925.lower j ∧ 0 ≤ branch_box_3925.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3925, Box.profileLo, Box.profileHi, box_3925]
theorem leaf_3925_BranchSafe : CertificateConsequences.BranchSafe branch_box_3925 := by
  left; refine ⟨branch_box_3925_nonnegative, ?_⟩
  intro z hz; exact leaf_3925_sound hz

theorem leaf_3926_ok : checkAt 527 1000 box_3926 cert_3926 = true := by
  have h := List.all_eq_true.mp batch_78_12_ok accepted_3926 (by simp [batch_78_12_values])
  exact h
theorem leaf_3926_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3926.profileLo box_3926.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3926_ok
theorem branch_box_3926_nonnegative : ∀ j, 0 ≤ branch_box_3926.lower j ∧ 0 ≤ branch_box_3926.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3926, Box.profileLo, Box.profileHi, box_3926]
theorem leaf_3926_BranchSafe : CertificateConsequences.BranchSafe branch_box_3926 := by
  left; refine ⟨branch_box_3926_nonnegative, ?_⟩
  intro z hz; exact leaf_3926_sound hz

theorem leaf_3931_ok : checkAt 527 1000 box_3931 cert_3931 = true := by
  have h := List.all_eq_true.mp batch_78_13_ok accepted_3931 (by simp [batch_78_13_values])
  exact h
theorem leaf_3931_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3931.profileLo box_3931.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3931_ok
theorem branch_box_3931_nonnegative : ∀ j, 0 ≤ branch_box_3931.lower j ∧ 0 ≤ branch_box_3931.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3931, Box.profileLo, Box.profileHi, box_3931]
theorem leaf_3931_BranchSafe : CertificateConsequences.BranchSafe branch_box_3931 := by
  left; refine ⟨branch_box_3931_nonnegative, ?_⟩
  intro z hz; exact leaf_3931_sound hz

theorem leaf_3932_ok : checkAt 527 1000 box_3932 cert_3932 = true := by
  have h := List.all_eq_true.mp batch_78_14_ok accepted_3932 (by simp [batch_78_14_values])
  exact h
theorem leaf_3932_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3932.profileLo box_3932.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3932_ok
theorem branch_box_3932_nonnegative : ∀ j, 0 ≤ branch_box_3932.lower j ∧ 0 ≤ branch_box_3932.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3932, Box.profileLo, Box.profileHi, box_3932]
theorem leaf_3932_BranchSafe : CertificateConsequences.BranchSafe branch_box_3932 := by
  left; refine ⟨branch_box_3932_nonnegative, ?_⟩
  intro z hz; exact leaf_3932_sound hz

theorem leaf_3937_ok : checkAt 527 1000 box_3937 cert_3937 = true := by
  have h := List.all_eq_true.mp batch_78_15_ok accepted_3937 (by simp [batch_78_15_values])
  exact h
theorem leaf_3937_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3937.profileLo box_3937.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3937_ok
theorem branch_box_3937_nonnegative : ∀ j, 0 ≤ branch_box_3937.lower j ∧ 0 ≤ branch_box_3937.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3937, Box.profileLo, Box.profileHi, box_3937]
theorem leaf_3937_BranchSafe : CertificateConsequences.BranchSafe branch_box_3937 := by
  left; refine ⟨branch_box_3937_nonnegative, ?_⟩
  intro z hz; exact leaf_3937_sound hz

theorem leaf_3938_ok : checkAt 527 1000 box_3938 cert_3938 = true := by
  have h := List.all_eq_true.mp batch_78_16_ok accepted_3938 (by simp [batch_78_16_values])
  exact h
theorem leaf_3938_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3938.profileLo box_3938.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3938_ok
theorem branch_box_3938_nonnegative : ∀ j, 0 ≤ branch_box_3938.lower j ∧ 0 ≤ branch_box_3938.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3938, Box.profileLo, Box.profileHi, box_3938]
theorem leaf_3938_BranchSafe : CertificateConsequences.BranchSafe branch_box_3938 := by
  left; refine ⟨branch_box_3938_nonnegative, ?_⟩
  intro z hz; exact leaf_3938_sound hz

theorem leaf_3941_ok : checkAt 527 1000 box_3941 cert_3941 = true := by
  have h := List.all_eq_true.mp batch_78_17_ok accepted_3941 (by simp [batch_78_17_values])
  exact h
theorem leaf_3941_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3941.profileLo box_3941.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3941_ok
theorem branch_box_3941_nonnegative : ∀ j, 0 ≤ branch_box_3941.lower j ∧ 0 ≤ branch_box_3941.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3941, Box.profileLo, Box.profileHi, box_3941]
theorem leaf_3941_BranchSafe : CertificateConsequences.BranchSafe branch_box_3941 := by
  left; refine ⟨branch_box_3941_nonnegative, ?_⟩
  intro z hz; exact leaf_3941_sound hz

theorem leaf_3942_ok : checkAt 527 1000 box_3942 cert_3942 = true := by
  have h := List.all_eq_true.mp batch_78_18_ok accepted_3942 (by simp [batch_78_18_values])
  exact h
theorem leaf_3942_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3942.profileLo box_3942.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3942_ok
theorem branch_box_3942_nonnegative : ∀ j, 0 ≤ branch_box_3942.lower j ∧ 0 ≤ branch_box_3942.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3942, Box.profileLo, Box.profileHi, box_3942]
theorem leaf_3942_BranchSafe : CertificateConsequences.BranchSafe branch_box_3942 := by
  left; refine ⟨branch_box_3942_nonnegative, ?_⟩
  intro z hz; exact leaf_3942_sound hz

#print axioms batch_78_00_ok
#print axioms leaf_3900_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
