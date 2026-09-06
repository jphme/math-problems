import PeaceableQueens.UpperBound.Generated.Even.CoreScaled78Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_78_00_values : List Bool := [accepted_3900]
theorem batch_78_00_ok : batch_78_00_values.all id = true := by decide

def batch_78_01_values : List Bool := [accepted_3902]
theorem batch_78_01_ok : batch_78_01_values.all id = true := by decide

def batch_78_02_values : List Bool := [accepted_3908]
theorem batch_78_02_ok : batch_78_02_values.all id = true := by decide

def batch_78_03_values : List Bool := [accepted_3910]
theorem batch_78_03_ok : batch_78_03_values.all id = true := by decide

def batch_78_04_values : List Bool := [accepted_3911]
theorem batch_78_04_ok : batch_78_04_values.all id = true := by decide

def batch_78_05_values : List Bool := [accepted_3913]
theorem batch_78_05_ok : batch_78_05_values.all id = true := by decide

def batch_78_06_values : List Bool := [accepted_3920]
theorem batch_78_06_ok : batch_78_06_values.all id = true := by decide

def batch_78_07_values : List Bool := [accepted_3921]
theorem batch_78_07_ok : batch_78_07_values.all id = true := by decide

def batch_78_08_values : List Bool := [accepted_3923]
theorem batch_78_08_ok : batch_78_08_values.all id = true := by decide

def batch_78_09_values : List Bool := [accepted_3930]
theorem batch_78_09_ok : batch_78_09_values.all id = true := by decide

def batch_78_10_values : List Bool := [accepted_3935]
theorem batch_78_10_ok : batch_78_10_values.all id = true := by decide

def batch_78_11_values : List Bool := [accepted_3938]
theorem batch_78_11_ok : batch_78_11_values.all id = true := by decide

def batch_78_12_values : List Bool := [accepted_3939]
theorem batch_78_12_ok : batch_78_12_values.all id = true := by decide

def batch_78_13_values : List Bool := [accepted_3942]
theorem batch_78_13_ok : batch_78_13_values.all id = true := by decide

def batch_78_14_values : List Bool := [accepted_3943]
theorem batch_78_14_ok : batch_78_14_values.all id = true := by decide

def batch_78_15_values : List Bool := [accepted_3945]
theorem batch_78_15_ok : batch_78_15_values.all id = true := by decide

def batch_78_16_values : List Bool := [accepted_3948]
theorem batch_78_16_ok : batch_78_16_values.all id = true := by decide

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

theorem leaf_3902_ok : checkAt 527 1000 box_3902 cert_3902 = true := by
  have h := List.all_eq_true.mp batch_78_01_ok accepted_3902 (by simp [batch_78_01_values])
  exact h
theorem leaf_3902_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3902.profileLo box_3902.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3902_ok
theorem branch_box_3902_nonnegative : ∀ j, 0 ≤ branch_box_3902.lower j ∧ 0 ≤ branch_box_3902.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3902, Box.profileLo, Box.profileHi, box_3902]
theorem leaf_3902_BranchSafe : CertificateConsequences.BranchSafe branch_box_3902 := by
  left; refine ⟨branch_box_3902_nonnegative, ?_⟩
  intro z hz; exact leaf_3902_sound hz

theorem leaf_3908_ok : checkAt 527 1000 box_3908 cert_3908 = true := by
  have h := List.all_eq_true.mp batch_78_02_ok accepted_3908 (by simp [batch_78_02_values])
  exact h
theorem leaf_3908_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3908.profileLo box_3908.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3908_ok
theorem branch_box_3908_nonnegative : ∀ j, 0 ≤ branch_box_3908.lower j ∧ 0 ≤ branch_box_3908.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3908, Box.profileLo, Box.profileHi, box_3908]
theorem leaf_3908_BranchSafe : CertificateConsequences.BranchSafe branch_box_3908 := by
  left; refine ⟨branch_box_3908_nonnegative, ?_⟩
  intro z hz; exact leaf_3908_sound hz

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

theorem leaf_3920_ok : checkAt 527 1000 box_3920 cert_3920 = true := by
  have h := List.all_eq_true.mp batch_78_06_ok accepted_3920 (by simp [batch_78_06_values])
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
  have h := List.all_eq_true.mp batch_78_07_ok accepted_3921 (by simp [batch_78_07_values])
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

theorem leaf_3923_ok : checkAt 527 1000 box_3923 cert_3923 = true := by
  have h := List.all_eq_true.mp batch_78_08_ok accepted_3923 (by simp [batch_78_08_values])
  exact h
theorem leaf_3923_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3923.profileLo box_3923.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3923_ok
theorem branch_box_3923_nonnegative : ∀ j, 0 ≤ branch_box_3923.lower j ∧ 0 ≤ branch_box_3923.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3923, Box.profileLo, Box.profileHi, box_3923]
theorem leaf_3923_BranchSafe : CertificateConsequences.BranchSafe branch_box_3923 := by
  left; refine ⟨branch_box_3923_nonnegative, ?_⟩
  intro z hz; exact leaf_3923_sound hz

theorem leaf_3930_ok : checkAt 527 1000 box_3930 cert_3930 = true := by
  have h := List.all_eq_true.mp batch_78_09_ok accepted_3930 (by simp [batch_78_09_values])
  exact h
theorem leaf_3930_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3930.profileLo box_3930.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3930_ok
theorem branch_box_3930_nonnegative : ∀ j, 0 ≤ branch_box_3930.lower j ∧ 0 ≤ branch_box_3930.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3930, Box.profileLo, Box.profileHi, box_3930]
theorem leaf_3930_BranchSafe : CertificateConsequences.BranchSafe branch_box_3930 := by
  left; refine ⟨branch_box_3930_nonnegative, ?_⟩
  intro z hz; exact leaf_3930_sound hz

theorem leaf_3935_ok : checkAt 527 1000 box_3935 cert_3935 = true := by
  have h := List.all_eq_true.mp batch_78_10_ok accepted_3935 (by simp [batch_78_10_values])
  exact h
theorem leaf_3935_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3935.profileLo box_3935.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3935_ok
theorem branch_box_3935_nonnegative : ∀ j, 0 ≤ branch_box_3935.lower j ∧ 0 ≤ branch_box_3935.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3935, Box.profileLo, Box.profileHi, box_3935]
theorem leaf_3935_BranchSafe : CertificateConsequences.BranchSafe branch_box_3935 := by
  left; refine ⟨branch_box_3935_nonnegative, ?_⟩
  intro z hz; exact leaf_3935_sound hz

theorem leaf_3938_ok : checkAt 527 1000 box_3938 cert_3938 = true := by
  have h := List.all_eq_true.mp batch_78_11_ok accepted_3938 (by simp [batch_78_11_values])
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

theorem leaf_3939_ok : checkAt 527 1000 box_3939 cert_3939 = true := by
  have h := List.all_eq_true.mp batch_78_12_ok accepted_3939 (by simp [batch_78_12_values])
  exact h
theorem leaf_3939_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3939.profileLo box_3939.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3939_ok
theorem branch_box_3939_nonnegative : ∀ j, 0 ≤ branch_box_3939.lower j ∧ 0 ≤ branch_box_3939.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3939, Box.profileLo, Box.profileHi, box_3939]
theorem leaf_3939_BranchSafe : CertificateConsequences.BranchSafe branch_box_3939 := by
  left; refine ⟨branch_box_3939_nonnegative, ?_⟩
  intro z hz; exact leaf_3939_sound hz

theorem leaf_3942_ok : checkAt 527 1000 box_3942 cert_3942 = true := by
  have h := List.all_eq_true.mp batch_78_13_ok accepted_3942 (by simp [batch_78_13_values])
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

theorem leaf_3943_ok : checkAt 527 1000 box_3943 cert_3943 = true := by
  have h := List.all_eq_true.mp batch_78_14_ok accepted_3943 (by simp [batch_78_14_values])
  exact h
theorem leaf_3943_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3943.profileLo box_3943.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3943_ok
theorem branch_box_3943_nonnegative : ∀ j, 0 ≤ branch_box_3943.lower j ∧ 0 ≤ branch_box_3943.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3943, Box.profileLo, Box.profileHi, box_3943]
theorem leaf_3943_BranchSafe : CertificateConsequences.BranchSafe branch_box_3943 := by
  left; refine ⟨branch_box_3943_nonnegative, ?_⟩
  intro z hz; exact leaf_3943_sound hz

theorem leaf_3945_ok : checkAt 527 1000 box_3945 cert_3945 = true := by
  have h := List.all_eq_true.mp batch_78_15_ok accepted_3945 (by simp [batch_78_15_values])
  exact h
theorem leaf_3945_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3945.profileLo box_3945.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3945_ok
theorem branch_box_3945_nonnegative : ∀ j, 0 ≤ branch_box_3945.lower j ∧ 0 ≤ branch_box_3945.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3945, Box.profileLo, Box.profileHi, box_3945]
theorem leaf_3945_BranchSafe : CertificateConsequences.BranchSafe branch_box_3945 := by
  left; refine ⟨branch_box_3945_nonnegative, ?_⟩
  intro z hz; exact leaf_3945_sound hz

theorem leaf_3948_ok : checkAt 527 1000 box_3948 cert_3948 = true := by
  have h := List.all_eq_true.mp batch_78_16_ok accepted_3948 (by simp [batch_78_16_values])
  exact h
theorem leaf_3948_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3948.profileLo box_3948.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3948_ok
theorem branch_box_3948_nonnegative : ∀ j, 0 ≤ branch_box_3948.lower j ∧ 0 ≤ branch_box_3948.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3948, Box.profileLo, Box.profileHi, box_3948]
theorem leaf_3948_BranchSafe : CertificateConsequences.BranchSafe branch_box_3948 := by
  left; refine ⟨branch_box_3948_nonnegative, ?_⟩
  intro z hz; exact leaf_3948_sound hz

#print axioms batch_78_00_ok
#print axioms leaf_3900_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
