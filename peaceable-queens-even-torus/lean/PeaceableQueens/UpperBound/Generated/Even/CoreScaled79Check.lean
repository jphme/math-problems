import PeaceableQueens.UpperBound.Generated.Even.CoreScaled79Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_79_00_values : List Bool := [accepted_3951]
theorem batch_79_00_ok : batch_79_00_values.all id = true := by decide

def batch_79_01_values : List Bool := [accepted_3953]
theorem batch_79_01_ok : batch_79_01_values.all id = true := by decide

def batch_79_02_values : List Bool := [accepted_3957]
theorem batch_79_02_ok : batch_79_02_values.all id = true := by decide

def batch_79_03_values : List Bool := [accepted_3960]
theorem batch_79_03_ok : batch_79_03_values.all id = true := by decide

def batch_79_04_values : List Bool := [accepted_3961]
theorem batch_79_04_ok : batch_79_04_values.all id = true := by decide

def batch_79_05_values : List Bool := [accepted_3963]
theorem batch_79_05_ok : batch_79_05_values.all id = true := by decide

def batch_79_06_values : List Bool := [accepted_3968]
theorem batch_79_06_ok : batch_79_06_values.all id = true := by decide

def batch_79_07_values : List Bool := [accepted_3969]
theorem batch_79_07_ok : batch_79_07_values.all id = true := by decide

def batch_79_08_values : List Bool := [accepted_3971]
theorem batch_79_08_ok : batch_79_08_values.all id = true := by decide

def batch_79_09_values : List Bool := [accepted_3974]
theorem batch_79_09_ok : batch_79_09_values.all id = true := by decide

def batch_79_10_values : List Bool := [accepted_3975]
theorem batch_79_10_ok : batch_79_10_values.all id = true := by decide

def batch_79_11_values : List Bool := [accepted_3985]
theorem batch_79_11_ok : batch_79_11_values.all id = true := by decide

def batch_79_12_values : List Bool := [accepted_3991]
theorem batch_79_12_ok : batch_79_12_values.all id = true := by decide

def batch_79_13_values : List Bool := [accepted_3993]
theorem batch_79_13_ok : batch_79_13_values.all id = true := by decide

def batch_79_14_values : List Bool := [accepted_3996]
theorem batch_79_14_ok : batch_79_14_values.all id = true := by decide

theorem leaf_3951_ok : checkAt 527 1000 box_3951 cert_3951 = true := by
  have h := List.all_eq_true.mp batch_79_00_ok accepted_3951 (by simp [batch_79_00_values])
  exact h
theorem leaf_3951_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3951.profileLo box_3951.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3951_ok
theorem branch_box_3951_nonnegative : ∀ j, 0 ≤ branch_box_3951.lower j ∧ 0 ≤ branch_box_3951.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3951, Box.profileLo, Box.profileHi, box_3951]
theorem leaf_3951_BranchSafe : CertificateConsequences.BranchSafe branch_box_3951 := by
  left; refine ⟨branch_box_3951_nonnegative, ?_⟩
  intro z hz; exact leaf_3951_sound hz

theorem leaf_3953_ok : checkAt 527 1000 box_3953 cert_3953 = true := by
  have h := List.all_eq_true.mp batch_79_01_ok accepted_3953 (by simp [batch_79_01_values])
  exact h
theorem leaf_3953_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3953.profileLo box_3953.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3953_ok
theorem branch_box_3953_nonnegative : ∀ j, 0 ≤ branch_box_3953.lower j ∧ 0 ≤ branch_box_3953.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3953, Box.profileLo, Box.profileHi, box_3953]
theorem leaf_3953_BranchSafe : CertificateConsequences.BranchSafe branch_box_3953 := by
  left; refine ⟨branch_box_3953_nonnegative, ?_⟩
  intro z hz; exact leaf_3953_sound hz

theorem leaf_3957_ok : checkAt 527 1000 box_3957 cert_3957 = true := by
  have h := List.all_eq_true.mp batch_79_02_ok accepted_3957 (by simp [batch_79_02_values])
  exact h
theorem leaf_3957_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3957.profileLo box_3957.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3957_ok
theorem branch_box_3957_nonnegative : ∀ j, 0 ≤ branch_box_3957.lower j ∧ 0 ≤ branch_box_3957.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3957, Box.profileLo, Box.profileHi, box_3957]
theorem leaf_3957_BranchSafe : CertificateConsequences.BranchSafe branch_box_3957 := by
  left; refine ⟨branch_box_3957_nonnegative, ?_⟩
  intro z hz; exact leaf_3957_sound hz

theorem leaf_3960_ok : checkAt 527 1000 box_3960 cert_3960 = true := by
  have h := List.all_eq_true.mp batch_79_03_ok accepted_3960 (by simp [batch_79_03_values])
  exact h
theorem leaf_3960_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3960.profileLo box_3960.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3960_ok
theorem branch_box_3960_nonnegative : ∀ j, 0 ≤ branch_box_3960.lower j ∧ 0 ≤ branch_box_3960.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3960, Box.profileLo, Box.profileHi, box_3960]
theorem leaf_3960_BranchSafe : CertificateConsequences.BranchSafe branch_box_3960 := by
  left; refine ⟨branch_box_3960_nonnegative, ?_⟩
  intro z hz; exact leaf_3960_sound hz

theorem leaf_3961_ok : checkAt 527 1000 box_3961 cert_3961 = true := by
  have h := List.all_eq_true.mp batch_79_04_ok accepted_3961 (by simp [batch_79_04_values])
  exact h
theorem leaf_3961_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3961.profileLo box_3961.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3961_ok
theorem branch_box_3961_nonnegative : ∀ j, 0 ≤ branch_box_3961.lower j ∧ 0 ≤ branch_box_3961.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3961, Box.profileLo, Box.profileHi, box_3961]
theorem leaf_3961_BranchSafe : CertificateConsequences.BranchSafe branch_box_3961 := by
  left; refine ⟨branch_box_3961_nonnegative, ?_⟩
  intro z hz; exact leaf_3961_sound hz

theorem leaf_3963_ok : checkAt 527 1000 box_3963 cert_3963 = true := by
  have h := List.all_eq_true.mp batch_79_05_ok accepted_3963 (by simp [batch_79_05_values])
  exact h
theorem leaf_3963_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3963.profileLo box_3963.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3963_ok
theorem branch_box_3963_nonnegative : ∀ j, 0 ≤ branch_box_3963.lower j ∧ 0 ≤ branch_box_3963.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3963, Box.profileLo, Box.profileHi, box_3963]
theorem leaf_3963_BranchSafe : CertificateConsequences.BranchSafe branch_box_3963 := by
  left; refine ⟨branch_box_3963_nonnegative, ?_⟩
  intro z hz; exact leaf_3963_sound hz

theorem leaf_3968_ok : checkAt 527 1000 box_3968 cert_3968 = true := by
  have h := List.all_eq_true.mp batch_79_06_ok accepted_3968 (by simp [batch_79_06_values])
  exact h
theorem leaf_3968_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3968.profileLo box_3968.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3968_ok
theorem branch_box_3968_nonnegative : ∀ j, 0 ≤ branch_box_3968.lower j ∧ 0 ≤ branch_box_3968.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3968, Box.profileLo, Box.profileHi, box_3968]
theorem leaf_3968_BranchSafe : CertificateConsequences.BranchSafe branch_box_3968 := by
  left; refine ⟨branch_box_3968_nonnegative, ?_⟩
  intro z hz; exact leaf_3968_sound hz

theorem leaf_3969_ok : checkAt 527 1000 box_3969 cert_3969 = true := by
  have h := List.all_eq_true.mp batch_79_07_ok accepted_3969 (by simp [batch_79_07_values])
  exact h
theorem leaf_3969_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3969.profileLo box_3969.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3969_ok
theorem branch_box_3969_nonnegative : ∀ j, 0 ≤ branch_box_3969.lower j ∧ 0 ≤ branch_box_3969.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3969, Box.profileLo, Box.profileHi, box_3969]
theorem leaf_3969_BranchSafe : CertificateConsequences.BranchSafe branch_box_3969 := by
  left; refine ⟨branch_box_3969_nonnegative, ?_⟩
  intro z hz; exact leaf_3969_sound hz

theorem leaf_3971_ok : checkAt 527 1000 box_3971 cert_3971 = true := by
  have h := List.all_eq_true.mp batch_79_08_ok accepted_3971 (by simp [batch_79_08_values])
  exact h
theorem leaf_3971_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3971.profileLo box_3971.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3971_ok
theorem branch_box_3971_nonnegative : ∀ j, 0 ≤ branch_box_3971.lower j ∧ 0 ≤ branch_box_3971.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3971, Box.profileLo, Box.profileHi, box_3971]
theorem leaf_3971_BranchSafe : CertificateConsequences.BranchSafe branch_box_3971 := by
  left; refine ⟨branch_box_3971_nonnegative, ?_⟩
  intro z hz; exact leaf_3971_sound hz

theorem leaf_3974_ok : checkAt 527 1000 box_3974 cert_3974 = true := by
  have h := List.all_eq_true.mp batch_79_09_ok accepted_3974 (by simp [batch_79_09_values])
  exact h
theorem leaf_3974_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3974.profileLo box_3974.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3974_ok
theorem branch_box_3974_nonnegative : ∀ j, 0 ≤ branch_box_3974.lower j ∧ 0 ≤ branch_box_3974.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3974, Box.profileLo, Box.profileHi, box_3974]
theorem leaf_3974_BranchSafe : CertificateConsequences.BranchSafe branch_box_3974 := by
  left; refine ⟨branch_box_3974_nonnegative, ?_⟩
  intro z hz; exact leaf_3974_sound hz

theorem leaf_3975_ok : checkAt 527 1000 box_3975 cert_3975 = true := by
  have h := List.all_eq_true.mp batch_79_10_ok accepted_3975 (by simp [batch_79_10_values])
  exact h
theorem leaf_3975_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3975.profileLo box_3975.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3975_ok
theorem branch_box_3975_nonnegative : ∀ j, 0 ≤ branch_box_3975.lower j ∧ 0 ≤ branch_box_3975.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3975, Box.profileLo, Box.profileHi, box_3975]
theorem leaf_3975_BranchSafe : CertificateConsequences.BranchSafe branch_box_3975 := by
  left; refine ⟨branch_box_3975_nonnegative, ?_⟩
  intro z hz; exact leaf_3975_sound hz

theorem leaf_3985_ok : checkAt 527 1000 box_3985 cert_3985 = true := by
  have h := List.all_eq_true.mp batch_79_11_ok accepted_3985 (by simp [batch_79_11_values])
  exact h
theorem leaf_3985_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3985.profileLo box_3985.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3985_ok
theorem branch_box_3985_nonnegative : ∀ j, 0 ≤ branch_box_3985.lower j ∧ 0 ≤ branch_box_3985.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3985, Box.profileLo, Box.profileHi, box_3985]
theorem leaf_3985_BranchSafe : CertificateConsequences.BranchSafe branch_box_3985 := by
  left; refine ⟨branch_box_3985_nonnegative, ?_⟩
  intro z hz; exact leaf_3985_sound hz

theorem leaf_3991_ok : checkAt 527 1000 box_3991 cert_3991 = true := by
  have h := List.all_eq_true.mp batch_79_12_ok accepted_3991 (by simp [batch_79_12_values])
  exact h
theorem leaf_3991_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3991.profileLo box_3991.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3991_ok
theorem branch_box_3991_nonnegative : ∀ j, 0 ≤ branch_box_3991.lower j ∧ 0 ≤ branch_box_3991.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3991, Box.profileLo, Box.profileHi, box_3991]
theorem leaf_3991_BranchSafe : CertificateConsequences.BranchSafe branch_box_3991 := by
  left; refine ⟨branch_box_3991_nonnegative, ?_⟩
  intro z hz; exact leaf_3991_sound hz

theorem leaf_3993_ok : checkAt 527 1000 box_3993 cert_3993 = true := by
  have h := List.all_eq_true.mp batch_79_13_ok accepted_3993 (by simp [batch_79_13_values])
  exact h
theorem leaf_3993_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3993.profileLo box_3993.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3993_ok
theorem branch_box_3993_nonnegative : ∀ j, 0 ≤ branch_box_3993.lower j ∧ 0 ≤ branch_box_3993.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3993, Box.profileLo, Box.profileHi, box_3993]
theorem leaf_3993_BranchSafe : CertificateConsequences.BranchSafe branch_box_3993 := by
  left; refine ⟨branch_box_3993_nonnegative, ?_⟩
  intro z hz; exact leaf_3993_sound hz

theorem leaf_3996_ok : checkAt 527 1000 box_3996 cert_3996 = true := by
  have h := List.all_eq_true.mp batch_79_14_ok accepted_3996 (by simp [batch_79_14_values])
  exact h
theorem leaf_3996_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3996.profileLo box_3996.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3996_ok
theorem branch_box_3996_nonnegative : ∀ j, 0 ≤ branch_box_3996.lower j ∧ 0 ≤ branch_box_3996.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3996, Box.profileLo, Box.profileHi, box_3996]
theorem leaf_3996_BranchSafe : CertificateConsequences.BranchSafe branch_box_3996 := by
  left; refine ⟨branch_box_3996_nonnegative, ?_⟩
  intro z hz; exact leaf_3996_sound hz

#print axioms batch_79_00_ok
#print axioms leaf_3951_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
