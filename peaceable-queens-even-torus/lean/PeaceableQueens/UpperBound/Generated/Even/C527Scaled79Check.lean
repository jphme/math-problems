import PeaceableQueens.UpperBound.Generated.Even.C527Scaled79Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_79_00_values : List Bool := [accepted_3951]
theorem batch_79_00_ok : batch_79_00_values.all id = true := by decide

def batch_79_01_values : List Bool := [accepted_3952]
theorem batch_79_01_ok : batch_79_01_values.all id = true := by decide

def batch_79_02_values : List Bool := [accepted_3954]
theorem batch_79_02_ok : batch_79_02_values.all id = true := by decide

def batch_79_03_values : List Bool := [accepted_3955]
theorem batch_79_03_ok : batch_79_03_values.all id = true := by decide

def batch_79_04_values : List Bool := [accepted_3956]
theorem batch_79_04_ok : batch_79_04_values.all id = true := by decide

def batch_79_05_values : List Bool := [accepted_3957]
theorem batch_79_05_ok : batch_79_05_values.all id = true := by decide

def batch_79_06_values : List Bool := [accepted_3958]
theorem batch_79_06_ok : batch_79_06_values.all id = true := by decide

def batch_79_07_values : List Bool := [accepted_3965]
theorem batch_79_07_ok : batch_79_07_values.all id = true := by decide

def batch_79_08_values : List Bool := [accepted_3966]
theorem batch_79_08_ok : batch_79_08_values.all id = true := by decide

def batch_79_09_values : List Bool := [accepted_3968]
theorem batch_79_09_ok : batch_79_09_values.all id = true := by decide

def batch_79_10_values : List Bool := [accepted_3969]
theorem batch_79_10_ok : batch_79_10_values.all id = true := by decide

def batch_79_11_values : List Bool := [accepted_3970]
theorem batch_79_11_ok : batch_79_11_values.all id = true := by decide

def batch_79_12_values : List Bool := [accepted_3971]
theorem batch_79_12_ok : batch_79_12_values.all id = true := by decide

def batch_79_13_values : List Bool := [accepted_3972]
theorem batch_79_13_ok : batch_79_13_values.all id = true := by decide

def batch_79_14_values : List Bool := [accepted_3975]
theorem batch_79_14_ok : batch_79_14_values.all id = true := by decide

def batch_79_15_values : List Bool := [accepted_3978]
theorem batch_79_15_ok : batch_79_15_values.all id = true := by decide

def batch_79_16_values : List Bool := [accepted_3979]
theorem batch_79_16_ok : batch_79_16_values.all id = true := by decide

def batch_79_17_values : List Bool := [accepted_3980]
theorem batch_79_17_ok : batch_79_17_values.all id = true := by decide

def batch_79_18_values : List Bool := [accepted_3981]
theorem batch_79_18_ok : batch_79_18_values.all id = true := by decide

def batch_79_19_values : List Bool := [accepted_3982]
theorem batch_79_19_ok : batch_79_19_values.all id = true := by decide

def batch_79_20_values : List Bool := [accepted_3991]
theorem batch_79_20_ok : batch_79_20_values.all id = true := by decide

def batch_79_21_values : List Bool := [accepted_3996]
theorem batch_79_21_ok : batch_79_21_values.all id = true := by decide

def batch_79_22_values : List Bool := [accepted_3997]
theorem batch_79_22_ok : batch_79_22_values.all id = true := by decide

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

theorem leaf_3952_ok : checkAt 527 1000 box_3952 cert_3952 = true := by
  have h := List.all_eq_true.mp batch_79_01_ok accepted_3952 (by simp [batch_79_01_values])
  exact h
theorem leaf_3952_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3952.profileLo box_3952.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3952_ok
theorem branch_box_3952_nonnegative : ∀ j, 0 ≤ branch_box_3952.lower j ∧ 0 ≤ branch_box_3952.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3952, Box.profileLo, Box.profileHi, box_3952]
theorem leaf_3952_BranchSafe : CertificateConsequences.BranchSafe branch_box_3952 := by
  left; refine ⟨branch_box_3952_nonnegative, ?_⟩
  intro z hz; exact leaf_3952_sound hz

theorem leaf_3954_ok : checkAt 527 1000 box_3954 cert_3954 = true := by
  have h := List.all_eq_true.mp batch_79_02_ok accepted_3954 (by simp [batch_79_02_values])
  exact h
theorem leaf_3954_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3954.profileLo box_3954.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3954_ok
theorem branch_box_3954_nonnegative : ∀ j, 0 ≤ branch_box_3954.lower j ∧ 0 ≤ branch_box_3954.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3954, Box.profileLo, Box.profileHi, box_3954]
theorem leaf_3954_BranchSafe : CertificateConsequences.BranchSafe branch_box_3954 := by
  left; refine ⟨branch_box_3954_nonnegative, ?_⟩
  intro z hz; exact leaf_3954_sound hz

theorem leaf_3955_ok : checkAt 527 1000 box_3955 cert_3955 = true := by
  have h := List.all_eq_true.mp batch_79_03_ok accepted_3955 (by simp [batch_79_03_values])
  exact h
theorem leaf_3955_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3955.profileLo box_3955.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3955_ok
theorem branch_box_3955_nonnegative : ∀ j, 0 ≤ branch_box_3955.lower j ∧ 0 ≤ branch_box_3955.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3955, Box.profileLo, Box.profileHi, box_3955]
theorem leaf_3955_BranchSafe : CertificateConsequences.BranchSafe branch_box_3955 := by
  left; refine ⟨branch_box_3955_nonnegative, ?_⟩
  intro z hz; exact leaf_3955_sound hz

theorem leaf_3956_ok : checkAt 527 1000 box_3956 cert_3956 = true := by
  have h := List.all_eq_true.mp batch_79_04_ok accepted_3956 (by simp [batch_79_04_values])
  exact h
theorem leaf_3956_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3956.profileLo box_3956.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3956_ok
theorem branch_box_3956_nonnegative : ∀ j, 0 ≤ branch_box_3956.lower j ∧ 0 ≤ branch_box_3956.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3956, Box.profileLo, Box.profileHi, box_3956]
theorem leaf_3956_BranchSafe : CertificateConsequences.BranchSafe branch_box_3956 := by
  left; refine ⟨branch_box_3956_nonnegative, ?_⟩
  intro z hz; exact leaf_3956_sound hz

theorem leaf_3957_ok : checkAt 527 1000 box_3957 cert_3957 = true := by
  have h := List.all_eq_true.mp batch_79_05_ok accepted_3957 (by simp [batch_79_05_values])
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

theorem leaf_3958_ok : checkAt 527 1000 box_3958 cert_3958 = true := by
  have h := List.all_eq_true.mp batch_79_06_ok accepted_3958 (by simp [batch_79_06_values])
  exact h
theorem leaf_3958_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3958.profileLo box_3958.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3958_ok
theorem branch_box_3958_nonnegative : ∀ j, 0 ≤ branch_box_3958.lower j ∧ 0 ≤ branch_box_3958.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3958, Box.profileLo, Box.profileHi, box_3958]
theorem leaf_3958_BranchSafe : CertificateConsequences.BranchSafe branch_box_3958 := by
  left; refine ⟨branch_box_3958_nonnegative, ?_⟩
  intro z hz; exact leaf_3958_sound hz

theorem leaf_3965_ok : checkAt 527 1000 box_3965 cert_3965 = true := by
  have h := List.all_eq_true.mp batch_79_07_ok accepted_3965 (by simp [batch_79_07_values])
  exact h
theorem leaf_3965_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3965.profileLo box_3965.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3965_ok
theorem branch_box_3965_nonnegative : ∀ j, 0 ≤ branch_box_3965.lower j ∧ 0 ≤ branch_box_3965.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3965, Box.profileLo, Box.profileHi, box_3965]
theorem leaf_3965_BranchSafe : CertificateConsequences.BranchSafe branch_box_3965 := by
  left; refine ⟨branch_box_3965_nonnegative, ?_⟩
  intro z hz; exact leaf_3965_sound hz

theorem leaf_3966_ok : checkAt 527 1000 box_3966 cert_3966 = true := by
  have h := List.all_eq_true.mp batch_79_08_ok accepted_3966 (by simp [batch_79_08_values])
  exact h
theorem leaf_3966_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3966.profileLo box_3966.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3966_ok
theorem branch_box_3966_nonnegative : ∀ j, 0 ≤ branch_box_3966.lower j ∧ 0 ≤ branch_box_3966.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3966, Box.profileLo, Box.profileHi, box_3966]
theorem leaf_3966_BranchSafe : CertificateConsequences.BranchSafe branch_box_3966 := by
  left; refine ⟨branch_box_3966_nonnegative, ?_⟩
  intro z hz; exact leaf_3966_sound hz

theorem leaf_3968_ok : checkAt 527 1000 box_3968 cert_3968 = true := by
  have h := List.all_eq_true.mp batch_79_09_ok accepted_3968 (by simp [batch_79_09_values])
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
  have h := List.all_eq_true.mp batch_79_10_ok accepted_3969 (by simp [batch_79_10_values])
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

theorem leaf_3970_ok : checkAt 527 1000 box_3970 cert_3970 = true := by
  have h := List.all_eq_true.mp batch_79_11_ok accepted_3970 (by simp [batch_79_11_values])
  exact h
theorem leaf_3970_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3970.profileLo box_3970.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3970_ok
theorem branch_box_3970_nonnegative : ∀ j, 0 ≤ branch_box_3970.lower j ∧ 0 ≤ branch_box_3970.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3970, Box.profileLo, Box.profileHi, box_3970]
theorem leaf_3970_BranchSafe : CertificateConsequences.BranchSafe branch_box_3970 := by
  left; refine ⟨branch_box_3970_nonnegative, ?_⟩
  intro z hz; exact leaf_3970_sound hz

theorem leaf_3971_ok : checkAt 527 1000 box_3971 cert_3971 = true := by
  have h := List.all_eq_true.mp batch_79_12_ok accepted_3971 (by simp [batch_79_12_values])
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

theorem leaf_3972_ok : checkAt 527 1000 box_3972 cert_3972 = true := by
  have h := List.all_eq_true.mp batch_79_13_ok accepted_3972 (by simp [batch_79_13_values])
  exact h
theorem leaf_3972_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3972.profileLo box_3972.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3972_ok
theorem branch_box_3972_nonnegative : ∀ j, 0 ≤ branch_box_3972.lower j ∧ 0 ≤ branch_box_3972.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3972, Box.profileLo, Box.profileHi, box_3972]
theorem leaf_3972_BranchSafe : CertificateConsequences.BranchSafe branch_box_3972 := by
  left; refine ⟨branch_box_3972_nonnegative, ?_⟩
  intro z hz; exact leaf_3972_sound hz

theorem leaf_3975_ok : checkAt 527 1000 box_3975 cert_3975 = true := by
  have h := List.all_eq_true.mp batch_79_14_ok accepted_3975 (by simp [batch_79_14_values])
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

theorem leaf_3978_ok : checkAt 527 1000 box_3978 cert_3978 = true := by
  have h := List.all_eq_true.mp batch_79_15_ok accepted_3978 (by simp [batch_79_15_values])
  exact h
theorem leaf_3978_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3978.profileLo box_3978.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3978_ok
theorem branch_box_3978_nonnegative : ∀ j, 0 ≤ branch_box_3978.lower j ∧ 0 ≤ branch_box_3978.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3978, Box.profileLo, Box.profileHi, box_3978]
theorem leaf_3978_BranchSafe : CertificateConsequences.BranchSafe branch_box_3978 := by
  left; refine ⟨branch_box_3978_nonnegative, ?_⟩
  intro z hz; exact leaf_3978_sound hz

theorem leaf_3979_ok : checkAt 527 1000 box_3979 cert_3979 = true := by
  have h := List.all_eq_true.mp batch_79_16_ok accepted_3979 (by simp [batch_79_16_values])
  exact h
theorem leaf_3979_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3979.profileLo box_3979.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3979_ok
theorem branch_box_3979_nonnegative : ∀ j, 0 ≤ branch_box_3979.lower j ∧ 0 ≤ branch_box_3979.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3979, Box.profileLo, Box.profileHi, box_3979]
theorem leaf_3979_BranchSafe : CertificateConsequences.BranchSafe branch_box_3979 := by
  left; refine ⟨branch_box_3979_nonnegative, ?_⟩
  intro z hz; exact leaf_3979_sound hz

theorem leaf_3980_ok : checkAt 527 1000 box_3980 cert_3980 = true := by
  have h := List.all_eq_true.mp batch_79_17_ok accepted_3980 (by simp [batch_79_17_values])
  exact h
theorem leaf_3980_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3980.profileLo box_3980.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3980_ok
theorem branch_box_3980_nonnegative : ∀ j, 0 ≤ branch_box_3980.lower j ∧ 0 ≤ branch_box_3980.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3980, Box.profileLo, Box.profileHi, box_3980]
theorem leaf_3980_BranchSafe : CertificateConsequences.BranchSafe branch_box_3980 := by
  left; refine ⟨branch_box_3980_nonnegative, ?_⟩
  intro z hz; exact leaf_3980_sound hz

theorem leaf_3981_ok : checkAt 527 1000 box_3981 cert_3981 = true := by
  have h := List.all_eq_true.mp batch_79_18_ok accepted_3981 (by simp [batch_79_18_values])
  exact h
theorem leaf_3981_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3981.profileLo box_3981.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3981_ok
theorem branch_box_3981_nonnegative : ∀ j, 0 ≤ branch_box_3981.lower j ∧ 0 ≤ branch_box_3981.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3981, Box.profileLo, Box.profileHi, box_3981]
theorem leaf_3981_BranchSafe : CertificateConsequences.BranchSafe branch_box_3981 := by
  left; refine ⟨branch_box_3981_nonnegative, ?_⟩
  intro z hz; exact leaf_3981_sound hz

theorem leaf_3982_ok : checkAt 527 1000 box_3982 cert_3982 = true := by
  have h := List.all_eq_true.mp batch_79_19_ok accepted_3982 (by simp [batch_79_19_values])
  exact h
theorem leaf_3982_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3982.profileLo box_3982.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3982_ok
theorem branch_box_3982_nonnegative : ∀ j, 0 ≤ branch_box_3982.lower j ∧ 0 ≤ branch_box_3982.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3982, Box.profileLo, Box.profileHi, box_3982]
theorem leaf_3982_BranchSafe : CertificateConsequences.BranchSafe branch_box_3982 := by
  left; refine ⟨branch_box_3982_nonnegative, ?_⟩
  intro z hz; exact leaf_3982_sound hz

theorem leaf_3991_ok : checkAt 527 1000 box_3991 cert_3991 = true := by
  have h := List.all_eq_true.mp batch_79_20_ok accepted_3991 (by simp [batch_79_20_values])
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

theorem leaf_3996_ok : checkAt 527 1000 box_3996 cert_3996 = true := by
  have h := List.all_eq_true.mp batch_79_21_ok accepted_3996 (by simp [batch_79_21_values])
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

theorem leaf_3997_ok : checkAt 527 1000 box_3997 cert_3997 = true := by
  have h := List.all_eq_true.mp batch_79_22_ok accepted_3997 (by simp [batch_79_22_values])
  exact h
theorem leaf_3997_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3997.profileLo box_3997.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3997_ok
theorem branch_box_3997_nonnegative : ∀ j, 0 ≤ branch_box_3997.lower j ∧ 0 ≤ branch_box_3997.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3997, Box.profileLo, Box.profileHi, box_3997]
theorem leaf_3997_BranchSafe : CertificateConsequences.BranchSafe branch_box_3997 := by
  left; refine ⟨branch_box_3997_nonnegative, ?_⟩
  intro z hz; exact leaf_3997_sound hz

#print axioms batch_79_00_ok
#print axioms leaf_3951_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
