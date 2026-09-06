import PeaceableQueens.UpperBound.Generated.Even.C527Scaled99Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_99_00_values : List Bool := [accepted_4951]
theorem batch_99_00_ok : batch_99_00_values.all id = true := by decide

def batch_99_01_values : List Bool := [accepted_4952]
theorem batch_99_01_ok : batch_99_01_values.all id = true := by decide

def batch_99_02_values : List Bool := [accepted_4955]
theorem batch_99_02_ok : batch_99_02_values.all id = true := by decide

def batch_99_03_values : List Bool := [accepted_4957]
theorem batch_99_03_ok : batch_99_03_values.all id = true := by decide

def batch_99_04_values : List Bool := [accepted_4958]
theorem batch_99_04_ok : batch_99_04_values.all id = true := by decide

def batch_99_05_values : List Bool := [accepted_4959]
theorem batch_99_05_ok : batch_99_05_values.all id = true := by decide

def batch_99_06_values : List Bool := [accepted_4963]
theorem batch_99_06_ok : batch_99_06_values.all id = true := by decide

def batch_99_07_values : List Bool := [accepted_4965]
theorem batch_99_07_ok : batch_99_07_values.all id = true := by decide

def batch_99_08_values : List Bool := [accepted_4966]
theorem batch_99_08_ok : batch_99_08_values.all id = true := by decide

def batch_99_09_values : List Bool := [accepted_4969]
theorem batch_99_09_ok : batch_99_09_values.all id = true := by decide

def batch_99_10_values : List Bool := [accepted_4970]
theorem batch_99_10_ok : batch_99_10_values.all id = true := by decide

def batch_99_11_values : List Bool := [accepted_4971]
theorem batch_99_11_ok : batch_99_11_values.all id = true := by decide

def batch_99_12_values : List Bool := [accepted_4972]
theorem batch_99_12_ok : batch_99_12_values.all id = true := by decide

def batch_99_13_values : List Bool := [accepted_4979]
theorem batch_99_13_ok : batch_99_13_values.all id = true := by decide

def batch_99_14_values : List Bool := [accepted_4981]
theorem batch_99_14_ok : batch_99_14_values.all id = true := by decide

def batch_99_15_values : List Bool := [accepted_4982]
theorem batch_99_15_ok : batch_99_15_values.all id = true := by decide

def batch_99_16_values : List Bool := [accepted_4983]
theorem batch_99_16_ok : batch_99_16_values.all id = true := by decide

def batch_99_17_values : List Bool := [accepted_4984]
theorem batch_99_17_ok : batch_99_17_values.all id = true := by decide

def batch_99_18_values : List Bool := [accepted_4989]
theorem batch_99_18_ok : batch_99_18_values.all id = true := by decide

def batch_99_19_values : List Bool := [accepted_4991]
theorem batch_99_19_ok : batch_99_19_values.all id = true := by decide

def batch_99_20_values : List Bool := [accepted_4992]
theorem batch_99_20_ok : batch_99_20_values.all id = true := by decide

def batch_99_21_values : List Bool := [accepted_4997]
theorem batch_99_21_ok : batch_99_21_values.all id = true := by decide

def batch_99_22_values : List Bool := [accepted_4998]
theorem batch_99_22_ok : batch_99_22_values.all id = true := by decide

theorem leaf_4951_ok : checkAt 527 1000 box_4951 cert_4951 = true := by
  have h := List.all_eq_true.mp batch_99_00_ok accepted_4951 (by simp [batch_99_00_values])
  exact h
theorem leaf_4951_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4951.profileLo box_4951.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4951_ok
theorem branch_box_4951_nonnegative : ∀ j, 0 ≤ branch_box_4951.lower j ∧ 0 ≤ branch_box_4951.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4951, Box.profileLo, Box.profileHi, box_4951]
theorem leaf_4951_BranchSafe : CertificateConsequences.BranchSafe branch_box_4951 := by
  left; refine ⟨branch_box_4951_nonnegative, ?_⟩
  intro z hz; exact leaf_4951_sound hz

theorem leaf_4952_ok : checkAt 527 1000 box_4952 cert_4952 = true := by
  have h := List.all_eq_true.mp batch_99_01_ok accepted_4952 (by simp [batch_99_01_values])
  exact h
theorem leaf_4952_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4952.profileLo box_4952.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4952_ok
theorem branch_box_4952_nonnegative : ∀ j, 0 ≤ branch_box_4952.lower j ∧ 0 ≤ branch_box_4952.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4952, Box.profileLo, Box.profileHi, box_4952]
theorem leaf_4952_BranchSafe : CertificateConsequences.BranchSafe branch_box_4952 := by
  left; refine ⟨branch_box_4952_nonnegative, ?_⟩
  intro z hz; exact leaf_4952_sound hz

theorem leaf_4955_ok : checkAt 527 1000 box_4955 cert_4955 = true := by
  have h := List.all_eq_true.mp batch_99_02_ok accepted_4955 (by simp [batch_99_02_values])
  exact h
theorem leaf_4955_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4955.profileLo box_4955.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4955_ok
theorem branch_box_4955_nonnegative : ∀ j, 0 ≤ branch_box_4955.lower j ∧ 0 ≤ branch_box_4955.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4955, Box.profileLo, Box.profileHi, box_4955]
theorem leaf_4955_BranchSafe : CertificateConsequences.BranchSafe branch_box_4955 := by
  left; refine ⟨branch_box_4955_nonnegative, ?_⟩
  intro z hz; exact leaf_4955_sound hz

theorem leaf_4957_ok : checkAt 527 1000 box_4957 cert_4957 = true := by
  have h := List.all_eq_true.mp batch_99_03_ok accepted_4957 (by simp [batch_99_03_values])
  exact h
theorem leaf_4957_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4957.profileLo box_4957.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4957_ok
theorem branch_box_4957_nonnegative : ∀ j, 0 ≤ branch_box_4957.lower j ∧ 0 ≤ branch_box_4957.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4957, Box.profileLo, Box.profileHi, box_4957]
theorem leaf_4957_BranchSafe : CertificateConsequences.BranchSafe branch_box_4957 := by
  left; refine ⟨branch_box_4957_nonnegative, ?_⟩
  intro z hz; exact leaf_4957_sound hz

theorem leaf_4958_ok : checkAt 527 1000 box_4958 cert_4958 = true := by
  have h := List.all_eq_true.mp batch_99_04_ok accepted_4958 (by simp [batch_99_04_values])
  exact h
theorem leaf_4958_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4958.profileLo box_4958.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4958_ok
theorem branch_box_4958_nonnegative : ∀ j, 0 ≤ branch_box_4958.lower j ∧ 0 ≤ branch_box_4958.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4958, Box.profileLo, Box.profileHi, box_4958]
theorem leaf_4958_BranchSafe : CertificateConsequences.BranchSafe branch_box_4958 := by
  left; refine ⟨branch_box_4958_nonnegative, ?_⟩
  intro z hz; exact leaf_4958_sound hz

theorem leaf_4959_ok : checkAt 527 1000 box_4959 cert_4959 = true := by
  have h := List.all_eq_true.mp batch_99_05_ok accepted_4959 (by simp [batch_99_05_values])
  exact h
theorem leaf_4959_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4959.profileLo box_4959.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4959_ok
theorem branch_box_4959_nonnegative : ∀ j, 0 ≤ branch_box_4959.lower j ∧ 0 ≤ branch_box_4959.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4959, Box.profileLo, Box.profileHi, box_4959]
theorem leaf_4959_BranchSafe : CertificateConsequences.BranchSafe branch_box_4959 := by
  left; refine ⟨branch_box_4959_nonnegative, ?_⟩
  intro z hz; exact leaf_4959_sound hz

theorem leaf_4963_ok : checkAt 527 1000 box_4963 cert_4963 = true := by
  have h := List.all_eq_true.mp batch_99_06_ok accepted_4963 (by simp [batch_99_06_values])
  exact h
theorem leaf_4963_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4963.profileLo box_4963.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4963_ok
theorem branch_box_4963_nonnegative : ∀ j, 0 ≤ branch_box_4963.lower j ∧ 0 ≤ branch_box_4963.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4963, Box.profileLo, Box.profileHi, box_4963]
theorem leaf_4963_BranchSafe : CertificateConsequences.BranchSafe branch_box_4963 := by
  left; refine ⟨branch_box_4963_nonnegative, ?_⟩
  intro z hz; exact leaf_4963_sound hz

theorem leaf_4965_ok : checkAt 527 1000 box_4965 cert_4965 = true := by
  have h := List.all_eq_true.mp batch_99_07_ok accepted_4965 (by simp [batch_99_07_values])
  exact h
theorem leaf_4965_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4965.profileLo box_4965.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4965_ok
theorem branch_box_4965_nonnegative : ∀ j, 0 ≤ branch_box_4965.lower j ∧ 0 ≤ branch_box_4965.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4965, Box.profileLo, Box.profileHi, box_4965]
theorem leaf_4965_BranchSafe : CertificateConsequences.BranchSafe branch_box_4965 := by
  left; refine ⟨branch_box_4965_nonnegative, ?_⟩
  intro z hz; exact leaf_4965_sound hz

theorem leaf_4966_ok : checkAt 527 1000 box_4966 cert_4966 = true := by
  have h := List.all_eq_true.mp batch_99_08_ok accepted_4966 (by simp [batch_99_08_values])
  exact h
theorem leaf_4966_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4966.profileLo box_4966.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4966_ok
theorem branch_box_4966_nonnegative : ∀ j, 0 ≤ branch_box_4966.lower j ∧ 0 ≤ branch_box_4966.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4966, Box.profileLo, Box.profileHi, box_4966]
theorem leaf_4966_BranchSafe : CertificateConsequences.BranchSafe branch_box_4966 := by
  left; refine ⟨branch_box_4966_nonnegative, ?_⟩
  intro z hz; exact leaf_4966_sound hz

theorem leaf_4969_ok : checkAt 527 1000 box_4969 cert_4969 = true := by
  have h := List.all_eq_true.mp batch_99_09_ok accepted_4969 (by simp [batch_99_09_values])
  exact h
theorem leaf_4969_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4969.profileLo box_4969.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4969_ok
theorem branch_box_4969_nonnegative : ∀ j, 0 ≤ branch_box_4969.lower j ∧ 0 ≤ branch_box_4969.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4969, Box.profileLo, Box.profileHi, box_4969]
theorem leaf_4969_BranchSafe : CertificateConsequences.BranchSafe branch_box_4969 := by
  left; refine ⟨branch_box_4969_nonnegative, ?_⟩
  intro z hz; exact leaf_4969_sound hz

theorem leaf_4970_ok : checkAt 527 1000 box_4970 cert_4970 = true := by
  have h := List.all_eq_true.mp batch_99_10_ok accepted_4970 (by simp [batch_99_10_values])
  exact h
theorem leaf_4970_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4970.profileLo box_4970.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4970_ok
theorem branch_box_4970_nonnegative : ∀ j, 0 ≤ branch_box_4970.lower j ∧ 0 ≤ branch_box_4970.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4970, Box.profileLo, Box.profileHi, box_4970]
theorem leaf_4970_BranchSafe : CertificateConsequences.BranchSafe branch_box_4970 := by
  left; refine ⟨branch_box_4970_nonnegative, ?_⟩
  intro z hz; exact leaf_4970_sound hz

theorem leaf_4971_ok : checkAt 527 1000 box_4971 cert_4971 = true := by
  have h := List.all_eq_true.mp batch_99_11_ok accepted_4971 (by simp [batch_99_11_values])
  exact h
theorem leaf_4971_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4971.profileLo box_4971.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4971_ok
theorem branch_box_4971_nonnegative : ∀ j, 0 ≤ branch_box_4971.lower j ∧ 0 ≤ branch_box_4971.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4971, Box.profileLo, Box.profileHi, box_4971]
theorem leaf_4971_BranchSafe : CertificateConsequences.BranchSafe branch_box_4971 := by
  left; refine ⟨branch_box_4971_nonnegative, ?_⟩
  intro z hz; exact leaf_4971_sound hz

theorem leaf_4972_ok : checkAt 527 1000 box_4972 cert_4972 = true := by
  have h := List.all_eq_true.mp batch_99_12_ok accepted_4972 (by simp [batch_99_12_values])
  exact h
theorem leaf_4972_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4972.profileLo box_4972.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4972_ok
theorem branch_box_4972_nonnegative : ∀ j, 0 ≤ branch_box_4972.lower j ∧ 0 ≤ branch_box_4972.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4972, Box.profileLo, Box.profileHi, box_4972]
theorem leaf_4972_BranchSafe : CertificateConsequences.BranchSafe branch_box_4972 := by
  left; refine ⟨branch_box_4972_nonnegative, ?_⟩
  intro z hz; exact leaf_4972_sound hz

theorem leaf_4979_ok : checkAt 527 1000 box_4979 cert_4979 = true := by
  have h := List.all_eq_true.mp batch_99_13_ok accepted_4979 (by simp [batch_99_13_values])
  exact h
theorem leaf_4979_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4979.profileLo box_4979.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4979_ok
theorem branch_box_4979_nonnegative : ∀ j, 0 ≤ branch_box_4979.lower j ∧ 0 ≤ branch_box_4979.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4979, Box.profileLo, Box.profileHi, box_4979]
theorem leaf_4979_BranchSafe : CertificateConsequences.BranchSafe branch_box_4979 := by
  left; refine ⟨branch_box_4979_nonnegative, ?_⟩
  intro z hz; exact leaf_4979_sound hz

theorem leaf_4981_ok : checkAt 527 1000 box_4981 cert_4981 = true := by
  have h := List.all_eq_true.mp batch_99_14_ok accepted_4981 (by simp [batch_99_14_values])
  exact h
theorem leaf_4981_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4981.profileLo box_4981.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4981_ok
theorem branch_box_4981_nonnegative : ∀ j, 0 ≤ branch_box_4981.lower j ∧ 0 ≤ branch_box_4981.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4981, Box.profileLo, Box.profileHi, box_4981]
theorem leaf_4981_BranchSafe : CertificateConsequences.BranchSafe branch_box_4981 := by
  left; refine ⟨branch_box_4981_nonnegative, ?_⟩
  intro z hz; exact leaf_4981_sound hz

theorem leaf_4982_ok : checkAt 527 1000 box_4982 cert_4982 = true := by
  have h := List.all_eq_true.mp batch_99_15_ok accepted_4982 (by simp [batch_99_15_values])
  exact h
theorem leaf_4982_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4982.profileLo box_4982.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4982_ok
theorem branch_box_4982_nonnegative : ∀ j, 0 ≤ branch_box_4982.lower j ∧ 0 ≤ branch_box_4982.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4982, Box.profileLo, Box.profileHi, box_4982]
theorem leaf_4982_BranchSafe : CertificateConsequences.BranchSafe branch_box_4982 := by
  left; refine ⟨branch_box_4982_nonnegative, ?_⟩
  intro z hz; exact leaf_4982_sound hz

theorem leaf_4983_ok : checkAt 527 1000 box_4983 cert_4983 = true := by
  have h := List.all_eq_true.mp batch_99_16_ok accepted_4983 (by simp [batch_99_16_values])
  exact h
theorem leaf_4983_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4983.profileLo box_4983.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4983_ok
theorem branch_box_4983_nonnegative : ∀ j, 0 ≤ branch_box_4983.lower j ∧ 0 ≤ branch_box_4983.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4983, Box.profileLo, Box.profileHi, box_4983]
theorem leaf_4983_BranchSafe : CertificateConsequences.BranchSafe branch_box_4983 := by
  left; refine ⟨branch_box_4983_nonnegative, ?_⟩
  intro z hz; exact leaf_4983_sound hz

theorem leaf_4984_ok : checkAt 527 1000 box_4984 cert_4984 = true := by
  have h := List.all_eq_true.mp batch_99_17_ok accepted_4984 (by simp [batch_99_17_values])
  exact h
theorem leaf_4984_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4984.profileLo box_4984.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4984_ok
theorem branch_box_4984_nonnegative : ∀ j, 0 ≤ branch_box_4984.lower j ∧ 0 ≤ branch_box_4984.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4984, Box.profileLo, Box.profileHi, box_4984]
theorem leaf_4984_BranchSafe : CertificateConsequences.BranchSafe branch_box_4984 := by
  left; refine ⟨branch_box_4984_nonnegative, ?_⟩
  intro z hz; exact leaf_4984_sound hz

theorem leaf_4989_ok : checkAt 527 1000 box_4989 cert_4989 = true := by
  have h := List.all_eq_true.mp batch_99_18_ok accepted_4989 (by simp [batch_99_18_values])
  exact h
theorem leaf_4989_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4989.profileLo box_4989.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4989_ok
theorem branch_box_4989_nonnegative : ∀ j, 0 ≤ branch_box_4989.lower j ∧ 0 ≤ branch_box_4989.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4989, Box.profileLo, Box.profileHi, box_4989]
theorem leaf_4989_BranchSafe : CertificateConsequences.BranchSafe branch_box_4989 := by
  left; refine ⟨branch_box_4989_nonnegative, ?_⟩
  intro z hz; exact leaf_4989_sound hz

theorem leaf_4991_ok : checkAt 527 1000 box_4991 cert_4991 = true := by
  have h := List.all_eq_true.mp batch_99_19_ok accepted_4991 (by simp [batch_99_19_values])
  exact h
theorem leaf_4991_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4991.profileLo box_4991.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4991_ok
theorem branch_box_4991_nonnegative : ∀ j, 0 ≤ branch_box_4991.lower j ∧ 0 ≤ branch_box_4991.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4991, Box.profileLo, Box.profileHi, box_4991]
theorem leaf_4991_BranchSafe : CertificateConsequences.BranchSafe branch_box_4991 := by
  left; refine ⟨branch_box_4991_nonnegative, ?_⟩
  intro z hz; exact leaf_4991_sound hz

theorem leaf_4992_ok : checkAt 527 1000 box_4992 cert_4992 = true := by
  have h := List.all_eq_true.mp batch_99_20_ok accepted_4992 (by simp [batch_99_20_values])
  exact h
theorem leaf_4992_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4992.profileLo box_4992.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4992_ok
theorem branch_box_4992_nonnegative : ∀ j, 0 ≤ branch_box_4992.lower j ∧ 0 ≤ branch_box_4992.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4992, Box.profileLo, Box.profileHi, box_4992]
theorem leaf_4992_BranchSafe : CertificateConsequences.BranchSafe branch_box_4992 := by
  left; refine ⟨branch_box_4992_nonnegative, ?_⟩
  intro z hz; exact leaf_4992_sound hz

theorem leaf_4997_ok : checkAt 527 1000 box_4997 cert_4997 = true := by
  have h := List.all_eq_true.mp batch_99_21_ok accepted_4997 (by simp [batch_99_21_values])
  exact h
theorem leaf_4997_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4997.profileLo box_4997.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4997_ok
theorem branch_box_4997_nonnegative : ∀ j, 0 ≤ branch_box_4997.lower j ∧ 0 ≤ branch_box_4997.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4997, Box.profileLo, Box.profileHi, box_4997]
theorem leaf_4997_BranchSafe : CertificateConsequences.BranchSafe branch_box_4997 := by
  left; refine ⟨branch_box_4997_nonnegative, ?_⟩
  intro z hz; exact leaf_4997_sound hz

theorem leaf_4998_ok : checkAt 527 1000 box_4998 cert_4998 = true := by
  have h := List.all_eq_true.mp batch_99_22_ok accepted_4998 (by simp [batch_99_22_values])
  exact h
theorem leaf_4998_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4998.profileLo box_4998.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4998_ok
theorem branch_box_4998_nonnegative : ∀ j, 0 ≤ branch_box_4998.lower j ∧ 0 ≤ branch_box_4998.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4998, Box.profileLo, Box.profileHi, box_4998]
theorem leaf_4998_BranchSafe : CertificateConsequences.BranchSafe branch_box_4998 := by
  left; refine ⟨branch_box_4998_nonnegative, ?_⟩
  intro z hz; exact leaf_4998_sound hz

#print axioms batch_99_00_ok
#print axioms leaf_4951_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
