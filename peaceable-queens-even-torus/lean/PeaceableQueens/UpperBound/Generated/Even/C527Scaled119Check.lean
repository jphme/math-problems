import PeaceableQueens.UpperBound.Generated.Even.C527Scaled119Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_119_00_values : List Bool := [accepted_5950]
theorem batch_119_00_ok : batch_119_00_values.all id = true := by decide

def batch_119_01_values : List Bool := [accepted_5951]
theorem batch_119_01_ok : batch_119_01_values.all id = true := by decide

def batch_119_02_values : List Bool := [accepted_5952]
theorem batch_119_02_ok : batch_119_02_values.all id = true := by decide

def batch_119_03_values : List Bool := [accepted_5953]
theorem batch_119_03_ok : batch_119_03_values.all id = true := by decide

def batch_119_04_values : List Bool := [accepted_5954]
theorem batch_119_04_ok : batch_119_04_values.all id = true := by decide

def batch_119_05_values : List Bool := [accepted_5959]
theorem batch_119_05_ok : batch_119_05_values.all id = true := by decide

def batch_119_06_values : List Bool := [accepted_5960]
theorem batch_119_06_ok : batch_119_06_values.all id = true := by decide

def batch_119_07_values : List Bool := [accepted_5961]
theorem batch_119_07_ok : batch_119_07_values.all id = true := by decide

def batch_119_08_values : List Bool := [accepted_5963]
theorem batch_119_08_ok : batch_119_08_values.all id = true := by decide

def batch_119_09_values : List Bool := [accepted_5964]
theorem batch_119_09_ok : batch_119_09_values.all id = true := by decide

def batch_119_10_values : List Bool := [accepted_5967]
theorem batch_119_10_ok : batch_119_10_values.all id = true := by decide

def batch_119_11_values : List Bool := [accepted_5968]
theorem batch_119_11_ok : batch_119_11_values.all id = true := by decide

def batch_119_12_values : List Bool := [accepted_5971]
theorem batch_119_12_ok : batch_119_12_values.all id = true := by decide

def batch_119_13_values : List Bool := [accepted_5972]
theorem batch_119_13_ok : batch_119_13_values.all id = true := by decide

def batch_119_14_values : List Bool := [accepted_5973]
theorem batch_119_14_ok : batch_119_14_values.all id = true := by decide

def batch_119_15_values : List Bool := [accepted_5975]
theorem batch_119_15_ok : batch_119_15_values.all id = true := by decide

def batch_119_16_values : List Bool := [accepted_5977]
theorem batch_119_16_ok : batch_119_16_values.all id = true := by decide

def batch_119_17_values : List Bool := [accepted_5978]
theorem batch_119_17_ok : batch_119_17_values.all id = true := by decide

def batch_119_18_values : List Bool := [accepted_5985]
theorem batch_119_18_ok : batch_119_18_values.all id = true := by decide

def batch_119_19_values : List Bool := [accepted_5986]
theorem batch_119_19_ok : batch_119_19_values.all id = true := by decide

def batch_119_20_values : List Bool := [accepted_5989]
theorem batch_119_20_ok : batch_119_20_values.all id = true := by decide

def batch_119_21_values : List Bool := [accepted_5990]
theorem batch_119_21_ok : batch_119_21_values.all id = true := by decide

def batch_119_22_values : List Bool := [accepted_5992]
theorem batch_119_22_ok : batch_119_22_values.all id = true := by decide

def batch_119_23_values : List Bool := [accepted_5993]
theorem batch_119_23_ok : batch_119_23_values.all id = true := by decide

def batch_119_24_values : List Bool := [accepted_5994]
theorem batch_119_24_ok : batch_119_24_values.all id = true := by decide

def batch_119_25_values : List Bool := [accepted_5997]
theorem batch_119_25_ok : batch_119_25_values.all id = true := by decide

def batch_119_26_values : List Bool := [accepted_5998]
theorem batch_119_26_ok : batch_119_26_values.all id = true := by decide

theorem leaf_5950_ok : checkAt 527 1000 box_5950 cert_5950 = true := by
  have h := List.all_eq_true.mp batch_119_00_ok accepted_5950 (by simp [batch_119_00_values])
  exact h
theorem leaf_5950_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5950.profileLo box_5950.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5950_ok
theorem branch_box_5950_nonnegative : ∀ j, 0 ≤ branch_box_5950.lower j ∧ 0 ≤ branch_box_5950.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5950, Box.profileLo, Box.profileHi, box_5950]
theorem leaf_5950_BranchSafe : CertificateConsequences.BranchSafe branch_box_5950 := by
  left; refine ⟨branch_box_5950_nonnegative, ?_⟩
  intro z hz; exact leaf_5950_sound hz

theorem leaf_5951_ok : checkAt 527 1000 box_5951 cert_5951 = true := by
  have h := List.all_eq_true.mp batch_119_01_ok accepted_5951 (by simp [batch_119_01_values])
  exact h
theorem leaf_5951_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5951.profileLo box_5951.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5951_ok
theorem branch_box_5951_nonnegative : ∀ j, 0 ≤ branch_box_5951.lower j ∧ 0 ≤ branch_box_5951.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5951, Box.profileLo, Box.profileHi, box_5951]
theorem leaf_5951_BranchSafe : CertificateConsequences.BranchSafe branch_box_5951 := by
  left; refine ⟨branch_box_5951_nonnegative, ?_⟩
  intro z hz; exact leaf_5951_sound hz

theorem leaf_5952_ok : checkAt 527 1000 box_5952 cert_5952 = true := by
  have h := List.all_eq_true.mp batch_119_02_ok accepted_5952 (by simp [batch_119_02_values])
  exact h
theorem leaf_5952_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5952.profileLo box_5952.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5952_ok
theorem branch_box_5952_nonnegative : ∀ j, 0 ≤ branch_box_5952.lower j ∧ 0 ≤ branch_box_5952.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5952, Box.profileLo, Box.profileHi, box_5952]
theorem leaf_5952_BranchSafe : CertificateConsequences.BranchSafe branch_box_5952 := by
  left; refine ⟨branch_box_5952_nonnegative, ?_⟩
  intro z hz; exact leaf_5952_sound hz

theorem leaf_5953_ok : checkAt 527 1000 box_5953 cert_5953 = true := by
  have h := List.all_eq_true.mp batch_119_03_ok accepted_5953 (by simp [batch_119_03_values])
  exact h
theorem leaf_5953_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5953.profileLo box_5953.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5953_ok
theorem branch_box_5953_nonnegative : ∀ j, 0 ≤ branch_box_5953.lower j ∧ 0 ≤ branch_box_5953.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5953, Box.profileLo, Box.profileHi, box_5953]
theorem leaf_5953_BranchSafe : CertificateConsequences.BranchSafe branch_box_5953 := by
  left; refine ⟨branch_box_5953_nonnegative, ?_⟩
  intro z hz; exact leaf_5953_sound hz

theorem leaf_5954_ok : checkAt 527 1000 box_5954 cert_5954 = true := by
  have h := List.all_eq_true.mp batch_119_04_ok accepted_5954 (by simp [batch_119_04_values])
  exact h
theorem leaf_5954_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5954.profileLo box_5954.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5954_ok
theorem branch_box_5954_nonnegative : ∀ j, 0 ≤ branch_box_5954.lower j ∧ 0 ≤ branch_box_5954.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5954, Box.profileLo, Box.profileHi, box_5954]
theorem leaf_5954_BranchSafe : CertificateConsequences.BranchSafe branch_box_5954 := by
  left; refine ⟨branch_box_5954_nonnegative, ?_⟩
  intro z hz; exact leaf_5954_sound hz

theorem leaf_5959_ok : checkAt 527 1000 box_5959 cert_5959 = true := by
  have h := List.all_eq_true.mp batch_119_05_ok accepted_5959 (by simp [batch_119_05_values])
  exact h
theorem leaf_5959_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5959.profileLo box_5959.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5959_ok
theorem branch_box_5959_nonnegative : ∀ j, 0 ≤ branch_box_5959.lower j ∧ 0 ≤ branch_box_5959.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5959, Box.profileLo, Box.profileHi, box_5959]
theorem leaf_5959_BranchSafe : CertificateConsequences.BranchSafe branch_box_5959 := by
  left; refine ⟨branch_box_5959_nonnegative, ?_⟩
  intro z hz; exact leaf_5959_sound hz

theorem leaf_5960_ok : checkAt 527 1000 box_5960 cert_5960 = true := by
  have h := List.all_eq_true.mp batch_119_06_ok accepted_5960 (by simp [batch_119_06_values])
  exact h
theorem leaf_5960_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5960.profileLo box_5960.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5960_ok
theorem branch_box_5960_nonnegative : ∀ j, 0 ≤ branch_box_5960.lower j ∧ 0 ≤ branch_box_5960.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5960, Box.profileLo, Box.profileHi, box_5960]
theorem leaf_5960_BranchSafe : CertificateConsequences.BranchSafe branch_box_5960 := by
  left; refine ⟨branch_box_5960_nonnegative, ?_⟩
  intro z hz; exact leaf_5960_sound hz

theorem leaf_5961_ok : checkAt 527 1000 box_5961 cert_5961 = true := by
  have h := List.all_eq_true.mp batch_119_07_ok accepted_5961 (by simp [batch_119_07_values])
  exact h
theorem leaf_5961_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5961.profileLo box_5961.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5961_ok
theorem branch_box_5961_nonnegative : ∀ j, 0 ≤ branch_box_5961.lower j ∧ 0 ≤ branch_box_5961.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5961, Box.profileLo, Box.profileHi, box_5961]
theorem leaf_5961_BranchSafe : CertificateConsequences.BranchSafe branch_box_5961 := by
  left; refine ⟨branch_box_5961_nonnegative, ?_⟩
  intro z hz; exact leaf_5961_sound hz

theorem leaf_5963_ok : checkAt 527 1000 box_5963 cert_5963 = true := by
  have h := List.all_eq_true.mp batch_119_08_ok accepted_5963 (by simp [batch_119_08_values])
  exact h
theorem leaf_5963_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5963.profileLo box_5963.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5963_ok
theorem branch_box_5963_nonnegative : ∀ j, 0 ≤ branch_box_5963.lower j ∧ 0 ≤ branch_box_5963.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5963, Box.profileLo, Box.profileHi, box_5963]
theorem leaf_5963_BranchSafe : CertificateConsequences.BranchSafe branch_box_5963 := by
  left; refine ⟨branch_box_5963_nonnegative, ?_⟩
  intro z hz; exact leaf_5963_sound hz

theorem leaf_5964_ok : checkAt 527 1000 box_5964 cert_5964 = true := by
  have h := List.all_eq_true.mp batch_119_09_ok accepted_5964 (by simp [batch_119_09_values])
  exact h
theorem leaf_5964_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5964.profileLo box_5964.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5964_ok
theorem branch_box_5964_nonnegative : ∀ j, 0 ≤ branch_box_5964.lower j ∧ 0 ≤ branch_box_5964.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5964, Box.profileLo, Box.profileHi, box_5964]
theorem leaf_5964_BranchSafe : CertificateConsequences.BranchSafe branch_box_5964 := by
  left; refine ⟨branch_box_5964_nonnegative, ?_⟩
  intro z hz; exact leaf_5964_sound hz

theorem leaf_5967_ok : checkAt 527 1000 box_5967 cert_5967 = true := by
  have h := List.all_eq_true.mp batch_119_10_ok accepted_5967 (by simp [batch_119_10_values])
  exact h
theorem leaf_5967_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5967.profileLo box_5967.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5967_ok
theorem branch_box_5967_nonnegative : ∀ j, 0 ≤ branch_box_5967.lower j ∧ 0 ≤ branch_box_5967.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5967, Box.profileLo, Box.profileHi, box_5967]
theorem leaf_5967_BranchSafe : CertificateConsequences.BranchSafe branch_box_5967 := by
  left; refine ⟨branch_box_5967_nonnegative, ?_⟩
  intro z hz; exact leaf_5967_sound hz

theorem leaf_5968_ok : checkAt 527 1000 box_5968 cert_5968 = true := by
  have h := List.all_eq_true.mp batch_119_11_ok accepted_5968 (by simp [batch_119_11_values])
  exact h
theorem leaf_5968_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5968.profileLo box_5968.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5968_ok
theorem branch_box_5968_nonnegative : ∀ j, 0 ≤ branch_box_5968.lower j ∧ 0 ≤ branch_box_5968.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5968, Box.profileLo, Box.profileHi, box_5968]
theorem leaf_5968_BranchSafe : CertificateConsequences.BranchSafe branch_box_5968 := by
  left; refine ⟨branch_box_5968_nonnegative, ?_⟩
  intro z hz; exact leaf_5968_sound hz

theorem leaf_5971_ok : checkAt 527 1000 box_5971 cert_5971 = true := by
  have h := List.all_eq_true.mp batch_119_12_ok accepted_5971 (by simp [batch_119_12_values])
  exact h
theorem leaf_5971_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5971.profileLo box_5971.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5971_ok
theorem branch_box_5971_nonnegative : ∀ j, 0 ≤ branch_box_5971.lower j ∧ 0 ≤ branch_box_5971.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5971, Box.profileLo, Box.profileHi, box_5971]
theorem leaf_5971_BranchSafe : CertificateConsequences.BranchSafe branch_box_5971 := by
  left; refine ⟨branch_box_5971_nonnegative, ?_⟩
  intro z hz; exact leaf_5971_sound hz

theorem leaf_5972_ok : checkAt 527 1000 box_5972 cert_5972 = true := by
  have h := List.all_eq_true.mp batch_119_13_ok accepted_5972 (by simp [batch_119_13_values])
  exact h
theorem leaf_5972_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5972.profileLo box_5972.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5972_ok
theorem branch_box_5972_nonnegative : ∀ j, 0 ≤ branch_box_5972.lower j ∧ 0 ≤ branch_box_5972.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5972, Box.profileLo, Box.profileHi, box_5972]
theorem leaf_5972_BranchSafe : CertificateConsequences.BranchSafe branch_box_5972 := by
  left; refine ⟨branch_box_5972_nonnegative, ?_⟩
  intro z hz; exact leaf_5972_sound hz

theorem leaf_5973_ok : checkAt 527 1000 box_5973 cert_5973 = true := by
  have h := List.all_eq_true.mp batch_119_14_ok accepted_5973 (by simp [batch_119_14_values])
  exact h
theorem leaf_5973_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5973.profileLo box_5973.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5973_ok
theorem branch_box_5973_nonnegative : ∀ j, 0 ≤ branch_box_5973.lower j ∧ 0 ≤ branch_box_5973.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5973, Box.profileLo, Box.profileHi, box_5973]
theorem leaf_5973_BranchSafe : CertificateConsequences.BranchSafe branch_box_5973 := by
  left; refine ⟨branch_box_5973_nonnegative, ?_⟩
  intro z hz; exact leaf_5973_sound hz

theorem leaf_5975_ok : checkAt 527 1000 box_5975 cert_5975 = true := by
  have h := List.all_eq_true.mp batch_119_15_ok accepted_5975 (by simp [batch_119_15_values])
  exact h
theorem leaf_5975_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5975.profileLo box_5975.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5975_ok
theorem branch_box_5975_nonnegative : ∀ j, 0 ≤ branch_box_5975.lower j ∧ 0 ≤ branch_box_5975.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5975, Box.profileLo, Box.profileHi, box_5975]
theorem leaf_5975_BranchSafe : CertificateConsequences.BranchSafe branch_box_5975 := by
  left; refine ⟨branch_box_5975_nonnegative, ?_⟩
  intro z hz; exact leaf_5975_sound hz

theorem leaf_5977_ok : checkAt 527 1000 box_5977 cert_5977 = true := by
  have h := List.all_eq_true.mp batch_119_16_ok accepted_5977 (by simp [batch_119_16_values])
  exact h
theorem leaf_5977_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5977.profileLo box_5977.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5977_ok
theorem branch_box_5977_nonnegative : ∀ j, 0 ≤ branch_box_5977.lower j ∧ 0 ≤ branch_box_5977.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5977, Box.profileLo, Box.profileHi, box_5977]
theorem leaf_5977_BranchSafe : CertificateConsequences.BranchSafe branch_box_5977 := by
  left; refine ⟨branch_box_5977_nonnegative, ?_⟩
  intro z hz; exact leaf_5977_sound hz

theorem leaf_5978_ok : checkAt 527 1000 box_5978 cert_5978 = true := by
  have h := List.all_eq_true.mp batch_119_17_ok accepted_5978 (by simp [batch_119_17_values])
  exact h
theorem leaf_5978_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5978.profileLo box_5978.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5978_ok
theorem branch_box_5978_nonnegative : ∀ j, 0 ≤ branch_box_5978.lower j ∧ 0 ≤ branch_box_5978.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5978, Box.profileLo, Box.profileHi, box_5978]
theorem leaf_5978_BranchSafe : CertificateConsequences.BranchSafe branch_box_5978 := by
  left; refine ⟨branch_box_5978_nonnegative, ?_⟩
  intro z hz; exact leaf_5978_sound hz

theorem leaf_5985_ok : checkAt 527 1000 box_5985 cert_5985 = true := by
  have h := List.all_eq_true.mp batch_119_18_ok accepted_5985 (by simp [batch_119_18_values])
  exact h
theorem leaf_5985_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5985.profileLo box_5985.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5985_ok
theorem branch_box_5985_nonnegative : ∀ j, 0 ≤ branch_box_5985.lower j ∧ 0 ≤ branch_box_5985.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5985, Box.profileLo, Box.profileHi, box_5985]
theorem leaf_5985_BranchSafe : CertificateConsequences.BranchSafe branch_box_5985 := by
  left; refine ⟨branch_box_5985_nonnegative, ?_⟩
  intro z hz; exact leaf_5985_sound hz

theorem leaf_5986_ok : checkAt 527 1000 box_5986 cert_5986 = true := by
  have h := List.all_eq_true.mp batch_119_19_ok accepted_5986 (by simp [batch_119_19_values])
  exact h
theorem leaf_5986_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5986.profileLo box_5986.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5986_ok
theorem branch_box_5986_nonnegative : ∀ j, 0 ≤ branch_box_5986.lower j ∧ 0 ≤ branch_box_5986.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5986, Box.profileLo, Box.profileHi, box_5986]
theorem leaf_5986_BranchSafe : CertificateConsequences.BranchSafe branch_box_5986 := by
  left; refine ⟨branch_box_5986_nonnegative, ?_⟩
  intro z hz; exact leaf_5986_sound hz

theorem leaf_5989_ok : checkAt 527 1000 box_5989 cert_5989 = true := by
  have h := List.all_eq_true.mp batch_119_20_ok accepted_5989 (by simp [batch_119_20_values])
  exact h
theorem leaf_5989_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5989.profileLo box_5989.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5989_ok
theorem branch_box_5989_nonnegative : ∀ j, 0 ≤ branch_box_5989.lower j ∧ 0 ≤ branch_box_5989.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5989, Box.profileLo, Box.profileHi, box_5989]
theorem leaf_5989_BranchSafe : CertificateConsequences.BranchSafe branch_box_5989 := by
  left; refine ⟨branch_box_5989_nonnegative, ?_⟩
  intro z hz; exact leaf_5989_sound hz

theorem leaf_5990_ok : checkAt 527 1000 box_5990 cert_5990 = true := by
  have h := List.all_eq_true.mp batch_119_21_ok accepted_5990 (by simp [batch_119_21_values])
  exact h
theorem leaf_5990_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5990.profileLo box_5990.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5990_ok
theorem branch_box_5990_nonnegative : ∀ j, 0 ≤ branch_box_5990.lower j ∧ 0 ≤ branch_box_5990.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5990, Box.profileLo, Box.profileHi, box_5990]
theorem leaf_5990_BranchSafe : CertificateConsequences.BranchSafe branch_box_5990 := by
  left; refine ⟨branch_box_5990_nonnegative, ?_⟩
  intro z hz; exact leaf_5990_sound hz

theorem leaf_5992_ok : checkAt 527 1000 box_5992 cert_5992 = true := by
  have h := List.all_eq_true.mp batch_119_22_ok accepted_5992 (by simp [batch_119_22_values])
  exact h
theorem leaf_5992_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5992.profileLo box_5992.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5992_ok
theorem branch_box_5992_nonnegative : ∀ j, 0 ≤ branch_box_5992.lower j ∧ 0 ≤ branch_box_5992.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5992, Box.profileLo, Box.profileHi, box_5992]
theorem leaf_5992_BranchSafe : CertificateConsequences.BranchSafe branch_box_5992 := by
  left; refine ⟨branch_box_5992_nonnegative, ?_⟩
  intro z hz; exact leaf_5992_sound hz

theorem leaf_5993_ok : checkAt 527 1000 box_5993 cert_5993 = true := by
  have h := List.all_eq_true.mp batch_119_23_ok accepted_5993 (by simp [batch_119_23_values])
  exact h
theorem leaf_5993_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5993.profileLo box_5993.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5993_ok
theorem branch_box_5993_nonnegative : ∀ j, 0 ≤ branch_box_5993.lower j ∧ 0 ≤ branch_box_5993.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5993, Box.profileLo, Box.profileHi, box_5993]
theorem leaf_5993_BranchSafe : CertificateConsequences.BranchSafe branch_box_5993 := by
  left; refine ⟨branch_box_5993_nonnegative, ?_⟩
  intro z hz; exact leaf_5993_sound hz

theorem leaf_5994_ok : checkAt 527 1000 box_5994 cert_5994 = true := by
  have h := List.all_eq_true.mp batch_119_24_ok accepted_5994 (by simp [batch_119_24_values])
  exact h
theorem leaf_5994_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5994.profileLo box_5994.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5994_ok
theorem branch_box_5994_nonnegative : ∀ j, 0 ≤ branch_box_5994.lower j ∧ 0 ≤ branch_box_5994.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5994, Box.profileLo, Box.profileHi, box_5994]
theorem leaf_5994_BranchSafe : CertificateConsequences.BranchSafe branch_box_5994 := by
  left; refine ⟨branch_box_5994_nonnegative, ?_⟩
  intro z hz; exact leaf_5994_sound hz

theorem leaf_5997_ok : checkAt 527 1000 box_5997 cert_5997 = true := by
  have h := List.all_eq_true.mp batch_119_25_ok accepted_5997 (by simp [batch_119_25_values])
  exact h
theorem leaf_5997_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5997.profileLo box_5997.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5997_ok
theorem branch_box_5997_nonnegative : ∀ j, 0 ≤ branch_box_5997.lower j ∧ 0 ≤ branch_box_5997.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5997, Box.profileLo, Box.profileHi, box_5997]
theorem leaf_5997_BranchSafe : CertificateConsequences.BranchSafe branch_box_5997 := by
  left; refine ⟨branch_box_5997_nonnegative, ?_⟩
  intro z hz; exact leaf_5997_sound hz

theorem leaf_5998_ok : checkAt 527 1000 box_5998 cert_5998 = true := by
  have h := List.all_eq_true.mp batch_119_26_ok accepted_5998 (by simp [batch_119_26_values])
  exact h
theorem leaf_5998_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5998.profileLo box_5998.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5998_ok
theorem branch_box_5998_nonnegative : ∀ j, 0 ≤ branch_box_5998.lower j ∧ 0 ≤ branch_box_5998.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5998, Box.profileLo, Box.profileHi, box_5998]
theorem leaf_5998_BranchSafe : CertificateConsequences.BranchSafe branch_box_5998 := by
  left; refine ⟨branch_box_5998_nonnegative, ?_⟩
  intro z hz; exact leaf_5998_sound hz

#print axioms batch_119_00_ok
#print axioms leaf_5950_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
