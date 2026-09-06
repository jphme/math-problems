import PeaceableQueens.UpperBound.Generated.Even.C527Scaled19Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_19_00_values : List Bool := [accepted_950]
theorem batch_19_00_ok : batch_19_00_values.all id = true := by decide

def batch_19_01_values : List Bool := [accepted_953]
theorem batch_19_01_ok : batch_19_01_values.all id = true := by decide

def batch_19_02_values : List Bool := [accepted_954]
theorem batch_19_02_ok : batch_19_02_values.all id = true := by decide

def batch_19_03_values : List Bool := [accepted_957]
theorem batch_19_03_ok : batch_19_03_values.all id = true := by decide

def batch_19_04_values : List Bool := [accepted_959]
theorem batch_19_04_ok : batch_19_04_values.all id = true := by decide

def batch_19_05_values : List Bool := [accepted_960]
theorem batch_19_05_ok : batch_19_05_values.all id = true := by decide

def batch_19_06_values : List Bool := [accepted_961]
theorem batch_19_06_ok : batch_19_06_values.all id = true := by decide

def batch_19_07_values : List Bool := [accepted_962]
theorem batch_19_07_ok : batch_19_07_values.all id = true := by decide

def batch_19_08_values : List Bool := [accepted_968]
theorem batch_19_08_ok : batch_19_08_values.all id = true := by decide

def batch_19_09_values : List Bool := [accepted_970]
theorem batch_19_09_ok : batch_19_09_values.all id = true := by decide

def batch_19_10_values : List Bool := [accepted_973]
theorem batch_19_10_ok : batch_19_10_values.all id = true := by decide

def batch_19_11_values : List Bool := [accepted_974]
theorem batch_19_11_ok : batch_19_11_values.all id = true := by decide

def batch_19_12_values : List Bool := [accepted_975]
theorem batch_19_12_ok : batch_19_12_values.all id = true := by decide

def batch_19_13_values : List Bool := [accepted_977]
theorem batch_19_13_ok : batch_19_13_values.all id = true := by decide

def batch_19_14_values : List Bool := [accepted_978]
theorem batch_19_14_ok : batch_19_14_values.all id = true := by decide

def batch_19_15_values : List Bool := [accepted_983]
theorem batch_19_15_ok : batch_19_15_values.all id = true := by decide

def batch_19_16_values : List Bool := [accepted_984]
theorem batch_19_16_ok : batch_19_16_values.all id = true := by decide

def batch_19_17_values : List Bool := [accepted_985]
theorem batch_19_17_ok : batch_19_17_values.all id = true := by decide

def batch_19_18_values : List Bool := [accepted_987]
theorem batch_19_18_ok : batch_19_18_values.all id = true := by decide

def batch_19_19_values : List Bool := [accepted_988]
theorem batch_19_19_ok : batch_19_19_values.all id = true := by decide

def batch_19_20_values : List Bool := [accepted_989]
theorem batch_19_20_ok : batch_19_20_values.all id = true := by decide

def batch_19_21_values : List Bool := [accepted_991]
theorem batch_19_21_ok : batch_19_21_values.all id = true := by decide

def batch_19_22_values : List Bool := [accepted_992]
theorem batch_19_22_ok : batch_19_22_values.all id = true := by decide

def batch_19_23_values : List Bool := [accepted_995]
theorem batch_19_23_ok : batch_19_23_values.all id = true := by decide

def batch_19_24_values : List Bool := [accepted_997]
theorem batch_19_24_ok : batch_19_24_values.all id = true := by decide

def batch_19_25_values : List Bool := [accepted_998]
theorem batch_19_25_ok : batch_19_25_values.all id = true := by decide

theorem leaf_950_ok : checkAt 527 1000 box_950 cert_950 = true := by
  have h := List.all_eq_true.mp batch_19_00_ok accepted_950 (by simp [batch_19_00_values])
  exact h
theorem leaf_950_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_950.profileLo box_950.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_950_ok
theorem branch_box_950_nonnegative : ∀ j, 0 ≤ branch_box_950.lower j ∧ 0 ≤ branch_box_950.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_950, Box.profileLo, Box.profileHi, box_950]
theorem leaf_950_BranchSafe : CertificateConsequences.BranchSafe branch_box_950 := by
  left; refine ⟨branch_box_950_nonnegative, ?_⟩
  intro z hz; exact leaf_950_sound hz

theorem leaf_953_ok : checkAt 527 1000 box_953 cert_953 = true := by
  have h := List.all_eq_true.mp batch_19_01_ok accepted_953 (by simp [batch_19_01_values])
  exact h
theorem leaf_953_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_953.profileLo box_953.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_953_ok
theorem branch_box_953_nonnegative : ∀ j, 0 ≤ branch_box_953.lower j ∧ 0 ≤ branch_box_953.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_953, Box.profileLo, Box.profileHi, box_953]
theorem leaf_953_BranchSafe : CertificateConsequences.BranchSafe branch_box_953 := by
  left; refine ⟨branch_box_953_nonnegative, ?_⟩
  intro z hz; exact leaf_953_sound hz

theorem leaf_954_ok : checkAt 527 1000 box_954 cert_954 = true := by
  have h := List.all_eq_true.mp batch_19_02_ok accepted_954 (by simp [batch_19_02_values])
  exact h
theorem leaf_954_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_954.profileLo box_954.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_954_ok
theorem branch_box_954_nonnegative : ∀ j, 0 ≤ branch_box_954.lower j ∧ 0 ≤ branch_box_954.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_954, Box.profileLo, Box.profileHi, box_954]
theorem leaf_954_BranchSafe : CertificateConsequences.BranchSafe branch_box_954 := by
  left; refine ⟨branch_box_954_nonnegative, ?_⟩
  intro z hz; exact leaf_954_sound hz

theorem leaf_957_ok : checkAt 527 1000 box_957 cert_957 = true := by
  have h := List.all_eq_true.mp batch_19_03_ok accepted_957 (by simp [batch_19_03_values])
  exact h
theorem leaf_957_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_957.profileLo box_957.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_957_ok
theorem branch_box_957_nonnegative : ∀ j, 0 ≤ branch_box_957.lower j ∧ 0 ≤ branch_box_957.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_957, Box.profileLo, Box.profileHi, box_957]
theorem leaf_957_BranchSafe : CertificateConsequences.BranchSafe branch_box_957 := by
  left; refine ⟨branch_box_957_nonnegative, ?_⟩
  intro z hz; exact leaf_957_sound hz

theorem leaf_959_ok : checkAt 527 1000 box_959 cert_959 = true := by
  have h := List.all_eq_true.mp batch_19_04_ok accepted_959 (by simp [batch_19_04_values])
  exact h
theorem leaf_959_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_959.profileLo box_959.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_959_ok
theorem branch_box_959_nonnegative : ∀ j, 0 ≤ branch_box_959.lower j ∧ 0 ≤ branch_box_959.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_959, Box.profileLo, Box.profileHi, box_959]
theorem leaf_959_BranchSafe : CertificateConsequences.BranchSafe branch_box_959 := by
  left; refine ⟨branch_box_959_nonnegative, ?_⟩
  intro z hz; exact leaf_959_sound hz

theorem leaf_960_ok : checkAt 527 1000 box_960 cert_960 = true := by
  have h := List.all_eq_true.mp batch_19_05_ok accepted_960 (by simp [batch_19_05_values])
  exact h
theorem leaf_960_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_960.profileLo box_960.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_960_ok
theorem branch_box_960_nonnegative : ∀ j, 0 ≤ branch_box_960.lower j ∧ 0 ≤ branch_box_960.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_960, Box.profileLo, Box.profileHi, box_960]
theorem leaf_960_BranchSafe : CertificateConsequences.BranchSafe branch_box_960 := by
  left; refine ⟨branch_box_960_nonnegative, ?_⟩
  intro z hz; exact leaf_960_sound hz

theorem leaf_961_ok : checkAt 527 1000 box_961 cert_961 = true := by
  have h := List.all_eq_true.mp batch_19_06_ok accepted_961 (by simp [batch_19_06_values])
  exact h
theorem leaf_961_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_961.profileLo box_961.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_961_ok
theorem branch_box_961_nonnegative : ∀ j, 0 ≤ branch_box_961.lower j ∧ 0 ≤ branch_box_961.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_961, Box.profileLo, Box.profileHi, box_961]
theorem leaf_961_BranchSafe : CertificateConsequences.BranchSafe branch_box_961 := by
  left; refine ⟨branch_box_961_nonnegative, ?_⟩
  intro z hz; exact leaf_961_sound hz

theorem leaf_962_ok : checkAt 527 1000 box_962 cert_962 = true := by
  have h := List.all_eq_true.mp batch_19_07_ok accepted_962 (by simp [batch_19_07_values])
  exact h
theorem leaf_962_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_962.profileLo box_962.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_962_ok
theorem branch_box_962_nonnegative : ∀ j, 0 ≤ branch_box_962.lower j ∧ 0 ≤ branch_box_962.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_962, Box.profileLo, Box.profileHi, box_962]
theorem leaf_962_BranchSafe : CertificateConsequences.BranchSafe branch_box_962 := by
  left; refine ⟨branch_box_962_nonnegative, ?_⟩
  intro z hz; exact leaf_962_sound hz

theorem leaf_968_ok : checkAt 527 1000 box_968 cert_968 = true := by
  have h := List.all_eq_true.mp batch_19_08_ok accepted_968 (by simp [batch_19_08_values])
  exact h
theorem leaf_968_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_968.profileLo box_968.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_968_ok
theorem branch_box_968_nonnegative : ∀ j, 0 ≤ branch_box_968.lower j ∧ 0 ≤ branch_box_968.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_968, Box.profileLo, Box.profileHi, box_968]
theorem leaf_968_BranchSafe : CertificateConsequences.BranchSafe branch_box_968 := by
  left; refine ⟨branch_box_968_nonnegative, ?_⟩
  intro z hz; exact leaf_968_sound hz

theorem leaf_970_ok : checkAt 527 1000 box_970 cert_970 = true := by
  have h := List.all_eq_true.mp batch_19_09_ok accepted_970 (by simp [batch_19_09_values])
  exact h
theorem leaf_970_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_970.profileLo box_970.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_970_ok
theorem branch_box_970_nonnegative : ∀ j, 0 ≤ branch_box_970.lower j ∧ 0 ≤ branch_box_970.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_970, Box.profileLo, Box.profileHi, box_970]
theorem leaf_970_BranchSafe : CertificateConsequences.BranchSafe branch_box_970 := by
  left; refine ⟨branch_box_970_nonnegative, ?_⟩
  intro z hz; exact leaf_970_sound hz

theorem leaf_973_ok : checkAt 527 1000 box_973 cert_973 = true := by
  have h := List.all_eq_true.mp batch_19_10_ok accepted_973 (by simp [batch_19_10_values])
  exact h
theorem leaf_973_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_973.profileLo box_973.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_973_ok
theorem branch_box_973_nonnegative : ∀ j, 0 ≤ branch_box_973.lower j ∧ 0 ≤ branch_box_973.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_973, Box.profileLo, Box.profileHi, box_973]
theorem leaf_973_BranchSafe : CertificateConsequences.BranchSafe branch_box_973 := by
  left; refine ⟨branch_box_973_nonnegative, ?_⟩
  intro z hz; exact leaf_973_sound hz

theorem leaf_974_ok : checkAt 527 1000 box_974 cert_974 = true := by
  have h := List.all_eq_true.mp batch_19_11_ok accepted_974 (by simp [batch_19_11_values])
  exact h
theorem leaf_974_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_974.profileLo box_974.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_974_ok
theorem branch_box_974_nonnegative : ∀ j, 0 ≤ branch_box_974.lower j ∧ 0 ≤ branch_box_974.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_974, Box.profileLo, Box.profileHi, box_974]
theorem leaf_974_BranchSafe : CertificateConsequences.BranchSafe branch_box_974 := by
  left; refine ⟨branch_box_974_nonnegative, ?_⟩
  intro z hz; exact leaf_974_sound hz

theorem leaf_975_ok : checkAt 527 1000 box_975 cert_975 = true := by
  have h := List.all_eq_true.mp batch_19_12_ok accepted_975 (by simp [batch_19_12_values])
  exact h
theorem leaf_975_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_975.profileLo box_975.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_975_ok
theorem branch_box_975_nonnegative : ∀ j, 0 ≤ branch_box_975.lower j ∧ 0 ≤ branch_box_975.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_975, Box.profileLo, Box.profileHi, box_975]
theorem leaf_975_BranchSafe : CertificateConsequences.BranchSafe branch_box_975 := by
  left; refine ⟨branch_box_975_nonnegative, ?_⟩
  intro z hz; exact leaf_975_sound hz

theorem leaf_977_ok : checkAt 527 1000 box_977 cert_977 = true := by
  have h := List.all_eq_true.mp batch_19_13_ok accepted_977 (by simp [batch_19_13_values])
  exact h
theorem leaf_977_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_977.profileLo box_977.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_977_ok
theorem branch_box_977_nonnegative : ∀ j, 0 ≤ branch_box_977.lower j ∧ 0 ≤ branch_box_977.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_977, Box.profileLo, Box.profileHi, box_977]
theorem leaf_977_BranchSafe : CertificateConsequences.BranchSafe branch_box_977 := by
  left; refine ⟨branch_box_977_nonnegative, ?_⟩
  intro z hz; exact leaf_977_sound hz

theorem leaf_978_ok : checkAt 527 1000 box_978 cert_978 = true := by
  have h := List.all_eq_true.mp batch_19_14_ok accepted_978 (by simp [batch_19_14_values])
  exact h
theorem leaf_978_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_978.profileLo box_978.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_978_ok
theorem branch_box_978_nonnegative : ∀ j, 0 ≤ branch_box_978.lower j ∧ 0 ≤ branch_box_978.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_978, Box.profileLo, Box.profileHi, box_978]
theorem leaf_978_BranchSafe : CertificateConsequences.BranchSafe branch_box_978 := by
  left; refine ⟨branch_box_978_nonnegative, ?_⟩
  intro z hz; exact leaf_978_sound hz

theorem leaf_983_ok : checkAt 527 1000 box_983 cert_983 = true := by
  have h := List.all_eq_true.mp batch_19_15_ok accepted_983 (by simp [batch_19_15_values])
  exact h
theorem leaf_983_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_983.profileLo box_983.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_983_ok
theorem branch_box_983_nonnegative : ∀ j, 0 ≤ branch_box_983.lower j ∧ 0 ≤ branch_box_983.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_983, Box.profileLo, Box.profileHi, box_983]
theorem leaf_983_BranchSafe : CertificateConsequences.BranchSafe branch_box_983 := by
  left; refine ⟨branch_box_983_nonnegative, ?_⟩
  intro z hz; exact leaf_983_sound hz

theorem leaf_984_ok : checkAt 527 1000 box_984 cert_984 = true := by
  have h := List.all_eq_true.mp batch_19_16_ok accepted_984 (by simp [batch_19_16_values])
  exact h
theorem leaf_984_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_984.profileLo box_984.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_984_ok
theorem branch_box_984_nonnegative : ∀ j, 0 ≤ branch_box_984.lower j ∧ 0 ≤ branch_box_984.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_984, Box.profileLo, Box.profileHi, box_984]
theorem leaf_984_BranchSafe : CertificateConsequences.BranchSafe branch_box_984 := by
  left; refine ⟨branch_box_984_nonnegative, ?_⟩
  intro z hz; exact leaf_984_sound hz

theorem leaf_985_ok : checkAt 527 1000 box_985 cert_985 = true := by
  have h := List.all_eq_true.mp batch_19_17_ok accepted_985 (by simp [batch_19_17_values])
  exact h
theorem leaf_985_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_985.profileLo box_985.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_985_ok
theorem branch_box_985_nonnegative : ∀ j, 0 ≤ branch_box_985.lower j ∧ 0 ≤ branch_box_985.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_985, Box.profileLo, Box.profileHi, box_985]
theorem leaf_985_BranchSafe : CertificateConsequences.BranchSafe branch_box_985 := by
  left; refine ⟨branch_box_985_nonnegative, ?_⟩
  intro z hz; exact leaf_985_sound hz

theorem leaf_987_ok : checkAt 527 1000 box_987 cert_987 = true := by
  have h := List.all_eq_true.mp batch_19_18_ok accepted_987 (by simp [batch_19_18_values])
  exact h
theorem leaf_987_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_987.profileLo box_987.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_987_ok
theorem branch_box_987_nonnegative : ∀ j, 0 ≤ branch_box_987.lower j ∧ 0 ≤ branch_box_987.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_987, Box.profileLo, Box.profileHi, box_987]
theorem leaf_987_BranchSafe : CertificateConsequences.BranchSafe branch_box_987 := by
  left; refine ⟨branch_box_987_nonnegative, ?_⟩
  intro z hz; exact leaf_987_sound hz

theorem leaf_988_ok : checkAt 527 1000 box_988 cert_988 = true := by
  have h := List.all_eq_true.mp batch_19_19_ok accepted_988 (by simp [batch_19_19_values])
  exact h
theorem leaf_988_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_988.profileLo box_988.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_988_ok
theorem branch_box_988_nonnegative : ∀ j, 0 ≤ branch_box_988.lower j ∧ 0 ≤ branch_box_988.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_988, Box.profileLo, Box.profileHi, box_988]
theorem leaf_988_BranchSafe : CertificateConsequences.BranchSafe branch_box_988 := by
  left; refine ⟨branch_box_988_nonnegative, ?_⟩
  intro z hz; exact leaf_988_sound hz

theorem leaf_989_ok : checkAt 527 1000 box_989 cert_989 = true := by
  have h := List.all_eq_true.mp batch_19_20_ok accepted_989 (by simp [batch_19_20_values])
  exact h
theorem leaf_989_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_989.profileLo box_989.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_989_ok
theorem branch_box_989_nonnegative : ∀ j, 0 ≤ branch_box_989.lower j ∧ 0 ≤ branch_box_989.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_989, Box.profileLo, Box.profileHi, box_989]
theorem leaf_989_BranchSafe : CertificateConsequences.BranchSafe branch_box_989 := by
  left; refine ⟨branch_box_989_nonnegative, ?_⟩
  intro z hz; exact leaf_989_sound hz

theorem leaf_991_ok : checkAt 527 1000 box_991 cert_991 = true := by
  have h := List.all_eq_true.mp batch_19_21_ok accepted_991 (by simp [batch_19_21_values])
  exact h
theorem leaf_991_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_991.profileLo box_991.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_991_ok
theorem branch_box_991_nonnegative : ∀ j, 0 ≤ branch_box_991.lower j ∧ 0 ≤ branch_box_991.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_991, Box.profileLo, Box.profileHi, box_991]
theorem leaf_991_BranchSafe : CertificateConsequences.BranchSafe branch_box_991 := by
  left; refine ⟨branch_box_991_nonnegative, ?_⟩
  intro z hz; exact leaf_991_sound hz

theorem leaf_992_ok : checkAt 527 1000 box_992 cert_992 = true := by
  have h := List.all_eq_true.mp batch_19_22_ok accepted_992 (by simp [batch_19_22_values])
  exact h
theorem leaf_992_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_992.profileLo box_992.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_992_ok
theorem branch_box_992_nonnegative : ∀ j, 0 ≤ branch_box_992.lower j ∧ 0 ≤ branch_box_992.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_992, Box.profileLo, Box.profileHi, box_992]
theorem leaf_992_BranchSafe : CertificateConsequences.BranchSafe branch_box_992 := by
  left; refine ⟨branch_box_992_nonnegative, ?_⟩
  intro z hz; exact leaf_992_sound hz

theorem leaf_995_ok : checkAt 527 1000 box_995 cert_995 = true := by
  have h := List.all_eq_true.mp batch_19_23_ok accepted_995 (by simp [batch_19_23_values])
  exact h
theorem leaf_995_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_995.profileLo box_995.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_995_ok
theorem branch_box_995_nonnegative : ∀ j, 0 ≤ branch_box_995.lower j ∧ 0 ≤ branch_box_995.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_995, Box.profileLo, Box.profileHi, box_995]
theorem leaf_995_BranchSafe : CertificateConsequences.BranchSafe branch_box_995 := by
  left; refine ⟨branch_box_995_nonnegative, ?_⟩
  intro z hz; exact leaf_995_sound hz

theorem leaf_997_ok : checkAt 527 1000 box_997 cert_997 = true := by
  have h := List.all_eq_true.mp batch_19_24_ok accepted_997 (by simp [batch_19_24_values])
  exact h
theorem leaf_997_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_997.profileLo box_997.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_997_ok
theorem branch_box_997_nonnegative : ∀ j, 0 ≤ branch_box_997.lower j ∧ 0 ≤ branch_box_997.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_997, Box.profileLo, Box.profileHi, box_997]
theorem leaf_997_BranchSafe : CertificateConsequences.BranchSafe branch_box_997 := by
  left; refine ⟨branch_box_997_nonnegative, ?_⟩
  intro z hz; exact leaf_997_sound hz

theorem leaf_998_ok : checkAt 527 1000 box_998 cert_998 = true := by
  have h := List.all_eq_true.mp batch_19_25_ok accepted_998 (by simp [batch_19_25_values])
  exact h
theorem leaf_998_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_998.profileLo box_998.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_998_ok
theorem branch_box_998_nonnegative : ∀ j, 0 ≤ branch_box_998.lower j ∧ 0 ≤ branch_box_998.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_998, Box.profileLo, Box.profileHi, box_998]
theorem leaf_998_BranchSafe : CertificateConsequences.BranchSafe branch_box_998 := by
  left; refine ⟨branch_box_998_nonnegative, ?_⟩
  intro z hz; exact leaf_998_sound hz

#print axioms batch_19_00_ok
#print axioms leaf_950_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
