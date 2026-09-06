import PeaceableQueens.UpperBound.Generated.Even.CoreScaled19Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_19_00_values : List Bool := [accepted_950]
theorem batch_19_00_ok : batch_19_00_values.all id = true := by decide

def batch_19_01_values : List Bool := [accepted_954]
theorem batch_19_01_ok : batch_19_01_values.all id = true := by decide

def batch_19_02_values : List Bool := [accepted_956]
theorem batch_19_02_ok : batch_19_02_values.all id = true := by decide

def batch_19_03_values : List Bool := [accepted_957]
theorem batch_19_03_ok : batch_19_03_values.all id = true := by decide

def batch_19_04_values : List Bool := [accepted_959]
theorem batch_19_04_ok : batch_19_04_values.all id = true := by decide

def batch_19_05_values : List Bool := [accepted_961]
theorem batch_19_05_ok : batch_19_05_values.all id = true := by decide

def batch_19_06_values : List Bool := [accepted_966]
theorem batch_19_06_ok : batch_19_06_values.all id = true := by decide

def batch_19_07_values : List Bool := [accepted_967]
theorem batch_19_07_ok : batch_19_07_values.all id = true := by decide

def batch_19_08_values : List Bool := [accepted_969]
theorem batch_19_08_ok : batch_19_08_values.all id = true := by decide

def batch_19_09_values : List Bool := [accepted_971]
theorem batch_19_09_ok : batch_19_09_values.all id = true := by decide

def batch_19_10_values : List Bool := [accepted_974]
theorem batch_19_10_ok : batch_19_10_values.all id = true := by decide

def batch_19_11_values : List Bool := [accepted_977]
theorem batch_19_11_ok : batch_19_11_values.all id = true := by decide

def batch_19_12_values : List Bool := [accepted_980]
theorem batch_19_12_ok : batch_19_12_values.all id = true := by decide

def batch_19_13_values : List Bool := [accepted_982]
theorem batch_19_13_ok : batch_19_13_values.all id = true := by decide

def batch_19_14_values : List Bool := [accepted_983]
theorem batch_19_14_ok : batch_19_14_values.all id = true := by decide

def batch_19_15_values : List Bool := [accepted_985]
theorem batch_19_15_ok : batch_19_15_values.all id = true := by decide

def batch_19_16_values : List Bool := [accepted_987]
theorem batch_19_16_ok : batch_19_16_values.all id = true := by decide

def batch_19_17_values : List Bool := [accepted_994]
theorem batch_19_17_ok : batch_19_17_values.all id = true := by decide

def batch_19_18_values : List Bool := [accepted_995]
theorem batch_19_18_ok : batch_19_18_values.all id = true := by decide

def batch_19_19_values : List Bool := [accepted_997]
theorem batch_19_19_ok : batch_19_19_values.all id = true := by decide

def batch_19_20_values : List Bool := [accepted_999]
theorem batch_19_20_ok : batch_19_20_values.all id = true := by decide

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

theorem leaf_954_ok : checkAt 527 1000 box_954 cert_954 = true := by
  have h := List.all_eq_true.mp batch_19_01_ok accepted_954 (by simp [batch_19_01_values])
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

theorem leaf_956_ok : checkAt 527 1000 box_956 cert_956 = true := by
  have h := List.all_eq_true.mp batch_19_02_ok accepted_956 (by simp [batch_19_02_values])
  exact h
theorem leaf_956_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_956.profileLo box_956.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_956_ok
theorem branch_box_956_nonnegative : ∀ j, 0 ≤ branch_box_956.lower j ∧ 0 ≤ branch_box_956.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_956, Box.profileLo, Box.profileHi, box_956]
theorem leaf_956_BranchSafe : CertificateConsequences.BranchSafe branch_box_956 := by
  left; refine ⟨branch_box_956_nonnegative, ?_⟩
  intro z hz; exact leaf_956_sound hz

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

theorem leaf_961_ok : checkAt 527 1000 box_961 cert_961 = true := by
  have h := List.all_eq_true.mp batch_19_05_ok accepted_961 (by simp [batch_19_05_values])
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

theorem leaf_966_ok : checkAt 527 1000 box_966 cert_966 = true := by
  have h := List.all_eq_true.mp batch_19_06_ok accepted_966 (by simp [batch_19_06_values])
  exact h
theorem leaf_966_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_966.profileLo box_966.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_966_ok
theorem branch_box_966_nonnegative : ∀ j, 0 ≤ branch_box_966.lower j ∧ 0 ≤ branch_box_966.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_966, Box.profileLo, Box.profileHi, box_966]
theorem leaf_966_BranchSafe : CertificateConsequences.BranchSafe branch_box_966 := by
  left; refine ⟨branch_box_966_nonnegative, ?_⟩
  intro z hz; exact leaf_966_sound hz

theorem leaf_967_ok : checkAt 527 1000 box_967 cert_967 = true := by
  have h := List.all_eq_true.mp batch_19_07_ok accepted_967 (by simp [batch_19_07_values])
  exact h
theorem leaf_967_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_967.profileLo box_967.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_967_ok
theorem branch_box_967_nonnegative : ∀ j, 0 ≤ branch_box_967.lower j ∧ 0 ≤ branch_box_967.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_967, Box.profileLo, Box.profileHi, box_967]
theorem leaf_967_BranchSafe : CertificateConsequences.BranchSafe branch_box_967 := by
  left; refine ⟨branch_box_967_nonnegative, ?_⟩
  intro z hz; exact leaf_967_sound hz

theorem leaf_969_ok : checkAt 527 1000 box_969 cert_969 = true := by
  have h := List.all_eq_true.mp batch_19_08_ok accepted_969 (by simp [batch_19_08_values])
  exact h
theorem leaf_969_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_969.profileLo box_969.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_969_ok
theorem branch_box_969_nonnegative : ∀ j, 0 ≤ branch_box_969.lower j ∧ 0 ≤ branch_box_969.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_969, Box.profileLo, Box.profileHi, box_969]
theorem leaf_969_BranchSafe : CertificateConsequences.BranchSafe branch_box_969 := by
  left; refine ⟨branch_box_969_nonnegative, ?_⟩
  intro z hz; exact leaf_969_sound hz

theorem leaf_971_ok : checkAt 527 1000 box_971 cert_971 = true := by
  have h := List.all_eq_true.mp batch_19_09_ok accepted_971 (by simp [batch_19_09_values])
  exact h
theorem leaf_971_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_971.profileLo box_971.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_971_ok
theorem branch_box_971_nonnegative : ∀ j, 0 ≤ branch_box_971.lower j ∧ 0 ≤ branch_box_971.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_971, Box.profileLo, Box.profileHi, box_971]
theorem leaf_971_BranchSafe : CertificateConsequences.BranchSafe branch_box_971 := by
  left; refine ⟨branch_box_971_nonnegative, ?_⟩
  intro z hz; exact leaf_971_sound hz

theorem leaf_974_ok : checkAt 527 1000 box_974 cert_974 = true := by
  have h := List.all_eq_true.mp batch_19_10_ok accepted_974 (by simp [batch_19_10_values])
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

theorem leaf_977_ok : checkAt 527 1000 box_977 cert_977 = true := by
  have h := List.all_eq_true.mp batch_19_11_ok accepted_977 (by simp [batch_19_11_values])
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

theorem leaf_980_ok : checkAt 527 1000 box_980 cert_980 = true := by
  have h := List.all_eq_true.mp batch_19_12_ok accepted_980 (by simp [batch_19_12_values])
  exact h
theorem leaf_980_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_980.profileLo box_980.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_980_ok
theorem branch_box_980_nonnegative : ∀ j, 0 ≤ branch_box_980.lower j ∧ 0 ≤ branch_box_980.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_980, Box.profileLo, Box.profileHi, box_980]
theorem leaf_980_BranchSafe : CertificateConsequences.BranchSafe branch_box_980 := by
  left; refine ⟨branch_box_980_nonnegative, ?_⟩
  intro z hz; exact leaf_980_sound hz

theorem leaf_982_ok : checkAt 527 1000 box_982 cert_982 = true := by
  have h := List.all_eq_true.mp batch_19_13_ok accepted_982 (by simp [batch_19_13_values])
  exact h
theorem leaf_982_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_982.profileLo box_982.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_982_ok
theorem branch_box_982_nonnegative : ∀ j, 0 ≤ branch_box_982.lower j ∧ 0 ≤ branch_box_982.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_982, Box.profileLo, Box.profileHi, box_982]
theorem leaf_982_BranchSafe : CertificateConsequences.BranchSafe branch_box_982 := by
  left; refine ⟨branch_box_982_nonnegative, ?_⟩
  intro z hz; exact leaf_982_sound hz

theorem leaf_983_ok : checkAt 527 1000 box_983 cert_983 = true := by
  have h := List.all_eq_true.mp batch_19_14_ok accepted_983 (by simp [batch_19_14_values])
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

theorem leaf_985_ok : checkAt 527 1000 box_985 cert_985 = true := by
  have h := List.all_eq_true.mp batch_19_15_ok accepted_985 (by simp [batch_19_15_values])
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
  have h := List.all_eq_true.mp batch_19_16_ok accepted_987 (by simp [batch_19_16_values])
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

theorem leaf_994_ok : checkAt 527 1000 box_994 cert_994 = true := by
  have h := List.all_eq_true.mp batch_19_17_ok accepted_994 (by simp [batch_19_17_values])
  exact h
theorem leaf_994_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_994.profileLo box_994.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_994_ok
theorem branch_box_994_nonnegative : ∀ j, 0 ≤ branch_box_994.lower j ∧ 0 ≤ branch_box_994.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_994, Box.profileLo, Box.profileHi, box_994]
theorem leaf_994_BranchSafe : CertificateConsequences.BranchSafe branch_box_994 := by
  left; refine ⟨branch_box_994_nonnegative, ?_⟩
  intro z hz; exact leaf_994_sound hz

theorem leaf_995_ok : checkAt 527 1000 box_995 cert_995 = true := by
  have h := List.all_eq_true.mp batch_19_18_ok accepted_995 (by simp [batch_19_18_values])
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
  have h := List.all_eq_true.mp batch_19_19_ok accepted_997 (by simp [batch_19_19_values])
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

theorem leaf_999_ok : checkAt 527 1000 box_999 cert_999 = true := by
  have h := List.all_eq_true.mp batch_19_20_ok accepted_999 (by simp [batch_19_20_values])
  exact h
theorem leaf_999_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_999.profileLo box_999.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_999_ok
theorem branch_box_999_nonnegative : ∀ j, 0 ≤ branch_box_999.lower j ∧ 0 ≤ branch_box_999.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_999, Box.profileLo, Box.profileHi, box_999]
theorem leaf_999_BranchSafe : CertificateConsequences.BranchSafe branch_box_999 := by
  left; refine ⟨branch_box_999_nonnegative, ?_⟩
  intro z hz; exact leaf_999_sound hz

#print axioms batch_19_00_ok
#print axioms leaf_950_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
