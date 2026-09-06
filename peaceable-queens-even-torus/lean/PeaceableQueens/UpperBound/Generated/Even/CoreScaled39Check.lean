import PeaceableQueens.UpperBound.Generated.Even.CoreScaled39Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_39_00_values : List Bool := [accepted_1951]
theorem batch_39_00_ok : batch_39_00_values.all id = true := by decide

def batch_39_01_values : List Bool := [accepted_1954]
theorem batch_39_01_ok : batch_39_01_values.all id = true := by decide

def batch_39_02_values : List Bool := [accepted_1955]
theorem batch_39_02_ok : batch_39_02_values.all id = true := by decide

def batch_39_03_values : List Bool := [accepted_1957]
theorem batch_39_03_ok : batch_39_03_values.all id = true := by decide

def batch_39_04_values : List Bool := [accepted_1962]
theorem batch_39_04_ok : batch_39_04_values.all id = true := by decide

def batch_39_05_values : List Bool := [accepted_1963]
theorem batch_39_05_ok : batch_39_05_values.all id = true := by decide

def batch_39_06_values : List Bool := [accepted_1965]
theorem batch_39_06_ok : batch_39_06_values.all id = true := by decide

def batch_39_07_values : List Bool := [accepted_1968]
theorem batch_39_07_ok : batch_39_07_values.all id = true := by decide

def batch_39_08_values : List Bool := [accepted_1969]
theorem batch_39_08_ok : batch_39_08_values.all id = true := by decide

def batch_39_09_values : List Bool := [accepted_1971]
theorem batch_39_09_ok : batch_39_09_values.all id = true := by decide

def batch_39_10_values : List Bool := [accepted_1976]
theorem batch_39_10_ok : batch_39_10_values.all id = true := by decide

def batch_39_11_values : List Bool := [accepted_1978]
theorem batch_39_11_ok : batch_39_11_values.all id = true := by decide

def batch_39_12_values : List Bool := [accepted_1980]
theorem batch_39_12_ok : batch_39_12_values.all id = true := by decide

def batch_39_13_values : List Bool := [accepted_1981]
theorem batch_39_13_ok : batch_39_13_values.all id = true := by decide

def batch_39_14_values : List Bool := [accepted_1983]
theorem batch_39_14_ok : batch_39_14_values.all id = true := by decide

def batch_39_15_values : List Bool := [accepted_1989]
theorem batch_39_15_ok : batch_39_15_values.all id = true := by decide

def batch_39_16_values : List Bool := [accepted_1991]
theorem batch_39_16_ok : batch_39_16_values.all id = true := by decide

def batch_39_17_values : List Bool := [accepted_1993]
theorem batch_39_17_ok : batch_39_17_values.all id = true := by decide

def batch_39_18_values : List Bool := [accepted_1995]
theorem batch_39_18_ok : batch_39_18_values.all id = true := by decide

theorem leaf_1951_ok : checkAt 527 1000 box_1951 cert_1951 = true := by
  have h := List.all_eq_true.mp batch_39_00_ok accepted_1951 (by simp [batch_39_00_values])
  exact h
theorem leaf_1951_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1951.profileLo box_1951.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1951_ok
theorem branch_box_1951_nonnegative : ∀ j, 0 ≤ branch_box_1951.lower j ∧ 0 ≤ branch_box_1951.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1951, Box.profileLo, Box.profileHi, box_1951]
theorem leaf_1951_BranchSafe : CertificateConsequences.BranchSafe branch_box_1951 := by
  left; refine ⟨branch_box_1951_nonnegative, ?_⟩
  intro z hz; exact leaf_1951_sound hz

theorem leaf_1954_ok : checkAt 527 1000 box_1954 cert_1954 = true := by
  have h := List.all_eq_true.mp batch_39_01_ok accepted_1954 (by simp [batch_39_01_values])
  exact h
theorem leaf_1954_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1954.profileLo box_1954.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1954_ok
theorem branch_box_1954_nonnegative : ∀ j, 0 ≤ branch_box_1954.lower j ∧ 0 ≤ branch_box_1954.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1954, Box.profileLo, Box.profileHi, box_1954]
theorem leaf_1954_BranchSafe : CertificateConsequences.BranchSafe branch_box_1954 := by
  left; refine ⟨branch_box_1954_nonnegative, ?_⟩
  intro z hz; exact leaf_1954_sound hz

theorem leaf_1955_ok : checkAt 527 1000 box_1955 cert_1955 = true := by
  have h := List.all_eq_true.mp batch_39_02_ok accepted_1955 (by simp [batch_39_02_values])
  exact h
theorem leaf_1955_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1955.profileLo box_1955.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1955_ok
theorem branch_box_1955_nonnegative : ∀ j, 0 ≤ branch_box_1955.lower j ∧ 0 ≤ branch_box_1955.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1955, Box.profileLo, Box.profileHi, box_1955]
theorem leaf_1955_BranchSafe : CertificateConsequences.BranchSafe branch_box_1955 := by
  left; refine ⟨branch_box_1955_nonnegative, ?_⟩
  intro z hz; exact leaf_1955_sound hz

theorem leaf_1957_ok : checkAt 527 1000 box_1957 cert_1957 = true := by
  have h := List.all_eq_true.mp batch_39_03_ok accepted_1957 (by simp [batch_39_03_values])
  exact h
theorem leaf_1957_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1957.profileLo box_1957.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1957_ok
theorem branch_box_1957_nonnegative : ∀ j, 0 ≤ branch_box_1957.lower j ∧ 0 ≤ branch_box_1957.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1957, Box.profileLo, Box.profileHi, box_1957]
theorem leaf_1957_BranchSafe : CertificateConsequences.BranchSafe branch_box_1957 := by
  left; refine ⟨branch_box_1957_nonnegative, ?_⟩
  intro z hz; exact leaf_1957_sound hz

theorem leaf_1962_ok : checkAt 527 1000 box_1962 cert_1962 = true := by
  have h := List.all_eq_true.mp batch_39_04_ok accepted_1962 (by simp [batch_39_04_values])
  exact h
theorem leaf_1962_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1962.profileLo box_1962.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1962_ok
theorem branch_box_1962_nonnegative : ∀ j, 0 ≤ branch_box_1962.lower j ∧ 0 ≤ branch_box_1962.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1962, Box.profileLo, Box.profileHi, box_1962]
theorem leaf_1962_BranchSafe : CertificateConsequences.BranchSafe branch_box_1962 := by
  left; refine ⟨branch_box_1962_nonnegative, ?_⟩
  intro z hz; exact leaf_1962_sound hz

theorem leaf_1963_ok : checkAt 527 1000 box_1963 cert_1963 = true := by
  have h := List.all_eq_true.mp batch_39_05_ok accepted_1963 (by simp [batch_39_05_values])
  exact h
theorem leaf_1963_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1963.profileLo box_1963.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1963_ok
theorem branch_box_1963_nonnegative : ∀ j, 0 ≤ branch_box_1963.lower j ∧ 0 ≤ branch_box_1963.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1963, Box.profileLo, Box.profileHi, box_1963]
theorem leaf_1963_BranchSafe : CertificateConsequences.BranchSafe branch_box_1963 := by
  left; refine ⟨branch_box_1963_nonnegative, ?_⟩
  intro z hz; exact leaf_1963_sound hz

theorem leaf_1965_ok : checkAt 527 1000 box_1965 cert_1965 = true := by
  have h := List.all_eq_true.mp batch_39_06_ok accepted_1965 (by simp [batch_39_06_values])
  exact h
theorem leaf_1965_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1965.profileLo box_1965.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1965_ok
theorem branch_box_1965_nonnegative : ∀ j, 0 ≤ branch_box_1965.lower j ∧ 0 ≤ branch_box_1965.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1965, Box.profileLo, Box.profileHi, box_1965]
theorem leaf_1965_BranchSafe : CertificateConsequences.BranchSafe branch_box_1965 := by
  left; refine ⟨branch_box_1965_nonnegative, ?_⟩
  intro z hz; exact leaf_1965_sound hz

theorem leaf_1968_ok : checkAt 527 1000 box_1968 cert_1968 = true := by
  have h := List.all_eq_true.mp batch_39_07_ok accepted_1968 (by simp [batch_39_07_values])
  exact h
theorem leaf_1968_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1968.profileLo box_1968.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1968_ok
theorem branch_box_1968_nonnegative : ∀ j, 0 ≤ branch_box_1968.lower j ∧ 0 ≤ branch_box_1968.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1968, Box.profileLo, Box.profileHi, box_1968]
theorem leaf_1968_BranchSafe : CertificateConsequences.BranchSafe branch_box_1968 := by
  left; refine ⟨branch_box_1968_nonnegative, ?_⟩
  intro z hz; exact leaf_1968_sound hz

theorem leaf_1969_ok : checkAt 527 1000 box_1969 cert_1969 = true := by
  have h := List.all_eq_true.mp batch_39_08_ok accepted_1969 (by simp [batch_39_08_values])
  exact h
theorem leaf_1969_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1969.profileLo box_1969.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1969_ok
theorem branch_box_1969_nonnegative : ∀ j, 0 ≤ branch_box_1969.lower j ∧ 0 ≤ branch_box_1969.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1969, Box.profileLo, Box.profileHi, box_1969]
theorem leaf_1969_BranchSafe : CertificateConsequences.BranchSafe branch_box_1969 := by
  left; refine ⟨branch_box_1969_nonnegative, ?_⟩
  intro z hz; exact leaf_1969_sound hz

theorem leaf_1971_ok : checkAt 527 1000 box_1971 cert_1971 = true := by
  have h := List.all_eq_true.mp batch_39_09_ok accepted_1971 (by simp [batch_39_09_values])
  exact h
theorem leaf_1971_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1971.profileLo box_1971.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1971_ok
theorem branch_box_1971_nonnegative : ∀ j, 0 ≤ branch_box_1971.lower j ∧ 0 ≤ branch_box_1971.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1971, Box.profileLo, Box.profileHi, box_1971]
theorem leaf_1971_BranchSafe : CertificateConsequences.BranchSafe branch_box_1971 := by
  left; refine ⟨branch_box_1971_nonnegative, ?_⟩
  intro z hz; exact leaf_1971_sound hz

theorem leaf_1976_ok : checkAt 527 1000 box_1976 cert_1976 = true := by
  have h := List.all_eq_true.mp batch_39_10_ok accepted_1976 (by simp [batch_39_10_values])
  exact h
theorem leaf_1976_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1976.profileLo box_1976.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1976_ok
theorem branch_box_1976_nonnegative : ∀ j, 0 ≤ branch_box_1976.lower j ∧ 0 ≤ branch_box_1976.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1976, Box.profileLo, Box.profileHi, box_1976]
theorem leaf_1976_BranchSafe : CertificateConsequences.BranchSafe branch_box_1976 := by
  left; refine ⟨branch_box_1976_nonnegative, ?_⟩
  intro z hz; exact leaf_1976_sound hz

theorem leaf_1978_ok : checkAt 527 1000 box_1978 cert_1978 = true := by
  have h := List.all_eq_true.mp batch_39_11_ok accepted_1978 (by simp [batch_39_11_values])
  exact h
theorem leaf_1978_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1978.profileLo box_1978.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1978_ok
theorem branch_box_1978_nonnegative : ∀ j, 0 ≤ branch_box_1978.lower j ∧ 0 ≤ branch_box_1978.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1978, Box.profileLo, Box.profileHi, box_1978]
theorem leaf_1978_BranchSafe : CertificateConsequences.BranchSafe branch_box_1978 := by
  left; refine ⟨branch_box_1978_nonnegative, ?_⟩
  intro z hz; exact leaf_1978_sound hz

theorem leaf_1980_ok : checkAt 527 1000 box_1980 cert_1980 = true := by
  have h := List.all_eq_true.mp batch_39_12_ok accepted_1980 (by simp [batch_39_12_values])
  exact h
theorem leaf_1980_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1980.profileLo box_1980.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1980_ok
theorem branch_box_1980_nonnegative : ∀ j, 0 ≤ branch_box_1980.lower j ∧ 0 ≤ branch_box_1980.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1980, Box.profileLo, Box.profileHi, box_1980]
theorem leaf_1980_BranchSafe : CertificateConsequences.BranchSafe branch_box_1980 := by
  left; refine ⟨branch_box_1980_nonnegative, ?_⟩
  intro z hz; exact leaf_1980_sound hz

theorem leaf_1981_ok : checkAt 527 1000 box_1981 cert_1981 = true := by
  have h := List.all_eq_true.mp batch_39_13_ok accepted_1981 (by simp [batch_39_13_values])
  exact h
theorem leaf_1981_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1981.profileLo box_1981.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1981_ok
theorem branch_box_1981_nonnegative : ∀ j, 0 ≤ branch_box_1981.lower j ∧ 0 ≤ branch_box_1981.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1981, Box.profileLo, Box.profileHi, box_1981]
theorem leaf_1981_BranchSafe : CertificateConsequences.BranchSafe branch_box_1981 := by
  left; refine ⟨branch_box_1981_nonnegative, ?_⟩
  intro z hz; exact leaf_1981_sound hz

theorem leaf_1983_ok : checkAt 527 1000 box_1983 cert_1983 = true := by
  have h := List.all_eq_true.mp batch_39_14_ok accepted_1983 (by simp [batch_39_14_values])
  exact h
theorem leaf_1983_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1983.profileLo box_1983.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1983_ok
theorem branch_box_1983_nonnegative : ∀ j, 0 ≤ branch_box_1983.lower j ∧ 0 ≤ branch_box_1983.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1983, Box.profileLo, Box.profileHi, box_1983]
theorem leaf_1983_BranchSafe : CertificateConsequences.BranchSafe branch_box_1983 := by
  left; refine ⟨branch_box_1983_nonnegative, ?_⟩
  intro z hz; exact leaf_1983_sound hz

theorem leaf_1989_ok : checkAt 527 1000 box_1989 cert_1989 = true := by
  have h := List.all_eq_true.mp batch_39_15_ok accepted_1989 (by simp [batch_39_15_values])
  exact h
theorem leaf_1989_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1989.profileLo box_1989.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1989_ok
theorem branch_box_1989_nonnegative : ∀ j, 0 ≤ branch_box_1989.lower j ∧ 0 ≤ branch_box_1989.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1989, Box.profileLo, Box.profileHi, box_1989]
theorem leaf_1989_BranchSafe : CertificateConsequences.BranchSafe branch_box_1989 := by
  left; refine ⟨branch_box_1989_nonnegative, ?_⟩
  intro z hz; exact leaf_1989_sound hz

theorem leaf_1991_ok : checkAt 527 1000 box_1991 cert_1991 = true := by
  have h := List.all_eq_true.mp batch_39_16_ok accepted_1991 (by simp [batch_39_16_values])
  exact h
theorem leaf_1991_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1991.profileLo box_1991.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1991_ok
theorem branch_box_1991_nonnegative : ∀ j, 0 ≤ branch_box_1991.lower j ∧ 0 ≤ branch_box_1991.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1991, Box.profileLo, Box.profileHi, box_1991]
theorem leaf_1991_BranchSafe : CertificateConsequences.BranchSafe branch_box_1991 := by
  left; refine ⟨branch_box_1991_nonnegative, ?_⟩
  intro z hz; exact leaf_1991_sound hz

theorem leaf_1993_ok : checkAt 527 1000 box_1993 cert_1993 = true := by
  have h := List.all_eq_true.mp batch_39_17_ok accepted_1993 (by simp [batch_39_17_values])
  exact h
theorem leaf_1993_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1993.profileLo box_1993.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1993_ok
theorem branch_box_1993_nonnegative : ∀ j, 0 ≤ branch_box_1993.lower j ∧ 0 ≤ branch_box_1993.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1993, Box.profileLo, Box.profileHi, box_1993]
theorem leaf_1993_BranchSafe : CertificateConsequences.BranchSafe branch_box_1993 := by
  left; refine ⟨branch_box_1993_nonnegative, ?_⟩
  intro z hz; exact leaf_1993_sound hz

theorem leaf_1995_ok : checkAt 527 1000 box_1995 cert_1995 = true := by
  have h := List.all_eq_true.mp batch_39_18_ok accepted_1995 (by simp [batch_39_18_values])
  exact h
theorem leaf_1995_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1995.profileLo box_1995.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1995_ok
theorem branch_box_1995_nonnegative : ∀ j, 0 ≤ branch_box_1995.lower j ∧ 0 ≤ branch_box_1995.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1995, Box.profileLo, Box.profileHi, box_1995]
theorem leaf_1995_BranchSafe : CertificateConsequences.BranchSafe branch_box_1995 := by
  left; refine ⟨branch_box_1995_nonnegative, ?_⟩
  intro z hz; exact leaf_1995_sound hz

#print axioms batch_39_00_ok
#print axioms leaf_1951_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
