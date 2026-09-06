import PeaceableQueens.UpperBound.Generated.Even.C527Scaled39Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_39_00_values : List Bool := [accepted_1951]
theorem batch_39_00_ok : batch_39_00_values.all id = true := by decide

def batch_39_01_values : List Bool := [accepted_1952]
theorem batch_39_01_ok : batch_39_01_values.all id = true := by decide

def batch_39_02_values : List Bool := [accepted_1953]
theorem batch_39_02_ok : batch_39_02_values.all id = true := by decide

def batch_39_03_values : List Bool := [accepted_1955]
theorem batch_39_03_ok : batch_39_03_values.all id = true := by decide

def batch_39_04_values : List Bool := [accepted_1956]
theorem batch_39_04_ok : batch_39_04_values.all id = true := by decide

def batch_39_05_values : List Bool := [accepted_1961]
theorem batch_39_05_ok : batch_39_05_values.all id = true := by decide

def batch_39_06_values : List Bool := [accepted_1962]
theorem batch_39_06_ok : batch_39_06_values.all id = true := by decide

def batch_39_07_values : List Bool := [accepted_1963]
theorem batch_39_07_ok : batch_39_07_values.all id = true := by decide

def batch_39_08_values : List Bool := [accepted_1964]
theorem batch_39_08_ok : batch_39_08_values.all id = true := by decide

def batch_39_09_values : List Bool := [accepted_1967]
theorem batch_39_09_ok : batch_39_09_values.all id = true := by decide

def batch_39_10_values : List Bool := [accepted_1968]
theorem batch_39_10_ok : batch_39_10_values.all id = true := by decide

def batch_39_11_values : List Bool := [accepted_1971]
theorem batch_39_11_ok : batch_39_11_values.all id = true := by decide

def batch_39_12_values : List Bool := [accepted_1977]
theorem batch_39_12_ok : batch_39_12_values.all id = true := by decide

def batch_39_13_values : List Bool := [accepted_1978]
theorem batch_39_13_ok : batch_39_13_values.all id = true := by decide

def batch_39_14_values : List Bool := [accepted_1980]
theorem batch_39_14_ok : batch_39_14_values.all id = true := by decide

def batch_39_15_values : List Bool := [accepted_1981]
theorem batch_39_15_ok : batch_39_15_values.all id = true := by decide

def batch_39_16_values : List Bool := [accepted_1982]
theorem batch_39_16_ok : batch_39_16_values.all id = true := by decide

def batch_39_17_values : List Bool := [accepted_1983]
theorem batch_39_17_ok : batch_39_17_values.all id = true := by decide

def batch_39_18_values : List Bool := [accepted_1984]
theorem batch_39_18_ok : batch_39_18_values.all id = true := by decide

def batch_39_19_values : List Bool := [accepted_1985]
theorem batch_39_19_ok : batch_39_19_values.all id = true := by decide

def batch_39_20_values : List Bool := [accepted_1986]
theorem batch_39_20_ok : batch_39_20_values.all id = true := by decide

def batch_39_21_values : List Bool := [accepted_1989]
theorem batch_39_21_ok : batch_39_21_values.all id = true := by decide

def batch_39_22_values : List Bool := [accepted_1990]
theorem batch_39_22_ok : batch_39_22_values.all id = true := by decide

def batch_39_23_values : List Bool := [accepted_1993]
theorem batch_39_23_ok : batch_39_23_values.all id = true := by decide

def batch_39_24_values : List Bool := [accepted_1994]
theorem batch_39_24_ok : batch_39_24_values.all id = true := by decide

def batch_39_25_values : List Bool := [accepted_1997]
theorem batch_39_25_ok : batch_39_25_values.all id = true := by decide

def batch_39_26_values : List Bool := [accepted_1998]
theorem batch_39_26_ok : batch_39_26_values.all id = true := by decide

def batch_39_27_values : List Bool := [accepted_1999]
theorem batch_39_27_ok : batch_39_27_values.all id = true := by decide

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

theorem leaf_1952_ok : checkAt 527 1000 box_1952 cert_1952 = true := by
  have h := List.all_eq_true.mp batch_39_01_ok accepted_1952 (by simp [batch_39_01_values])
  exact h
theorem leaf_1952_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1952.profileLo box_1952.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1952_ok
theorem branch_box_1952_nonnegative : ∀ j, 0 ≤ branch_box_1952.lower j ∧ 0 ≤ branch_box_1952.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1952, Box.profileLo, Box.profileHi, box_1952]
theorem leaf_1952_BranchSafe : CertificateConsequences.BranchSafe branch_box_1952 := by
  left; refine ⟨branch_box_1952_nonnegative, ?_⟩
  intro z hz; exact leaf_1952_sound hz

theorem leaf_1953_ok : checkAt 527 1000 box_1953 cert_1953 = true := by
  have h := List.all_eq_true.mp batch_39_02_ok accepted_1953 (by simp [batch_39_02_values])
  exact h
theorem leaf_1953_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1953.profileLo box_1953.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1953_ok
theorem branch_box_1953_nonnegative : ∀ j, 0 ≤ branch_box_1953.lower j ∧ 0 ≤ branch_box_1953.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1953, Box.profileLo, Box.profileHi, box_1953]
theorem leaf_1953_BranchSafe : CertificateConsequences.BranchSafe branch_box_1953 := by
  left; refine ⟨branch_box_1953_nonnegative, ?_⟩
  intro z hz; exact leaf_1953_sound hz

theorem leaf_1955_ok : checkAt 527 1000 box_1955 cert_1955 = true := by
  have h := List.all_eq_true.mp batch_39_03_ok accepted_1955 (by simp [batch_39_03_values])
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

theorem leaf_1956_ok : checkAt 527 1000 box_1956 cert_1956 = true := by
  have h := List.all_eq_true.mp batch_39_04_ok accepted_1956 (by simp [batch_39_04_values])
  exact h
theorem leaf_1956_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1956.profileLo box_1956.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1956_ok
theorem branch_box_1956_nonnegative : ∀ j, 0 ≤ branch_box_1956.lower j ∧ 0 ≤ branch_box_1956.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1956, Box.profileLo, Box.profileHi, box_1956]
theorem leaf_1956_BranchSafe : CertificateConsequences.BranchSafe branch_box_1956 := by
  left; refine ⟨branch_box_1956_nonnegative, ?_⟩
  intro z hz; exact leaf_1956_sound hz

theorem leaf_1961_ok : checkAt 527 1000 box_1961 cert_1961 = true := by
  have h := List.all_eq_true.mp batch_39_05_ok accepted_1961 (by simp [batch_39_05_values])
  exact h
theorem leaf_1961_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1961.profileLo box_1961.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1961_ok
theorem branch_box_1961_nonnegative : ∀ j, 0 ≤ branch_box_1961.lower j ∧ 0 ≤ branch_box_1961.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1961, Box.profileLo, Box.profileHi, box_1961]
theorem leaf_1961_BranchSafe : CertificateConsequences.BranchSafe branch_box_1961 := by
  left; refine ⟨branch_box_1961_nonnegative, ?_⟩
  intro z hz; exact leaf_1961_sound hz

theorem leaf_1962_ok : checkAt 527 1000 box_1962 cert_1962 = true := by
  have h := List.all_eq_true.mp batch_39_06_ok accepted_1962 (by simp [batch_39_06_values])
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
  have h := List.all_eq_true.mp batch_39_07_ok accepted_1963 (by simp [batch_39_07_values])
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

theorem leaf_1964_ok : checkAt 527 1000 box_1964 cert_1964 = true := by
  have h := List.all_eq_true.mp batch_39_08_ok accepted_1964 (by simp [batch_39_08_values])
  exact h
theorem leaf_1964_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1964.profileLo box_1964.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1964_ok
theorem branch_box_1964_nonnegative : ∀ j, 0 ≤ branch_box_1964.lower j ∧ 0 ≤ branch_box_1964.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1964, Box.profileLo, Box.profileHi, box_1964]
theorem leaf_1964_BranchSafe : CertificateConsequences.BranchSafe branch_box_1964 := by
  left; refine ⟨branch_box_1964_nonnegative, ?_⟩
  intro z hz; exact leaf_1964_sound hz

theorem leaf_1967_ok : checkAt 527 1000 box_1967 cert_1967 = true := by
  have h := List.all_eq_true.mp batch_39_09_ok accepted_1967 (by simp [batch_39_09_values])
  exact h
theorem leaf_1967_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1967.profileLo box_1967.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1967_ok
theorem branch_box_1967_nonnegative : ∀ j, 0 ≤ branch_box_1967.lower j ∧ 0 ≤ branch_box_1967.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1967, Box.profileLo, Box.profileHi, box_1967]
theorem leaf_1967_BranchSafe : CertificateConsequences.BranchSafe branch_box_1967 := by
  left; refine ⟨branch_box_1967_nonnegative, ?_⟩
  intro z hz; exact leaf_1967_sound hz

theorem leaf_1968_ok : checkAt 527 1000 box_1968 cert_1968 = true := by
  have h := List.all_eq_true.mp batch_39_10_ok accepted_1968 (by simp [batch_39_10_values])
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

theorem leaf_1971_ok : checkAt 527 1000 box_1971 cert_1971 = true := by
  have h := List.all_eq_true.mp batch_39_11_ok accepted_1971 (by simp [batch_39_11_values])
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

theorem leaf_1977_ok : checkAt 527 1000 box_1977 cert_1977 = true := by
  have h := List.all_eq_true.mp batch_39_12_ok accepted_1977 (by simp [batch_39_12_values])
  exact h
theorem leaf_1977_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1977.profileLo box_1977.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1977_ok
theorem branch_box_1977_nonnegative : ∀ j, 0 ≤ branch_box_1977.lower j ∧ 0 ≤ branch_box_1977.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1977, Box.profileLo, Box.profileHi, box_1977]
theorem leaf_1977_BranchSafe : CertificateConsequences.BranchSafe branch_box_1977 := by
  left; refine ⟨branch_box_1977_nonnegative, ?_⟩
  intro z hz; exact leaf_1977_sound hz

theorem leaf_1978_ok : checkAt 527 1000 box_1978 cert_1978 = true := by
  have h := List.all_eq_true.mp batch_39_13_ok accepted_1978 (by simp [batch_39_13_values])
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
  have h := List.all_eq_true.mp batch_39_14_ok accepted_1980 (by simp [batch_39_14_values])
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
  have h := List.all_eq_true.mp batch_39_15_ok accepted_1981 (by simp [batch_39_15_values])
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

theorem leaf_1982_ok : checkAt 527 1000 box_1982 cert_1982 = true := by
  have h := List.all_eq_true.mp batch_39_16_ok accepted_1982 (by simp [batch_39_16_values])
  exact h
theorem leaf_1982_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1982.profileLo box_1982.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1982_ok
theorem branch_box_1982_nonnegative : ∀ j, 0 ≤ branch_box_1982.lower j ∧ 0 ≤ branch_box_1982.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1982, Box.profileLo, Box.profileHi, box_1982]
theorem leaf_1982_BranchSafe : CertificateConsequences.BranchSafe branch_box_1982 := by
  left; refine ⟨branch_box_1982_nonnegative, ?_⟩
  intro z hz; exact leaf_1982_sound hz

theorem leaf_1983_ok : checkAt 527 1000 box_1983 cert_1983 = true := by
  have h := List.all_eq_true.mp batch_39_17_ok accepted_1983 (by simp [batch_39_17_values])
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

theorem leaf_1984_ok : checkAt 527 1000 box_1984 cert_1984 = true := by
  have h := List.all_eq_true.mp batch_39_18_ok accepted_1984 (by simp [batch_39_18_values])
  exact h
theorem leaf_1984_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1984.profileLo box_1984.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1984_ok
theorem branch_box_1984_nonnegative : ∀ j, 0 ≤ branch_box_1984.lower j ∧ 0 ≤ branch_box_1984.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1984, Box.profileLo, Box.profileHi, box_1984]
theorem leaf_1984_BranchSafe : CertificateConsequences.BranchSafe branch_box_1984 := by
  left; refine ⟨branch_box_1984_nonnegative, ?_⟩
  intro z hz; exact leaf_1984_sound hz

theorem leaf_1985_ok : checkAt 527 1000 box_1985 cert_1985 = true := by
  have h := List.all_eq_true.mp batch_39_19_ok accepted_1985 (by simp [batch_39_19_values])
  exact h
theorem leaf_1985_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1985.profileLo box_1985.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1985_ok
theorem branch_box_1985_nonnegative : ∀ j, 0 ≤ branch_box_1985.lower j ∧ 0 ≤ branch_box_1985.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1985, Box.profileLo, Box.profileHi, box_1985]
theorem leaf_1985_BranchSafe : CertificateConsequences.BranchSafe branch_box_1985 := by
  left; refine ⟨branch_box_1985_nonnegative, ?_⟩
  intro z hz; exact leaf_1985_sound hz

theorem leaf_1986_ok : checkAt 527 1000 box_1986 cert_1986 = true := by
  have h := List.all_eq_true.mp batch_39_20_ok accepted_1986 (by simp [batch_39_20_values])
  exact h
theorem leaf_1986_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1986.profileLo box_1986.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1986_ok
theorem branch_box_1986_nonnegative : ∀ j, 0 ≤ branch_box_1986.lower j ∧ 0 ≤ branch_box_1986.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1986, Box.profileLo, Box.profileHi, box_1986]
theorem leaf_1986_BranchSafe : CertificateConsequences.BranchSafe branch_box_1986 := by
  left; refine ⟨branch_box_1986_nonnegative, ?_⟩
  intro z hz; exact leaf_1986_sound hz

theorem leaf_1989_ok : checkAt 527 1000 box_1989 cert_1989 = true := by
  have h := List.all_eq_true.mp batch_39_21_ok accepted_1989 (by simp [batch_39_21_values])
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

theorem leaf_1990_ok : checkAt 527 1000 box_1990 cert_1990 = true := by
  have h := List.all_eq_true.mp batch_39_22_ok accepted_1990 (by simp [batch_39_22_values])
  exact h
theorem leaf_1990_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1990.profileLo box_1990.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1990_ok
theorem branch_box_1990_nonnegative : ∀ j, 0 ≤ branch_box_1990.lower j ∧ 0 ≤ branch_box_1990.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1990, Box.profileLo, Box.profileHi, box_1990]
theorem leaf_1990_BranchSafe : CertificateConsequences.BranchSafe branch_box_1990 := by
  left; refine ⟨branch_box_1990_nonnegative, ?_⟩
  intro z hz; exact leaf_1990_sound hz

theorem leaf_1993_ok : checkAt 527 1000 box_1993 cert_1993 = true := by
  have h := List.all_eq_true.mp batch_39_23_ok accepted_1993 (by simp [batch_39_23_values])
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

theorem leaf_1994_ok : checkAt 527 1000 box_1994 cert_1994 = true := by
  have h := List.all_eq_true.mp batch_39_24_ok accepted_1994 (by simp [batch_39_24_values])
  exact h
theorem leaf_1994_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1994.profileLo box_1994.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1994_ok
theorem branch_box_1994_nonnegative : ∀ j, 0 ≤ branch_box_1994.lower j ∧ 0 ≤ branch_box_1994.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1994, Box.profileLo, Box.profileHi, box_1994]
theorem leaf_1994_BranchSafe : CertificateConsequences.BranchSafe branch_box_1994 := by
  left; refine ⟨branch_box_1994_nonnegative, ?_⟩
  intro z hz; exact leaf_1994_sound hz

theorem leaf_1997_ok : checkAt 527 1000 box_1997 cert_1997 = true := by
  have h := List.all_eq_true.mp batch_39_25_ok accepted_1997 (by simp [batch_39_25_values])
  exact h
theorem leaf_1997_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1997.profileLo box_1997.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1997_ok
theorem branch_box_1997_nonnegative : ∀ j, 0 ≤ branch_box_1997.lower j ∧ 0 ≤ branch_box_1997.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1997, Box.profileLo, Box.profileHi, box_1997]
theorem leaf_1997_BranchSafe : CertificateConsequences.BranchSafe branch_box_1997 := by
  left; refine ⟨branch_box_1997_nonnegative, ?_⟩
  intro z hz; exact leaf_1997_sound hz

theorem leaf_1998_ok : checkAt 527 1000 box_1998 cert_1998 = true := by
  have h := List.all_eq_true.mp batch_39_26_ok accepted_1998 (by simp [batch_39_26_values])
  exact h
theorem leaf_1998_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1998.profileLo box_1998.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1998_ok
theorem branch_box_1998_nonnegative : ∀ j, 0 ≤ branch_box_1998.lower j ∧ 0 ≤ branch_box_1998.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1998, Box.profileLo, Box.profileHi, box_1998]
theorem leaf_1998_BranchSafe : CertificateConsequences.BranchSafe branch_box_1998 := by
  left; refine ⟨branch_box_1998_nonnegative, ?_⟩
  intro z hz; exact leaf_1998_sound hz

theorem leaf_1999_ok : checkAt 527 1000 box_1999 cert_1999 = true := by
  have h := List.all_eq_true.mp batch_39_27_ok accepted_1999 (by simp [batch_39_27_values])
  exact h
theorem leaf_1999_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1999.profileLo box_1999.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1999_ok
theorem branch_box_1999_nonnegative : ∀ j, 0 ≤ branch_box_1999.lower j ∧ 0 ≤ branch_box_1999.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1999, Box.profileLo, Box.profileHi, box_1999]
theorem leaf_1999_BranchSafe : CertificateConsequences.BranchSafe branch_box_1999 := by
  left; refine ⟨branch_box_1999_nonnegative, ?_⟩
  intro z hz; exact leaf_1999_sound hz

#print axioms batch_39_00_ok
#print axioms leaf_1951_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
