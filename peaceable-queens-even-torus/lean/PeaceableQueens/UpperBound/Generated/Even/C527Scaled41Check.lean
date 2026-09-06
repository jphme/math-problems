import PeaceableQueens.UpperBound.Generated.Even.C527Scaled41Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_41_00_values : List Bool := [accepted_2051]
theorem batch_41_00_ok : batch_41_00_values.all id = true := by decide

def batch_41_01_values : List Bool := [accepted_2053]
theorem batch_41_01_ok : batch_41_01_values.all id = true := by decide

def batch_41_02_values : List Bool := [accepted_2054]
theorem batch_41_02_ok : batch_41_02_values.all id = true := by decide

def batch_41_03_values : List Bool := [accepted_2059]
theorem batch_41_03_ok : batch_41_03_values.all id = true := by decide

def batch_41_04_values : List Bool := [accepted_2061]
theorem batch_41_04_ok : batch_41_04_values.all id = true := by decide

def batch_41_05_values : List Bool := [accepted_2062]
theorem batch_41_05_ok : batch_41_05_values.all id = true := by decide

def batch_41_06_values : List Bool := [accepted_2063]
theorem batch_41_06_ok : batch_41_06_values.all id = true := by decide

def batch_41_07_values : List Bool := [accepted_2065]
theorem batch_41_07_ok : batch_41_07_values.all id = true := by decide

def batch_41_08_values : List Bool := [accepted_2067]
theorem batch_41_08_ok : batch_41_08_values.all id = true := by decide

def batch_41_09_values : List Bool := [accepted_2068]
theorem batch_41_09_ok : batch_41_09_values.all id = true := by decide

def batch_41_10_values : List Bool := [accepted_2071]
theorem batch_41_10_ok : batch_41_10_values.all id = true := by decide

def batch_41_11_values : List Bool := [accepted_2072]
theorem batch_41_11_ok : batch_41_11_values.all id = true := by decide

def batch_41_12_values : List Bool := [accepted_2075]
theorem batch_41_12_ok : batch_41_12_values.all id = true := by decide

def batch_41_13_values : List Bool := [accepted_2076]
theorem batch_41_13_ok : batch_41_13_values.all id = true := by decide

def batch_41_14_values : List Bool := [accepted_2077]
theorem batch_41_14_ok : batch_41_14_values.all id = true := by decide

def batch_41_15_values : List Bool := [accepted_2081]
theorem batch_41_15_ok : batch_41_15_values.all id = true := by decide

def batch_41_16_values : List Bool := [accepted_2083]
theorem batch_41_16_ok : batch_41_16_values.all id = true := by decide

def batch_41_17_values : List Bool := [accepted_2084]
theorem batch_41_17_ok : batch_41_17_values.all id = true := by decide

def batch_41_18_values : List Bool := [accepted_2085]
theorem batch_41_18_ok : batch_41_18_values.all id = true := by decide

def batch_41_19_values : List Bool := [accepted_2086]
theorem batch_41_19_ok : batch_41_19_values.all id = true := by decide

def batch_41_20_values : List Bool := [accepted_2095]
theorem batch_41_20_ok : batch_41_20_values.all id = true := by decide

def batch_41_21_values : List Bool := [accepted_2096]
theorem batch_41_21_ok : batch_41_21_values.all id = true := by decide

def batch_41_22_values : List Bool := [accepted_2099]
theorem batch_41_22_ok : batch_41_22_values.all id = true := by decide

theorem leaf_2051_ok : checkAt 527 1000 box_2051 cert_2051 = true := by
  have h := List.all_eq_true.mp batch_41_00_ok accepted_2051 (by simp [batch_41_00_values])
  exact h
theorem leaf_2051_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2051.profileLo box_2051.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2051_ok
theorem branch_box_2051_nonnegative : ∀ j, 0 ≤ branch_box_2051.lower j ∧ 0 ≤ branch_box_2051.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2051, Box.profileLo, Box.profileHi, box_2051]
theorem leaf_2051_BranchSafe : CertificateConsequences.BranchSafe branch_box_2051 := by
  left; refine ⟨branch_box_2051_nonnegative, ?_⟩
  intro z hz; exact leaf_2051_sound hz

theorem leaf_2053_ok : checkAt 527 1000 box_2053 cert_2053 = true := by
  have h := List.all_eq_true.mp batch_41_01_ok accepted_2053 (by simp [batch_41_01_values])
  exact h
theorem leaf_2053_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2053.profileLo box_2053.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2053_ok
theorem branch_box_2053_nonnegative : ∀ j, 0 ≤ branch_box_2053.lower j ∧ 0 ≤ branch_box_2053.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2053, Box.profileLo, Box.profileHi, box_2053]
theorem leaf_2053_BranchSafe : CertificateConsequences.BranchSafe branch_box_2053 := by
  left; refine ⟨branch_box_2053_nonnegative, ?_⟩
  intro z hz; exact leaf_2053_sound hz

theorem leaf_2054_ok : checkAt 527 1000 box_2054 cert_2054 = true := by
  have h := List.all_eq_true.mp batch_41_02_ok accepted_2054 (by simp [batch_41_02_values])
  exact h
theorem leaf_2054_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2054.profileLo box_2054.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2054_ok
theorem branch_box_2054_nonnegative : ∀ j, 0 ≤ branch_box_2054.lower j ∧ 0 ≤ branch_box_2054.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2054, Box.profileLo, Box.profileHi, box_2054]
theorem leaf_2054_BranchSafe : CertificateConsequences.BranchSafe branch_box_2054 := by
  left; refine ⟨branch_box_2054_nonnegative, ?_⟩
  intro z hz; exact leaf_2054_sound hz

theorem leaf_2059_ok : checkAt 527 1000 box_2059 cert_2059 = true := by
  have h := List.all_eq_true.mp batch_41_03_ok accepted_2059 (by simp [batch_41_03_values])
  exact h
theorem leaf_2059_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2059.profileLo box_2059.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2059_ok
theorem branch_box_2059_nonnegative : ∀ j, 0 ≤ branch_box_2059.lower j ∧ 0 ≤ branch_box_2059.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2059, Box.profileLo, Box.profileHi, box_2059]
theorem leaf_2059_BranchSafe : CertificateConsequences.BranchSafe branch_box_2059 := by
  left; refine ⟨branch_box_2059_nonnegative, ?_⟩
  intro z hz; exact leaf_2059_sound hz

theorem leaf_2061_ok : checkAt 527 1000 box_2061 cert_2061 = true := by
  have h := List.all_eq_true.mp batch_41_04_ok accepted_2061 (by simp [batch_41_04_values])
  exact h
theorem leaf_2061_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2061.profileLo box_2061.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2061_ok
theorem branch_box_2061_nonnegative : ∀ j, 0 ≤ branch_box_2061.lower j ∧ 0 ≤ branch_box_2061.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2061, Box.profileLo, Box.profileHi, box_2061]
theorem leaf_2061_BranchSafe : CertificateConsequences.BranchSafe branch_box_2061 := by
  left; refine ⟨branch_box_2061_nonnegative, ?_⟩
  intro z hz; exact leaf_2061_sound hz

theorem leaf_2062_ok : checkAt 527 1000 box_2062 cert_2062 = true := by
  have h := List.all_eq_true.mp batch_41_05_ok accepted_2062 (by simp [batch_41_05_values])
  exact h
theorem leaf_2062_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2062.profileLo box_2062.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2062_ok
theorem branch_box_2062_nonnegative : ∀ j, 0 ≤ branch_box_2062.lower j ∧ 0 ≤ branch_box_2062.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2062, Box.profileLo, Box.profileHi, box_2062]
theorem leaf_2062_BranchSafe : CertificateConsequences.BranchSafe branch_box_2062 := by
  left; refine ⟨branch_box_2062_nonnegative, ?_⟩
  intro z hz; exact leaf_2062_sound hz

theorem leaf_2063_ok : checkAt 527 1000 box_2063 cert_2063 = true := by
  have h := List.all_eq_true.mp batch_41_06_ok accepted_2063 (by simp [batch_41_06_values])
  exact h
theorem leaf_2063_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2063.profileLo box_2063.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2063_ok
theorem branch_box_2063_nonnegative : ∀ j, 0 ≤ branch_box_2063.lower j ∧ 0 ≤ branch_box_2063.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2063, Box.profileLo, Box.profileHi, box_2063]
theorem leaf_2063_BranchSafe : CertificateConsequences.BranchSafe branch_box_2063 := by
  left; refine ⟨branch_box_2063_nonnegative, ?_⟩
  intro z hz; exact leaf_2063_sound hz

theorem leaf_2065_ok : checkAt 527 1000 box_2065 cert_2065 = true := by
  have h := List.all_eq_true.mp batch_41_07_ok accepted_2065 (by simp [batch_41_07_values])
  exact h
theorem leaf_2065_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2065.profileLo box_2065.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2065_ok
theorem branch_box_2065_nonnegative : ∀ j, 0 ≤ branch_box_2065.lower j ∧ 0 ≤ branch_box_2065.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2065, Box.profileLo, Box.profileHi, box_2065]
theorem leaf_2065_BranchSafe : CertificateConsequences.BranchSafe branch_box_2065 := by
  left; refine ⟨branch_box_2065_nonnegative, ?_⟩
  intro z hz; exact leaf_2065_sound hz

theorem leaf_2067_ok : checkAt 527 1000 box_2067 cert_2067 = true := by
  have h := List.all_eq_true.mp batch_41_08_ok accepted_2067 (by simp [batch_41_08_values])
  exact h
theorem leaf_2067_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2067.profileLo box_2067.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2067_ok
theorem branch_box_2067_nonnegative : ∀ j, 0 ≤ branch_box_2067.lower j ∧ 0 ≤ branch_box_2067.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2067, Box.profileLo, Box.profileHi, box_2067]
theorem leaf_2067_BranchSafe : CertificateConsequences.BranchSafe branch_box_2067 := by
  left; refine ⟨branch_box_2067_nonnegative, ?_⟩
  intro z hz; exact leaf_2067_sound hz

theorem leaf_2068_ok : checkAt 527 1000 box_2068 cert_2068 = true := by
  have h := List.all_eq_true.mp batch_41_09_ok accepted_2068 (by simp [batch_41_09_values])
  exact h
theorem leaf_2068_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2068.profileLo box_2068.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2068_ok
theorem branch_box_2068_nonnegative : ∀ j, 0 ≤ branch_box_2068.lower j ∧ 0 ≤ branch_box_2068.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2068, Box.profileLo, Box.profileHi, box_2068]
theorem leaf_2068_BranchSafe : CertificateConsequences.BranchSafe branch_box_2068 := by
  left; refine ⟨branch_box_2068_nonnegative, ?_⟩
  intro z hz; exact leaf_2068_sound hz

theorem leaf_2071_ok : checkAt 527 1000 box_2071 cert_2071 = true := by
  have h := List.all_eq_true.mp batch_41_10_ok accepted_2071 (by simp [batch_41_10_values])
  exact h
theorem leaf_2071_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2071.profileLo box_2071.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2071_ok
theorem branch_box_2071_nonnegative : ∀ j, 0 ≤ branch_box_2071.lower j ∧ 0 ≤ branch_box_2071.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2071, Box.profileLo, Box.profileHi, box_2071]
theorem leaf_2071_BranchSafe : CertificateConsequences.BranchSafe branch_box_2071 := by
  left; refine ⟨branch_box_2071_nonnegative, ?_⟩
  intro z hz; exact leaf_2071_sound hz

theorem leaf_2072_ok : checkAt 527 1000 box_2072 cert_2072 = true := by
  have h := List.all_eq_true.mp batch_41_11_ok accepted_2072 (by simp [batch_41_11_values])
  exact h
theorem leaf_2072_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2072.profileLo box_2072.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2072_ok
theorem branch_box_2072_nonnegative : ∀ j, 0 ≤ branch_box_2072.lower j ∧ 0 ≤ branch_box_2072.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2072, Box.profileLo, Box.profileHi, box_2072]
theorem leaf_2072_BranchSafe : CertificateConsequences.BranchSafe branch_box_2072 := by
  left; refine ⟨branch_box_2072_nonnegative, ?_⟩
  intro z hz; exact leaf_2072_sound hz

theorem leaf_2075_ok : checkAt 527 1000 box_2075 cert_2075 = true := by
  have h := List.all_eq_true.mp batch_41_12_ok accepted_2075 (by simp [batch_41_12_values])
  exact h
theorem leaf_2075_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2075.profileLo box_2075.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2075_ok
theorem branch_box_2075_nonnegative : ∀ j, 0 ≤ branch_box_2075.lower j ∧ 0 ≤ branch_box_2075.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2075, Box.profileLo, Box.profileHi, box_2075]
theorem leaf_2075_BranchSafe : CertificateConsequences.BranchSafe branch_box_2075 := by
  left; refine ⟨branch_box_2075_nonnegative, ?_⟩
  intro z hz; exact leaf_2075_sound hz

theorem leaf_2076_ok : checkAt 527 1000 box_2076 cert_2076 = true := by
  have h := List.all_eq_true.mp batch_41_13_ok accepted_2076 (by simp [batch_41_13_values])
  exact h
theorem leaf_2076_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2076.profileLo box_2076.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2076_ok
theorem branch_box_2076_nonnegative : ∀ j, 0 ≤ branch_box_2076.lower j ∧ 0 ≤ branch_box_2076.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2076, Box.profileLo, Box.profileHi, box_2076]
theorem leaf_2076_BranchSafe : CertificateConsequences.BranchSafe branch_box_2076 := by
  left; refine ⟨branch_box_2076_nonnegative, ?_⟩
  intro z hz; exact leaf_2076_sound hz

theorem leaf_2077_ok : checkAt 527 1000 box_2077 cert_2077 = true := by
  have h := List.all_eq_true.mp batch_41_14_ok accepted_2077 (by simp [batch_41_14_values])
  exact h
theorem leaf_2077_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2077.profileLo box_2077.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2077_ok
theorem branch_box_2077_nonnegative : ∀ j, 0 ≤ branch_box_2077.lower j ∧ 0 ≤ branch_box_2077.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2077, Box.profileLo, Box.profileHi, box_2077]
theorem leaf_2077_BranchSafe : CertificateConsequences.BranchSafe branch_box_2077 := by
  left; refine ⟨branch_box_2077_nonnegative, ?_⟩
  intro z hz; exact leaf_2077_sound hz

theorem leaf_2081_ok : checkAt 527 1000 box_2081 cert_2081 = true := by
  have h := List.all_eq_true.mp batch_41_15_ok accepted_2081 (by simp [batch_41_15_values])
  exact h
theorem leaf_2081_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2081.profileLo box_2081.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2081_ok
theorem branch_box_2081_nonnegative : ∀ j, 0 ≤ branch_box_2081.lower j ∧ 0 ≤ branch_box_2081.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2081, Box.profileLo, Box.profileHi, box_2081]
theorem leaf_2081_BranchSafe : CertificateConsequences.BranchSafe branch_box_2081 := by
  left; refine ⟨branch_box_2081_nonnegative, ?_⟩
  intro z hz; exact leaf_2081_sound hz

theorem leaf_2083_ok : checkAt 527 1000 box_2083 cert_2083 = true := by
  have h := List.all_eq_true.mp batch_41_16_ok accepted_2083 (by simp [batch_41_16_values])
  exact h
theorem leaf_2083_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2083.profileLo box_2083.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2083_ok
theorem branch_box_2083_nonnegative : ∀ j, 0 ≤ branch_box_2083.lower j ∧ 0 ≤ branch_box_2083.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2083, Box.profileLo, Box.profileHi, box_2083]
theorem leaf_2083_BranchSafe : CertificateConsequences.BranchSafe branch_box_2083 := by
  left; refine ⟨branch_box_2083_nonnegative, ?_⟩
  intro z hz; exact leaf_2083_sound hz

theorem leaf_2084_ok : checkAt 527 1000 box_2084 cert_2084 = true := by
  have h := List.all_eq_true.mp batch_41_17_ok accepted_2084 (by simp [batch_41_17_values])
  exact h
theorem leaf_2084_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2084.profileLo box_2084.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2084_ok
theorem branch_box_2084_nonnegative : ∀ j, 0 ≤ branch_box_2084.lower j ∧ 0 ≤ branch_box_2084.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2084, Box.profileLo, Box.profileHi, box_2084]
theorem leaf_2084_BranchSafe : CertificateConsequences.BranchSafe branch_box_2084 := by
  left; refine ⟨branch_box_2084_nonnegative, ?_⟩
  intro z hz; exact leaf_2084_sound hz

theorem leaf_2085_ok : checkAt 527 1000 box_2085 cert_2085 = true := by
  have h := List.all_eq_true.mp batch_41_18_ok accepted_2085 (by simp [batch_41_18_values])
  exact h
theorem leaf_2085_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2085.profileLo box_2085.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2085_ok
theorem branch_box_2085_nonnegative : ∀ j, 0 ≤ branch_box_2085.lower j ∧ 0 ≤ branch_box_2085.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2085, Box.profileLo, Box.profileHi, box_2085]
theorem leaf_2085_BranchSafe : CertificateConsequences.BranchSafe branch_box_2085 := by
  left; refine ⟨branch_box_2085_nonnegative, ?_⟩
  intro z hz; exact leaf_2085_sound hz

theorem leaf_2086_ok : checkAt 527 1000 box_2086 cert_2086 = true := by
  have h := List.all_eq_true.mp batch_41_19_ok accepted_2086 (by simp [batch_41_19_values])
  exact h
theorem leaf_2086_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2086.profileLo box_2086.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2086_ok
theorem branch_box_2086_nonnegative : ∀ j, 0 ≤ branch_box_2086.lower j ∧ 0 ≤ branch_box_2086.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2086, Box.profileLo, Box.profileHi, box_2086]
theorem leaf_2086_BranchSafe : CertificateConsequences.BranchSafe branch_box_2086 := by
  left; refine ⟨branch_box_2086_nonnegative, ?_⟩
  intro z hz; exact leaf_2086_sound hz

theorem leaf_2095_ok : checkAt 527 1000 box_2095 cert_2095 = true := by
  have h := List.all_eq_true.mp batch_41_20_ok accepted_2095 (by simp [batch_41_20_values])
  exact h
theorem leaf_2095_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2095.profileLo box_2095.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2095_ok
theorem branch_box_2095_nonnegative : ∀ j, 0 ≤ branch_box_2095.lower j ∧ 0 ≤ branch_box_2095.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2095, Box.profileLo, Box.profileHi, box_2095]
theorem leaf_2095_BranchSafe : CertificateConsequences.BranchSafe branch_box_2095 := by
  left; refine ⟨branch_box_2095_nonnegative, ?_⟩
  intro z hz; exact leaf_2095_sound hz

theorem leaf_2096_ok : checkAt 527 1000 box_2096 cert_2096 = true := by
  have h := List.all_eq_true.mp batch_41_21_ok accepted_2096 (by simp [batch_41_21_values])
  exact h
theorem leaf_2096_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2096.profileLo box_2096.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2096_ok
theorem branch_box_2096_nonnegative : ∀ j, 0 ≤ branch_box_2096.lower j ∧ 0 ≤ branch_box_2096.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2096, Box.profileLo, Box.profileHi, box_2096]
theorem leaf_2096_BranchSafe : CertificateConsequences.BranchSafe branch_box_2096 := by
  left; refine ⟨branch_box_2096_nonnegative, ?_⟩
  intro z hz; exact leaf_2096_sound hz

theorem leaf_2099_ok : checkAt 527 1000 box_2099 cert_2099 = true := by
  have h := List.all_eq_true.mp batch_41_22_ok accepted_2099 (by simp [batch_41_22_values])
  exact h
theorem leaf_2099_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2099.profileLo box_2099.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2099_ok
theorem branch_box_2099_nonnegative : ∀ j, 0 ≤ branch_box_2099.lower j ∧ 0 ≤ branch_box_2099.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2099, Box.profileLo, Box.profileHi, box_2099]
theorem leaf_2099_BranchSafe : CertificateConsequences.BranchSafe branch_box_2099 := by
  left; refine ⟨branch_box_2099_nonnegative, ?_⟩
  intro z hz; exact leaf_2099_sound hz

#print axioms batch_41_00_ok
#print axioms leaf_2051_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
