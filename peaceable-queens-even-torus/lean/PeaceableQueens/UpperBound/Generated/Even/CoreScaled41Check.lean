import PeaceableQueens.UpperBound.Generated.Even.CoreScaled41Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_41_00_values : List Bool := [accepted_2051]
theorem batch_41_00_ok : batch_41_00_values.all id = true := by decide

def batch_41_01_values : List Bool := [accepted_2053]
theorem batch_41_01_ok : batch_41_01_values.all id = true := by decide

def batch_41_02_values : List Bool := [accepted_2058]
theorem batch_41_02_ok : batch_41_02_values.all id = true := by decide

def batch_41_03_values : List Bool := [accepted_2060]
theorem batch_41_03_ok : batch_41_03_values.all id = true := by decide

def batch_41_04_values : List Bool := [accepted_2061]
theorem batch_41_04_ok : batch_41_04_values.all id = true := by decide

def batch_41_05_values : List Bool := [accepted_2063]
theorem batch_41_05_ok : batch_41_05_values.all id = true := by decide

def batch_41_06_values : List Bool := [accepted_2068]
theorem batch_41_06_ok : batch_41_06_values.all id = true := by decide

def batch_41_07_values : List Bool := [accepted_2076]
theorem batch_41_07_ok : batch_41_07_values.all id = true := by decide

def batch_41_08_values : List Bool := [accepted_2078]
theorem batch_41_08_ok : batch_41_08_values.all id = true := by decide

def batch_41_09_values : List Bool := [accepted_2082]
theorem batch_41_09_ok : batch_41_09_values.all id = true := by decide

def batch_41_10_values : List Bool := [accepted_2090]
theorem batch_41_10_ok : batch_41_10_values.all id = true := by decide

def batch_41_11_values : List Bool := [accepted_2092]
theorem batch_41_11_ok : batch_41_11_values.all id = true := by decide

def batch_41_12_values : List Bool := [accepted_2096]
theorem batch_41_12_ok : batch_41_12_values.all id = true := by decide

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

theorem leaf_2058_ok : checkAt 527 1000 box_2058 cert_2058 = true := by
  have h := List.all_eq_true.mp batch_41_02_ok accepted_2058 (by simp [batch_41_02_values])
  exact h
theorem leaf_2058_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2058.profileLo box_2058.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2058_ok
theorem branch_box_2058_nonnegative : ∀ j, 0 ≤ branch_box_2058.lower j ∧ 0 ≤ branch_box_2058.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2058, Box.profileLo, Box.profileHi, box_2058]
theorem leaf_2058_BranchSafe : CertificateConsequences.BranchSafe branch_box_2058 := by
  left; refine ⟨branch_box_2058_nonnegative, ?_⟩
  intro z hz; exact leaf_2058_sound hz

theorem leaf_2060_ok : checkAt 527 1000 box_2060 cert_2060 = true := by
  have h := List.all_eq_true.mp batch_41_03_ok accepted_2060 (by simp [batch_41_03_values])
  exact h
theorem leaf_2060_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2060.profileLo box_2060.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2060_ok
theorem branch_box_2060_nonnegative : ∀ j, 0 ≤ branch_box_2060.lower j ∧ 0 ≤ branch_box_2060.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2060, Box.profileLo, Box.profileHi, box_2060]
theorem leaf_2060_BranchSafe : CertificateConsequences.BranchSafe branch_box_2060 := by
  left; refine ⟨branch_box_2060_nonnegative, ?_⟩
  intro z hz; exact leaf_2060_sound hz

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

theorem leaf_2063_ok : checkAt 527 1000 box_2063 cert_2063 = true := by
  have h := List.all_eq_true.mp batch_41_05_ok accepted_2063 (by simp [batch_41_05_values])
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

theorem leaf_2068_ok : checkAt 527 1000 box_2068 cert_2068 = true := by
  have h := List.all_eq_true.mp batch_41_06_ok accepted_2068 (by simp [batch_41_06_values])
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

theorem leaf_2076_ok : checkAt 527 1000 box_2076 cert_2076 = true := by
  have h := List.all_eq_true.mp batch_41_07_ok accepted_2076 (by simp [batch_41_07_values])
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

theorem leaf_2078_ok : checkAt 527 1000 box_2078 cert_2078 = true := by
  have h := List.all_eq_true.mp batch_41_08_ok accepted_2078 (by simp [batch_41_08_values])
  exact h
theorem leaf_2078_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2078.profileLo box_2078.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2078_ok
theorem branch_box_2078_nonnegative : ∀ j, 0 ≤ branch_box_2078.lower j ∧ 0 ≤ branch_box_2078.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2078, Box.profileLo, Box.profileHi, box_2078]
theorem leaf_2078_BranchSafe : CertificateConsequences.BranchSafe branch_box_2078 := by
  left; refine ⟨branch_box_2078_nonnegative, ?_⟩
  intro z hz; exact leaf_2078_sound hz

theorem leaf_2082_ok : checkAt 527 1000 box_2082 cert_2082 = true := by
  have h := List.all_eq_true.mp batch_41_09_ok accepted_2082 (by simp [batch_41_09_values])
  exact h
theorem leaf_2082_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2082.profileLo box_2082.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2082_ok
theorem branch_box_2082_nonnegative : ∀ j, 0 ≤ branch_box_2082.lower j ∧ 0 ≤ branch_box_2082.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2082, Box.profileLo, Box.profileHi, box_2082]
theorem leaf_2082_BranchSafe : CertificateConsequences.BranchSafe branch_box_2082 := by
  left; refine ⟨branch_box_2082_nonnegative, ?_⟩
  intro z hz; exact leaf_2082_sound hz

theorem leaf_2090_ok : checkAt 527 1000 box_2090 cert_2090 = true := by
  have h := List.all_eq_true.mp batch_41_10_ok accepted_2090 (by simp [batch_41_10_values])
  exact h
theorem leaf_2090_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2090.profileLo box_2090.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2090_ok
theorem branch_box_2090_nonnegative : ∀ j, 0 ≤ branch_box_2090.lower j ∧ 0 ≤ branch_box_2090.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2090, Box.profileLo, Box.profileHi, box_2090]
theorem leaf_2090_BranchSafe : CertificateConsequences.BranchSafe branch_box_2090 := by
  left; refine ⟨branch_box_2090_nonnegative, ?_⟩
  intro z hz; exact leaf_2090_sound hz

theorem leaf_2092_ok : checkAt 527 1000 box_2092 cert_2092 = true := by
  have h := List.all_eq_true.mp batch_41_11_ok accepted_2092 (by simp [batch_41_11_values])
  exact h
theorem leaf_2092_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2092.profileLo box_2092.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2092_ok
theorem branch_box_2092_nonnegative : ∀ j, 0 ≤ branch_box_2092.lower j ∧ 0 ≤ branch_box_2092.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2092, Box.profileLo, Box.profileHi, box_2092]
theorem leaf_2092_BranchSafe : CertificateConsequences.BranchSafe branch_box_2092 := by
  left; refine ⟨branch_box_2092_nonnegative, ?_⟩
  intro z hz; exact leaf_2092_sound hz

theorem leaf_2096_ok : checkAt 527 1000 box_2096 cert_2096 = true := by
  have h := List.all_eq_true.mp batch_41_12_ok accepted_2096 (by simp [batch_41_12_values])
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

#print axioms batch_41_00_ok
#print axioms leaf_2051_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
