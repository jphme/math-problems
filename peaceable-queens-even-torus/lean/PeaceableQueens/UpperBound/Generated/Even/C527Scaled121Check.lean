import PeaceableQueens.UpperBound.Generated.Even.C527Scaled121Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_121_00_values : List Bool := [accepted_6051]
theorem batch_121_00_ok : batch_121_00_values.all id = true := by decide

def batch_121_01_values : List Bool := [accepted_6052]
theorem batch_121_01_ok : batch_121_01_values.all id = true := by decide

def batch_121_02_values : List Bool := [accepted_6053]
theorem batch_121_02_ok : batch_121_02_values.all id = true := by decide

def batch_121_03_values : List Bool := [accepted_6056]
theorem batch_121_03_ok : batch_121_03_values.all id = true := by decide

def batch_121_04_values : List Bool := [accepted_6057]
theorem batch_121_04_ok : batch_121_04_values.all id = true := by decide

def batch_121_05_values : List Bool := [accepted_6058]
theorem batch_121_05_ok : batch_121_05_values.all id = true := by decide

def batch_121_06_values : List Bool := [accepted_6061]
theorem batch_121_06_ok : batch_121_06_values.all id = true := by decide

def batch_121_07_values : List Bool := [accepted_6063]
theorem batch_121_07_ok : batch_121_07_values.all id = true := by decide

def batch_121_08_values : List Bool := [accepted_6065]
theorem batch_121_08_ok : batch_121_08_values.all id = true := by decide

def batch_121_09_values : List Bool := [accepted_6066]
theorem batch_121_09_ok : batch_121_09_values.all id = true := by decide

def batch_121_10_values : List Bool := [accepted_6069]
theorem batch_121_10_ok : batch_121_10_values.all id = true := by decide

def batch_121_11_values : List Bool := [accepted_6071]
theorem batch_121_11_ok : batch_121_11_values.all id = true := by decide

def batch_121_12_values : List Bool := [accepted_6073]
theorem batch_121_12_ok : batch_121_12_values.all id = true := by decide

def batch_121_13_values : List Bool := [accepted_6074]
theorem batch_121_13_ok : batch_121_13_values.all id = true := by decide

def batch_121_14_values : List Bool := [accepted_6077]
theorem batch_121_14_ok : batch_121_14_values.all id = true := by decide

def batch_121_15_values : List Bool := [accepted_6078]
theorem batch_121_15_ok : batch_121_15_values.all id = true := by decide

def batch_121_16_values : List Bool := [accepted_6080]
theorem batch_121_16_ok : batch_121_16_values.all id = true := by decide

def batch_121_17_values : List Bool := [accepted_6083]
theorem batch_121_17_ok : batch_121_17_values.all id = true := by decide

def batch_121_18_values : List Bool := [accepted_6084]
theorem batch_121_18_ok : batch_121_18_values.all id = true := by decide

def batch_121_19_values : List Bool := [accepted_6096]
theorem batch_121_19_ok : batch_121_19_values.all id = true := by decide

def batch_121_20_values : List Bool := [accepted_6098]
theorem batch_121_20_ok : batch_121_20_values.all id = true := by decide

theorem leaf_6051_ok : checkAt 527 1000 box_6051 cert_6051 = true := by
  have h := List.all_eq_true.mp batch_121_00_ok accepted_6051 (by simp [batch_121_00_values])
  exact h
theorem leaf_6051_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6051.profileLo box_6051.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6051_ok
theorem branch_box_6051_nonnegative : ∀ j, 0 ≤ branch_box_6051.lower j ∧ 0 ≤ branch_box_6051.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6051, Box.profileLo, Box.profileHi, box_6051]
theorem leaf_6051_BranchSafe : CertificateConsequences.BranchSafe branch_box_6051 := by
  left; refine ⟨branch_box_6051_nonnegative, ?_⟩
  intro z hz; exact leaf_6051_sound hz

theorem leaf_6052_ok : checkAt 527 1000 box_6052 cert_6052 = true := by
  have h := List.all_eq_true.mp batch_121_01_ok accepted_6052 (by simp [batch_121_01_values])
  exact h
theorem leaf_6052_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6052.profileLo box_6052.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6052_ok
theorem branch_box_6052_nonnegative : ∀ j, 0 ≤ branch_box_6052.lower j ∧ 0 ≤ branch_box_6052.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6052, Box.profileLo, Box.profileHi, box_6052]
theorem leaf_6052_BranchSafe : CertificateConsequences.BranchSafe branch_box_6052 := by
  left; refine ⟨branch_box_6052_nonnegative, ?_⟩
  intro z hz; exact leaf_6052_sound hz

theorem leaf_6053_ok : checkAt 527 1000 box_6053 cert_6053 = true := by
  have h := List.all_eq_true.mp batch_121_02_ok accepted_6053 (by simp [batch_121_02_values])
  exact h
theorem leaf_6053_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6053.profileLo box_6053.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6053_ok
theorem branch_box_6053_nonnegative : ∀ j, 0 ≤ branch_box_6053.lower j ∧ 0 ≤ branch_box_6053.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6053, Box.profileLo, Box.profileHi, box_6053]
theorem leaf_6053_BranchSafe : CertificateConsequences.BranchSafe branch_box_6053 := by
  left; refine ⟨branch_box_6053_nonnegative, ?_⟩
  intro z hz; exact leaf_6053_sound hz

theorem leaf_6056_ok : checkAt 527 1000 box_6056 cert_6056 = true := by
  have h := List.all_eq_true.mp batch_121_03_ok accepted_6056 (by simp [batch_121_03_values])
  exact h
theorem leaf_6056_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6056.profileLo box_6056.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6056_ok
theorem branch_box_6056_nonnegative : ∀ j, 0 ≤ branch_box_6056.lower j ∧ 0 ≤ branch_box_6056.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6056, Box.profileLo, Box.profileHi, box_6056]
theorem leaf_6056_BranchSafe : CertificateConsequences.BranchSafe branch_box_6056 := by
  left; refine ⟨branch_box_6056_nonnegative, ?_⟩
  intro z hz; exact leaf_6056_sound hz

theorem leaf_6057_ok : checkAt 527 1000 box_6057 cert_6057 = true := by
  have h := List.all_eq_true.mp batch_121_04_ok accepted_6057 (by simp [batch_121_04_values])
  exact h
theorem leaf_6057_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6057.profileLo box_6057.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6057_ok
theorem branch_box_6057_nonnegative : ∀ j, 0 ≤ branch_box_6057.lower j ∧ 0 ≤ branch_box_6057.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6057, Box.profileLo, Box.profileHi, box_6057]
theorem leaf_6057_BranchSafe : CertificateConsequences.BranchSafe branch_box_6057 := by
  left; refine ⟨branch_box_6057_nonnegative, ?_⟩
  intro z hz; exact leaf_6057_sound hz

theorem leaf_6058_ok : checkAt 527 1000 box_6058 cert_6058 = true := by
  have h := List.all_eq_true.mp batch_121_05_ok accepted_6058 (by simp [batch_121_05_values])
  exact h
theorem leaf_6058_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6058.profileLo box_6058.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6058_ok
theorem branch_box_6058_nonnegative : ∀ j, 0 ≤ branch_box_6058.lower j ∧ 0 ≤ branch_box_6058.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6058, Box.profileLo, Box.profileHi, box_6058]
theorem leaf_6058_BranchSafe : CertificateConsequences.BranchSafe branch_box_6058 := by
  left; refine ⟨branch_box_6058_nonnegative, ?_⟩
  intro z hz; exact leaf_6058_sound hz

theorem leaf_6061_ok : checkAt 527 1000 box_6061 cert_6061 = true := by
  have h := List.all_eq_true.mp batch_121_06_ok accepted_6061 (by simp [batch_121_06_values])
  exact h
theorem leaf_6061_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6061.profileLo box_6061.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6061_ok
theorem branch_box_6061_nonnegative : ∀ j, 0 ≤ branch_box_6061.lower j ∧ 0 ≤ branch_box_6061.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6061, Box.profileLo, Box.profileHi, box_6061]
theorem leaf_6061_BranchSafe : CertificateConsequences.BranchSafe branch_box_6061 := by
  left; refine ⟨branch_box_6061_nonnegative, ?_⟩
  intro z hz; exact leaf_6061_sound hz

theorem leaf_6063_ok : checkAt 527 1000 box_6063 cert_6063 = true := by
  have h := List.all_eq_true.mp batch_121_07_ok accepted_6063 (by simp [batch_121_07_values])
  exact h
theorem leaf_6063_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6063.profileLo box_6063.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6063_ok
theorem branch_box_6063_nonnegative : ∀ j, 0 ≤ branch_box_6063.lower j ∧ 0 ≤ branch_box_6063.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6063, Box.profileLo, Box.profileHi, box_6063]
theorem leaf_6063_BranchSafe : CertificateConsequences.BranchSafe branch_box_6063 := by
  left; refine ⟨branch_box_6063_nonnegative, ?_⟩
  intro z hz; exact leaf_6063_sound hz

theorem leaf_6065_ok : checkAt 527 1000 box_6065 cert_6065 = true := by
  have h := List.all_eq_true.mp batch_121_08_ok accepted_6065 (by simp [batch_121_08_values])
  exact h
theorem leaf_6065_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6065.profileLo box_6065.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6065_ok
theorem branch_box_6065_nonnegative : ∀ j, 0 ≤ branch_box_6065.lower j ∧ 0 ≤ branch_box_6065.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6065, Box.profileLo, Box.profileHi, box_6065]
theorem leaf_6065_BranchSafe : CertificateConsequences.BranchSafe branch_box_6065 := by
  left; refine ⟨branch_box_6065_nonnegative, ?_⟩
  intro z hz; exact leaf_6065_sound hz

theorem leaf_6066_ok : checkAt 527 1000 box_6066 cert_6066 = true := by
  have h := List.all_eq_true.mp batch_121_09_ok accepted_6066 (by simp [batch_121_09_values])
  exact h
theorem leaf_6066_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6066.profileLo box_6066.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6066_ok
theorem branch_box_6066_nonnegative : ∀ j, 0 ≤ branch_box_6066.lower j ∧ 0 ≤ branch_box_6066.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6066, Box.profileLo, Box.profileHi, box_6066]
theorem leaf_6066_BranchSafe : CertificateConsequences.BranchSafe branch_box_6066 := by
  left; refine ⟨branch_box_6066_nonnegative, ?_⟩
  intro z hz; exact leaf_6066_sound hz

theorem leaf_6069_ok : checkAt 527 1000 box_6069 cert_6069 = true := by
  have h := List.all_eq_true.mp batch_121_10_ok accepted_6069 (by simp [batch_121_10_values])
  exact h
theorem leaf_6069_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6069.profileLo box_6069.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6069_ok
theorem branch_box_6069_nonnegative : ∀ j, 0 ≤ branch_box_6069.lower j ∧ 0 ≤ branch_box_6069.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6069, Box.profileLo, Box.profileHi, box_6069]
theorem leaf_6069_BranchSafe : CertificateConsequences.BranchSafe branch_box_6069 := by
  left; refine ⟨branch_box_6069_nonnegative, ?_⟩
  intro z hz; exact leaf_6069_sound hz

theorem leaf_6071_ok : checkAt 527 1000 box_6071 cert_6071 = true := by
  have h := List.all_eq_true.mp batch_121_11_ok accepted_6071 (by simp [batch_121_11_values])
  exact h
theorem leaf_6071_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6071.profileLo box_6071.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6071_ok
theorem branch_box_6071_nonnegative : ∀ j, 0 ≤ branch_box_6071.lower j ∧ 0 ≤ branch_box_6071.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6071, Box.profileLo, Box.profileHi, box_6071]
theorem leaf_6071_BranchSafe : CertificateConsequences.BranchSafe branch_box_6071 := by
  left; refine ⟨branch_box_6071_nonnegative, ?_⟩
  intro z hz; exact leaf_6071_sound hz

theorem leaf_6073_ok : checkAt 527 1000 box_6073 cert_6073 = true := by
  have h := List.all_eq_true.mp batch_121_12_ok accepted_6073 (by simp [batch_121_12_values])
  exact h
theorem leaf_6073_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6073.profileLo box_6073.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6073_ok
theorem branch_box_6073_nonnegative : ∀ j, 0 ≤ branch_box_6073.lower j ∧ 0 ≤ branch_box_6073.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6073, Box.profileLo, Box.profileHi, box_6073]
theorem leaf_6073_BranchSafe : CertificateConsequences.BranchSafe branch_box_6073 := by
  left; refine ⟨branch_box_6073_nonnegative, ?_⟩
  intro z hz; exact leaf_6073_sound hz

theorem leaf_6074_ok : checkAt 527 1000 box_6074 cert_6074 = true := by
  have h := List.all_eq_true.mp batch_121_13_ok accepted_6074 (by simp [batch_121_13_values])
  exact h
theorem leaf_6074_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6074.profileLo box_6074.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6074_ok
theorem branch_box_6074_nonnegative : ∀ j, 0 ≤ branch_box_6074.lower j ∧ 0 ≤ branch_box_6074.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6074, Box.profileLo, Box.profileHi, box_6074]
theorem leaf_6074_BranchSafe : CertificateConsequences.BranchSafe branch_box_6074 := by
  left; refine ⟨branch_box_6074_nonnegative, ?_⟩
  intro z hz; exact leaf_6074_sound hz

theorem leaf_6077_ok : checkAt 527 1000 box_6077 cert_6077 = true := by
  have h := List.all_eq_true.mp batch_121_14_ok accepted_6077 (by simp [batch_121_14_values])
  exact h
theorem leaf_6077_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6077.profileLo box_6077.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6077_ok
theorem branch_box_6077_nonnegative : ∀ j, 0 ≤ branch_box_6077.lower j ∧ 0 ≤ branch_box_6077.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6077, Box.profileLo, Box.profileHi, box_6077]
theorem leaf_6077_BranchSafe : CertificateConsequences.BranchSafe branch_box_6077 := by
  left; refine ⟨branch_box_6077_nonnegative, ?_⟩
  intro z hz; exact leaf_6077_sound hz

theorem leaf_6078_ok : checkAt 527 1000 box_6078 cert_6078 = true := by
  have h := List.all_eq_true.mp batch_121_15_ok accepted_6078 (by simp [batch_121_15_values])
  exact h
theorem leaf_6078_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6078.profileLo box_6078.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6078_ok
theorem branch_box_6078_nonnegative : ∀ j, 0 ≤ branch_box_6078.lower j ∧ 0 ≤ branch_box_6078.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6078, Box.profileLo, Box.profileHi, box_6078]
theorem leaf_6078_BranchSafe : CertificateConsequences.BranchSafe branch_box_6078 := by
  left; refine ⟨branch_box_6078_nonnegative, ?_⟩
  intro z hz; exact leaf_6078_sound hz

theorem leaf_6080_ok : checkAt 527 1000 box_6080 cert_6080 = true := by
  have h := List.all_eq_true.mp batch_121_16_ok accepted_6080 (by simp [batch_121_16_values])
  exact h
theorem leaf_6080_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6080.profileLo box_6080.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6080_ok
theorem branch_box_6080_nonnegative : ∀ j, 0 ≤ branch_box_6080.lower j ∧ 0 ≤ branch_box_6080.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6080, Box.profileLo, Box.profileHi, box_6080]
theorem leaf_6080_BranchSafe : CertificateConsequences.BranchSafe branch_box_6080 := by
  left; refine ⟨branch_box_6080_nonnegative, ?_⟩
  intro z hz; exact leaf_6080_sound hz

theorem leaf_6083_ok : checkAt 527 1000 box_6083 cert_6083 = true := by
  have h := List.all_eq_true.mp batch_121_17_ok accepted_6083 (by simp [batch_121_17_values])
  exact h
theorem leaf_6083_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6083.profileLo box_6083.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6083_ok
theorem branch_box_6083_nonnegative : ∀ j, 0 ≤ branch_box_6083.lower j ∧ 0 ≤ branch_box_6083.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6083, Box.profileLo, Box.profileHi, box_6083]
theorem leaf_6083_BranchSafe : CertificateConsequences.BranchSafe branch_box_6083 := by
  left; refine ⟨branch_box_6083_nonnegative, ?_⟩
  intro z hz; exact leaf_6083_sound hz

theorem leaf_6084_ok : checkAt 527 1000 box_6084 cert_6084 = true := by
  have h := List.all_eq_true.mp batch_121_18_ok accepted_6084 (by simp [batch_121_18_values])
  exact h
theorem leaf_6084_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6084.profileLo box_6084.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6084_ok
theorem branch_box_6084_nonnegative : ∀ j, 0 ≤ branch_box_6084.lower j ∧ 0 ≤ branch_box_6084.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6084, Box.profileLo, Box.profileHi, box_6084]
theorem leaf_6084_BranchSafe : CertificateConsequences.BranchSafe branch_box_6084 := by
  left; refine ⟨branch_box_6084_nonnegative, ?_⟩
  intro z hz; exact leaf_6084_sound hz

theorem leaf_6096_ok : checkAt 527 1000 box_6096 cert_6096 = true := by
  have h := List.all_eq_true.mp batch_121_19_ok accepted_6096 (by simp [batch_121_19_values])
  exact h
theorem leaf_6096_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6096.profileLo box_6096.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6096_ok
theorem branch_box_6096_nonnegative : ∀ j, 0 ≤ branch_box_6096.lower j ∧ 0 ≤ branch_box_6096.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6096, Box.profileLo, Box.profileHi, box_6096]
theorem leaf_6096_BranchSafe : CertificateConsequences.BranchSafe branch_box_6096 := by
  left; refine ⟨branch_box_6096_nonnegative, ?_⟩
  intro z hz; exact leaf_6096_sound hz

theorem leaf_6098_ok : checkAt 527 1000 box_6098 cert_6098 = true := by
  have h := List.all_eq_true.mp batch_121_20_ok accepted_6098 (by simp [batch_121_20_values])
  exact h
theorem leaf_6098_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6098.profileLo box_6098.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6098_ok
theorem branch_box_6098_nonnegative : ∀ j, 0 ≤ branch_box_6098.lower j ∧ 0 ≤ branch_box_6098.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6098, Box.profileLo, Box.profileHi, box_6098]
theorem leaf_6098_BranchSafe : CertificateConsequences.BranchSafe branch_box_6098 := by
  left; refine ⟨branch_box_6098_nonnegative, ?_⟩
  intro z hz; exact leaf_6098_sound hz

#print axioms batch_121_00_ok
#print axioms leaf_6051_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
