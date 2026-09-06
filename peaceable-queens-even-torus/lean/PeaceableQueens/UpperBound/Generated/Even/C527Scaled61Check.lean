import PeaceableQueens.UpperBound.Generated.Even.C527Scaled61Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_61_00_values : List Bool := [accepted_3052]
theorem batch_61_00_ok : batch_61_00_values.all id = true := by decide

def batch_61_01_values : List Bool := [accepted_3053]
theorem batch_61_01_ok : batch_61_01_values.all id = true := by decide

def batch_61_02_values : List Bool := [accepted_3054]
theorem batch_61_02_ok : batch_61_02_values.all id = true := by decide

def batch_61_03_values : List Bool := [accepted_3056]
theorem batch_61_03_ok : batch_61_03_values.all id = true := by decide

def batch_61_04_values : List Bool := [accepted_3058]
theorem batch_61_04_ok : batch_61_04_values.all id = true := by decide

def batch_61_05_values : List Bool := [accepted_3059]
theorem batch_61_05_ok : batch_61_05_values.all id = true := by decide

def batch_61_06_values : List Bool := [accepted_3061]
theorem batch_61_06_ok : batch_61_06_values.all id = true := by decide

def batch_61_07_values : List Bool := [accepted_3062]
theorem batch_61_07_ok : batch_61_07_values.all id = true := by decide

def batch_61_08_values : List Bool := [accepted_3063]
theorem batch_61_08_ok : batch_61_08_values.all id = true := by decide

def batch_61_09_values : List Bool := [accepted_3064]
theorem batch_61_09_ok : batch_61_09_values.all id = true := by decide

def batch_61_10_values : List Bool := [accepted_3067]
theorem batch_61_10_ok : batch_61_10_values.all id = true := by decide

def batch_61_11_values : List Bool := [accepted_3069]
theorem batch_61_11_ok : batch_61_11_values.all id = true := by decide

def batch_61_12_values : List Bool := [accepted_3071]
theorem batch_61_12_ok : batch_61_12_values.all id = true := by decide

def batch_61_13_values : List Bool := [accepted_3072]
theorem batch_61_13_ok : batch_61_13_values.all id = true := by decide

def batch_61_14_values : List Bool := [accepted_3077]
theorem batch_61_14_ok : batch_61_14_values.all id = true := by decide

def batch_61_15_values : List Bool := [accepted_3078]
theorem batch_61_15_ok : batch_61_15_values.all id = true := by decide

def batch_61_16_values : List Bool := [accepted_3079]
theorem batch_61_16_ok : batch_61_16_values.all id = true := by decide

def batch_61_17_values : List Bool := [accepted_3080]
theorem batch_61_17_ok : batch_61_17_values.all id = true := by decide

def batch_61_18_values : List Bool := [accepted_3085]
theorem batch_61_18_ok : batch_61_18_values.all id = true := by decide

def batch_61_19_values : List Bool := [accepted_3086]
theorem batch_61_19_ok : batch_61_19_values.all id = true := by decide

def batch_61_20_values : List Bool := [accepted_3087]
theorem batch_61_20_ok : batch_61_20_values.all id = true := by decide

def batch_61_21_values : List Bool := [accepted_3088]
theorem batch_61_21_ok : batch_61_21_values.all id = true := by decide

def batch_61_22_values : List Bool := [accepted_3089]
theorem batch_61_22_ok : batch_61_22_values.all id = true := by decide

def batch_61_23_values : List Bool := [accepted_3092]
theorem batch_61_23_ok : batch_61_23_values.all id = true := by decide

def batch_61_24_values : List Bool := [accepted_3094]
theorem batch_61_24_ok : batch_61_24_values.all id = true := by decide

def batch_61_25_values : List Bool := [accepted_3096]
theorem batch_61_25_ok : batch_61_25_values.all id = true := by decide

def batch_61_26_values : List Bool := [accepted_3097]
theorem batch_61_26_ok : batch_61_26_values.all id = true := by decide

def batch_61_27_values : List Bool := [accepted_3099]
theorem batch_61_27_ok : batch_61_27_values.all id = true := by decide

theorem leaf_3052_ok : checkAt 527 1000 box_3052 cert_3052 = true := by
  have h := List.all_eq_true.mp batch_61_00_ok accepted_3052 (by simp [batch_61_00_values])
  exact h
theorem leaf_3052_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3052.profileLo box_3052.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3052_ok
theorem branch_box_3052_nonnegative : ∀ j, 0 ≤ branch_box_3052.lower j ∧ 0 ≤ branch_box_3052.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3052, Box.profileLo, Box.profileHi, box_3052]
theorem leaf_3052_BranchSafe : CertificateConsequences.BranchSafe branch_box_3052 := by
  left; refine ⟨branch_box_3052_nonnegative, ?_⟩
  intro z hz; exact leaf_3052_sound hz

theorem leaf_3053_ok : checkAt 527 1000 box_3053 cert_3053 = true := by
  have h := List.all_eq_true.mp batch_61_01_ok accepted_3053 (by simp [batch_61_01_values])
  exact h
theorem leaf_3053_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3053.profileLo box_3053.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3053_ok
theorem branch_box_3053_nonnegative : ∀ j, 0 ≤ branch_box_3053.lower j ∧ 0 ≤ branch_box_3053.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3053, Box.profileLo, Box.profileHi, box_3053]
theorem leaf_3053_BranchSafe : CertificateConsequences.BranchSafe branch_box_3053 := by
  left; refine ⟨branch_box_3053_nonnegative, ?_⟩
  intro z hz; exact leaf_3053_sound hz

theorem leaf_3054_ok : checkAt 527 1000 box_3054 cert_3054 = true := by
  have h := List.all_eq_true.mp batch_61_02_ok accepted_3054 (by simp [batch_61_02_values])
  exact h
theorem leaf_3054_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3054.profileLo box_3054.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3054_ok
theorem branch_box_3054_nonnegative : ∀ j, 0 ≤ branch_box_3054.lower j ∧ 0 ≤ branch_box_3054.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3054, Box.profileLo, Box.profileHi, box_3054]
theorem leaf_3054_BranchSafe : CertificateConsequences.BranchSafe branch_box_3054 := by
  left; refine ⟨branch_box_3054_nonnegative, ?_⟩
  intro z hz; exact leaf_3054_sound hz

theorem leaf_3056_ok : checkAt 527 1000 box_3056 cert_3056 = true := by
  have h := List.all_eq_true.mp batch_61_03_ok accepted_3056 (by simp [batch_61_03_values])
  exact h
theorem leaf_3056_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3056.profileLo box_3056.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3056_ok
theorem branch_box_3056_nonnegative : ∀ j, 0 ≤ branch_box_3056.lower j ∧ 0 ≤ branch_box_3056.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3056, Box.profileLo, Box.profileHi, box_3056]
theorem leaf_3056_BranchSafe : CertificateConsequences.BranchSafe branch_box_3056 := by
  left; refine ⟨branch_box_3056_nonnegative, ?_⟩
  intro z hz; exact leaf_3056_sound hz

theorem leaf_3058_ok : checkAt 527 1000 box_3058 cert_3058 = true := by
  have h := List.all_eq_true.mp batch_61_04_ok accepted_3058 (by simp [batch_61_04_values])
  exact h
theorem leaf_3058_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3058.profileLo box_3058.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3058_ok
theorem branch_box_3058_nonnegative : ∀ j, 0 ≤ branch_box_3058.lower j ∧ 0 ≤ branch_box_3058.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3058, Box.profileLo, Box.profileHi, box_3058]
theorem leaf_3058_BranchSafe : CertificateConsequences.BranchSafe branch_box_3058 := by
  left; refine ⟨branch_box_3058_nonnegative, ?_⟩
  intro z hz; exact leaf_3058_sound hz

theorem leaf_3059_ok : checkAt 527 1000 box_3059 cert_3059 = true := by
  have h := List.all_eq_true.mp batch_61_05_ok accepted_3059 (by simp [batch_61_05_values])
  exact h
theorem leaf_3059_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3059.profileLo box_3059.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3059_ok
theorem branch_box_3059_nonnegative : ∀ j, 0 ≤ branch_box_3059.lower j ∧ 0 ≤ branch_box_3059.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3059, Box.profileLo, Box.profileHi, box_3059]
theorem leaf_3059_BranchSafe : CertificateConsequences.BranchSafe branch_box_3059 := by
  left; refine ⟨branch_box_3059_nonnegative, ?_⟩
  intro z hz; exact leaf_3059_sound hz

theorem leaf_3061_ok : checkAt 527 1000 box_3061 cert_3061 = true := by
  have h := List.all_eq_true.mp batch_61_06_ok accepted_3061 (by simp [batch_61_06_values])
  exact h
theorem leaf_3061_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3061.profileLo box_3061.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3061_ok
theorem branch_box_3061_nonnegative : ∀ j, 0 ≤ branch_box_3061.lower j ∧ 0 ≤ branch_box_3061.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3061, Box.profileLo, Box.profileHi, box_3061]
theorem leaf_3061_BranchSafe : CertificateConsequences.BranchSafe branch_box_3061 := by
  left; refine ⟨branch_box_3061_nonnegative, ?_⟩
  intro z hz; exact leaf_3061_sound hz

theorem leaf_3062_ok : checkAt 527 1000 box_3062 cert_3062 = true := by
  have h := List.all_eq_true.mp batch_61_07_ok accepted_3062 (by simp [batch_61_07_values])
  exact h
theorem leaf_3062_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3062.profileLo box_3062.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3062_ok
theorem branch_box_3062_nonnegative : ∀ j, 0 ≤ branch_box_3062.lower j ∧ 0 ≤ branch_box_3062.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3062, Box.profileLo, Box.profileHi, box_3062]
theorem leaf_3062_BranchSafe : CertificateConsequences.BranchSafe branch_box_3062 := by
  left; refine ⟨branch_box_3062_nonnegative, ?_⟩
  intro z hz; exact leaf_3062_sound hz

theorem leaf_3063_ok : checkAt 527 1000 box_3063 cert_3063 = true := by
  have h := List.all_eq_true.mp batch_61_08_ok accepted_3063 (by simp [batch_61_08_values])
  exact h
theorem leaf_3063_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3063.profileLo box_3063.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3063_ok
theorem branch_box_3063_nonnegative : ∀ j, 0 ≤ branch_box_3063.lower j ∧ 0 ≤ branch_box_3063.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3063, Box.profileLo, Box.profileHi, box_3063]
theorem leaf_3063_BranchSafe : CertificateConsequences.BranchSafe branch_box_3063 := by
  left; refine ⟨branch_box_3063_nonnegative, ?_⟩
  intro z hz; exact leaf_3063_sound hz

theorem leaf_3064_ok : checkAt 527 1000 box_3064 cert_3064 = true := by
  have h := List.all_eq_true.mp batch_61_09_ok accepted_3064 (by simp [batch_61_09_values])
  exact h
theorem leaf_3064_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3064.profileLo box_3064.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3064_ok
theorem branch_box_3064_nonnegative : ∀ j, 0 ≤ branch_box_3064.lower j ∧ 0 ≤ branch_box_3064.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3064, Box.profileLo, Box.profileHi, box_3064]
theorem leaf_3064_BranchSafe : CertificateConsequences.BranchSafe branch_box_3064 := by
  left; refine ⟨branch_box_3064_nonnegative, ?_⟩
  intro z hz; exact leaf_3064_sound hz

theorem leaf_3067_ok : checkAt 527 1000 box_3067 cert_3067 = true := by
  have h := List.all_eq_true.mp batch_61_10_ok accepted_3067 (by simp [batch_61_10_values])
  exact h
theorem leaf_3067_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3067.profileLo box_3067.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3067_ok
theorem branch_box_3067_nonnegative : ∀ j, 0 ≤ branch_box_3067.lower j ∧ 0 ≤ branch_box_3067.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3067, Box.profileLo, Box.profileHi, box_3067]
theorem leaf_3067_BranchSafe : CertificateConsequences.BranchSafe branch_box_3067 := by
  left; refine ⟨branch_box_3067_nonnegative, ?_⟩
  intro z hz; exact leaf_3067_sound hz

theorem leaf_3069_ok : checkAt 527 1000 box_3069 cert_3069 = true := by
  have h := List.all_eq_true.mp batch_61_11_ok accepted_3069 (by simp [batch_61_11_values])
  exact h
theorem leaf_3069_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3069.profileLo box_3069.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3069_ok
theorem branch_box_3069_nonnegative : ∀ j, 0 ≤ branch_box_3069.lower j ∧ 0 ≤ branch_box_3069.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3069, Box.profileLo, Box.profileHi, box_3069]
theorem leaf_3069_BranchSafe : CertificateConsequences.BranchSafe branch_box_3069 := by
  left; refine ⟨branch_box_3069_nonnegative, ?_⟩
  intro z hz; exact leaf_3069_sound hz

theorem leaf_3071_ok : checkAt 527 1000 box_3071 cert_3071 = true := by
  have h := List.all_eq_true.mp batch_61_12_ok accepted_3071 (by simp [batch_61_12_values])
  exact h
theorem leaf_3071_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3071.profileLo box_3071.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3071_ok
theorem branch_box_3071_nonnegative : ∀ j, 0 ≤ branch_box_3071.lower j ∧ 0 ≤ branch_box_3071.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3071, Box.profileLo, Box.profileHi, box_3071]
theorem leaf_3071_BranchSafe : CertificateConsequences.BranchSafe branch_box_3071 := by
  left; refine ⟨branch_box_3071_nonnegative, ?_⟩
  intro z hz; exact leaf_3071_sound hz

theorem leaf_3072_ok : checkAt 527 1000 box_3072 cert_3072 = true := by
  have h := List.all_eq_true.mp batch_61_13_ok accepted_3072 (by simp [batch_61_13_values])
  exact h
theorem leaf_3072_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3072.profileLo box_3072.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3072_ok
theorem branch_box_3072_nonnegative : ∀ j, 0 ≤ branch_box_3072.lower j ∧ 0 ≤ branch_box_3072.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3072, Box.profileLo, Box.profileHi, box_3072]
theorem leaf_3072_BranchSafe : CertificateConsequences.BranchSafe branch_box_3072 := by
  left; refine ⟨branch_box_3072_nonnegative, ?_⟩
  intro z hz; exact leaf_3072_sound hz

theorem leaf_3077_ok : checkAt 527 1000 box_3077 cert_3077 = true := by
  have h := List.all_eq_true.mp batch_61_14_ok accepted_3077 (by simp [batch_61_14_values])
  exact h
theorem leaf_3077_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3077.profileLo box_3077.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3077_ok
theorem branch_box_3077_nonnegative : ∀ j, 0 ≤ branch_box_3077.lower j ∧ 0 ≤ branch_box_3077.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3077, Box.profileLo, Box.profileHi, box_3077]
theorem leaf_3077_BranchSafe : CertificateConsequences.BranchSafe branch_box_3077 := by
  left; refine ⟨branch_box_3077_nonnegative, ?_⟩
  intro z hz; exact leaf_3077_sound hz

theorem leaf_3078_ok : checkAt 527 1000 box_3078 cert_3078 = true := by
  have h := List.all_eq_true.mp batch_61_15_ok accepted_3078 (by simp [batch_61_15_values])
  exact h
theorem leaf_3078_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3078.profileLo box_3078.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3078_ok
theorem branch_box_3078_nonnegative : ∀ j, 0 ≤ branch_box_3078.lower j ∧ 0 ≤ branch_box_3078.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3078, Box.profileLo, Box.profileHi, box_3078]
theorem leaf_3078_BranchSafe : CertificateConsequences.BranchSafe branch_box_3078 := by
  left; refine ⟨branch_box_3078_nonnegative, ?_⟩
  intro z hz; exact leaf_3078_sound hz

theorem leaf_3079_ok : checkAt 527 1000 box_3079 cert_3079 = true := by
  have h := List.all_eq_true.mp batch_61_16_ok accepted_3079 (by simp [batch_61_16_values])
  exact h
theorem leaf_3079_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3079.profileLo box_3079.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3079_ok
theorem branch_box_3079_nonnegative : ∀ j, 0 ≤ branch_box_3079.lower j ∧ 0 ≤ branch_box_3079.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3079, Box.profileLo, Box.profileHi, box_3079]
theorem leaf_3079_BranchSafe : CertificateConsequences.BranchSafe branch_box_3079 := by
  left; refine ⟨branch_box_3079_nonnegative, ?_⟩
  intro z hz; exact leaf_3079_sound hz

theorem leaf_3080_ok : checkAt 527 1000 box_3080 cert_3080 = true := by
  have h := List.all_eq_true.mp batch_61_17_ok accepted_3080 (by simp [batch_61_17_values])
  exact h
theorem leaf_3080_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3080.profileLo box_3080.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3080_ok
theorem branch_box_3080_nonnegative : ∀ j, 0 ≤ branch_box_3080.lower j ∧ 0 ≤ branch_box_3080.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3080, Box.profileLo, Box.profileHi, box_3080]
theorem leaf_3080_BranchSafe : CertificateConsequences.BranchSafe branch_box_3080 := by
  left; refine ⟨branch_box_3080_nonnegative, ?_⟩
  intro z hz; exact leaf_3080_sound hz

theorem leaf_3085_ok : checkAt 527 1000 box_3085 cert_3085 = true := by
  have h := List.all_eq_true.mp batch_61_18_ok accepted_3085 (by simp [batch_61_18_values])
  exact h
theorem leaf_3085_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3085.profileLo box_3085.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3085_ok
theorem branch_box_3085_nonnegative : ∀ j, 0 ≤ branch_box_3085.lower j ∧ 0 ≤ branch_box_3085.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3085, Box.profileLo, Box.profileHi, box_3085]
theorem leaf_3085_BranchSafe : CertificateConsequences.BranchSafe branch_box_3085 := by
  left; refine ⟨branch_box_3085_nonnegative, ?_⟩
  intro z hz; exact leaf_3085_sound hz

theorem leaf_3086_ok : checkAt 527 1000 box_3086 cert_3086 = true := by
  have h := List.all_eq_true.mp batch_61_19_ok accepted_3086 (by simp [batch_61_19_values])
  exact h
theorem leaf_3086_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3086.profileLo box_3086.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3086_ok
theorem branch_box_3086_nonnegative : ∀ j, 0 ≤ branch_box_3086.lower j ∧ 0 ≤ branch_box_3086.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3086, Box.profileLo, Box.profileHi, box_3086]
theorem leaf_3086_BranchSafe : CertificateConsequences.BranchSafe branch_box_3086 := by
  left; refine ⟨branch_box_3086_nonnegative, ?_⟩
  intro z hz; exact leaf_3086_sound hz

theorem leaf_3087_ok : checkAt 527 1000 box_3087 cert_3087 = true := by
  have h := List.all_eq_true.mp batch_61_20_ok accepted_3087 (by simp [batch_61_20_values])
  exact h
theorem leaf_3087_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3087.profileLo box_3087.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3087_ok
theorem branch_box_3087_nonnegative : ∀ j, 0 ≤ branch_box_3087.lower j ∧ 0 ≤ branch_box_3087.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3087, Box.profileLo, Box.profileHi, box_3087]
theorem leaf_3087_BranchSafe : CertificateConsequences.BranchSafe branch_box_3087 := by
  left; refine ⟨branch_box_3087_nonnegative, ?_⟩
  intro z hz; exact leaf_3087_sound hz

theorem leaf_3088_ok : checkAt 527 1000 box_3088 cert_3088 = true := by
  have h := List.all_eq_true.mp batch_61_21_ok accepted_3088 (by simp [batch_61_21_values])
  exact h
theorem leaf_3088_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3088.profileLo box_3088.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3088_ok
theorem branch_box_3088_nonnegative : ∀ j, 0 ≤ branch_box_3088.lower j ∧ 0 ≤ branch_box_3088.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3088, Box.profileLo, Box.profileHi, box_3088]
theorem leaf_3088_BranchSafe : CertificateConsequences.BranchSafe branch_box_3088 := by
  left; refine ⟨branch_box_3088_nonnegative, ?_⟩
  intro z hz; exact leaf_3088_sound hz

theorem leaf_3089_ok : checkAt 527 1000 box_3089 cert_3089 = true := by
  have h := List.all_eq_true.mp batch_61_22_ok accepted_3089 (by simp [batch_61_22_values])
  exact h
theorem leaf_3089_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3089.profileLo box_3089.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3089_ok
theorem branch_box_3089_nonnegative : ∀ j, 0 ≤ branch_box_3089.lower j ∧ 0 ≤ branch_box_3089.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3089, Box.profileLo, Box.profileHi, box_3089]
theorem leaf_3089_BranchSafe : CertificateConsequences.BranchSafe branch_box_3089 := by
  left; refine ⟨branch_box_3089_nonnegative, ?_⟩
  intro z hz; exact leaf_3089_sound hz

theorem leaf_3092_ok : checkAt 527 1000 box_3092 cert_3092 = true := by
  have h := List.all_eq_true.mp batch_61_23_ok accepted_3092 (by simp [batch_61_23_values])
  exact h
theorem leaf_3092_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3092.profileLo box_3092.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3092_ok
theorem branch_box_3092_nonnegative : ∀ j, 0 ≤ branch_box_3092.lower j ∧ 0 ≤ branch_box_3092.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3092, Box.profileLo, Box.profileHi, box_3092]
theorem leaf_3092_BranchSafe : CertificateConsequences.BranchSafe branch_box_3092 := by
  left; refine ⟨branch_box_3092_nonnegative, ?_⟩
  intro z hz; exact leaf_3092_sound hz

theorem leaf_3094_ok : checkAt 527 1000 box_3094 cert_3094 = true := by
  have h := List.all_eq_true.mp batch_61_24_ok accepted_3094 (by simp [batch_61_24_values])
  exact h
theorem leaf_3094_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3094.profileLo box_3094.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3094_ok
theorem branch_box_3094_nonnegative : ∀ j, 0 ≤ branch_box_3094.lower j ∧ 0 ≤ branch_box_3094.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3094, Box.profileLo, Box.profileHi, box_3094]
theorem leaf_3094_BranchSafe : CertificateConsequences.BranchSafe branch_box_3094 := by
  left; refine ⟨branch_box_3094_nonnegative, ?_⟩
  intro z hz; exact leaf_3094_sound hz

theorem leaf_3096_ok : checkAt 527 1000 box_3096 cert_3096 = true := by
  have h := List.all_eq_true.mp batch_61_25_ok accepted_3096 (by simp [batch_61_25_values])
  exact h
theorem leaf_3096_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3096.profileLo box_3096.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3096_ok
theorem branch_box_3096_nonnegative : ∀ j, 0 ≤ branch_box_3096.lower j ∧ 0 ≤ branch_box_3096.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3096, Box.profileLo, Box.profileHi, box_3096]
theorem leaf_3096_BranchSafe : CertificateConsequences.BranchSafe branch_box_3096 := by
  left; refine ⟨branch_box_3096_nonnegative, ?_⟩
  intro z hz; exact leaf_3096_sound hz

theorem leaf_3097_ok : checkAt 527 1000 box_3097 cert_3097 = true := by
  have h := List.all_eq_true.mp batch_61_26_ok accepted_3097 (by simp [batch_61_26_values])
  exact h
theorem leaf_3097_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3097.profileLo box_3097.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3097_ok
theorem branch_box_3097_nonnegative : ∀ j, 0 ≤ branch_box_3097.lower j ∧ 0 ≤ branch_box_3097.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3097, Box.profileLo, Box.profileHi, box_3097]
theorem leaf_3097_BranchSafe : CertificateConsequences.BranchSafe branch_box_3097 := by
  left; refine ⟨branch_box_3097_nonnegative, ?_⟩
  intro z hz; exact leaf_3097_sound hz

theorem leaf_3099_ok : checkAt 527 1000 box_3099 cert_3099 = true := by
  have h := List.all_eq_true.mp batch_61_27_ok accepted_3099 (by simp [batch_61_27_values])
  exact h
theorem leaf_3099_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3099.profileLo box_3099.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3099_ok
theorem branch_box_3099_nonnegative : ∀ j, 0 ≤ branch_box_3099.lower j ∧ 0 ≤ branch_box_3099.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3099, Box.profileLo, Box.profileHi, box_3099]
theorem leaf_3099_BranchSafe : CertificateConsequences.BranchSafe branch_box_3099 := by
  left; refine ⟨branch_box_3099_nonnegative, ?_⟩
  intro z hz; exact leaf_3099_sound hz

#print axioms batch_61_00_ok
#print axioms leaf_3052_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
