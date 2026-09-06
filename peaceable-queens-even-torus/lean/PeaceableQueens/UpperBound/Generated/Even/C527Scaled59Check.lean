import PeaceableQueens.UpperBound.Generated.Even.C527Scaled59Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_59_00_values : List Bool := [accepted_2953]
theorem batch_59_00_ok : batch_59_00_values.all id = true := by decide

def batch_59_01_values : List Bool := [accepted_2955]
theorem batch_59_01_ok : batch_59_01_values.all id = true := by decide

def batch_59_02_values : List Bool := [accepted_2956]
theorem batch_59_02_ok : batch_59_02_values.all id = true := by decide

def batch_59_03_values : List Bool := [accepted_2959]
theorem batch_59_03_ok : batch_59_03_values.all id = true := by decide

def batch_59_04_values : List Bool := [accepted_2960]
theorem batch_59_04_ok : batch_59_04_values.all id = true := by decide

def batch_59_05_values : List Bool := [accepted_2961]
theorem batch_59_05_ok : batch_59_05_values.all id = true := by decide

def batch_59_06_values : List Bool := [accepted_2962]
theorem batch_59_06_ok : batch_59_06_values.all id = true := by decide

def batch_59_07_values : List Bool := [accepted_2968]
theorem batch_59_07_ok : batch_59_07_values.all id = true := by decide

def batch_59_08_values : List Bool := [accepted_2969]
theorem batch_59_08_ok : batch_59_08_values.all id = true := by decide

def batch_59_09_values : List Bool := [accepted_2970]
theorem batch_59_09_ok : batch_59_09_values.all id = true := by decide

def batch_59_10_values : List Bool := [accepted_2974]
theorem batch_59_10_ok : batch_59_10_values.all id = true := by decide

def batch_59_11_values : List Bool := [accepted_2975]
theorem batch_59_11_ok : batch_59_11_values.all id = true := by decide

def batch_59_12_values : List Bool := [accepted_2976]
theorem batch_59_12_ok : batch_59_12_values.all id = true := by decide

def batch_59_13_values : List Bool := [accepted_2977]
theorem batch_59_13_ok : batch_59_13_values.all id = true := by decide

def batch_59_14_values : List Bool := [accepted_2978]
theorem batch_59_14_ok : batch_59_14_values.all id = true := by decide

def batch_59_15_values : List Bool := [accepted_2981]
theorem batch_59_15_ok : batch_59_15_values.all id = true := by decide

def batch_59_16_values : List Bool := [accepted_2982]
theorem batch_59_16_ok : batch_59_16_values.all id = true := by decide

def batch_59_17_values : List Bool := [accepted_2986]
theorem batch_59_17_ok : batch_59_17_values.all id = true := by decide

def batch_59_18_values : List Bool := [accepted_2988]
theorem batch_59_18_ok : batch_59_18_values.all id = true := by decide

def batch_59_19_values : List Bool := [accepted_2989]
theorem batch_59_19_ok : batch_59_19_values.all id = true := by decide

def batch_59_20_values : List Bool := [accepted_2990]
theorem batch_59_20_ok : batch_59_20_values.all id = true := by decide

def batch_59_21_values : List Bool := [accepted_2993]
theorem batch_59_21_ok : batch_59_21_values.all id = true := by decide

def batch_59_22_values : List Bool := [accepted_2994]
theorem batch_59_22_ok : batch_59_22_values.all id = true := by decide

def batch_59_23_values : List Bool := [accepted_2996]
theorem batch_59_23_ok : batch_59_23_values.all id = true := by decide

def batch_59_24_values : List Bool := [accepted_2998]
theorem batch_59_24_ok : batch_59_24_values.all id = true := by decide

def batch_59_25_values : List Bool := [accepted_2999]
theorem batch_59_25_ok : batch_59_25_values.all id = true := by decide

theorem leaf_2953_ok : checkAt 527 1000 box_2953 cert_2953 = true := by
  have h := List.all_eq_true.mp batch_59_00_ok accepted_2953 (by simp [batch_59_00_values])
  exact h
theorem leaf_2953_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2953.profileLo box_2953.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2953_ok
theorem branch_box_2953_nonnegative : ∀ j, 0 ≤ branch_box_2953.lower j ∧ 0 ≤ branch_box_2953.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2953, Box.profileLo, Box.profileHi, box_2953]
theorem leaf_2953_BranchSafe : CertificateConsequences.BranchSafe branch_box_2953 := by
  left; refine ⟨branch_box_2953_nonnegative, ?_⟩
  intro z hz; exact leaf_2953_sound hz

theorem leaf_2955_ok : checkAt 527 1000 box_2955 cert_2955 = true := by
  have h := List.all_eq_true.mp batch_59_01_ok accepted_2955 (by simp [batch_59_01_values])
  exact h
theorem leaf_2955_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2955.profileLo box_2955.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2955_ok
theorem branch_box_2955_nonnegative : ∀ j, 0 ≤ branch_box_2955.lower j ∧ 0 ≤ branch_box_2955.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2955, Box.profileLo, Box.profileHi, box_2955]
theorem leaf_2955_BranchSafe : CertificateConsequences.BranchSafe branch_box_2955 := by
  left; refine ⟨branch_box_2955_nonnegative, ?_⟩
  intro z hz; exact leaf_2955_sound hz

theorem leaf_2956_ok : checkAt 527 1000 box_2956 cert_2956 = true := by
  have h := List.all_eq_true.mp batch_59_02_ok accepted_2956 (by simp [batch_59_02_values])
  exact h
theorem leaf_2956_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2956.profileLo box_2956.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2956_ok
theorem branch_box_2956_nonnegative : ∀ j, 0 ≤ branch_box_2956.lower j ∧ 0 ≤ branch_box_2956.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2956, Box.profileLo, Box.profileHi, box_2956]
theorem leaf_2956_BranchSafe : CertificateConsequences.BranchSafe branch_box_2956 := by
  left; refine ⟨branch_box_2956_nonnegative, ?_⟩
  intro z hz; exact leaf_2956_sound hz

theorem leaf_2959_ok : checkAt 527 1000 box_2959 cert_2959 = true := by
  have h := List.all_eq_true.mp batch_59_03_ok accepted_2959 (by simp [batch_59_03_values])
  exact h
theorem leaf_2959_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2959.profileLo box_2959.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2959_ok
theorem branch_box_2959_nonnegative : ∀ j, 0 ≤ branch_box_2959.lower j ∧ 0 ≤ branch_box_2959.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2959, Box.profileLo, Box.profileHi, box_2959]
theorem leaf_2959_BranchSafe : CertificateConsequences.BranchSafe branch_box_2959 := by
  left; refine ⟨branch_box_2959_nonnegative, ?_⟩
  intro z hz; exact leaf_2959_sound hz

theorem leaf_2960_ok : checkAt 527 1000 box_2960 cert_2960 = true := by
  have h := List.all_eq_true.mp batch_59_04_ok accepted_2960 (by simp [batch_59_04_values])
  exact h
theorem leaf_2960_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2960.profileLo box_2960.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2960_ok
theorem branch_box_2960_nonnegative : ∀ j, 0 ≤ branch_box_2960.lower j ∧ 0 ≤ branch_box_2960.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2960, Box.profileLo, Box.profileHi, box_2960]
theorem leaf_2960_BranchSafe : CertificateConsequences.BranchSafe branch_box_2960 := by
  left; refine ⟨branch_box_2960_nonnegative, ?_⟩
  intro z hz; exact leaf_2960_sound hz

theorem leaf_2961_ok : checkAt 527 1000 box_2961 cert_2961 = true := by
  have h := List.all_eq_true.mp batch_59_05_ok accepted_2961 (by simp [batch_59_05_values])
  exact h
theorem leaf_2961_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2961.profileLo box_2961.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2961_ok
theorem branch_box_2961_nonnegative : ∀ j, 0 ≤ branch_box_2961.lower j ∧ 0 ≤ branch_box_2961.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2961, Box.profileLo, Box.profileHi, box_2961]
theorem leaf_2961_BranchSafe : CertificateConsequences.BranchSafe branch_box_2961 := by
  left; refine ⟨branch_box_2961_nonnegative, ?_⟩
  intro z hz; exact leaf_2961_sound hz

theorem leaf_2962_ok : checkAt 527 1000 box_2962 cert_2962 = true := by
  have h := List.all_eq_true.mp batch_59_06_ok accepted_2962 (by simp [batch_59_06_values])
  exact h
theorem leaf_2962_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2962.profileLo box_2962.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2962_ok
theorem branch_box_2962_nonnegative : ∀ j, 0 ≤ branch_box_2962.lower j ∧ 0 ≤ branch_box_2962.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2962, Box.profileLo, Box.profileHi, box_2962]
theorem leaf_2962_BranchSafe : CertificateConsequences.BranchSafe branch_box_2962 := by
  left; refine ⟨branch_box_2962_nonnegative, ?_⟩
  intro z hz; exact leaf_2962_sound hz

theorem leaf_2968_ok : checkAt 527 1000 box_2968 cert_2968 = true := by
  have h := List.all_eq_true.mp batch_59_07_ok accepted_2968 (by simp [batch_59_07_values])
  exact h
theorem leaf_2968_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2968.profileLo box_2968.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2968_ok
theorem branch_box_2968_nonnegative : ∀ j, 0 ≤ branch_box_2968.lower j ∧ 0 ≤ branch_box_2968.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2968, Box.profileLo, Box.profileHi, box_2968]
theorem leaf_2968_BranchSafe : CertificateConsequences.BranchSafe branch_box_2968 := by
  left; refine ⟨branch_box_2968_nonnegative, ?_⟩
  intro z hz; exact leaf_2968_sound hz

theorem leaf_2969_ok : checkAt 527 1000 box_2969 cert_2969 = true := by
  have h := List.all_eq_true.mp batch_59_08_ok accepted_2969 (by simp [batch_59_08_values])
  exact h
theorem leaf_2969_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2969.profileLo box_2969.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2969_ok
theorem branch_box_2969_nonnegative : ∀ j, 0 ≤ branch_box_2969.lower j ∧ 0 ≤ branch_box_2969.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2969, Box.profileLo, Box.profileHi, box_2969]
theorem leaf_2969_BranchSafe : CertificateConsequences.BranchSafe branch_box_2969 := by
  left; refine ⟨branch_box_2969_nonnegative, ?_⟩
  intro z hz; exact leaf_2969_sound hz

theorem leaf_2970_ok : checkAt 527 1000 box_2970 cert_2970 = true := by
  have h := List.all_eq_true.mp batch_59_09_ok accepted_2970 (by simp [batch_59_09_values])
  exact h
theorem leaf_2970_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2970.profileLo box_2970.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2970_ok
theorem branch_box_2970_nonnegative : ∀ j, 0 ≤ branch_box_2970.lower j ∧ 0 ≤ branch_box_2970.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2970, Box.profileLo, Box.profileHi, box_2970]
theorem leaf_2970_BranchSafe : CertificateConsequences.BranchSafe branch_box_2970 := by
  left; refine ⟨branch_box_2970_nonnegative, ?_⟩
  intro z hz; exact leaf_2970_sound hz

theorem leaf_2974_ok : checkAt 527 1000 box_2974 cert_2974 = true := by
  have h := List.all_eq_true.mp batch_59_10_ok accepted_2974 (by simp [batch_59_10_values])
  exact h
theorem leaf_2974_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2974.profileLo box_2974.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2974_ok
theorem branch_box_2974_nonnegative : ∀ j, 0 ≤ branch_box_2974.lower j ∧ 0 ≤ branch_box_2974.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2974, Box.profileLo, Box.profileHi, box_2974]
theorem leaf_2974_BranchSafe : CertificateConsequences.BranchSafe branch_box_2974 := by
  left; refine ⟨branch_box_2974_nonnegative, ?_⟩
  intro z hz; exact leaf_2974_sound hz

theorem leaf_2975_ok : checkAt 527 1000 box_2975 cert_2975 = true := by
  have h := List.all_eq_true.mp batch_59_11_ok accepted_2975 (by simp [batch_59_11_values])
  exact h
theorem leaf_2975_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2975.profileLo box_2975.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2975_ok
theorem branch_box_2975_nonnegative : ∀ j, 0 ≤ branch_box_2975.lower j ∧ 0 ≤ branch_box_2975.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2975, Box.profileLo, Box.profileHi, box_2975]
theorem leaf_2975_BranchSafe : CertificateConsequences.BranchSafe branch_box_2975 := by
  left; refine ⟨branch_box_2975_nonnegative, ?_⟩
  intro z hz; exact leaf_2975_sound hz

theorem leaf_2976_ok : checkAt 527 1000 box_2976 cert_2976 = true := by
  have h := List.all_eq_true.mp batch_59_12_ok accepted_2976 (by simp [batch_59_12_values])
  exact h
theorem leaf_2976_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2976.profileLo box_2976.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2976_ok
theorem branch_box_2976_nonnegative : ∀ j, 0 ≤ branch_box_2976.lower j ∧ 0 ≤ branch_box_2976.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2976, Box.profileLo, Box.profileHi, box_2976]
theorem leaf_2976_BranchSafe : CertificateConsequences.BranchSafe branch_box_2976 := by
  left; refine ⟨branch_box_2976_nonnegative, ?_⟩
  intro z hz; exact leaf_2976_sound hz

theorem leaf_2977_ok : checkAt 527 1000 box_2977 cert_2977 = true := by
  have h := List.all_eq_true.mp batch_59_13_ok accepted_2977 (by simp [batch_59_13_values])
  exact h
theorem leaf_2977_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2977.profileLo box_2977.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2977_ok
theorem branch_box_2977_nonnegative : ∀ j, 0 ≤ branch_box_2977.lower j ∧ 0 ≤ branch_box_2977.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2977, Box.profileLo, Box.profileHi, box_2977]
theorem leaf_2977_BranchSafe : CertificateConsequences.BranchSafe branch_box_2977 := by
  left; refine ⟨branch_box_2977_nonnegative, ?_⟩
  intro z hz; exact leaf_2977_sound hz

theorem leaf_2978_ok : checkAt 527 1000 box_2978 cert_2978 = true := by
  have h := List.all_eq_true.mp batch_59_14_ok accepted_2978 (by simp [batch_59_14_values])
  exact h
theorem leaf_2978_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2978.profileLo box_2978.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2978_ok
theorem branch_box_2978_nonnegative : ∀ j, 0 ≤ branch_box_2978.lower j ∧ 0 ≤ branch_box_2978.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2978, Box.profileLo, Box.profileHi, box_2978]
theorem leaf_2978_BranchSafe : CertificateConsequences.BranchSafe branch_box_2978 := by
  left; refine ⟨branch_box_2978_nonnegative, ?_⟩
  intro z hz; exact leaf_2978_sound hz

theorem leaf_2981_ok : checkAt 527 1000 box_2981 cert_2981 = true := by
  have h := List.all_eq_true.mp batch_59_15_ok accepted_2981 (by simp [batch_59_15_values])
  exact h
theorem leaf_2981_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2981.profileLo box_2981.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2981_ok
theorem branch_box_2981_nonnegative : ∀ j, 0 ≤ branch_box_2981.lower j ∧ 0 ≤ branch_box_2981.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2981, Box.profileLo, Box.profileHi, box_2981]
theorem leaf_2981_BranchSafe : CertificateConsequences.BranchSafe branch_box_2981 := by
  left; refine ⟨branch_box_2981_nonnegative, ?_⟩
  intro z hz; exact leaf_2981_sound hz

theorem leaf_2982_ok : checkAt 527 1000 box_2982 cert_2982 = true := by
  have h := List.all_eq_true.mp batch_59_16_ok accepted_2982 (by simp [batch_59_16_values])
  exact h
theorem leaf_2982_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2982.profileLo box_2982.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2982_ok
theorem branch_box_2982_nonnegative : ∀ j, 0 ≤ branch_box_2982.lower j ∧ 0 ≤ branch_box_2982.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2982, Box.profileLo, Box.profileHi, box_2982]
theorem leaf_2982_BranchSafe : CertificateConsequences.BranchSafe branch_box_2982 := by
  left; refine ⟨branch_box_2982_nonnegative, ?_⟩
  intro z hz; exact leaf_2982_sound hz

theorem leaf_2986_ok : checkAt 527 1000 box_2986 cert_2986 = true := by
  have h := List.all_eq_true.mp batch_59_17_ok accepted_2986 (by simp [batch_59_17_values])
  exact h
theorem leaf_2986_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2986.profileLo box_2986.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2986_ok
theorem branch_box_2986_nonnegative : ∀ j, 0 ≤ branch_box_2986.lower j ∧ 0 ≤ branch_box_2986.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2986, Box.profileLo, Box.profileHi, box_2986]
theorem leaf_2986_BranchSafe : CertificateConsequences.BranchSafe branch_box_2986 := by
  left; refine ⟨branch_box_2986_nonnegative, ?_⟩
  intro z hz; exact leaf_2986_sound hz

theorem leaf_2988_ok : checkAt 527 1000 box_2988 cert_2988 = true := by
  have h := List.all_eq_true.mp batch_59_18_ok accepted_2988 (by simp [batch_59_18_values])
  exact h
theorem leaf_2988_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2988.profileLo box_2988.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2988_ok
theorem branch_box_2988_nonnegative : ∀ j, 0 ≤ branch_box_2988.lower j ∧ 0 ≤ branch_box_2988.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2988, Box.profileLo, Box.profileHi, box_2988]
theorem leaf_2988_BranchSafe : CertificateConsequences.BranchSafe branch_box_2988 := by
  left; refine ⟨branch_box_2988_nonnegative, ?_⟩
  intro z hz; exact leaf_2988_sound hz

theorem leaf_2989_ok : checkAt 527 1000 box_2989 cert_2989 = true := by
  have h := List.all_eq_true.mp batch_59_19_ok accepted_2989 (by simp [batch_59_19_values])
  exact h
theorem leaf_2989_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2989.profileLo box_2989.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2989_ok
theorem branch_box_2989_nonnegative : ∀ j, 0 ≤ branch_box_2989.lower j ∧ 0 ≤ branch_box_2989.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2989, Box.profileLo, Box.profileHi, box_2989]
theorem leaf_2989_BranchSafe : CertificateConsequences.BranchSafe branch_box_2989 := by
  left; refine ⟨branch_box_2989_nonnegative, ?_⟩
  intro z hz; exact leaf_2989_sound hz

theorem leaf_2990_ok : checkAt 527 1000 box_2990 cert_2990 = true := by
  have h := List.all_eq_true.mp batch_59_20_ok accepted_2990 (by simp [batch_59_20_values])
  exact h
theorem leaf_2990_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2990.profileLo box_2990.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2990_ok
theorem branch_box_2990_nonnegative : ∀ j, 0 ≤ branch_box_2990.lower j ∧ 0 ≤ branch_box_2990.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2990, Box.profileLo, Box.profileHi, box_2990]
theorem leaf_2990_BranchSafe : CertificateConsequences.BranchSafe branch_box_2990 := by
  left; refine ⟨branch_box_2990_nonnegative, ?_⟩
  intro z hz; exact leaf_2990_sound hz

theorem leaf_2993_ok : checkAt 527 1000 box_2993 cert_2993 = true := by
  have h := List.all_eq_true.mp batch_59_21_ok accepted_2993 (by simp [batch_59_21_values])
  exact h
theorem leaf_2993_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2993.profileLo box_2993.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2993_ok
theorem branch_box_2993_nonnegative : ∀ j, 0 ≤ branch_box_2993.lower j ∧ 0 ≤ branch_box_2993.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2993, Box.profileLo, Box.profileHi, box_2993]
theorem leaf_2993_BranchSafe : CertificateConsequences.BranchSafe branch_box_2993 := by
  left; refine ⟨branch_box_2993_nonnegative, ?_⟩
  intro z hz; exact leaf_2993_sound hz

theorem leaf_2994_ok : checkAt 527 1000 box_2994 cert_2994 = true := by
  have h := List.all_eq_true.mp batch_59_22_ok accepted_2994 (by simp [batch_59_22_values])
  exact h
theorem leaf_2994_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2994.profileLo box_2994.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2994_ok
theorem branch_box_2994_nonnegative : ∀ j, 0 ≤ branch_box_2994.lower j ∧ 0 ≤ branch_box_2994.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2994, Box.profileLo, Box.profileHi, box_2994]
theorem leaf_2994_BranchSafe : CertificateConsequences.BranchSafe branch_box_2994 := by
  left; refine ⟨branch_box_2994_nonnegative, ?_⟩
  intro z hz; exact leaf_2994_sound hz

theorem leaf_2996_ok : checkAt 527 1000 box_2996 cert_2996 = true := by
  have h := List.all_eq_true.mp batch_59_23_ok accepted_2996 (by simp [batch_59_23_values])
  exact h
theorem leaf_2996_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2996.profileLo box_2996.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2996_ok
theorem branch_box_2996_nonnegative : ∀ j, 0 ≤ branch_box_2996.lower j ∧ 0 ≤ branch_box_2996.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2996, Box.profileLo, Box.profileHi, box_2996]
theorem leaf_2996_BranchSafe : CertificateConsequences.BranchSafe branch_box_2996 := by
  left; refine ⟨branch_box_2996_nonnegative, ?_⟩
  intro z hz; exact leaf_2996_sound hz

theorem leaf_2998_ok : checkAt 527 1000 box_2998 cert_2998 = true := by
  have h := List.all_eq_true.mp batch_59_24_ok accepted_2998 (by simp [batch_59_24_values])
  exact h
theorem leaf_2998_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2998.profileLo box_2998.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2998_ok
theorem branch_box_2998_nonnegative : ∀ j, 0 ≤ branch_box_2998.lower j ∧ 0 ≤ branch_box_2998.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2998, Box.profileLo, Box.profileHi, box_2998]
theorem leaf_2998_BranchSafe : CertificateConsequences.BranchSafe branch_box_2998 := by
  left; refine ⟨branch_box_2998_nonnegative, ?_⟩
  intro z hz; exact leaf_2998_sound hz

theorem leaf_2999_ok : checkAt 527 1000 box_2999 cert_2999 = true := by
  have h := List.all_eq_true.mp batch_59_25_ok accepted_2999 (by simp [batch_59_25_values])
  exact h
theorem leaf_2999_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2999.profileLo box_2999.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2999_ok
theorem branch_box_2999_nonnegative : ∀ j, 0 ≤ branch_box_2999.lower j ∧ 0 ≤ branch_box_2999.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2999, Box.profileLo, Box.profileHi, box_2999]
theorem leaf_2999_BranchSafe : CertificateConsequences.BranchSafe branch_box_2999 := by
  left; refine ⟨branch_box_2999_nonnegative, ?_⟩
  intro z hz; exact leaf_2999_sound hz

#print axioms batch_59_00_ok
#print axioms leaf_2953_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
