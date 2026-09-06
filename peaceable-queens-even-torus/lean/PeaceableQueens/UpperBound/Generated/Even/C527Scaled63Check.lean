import PeaceableQueens.UpperBound.Generated.Even.C527Scaled63Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_63_00_values : List Bool := [accepted_3151]
theorem batch_63_00_ok : batch_63_00_values.all id = true := by decide

def batch_63_01_values : List Bool := [accepted_3154]
theorem batch_63_01_ok : batch_63_01_values.all id = true := by decide

def batch_63_02_values : List Bool := [accepted_3155]
theorem batch_63_02_ok : batch_63_02_values.all id = true := by decide

def batch_63_03_values : List Bool := [accepted_3156]
theorem batch_63_03_ok : batch_63_03_values.all id = true := by decide

def batch_63_04_values : List Bool := [accepted_3163]
theorem batch_63_04_ok : batch_63_04_values.all id = true := by decide

def batch_63_05_values : List Bool := [accepted_3164]
theorem batch_63_05_ok : batch_63_05_values.all id = true := by decide

def batch_63_06_values : List Bool := [accepted_3165]
theorem batch_63_06_ok : batch_63_06_values.all id = true := by decide

def batch_63_07_values : List Bool := [accepted_3166]
theorem batch_63_07_ok : batch_63_07_values.all id = true := by decide

def batch_63_08_values : List Bool := [accepted_3169]
theorem batch_63_08_ok : batch_63_08_values.all id = true := by decide

def batch_63_09_values : List Bool := [accepted_3170]
theorem batch_63_09_ok : batch_63_09_values.all id = true := by decide

def batch_63_10_values : List Bool := [accepted_3171]
theorem batch_63_10_ok : batch_63_10_values.all id = true := by decide

def batch_63_11_values : List Bool := [accepted_3172]
theorem batch_63_11_ok : batch_63_11_values.all id = true := by decide

def batch_63_12_values : List Bool := [accepted_3174]
theorem batch_63_12_ok : batch_63_12_values.all id = true := by decide

def batch_63_13_values : List Bool := [accepted_3175]
theorem batch_63_13_ok : batch_63_13_values.all id = true := by decide

def batch_63_14_values : List Bool := [accepted_3177]
theorem batch_63_14_ok : batch_63_14_values.all id = true := by decide

def batch_63_15_values : List Bool := [accepted_3179]
theorem batch_63_15_ok : batch_63_15_values.all id = true := by decide

def batch_63_16_values : List Bool := [accepted_3180]
theorem batch_63_16_ok : batch_63_16_values.all id = true := by decide

def batch_63_17_values : List Bool := [accepted_3189]
theorem batch_63_17_ok : batch_63_17_values.all id = true := by decide

def batch_63_18_values : List Bool := [accepted_3191]
theorem batch_63_18_ok : batch_63_18_values.all id = true := by decide

def batch_63_19_values : List Bool := [accepted_3192]
theorem batch_63_19_ok : batch_63_19_values.all id = true := by decide

def batch_63_20_values : List Bool := [accepted_3193]
theorem batch_63_20_ok : batch_63_20_values.all id = true := by decide

def batch_63_21_values : List Bool := [accepted_3194]
theorem batch_63_21_ok : batch_63_21_values.all id = true := by decide

def batch_63_22_values : List Bool := [accepted_3197]
theorem batch_63_22_ok : batch_63_22_values.all id = true := by decide

def batch_63_23_values : List Bool := [accepted_3198]
theorem batch_63_23_ok : batch_63_23_values.all id = true := by decide

def batch_63_24_values : List Bool := [accepted_3199]
theorem batch_63_24_ok : batch_63_24_values.all id = true := by decide

theorem leaf_3151_ok : checkAt 527 1000 box_3151 cert_3151 = true := by
  have h := List.all_eq_true.mp batch_63_00_ok accepted_3151 (by simp [batch_63_00_values])
  exact h
theorem leaf_3151_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3151.profileLo box_3151.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3151_ok
theorem branch_box_3151_nonnegative : ∀ j, 0 ≤ branch_box_3151.lower j ∧ 0 ≤ branch_box_3151.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3151, Box.profileLo, Box.profileHi, box_3151]
theorem leaf_3151_BranchSafe : CertificateConsequences.BranchSafe branch_box_3151 := by
  left; refine ⟨branch_box_3151_nonnegative, ?_⟩
  intro z hz; exact leaf_3151_sound hz

theorem leaf_3154_ok : checkAt 527 1000 box_3154 cert_3154 = true := by
  have h := List.all_eq_true.mp batch_63_01_ok accepted_3154 (by simp [batch_63_01_values])
  exact h
theorem leaf_3154_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3154.profileLo box_3154.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3154_ok
theorem branch_box_3154_nonnegative : ∀ j, 0 ≤ branch_box_3154.lower j ∧ 0 ≤ branch_box_3154.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3154, Box.profileLo, Box.profileHi, box_3154]
theorem leaf_3154_BranchSafe : CertificateConsequences.BranchSafe branch_box_3154 := by
  left; refine ⟨branch_box_3154_nonnegative, ?_⟩
  intro z hz; exact leaf_3154_sound hz

theorem leaf_3155_ok : checkAt 527 1000 box_3155 cert_3155 = true := by
  have h := List.all_eq_true.mp batch_63_02_ok accepted_3155 (by simp [batch_63_02_values])
  exact h
theorem leaf_3155_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3155.profileLo box_3155.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3155_ok
theorem branch_box_3155_nonnegative : ∀ j, 0 ≤ branch_box_3155.lower j ∧ 0 ≤ branch_box_3155.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3155, Box.profileLo, Box.profileHi, box_3155]
theorem leaf_3155_BranchSafe : CertificateConsequences.BranchSafe branch_box_3155 := by
  left; refine ⟨branch_box_3155_nonnegative, ?_⟩
  intro z hz; exact leaf_3155_sound hz

theorem leaf_3156_ok : checkAt 527 1000 box_3156 cert_3156 = true := by
  have h := List.all_eq_true.mp batch_63_03_ok accepted_3156 (by simp [batch_63_03_values])
  exact h
theorem leaf_3156_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3156.profileLo box_3156.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3156_ok
theorem branch_box_3156_nonnegative : ∀ j, 0 ≤ branch_box_3156.lower j ∧ 0 ≤ branch_box_3156.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3156, Box.profileLo, Box.profileHi, box_3156]
theorem leaf_3156_BranchSafe : CertificateConsequences.BranchSafe branch_box_3156 := by
  left; refine ⟨branch_box_3156_nonnegative, ?_⟩
  intro z hz; exact leaf_3156_sound hz

theorem leaf_3163_ok : checkAt 527 1000 box_3163 cert_3163 = true := by
  have h := List.all_eq_true.mp batch_63_04_ok accepted_3163 (by simp [batch_63_04_values])
  exact h
theorem leaf_3163_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3163.profileLo box_3163.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3163_ok
theorem branch_box_3163_nonnegative : ∀ j, 0 ≤ branch_box_3163.lower j ∧ 0 ≤ branch_box_3163.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3163, Box.profileLo, Box.profileHi, box_3163]
theorem leaf_3163_BranchSafe : CertificateConsequences.BranchSafe branch_box_3163 := by
  left; refine ⟨branch_box_3163_nonnegative, ?_⟩
  intro z hz; exact leaf_3163_sound hz

theorem leaf_3164_ok : checkAt 527 1000 box_3164 cert_3164 = true := by
  have h := List.all_eq_true.mp batch_63_05_ok accepted_3164 (by simp [batch_63_05_values])
  exact h
theorem leaf_3164_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3164.profileLo box_3164.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3164_ok
theorem branch_box_3164_nonnegative : ∀ j, 0 ≤ branch_box_3164.lower j ∧ 0 ≤ branch_box_3164.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3164, Box.profileLo, Box.profileHi, box_3164]
theorem leaf_3164_BranchSafe : CertificateConsequences.BranchSafe branch_box_3164 := by
  left; refine ⟨branch_box_3164_nonnegative, ?_⟩
  intro z hz; exact leaf_3164_sound hz

theorem leaf_3165_ok : checkAt 527 1000 box_3165 cert_3165 = true := by
  have h := List.all_eq_true.mp batch_63_06_ok accepted_3165 (by simp [batch_63_06_values])
  exact h
theorem leaf_3165_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3165.profileLo box_3165.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3165_ok
theorem branch_box_3165_nonnegative : ∀ j, 0 ≤ branch_box_3165.lower j ∧ 0 ≤ branch_box_3165.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3165, Box.profileLo, Box.profileHi, box_3165]
theorem leaf_3165_BranchSafe : CertificateConsequences.BranchSafe branch_box_3165 := by
  left; refine ⟨branch_box_3165_nonnegative, ?_⟩
  intro z hz; exact leaf_3165_sound hz

theorem leaf_3166_ok : checkAt 527 1000 box_3166 cert_3166 = true := by
  have h := List.all_eq_true.mp batch_63_07_ok accepted_3166 (by simp [batch_63_07_values])
  exact h
theorem leaf_3166_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3166.profileLo box_3166.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3166_ok
theorem branch_box_3166_nonnegative : ∀ j, 0 ≤ branch_box_3166.lower j ∧ 0 ≤ branch_box_3166.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3166, Box.profileLo, Box.profileHi, box_3166]
theorem leaf_3166_BranchSafe : CertificateConsequences.BranchSafe branch_box_3166 := by
  left; refine ⟨branch_box_3166_nonnegative, ?_⟩
  intro z hz; exact leaf_3166_sound hz

theorem leaf_3169_ok : checkAt 527 1000 box_3169 cert_3169 = true := by
  have h := List.all_eq_true.mp batch_63_08_ok accepted_3169 (by simp [batch_63_08_values])
  exact h
theorem leaf_3169_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3169.profileLo box_3169.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3169_ok
theorem branch_box_3169_nonnegative : ∀ j, 0 ≤ branch_box_3169.lower j ∧ 0 ≤ branch_box_3169.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3169, Box.profileLo, Box.profileHi, box_3169]
theorem leaf_3169_BranchSafe : CertificateConsequences.BranchSafe branch_box_3169 := by
  left; refine ⟨branch_box_3169_nonnegative, ?_⟩
  intro z hz; exact leaf_3169_sound hz

theorem leaf_3170_ok : checkAt 527 1000 box_3170 cert_3170 = true := by
  have h := List.all_eq_true.mp batch_63_09_ok accepted_3170 (by simp [batch_63_09_values])
  exact h
theorem leaf_3170_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3170.profileLo box_3170.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3170_ok
theorem branch_box_3170_nonnegative : ∀ j, 0 ≤ branch_box_3170.lower j ∧ 0 ≤ branch_box_3170.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3170, Box.profileLo, Box.profileHi, box_3170]
theorem leaf_3170_BranchSafe : CertificateConsequences.BranchSafe branch_box_3170 := by
  left; refine ⟨branch_box_3170_nonnegative, ?_⟩
  intro z hz; exact leaf_3170_sound hz

theorem leaf_3171_ok : checkAt 527 1000 box_3171 cert_3171 = true := by
  have h := List.all_eq_true.mp batch_63_10_ok accepted_3171 (by simp [batch_63_10_values])
  exact h
theorem leaf_3171_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3171.profileLo box_3171.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3171_ok
theorem branch_box_3171_nonnegative : ∀ j, 0 ≤ branch_box_3171.lower j ∧ 0 ≤ branch_box_3171.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3171, Box.profileLo, Box.profileHi, box_3171]
theorem leaf_3171_BranchSafe : CertificateConsequences.BranchSafe branch_box_3171 := by
  left; refine ⟨branch_box_3171_nonnegative, ?_⟩
  intro z hz; exact leaf_3171_sound hz

theorem leaf_3172_ok : checkAt 527 1000 box_3172 cert_3172 = true := by
  have h := List.all_eq_true.mp batch_63_11_ok accepted_3172 (by simp [batch_63_11_values])
  exact h
theorem leaf_3172_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3172.profileLo box_3172.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3172_ok
theorem branch_box_3172_nonnegative : ∀ j, 0 ≤ branch_box_3172.lower j ∧ 0 ≤ branch_box_3172.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3172, Box.profileLo, Box.profileHi, box_3172]
theorem leaf_3172_BranchSafe : CertificateConsequences.BranchSafe branch_box_3172 := by
  left; refine ⟨branch_box_3172_nonnegative, ?_⟩
  intro z hz; exact leaf_3172_sound hz

theorem leaf_3174_ok : checkAt 527 1000 box_3174 cert_3174 = true := by
  have h := List.all_eq_true.mp batch_63_12_ok accepted_3174 (by simp [batch_63_12_values])
  exact h
theorem leaf_3174_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3174.profileLo box_3174.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3174_ok
theorem branch_box_3174_nonnegative : ∀ j, 0 ≤ branch_box_3174.lower j ∧ 0 ≤ branch_box_3174.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3174, Box.profileLo, Box.profileHi, box_3174]
theorem leaf_3174_BranchSafe : CertificateConsequences.BranchSafe branch_box_3174 := by
  left; refine ⟨branch_box_3174_nonnegative, ?_⟩
  intro z hz; exact leaf_3174_sound hz

theorem leaf_3175_ok : checkAt 527 1000 box_3175 cert_3175 = true := by
  have h := List.all_eq_true.mp batch_63_13_ok accepted_3175 (by simp [batch_63_13_values])
  exact h
theorem leaf_3175_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3175.profileLo box_3175.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3175_ok
theorem branch_box_3175_nonnegative : ∀ j, 0 ≤ branch_box_3175.lower j ∧ 0 ≤ branch_box_3175.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3175, Box.profileLo, Box.profileHi, box_3175]
theorem leaf_3175_BranchSafe : CertificateConsequences.BranchSafe branch_box_3175 := by
  left; refine ⟨branch_box_3175_nonnegative, ?_⟩
  intro z hz; exact leaf_3175_sound hz

theorem leaf_3177_ok : checkAt 527 1000 box_3177 cert_3177 = true := by
  have h := List.all_eq_true.mp batch_63_14_ok accepted_3177 (by simp [batch_63_14_values])
  exact h
theorem leaf_3177_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3177.profileLo box_3177.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3177_ok
theorem branch_box_3177_nonnegative : ∀ j, 0 ≤ branch_box_3177.lower j ∧ 0 ≤ branch_box_3177.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3177, Box.profileLo, Box.profileHi, box_3177]
theorem leaf_3177_BranchSafe : CertificateConsequences.BranchSafe branch_box_3177 := by
  left; refine ⟨branch_box_3177_nonnegative, ?_⟩
  intro z hz; exact leaf_3177_sound hz

theorem leaf_3179_ok : checkAt 527 1000 box_3179 cert_3179 = true := by
  have h := List.all_eq_true.mp batch_63_15_ok accepted_3179 (by simp [batch_63_15_values])
  exact h
theorem leaf_3179_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3179.profileLo box_3179.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3179_ok
theorem branch_box_3179_nonnegative : ∀ j, 0 ≤ branch_box_3179.lower j ∧ 0 ≤ branch_box_3179.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3179, Box.profileLo, Box.profileHi, box_3179]
theorem leaf_3179_BranchSafe : CertificateConsequences.BranchSafe branch_box_3179 := by
  left; refine ⟨branch_box_3179_nonnegative, ?_⟩
  intro z hz; exact leaf_3179_sound hz

theorem leaf_3180_ok : checkAt 527 1000 box_3180 cert_3180 = true := by
  have h := List.all_eq_true.mp batch_63_16_ok accepted_3180 (by simp [batch_63_16_values])
  exact h
theorem leaf_3180_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3180.profileLo box_3180.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3180_ok
theorem branch_box_3180_nonnegative : ∀ j, 0 ≤ branch_box_3180.lower j ∧ 0 ≤ branch_box_3180.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3180, Box.profileLo, Box.profileHi, box_3180]
theorem leaf_3180_BranchSafe : CertificateConsequences.BranchSafe branch_box_3180 := by
  left; refine ⟨branch_box_3180_nonnegative, ?_⟩
  intro z hz; exact leaf_3180_sound hz

theorem leaf_3189_ok : checkAt 527 1000 box_3189 cert_3189 = true := by
  have h := List.all_eq_true.mp batch_63_17_ok accepted_3189 (by simp [batch_63_17_values])
  exact h
theorem leaf_3189_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3189.profileLo box_3189.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3189_ok
theorem branch_box_3189_nonnegative : ∀ j, 0 ≤ branch_box_3189.lower j ∧ 0 ≤ branch_box_3189.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3189, Box.profileLo, Box.profileHi, box_3189]
theorem leaf_3189_BranchSafe : CertificateConsequences.BranchSafe branch_box_3189 := by
  left; refine ⟨branch_box_3189_nonnegative, ?_⟩
  intro z hz; exact leaf_3189_sound hz

theorem leaf_3191_ok : checkAt 527 1000 box_3191 cert_3191 = true := by
  have h := List.all_eq_true.mp batch_63_18_ok accepted_3191 (by simp [batch_63_18_values])
  exact h
theorem leaf_3191_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3191.profileLo box_3191.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3191_ok
theorem branch_box_3191_nonnegative : ∀ j, 0 ≤ branch_box_3191.lower j ∧ 0 ≤ branch_box_3191.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3191, Box.profileLo, Box.profileHi, box_3191]
theorem leaf_3191_BranchSafe : CertificateConsequences.BranchSafe branch_box_3191 := by
  left; refine ⟨branch_box_3191_nonnegative, ?_⟩
  intro z hz; exact leaf_3191_sound hz

theorem leaf_3192_ok : checkAt 527 1000 box_3192 cert_3192 = true := by
  have h := List.all_eq_true.mp batch_63_19_ok accepted_3192 (by simp [batch_63_19_values])
  exact h
theorem leaf_3192_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3192.profileLo box_3192.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3192_ok
theorem branch_box_3192_nonnegative : ∀ j, 0 ≤ branch_box_3192.lower j ∧ 0 ≤ branch_box_3192.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3192, Box.profileLo, Box.profileHi, box_3192]
theorem leaf_3192_BranchSafe : CertificateConsequences.BranchSafe branch_box_3192 := by
  left; refine ⟨branch_box_3192_nonnegative, ?_⟩
  intro z hz; exact leaf_3192_sound hz

theorem leaf_3193_ok : checkAt 527 1000 box_3193 cert_3193 = true := by
  have h := List.all_eq_true.mp batch_63_20_ok accepted_3193 (by simp [batch_63_20_values])
  exact h
theorem leaf_3193_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3193.profileLo box_3193.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3193_ok
theorem branch_box_3193_nonnegative : ∀ j, 0 ≤ branch_box_3193.lower j ∧ 0 ≤ branch_box_3193.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3193, Box.profileLo, Box.profileHi, box_3193]
theorem leaf_3193_BranchSafe : CertificateConsequences.BranchSafe branch_box_3193 := by
  left; refine ⟨branch_box_3193_nonnegative, ?_⟩
  intro z hz; exact leaf_3193_sound hz

theorem leaf_3194_ok : checkAt 527 1000 box_3194 cert_3194 = true := by
  have h := List.all_eq_true.mp batch_63_21_ok accepted_3194 (by simp [batch_63_21_values])
  exact h
theorem leaf_3194_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3194.profileLo box_3194.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3194_ok
theorem branch_box_3194_nonnegative : ∀ j, 0 ≤ branch_box_3194.lower j ∧ 0 ≤ branch_box_3194.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3194, Box.profileLo, Box.profileHi, box_3194]
theorem leaf_3194_BranchSafe : CertificateConsequences.BranchSafe branch_box_3194 := by
  left; refine ⟨branch_box_3194_nonnegative, ?_⟩
  intro z hz; exact leaf_3194_sound hz

theorem leaf_3197_ok : checkAt 527 1000 box_3197 cert_3197 = true := by
  have h := List.all_eq_true.mp batch_63_22_ok accepted_3197 (by simp [batch_63_22_values])
  exact h
theorem leaf_3197_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3197.profileLo box_3197.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3197_ok
theorem branch_box_3197_nonnegative : ∀ j, 0 ≤ branch_box_3197.lower j ∧ 0 ≤ branch_box_3197.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3197, Box.profileLo, Box.profileHi, box_3197]
theorem leaf_3197_BranchSafe : CertificateConsequences.BranchSafe branch_box_3197 := by
  left; refine ⟨branch_box_3197_nonnegative, ?_⟩
  intro z hz; exact leaf_3197_sound hz

theorem leaf_3198_ok : checkAt 527 1000 box_3198 cert_3198 = true := by
  have h := List.all_eq_true.mp batch_63_23_ok accepted_3198 (by simp [batch_63_23_values])
  exact h
theorem leaf_3198_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3198.profileLo box_3198.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3198_ok
theorem branch_box_3198_nonnegative : ∀ j, 0 ≤ branch_box_3198.lower j ∧ 0 ≤ branch_box_3198.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3198, Box.profileLo, Box.profileHi, box_3198]
theorem leaf_3198_BranchSafe : CertificateConsequences.BranchSafe branch_box_3198 := by
  left; refine ⟨branch_box_3198_nonnegative, ?_⟩
  intro z hz; exact leaf_3198_sound hz

theorem leaf_3199_ok : checkAt 527 1000 box_3199 cert_3199 = true := by
  have h := List.all_eq_true.mp batch_63_24_ok accepted_3199 (by simp [batch_63_24_values])
  exact h
theorem leaf_3199_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3199.profileLo box_3199.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3199_ok
theorem branch_box_3199_nonnegative : ∀ j, 0 ≤ branch_box_3199.lower j ∧ 0 ≤ branch_box_3199.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3199, Box.profileLo, Box.profileHi, box_3199]
theorem leaf_3199_BranchSafe : CertificateConsequences.BranchSafe branch_box_3199 := by
  left; refine ⟨branch_box_3199_nonnegative, ?_⟩
  intro z hz; exact leaf_3199_sound hz

#print axioms batch_63_00_ok
#print axioms leaf_3151_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
