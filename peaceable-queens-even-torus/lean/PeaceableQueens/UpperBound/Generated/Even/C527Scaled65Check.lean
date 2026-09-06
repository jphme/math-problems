import PeaceableQueens.UpperBound.Generated.Even.C527Scaled65Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_65_00_values : List Bool := [accepted_3250]
theorem batch_65_00_ok : batch_65_00_values.all id = true := by decide

def batch_65_01_values : List Bool := [accepted_3256]
theorem batch_65_01_ok : batch_65_01_values.all id = true := by decide

def batch_65_02_values : List Bool := [accepted_3257]
theorem batch_65_02_ok : batch_65_02_values.all id = true := by decide

def batch_65_03_values : List Bool := [accepted_3258]
theorem batch_65_03_ok : batch_65_03_values.all id = true := by decide

def batch_65_04_values : List Bool := [accepted_3259]
theorem batch_65_04_ok : batch_65_04_values.all id = true := by decide

def batch_65_05_values : List Bool := [accepted_3262]
theorem batch_65_05_ok : batch_65_05_values.all id = true := by decide

def batch_65_06_values : List Bool := [accepted_3263]
theorem batch_65_06_ok : batch_65_06_values.all id = true := by decide

def batch_65_07_values : List Bool := [accepted_3264]
theorem batch_65_07_ok : batch_65_07_values.all id = true := by decide

def batch_65_08_values : List Bool := [accepted_3269]
theorem batch_65_08_ok : batch_65_08_values.all id = true := by decide

def batch_65_09_values : List Bool := [accepted_3270]
theorem batch_65_09_ok : batch_65_09_values.all id = true := by decide

def batch_65_10_values : List Bool := [accepted_3271]
theorem batch_65_10_ok : batch_65_10_values.all id = true := by decide

def batch_65_11_values : List Bool := [accepted_3272]
theorem batch_65_11_ok : batch_65_11_values.all id = true := by decide

def batch_65_12_values : List Bool := [accepted_3273]
theorem batch_65_12_ok : batch_65_12_values.all id = true := by decide

def batch_65_13_values : List Bool := [accepted_3275]
theorem batch_65_13_ok : batch_65_13_values.all id = true := by decide

def batch_65_14_values : List Bool := [accepted_3276]
theorem batch_65_14_ok : batch_65_14_values.all id = true := by decide

def batch_65_15_values : List Bool := [accepted_3283]
theorem batch_65_15_ok : batch_65_15_values.all id = true := by decide

def batch_65_16_values : List Bool := [accepted_3284]
theorem batch_65_16_ok : batch_65_16_values.all id = true := by decide

def batch_65_17_values : List Bool := [accepted_3285]
theorem batch_65_17_ok : batch_65_17_values.all id = true := by decide

def batch_65_18_values : List Bool := [accepted_3288]
theorem batch_65_18_ok : batch_65_18_values.all id = true := by decide

def batch_65_19_values : List Bool := [accepted_3289]
theorem batch_65_19_ok : batch_65_19_values.all id = true := by decide

def batch_65_20_values : List Bool := [accepted_3290]
theorem batch_65_20_ok : batch_65_20_values.all id = true := by decide

def batch_65_21_values : List Bool := [accepted_3291]
theorem batch_65_21_ok : batch_65_21_values.all id = true := by decide

def batch_65_22_values : List Bool := [accepted_3293]
theorem batch_65_22_ok : batch_65_22_values.all id = true := by decide

def batch_65_23_values : List Bool := [accepted_3297]
theorem batch_65_23_ok : batch_65_23_values.all id = true := by decide

def batch_65_24_values : List Bool := [accepted_3298]
theorem batch_65_24_ok : batch_65_24_values.all id = true := by decide

theorem leaf_3250_ok : checkAt 527 1000 box_3250 cert_3250 = true := by
  have h := List.all_eq_true.mp batch_65_00_ok accepted_3250 (by simp [batch_65_00_values])
  exact h
theorem leaf_3250_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3250.profileLo box_3250.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3250_ok
theorem branch_box_3250_nonnegative : ∀ j, 0 ≤ branch_box_3250.lower j ∧ 0 ≤ branch_box_3250.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3250, Box.profileLo, Box.profileHi, box_3250]
theorem leaf_3250_BranchSafe : CertificateConsequences.BranchSafe branch_box_3250 := by
  left; refine ⟨branch_box_3250_nonnegative, ?_⟩
  intro z hz; exact leaf_3250_sound hz

theorem leaf_3256_ok : checkAt 527 1000 box_3256 cert_3256 = true := by
  have h := List.all_eq_true.mp batch_65_01_ok accepted_3256 (by simp [batch_65_01_values])
  exact h
theorem leaf_3256_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3256.profileLo box_3256.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3256_ok
theorem branch_box_3256_nonnegative : ∀ j, 0 ≤ branch_box_3256.lower j ∧ 0 ≤ branch_box_3256.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3256, Box.profileLo, Box.profileHi, box_3256]
theorem leaf_3256_BranchSafe : CertificateConsequences.BranchSafe branch_box_3256 := by
  left; refine ⟨branch_box_3256_nonnegative, ?_⟩
  intro z hz; exact leaf_3256_sound hz

theorem leaf_3257_ok : checkAt 527 1000 box_3257 cert_3257 = true := by
  have h := List.all_eq_true.mp batch_65_02_ok accepted_3257 (by simp [batch_65_02_values])
  exact h
theorem leaf_3257_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3257.profileLo box_3257.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3257_ok
theorem branch_box_3257_nonnegative : ∀ j, 0 ≤ branch_box_3257.lower j ∧ 0 ≤ branch_box_3257.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3257, Box.profileLo, Box.profileHi, box_3257]
theorem leaf_3257_BranchSafe : CertificateConsequences.BranchSafe branch_box_3257 := by
  left; refine ⟨branch_box_3257_nonnegative, ?_⟩
  intro z hz; exact leaf_3257_sound hz

theorem leaf_3258_ok : checkAt 527 1000 box_3258 cert_3258 = true := by
  have h := List.all_eq_true.mp batch_65_03_ok accepted_3258 (by simp [batch_65_03_values])
  exact h
theorem leaf_3258_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3258.profileLo box_3258.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3258_ok
theorem branch_box_3258_nonnegative : ∀ j, 0 ≤ branch_box_3258.lower j ∧ 0 ≤ branch_box_3258.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3258, Box.profileLo, Box.profileHi, box_3258]
theorem leaf_3258_BranchSafe : CertificateConsequences.BranchSafe branch_box_3258 := by
  left; refine ⟨branch_box_3258_nonnegative, ?_⟩
  intro z hz; exact leaf_3258_sound hz

theorem leaf_3259_ok : checkAt 527 1000 box_3259 cert_3259 = true := by
  have h := List.all_eq_true.mp batch_65_04_ok accepted_3259 (by simp [batch_65_04_values])
  exact h
theorem leaf_3259_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3259.profileLo box_3259.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3259_ok
theorem branch_box_3259_nonnegative : ∀ j, 0 ≤ branch_box_3259.lower j ∧ 0 ≤ branch_box_3259.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3259, Box.profileLo, Box.profileHi, box_3259]
theorem leaf_3259_BranchSafe : CertificateConsequences.BranchSafe branch_box_3259 := by
  left; refine ⟨branch_box_3259_nonnegative, ?_⟩
  intro z hz; exact leaf_3259_sound hz

theorem leaf_3262_ok : checkAt 527 1000 box_3262 cert_3262 = true := by
  have h := List.all_eq_true.mp batch_65_05_ok accepted_3262 (by simp [batch_65_05_values])
  exact h
theorem leaf_3262_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3262.profileLo box_3262.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3262_ok
theorem branch_box_3262_nonnegative : ∀ j, 0 ≤ branch_box_3262.lower j ∧ 0 ≤ branch_box_3262.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3262, Box.profileLo, Box.profileHi, box_3262]
theorem leaf_3262_BranchSafe : CertificateConsequences.BranchSafe branch_box_3262 := by
  left; refine ⟨branch_box_3262_nonnegative, ?_⟩
  intro z hz; exact leaf_3262_sound hz

theorem leaf_3263_ok : checkAt 527 1000 box_3263 cert_3263 = true := by
  have h := List.all_eq_true.mp batch_65_06_ok accepted_3263 (by simp [batch_65_06_values])
  exact h
theorem leaf_3263_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3263.profileLo box_3263.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3263_ok
theorem branch_box_3263_nonnegative : ∀ j, 0 ≤ branch_box_3263.lower j ∧ 0 ≤ branch_box_3263.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3263, Box.profileLo, Box.profileHi, box_3263]
theorem leaf_3263_BranchSafe : CertificateConsequences.BranchSafe branch_box_3263 := by
  left; refine ⟨branch_box_3263_nonnegative, ?_⟩
  intro z hz; exact leaf_3263_sound hz

theorem leaf_3264_ok : checkAt 527 1000 box_3264 cert_3264 = true := by
  have h := List.all_eq_true.mp batch_65_07_ok accepted_3264 (by simp [batch_65_07_values])
  exact h
theorem leaf_3264_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3264.profileLo box_3264.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3264_ok
theorem branch_box_3264_nonnegative : ∀ j, 0 ≤ branch_box_3264.lower j ∧ 0 ≤ branch_box_3264.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3264, Box.profileLo, Box.profileHi, box_3264]
theorem leaf_3264_BranchSafe : CertificateConsequences.BranchSafe branch_box_3264 := by
  left; refine ⟨branch_box_3264_nonnegative, ?_⟩
  intro z hz; exact leaf_3264_sound hz

theorem leaf_3269_ok : checkAt 527 1000 box_3269 cert_3269 = true := by
  have h := List.all_eq_true.mp batch_65_08_ok accepted_3269 (by simp [batch_65_08_values])
  exact h
theorem leaf_3269_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3269.profileLo box_3269.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3269_ok
theorem branch_box_3269_nonnegative : ∀ j, 0 ≤ branch_box_3269.lower j ∧ 0 ≤ branch_box_3269.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3269, Box.profileLo, Box.profileHi, box_3269]
theorem leaf_3269_BranchSafe : CertificateConsequences.BranchSafe branch_box_3269 := by
  left; refine ⟨branch_box_3269_nonnegative, ?_⟩
  intro z hz; exact leaf_3269_sound hz

theorem leaf_3270_ok : checkAt 527 1000 box_3270 cert_3270 = true := by
  have h := List.all_eq_true.mp batch_65_09_ok accepted_3270 (by simp [batch_65_09_values])
  exact h
theorem leaf_3270_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3270.profileLo box_3270.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3270_ok
theorem branch_box_3270_nonnegative : ∀ j, 0 ≤ branch_box_3270.lower j ∧ 0 ≤ branch_box_3270.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3270, Box.profileLo, Box.profileHi, box_3270]
theorem leaf_3270_BranchSafe : CertificateConsequences.BranchSafe branch_box_3270 := by
  left; refine ⟨branch_box_3270_nonnegative, ?_⟩
  intro z hz; exact leaf_3270_sound hz

theorem leaf_3271_ok : checkAt 527 1000 box_3271 cert_3271 = true := by
  have h := List.all_eq_true.mp batch_65_10_ok accepted_3271 (by simp [batch_65_10_values])
  exact h
theorem leaf_3271_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3271.profileLo box_3271.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3271_ok
theorem branch_box_3271_nonnegative : ∀ j, 0 ≤ branch_box_3271.lower j ∧ 0 ≤ branch_box_3271.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3271, Box.profileLo, Box.profileHi, box_3271]
theorem leaf_3271_BranchSafe : CertificateConsequences.BranchSafe branch_box_3271 := by
  left; refine ⟨branch_box_3271_nonnegative, ?_⟩
  intro z hz; exact leaf_3271_sound hz

theorem leaf_3272_ok : checkAt 527 1000 box_3272 cert_3272 = true := by
  have h := List.all_eq_true.mp batch_65_11_ok accepted_3272 (by simp [batch_65_11_values])
  exact h
theorem leaf_3272_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3272.profileLo box_3272.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3272_ok
theorem branch_box_3272_nonnegative : ∀ j, 0 ≤ branch_box_3272.lower j ∧ 0 ≤ branch_box_3272.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3272, Box.profileLo, Box.profileHi, box_3272]
theorem leaf_3272_BranchSafe : CertificateConsequences.BranchSafe branch_box_3272 := by
  left; refine ⟨branch_box_3272_nonnegative, ?_⟩
  intro z hz; exact leaf_3272_sound hz

theorem leaf_3273_ok : checkAt 527 1000 box_3273 cert_3273 = true := by
  have h := List.all_eq_true.mp batch_65_12_ok accepted_3273 (by simp [batch_65_12_values])
  exact h
theorem leaf_3273_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3273.profileLo box_3273.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3273_ok
theorem branch_box_3273_nonnegative : ∀ j, 0 ≤ branch_box_3273.lower j ∧ 0 ≤ branch_box_3273.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3273, Box.profileLo, Box.profileHi, box_3273]
theorem leaf_3273_BranchSafe : CertificateConsequences.BranchSafe branch_box_3273 := by
  left; refine ⟨branch_box_3273_nonnegative, ?_⟩
  intro z hz; exact leaf_3273_sound hz

theorem leaf_3275_ok : checkAt 527 1000 box_3275 cert_3275 = true := by
  have h := List.all_eq_true.mp batch_65_13_ok accepted_3275 (by simp [batch_65_13_values])
  exact h
theorem leaf_3275_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3275.profileLo box_3275.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3275_ok
theorem branch_box_3275_nonnegative : ∀ j, 0 ≤ branch_box_3275.lower j ∧ 0 ≤ branch_box_3275.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3275, Box.profileLo, Box.profileHi, box_3275]
theorem leaf_3275_BranchSafe : CertificateConsequences.BranchSafe branch_box_3275 := by
  left; refine ⟨branch_box_3275_nonnegative, ?_⟩
  intro z hz; exact leaf_3275_sound hz

theorem leaf_3276_ok : checkAt 527 1000 box_3276 cert_3276 = true := by
  have h := List.all_eq_true.mp batch_65_14_ok accepted_3276 (by simp [batch_65_14_values])
  exact h
theorem leaf_3276_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3276.profileLo box_3276.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3276_ok
theorem branch_box_3276_nonnegative : ∀ j, 0 ≤ branch_box_3276.lower j ∧ 0 ≤ branch_box_3276.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3276, Box.profileLo, Box.profileHi, box_3276]
theorem leaf_3276_BranchSafe : CertificateConsequences.BranchSafe branch_box_3276 := by
  left; refine ⟨branch_box_3276_nonnegative, ?_⟩
  intro z hz; exact leaf_3276_sound hz

theorem leaf_3283_ok : checkAt 527 1000 box_3283 cert_3283 = true := by
  have h := List.all_eq_true.mp batch_65_15_ok accepted_3283 (by simp [batch_65_15_values])
  exact h
theorem leaf_3283_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3283.profileLo box_3283.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3283_ok
theorem branch_box_3283_nonnegative : ∀ j, 0 ≤ branch_box_3283.lower j ∧ 0 ≤ branch_box_3283.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3283, Box.profileLo, Box.profileHi, box_3283]
theorem leaf_3283_BranchSafe : CertificateConsequences.BranchSafe branch_box_3283 := by
  left; refine ⟨branch_box_3283_nonnegative, ?_⟩
  intro z hz; exact leaf_3283_sound hz

theorem leaf_3284_ok : checkAt 527 1000 box_3284 cert_3284 = true := by
  have h := List.all_eq_true.mp batch_65_16_ok accepted_3284 (by simp [batch_65_16_values])
  exact h
theorem leaf_3284_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3284.profileLo box_3284.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3284_ok
theorem branch_box_3284_nonnegative : ∀ j, 0 ≤ branch_box_3284.lower j ∧ 0 ≤ branch_box_3284.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3284, Box.profileLo, Box.profileHi, box_3284]
theorem leaf_3284_BranchSafe : CertificateConsequences.BranchSafe branch_box_3284 := by
  left; refine ⟨branch_box_3284_nonnegative, ?_⟩
  intro z hz; exact leaf_3284_sound hz

theorem leaf_3285_ok : checkAt 527 1000 box_3285 cert_3285 = true := by
  have h := List.all_eq_true.mp batch_65_17_ok accepted_3285 (by simp [batch_65_17_values])
  exact h
theorem leaf_3285_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3285.profileLo box_3285.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3285_ok
theorem branch_box_3285_nonnegative : ∀ j, 0 ≤ branch_box_3285.lower j ∧ 0 ≤ branch_box_3285.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3285, Box.profileLo, Box.profileHi, box_3285]
theorem leaf_3285_BranchSafe : CertificateConsequences.BranchSafe branch_box_3285 := by
  left; refine ⟨branch_box_3285_nonnegative, ?_⟩
  intro z hz; exact leaf_3285_sound hz

theorem leaf_3288_ok : checkAt 527 1000 box_3288 cert_3288 = true := by
  have h := List.all_eq_true.mp batch_65_18_ok accepted_3288 (by simp [batch_65_18_values])
  exact h
theorem leaf_3288_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3288.profileLo box_3288.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3288_ok
theorem branch_box_3288_nonnegative : ∀ j, 0 ≤ branch_box_3288.lower j ∧ 0 ≤ branch_box_3288.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3288, Box.profileLo, Box.profileHi, box_3288]
theorem leaf_3288_BranchSafe : CertificateConsequences.BranchSafe branch_box_3288 := by
  left; refine ⟨branch_box_3288_nonnegative, ?_⟩
  intro z hz; exact leaf_3288_sound hz

theorem leaf_3289_ok : checkAt 527 1000 box_3289 cert_3289 = true := by
  have h := List.all_eq_true.mp batch_65_19_ok accepted_3289 (by simp [batch_65_19_values])
  exact h
theorem leaf_3289_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3289.profileLo box_3289.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3289_ok
theorem branch_box_3289_nonnegative : ∀ j, 0 ≤ branch_box_3289.lower j ∧ 0 ≤ branch_box_3289.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3289, Box.profileLo, Box.profileHi, box_3289]
theorem leaf_3289_BranchSafe : CertificateConsequences.BranchSafe branch_box_3289 := by
  left; refine ⟨branch_box_3289_nonnegative, ?_⟩
  intro z hz; exact leaf_3289_sound hz

theorem leaf_3290_ok : checkAt 527 1000 box_3290 cert_3290 = true := by
  have h := List.all_eq_true.mp batch_65_20_ok accepted_3290 (by simp [batch_65_20_values])
  exact h
theorem leaf_3290_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3290.profileLo box_3290.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3290_ok
theorem branch_box_3290_nonnegative : ∀ j, 0 ≤ branch_box_3290.lower j ∧ 0 ≤ branch_box_3290.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3290, Box.profileLo, Box.profileHi, box_3290]
theorem leaf_3290_BranchSafe : CertificateConsequences.BranchSafe branch_box_3290 := by
  left; refine ⟨branch_box_3290_nonnegative, ?_⟩
  intro z hz; exact leaf_3290_sound hz

theorem leaf_3291_ok : checkAt 527 1000 box_3291 cert_3291 = true := by
  have h := List.all_eq_true.mp batch_65_21_ok accepted_3291 (by simp [batch_65_21_values])
  exact h
theorem leaf_3291_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3291.profileLo box_3291.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3291_ok
theorem branch_box_3291_nonnegative : ∀ j, 0 ≤ branch_box_3291.lower j ∧ 0 ≤ branch_box_3291.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3291, Box.profileLo, Box.profileHi, box_3291]
theorem leaf_3291_BranchSafe : CertificateConsequences.BranchSafe branch_box_3291 := by
  left; refine ⟨branch_box_3291_nonnegative, ?_⟩
  intro z hz; exact leaf_3291_sound hz

theorem leaf_3293_ok : checkAt 527 1000 box_3293 cert_3293 = true := by
  have h := List.all_eq_true.mp batch_65_22_ok accepted_3293 (by simp [batch_65_22_values])
  exact h
theorem leaf_3293_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3293.profileLo box_3293.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3293_ok
theorem branch_box_3293_nonnegative : ∀ j, 0 ≤ branch_box_3293.lower j ∧ 0 ≤ branch_box_3293.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3293, Box.profileLo, Box.profileHi, box_3293]
theorem leaf_3293_BranchSafe : CertificateConsequences.BranchSafe branch_box_3293 := by
  left; refine ⟨branch_box_3293_nonnegative, ?_⟩
  intro z hz; exact leaf_3293_sound hz

theorem leaf_3297_ok : checkAt 527 1000 box_3297 cert_3297 = true := by
  have h := List.all_eq_true.mp batch_65_23_ok accepted_3297 (by simp [batch_65_23_values])
  exact h
theorem leaf_3297_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3297.profileLo box_3297.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3297_ok
theorem branch_box_3297_nonnegative : ∀ j, 0 ≤ branch_box_3297.lower j ∧ 0 ≤ branch_box_3297.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3297, Box.profileLo, Box.profileHi, box_3297]
theorem leaf_3297_BranchSafe : CertificateConsequences.BranchSafe branch_box_3297 := by
  left; refine ⟨branch_box_3297_nonnegative, ?_⟩
  intro z hz; exact leaf_3297_sound hz

theorem leaf_3298_ok : checkAt 527 1000 box_3298 cert_3298 = true := by
  have h := List.all_eq_true.mp batch_65_24_ok accepted_3298 (by simp [batch_65_24_values])
  exact h
theorem leaf_3298_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3298.profileLo box_3298.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3298_ok
theorem branch_box_3298_nonnegative : ∀ j, 0 ≤ branch_box_3298.lower j ∧ 0 ≤ branch_box_3298.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3298, Box.profileLo, Box.profileHi, box_3298]
theorem leaf_3298_BranchSafe : CertificateConsequences.BranchSafe branch_box_3298 := by
  left; refine ⟨branch_box_3298_nonnegative, ?_⟩
  intro z hz; exact leaf_3298_sound hz

#print axioms batch_65_00_ok
#print axioms leaf_3250_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
