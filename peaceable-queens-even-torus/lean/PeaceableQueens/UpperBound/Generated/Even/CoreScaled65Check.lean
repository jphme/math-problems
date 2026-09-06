import PeaceableQueens.UpperBound.Generated.Even.CoreScaled65Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_65_00_values : List Bool := [accepted_3250]
theorem batch_65_00_ok : batch_65_00_values.all id = true := by decide

def batch_65_01_values : List Bool := [accepted_3252]
theorem batch_65_01_ok : batch_65_01_values.all id = true := by decide

def batch_65_02_values : List Bool := [accepted_3254]
theorem batch_65_02_ok : batch_65_02_values.all id = true := by decide

def batch_65_03_values : List Bool := [accepted_3255]
theorem batch_65_03_ok : batch_65_03_values.all id = true := by decide

def batch_65_04_values : List Bool := [accepted_3257]
theorem batch_65_04_ok : batch_65_04_values.all id = true := by decide

def batch_65_05_values : List Bool := [accepted_3260]
theorem batch_65_05_ok : batch_65_05_values.all id = true := by decide

def batch_65_06_values : List Bool := [accepted_3262]
theorem batch_65_06_ok : batch_65_06_values.all id = true := by decide

def batch_65_07_values : List Bool := [accepted_3266]
theorem batch_65_07_ok : batch_65_07_values.all id = true := by decide

def batch_65_08_values : List Bool := [accepted_3267]
theorem batch_65_08_ok : batch_65_08_values.all id = true := by decide

def batch_65_09_values : List Bool := [accepted_3270]
theorem batch_65_09_ok : batch_65_09_values.all id = true := by decide

def batch_65_10_values : List Bool := [accepted_3272]
theorem batch_65_10_ok : batch_65_10_values.all id = true := by decide

def batch_65_11_values : List Bool := [accepted_3273]
theorem batch_65_11_ok : batch_65_11_values.all id = true := by decide

def batch_65_12_values : List Bool := [accepted_3276]
theorem batch_65_12_ok : batch_65_12_values.all id = true := by decide

def batch_65_13_values : List Bool := [accepted_3280]
theorem batch_65_13_ok : batch_65_13_values.all id = true := by decide

def batch_65_14_values : List Bool := [accepted_3282]
theorem batch_65_14_ok : batch_65_14_values.all id = true := by decide

def batch_65_15_values : List Bool := [accepted_3284]
theorem batch_65_15_ok : batch_65_15_values.all id = true := by decide

def batch_65_16_values : List Bool := [accepted_3285]
theorem batch_65_16_ok : batch_65_16_values.all id = true := by decide

def batch_65_17_values : List Bool := [accepted_3287]
theorem batch_65_17_ok : batch_65_17_values.all id = true := by decide

def batch_65_18_values : List Bool := [accepted_3296]
theorem batch_65_18_ok : batch_65_18_values.all id = true := by decide

def batch_65_19_values : List Bool := [accepted_3297]
theorem batch_65_19_ok : batch_65_19_values.all id = true := by decide

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

theorem leaf_3252_ok : checkAt 527 1000 box_3252 cert_3252 = true := by
  have h := List.all_eq_true.mp batch_65_01_ok accepted_3252 (by simp [batch_65_01_values])
  exact h
theorem leaf_3252_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3252.profileLo box_3252.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3252_ok
theorem branch_box_3252_nonnegative : ∀ j, 0 ≤ branch_box_3252.lower j ∧ 0 ≤ branch_box_3252.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3252, Box.profileLo, Box.profileHi, box_3252]
theorem leaf_3252_BranchSafe : CertificateConsequences.BranchSafe branch_box_3252 := by
  left; refine ⟨branch_box_3252_nonnegative, ?_⟩
  intro z hz; exact leaf_3252_sound hz

theorem leaf_3254_ok : checkAt 527 1000 box_3254 cert_3254 = true := by
  have h := List.all_eq_true.mp batch_65_02_ok accepted_3254 (by simp [batch_65_02_values])
  exact h
theorem leaf_3254_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3254.profileLo box_3254.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3254_ok
theorem branch_box_3254_nonnegative : ∀ j, 0 ≤ branch_box_3254.lower j ∧ 0 ≤ branch_box_3254.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3254, Box.profileLo, Box.profileHi, box_3254]
theorem leaf_3254_BranchSafe : CertificateConsequences.BranchSafe branch_box_3254 := by
  left; refine ⟨branch_box_3254_nonnegative, ?_⟩
  intro z hz; exact leaf_3254_sound hz

theorem leaf_3255_ok : checkAt 527 1000 box_3255 cert_3255 = true := by
  have h := List.all_eq_true.mp batch_65_03_ok accepted_3255 (by simp [batch_65_03_values])
  exact h
theorem leaf_3255_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3255.profileLo box_3255.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3255_ok
theorem branch_box_3255_nonnegative : ∀ j, 0 ≤ branch_box_3255.lower j ∧ 0 ≤ branch_box_3255.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3255, Box.profileLo, Box.profileHi, box_3255]
theorem leaf_3255_BranchSafe : CertificateConsequences.BranchSafe branch_box_3255 := by
  left; refine ⟨branch_box_3255_nonnegative, ?_⟩
  intro z hz; exact leaf_3255_sound hz

theorem leaf_3257_ok : checkAt 527 1000 box_3257 cert_3257 = true := by
  have h := List.all_eq_true.mp batch_65_04_ok accepted_3257 (by simp [batch_65_04_values])
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

theorem leaf_3260_ok : checkAt 527 1000 box_3260 cert_3260 = true := by
  have h := List.all_eq_true.mp batch_65_05_ok accepted_3260 (by simp [batch_65_05_values])
  exact h
theorem leaf_3260_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3260.profileLo box_3260.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3260_ok
theorem branch_box_3260_nonnegative : ∀ j, 0 ≤ branch_box_3260.lower j ∧ 0 ≤ branch_box_3260.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3260, Box.profileLo, Box.profileHi, box_3260]
theorem leaf_3260_BranchSafe : CertificateConsequences.BranchSafe branch_box_3260 := by
  left; refine ⟨branch_box_3260_nonnegative, ?_⟩
  intro z hz; exact leaf_3260_sound hz

theorem leaf_3262_ok : checkAt 527 1000 box_3262 cert_3262 = true := by
  have h := List.all_eq_true.mp batch_65_06_ok accepted_3262 (by simp [batch_65_06_values])
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

theorem leaf_3266_ok : checkAt 527 1000 box_3266 cert_3266 = true := by
  have h := List.all_eq_true.mp batch_65_07_ok accepted_3266 (by simp [batch_65_07_values])
  exact h
theorem leaf_3266_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3266.profileLo box_3266.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3266_ok
theorem branch_box_3266_nonnegative : ∀ j, 0 ≤ branch_box_3266.lower j ∧ 0 ≤ branch_box_3266.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3266, Box.profileLo, Box.profileHi, box_3266]
theorem leaf_3266_BranchSafe : CertificateConsequences.BranchSafe branch_box_3266 := by
  left; refine ⟨branch_box_3266_nonnegative, ?_⟩
  intro z hz; exact leaf_3266_sound hz

theorem leaf_3267_ok : checkAt 527 1000 box_3267 cert_3267 = true := by
  have h := List.all_eq_true.mp batch_65_08_ok accepted_3267 (by simp [batch_65_08_values])
  exact h
theorem leaf_3267_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3267.profileLo box_3267.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3267_ok
theorem branch_box_3267_nonnegative : ∀ j, 0 ≤ branch_box_3267.lower j ∧ 0 ≤ branch_box_3267.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3267, Box.profileLo, Box.profileHi, box_3267]
theorem leaf_3267_BranchSafe : CertificateConsequences.BranchSafe branch_box_3267 := by
  left; refine ⟨branch_box_3267_nonnegative, ?_⟩
  intro z hz; exact leaf_3267_sound hz

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

theorem leaf_3272_ok : checkAt 527 1000 box_3272 cert_3272 = true := by
  have h := List.all_eq_true.mp batch_65_10_ok accepted_3272 (by simp [batch_65_10_values])
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
  have h := List.all_eq_true.mp batch_65_11_ok accepted_3273 (by simp [batch_65_11_values])
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

theorem leaf_3276_ok : checkAt 527 1000 box_3276 cert_3276 = true := by
  have h := List.all_eq_true.mp batch_65_12_ok accepted_3276 (by simp [batch_65_12_values])
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

theorem leaf_3280_ok : checkAt 527 1000 box_3280 cert_3280 = true := by
  have h := List.all_eq_true.mp batch_65_13_ok accepted_3280 (by simp [batch_65_13_values])
  exact h
theorem leaf_3280_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3280.profileLo box_3280.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3280_ok
theorem branch_box_3280_nonnegative : ∀ j, 0 ≤ branch_box_3280.lower j ∧ 0 ≤ branch_box_3280.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3280, Box.profileLo, Box.profileHi, box_3280]
theorem leaf_3280_BranchSafe : CertificateConsequences.BranchSafe branch_box_3280 := by
  left; refine ⟨branch_box_3280_nonnegative, ?_⟩
  intro z hz; exact leaf_3280_sound hz

theorem leaf_3282_ok : checkAt 527 1000 box_3282 cert_3282 = true := by
  have h := List.all_eq_true.mp batch_65_14_ok accepted_3282 (by simp [batch_65_14_values])
  exact h
theorem leaf_3282_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3282.profileLo box_3282.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3282_ok
theorem branch_box_3282_nonnegative : ∀ j, 0 ≤ branch_box_3282.lower j ∧ 0 ≤ branch_box_3282.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3282, Box.profileLo, Box.profileHi, box_3282]
theorem leaf_3282_BranchSafe : CertificateConsequences.BranchSafe branch_box_3282 := by
  left; refine ⟨branch_box_3282_nonnegative, ?_⟩
  intro z hz; exact leaf_3282_sound hz

theorem leaf_3284_ok : checkAt 527 1000 box_3284 cert_3284 = true := by
  have h := List.all_eq_true.mp batch_65_15_ok accepted_3284 (by simp [batch_65_15_values])
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
  have h := List.all_eq_true.mp batch_65_16_ok accepted_3285 (by simp [batch_65_16_values])
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

theorem leaf_3287_ok : checkAt 527 1000 box_3287 cert_3287 = true := by
  have h := List.all_eq_true.mp batch_65_17_ok accepted_3287 (by simp [batch_65_17_values])
  exact h
theorem leaf_3287_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3287.profileLo box_3287.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3287_ok
theorem branch_box_3287_nonnegative : ∀ j, 0 ≤ branch_box_3287.lower j ∧ 0 ≤ branch_box_3287.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3287, Box.profileLo, Box.profileHi, box_3287]
theorem leaf_3287_BranchSafe : CertificateConsequences.BranchSafe branch_box_3287 := by
  left; refine ⟨branch_box_3287_nonnegative, ?_⟩
  intro z hz; exact leaf_3287_sound hz

theorem leaf_3296_ok : checkAt 527 1000 box_3296 cert_3296 = true := by
  have h := List.all_eq_true.mp batch_65_18_ok accepted_3296 (by simp [batch_65_18_values])
  exact h
theorem leaf_3296_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3296.profileLo box_3296.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3296_ok
theorem branch_box_3296_nonnegative : ∀ j, 0 ≤ branch_box_3296.lower j ∧ 0 ≤ branch_box_3296.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3296, Box.profileLo, Box.profileHi, box_3296]
theorem leaf_3296_BranchSafe : CertificateConsequences.BranchSafe branch_box_3296 := by
  left; refine ⟨branch_box_3296_nonnegative, ?_⟩
  intro z hz; exact leaf_3296_sound hz

theorem leaf_3297_ok : checkAt 527 1000 box_3297 cert_3297 = true := by
  have h := List.all_eq_true.mp batch_65_19_ok accepted_3297 (by simp [batch_65_19_values])
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

#print axioms batch_65_00_ok
#print axioms leaf_3250_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
