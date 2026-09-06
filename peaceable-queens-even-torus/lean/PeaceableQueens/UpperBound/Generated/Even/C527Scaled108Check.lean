import PeaceableQueens.UpperBound.Generated.Even.C527Scaled108Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_108_00_values : List Bool := [accepted_5404]
theorem batch_108_00_ok : batch_108_00_values.all id = true := by decide

def batch_108_01_values : List Bool := [accepted_5409]
theorem batch_108_01_ok : batch_108_01_values.all id = true := by decide

def batch_108_02_values : List Bool := [accepted_5410]
theorem batch_108_02_ok : batch_108_02_values.all id = true := by decide

def batch_108_03_values : List Bool := [accepted_5411]
theorem batch_108_03_ok : batch_108_03_values.all id = true := by decide

def batch_108_04_values : List Bool := [accepted_5412]
theorem batch_108_04_ok : batch_108_04_values.all id = true := by decide

def batch_108_05_values : List Bool := [accepted_5413]
theorem batch_108_05_ok : batch_108_05_values.all id = true := by decide

def batch_108_06_values : List Bool := [accepted_5415]
theorem batch_108_06_ok : batch_108_06_values.all id = true := by decide

def batch_108_07_values : List Bool := [accepted_5417]
theorem batch_108_07_ok : batch_108_07_values.all id = true := by decide

def batch_108_08_values : List Bool := [accepted_5418]
theorem batch_108_08_ok : batch_108_08_values.all id = true := by decide

def batch_108_09_values : List Bool := [accepted_5419]
theorem batch_108_09_ok : batch_108_09_values.all id = true := by decide

def batch_108_10_values : List Bool := [accepted_5420]
theorem batch_108_10_ok : batch_108_10_values.all id = true := by decide

def batch_108_11_values : List Bool := [accepted_5429]
theorem batch_108_11_ok : batch_108_11_values.all id = true := by decide

def batch_108_12_values : List Bool := [accepted_5430]
theorem batch_108_12_ok : batch_108_12_values.all id = true := by decide

def batch_108_13_values : List Bool := [accepted_5431]
theorem batch_108_13_ok : batch_108_13_values.all id = true := by decide

def batch_108_14_values : List Bool := [accepted_5432]
theorem batch_108_14_ok : batch_108_14_values.all id = true := by decide

def batch_108_15_values : List Bool := [accepted_5435]
theorem batch_108_15_ok : batch_108_15_values.all id = true := by decide

def batch_108_16_values : List Bool := [accepted_5436]
theorem batch_108_16_ok : batch_108_16_values.all id = true := by decide

def batch_108_17_values : List Bool := [accepted_5437]
theorem batch_108_17_ok : batch_108_17_values.all id = true := by decide

def batch_108_18_values : List Bool := [accepted_5439]
theorem batch_108_18_ok : batch_108_18_values.all id = true := by decide

def batch_108_19_values : List Bool := [accepted_5440]
theorem batch_108_19_ok : batch_108_19_values.all id = true := by decide

def batch_108_20_values : List Bool := [accepted_5441]
theorem batch_108_20_ok : batch_108_20_values.all id = true := by decide

def batch_108_21_values : List Bool := [accepted_5443]
theorem batch_108_21_ok : batch_108_21_values.all id = true := by decide

def batch_108_22_values : List Bool := [accepted_5444]
theorem batch_108_22_ok : batch_108_22_values.all id = true := by decide

def batch_108_23_values : List Bool := [accepted_5445]
theorem batch_108_23_ok : batch_108_23_values.all id = true := by decide

def batch_108_24_values : List Bool := [accepted_5447]
theorem batch_108_24_ok : batch_108_24_values.all id = true := by decide

def batch_108_25_values : List Bool := [accepted_5448]
theorem batch_108_25_ok : batch_108_25_values.all id = true := by decide

theorem leaf_5404_ok : checkAt 527 1000 box_5404 cert_5404 = true := by
  have h := List.all_eq_true.mp batch_108_00_ok accepted_5404 (by simp [batch_108_00_values])
  exact h
theorem leaf_5404_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5404.profileLo box_5404.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5404_ok
theorem branch_box_5404_nonnegative : ∀ j, 0 ≤ branch_box_5404.lower j ∧ 0 ≤ branch_box_5404.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5404, Box.profileLo, Box.profileHi, box_5404]
theorem leaf_5404_BranchSafe : CertificateConsequences.BranchSafe branch_box_5404 := by
  left; refine ⟨branch_box_5404_nonnegative, ?_⟩
  intro z hz; exact leaf_5404_sound hz

theorem leaf_5409_ok : checkAt 527 1000 box_5409 cert_5409 = true := by
  have h := List.all_eq_true.mp batch_108_01_ok accepted_5409 (by simp [batch_108_01_values])
  exact h
theorem leaf_5409_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5409.profileLo box_5409.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5409_ok
theorem branch_box_5409_nonnegative : ∀ j, 0 ≤ branch_box_5409.lower j ∧ 0 ≤ branch_box_5409.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5409, Box.profileLo, Box.profileHi, box_5409]
theorem leaf_5409_BranchSafe : CertificateConsequences.BranchSafe branch_box_5409 := by
  left; refine ⟨branch_box_5409_nonnegative, ?_⟩
  intro z hz; exact leaf_5409_sound hz

theorem leaf_5410_ok : checkAt 527 1000 box_5410 cert_5410 = true := by
  have h := List.all_eq_true.mp batch_108_02_ok accepted_5410 (by simp [batch_108_02_values])
  exact h
theorem leaf_5410_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5410.profileLo box_5410.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5410_ok
theorem branch_box_5410_nonnegative : ∀ j, 0 ≤ branch_box_5410.lower j ∧ 0 ≤ branch_box_5410.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5410, Box.profileLo, Box.profileHi, box_5410]
theorem leaf_5410_BranchSafe : CertificateConsequences.BranchSafe branch_box_5410 := by
  left; refine ⟨branch_box_5410_nonnegative, ?_⟩
  intro z hz; exact leaf_5410_sound hz

theorem leaf_5411_ok : checkAt 527 1000 box_5411 cert_5411 = true := by
  have h := List.all_eq_true.mp batch_108_03_ok accepted_5411 (by simp [batch_108_03_values])
  exact h
theorem leaf_5411_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5411.profileLo box_5411.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5411_ok
theorem branch_box_5411_nonnegative : ∀ j, 0 ≤ branch_box_5411.lower j ∧ 0 ≤ branch_box_5411.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5411, Box.profileLo, Box.profileHi, box_5411]
theorem leaf_5411_BranchSafe : CertificateConsequences.BranchSafe branch_box_5411 := by
  left; refine ⟨branch_box_5411_nonnegative, ?_⟩
  intro z hz; exact leaf_5411_sound hz

theorem leaf_5412_ok : checkAt 527 1000 box_5412 cert_5412 = true := by
  have h := List.all_eq_true.mp batch_108_04_ok accepted_5412 (by simp [batch_108_04_values])
  exact h
theorem leaf_5412_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5412.profileLo box_5412.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5412_ok
theorem branch_box_5412_nonnegative : ∀ j, 0 ≤ branch_box_5412.lower j ∧ 0 ≤ branch_box_5412.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5412, Box.profileLo, Box.profileHi, box_5412]
theorem leaf_5412_BranchSafe : CertificateConsequences.BranchSafe branch_box_5412 := by
  left; refine ⟨branch_box_5412_nonnegative, ?_⟩
  intro z hz; exact leaf_5412_sound hz

theorem leaf_5413_ok : checkAt 527 1000 box_5413 cert_5413 = true := by
  have h := List.all_eq_true.mp batch_108_05_ok accepted_5413 (by simp [batch_108_05_values])
  exact h
theorem leaf_5413_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5413.profileLo box_5413.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5413_ok
theorem branch_box_5413_nonnegative : ∀ j, 0 ≤ branch_box_5413.lower j ∧ 0 ≤ branch_box_5413.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5413, Box.profileLo, Box.profileHi, box_5413]
theorem leaf_5413_BranchSafe : CertificateConsequences.BranchSafe branch_box_5413 := by
  left; refine ⟨branch_box_5413_nonnegative, ?_⟩
  intro z hz; exact leaf_5413_sound hz

theorem leaf_5415_ok : checkAt 527 1000 box_5415 cert_5415 = true := by
  have h := List.all_eq_true.mp batch_108_06_ok accepted_5415 (by simp [batch_108_06_values])
  exact h
theorem leaf_5415_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5415.profileLo box_5415.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5415_ok
theorem branch_box_5415_nonnegative : ∀ j, 0 ≤ branch_box_5415.lower j ∧ 0 ≤ branch_box_5415.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5415, Box.profileLo, Box.profileHi, box_5415]
theorem leaf_5415_BranchSafe : CertificateConsequences.BranchSafe branch_box_5415 := by
  left; refine ⟨branch_box_5415_nonnegative, ?_⟩
  intro z hz; exact leaf_5415_sound hz

theorem leaf_5417_ok : checkAt 527 1000 box_5417 cert_5417 = true := by
  have h := List.all_eq_true.mp batch_108_07_ok accepted_5417 (by simp [batch_108_07_values])
  exact h
theorem leaf_5417_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5417.profileLo box_5417.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5417_ok
theorem branch_box_5417_nonnegative : ∀ j, 0 ≤ branch_box_5417.lower j ∧ 0 ≤ branch_box_5417.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5417, Box.profileLo, Box.profileHi, box_5417]
theorem leaf_5417_BranchSafe : CertificateConsequences.BranchSafe branch_box_5417 := by
  left; refine ⟨branch_box_5417_nonnegative, ?_⟩
  intro z hz; exact leaf_5417_sound hz

theorem leaf_5418_ok : checkAt 527 1000 box_5418 cert_5418 = true := by
  have h := List.all_eq_true.mp batch_108_08_ok accepted_5418 (by simp [batch_108_08_values])
  exact h
theorem leaf_5418_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5418.profileLo box_5418.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5418_ok
theorem branch_box_5418_nonnegative : ∀ j, 0 ≤ branch_box_5418.lower j ∧ 0 ≤ branch_box_5418.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5418, Box.profileLo, Box.profileHi, box_5418]
theorem leaf_5418_BranchSafe : CertificateConsequences.BranchSafe branch_box_5418 := by
  left; refine ⟨branch_box_5418_nonnegative, ?_⟩
  intro z hz; exact leaf_5418_sound hz

theorem leaf_5419_ok : checkAt 527 1000 box_5419 cert_5419 = true := by
  have h := List.all_eq_true.mp batch_108_09_ok accepted_5419 (by simp [batch_108_09_values])
  exact h
theorem leaf_5419_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5419.profileLo box_5419.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5419_ok
theorem branch_box_5419_nonnegative : ∀ j, 0 ≤ branch_box_5419.lower j ∧ 0 ≤ branch_box_5419.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5419, Box.profileLo, Box.profileHi, box_5419]
theorem leaf_5419_BranchSafe : CertificateConsequences.BranchSafe branch_box_5419 := by
  left; refine ⟨branch_box_5419_nonnegative, ?_⟩
  intro z hz; exact leaf_5419_sound hz

theorem leaf_5420_ok : checkAt 527 1000 box_5420 cert_5420 = true := by
  have h := List.all_eq_true.mp batch_108_10_ok accepted_5420 (by simp [batch_108_10_values])
  exact h
theorem leaf_5420_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5420.profileLo box_5420.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5420_ok
theorem branch_box_5420_nonnegative : ∀ j, 0 ≤ branch_box_5420.lower j ∧ 0 ≤ branch_box_5420.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5420, Box.profileLo, Box.profileHi, box_5420]
theorem leaf_5420_BranchSafe : CertificateConsequences.BranchSafe branch_box_5420 := by
  left; refine ⟨branch_box_5420_nonnegative, ?_⟩
  intro z hz; exact leaf_5420_sound hz

theorem leaf_5429_ok : checkAt 527 1000 box_5429 cert_5429 = true := by
  have h := List.all_eq_true.mp batch_108_11_ok accepted_5429 (by simp [batch_108_11_values])
  exact h
theorem leaf_5429_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5429.profileLo box_5429.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5429_ok
theorem branch_box_5429_nonnegative : ∀ j, 0 ≤ branch_box_5429.lower j ∧ 0 ≤ branch_box_5429.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5429, Box.profileLo, Box.profileHi, box_5429]
theorem leaf_5429_BranchSafe : CertificateConsequences.BranchSafe branch_box_5429 := by
  left; refine ⟨branch_box_5429_nonnegative, ?_⟩
  intro z hz; exact leaf_5429_sound hz

theorem leaf_5430_ok : checkAt 527 1000 box_5430 cert_5430 = true := by
  have h := List.all_eq_true.mp batch_108_12_ok accepted_5430 (by simp [batch_108_12_values])
  exact h
theorem leaf_5430_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5430.profileLo box_5430.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5430_ok
theorem branch_box_5430_nonnegative : ∀ j, 0 ≤ branch_box_5430.lower j ∧ 0 ≤ branch_box_5430.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5430, Box.profileLo, Box.profileHi, box_5430]
theorem leaf_5430_BranchSafe : CertificateConsequences.BranchSafe branch_box_5430 := by
  left; refine ⟨branch_box_5430_nonnegative, ?_⟩
  intro z hz; exact leaf_5430_sound hz

theorem leaf_5431_ok : checkAt 527 1000 box_5431 cert_5431 = true := by
  have h := List.all_eq_true.mp batch_108_13_ok accepted_5431 (by simp [batch_108_13_values])
  exact h
theorem leaf_5431_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5431.profileLo box_5431.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5431_ok
theorem branch_box_5431_nonnegative : ∀ j, 0 ≤ branch_box_5431.lower j ∧ 0 ≤ branch_box_5431.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5431, Box.profileLo, Box.profileHi, box_5431]
theorem leaf_5431_BranchSafe : CertificateConsequences.BranchSafe branch_box_5431 := by
  left; refine ⟨branch_box_5431_nonnegative, ?_⟩
  intro z hz; exact leaf_5431_sound hz

theorem leaf_5432_ok : checkAt 527 1000 box_5432 cert_5432 = true := by
  have h := List.all_eq_true.mp batch_108_14_ok accepted_5432 (by simp [batch_108_14_values])
  exact h
theorem leaf_5432_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5432.profileLo box_5432.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5432_ok
theorem branch_box_5432_nonnegative : ∀ j, 0 ≤ branch_box_5432.lower j ∧ 0 ≤ branch_box_5432.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5432, Box.profileLo, Box.profileHi, box_5432]
theorem leaf_5432_BranchSafe : CertificateConsequences.BranchSafe branch_box_5432 := by
  left; refine ⟨branch_box_5432_nonnegative, ?_⟩
  intro z hz; exact leaf_5432_sound hz

theorem leaf_5435_ok : checkAt 527 1000 box_5435 cert_5435 = true := by
  have h := List.all_eq_true.mp batch_108_15_ok accepted_5435 (by simp [batch_108_15_values])
  exact h
theorem leaf_5435_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5435.profileLo box_5435.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5435_ok
theorem branch_box_5435_nonnegative : ∀ j, 0 ≤ branch_box_5435.lower j ∧ 0 ≤ branch_box_5435.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5435, Box.profileLo, Box.profileHi, box_5435]
theorem leaf_5435_BranchSafe : CertificateConsequences.BranchSafe branch_box_5435 := by
  left; refine ⟨branch_box_5435_nonnegative, ?_⟩
  intro z hz; exact leaf_5435_sound hz

theorem leaf_5436_ok : checkAt 527 1000 box_5436 cert_5436 = true := by
  have h := List.all_eq_true.mp batch_108_16_ok accepted_5436 (by simp [batch_108_16_values])
  exact h
theorem leaf_5436_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5436.profileLo box_5436.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5436_ok
theorem branch_box_5436_nonnegative : ∀ j, 0 ≤ branch_box_5436.lower j ∧ 0 ≤ branch_box_5436.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5436, Box.profileLo, Box.profileHi, box_5436]
theorem leaf_5436_BranchSafe : CertificateConsequences.BranchSafe branch_box_5436 := by
  left; refine ⟨branch_box_5436_nonnegative, ?_⟩
  intro z hz; exact leaf_5436_sound hz

theorem leaf_5437_ok : checkAt 527 1000 box_5437 cert_5437 = true := by
  have h := List.all_eq_true.mp batch_108_17_ok accepted_5437 (by simp [batch_108_17_values])
  exact h
theorem leaf_5437_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5437.profileLo box_5437.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5437_ok
theorem branch_box_5437_nonnegative : ∀ j, 0 ≤ branch_box_5437.lower j ∧ 0 ≤ branch_box_5437.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5437, Box.profileLo, Box.profileHi, box_5437]
theorem leaf_5437_BranchSafe : CertificateConsequences.BranchSafe branch_box_5437 := by
  left; refine ⟨branch_box_5437_nonnegative, ?_⟩
  intro z hz; exact leaf_5437_sound hz

theorem leaf_5439_ok : checkAt 527 1000 box_5439 cert_5439 = true := by
  have h := List.all_eq_true.mp batch_108_18_ok accepted_5439 (by simp [batch_108_18_values])
  exact h
theorem leaf_5439_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5439.profileLo box_5439.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5439_ok
theorem branch_box_5439_nonnegative : ∀ j, 0 ≤ branch_box_5439.lower j ∧ 0 ≤ branch_box_5439.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5439, Box.profileLo, Box.profileHi, box_5439]
theorem leaf_5439_BranchSafe : CertificateConsequences.BranchSafe branch_box_5439 := by
  left; refine ⟨branch_box_5439_nonnegative, ?_⟩
  intro z hz; exact leaf_5439_sound hz

theorem leaf_5440_ok : checkAt 527 1000 box_5440 cert_5440 = true := by
  have h := List.all_eq_true.mp batch_108_19_ok accepted_5440 (by simp [batch_108_19_values])
  exact h
theorem leaf_5440_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5440.profileLo box_5440.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5440_ok
theorem branch_box_5440_nonnegative : ∀ j, 0 ≤ branch_box_5440.lower j ∧ 0 ≤ branch_box_5440.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5440, Box.profileLo, Box.profileHi, box_5440]
theorem leaf_5440_BranchSafe : CertificateConsequences.BranchSafe branch_box_5440 := by
  left; refine ⟨branch_box_5440_nonnegative, ?_⟩
  intro z hz; exact leaf_5440_sound hz

theorem leaf_5441_ok : checkAt 527 1000 box_5441 cert_5441 = true := by
  have h := List.all_eq_true.mp batch_108_20_ok accepted_5441 (by simp [batch_108_20_values])
  exact h
theorem leaf_5441_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5441.profileLo box_5441.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5441_ok
theorem branch_box_5441_nonnegative : ∀ j, 0 ≤ branch_box_5441.lower j ∧ 0 ≤ branch_box_5441.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5441, Box.profileLo, Box.profileHi, box_5441]
theorem leaf_5441_BranchSafe : CertificateConsequences.BranchSafe branch_box_5441 := by
  left; refine ⟨branch_box_5441_nonnegative, ?_⟩
  intro z hz; exact leaf_5441_sound hz

theorem leaf_5443_ok : checkAt 527 1000 box_5443 cert_5443 = true := by
  have h := List.all_eq_true.mp batch_108_21_ok accepted_5443 (by simp [batch_108_21_values])
  exact h
theorem leaf_5443_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5443.profileLo box_5443.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5443_ok
theorem branch_box_5443_nonnegative : ∀ j, 0 ≤ branch_box_5443.lower j ∧ 0 ≤ branch_box_5443.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5443, Box.profileLo, Box.profileHi, box_5443]
theorem leaf_5443_BranchSafe : CertificateConsequences.BranchSafe branch_box_5443 := by
  left; refine ⟨branch_box_5443_nonnegative, ?_⟩
  intro z hz; exact leaf_5443_sound hz

theorem leaf_5444_ok : checkAt 527 1000 box_5444 cert_5444 = true := by
  have h := List.all_eq_true.mp batch_108_22_ok accepted_5444 (by simp [batch_108_22_values])
  exact h
theorem leaf_5444_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5444.profileLo box_5444.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5444_ok
theorem branch_box_5444_nonnegative : ∀ j, 0 ≤ branch_box_5444.lower j ∧ 0 ≤ branch_box_5444.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5444, Box.profileLo, Box.profileHi, box_5444]
theorem leaf_5444_BranchSafe : CertificateConsequences.BranchSafe branch_box_5444 := by
  left; refine ⟨branch_box_5444_nonnegative, ?_⟩
  intro z hz; exact leaf_5444_sound hz

theorem leaf_5445_ok : checkAt 527 1000 box_5445 cert_5445 = true := by
  have h := List.all_eq_true.mp batch_108_23_ok accepted_5445 (by simp [batch_108_23_values])
  exact h
theorem leaf_5445_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5445.profileLo box_5445.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5445_ok
theorem branch_box_5445_nonnegative : ∀ j, 0 ≤ branch_box_5445.lower j ∧ 0 ≤ branch_box_5445.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5445, Box.profileLo, Box.profileHi, box_5445]
theorem leaf_5445_BranchSafe : CertificateConsequences.BranchSafe branch_box_5445 := by
  left; refine ⟨branch_box_5445_nonnegative, ?_⟩
  intro z hz; exact leaf_5445_sound hz

theorem leaf_5447_ok : checkAt 527 1000 box_5447 cert_5447 = true := by
  have h := List.all_eq_true.mp batch_108_24_ok accepted_5447 (by simp [batch_108_24_values])
  exact h
theorem leaf_5447_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5447.profileLo box_5447.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5447_ok
theorem branch_box_5447_nonnegative : ∀ j, 0 ≤ branch_box_5447.lower j ∧ 0 ≤ branch_box_5447.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5447, Box.profileLo, Box.profileHi, box_5447]
theorem leaf_5447_BranchSafe : CertificateConsequences.BranchSafe branch_box_5447 := by
  left; refine ⟨branch_box_5447_nonnegative, ?_⟩
  intro z hz; exact leaf_5447_sound hz

theorem leaf_5448_ok : checkAt 527 1000 box_5448 cert_5448 = true := by
  have h := List.all_eq_true.mp batch_108_25_ok accepted_5448 (by simp [batch_108_25_values])
  exact h
theorem leaf_5448_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5448.profileLo box_5448.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5448_ok
theorem branch_box_5448_nonnegative : ∀ j, 0 ≤ branch_box_5448.lower j ∧ 0 ≤ branch_box_5448.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5448, Box.profileLo, Box.profileHi, box_5448]
theorem leaf_5448_BranchSafe : CertificateConsequences.BranchSafe branch_box_5448 := by
  left; refine ⟨branch_box_5448_nonnegative, ?_⟩
  intro z hz; exact leaf_5448_sound hz

#print axioms batch_108_00_ok
#print axioms leaf_5404_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
