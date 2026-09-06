import PeaceableQueens.UpperBound.Generated.Even.C527Scaled48Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_48_00_values : List Bool := [accepted_2400]
theorem batch_48_00_ok : batch_48_00_values.all id = true := by decide

def batch_48_01_values : List Bool := [accepted_2403]
theorem batch_48_01_ok : batch_48_01_values.all id = true := by decide

def batch_48_02_values : List Bool := [accepted_2405]
theorem batch_48_02_ok : batch_48_02_values.all id = true := by decide

def batch_48_03_values : List Bool := [accepted_2406]
theorem batch_48_03_ok : batch_48_03_values.all id = true := by decide

def batch_48_04_values : List Bool := [accepted_2414]
theorem batch_48_04_ok : batch_48_04_values.all id = true := by decide

def batch_48_05_values : List Bool := [accepted_2415]
theorem batch_48_05_ok : batch_48_05_values.all id = true := by decide

def batch_48_06_values : List Bool := [accepted_2417]
theorem batch_48_06_ok : batch_48_06_values.all id = true := by decide

def batch_48_07_values : List Bool := [accepted_2418]
theorem batch_48_07_ok : batch_48_07_values.all id = true := by decide

def batch_48_08_values : List Bool := [accepted_2419]
theorem batch_48_08_ok : batch_48_08_values.all id = true := by decide

def batch_48_09_values : List Bool := [accepted_2420]
theorem batch_48_09_ok : batch_48_09_values.all id = true := by decide

def batch_48_10_values : List Bool := [accepted_2421]
theorem batch_48_10_ok : batch_48_10_values.all id = true := by decide

def batch_48_11_values : List Bool := [accepted_2423]
theorem batch_48_11_ok : batch_48_11_values.all id = true := by decide

def batch_48_12_values : List Bool := [accepted_2424]
theorem batch_48_12_ok : batch_48_12_values.all id = true := by decide

def batch_48_13_values : List Bool := [accepted_2429]
theorem batch_48_13_ok : batch_48_13_values.all id = true := by decide

def batch_48_14_values : List Bool := [accepted_2436]
theorem batch_48_14_ok : batch_48_14_values.all id = true := by decide

def batch_48_15_values : List Bool := [accepted_2437]
theorem batch_48_15_ok : batch_48_15_values.all id = true := by decide

def batch_48_16_values : List Bool := [accepted_2438]
theorem batch_48_16_ok : batch_48_16_values.all id = true := by decide

def batch_48_17_values : List Bool := [accepted_2440]
theorem batch_48_17_ok : batch_48_17_values.all id = true := by decide

def batch_48_18_values : List Bool := [accepted_2441]
theorem batch_48_18_ok : batch_48_18_values.all id = true := by decide

def batch_48_19_values : List Bool := [accepted_2443]
theorem batch_48_19_ok : batch_48_19_values.all id = true := by decide

def batch_48_20_values : List Bool := [accepted_2444]
theorem batch_48_20_ok : batch_48_20_values.all id = true := by decide

def batch_48_21_values : List Bool := [accepted_2446]
theorem batch_48_21_ok : batch_48_21_values.all id = true := by decide

def batch_48_22_values : List Bool := [accepted_2447]
theorem batch_48_22_ok : batch_48_22_values.all id = true := by decide

def batch_48_23_values : List Bool := [accepted_2448]
theorem batch_48_23_ok : batch_48_23_values.all id = true := by decide

def batch_48_24_values : List Bool := [accepted_2449]
theorem batch_48_24_ok : batch_48_24_values.all id = true := by decide

theorem leaf_2400_ok : checkAt 527 1000 box_2400 cert_2400 = true := by
  have h := List.all_eq_true.mp batch_48_00_ok accepted_2400 (by simp [batch_48_00_values])
  exact h
theorem leaf_2400_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2400.profileLo box_2400.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2400_ok
theorem branch_box_2400_nonnegative : ∀ j, 0 ≤ branch_box_2400.lower j ∧ 0 ≤ branch_box_2400.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2400, Box.profileLo, Box.profileHi, box_2400]
theorem leaf_2400_BranchSafe : CertificateConsequences.BranchSafe branch_box_2400 := by
  left; refine ⟨branch_box_2400_nonnegative, ?_⟩
  intro z hz; exact leaf_2400_sound hz

theorem leaf_2403_ok : checkAt 527 1000 box_2403 cert_2403 = true := by
  have h := List.all_eq_true.mp batch_48_01_ok accepted_2403 (by simp [batch_48_01_values])
  exact h
theorem leaf_2403_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2403.profileLo box_2403.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2403_ok
theorem branch_box_2403_nonnegative : ∀ j, 0 ≤ branch_box_2403.lower j ∧ 0 ≤ branch_box_2403.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2403, Box.profileLo, Box.profileHi, box_2403]
theorem leaf_2403_BranchSafe : CertificateConsequences.BranchSafe branch_box_2403 := by
  left; refine ⟨branch_box_2403_nonnegative, ?_⟩
  intro z hz; exact leaf_2403_sound hz

theorem leaf_2405_ok : checkAt 527 1000 box_2405 cert_2405 = true := by
  have h := List.all_eq_true.mp batch_48_02_ok accepted_2405 (by simp [batch_48_02_values])
  exact h
theorem leaf_2405_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2405.profileLo box_2405.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2405_ok
theorem branch_box_2405_nonnegative : ∀ j, 0 ≤ branch_box_2405.lower j ∧ 0 ≤ branch_box_2405.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2405, Box.profileLo, Box.profileHi, box_2405]
theorem leaf_2405_BranchSafe : CertificateConsequences.BranchSafe branch_box_2405 := by
  left; refine ⟨branch_box_2405_nonnegative, ?_⟩
  intro z hz; exact leaf_2405_sound hz

theorem leaf_2406_ok : checkAt 527 1000 box_2406 cert_2406 = true := by
  have h := List.all_eq_true.mp batch_48_03_ok accepted_2406 (by simp [batch_48_03_values])
  exact h
theorem leaf_2406_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2406.profileLo box_2406.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2406_ok
theorem branch_box_2406_nonnegative : ∀ j, 0 ≤ branch_box_2406.lower j ∧ 0 ≤ branch_box_2406.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2406, Box.profileLo, Box.profileHi, box_2406]
theorem leaf_2406_BranchSafe : CertificateConsequences.BranchSafe branch_box_2406 := by
  left; refine ⟨branch_box_2406_nonnegative, ?_⟩
  intro z hz; exact leaf_2406_sound hz

theorem leaf_2414_ok : checkAt 527 1000 box_2414 cert_2414 = true := by
  have h := List.all_eq_true.mp batch_48_04_ok accepted_2414 (by simp [batch_48_04_values])
  exact h
theorem leaf_2414_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2414.profileLo box_2414.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2414_ok
theorem branch_box_2414_nonnegative : ∀ j, 0 ≤ branch_box_2414.lower j ∧ 0 ≤ branch_box_2414.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2414, Box.profileLo, Box.profileHi, box_2414]
theorem leaf_2414_BranchSafe : CertificateConsequences.BranchSafe branch_box_2414 := by
  left; refine ⟨branch_box_2414_nonnegative, ?_⟩
  intro z hz; exact leaf_2414_sound hz

theorem leaf_2415_ok : checkAt 527 1000 box_2415 cert_2415 = true := by
  have h := List.all_eq_true.mp batch_48_05_ok accepted_2415 (by simp [batch_48_05_values])
  exact h
theorem leaf_2415_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2415.profileLo box_2415.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2415_ok
theorem branch_box_2415_nonnegative : ∀ j, 0 ≤ branch_box_2415.lower j ∧ 0 ≤ branch_box_2415.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2415, Box.profileLo, Box.profileHi, box_2415]
theorem leaf_2415_BranchSafe : CertificateConsequences.BranchSafe branch_box_2415 := by
  left; refine ⟨branch_box_2415_nonnegative, ?_⟩
  intro z hz; exact leaf_2415_sound hz

theorem leaf_2417_ok : checkAt 527 1000 box_2417 cert_2417 = true := by
  have h := List.all_eq_true.mp batch_48_06_ok accepted_2417 (by simp [batch_48_06_values])
  exact h
theorem leaf_2417_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2417.profileLo box_2417.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2417_ok
theorem branch_box_2417_nonnegative : ∀ j, 0 ≤ branch_box_2417.lower j ∧ 0 ≤ branch_box_2417.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2417, Box.profileLo, Box.profileHi, box_2417]
theorem leaf_2417_BranchSafe : CertificateConsequences.BranchSafe branch_box_2417 := by
  left; refine ⟨branch_box_2417_nonnegative, ?_⟩
  intro z hz; exact leaf_2417_sound hz

theorem leaf_2418_ok : checkAt 527 1000 box_2418 cert_2418 = true := by
  have h := List.all_eq_true.mp batch_48_07_ok accepted_2418 (by simp [batch_48_07_values])
  exact h
theorem leaf_2418_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2418.profileLo box_2418.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2418_ok
theorem branch_box_2418_nonnegative : ∀ j, 0 ≤ branch_box_2418.lower j ∧ 0 ≤ branch_box_2418.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2418, Box.profileLo, Box.profileHi, box_2418]
theorem leaf_2418_BranchSafe : CertificateConsequences.BranchSafe branch_box_2418 := by
  left; refine ⟨branch_box_2418_nonnegative, ?_⟩
  intro z hz; exact leaf_2418_sound hz

theorem leaf_2419_ok : checkAt 527 1000 box_2419 cert_2419 = true := by
  have h := List.all_eq_true.mp batch_48_08_ok accepted_2419 (by simp [batch_48_08_values])
  exact h
theorem leaf_2419_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2419.profileLo box_2419.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2419_ok
theorem branch_box_2419_nonnegative : ∀ j, 0 ≤ branch_box_2419.lower j ∧ 0 ≤ branch_box_2419.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2419, Box.profileLo, Box.profileHi, box_2419]
theorem leaf_2419_BranchSafe : CertificateConsequences.BranchSafe branch_box_2419 := by
  left; refine ⟨branch_box_2419_nonnegative, ?_⟩
  intro z hz; exact leaf_2419_sound hz

theorem leaf_2420_ok : checkAt 527 1000 box_2420 cert_2420 = true := by
  have h := List.all_eq_true.mp batch_48_09_ok accepted_2420 (by simp [batch_48_09_values])
  exact h
theorem leaf_2420_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2420.profileLo box_2420.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2420_ok
theorem branch_box_2420_nonnegative : ∀ j, 0 ≤ branch_box_2420.lower j ∧ 0 ≤ branch_box_2420.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2420, Box.profileLo, Box.profileHi, box_2420]
theorem leaf_2420_BranchSafe : CertificateConsequences.BranchSafe branch_box_2420 := by
  left; refine ⟨branch_box_2420_nonnegative, ?_⟩
  intro z hz; exact leaf_2420_sound hz

theorem leaf_2421_ok : checkAt 527 1000 box_2421 cert_2421 = true := by
  have h := List.all_eq_true.mp batch_48_10_ok accepted_2421 (by simp [batch_48_10_values])
  exact h
theorem leaf_2421_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2421.profileLo box_2421.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2421_ok
theorem branch_box_2421_nonnegative : ∀ j, 0 ≤ branch_box_2421.lower j ∧ 0 ≤ branch_box_2421.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2421, Box.profileLo, Box.profileHi, box_2421]
theorem leaf_2421_BranchSafe : CertificateConsequences.BranchSafe branch_box_2421 := by
  left; refine ⟨branch_box_2421_nonnegative, ?_⟩
  intro z hz; exact leaf_2421_sound hz

theorem leaf_2423_ok : checkAt 527 1000 box_2423 cert_2423 = true := by
  have h := List.all_eq_true.mp batch_48_11_ok accepted_2423 (by simp [batch_48_11_values])
  exact h
theorem leaf_2423_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2423.profileLo box_2423.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2423_ok
theorem branch_box_2423_nonnegative : ∀ j, 0 ≤ branch_box_2423.lower j ∧ 0 ≤ branch_box_2423.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2423, Box.profileLo, Box.profileHi, box_2423]
theorem leaf_2423_BranchSafe : CertificateConsequences.BranchSafe branch_box_2423 := by
  left; refine ⟨branch_box_2423_nonnegative, ?_⟩
  intro z hz; exact leaf_2423_sound hz

theorem leaf_2424_ok : checkAt 527 1000 box_2424 cert_2424 = true := by
  have h := List.all_eq_true.mp batch_48_12_ok accepted_2424 (by simp [batch_48_12_values])
  exact h
theorem leaf_2424_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2424.profileLo box_2424.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2424_ok
theorem branch_box_2424_nonnegative : ∀ j, 0 ≤ branch_box_2424.lower j ∧ 0 ≤ branch_box_2424.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2424, Box.profileLo, Box.profileHi, box_2424]
theorem leaf_2424_BranchSafe : CertificateConsequences.BranchSafe branch_box_2424 := by
  left; refine ⟨branch_box_2424_nonnegative, ?_⟩
  intro z hz; exact leaf_2424_sound hz

theorem leaf_2429_ok : checkAt 527 1000 box_2429 cert_2429 = true := by
  have h := List.all_eq_true.mp batch_48_13_ok accepted_2429 (by simp [batch_48_13_values])
  exact h
theorem leaf_2429_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2429.profileLo box_2429.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2429_ok
theorem branch_box_2429_nonnegative : ∀ j, 0 ≤ branch_box_2429.lower j ∧ 0 ≤ branch_box_2429.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2429, Box.profileLo, Box.profileHi, box_2429]
theorem leaf_2429_BranchSafe : CertificateConsequences.BranchSafe branch_box_2429 := by
  left; refine ⟨branch_box_2429_nonnegative, ?_⟩
  intro z hz; exact leaf_2429_sound hz

theorem leaf_2436_ok : checkAt 527 1000 box_2436 cert_2436 = true := by
  have h := List.all_eq_true.mp batch_48_14_ok accepted_2436 (by simp [batch_48_14_values])
  exact h
theorem leaf_2436_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2436.profileLo box_2436.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2436_ok
theorem branch_box_2436_nonnegative : ∀ j, 0 ≤ branch_box_2436.lower j ∧ 0 ≤ branch_box_2436.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2436, Box.profileLo, Box.profileHi, box_2436]
theorem leaf_2436_BranchSafe : CertificateConsequences.BranchSafe branch_box_2436 := by
  left; refine ⟨branch_box_2436_nonnegative, ?_⟩
  intro z hz; exact leaf_2436_sound hz

theorem leaf_2437_ok : checkAt 527 1000 box_2437 cert_2437 = true := by
  have h := List.all_eq_true.mp batch_48_15_ok accepted_2437 (by simp [batch_48_15_values])
  exact h
theorem leaf_2437_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2437.profileLo box_2437.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2437_ok
theorem branch_box_2437_nonnegative : ∀ j, 0 ≤ branch_box_2437.lower j ∧ 0 ≤ branch_box_2437.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2437, Box.profileLo, Box.profileHi, box_2437]
theorem leaf_2437_BranchSafe : CertificateConsequences.BranchSafe branch_box_2437 := by
  left; refine ⟨branch_box_2437_nonnegative, ?_⟩
  intro z hz; exact leaf_2437_sound hz

theorem leaf_2438_ok : checkAt 527 1000 box_2438 cert_2438 = true := by
  have h := List.all_eq_true.mp batch_48_16_ok accepted_2438 (by simp [batch_48_16_values])
  exact h
theorem leaf_2438_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2438.profileLo box_2438.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2438_ok
theorem branch_box_2438_nonnegative : ∀ j, 0 ≤ branch_box_2438.lower j ∧ 0 ≤ branch_box_2438.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2438, Box.profileLo, Box.profileHi, box_2438]
theorem leaf_2438_BranchSafe : CertificateConsequences.BranchSafe branch_box_2438 := by
  left; refine ⟨branch_box_2438_nonnegative, ?_⟩
  intro z hz; exact leaf_2438_sound hz

theorem leaf_2440_ok : checkAt 527 1000 box_2440 cert_2440 = true := by
  have h := List.all_eq_true.mp batch_48_17_ok accepted_2440 (by simp [batch_48_17_values])
  exact h
theorem leaf_2440_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2440.profileLo box_2440.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2440_ok
theorem branch_box_2440_nonnegative : ∀ j, 0 ≤ branch_box_2440.lower j ∧ 0 ≤ branch_box_2440.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2440, Box.profileLo, Box.profileHi, box_2440]
theorem leaf_2440_BranchSafe : CertificateConsequences.BranchSafe branch_box_2440 := by
  left; refine ⟨branch_box_2440_nonnegative, ?_⟩
  intro z hz; exact leaf_2440_sound hz

theorem leaf_2441_ok : checkAt 527 1000 box_2441 cert_2441 = true := by
  have h := List.all_eq_true.mp batch_48_18_ok accepted_2441 (by simp [batch_48_18_values])
  exact h
theorem leaf_2441_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2441.profileLo box_2441.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2441_ok
theorem branch_box_2441_nonnegative : ∀ j, 0 ≤ branch_box_2441.lower j ∧ 0 ≤ branch_box_2441.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2441, Box.profileLo, Box.profileHi, box_2441]
theorem leaf_2441_BranchSafe : CertificateConsequences.BranchSafe branch_box_2441 := by
  left; refine ⟨branch_box_2441_nonnegative, ?_⟩
  intro z hz; exact leaf_2441_sound hz

theorem leaf_2443_ok : checkAt 527 1000 box_2443 cert_2443 = true := by
  have h := List.all_eq_true.mp batch_48_19_ok accepted_2443 (by simp [batch_48_19_values])
  exact h
theorem leaf_2443_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2443.profileLo box_2443.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2443_ok
theorem branch_box_2443_nonnegative : ∀ j, 0 ≤ branch_box_2443.lower j ∧ 0 ≤ branch_box_2443.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2443, Box.profileLo, Box.profileHi, box_2443]
theorem leaf_2443_BranchSafe : CertificateConsequences.BranchSafe branch_box_2443 := by
  left; refine ⟨branch_box_2443_nonnegative, ?_⟩
  intro z hz; exact leaf_2443_sound hz

theorem leaf_2444_ok : checkAt 527 1000 box_2444 cert_2444 = true := by
  have h := List.all_eq_true.mp batch_48_20_ok accepted_2444 (by simp [batch_48_20_values])
  exact h
theorem leaf_2444_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2444.profileLo box_2444.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2444_ok
theorem branch_box_2444_nonnegative : ∀ j, 0 ≤ branch_box_2444.lower j ∧ 0 ≤ branch_box_2444.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2444, Box.profileLo, Box.profileHi, box_2444]
theorem leaf_2444_BranchSafe : CertificateConsequences.BranchSafe branch_box_2444 := by
  left; refine ⟨branch_box_2444_nonnegative, ?_⟩
  intro z hz; exact leaf_2444_sound hz

theorem leaf_2446_ok : checkAt 527 1000 box_2446 cert_2446 = true := by
  have h := List.all_eq_true.mp batch_48_21_ok accepted_2446 (by simp [batch_48_21_values])
  exact h
theorem leaf_2446_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2446.profileLo box_2446.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2446_ok
theorem branch_box_2446_nonnegative : ∀ j, 0 ≤ branch_box_2446.lower j ∧ 0 ≤ branch_box_2446.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2446, Box.profileLo, Box.profileHi, box_2446]
theorem leaf_2446_BranchSafe : CertificateConsequences.BranchSafe branch_box_2446 := by
  left; refine ⟨branch_box_2446_nonnegative, ?_⟩
  intro z hz; exact leaf_2446_sound hz

theorem leaf_2447_ok : checkAt 527 1000 box_2447 cert_2447 = true := by
  have h := List.all_eq_true.mp batch_48_22_ok accepted_2447 (by simp [batch_48_22_values])
  exact h
theorem leaf_2447_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2447.profileLo box_2447.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2447_ok
theorem branch_box_2447_nonnegative : ∀ j, 0 ≤ branch_box_2447.lower j ∧ 0 ≤ branch_box_2447.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2447, Box.profileLo, Box.profileHi, box_2447]
theorem leaf_2447_BranchSafe : CertificateConsequences.BranchSafe branch_box_2447 := by
  left; refine ⟨branch_box_2447_nonnegative, ?_⟩
  intro z hz; exact leaf_2447_sound hz

theorem leaf_2448_ok : checkAt 527 1000 box_2448 cert_2448 = true := by
  have h := List.all_eq_true.mp batch_48_23_ok accepted_2448 (by simp [batch_48_23_values])
  exact h
theorem leaf_2448_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2448.profileLo box_2448.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2448_ok
theorem branch_box_2448_nonnegative : ∀ j, 0 ≤ branch_box_2448.lower j ∧ 0 ≤ branch_box_2448.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2448, Box.profileLo, Box.profileHi, box_2448]
theorem leaf_2448_BranchSafe : CertificateConsequences.BranchSafe branch_box_2448 := by
  left; refine ⟨branch_box_2448_nonnegative, ?_⟩
  intro z hz; exact leaf_2448_sound hz

theorem leaf_2449_ok : checkAt 527 1000 box_2449 cert_2449 = true := by
  have h := List.all_eq_true.mp batch_48_24_ok accepted_2449 (by simp [batch_48_24_values])
  exact h
theorem leaf_2449_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2449.profileLo box_2449.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2449_ok
theorem branch_box_2449_nonnegative : ∀ j, 0 ≤ branch_box_2449.lower j ∧ 0 ≤ branch_box_2449.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2449, Box.profileLo, Box.profileHi, box_2449]
theorem leaf_2449_BranchSafe : CertificateConsequences.BranchSafe branch_box_2449 := by
  left; refine ⟨branch_box_2449_nonnegative, ?_⟩
  intro z hz; exact leaf_2449_sound hz

#print axioms batch_48_00_ok
#print axioms leaf_2400_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
