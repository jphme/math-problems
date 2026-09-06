import PeaceableQueens.UpperBound.Generated.Even.CoreScaled48Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_48_00_values : List Bool := [accepted_2403]
theorem batch_48_00_ok : batch_48_00_values.all id = true := by decide

def batch_48_01_values : List Bool := [accepted_2405]
theorem batch_48_01_ok : batch_48_01_values.all id = true := by decide

def batch_48_02_values : List Bool := [accepted_2407]
theorem batch_48_02_ok : batch_48_02_values.all id = true := by decide

def batch_48_03_values : List Bool := [accepted_2411]
theorem batch_48_03_ok : batch_48_03_values.all id = true := by decide

def batch_48_04_values : List Bool := [accepted_2413]
theorem batch_48_04_ok : batch_48_04_values.all id = true := by decide

def batch_48_05_values : List Bool := [accepted_2416]
theorem batch_48_05_ok : batch_48_05_values.all id = true := by decide

def batch_48_06_values : List Bool := [accepted_2417]
theorem batch_48_06_ok : batch_48_06_values.all id = true := by decide

def batch_48_07_values : List Bool := [accepted_2419]
theorem batch_48_07_ok : batch_48_07_values.all id = true := by decide

def batch_48_08_values : List Bool := [accepted_2427]
theorem batch_48_08_ok : batch_48_08_values.all id = true := by decide

def batch_48_09_values : List Bool := [accepted_2429]
theorem batch_48_09_ok : batch_48_09_values.all id = true := by decide

def batch_48_10_values : List Bool := [accepted_2431]
theorem batch_48_10_ok : batch_48_10_values.all id = true := by decide

def batch_48_11_values : List Bool := [accepted_2435]
theorem batch_48_11_ok : batch_48_11_values.all id = true := by decide

def batch_48_12_values : List Bool := [accepted_2437]
theorem batch_48_12_ok : batch_48_12_values.all id = true := by decide

def batch_48_13_values : List Bool := [accepted_2439]
theorem batch_48_13_ok : batch_48_13_values.all id = true := by decide

def batch_48_14_values : List Bool := [accepted_2445]
theorem batch_48_14_ok : batch_48_14_values.all id = true := by decide

def batch_48_15_values : List Bool := [accepted_2447]
theorem batch_48_15_ok : batch_48_15_values.all id = true := by decide

theorem leaf_2403_ok : checkAt 527 1000 box_2403 cert_2403 = true := by
  have h := List.all_eq_true.mp batch_48_00_ok accepted_2403 (by simp [batch_48_00_values])
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
  have h := List.all_eq_true.mp batch_48_01_ok accepted_2405 (by simp [batch_48_01_values])
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

theorem leaf_2407_ok : checkAt 527 1000 box_2407 cert_2407 = true := by
  have h := List.all_eq_true.mp batch_48_02_ok accepted_2407 (by simp [batch_48_02_values])
  exact h
theorem leaf_2407_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2407.profileLo box_2407.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2407_ok
theorem branch_box_2407_nonnegative : ∀ j, 0 ≤ branch_box_2407.lower j ∧ 0 ≤ branch_box_2407.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2407, Box.profileLo, Box.profileHi, box_2407]
theorem leaf_2407_BranchSafe : CertificateConsequences.BranchSafe branch_box_2407 := by
  left; refine ⟨branch_box_2407_nonnegative, ?_⟩
  intro z hz; exact leaf_2407_sound hz

theorem leaf_2411_ok : checkAt 527 1000 box_2411 cert_2411 = true := by
  have h := List.all_eq_true.mp batch_48_03_ok accepted_2411 (by simp [batch_48_03_values])
  exact h
theorem leaf_2411_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2411.profileLo box_2411.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2411_ok
theorem branch_box_2411_nonnegative : ∀ j, 0 ≤ branch_box_2411.lower j ∧ 0 ≤ branch_box_2411.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2411, Box.profileLo, Box.profileHi, box_2411]
theorem leaf_2411_BranchSafe : CertificateConsequences.BranchSafe branch_box_2411 := by
  left; refine ⟨branch_box_2411_nonnegative, ?_⟩
  intro z hz; exact leaf_2411_sound hz

theorem leaf_2413_ok : checkAt 527 1000 box_2413 cert_2413 = true := by
  have h := List.all_eq_true.mp batch_48_04_ok accepted_2413 (by simp [batch_48_04_values])
  exact h
theorem leaf_2413_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2413.profileLo box_2413.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2413_ok
theorem branch_box_2413_nonnegative : ∀ j, 0 ≤ branch_box_2413.lower j ∧ 0 ≤ branch_box_2413.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2413, Box.profileLo, Box.profileHi, box_2413]
theorem leaf_2413_BranchSafe : CertificateConsequences.BranchSafe branch_box_2413 := by
  left; refine ⟨branch_box_2413_nonnegative, ?_⟩
  intro z hz; exact leaf_2413_sound hz

theorem leaf_2416_ok : checkAt 527 1000 box_2416 cert_2416 = true := by
  have h := List.all_eq_true.mp batch_48_05_ok accepted_2416 (by simp [batch_48_05_values])
  exact h
theorem leaf_2416_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2416.profileLo box_2416.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2416_ok
theorem branch_box_2416_nonnegative : ∀ j, 0 ≤ branch_box_2416.lower j ∧ 0 ≤ branch_box_2416.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2416, Box.profileLo, Box.profileHi, box_2416]
theorem leaf_2416_BranchSafe : CertificateConsequences.BranchSafe branch_box_2416 := by
  left; refine ⟨branch_box_2416_nonnegative, ?_⟩
  intro z hz; exact leaf_2416_sound hz

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

theorem leaf_2419_ok : checkAt 527 1000 box_2419 cert_2419 = true := by
  have h := List.all_eq_true.mp batch_48_07_ok accepted_2419 (by simp [batch_48_07_values])
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

theorem leaf_2427_ok : checkAt 527 1000 box_2427 cert_2427 = true := by
  have h := List.all_eq_true.mp batch_48_08_ok accepted_2427 (by simp [batch_48_08_values])
  exact h
theorem leaf_2427_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2427.profileLo box_2427.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2427_ok
theorem branch_box_2427_nonnegative : ∀ j, 0 ≤ branch_box_2427.lower j ∧ 0 ≤ branch_box_2427.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2427, Box.profileLo, Box.profileHi, box_2427]
theorem leaf_2427_BranchSafe : CertificateConsequences.BranchSafe branch_box_2427 := by
  left; refine ⟨branch_box_2427_nonnegative, ?_⟩
  intro z hz; exact leaf_2427_sound hz

theorem leaf_2429_ok : checkAt 527 1000 box_2429 cert_2429 = true := by
  have h := List.all_eq_true.mp batch_48_09_ok accepted_2429 (by simp [batch_48_09_values])
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

theorem leaf_2431_ok : checkAt 527 1000 box_2431 cert_2431 = true := by
  have h := List.all_eq_true.mp batch_48_10_ok accepted_2431 (by simp [batch_48_10_values])
  exact h
theorem leaf_2431_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2431.profileLo box_2431.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2431_ok
theorem branch_box_2431_nonnegative : ∀ j, 0 ≤ branch_box_2431.lower j ∧ 0 ≤ branch_box_2431.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2431, Box.profileLo, Box.profileHi, box_2431]
theorem leaf_2431_BranchSafe : CertificateConsequences.BranchSafe branch_box_2431 := by
  left; refine ⟨branch_box_2431_nonnegative, ?_⟩
  intro z hz; exact leaf_2431_sound hz

theorem leaf_2435_ok : checkAt 527 1000 box_2435 cert_2435 = true := by
  have h := List.all_eq_true.mp batch_48_11_ok accepted_2435 (by simp [batch_48_11_values])
  exact h
theorem leaf_2435_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2435.profileLo box_2435.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2435_ok
theorem branch_box_2435_nonnegative : ∀ j, 0 ≤ branch_box_2435.lower j ∧ 0 ≤ branch_box_2435.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2435, Box.profileLo, Box.profileHi, box_2435]
theorem leaf_2435_BranchSafe : CertificateConsequences.BranchSafe branch_box_2435 := by
  left; refine ⟨branch_box_2435_nonnegative, ?_⟩
  intro z hz; exact leaf_2435_sound hz

theorem leaf_2437_ok : checkAt 527 1000 box_2437 cert_2437 = true := by
  have h := List.all_eq_true.mp batch_48_12_ok accepted_2437 (by simp [batch_48_12_values])
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

theorem leaf_2439_ok : checkAt 527 1000 box_2439 cert_2439 = true := by
  have h := List.all_eq_true.mp batch_48_13_ok accepted_2439 (by simp [batch_48_13_values])
  exact h
theorem leaf_2439_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2439.profileLo box_2439.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2439_ok
theorem branch_box_2439_nonnegative : ∀ j, 0 ≤ branch_box_2439.lower j ∧ 0 ≤ branch_box_2439.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2439, Box.profileLo, Box.profileHi, box_2439]
theorem leaf_2439_BranchSafe : CertificateConsequences.BranchSafe branch_box_2439 := by
  left; refine ⟨branch_box_2439_nonnegative, ?_⟩
  intro z hz; exact leaf_2439_sound hz

theorem leaf_2445_ok : checkAt 527 1000 box_2445 cert_2445 = true := by
  have h := List.all_eq_true.mp batch_48_14_ok accepted_2445 (by simp [batch_48_14_values])
  exact h
theorem leaf_2445_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2445.profileLo box_2445.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2445_ok
theorem branch_box_2445_nonnegative : ∀ j, 0 ≤ branch_box_2445.lower j ∧ 0 ≤ branch_box_2445.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2445, Box.profileLo, Box.profileHi, box_2445]
theorem leaf_2445_BranchSafe : CertificateConsequences.BranchSafe branch_box_2445 := by
  left; refine ⟨branch_box_2445_nonnegative, ?_⟩
  intro z hz; exact leaf_2445_sound hz

theorem leaf_2447_ok : checkAt 527 1000 box_2447 cert_2447 = true := by
  have h := List.all_eq_true.mp batch_48_15_ok accepted_2447 (by simp [batch_48_15_values])
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

#print axioms batch_48_00_ok
#print axioms leaf_2403_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
