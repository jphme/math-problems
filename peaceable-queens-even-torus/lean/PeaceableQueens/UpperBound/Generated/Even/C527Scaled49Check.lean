import PeaceableQueens.UpperBound.Generated.Even.C527Scaled49Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_49_00_values : List Bool := [accepted_2451]
theorem batch_49_00_ok : batch_49_00_values.all id = true := by decide

def batch_49_01_values : List Bool := [accepted_2452]
theorem batch_49_01_ok : batch_49_01_values.all id = true := by decide

def batch_49_02_values : List Bool := [accepted_2453]
theorem batch_49_02_ok : batch_49_02_values.all id = true := by decide

def batch_49_03_values : List Bool := [accepted_2455]
theorem batch_49_03_ok : batch_49_03_values.all id = true := by decide

def batch_49_04_values : List Bool := [accepted_2456]
theorem batch_49_04_ok : batch_49_04_values.all id = true := by decide

def batch_49_05_values : List Bool := [accepted_2463]
theorem batch_49_05_ok : batch_49_05_values.all id = true := by decide

def batch_49_06_values : List Bool := [accepted_2464]
theorem batch_49_06_ok : batch_49_06_values.all id = true := by decide

def batch_49_07_values : List Bool := [accepted_2466]
theorem batch_49_07_ok : batch_49_07_values.all id = true := by decide

def batch_49_08_values : List Bool := [accepted_2467]
theorem batch_49_08_ok : batch_49_08_values.all id = true := by decide

def batch_49_09_values : List Bool := [accepted_2468]
theorem batch_49_09_ok : batch_49_09_values.all id = true := by decide

def batch_49_10_values : List Bool := [accepted_2477]
theorem batch_49_10_ok : batch_49_10_values.all id = true := by decide

def batch_49_11_values : List Bool := [accepted_2478]
theorem batch_49_11_ok : batch_49_11_values.all id = true := by decide

def batch_49_12_values : List Bool := [accepted_2479]
theorem batch_49_12_ok : batch_49_12_values.all id = true := by decide

def batch_49_13_values : List Bool := [accepted_2480]
theorem batch_49_13_ok : batch_49_13_values.all id = true := by decide

def batch_49_14_values : List Bool := [accepted_2481]
theorem batch_49_14_ok : batch_49_14_values.all id = true := by decide

def batch_49_15_values : List Bool := [accepted_2482]
theorem batch_49_15_ok : batch_49_15_values.all id = true := by decide

def batch_49_16_values : List Bool := [accepted_2485]
theorem batch_49_16_ok : batch_49_16_values.all id = true := by decide

def batch_49_17_values : List Bool := [accepted_2486]
theorem batch_49_17_ok : batch_49_17_values.all id = true := by decide

def batch_49_18_values : List Bool := [accepted_2487]
theorem batch_49_18_ok : batch_49_18_values.all id = true := by decide

def batch_49_19_values : List Bool := [accepted_2489]
theorem batch_49_19_ok : batch_49_19_values.all id = true := by decide

def batch_49_20_values : List Bool := [accepted_2490]
theorem batch_49_20_ok : batch_49_20_values.all id = true := by decide

def batch_49_21_values : List Bool := [accepted_2493]
theorem batch_49_21_ok : batch_49_21_values.all id = true := by decide

def batch_49_22_values : List Bool := [accepted_2495]
theorem batch_49_22_ok : batch_49_22_values.all id = true := by decide

def batch_49_23_values : List Bool := [accepted_2496]
theorem batch_49_23_ok : batch_49_23_values.all id = true := by decide

def batch_49_24_values : List Bool := [accepted_2498]
theorem batch_49_24_ok : batch_49_24_values.all id = true := by decide

def batch_49_25_values : List Bool := [accepted_2499]
theorem batch_49_25_ok : batch_49_25_values.all id = true := by decide

theorem leaf_2451_ok : checkAt 527 1000 box_2451 cert_2451 = true := by
  have h := List.all_eq_true.mp batch_49_00_ok accepted_2451 (by simp [batch_49_00_values])
  exact h
theorem leaf_2451_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2451.profileLo box_2451.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2451_ok
theorem branch_box_2451_nonnegative : ∀ j, 0 ≤ branch_box_2451.lower j ∧ 0 ≤ branch_box_2451.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2451, Box.profileLo, Box.profileHi, box_2451]
theorem leaf_2451_BranchSafe : CertificateConsequences.BranchSafe branch_box_2451 := by
  left; refine ⟨branch_box_2451_nonnegative, ?_⟩
  intro z hz; exact leaf_2451_sound hz

theorem leaf_2452_ok : checkAt 527 1000 box_2452 cert_2452 = true := by
  have h := List.all_eq_true.mp batch_49_01_ok accepted_2452 (by simp [batch_49_01_values])
  exact h
theorem leaf_2452_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2452.profileLo box_2452.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2452_ok
theorem branch_box_2452_nonnegative : ∀ j, 0 ≤ branch_box_2452.lower j ∧ 0 ≤ branch_box_2452.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2452, Box.profileLo, Box.profileHi, box_2452]
theorem leaf_2452_BranchSafe : CertificateConsequences.BranchSafe branch_box_2452 := by
  left; refine ⟨branch_box_2452_nonnegative, ?_⟩
  intro z hz; exact leaf_2452_sound hz

theorem leaf_2453_ok : checkAt 527 1000 box_2453 cert_2453 = true := by
  have h := List.all_eq_true.mp batch_49_02_ok accepted_2453 (by simp [batch_49_02_values])
  exact h
theorem leaf_2453_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2453.profileLo box_2453.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2453_ok
theorem branch_box_2453_nonnegative : ∀ j, 0 ≤ branch_box_2453.lower j ∧ 0 ≤ branch_box_2453.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2453, Box.profileLo, Box.profileHi, box_2453]
theorem leaf_2453_BranchSafe : CertificateConsequences.BranchSafe branch_box_2453 := by
  left; refine ⟨branch_box_2453_nonnegative, ?_⟩
  intro z hz; exact leaf_2453_sound hz

theorem leaf_2455_ok : checkAt 527 1000 box_2455 cert_2455 = true := by
  have h := List.all_eq_true.mp batch_49_03_ok accepted_2455 (by simp [batch_49_03_values])
  exact h
theorem leaf_2455_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2455.profileLo box_2455.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2455_ok
theorem branch_box_2455_nonnegative : ∀ j, 0 ≤ branch_box_2455.lower j ∧ 0 ≤ branch_box_2455.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2455, Box.profileLo, Box.profileHi, box_2455]
theorem leaf_2455_BranchSafe : CertificateConsequences.BranchSafe branch_box_2455 := by
  left; refine ⟨branch_box_2455_nonnegative, ?_⟩
  intro z hz; exact leaf_2455_sound hz

theorem leaf_2456_ok : checkAt 527 1000 box_2456 cert_2456 = true := by
  have h := List.all_eq_true.mp batch_49_04_ok accepted_2456 (by simp [batch_49_04_values])
  exact h
theorem leaf_2456_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2456.profileLo box_2456.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2456_ok
theorem branch_box_2456_nonnegative : ∀ j, 0 ≤ branch_box_2456.lower j ∧ 0 ≤ branch_box_2456.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2456, Box.profileLo, Box.profileHi, box_2456]
theorem leaf_2456_BranchSafe : CertificateConsequences.BranchSafe branch_box_2456 := by
  left; refine ⟨branch_box_2456_nonnegative, ?_⟩
  intro z hz; exact leaf_2456_sound hz

theorem leaf_2463_ok : checkAt 527 1000 box_2463 cert_2463 = true := by
  have h := List.all_eq_true.mp batch_49_05_ok accepted_2463 (by simp [batch_49_05_values])
  exact h
theorem leaf_2463_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2463.profileLo box_2463.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2463_ok
theorem branch_box_2463_nonnegative : ∀ j, 0 ≤ branch_box_2463.lower j ∧ 0 ≤ branch_box_2463.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2463, Box.profileLo, Box.profileHi, box_2463]
theorem leaf_2463_BranchSafe : CertificateConsequences.BranchSafe branch_box_2463 := by
  left; refine ⟨branch_box_2463_nonnegative, ?_⟩
  intro z hz; exact leaf_2463_sound hz

theorem leaf_2464_ok : checkAt 527 1000 box_2464 cert_2464 = true := by
  have h := List.all_eq_true.mp batch_49_06_ok accepted_2464 (by simp [batch_49_06_values])
  exact h
theorem leaf_2464_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2464.profileLo box_2464.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2464_ok
theorem branch_box_2464_nonnegative : ∀ j, 0 ≤ branch_box_2464.lower j ∧ 0 ≤ branch_box_2464.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2464, Box.profileLo, Box.profileHi, box_2464]
theorem leaf_2464_BranchSafe : CertificateConsequences.BranchSafe branch_box_2464 := by
  left; refine ⟨branch_box_2464_nonnegative, ?_⟩
  intro z hz; exact leaf_2464_sound hz

theorem leaf_2466_ok : checkAt 527 1000 box_2466 cert_2466 = true := by
  have h := List.all_eq_true.mp batch_49_07_ok accepted_2466 (by simp [batch_49_07_values])
  exact h
theorem leaf_2466_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2466.profileLo box_2466.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2466_ok
theorem branch_box_2466_nonnegative : ∀ j, 0 ≤ branch_box_2466.lower j ∧ 0 ≤ branch_box_2466.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2466, Box.profileLo, Box.profileHi, box_2466]
theorem leaf_2466_BranchSafe : CertificateConsequences.BranchSafe branch_box_2466 := by
  left; refine ⟨branch_box_2466_nonnegative, ?_⟩
  intro z hz; exact leaf_2466_sound hz

theorem leaf_2467_ok : checkAt 527 1000 box_2467 cert_2467 = true := by
  have h := List.all_eq_true.mp batch_49_08_ok accepted_2467 (by simp [batch_49_08_values])
  exact h
theorem leaf_2467_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2467.profileLo box_2467.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2467_ok
theorem branch_box_2467_nonnegative : ∀ j, 0 ≤ branch_box_2467.lower j ∧ 0 ≤ branch_box_2467.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2467, Box.profileLo, Box.profileHi, box_2467]
theorem leaf_2467_BranchSafe : CertificateConsequences.BranchSafe branch_box_2467 := by
  left; refine ⟨branch_box_2467_nonnegative, ?_⟩
  intro z hz; exact leaf_2467_sound hz

theorem leaf_2468_ok : checkAt 527 1000 box_2468 cert_2468 = true := by
  have h := List.all_eq_true.mp batch_49_09_ok accepted_2468 (by simp [batch_49_09_values])
  exact h
theorem leaf_2468_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2468.profileLo box_2468.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2468_ok
theorem branch_box_2468_nonnegative : ∀ j, 0 ≤ branch_box_2468.lower j ∧ 0 ≤ branch_box_2468.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2468, Box.profileLo, Box.profileHi, box_2468]
theorem leaf_2468_BranchSafe : CertificateConsequences.BranchSafe branch_box_2468 := by
  left; refine ⟨branch_box_2468_nonnegative, ?_⟩
  intro z hz; exact leaf_2468_sound hz

theorem leaf_2477_ok : checkAt 527 1000 box_2477 cert_2477 = true := by
  have h := List.all_eq_true.mp batch_49_10_ok accepted_2477 (by simp [batch_49_10_values])
  exact h
theorem leaf_2477_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2477.profileLo box_2477.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2477_ok
theorem branch_box_2477_nonnegative : ∀ j, 0 ≤ branch_box_2477.lower j ∧ 0 ≤ branch_box_2477.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2477, Box.profileLo, Box.profileHi, box_2477]
theorem leaf_2477_BranchSafe : CertificateConsequences.BranchSafe branch_box_2477 := by
  left; refine ⟨branch_box_2477_nonnegative, ?_⟩
  intro z hz; exact leaf_2477_sound hz

theorem leaf_2478_ok : checkAt 527 1000 box_2478 cert_2478 = true := by
  have h := List.all_eq_true.mp batch_49_11_ok accepted_2478 (by simp [batch_49_11_values])
  exact h
theorem leaf_2478_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2478.profileLo box_2478.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2478_ok
theorem branch_box_2478_nonnegative : ∀ j, 0 ≤ branch_box_2478.lower j ∧ 0 ≤ branch_box_2478.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2478, Box.profileLo, Box.profileHi, box_2478]
theorem leaf_2478_BranchSafe : CertificateConsequences.BranchSafe branch_box_2478 := by
  left; refine ⟨branch_box_2478_nonnegative, ?_⟩
  intro z hz; exact leaf_2478_sound hz

theorem leaf_2479_ok : checkAt 527 1000 box_2479 cert_2479 = true := by
  have h := List.all_eq_true.mp batch_49_12_ok accepted_2479 (by simp [batch_49_12_values])
  exact h
theorem leaf_2479_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2479.profileLo box_2479.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2479_ok
theorem branch_box_2479_nonnegative : ∀ j, 0 ≤ branch_box_2479.lower j ∧ 0 ≤ branch_box_2479.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2479, Box.profileLo, Box.profileHi, box_2479]
theorem leaf_2479_BranchSafe : CertificateConsequences.BranchSafe branch_box_2479 := by
  left; refine ⟨branch_box_2479_nonnegative, ?_⟩
  intro z hz; exact leaf_2479_sound hz

theorem leaf_2480_ok : checkAt 527 1000 box_2480 cert_2480 = true := by
  have h := List.all_eq_true.mp batch_49_13_ok accepted_2480 (by simp [batch_49_13_values])
  exact h
theorem leaf_2480_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2480.profileLo box_2480.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2480_ok
theorem branch_box_2480_nonnegative : ∀ j, 0 ≤ branch_box_2480.lower j ∧ 0 ≤ branch_box_2480.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2480, Box.profileLo, Box.profileHi, box_2480]
theorem leaf_2480_BranchSafe : CertificateConsequences.BranchSafe branch_box_2480 := by
  left; refine ⟨branch_box_2480_nonnegative, ?_⟩
  intro z hz; exact leaf_2480_sound hz

theorem leaf_2481_ok : checkAt 527 1000 box_2481 cert_2481 = true := by
  have h := List.all_eq_true.mp batch_49_14_ok accepted_2481 (by simp [batch_49_14_values])
  exact h
theorem leaf_2481_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2481.profileLo box_2481.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2481_ok
theorem branch_box_2481_nonnegative : ∀ j, 0 ≤ branch_box_2481.lower j ∧ 0 ≤ branch_box_2481.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2481, Box.profileLo, Box.profileHi, box_2481]
theorem leaf_2481_BranchSafe : CertificateConsequences.BranchSafe branch_box_2481 := by
  left; refine ⟨branch_box_2481_nonnegative, ?_⟩
  intro z hz; exact leaf_2481_sound hz

theorem leaf_2482_ok : checkAt 527 1000 box_2482 cert_2482 = true := by
  have h := List.all_eq_true.mp batch_49_15_ok accepted_2482 (by simp [batch_49_15_values])
  exact h
theorem leaf_2482_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2482.profileLo box_2482.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2482_ok
theorem branch_box_2482_nonnegative : ∀ j, 0 ≤ branch_box_2482.lower j ∧ 0 ≤ branch_box_2482.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2482, Box.profileLo, Box.profileHi, box_2482]
theorem leaf_2482_BranchSafe : CertificateConsequences.BranchSafe branch_box_2482 := by
  left; refine ⟨branch_box_2482_nonnegative, ?_⟩
  intro z hz; exact leaf_2482_sound hz

theorem leaf_2485_ok : checkAt 527 1000 box_2485 cert_2485 = true := by
  have h := List.all_eq_true.mp batch_49_16_ok accepted_2485 (by simp [batch_49_16_values])
  exact h
theorem leaf_2485_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2485.profileLo box_2485.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2485_ok
theorem branch_box_2485_nonnegative : ∀ j, 0 ≤ branch_box_2485.lower j ∧ 0 ≤ branch_box_2485.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2485, Box.profileLo, Box.profileHi, box_2485]
theorem leaf_2485_BranchSafe : CertificateConsequences.BranchSafe branch_box_2485 := by
  left; refine ⟨branch_box_2485_nonnegative, ?_⟩
  intro z hz; exact leaf_2485_sound hz

theorem leaf_2486_ok : checkAt 527 1000 box_2486 cert_2486 = true := by
  have h := List.all_eq_true.mp batch_49_17_ok accepted_2486 (by simp [batch_49_17_values])
  exact h
theorem leaf_2486_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2486.profileLo box_2486.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2486_ok
theorem branch_box_2486_nonnegative : ∀ j, 0 ≤ branch_box_2486.lower j ∧ 0 ≤ branch_box_2486.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2486, Box.profileLo, Box.profileHi, box_2486]
theorem leaf_2486_BranchSafe : CertificateConsequences.BranchSafe branch_box_2486 := by
  left; refine ⟨branch_box_2486_nonnegative, ?_⟩
  intro z hz; exact leaf_2486_sound hz

theorem leaf_2487_ok : checkAt 527 1000 box_2487 cert_2487 = true := by
  have h := List.all_eq_true.mp batch_49_18_ok accepted_2487 (by simp [batch_49_18_values])
  exact h
theorem leaf_2487_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2487.profileLo box_2487.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2487_ok
theorem branch_box_2487_nonnegative : ∀ j, 0 ≤ branch_box_2487.lower j ∧ 0 ≤ branch_box_2487.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2487, Box.profileLo, Box.profileHi, box_2487]
theorem leaf_2487_BranchSafe : CertificateConsequences.BranchSafe branch_box_2487 := by
  left; refine ⟨branch_box_2487_nonnegative, ?_⟩
  intro z hz; exact leaf_2487_sound hz

theorem leaf_2489_ok : checkAt 527 1000 box_2489 cert_2489 = true := by
  have h := List.all_eq_true.mp batch_49_19_ok accepted_2489 (by simp [batch_49_19_values])
  exact h
theorem leaf_2489_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2489.profileLo box_2489.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2489_ok
theorem branch_box_2489_nonnegative : ∀ j, 0 ≤ branch_box_2489.lower j ∧ 0 ≤ branch_box_2489.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2489, Box.profileLo, Box.profileHi, box_2489]
theorem leaf_2489_BranchSafe : CertificateConsequences.BranchSafe branch_box_2489 := by
  left; refine ⟨branch_box_2489_nonnegative, ?_⟩
  intro z hz; exact leaf_2489_sound hz

theorem leaf_2490_ok : checkAt 527 1000 box_2490 cert_2490 = true := by
  have h := List.all_eq_true.mp batch_49_20_ok accepted_2490 (by simp [batch_49_20_values])
  exact h
theorem leaf_2490_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2490.profileLo box_2490.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2490_ok
theorem branch_box_2490_nonnegative : ∀ j, 0 ≤ branch_box_2490.lower j ∧ 0 ≤ branch_box_2490.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2490, Box.profileLo, Box.profileHi, box_2490]
theorem leaf_2490_BranchSafe : CertificateConsequences.BranchSafe branch_box_2490 := by
  left; refine ⟨branch_box_2490_nonnegative, ?_⟩
  intro z hz; exact leaf_2490_sound hz

theorem leaf_2493_ok : checkAt 527 1000 box_2493 cert_2493 = true := by
  have h := List.all_eq_true.mp batch_49_21_ok accepted_2493 (by simp [batch_49_21_values])
  exact h
theorem leaf_2493_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2493.profileLo box_2493.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2493_ok
theorem branch_box_2493_nonnegative : ∀ j, 0 ≤ branch_box_2493.lower j ∧ 0 ≤ branch_box_2493.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2493, Box.profileLo, Box.profileHi, box_2493]
theorem leaf_2493_BranchSafe : CertificateConsequences.BranchSafe branch_box_2493 := by
  left; refine ⟨branch_box_2493_nonnegative, ?_⟩
  intro z hz; exact leaf_2493_sound hz

theorem leaf_2495_ok : checkAt 527 1000 box_2495 cert_2495 = true := by
  have h := List.all_eq_true.mp batch_49_22_ok accepted_2495 (by simp [batch_49_22_values])
  exact h
theorem leaf_2495_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2495.profileLo box_2495.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2495_ok
theorem branch_box_2495_nonnegative : ∀ j, 0 ≤ branch_box_2495.lower j ∧ 0 ≤ branch_box_2495.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2495, Box.profileLo, Box.profileHi, box_2495]
theorem leaf_2495_BranchSafe : CertificateConsequences.BranchSafe branch_box_2495 := by
  left; refine ⟨branch_box_2495_nonnegative, ?_⟩
  intro z hz; exact leaf_2495_sound hz

theorem leaf_2496_ok : checkAt 527 1000 box_2496 cert_2496 = true := by
  have h := List.all_eq_true.mp batch_49_23_ok accepted_2496 (by simp [batch_49_23_values])
  exact h
theorem leaf_2496_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2496.profileLo box_2496.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2496_ok
theorem branch_box_2496_nonnegative : ∀ j, 0 ≤ branch_box_2496.lower j ∧ 0 ≤ branch_box_2496.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2496, Box.profileLo, Box.profileHi, box_2496]
theorem leaf_2496_BranchSafe : CertificateConsequences.BranchSafe branch_box_2496 := by
  left; refine ⟨branch_box_2496_nonnegative, ?_⟩
  intro z hz; exact leaf_2496_sound hz

theorem leaf_2498_ok : checkAt 527 1000 box_2498 cert_2498 = true := by
  have h := List.all_eq_true.mp batch_49_24_ok accepted_2498 (by simp [batch_49_24_values])
  exact h
theorem leaf_2498_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2498.profileLo box_2498.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2498_ok
theorem branch_box_2498_nonnegative : ∀ j, 0 ≤ branch_box_2498.lower j ∧ 0 ≤ branch_box_2498.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2498, Box.profileLo, Box.profileHi, box_2498]
theorem leaf_2498_BranchSafe : CertificateConsequences.BranchSafe branch_box_2498 := by
  left; refine ⟨branch_box_2498_nonnegative, ?_⟩
  intro z hz; exact leaf_2498_sound hz

theorem leaf_2499_ok : checkAt 527 1000 box_2499 cert_2499 = true := by
  have h := List.all_eq_true.mp batch_49_25_ok accepted_2499 (by simp [batch_49_25_values])
  exact h
theorem leaf_2499_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2499.profileLo box_2499.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2499_ok
theorem branch_box_2499_nonnegative : ∀ j, 0 ≤ branch_box_2499.lower j ∧ 0 ≤ branch_box_2499.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2499, Box.profileLo, Box.profileHi, box_2499]
theorem leaf_2499_BranchSafe : CertificateConsequences.BranchSafe branch_box_2499 := by
  left; refine ⟨branch_box_2499_nonnegative, ?_⟩
  intro z hz; exact leaf_2499_sound hz

#print axioms batch_49_00_ok
#print axioms leaf_2451_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
