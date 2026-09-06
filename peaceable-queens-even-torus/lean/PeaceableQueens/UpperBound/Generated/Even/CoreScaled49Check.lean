import PeaceableQueens.UpperBound.Generated.Even.CoreScaled49Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_49_00_values : List Bool := [accepted_2450]
theorem batch_49_00_ok : batch_49_00_values.all id = true := by decide

def batch_49_01_values : List Bool := [accepted_2451]
theorem batch_49_01_ok : batch_49_01_values.all id = true := by decide

def batch_49_02_values : List Bool := [accepted_2453]
theorem batch_49_02_ok : batch_49_02_values.all id = true := by decide

def batch_49_03_values : List Bool := [accepted_2458]
theorem batch_49_03_ok : batch_49_03_values.all id = true := by decide

def batch_49_04_values : List Bool := [accepted_2460]
theorem batch_49_04_ok : batch_49_04_values.all id = true := by decide

def batch_49_05_values : List Bool := [accepted_2463]
theorem batch_49_05_ok : batch_49_05_values.all id = true := by decide

def batch_49_06_values : List Bool := [accepted_2467]
theorem batch_49_06_ok : batch_49_06_values.all id = true := by decide

def batch_49_07_values : List Bool := [accepted_2469]
theorem batch_49_07_ok : batch_49_07_values.all id = true := by decide

def batch_49_08_values : List Bool := [accepted_2472]
theorem batch_49_08_ok : batch_49_08_values.all id = true := by decide

def batch_49_09_values : List Bool := [accepted_2473]
theorem batch_49_09_ok : batch_49_09_values.all id = true := by decide

def batch_49_10_values : List Bool := [accepted_2475]
theorem batch_49_10_ok : batch_49_10_values.all id = true := by decide

def batch_49_11_values : List Bool := [accepted_2481]
theorem batch_49_11_ok : batch_49_11_values.all id = true := by decide

def batch_49_12_values : List Bool := [accepted_2483]
theorem batch_49_12_ok : batch_49_12_values.all id = true := by decide

def batch_49_13_values : List Bool := [accepted_2486]
theorem batch_49_13_ok : batch_49_13_values.all id = true := by decide

def batch_49_14_values : List Bool := [accepted_2487]
theorem batch_49_14_ok : batch_49_14_values.all id = true := by decide

def batch_49_15_values : List Bool := [accepted_2489]
theorem batch_49_15_ok : batch_49_15_values.all id = true := by decide

def batch_49_16_values : List Bool := [accepted_2494]
theorem batch_49_16_ok : batch_49_16_values.all id = true := by decide

def batch_49_17_values : List Bool := [accepted_2496]
theorem batch_49_17_ok : batch_49_17_values.all id = true := by decide

def batch_49_18_values : List Bool := [accepted_2498]
theorem batch_49_18_ok : batch_49_18_values.all id = true := by decide

def batch_49_19_values : List Bool := [accepted_2499]
theorem batch_49_19_ok : batch_49_19_values.all id = true := by decide

theorem leaf_2450_ok : checkAt 527 1000 box_2450 cert_2450 = true := by
  have h := List.all_eq_true.mp batch_49_00_ok accepted_2450 (by simp [batch_49_00_values])
  exact h
theorem leaf_2450_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2450.profileLo box_2450.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2450_ok
theorem branch_box_2450_nonnegative : ∀ j, 0 ≤ branch_box_2450.lower j ∧ 0 ≤ branch_box_2450.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2450, Box.profileLo, Box.profileHi, box_2450]
theorem leaf_2450_BranchSafe : CertificateConsequences.BranchSafe branch_box_2450 := by
  left; refine ⟨branch_box_2450_nonnegative, ?_⟩
  intro z hz; exact leaf_2450_sound hz

theorem leaf_2451_ok : checkAt 527 1000 box_2451 cert_2451 = true := by
  have h := List.all_eq_true.mp batch_49_01_ok accepted_2451 (by simp [batch_49_01_values])
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

theorem leaf_2458_ok : checkAt 527 1000 box_2458 cert_2458 = true := by
  have h := List.all_eq_true.mp batch_49_03_ok accepted_2458 (by simp [batch_49_03_values])
  exact h
theorem leaf_2458_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2458.profileLo box_2458.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2458_ok
theorem branch_box_2458_nonnegative : ∀ j, 0 ≤ branch_box_2458.lower j ∧ 0 ≤ branch_box_2458.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2458, Box.profileLo, Box.profileHi, box_2458]
theorem leaf_2458_BranchSafe : CertificateConsequences.BranchSafe branch_box_2458 := by
  left; refine ⟨branch_box_2458_nonnegative, ?_⟩
  intro z hz; exact leaf_2458_sound hz

theorem leaf_2460_ok : checkAt 527 1000 box_2460 cert_2460 = true := by
  have h := List.all_eq_true.mp batch_49_04_ok accepted_2460 (by simp [batch_49_04_values])
  exact h
theorem leaf_2460_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2460.profileLo box_2460.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2460_ok
theorem branch_box_2460_nonnegative : ∀ j, 0 ≤ branch_box_2460.lower j ∧ 0 ≤ branch_box_2460.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2460, Box.profileLo, Box.profileHi, box_2460]
theorem leaf_2460_BranchSafe : CertificateConsequences.BranchSafe branch_box_2460 := by
  left; refine ⟨branch_box_2460_nonnegative, ?_⟩
  intro z hz; exact leaf_2460_sound hz

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

theorem leaf_2467_ok : checkAt 527 1000 box_2467 cert_2467 = true := by
  have h := List.all_eq_true.mp batch_49_06_ok accepted_2467 (by simp [batch_49_06_values])
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

theorem leaf_2469_ok : checkAt 527 1000 box_2469 cert_2469 = true := by
  have h := List.all_eq_true.mp batch_49_07_ok accepted_2469 (by simp [batch_49_07_values])
  exact h
theorem leaf_2469_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2469.profileLo box_2469.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2469_ok
theorem branch_box_2469_nonnegative : ∀ j, 0 ≤ branch_box_2469.lower j ∧ 0 ≤ branch_box_2469.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2469, Box.profileLo, Box.profileHi, box_2469]
theorem leaf_2469_BranchSafe : CertificateConsequences.BranchSafe branch_box_2469 := by
  left; refine ⟨branch_box_2469_nonnegative, ?_⟩
  intro z hz; exact leaf_2469_sound hz

theorem leaf_2472_ok : checkAt 527 1000 box_2472 cert_2472 = true := by
  have h := List.all_eq_true.mp batch_49_08_ok accepted_2472 (by simp [batch_49_08_values])
  exact h
theorem leaf_2472_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2472.profileLo box_2472.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2472_ok
theorem branch_box_2472_nonnegative : ∀ j, 0 ≤ branch_box_2472.lower j ∧ 0 ≤ branch_box_2472.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2472, Box.profileLo, Box.profileHi, box_2472]
theorem leaf_2472_BranchSafe : CertificateConsequences.BranchSafe branch_box_2472 := by
  left; refine ⟨branch_box_2472_nonnegative, ?_⟩
  intro z hz; exact leaf_2472_sound hz

theorem leaf_2473_ok : checkAt 527 1000 box_2473 cert_2473 = true := by
  have h := List.all_eq_true.mp batch_49_09_ok accepted_2473 (by simp [batch_49_09_values])
  exact h
theorem leaf_2473_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2473.profileLo box_2473.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2473_ok
theorem branch_box_2473_nonnegative : ∀ j, 0 ≤ branch_box_2473.lower j ∧ 0 ≤ branch_box_2473.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2473, Box.profileLo, Box.profileHi, box_2473]
theorem leaf_2473_BranchSafe : CertificateConsequences.BranchSafe branch_box_2473 := by
  left; refine ⟨branch_box_2473_nonnegative, ?_⟩
  intro z hz; exact leaf_2473_sound hz

theorem leaf_2475_ok : checkAt 527 1000 box_2475 cert_2475 = true := by
  have h := List.all_eq_true.mp batch_49_10_ok accepted_2475 (by simp [batch_49_10_values])
  exact h
theorem leaf_2475_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2475.profileLo box_2475.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2475_ok
theorem branch_box_2475_nonnegative : ∀ j, 0 ≤ branch_box_2475.lower j ∧ 0 ≤ branch_box_2475.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2475, Box.profileLo, Box.profileHi, box_2475]
theorem leaf_2475_BranchSafe : CertificateConsequences.BranchSafe branch_box_2475 := by
  left; refine ⟨branch_box_2475_nonnegative, ?_⟩
  intro z hz; exact leaf_2475_sound hz

theorem leaf_2481_ok : checkAt 527 1000 box_2481 cert_2481 = true := by
  have h := List.all_eq_true.mp batch_49_11_ok accepted_2481 (by simp [batch_49_11_values])
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

theorem leaf_2483_ok : checkAt 527 1000 box_2483 cert_2483 = true := by
  have h := List.all_eq_true.mp batch_49_12_ok accepted_2483 (by simp [batch_49_12_values])
  exact h
theorem leaf_2483_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2483.profileLo box_2483.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2483_ok
theorem branch_box_2483_nonnegative : ∀ j, 0 ≤ branch_box_2483.lower j ∧ 0 ≤ branch_box_2483.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2483, Box.profileLo, Box.profileHi, box_2483]
theorem leaf_2483_BranchSafe : CertificateConsequences.BranchSafe branch_box_2483 := by
  left; refine ⟨branch_box_2483_nonnegative, ?_⟩
  intro z hz; exact leaf_2483_sound hz

theorem leaf_2486_ok : checkAt 527 1000 box_2486 cert_2486 = true := by
  have h := List.all_eq_true.mp batch_49_13_ok accepted_2486 (by simp [batch_49_13_values])
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
  have h := List.all_eq_true.mp batch_49_14_ok accepted_2487 (by simp [batch_49_14_values])
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
  have h := List.all_eq_true.mp batch_49_15_ok accepted_2489 (by simp [batch_49_15_values])
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

theorem leaf_2494_ok : checkAt 527 1000 box_2494 cert_2494 = true := by
  have h := List.all_eq_true.mp batch_49_16_ok accepted_2494 (by simp [batch_49_16_values])
  exact h
theorem leaf_2494_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2494.profileLo box_2494.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2494_ok
theorem branch_box_2494_nonnegative : ∀ j, 0 ≤ branch_box_2494.lower j ∧ 0 ≤ branch_box_2494.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2494, Box.profileLo, Box.profileHi, box_2494]
theorem leaf_2494_BranchSafe : CertificateConsequences.BranchSafe branch_box_2494 := by
  left; refine ⟨branch_box_2494_nonnegative, ?_⟩
  intro z hz; exact leaf_2494_sound hz

theorem leaf_2496_ok : checkAt 527 1000 box_2496 cert_2496 = true := by
  have h := List.all_eq_true.mp batch_49_17_ok accepted_2496 (by simp [batch_49_17_values])
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
  have h := List.all_eq_true.mp batch_49_18_ok accepted_2498 (by simp [batch_49_18_values])
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
  have h := List.all_eq_true.mp batch_49_19_ok accepted_2499 (by simp [batch_49_19_values])
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
#print axioms leaf_2450_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
