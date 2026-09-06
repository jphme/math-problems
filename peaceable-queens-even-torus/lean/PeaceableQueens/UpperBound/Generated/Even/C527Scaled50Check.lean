import PeaceableQueens.UpperBound.Generated.Even.C527Scaled50Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_50_00_values : List Bool := [accepted_2500]
theorem batch_50_00_ok : batch_50_00_values.all id = true := by decide

def batch_50_01_values : List Bool := [accepted_2501]
theorem batch_50_01_ok : batch_50_01_values.all id = true := by decide

def batch_50_02_values : List Bool := [accepted_2503]
theorem batch_50_02_ok : batch_50_02_values.all id = true := by decide

def batch_50_03_values : List Bool := [accepted_2505]
theorem batch_50_03_ok : batch_50_03_values.all id = true := by decide

def batch_50_04_values : List Bool := [accepted_2506]
theorem batch_50_04_ok : batch_50_04_values.all id = true := by decide

def batch_50_05_values : List Bool := [accepted_2521]
theorem batch_50_05_ok : batch_50_05_values.all id = true := by decide

def batch_50_06_values : List Bool := [accepted_2525]
theorem batch_50_06_ok : batch_50_06_values.all id = true := by decide

def batch_50_07_values : List Bool := [accepted_2527]
theorem batch_50_07_ok : batch_50_07_values.all id = true := by decide

def batch_50_08_values : List Bool := [accepted_2531]
theorem batch_50_08_ok : batch_50_08_values.all id = true := by decide

def batch_50_09_values : List Bool := [accepted_2534]
theorem batch_50_09_ok : batch_50_09_values.all id = true := by decide

def batch_50_10_values : List Bool := [accepted_2535]
theorem batch_50_10_ok : batch_50_10_values.all id = true := by decide

def batch_50_11_values : List Bool := [accepted_2537]
theorem batch_50_11_ok : batch_50_11_values.all id = true := by decide

def batch_50_12_values : List Bool := [accepted_2538]
theorem batch_50_12_ok : batch_50_12_values.all id = true := by decide

def batch_50_13_values : List Bool := [accepted_2542]
theorem batch_50_13_ok : batch_50_13_values.all id = true := by decide

def batch_50_14_values : List Bool := [accepted_2543]
theorem batch_50_14_ok : batch_50_14_values.all id = true := by decide

def batch_50_15_values : List Bool := [accepted_2544]
theorem batch_50_15_ok : batch_50_15_values.all id = true := by decide

def batch_50_16_values : List Bool := [accepted_2546]
theorem batch_50_16_ok : batch_50_16_values.all id = true := by decide

def batch_50_17_values : List Bool := [accepted_2547]
theorem batch_50_17_ok : batch_50_17_values.all id = true := by decide

def batch_50_18_values : List Bool := [accepted_2548]
theorem batch_50_18_ok : batch_50_18_values.all id = true := by decide

theorem leaf_2500_ok : checkAt 527 1000 box_2500 cert_2500 = true := by
  have h := List.all_eq_true.mp batch_50_00_ok accepted_2500 (by simp [batch_50_00_values])
  exact h
theorem leaf_2500_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2500.profileLo box_2500.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2500_ok
theorem branch_box_2500_nonnegative : ∀ j, 0 ≤ branch_box_2500.lower j ∧ 0 ≤ branch_box_2500.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2500, Box.profileLo, Box.profileHi, box_2500]
theorem leaf_2500_BranchSafe : CertificateConsequences.BranchSafe branch_box_2500 := by
  left; refine ⟨branch_box_2500_nonnegative, ?_⟩
  intro z hz; exact leaf_2500_sound hz

theorem leaf_2501_ok : checkAt 527 1000 box_2501 cert_2501 = true := by
  have h := List.all_eq_true.mp batch_50_01_ok accepted_2501 (by simp [batch_50_01_values])
  exact h
theorem leaf_2501_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2501.profileLo box_2501.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2501_ok
theorem branch_box_2501_nonnegative : ∀ j, 0 ≤ branch_box_2501.lower j ∧ 0 ≤ branch_box_2501.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2501, Box.profileLo, Box.profileHi, box_2501]
theorem leaf_2501_BranchSafe : CertificateConsequences.BranchSafe branch_box_2501 := by
  left; refine ⟨branch_box_2501_nonnegative, ?_⟩
  intro z hz; exact leaf_2501_sound hz

theorem leaf_2503_ok : checkAt 527 1000 box_2503 cert_2503 = true := by
  have h := List.all_eq_true.mp batch_50_02_ok accepted_2503 (by simp [batch_50_02_values])
  exact h
theorem leaf_2503_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2503.profileLo box_2503.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2503_ok
theorem branch_box_2503_nonnegative : ∀ j, 0 ≤ branch_box_2503.lower j ∧ 0 ≤ branch_box_2503.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2503, Box.profileLo, Box.profileHi, box_2503]
theorem leaf_2503_BranchSafe : CertificateConsequences.BranchSafe branch_box_2503 := by
  left; refine ⟨branch_box_2503_nonnegative, ?_⟩
  intro z hz; exact leaf_2503_sound hz

theorem leaf_2505_ok : checkAt 527 1000 box_2505 cert_2505 = true := by
  have h := List.all_eq_true.mp batch_50_03_ok accepted_2505 (by simp [batch_50_03_values])
  exact h
theorem leaf_2505_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2505.profileLo box_2505.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2505_ok
theorem branch_box_2505_nonnegative : ∀ j, 0 ≤ branch_box_2505.lower j ∧ 0 ≤ branch_box_2505.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2505, Box.profileLo, Box.profileHi, box_2505]
theorem leaf_2505_BranchSafe : CertificateConsequences.BranchSafe branch_box_2505 := by
  left; refine ⟨branch_box_2505_nonnegative, ?_⟩
  intro z hz; exact leaf_2505_sound hz

theorem leaf_2506_ok : checkAt 527 1000 box_2506 cert_2506 = true := by
  have h := List.all_eq_true.mp batch_50_04_ok accepted_2506 (by simp [batch_50_04_values])
  exact h
theorem leaf_2506_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2506.profileLo box_2506.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2506_ok
theorem branch_box_2506_nonnegative : ∀ j, 0 ≤ branch_box_2506.lower j ∧ 0 ≤ branch_box_2506.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2506, Box.profileLo, Box.profileHi, box_2506]
theorem leaf_2506_BranchSafe : CertificateConsequences.BranchSafe branch_box_2506 := by
  left; refine ⟨branch_box_2506_nonnegative, ?_⟩
  intro z hz; exact leaf_2506_sound hz

theorem leaf_2521_ok : checkAt 527 1000 box_2521 cert_2521 = true := by
  have h := List.all_eq_true.mp batch_50_05_ok accepted_2521 (by simp [batch_50_05_values])
  exact h
theorem leaf_2521_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2521.profileLo box_2521.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2521_ok
theorem branch_box_2521_nonnegative : ∀ j, 0 ≤ branch_box_2521.lower j ∧ 0 ≤ branch_box_2521.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2521, Box.profileLo, Box.profileHi, box_2521]
theorem leaf_2521_BranchSafe : CertificateConsequences.BranchSafe branch_box_2521 := by
  left; refine ⟨branch_box_2521_nonnegative, ?_⟩
  intro z hz; exact leaf_2521_sound hz

theorem leaf_2525_ok : checkAt 527 1000 box_2525 cert_2525 = true := by
  have h := List.all_eq_true.mp batch_50_06_ok accepted_2525 (by simp [batch_50_06_values])
  exact h
theorem leaf_2525_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2525.profileLo box_2525.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2525_ok
theorem branch_box_2525_nonnegative : ∀ j, 0 ≤ branch_box_2525.lower j ∧ 0 ≤ branch_box_2525.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2525, Box.profileLo, Box.profileHi, box_2525]
theorem leaf_2525_BranchSafe : CertificateConsequences.BranchSafe branch_box_2525 := by
  left; refine ⟨branch_box_2525_nonnegative, ?_⟩
  intro z hz; exact leaf_2525_sound hz

theorem leaf_2527_ok : checkAt 527 1000 box_2527 cert_2527 = true := by
  have h := List.all_eq_true.mp batch_50_07_ok accepted_2527 (by simp [batch_50_07_values])
  exact h
theorem leaf_2527_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2527.profileLo box_2527.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2527_ok
theorem branch_box_2527_nonnegative : ∀ j, 0 ≤ branch_box_2527.lower j ∧ 0 ≤ branch_box_2527.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2527, Box.profileLo, Box.profileHi, box_2527]
theorem leaf_2527_BranchSafe : CertificateConsequences.BranchSafe branch_box_2527 := by
  left; refine ⟨branch_box_2527_nonnegative, ?_⟩
  intro z hz; exact leaf_2527_sound hz

theorem leaf_2531_ok : checkAt 527 1000 box_2531 cert_2531 = true := by
  have h := List.all_eq_true.mp batch_50_08_ok accepted_2531 (by simp [batch_50_08_values])
  exact h
theorem leaf_2531_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2531.profileLo box_2531.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2531_ok
theorem branch_box_2531_nonnegative : ∀ j, 0 ≤ branch_box_2531.lower j ∧ 0 ≤ branch_box_2531.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2531, Box.profileLo, Box.profileHi, box_2531]
theorem leaf_2531_BranchSafe : CertificateConsequences.BranchSafe branch_box_2531 := by
  left; refine ⟨branch_box_2531_nonnegative, ?_⟩
  intro z hz; exact leaf_2531_sound hz

theorem leaf_2534_ok : checkAt 527 1000 box_2534 cert_2534 = true := by
  have h := List.all_eq_true.mp batch_50_09_ok accepted_2534 (by simp [batch_50_09_values])
  exact h
theorem leaf_2534_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2534.profileLo box_2534.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2534_ok
theorem branch_box_2534_nonnegative : ∀ j, 0 ≤ branch_box_2534.lower j ∧ 0 ≤ branch_box_2534.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2534, Box.profileLo, Box.profileHi, box_2534]
theorem leaf_2534_BranchSafe : CertificateConsequences.BranchSafe branch_box_2534 := by
  left; refine ⟨branch_box_2534_nonnegative, ?_⟩
  intro z hz; exact leaf_2534_sound hz

theorem leaf_2535_ok : checkAt 527 1000 box_2535 cert_2535 = true := by
  have h := List.all_eq_true.mp batch_50_10_ok accepted_2535 (by simp [batch_50_10_values])
  exact h
theorem leaf_2535_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2535.profileLo box_2535.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2535_ok
theorem branch_box_2535_nonnegative : ∀ j, 0 ≤ branch_box_2535.lower j ∧ 0 ≤ branch_box_2535.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2535, Box.profileLo, Box.profileHi, box_2535]
theorem leaf_2535_BranchSafe : CertificateConsequences.BranchSafe branch_box_2535 := by
  left; refine ⟨branch_box_2535_nonnegative, ?_⟩
  intro z hz; exact leaf_2535_sound hz

theorem leaf_2537_ok : checkAt 527 1000 box_2537 cert_2537 = true := by
  have h := List.all_eq_true.mp batch_50_11_ok accepted_2537 (by simp [batch_50_11_values])
  exact h
theorem leaf_2537_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2537.profileLo box_2537.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2537_ok
theorem branch_box_2537_nonnegative : ∀ j, 0 ≤ branch_box_2537.lower j ∧ 0 ≤ branch_box_2537.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2537, Box.profileLo, Box.profileHi, box_2537]
theorem leaf_2537_BranchSafe : CertificateConsequences.BranchSafe branch_box_2537 := by
  left; refine ⟨branch_box_2537_nonnegative, ?_⟩
  intro z hz; exact leaf_2537_sound hz

theorem leaf_2538_ok : checkAt 527 1000 box_2538 cert_2538 = true := by
  have h := List.all_eq_true.mp batch_50_12_ok accepted_2538 (by simp [batch_50_12_values])
  exact h
theorem leaf_2538_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2538.profileLo box_2538.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2538_ok
theorem branch_box_2538_nonnegative : ∀ j, 0 ≤ branch_box_2538.lower j ∧ 0 ≤ branch_box_2538.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2538, Box.profileLo, Box.profileHi, box_2538]
theorem leaf_2538_BranchSafe : CertificateConsequences.BranchSafe branch_box_2538 := by
  left; refine ⟨branch_box_2538_nonnegative, ?_⟩
  intro z hz; exact leaf_2538_sound hz

theorem leaf_2542_ok : checkAt 527 1000 box_2542 cert_2542 = true := by
  have h := List.all_eq_true.mp batch_50_13_ok accepted_2542 (by simp [batch_50_13_values])
  exact h
theorem leaf_2542_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2542.profileLo box_2542.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2542_ok
theorem branch_box_2542_nonnegative : ∀ j, 0 ≤ branch_box_2542.lower j ∧ 0 ≤ branch_box_2542.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2542, Box.profileLo, Box.profileHi, box_2542]
theorem leaf_2542_BranchSafe : CertificateConsequences.BranchSafe branch_box_2542 := by
  left; refine ⟨branch_box_2542_nonnegative, ?_⟩
  intro z hz; exact leaf_2542_sound hz

theorem leaf_2543_ok : checkAt 527 1000 box_2543 cert_2543 = true := by
  have h := List.all_eq_true.mp batch_50_14_ok accepted_2543 (by simp [batch_50_14_values])
  exact h
theorem leaf_2543_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2543.profileLo box_2543.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2543_ok
theorem branch_box_2543_nonnegative : ∀ j, 0 ≤ branch_box_2543.lower j ∧ 0 ≤ branch_box_2543.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2543, Box.profileLo, Box.profileHi, box_2543]
theorem leaf_2543_BranchSafe : CertificateConsequences.BranchSafe branch_box_2543 := by
  left; refine ⟨branch_box_2543_nonnegative, ?_⟩
  intro z hz; exact leaf_2543_sound hz

theorem leaf_2544_ok : checkAt 527 1000 box_2544 cert_2544 = true := by
  have h := List.all_eq_true.mp batch_50_15_ok accepted_2544 (by simp [batch_50_15_values])
  exact h
theorem leaf_2544_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2544.profileLo box_2544.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2544_ok
theorem branch_box_2544_nonnegative : ∀ j, 0 ≤ branch_box_2544.lower j ∧ 0 ≤ branch_box_2544.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2544, Box.profileLo, Box.profileHi, box_2544]
theorem leaf_2544_BranchSafe : CertificateConsequences.BranchSafe branch_box_2544 := by
  left; refine ⟨branch_box_2544_nonnegative, ?_⟩
  intro z hz; exact leaf_2544_sound hz

theorem leaf_2546_ok : checkAt 527 1000 box_2546 cert_2546 = true := by
  have h := List.all_eq_true.mp batch_50_16_ok accepted_2546 (by simp [batch_50_16_values])
  exact h
theorem leaf_2546_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2546.profileLo box_2546.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2546_ok
theorem branch_box_2546_nonnegative : ∀ j, 0 ≤ branch_box_2546.lower j ∧ 0 ≤ branch_box_2546.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2546, Box.profileLo, Box.profileHi, box_2546]
theorem leaf_2546_BranchSafe : CertificateConsequences.BranchSafe branch_box_2546 := by
  left; refine ⟨branch_box_2546_nonnegative, ?_⟩
  intro z hz; exact leaf_2546_sound hz

theorem leaf_2547_ok : checkAt 527 1000 box_2547 cert_2547 = true := by
  have h := List.all_eq_true.mp batch_50_17_ok accepted_2547 (by simp [batch_50_17_values])
  exact h
theorem leaf_2547_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2547.profileLo box_2547.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2547_ok
theorem branch_box_2547_nonnegative : ∀ j, 0 ≤ branch_box_2547.lower j ∧ 0 ≤ branch_box_2547.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2547, Box.profileLo, Box.profileHi, box_2547]
theorem leaf_2547_BranchSafe : CertificateConsequences.BranchSafe branch_box_2547 := by
  left; refine ⟨branch_box_2547_nonnegative, ?_⟩
  intro z hz; exact leaf_2547_sound hz

theorem leaf_2548_ok : checkAt 527 1000 box_2548 cert_2548 = true := by
  have h := List.all_eq_true.mp batch_50_18_ok accepted_2548 (by simp [batch_50_18_values])
  exact h
theorem leaf_2548_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2548.profileLo box_2548.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2548_ok
theorem branch_box_2548_nonnegative : ∀ j, 0 ≤ branch_box_2548.lower j ∧ 0 ≤ branch_box_2548.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2548, Box.profileLo, Box.profileHi, box_2548]
theorem leaf_2548_BranchSafe : CertificateConsequences.BranchSafe branch_box_2548 := by
  left; refine ⟨branch_box_2548_nonnegative, ?_⟩
  intro z hz; exact leaf_2548_sound hz

#print axioms batch_50_00_ok
#print axioms leaf_2500_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
