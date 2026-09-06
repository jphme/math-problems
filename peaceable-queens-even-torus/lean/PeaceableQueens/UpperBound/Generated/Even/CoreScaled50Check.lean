import PeaceableQueens.UpperBound.Generated.Even.CoreScaled50Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_50_00_values : List Bool := [accepted_2501]
theorem batch_50_00_ok : batch_50_00_values.all id = true := by decide

def batch_50_01_values : List Bool := [accepted_2509]
theorem batch_50_01_ok : batch_50_01_values.all id = true := by decide

def batch_50_02_values : List Bool := [accepted_2511]
theorem batch_50_02_ok : batch_50_02_values.all id = true := by decide

def batch_50_03_values : List Bool := [accepted_2513]
theorem batch_50_03_ok : batch_50_03_values.all id = true := by decide

def batch_50_04_values : List Bool := [accepted_2517]
theorem batch_50_04_ok : batch_50_04_values.all id = true := by decide

def batch_50_05_values : List Bool := [accepted_2519]
theorem batch_50_05_ok : batch_50_05_values.all id = true := by decide

def batch_50_06_values : List Bool := [accepted_2523]
theorem batch_50_06_ok : batch_50_06_values.all id = true := by decide

def batch_50_07_values : List Bool := [accepted_2527]
theorem batch_50_07_ok : batch_50_07_values.all id = true := by decide

def batch_50_08_values : List Bool := [accepted_2529]
theorem batch_50_08_ok : batch_50_08_values.all id = true := by decide

def batch_50_09_values : List Bool := [accepted_2532]
theorem batch_50_09_ok : batch_50_09_values.all id = true := by decide

def batch_50_10_values : List Bool := [accepted_2533]
theorem batch_50_10_ok : batch_50_10_values.all id = true := by decide

def batch_50_11_values : List Bool := [accepted_2535]
theorem batch_50_11_ok : batch_50_11_values.all id = true := by decide

def batch_50_12_values : List Bool := [accepted_2541]
theorem batch_50_12_ok : batch_50_12_values.all id = true := by decide

def batch_50_13_values : List Bool := [accepted_2543]
theorem batch_50_13_ok : batch_50_13_values.all id = true := by decide

def batch_50_14_values : List Bool := [accepted_2546]
theorem batch_50_14_ok : batch_50_14_values.all id = true := by decide

def batch_50_15_values : List Bool := [accepted_2547]
theorem batch_50_15_ok : batch_50_15_values.all id = true := by decide

def batch_50_16_values : List Bool := [accepted_2549]
theorem batch_50_16_ok : batch_50_16_values.all id = true := by decide

theorem leaf_2501_ok : checkAt 527 1000 box_2501 cert_2501 = true := by
  have h := List.all_eq_true.mp batch_50_00_ok accepted_2501 (by simp [batch_50_00_values])
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

theorem leaf_2509_ok : checkAt 527 1000 box_2509 cert_2509 = true := by
  have h := List.all_eq_true.mp batch_50_01_ok accepted_2509 (by simp [batch_50_01_values])
  exact h
theorem leaf_2509_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2509.profileLo box_2509.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2509_ok
theorem branch_box_2509_nonnegative : ∀ j, 0 ≤ branch_box_2509.lower j ∧ 0 ≤ branch_box_2509.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2509, Box.profileLo, Box.profileHi, box_2509]
theorem leaf_2509_BranchSafe : CertificateConsequences.BranchSafe branch_box_2509 := by
  left; refine ⟨branch_box_2509_nonnegative, ?_⟩
  intro z hz; exact leaf_2509_sound hz

theorem leaf_2511_ok : checkAt 527 1000 box_2511 cert_2511 = true := by
  have h := List.all_eq_true.mp batch_50_02_ok accepted_2511 (by simp [batch_50_02_values])
  exact h
theorem leaf_2511_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2511.profileLo box_2511.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2511_ok
theorem branch_box_2511_nonnegative : ∀ j, 0 ≤ branch_box_2511.lower j ∧ 0 ≤ branch_box_2511.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2511, Box.profileLo, Box.profileHi, box_2511]
theorem leaf_2511_BranchSafe : CertificateConsequences.BranchSafe branch_box_2511 := by
  left; refine ⟨branch_box_2511_nonnegative, ?_⟩
  intro z hz; exact leaf_2511_sound hz

theorem leaf_2513_ok : checkAt 527 1000 box_2513 cert_2513 = true := by
  have h := List.all_eq_true.mp batch_50_03_ok accepted_2513 (by simp [batch_50_03_values])
  exact h
theorem leaf_2513_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2513.profileLo box_2513.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2513_ok
theorem branch_box_2513_nonnegative : ∀ j, 0 ≤ branch_box_2513.lower j ∧ 0 ≤ branch_box_2513.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2513, Box.profileLo, Box.profileHi, box_2513]
theorem leaf_2513_BranchSafe : CertificateConsequences.BranchSafe branch_box_2513 := by
  left; refine ⟨branch_box_2513_nonnegative, ?_⟩
  intro z hz; exact leaf_2513_sound hz

theorem leaf_2517_ok : checkAt 527 1000 box_2517 cert_2517 = true := by
  have h := List.all_eq_true.mp batch_50_04_ok accepted_2517 (by simp [batch_50_04_values])
  exact h
theorem leaf_2517_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2517.profileLo box_2517.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2517_ok
theorem branch_box_2517_nonnegative : ∀ j, 0 ≤ branch_box_2517.lower j ∧ 0 ≤ branch_box_2517.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2517, Box.profileLo, Box.profileHi, box_2517]
theorem leaf_2517_BranchSafe : CertificateConsequences.BranchSafe branch_box_2517 := by
  left; refine ⟨branch_box_2517_nonnegative, ?_⟩
  intro z hz; exact leaf_2517_sound hz

theorem leaf_2519_ok : checkAt 527 1000 box_2519 cert_2519 = true := by
  have h := List.all_eq_true.mp batch_50_05_ok accepted_2519 (by simp [batch_50_05_values])
  exact h
theorem leaf_2519_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2519.profileLo box_2519.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2519_ok
theorem branch_box_2519_nonnegative : ∀ j, 0 ≤ branch_box_2519.lower j ∧ 0 ≤ branch_box_2519.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2519, Box.profileLo, Box.profileHi, box_2519]
theorem leaf_2519_BranchSafe : CertificateConsequences.BranchSafe branch_box_2519 := by
  left; refine ⟨branch_box_2519_nonnegative, ?_⟩
  intro z hz; exact leaf_2519_sound hz

theorem leaf_2523_ok : checkAt 527 1000 box_2523 cert_2523 = true := by
  have h := List.all_eq_true.mp batch_50_06_ok accepted_2523 (by simp [batch_50_06_values])
  exact h
theorem leaf_2523_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2523.profileLo box_2523.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2523_ok
theorem branch_box_2523_nonnegative : ∀ j, 0 ≤ branch_box_2523.lower j ∧ 0 ≤ branch_box_2523.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2523, Box.profileLo, Box.profileHi, box_2523]
theorem leaf_2523_BranchSafe : CertificateConsequences.BranchSafe branch_box_2523 := by
  left; refine ⟨branch_box_2523_nonnegative, ?_⟩
  intro z hz; exact leaf_2523_sound hz

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

theorem leaf_2529_ok : checkAt 527 1000 box_2529 cert_2529 = true := by
  have h := List.all_eq_true.mp batch_50_08_ok accepted_2529 (by simp [batch_50_08_values])
  exact h
theorem leaf_2529_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2529.profileLo box_2529.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2529_ok
theorem branch_box_2529_nonnegative : ∀ j, 0 ≤ branch_box_2529.lower j ∧ 0 ≤ branch_box_2529.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2529, Box.profileLo, Box.profileHi, box_2529]
theorem leaf_2529_BranchSafe : CertificateConsequences.BranchSafe branch_box_2529 := by
  left; refine ⟨branch_box_2529_nonnegative, ?_⟩
  intro z hz; exact leaf_2529_sound hz

theorem leaf_2532_ok : checkAt 527 1000 box_2532 cert_2532 = true := by
  have h := List.all_eq_true.mp batch_50_09_ok accepted_2532 (by simp [batch_50_09_values])
  exact h
theorem leaf_2532_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2532.profileLo box_2532.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2532_ok
theorem branch_box_2532_nonnegative : ∀ j, 0 ≤ branch_box_2532.lower j ∧ 0 ≤ branch_box_2532.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2532, Box.profileLo, Box.profileHi, box_2532]
theorem leaf_2532_BranchSafe : CertificateConsequences.BranchSafe branch_box_2532 := by
  left; refine ⟨branch_box_2532_nonnegative, ?_⟩
  intro z hz; exact leaf_2532_sound hz

theorem leaf_2533_ok : checkAt 527 1000 box_2533 cert_2533 = true := by
  have h := List.all_eq_true.mp batch_50_10_ok accepted_2533 (by simp [batch_50_10_values])
  exact h
theorem leaf_2533_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2533.profileLo box_2533.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2533_ok
theorem branch_box_2533_nonnegative : ∀ j, 0 ≤ branch_box_2533.lower j ∧ 0 ≤ branch_box_2533.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2533, Box.profileLo, Box.profileHi, box_2533]
theorem leaf_2533_BranchSafe : CertificateConsequences.BranchSafe branch_box_2533 := by
  left; refine ⟨branch_box_2533_nonnegative, ?_⟩
  intro z hz; exact leaf_2533_sound hz

theorem leaf_2535_ok : checkAt 527 1000 box_2535 cert_2535 = true := by
  have h := List.all_eq_true.mp batch_50_11_ok accepted_2535 (by simp [batch_50_11_values])
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

theorem leaf_2541_ok : checkAt 527 1000 box_2541 cert_2541 = true := by
  have h := List.all_eq_true.mp batch_50_12_ok accepted_2541 (by simp [batch_50_12_values])
  exact h
theorem leaf_2541_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2541.profileLo box_2541.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2541_ok
theorem branch_box_2541_nonnegative : ∀ j, 0 ≤ branch_box_2541.lower j ∧ 0 ≤ branch_box_2541.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2541, Box.profileLo, Box.profileHi, box_2541]
theorem leaf_2541_BranchSafe : CertificateConsequences.BranchSafe branch_box_2541 := by
  left; refine ⟨branch_box_2541_nonnegative, ?_⟩
  intro z hz; exact leaf_2541_sound hz

theorem leaf_2543_ok : checkAt 527 1000 box_2543 cert_2543 = true := by
  have h := List.all_eq_true.mp batch_50_13_ok accepted_2543 (by simp [batch_50_13_values])
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

theorem leaf_2546_ok : checkAt 527 1000 box_2546 cert_2546 = true := by
  have h := List.all_eq_true.mp batch_50_14_ok accepted_2546 (by simp [batch_50_14_values])
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
  have h := List.all_eq_true.mp batch_50_15_ok accepted_2547 (by simp [batch_50_15_values])
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

theorem leaf_2549_ok : checkAt 527 1000 box_2549 cert_2549 = true := by
  have h := List.all_eq_true.mp batch_50_16_ok accepted_2549 (by simp [batch_50_16_values])
  exact h
theorem leaf_2549_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2549.profileLo box_2549.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2549_ok
theorem branch_box_2549_nonnegative : ∀ j, 0 ≤ branch_box_2549.lower j ∧ 0 ≤ branch_box_2549.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2549, Box.profileLo, Box.profileHi, box_2549]
theorem leaf_2549_BranchSafe : CertificateConsequences.BranchSafe branch_box_2549 := by
  left; refine ⟨branch_box_2549_nonnegative, ?_⟩
  intro z hz; exact leaf_2549_sound hz

#print axioms batch_50_00_ok
#print axioms leaf_2501_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
