import PeaceableQueens.UpperBound.Generated.Even.C527Scaled109Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_109_00_values : List Bool := [accepted_5453]
theorem batch_109_00_ok : batch_109_00_values.all id = true := by decide

def batch_109_01_values : List Bool := [accepted_5454]
theorem batch_109_01_ok : batch_109_01_values.all id = true := by decide

def batch_109_02_values : List Bool := [accepted_5455]
theorem batch_109_02_ok : batch_109_02_values.all id = true := by decide

def batch_109_03_values : List Bool := [accepted_5456]
theorem batch_109_03_ok : batch_109_03_values.all id = true := by decide

def batch_109_04_values : List Bool := [accepted_5463]
theorem batch_109_04_ok : batch_109_04_values.all id = true := by decide

def batch_109_05_values : List Bool := [accepted_5464]
theorem batch_109_05_ok : batch_109_05_values.all id = true := by decide

def batch_109_06_values : List Bool := [accepted_5468]
theorem batch_109_06_ok : batch_109_06_values.all id = true := by decide

def batch_109_07_values : List Bool := [accepted_5469]
theorem batch_109_07_ok : batch_109_07_values.all id = true := by decide

def batch_109_08_values : List Bool := [accepted_5470]
theorem batch_109_08_ok : batch_109_08_values.all id = true := by decide

def batch_109_09_values : List Bool := [accepted_5471]
theorem batch_109_09_ok : batch_109_09_values.all id = true := by decide

def batch_109_10_values : List Bool := [accepted_5472]
theorem batch_109_10_ok : batch_109_10_values.all id = true := by decide

def batch_109_11_values : List Bool := [accepted_5475]
theorem batch_109_11_ok : batch_109_11_values.all id = true := by decide

def batch_109_12_values : List Bool := [accepted_5477]
theorem batch_109_12_ok : batch_109_12_values.all id = true := by decide

def batch_109_13_values : List Bool := [accepted_5478]
theorem batch_109_13_ok : batch_109_13_values.all id = true := by decide

def batch_109_14_values : List Bool := [accepted_5479]
theorem batch_109_14_ok : batch_109_14_values.all id = true := by decide

def batch_109_15_values : List Bool := [accepted_5480]
theorem batch_109_15_ok : batch_109_15_values.all id = true := by decide

def batch_109_16_values : List Bool := [accepted_5487]
theorem batch_109_16_ok : batch_109_16_values.all id = true := by decide

def batch_109_17_values : List Bool := [accepted_5488]
theorem batch_109_17_ok : batch_109_17_values.all id = true := by decide

def batch_109_18_values : List Bool := [accepted_5489]
theorem batch_109_18_ok : batch_109_18_values.all id = true := by decide

def batch_109_19_values : List Bool := [accepted_5490]
theorem batch_109_19_ok : batch_109_19_values.all id = true := by decide

def batch_109_20_values : List Bool := [accepted_5492]
theorem batch_109_20_ok : batch_109_20_values.all id = true := by decide

def batch_109_21_values : List Bool := [accepted_5493]
theorem batch_109_21_ok : batch_109_21_values.all id = true := by decide

def batch_109_22_values : List Bool := [accepted_5494]
theorem batch_109_22_ok : batch_109_22_values.all id = true := by decide

def batch_109_23_values : List Bool := [accepted_5499]
theorem batch_109_23_ok : batch_109_23_values.all id = true := by decide

theorem leaf_5453_ok : checkAt 527 1000 box_5453 cert_5453 = true := by
  have h := List.all_eq_true.mp batch_109_00_ok accepted_5453 (by simp [batch_109_00_values])
  exact h
theorem leaf_5453_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5453.profileLo box_5453.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5453_ok
theorem branch_box_5453_nonnegative : ∀ j, 0 ≤ branch_box_5453.lower j ∧ 0 ≤ branch_box_5453.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5453, Box.profileLo, Box.profileHi, box_5453]
theorem leaf_5453_BranchSafe : CertificateConsequences.BranchSafe branch_box_5453 := by
  left; refine ⟨branch_box_5453_nonnegative, ?_⟩
  intro z hz; exact leaf_5453_sound hz

theorem leaf_5454_ok : checkAt 527 1000 box_5454 cert_5454 = true := by
  have h := List.all_eq_true.mp batch_109_01_ok accepted_5454 (by simp [batch_109_01_values])
  exact h
theorem leaf_5454_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5454.profileLo box_5454.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5454_ok
theorem branch_box_5454_nonnegative : ∀ j, 0 ≤ branch_box_5454.lower j ∧ 0 ≤ branch_box_5454.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5454, Box.profileLo, Box.profileHi, box_5454]
theorem leaf_5454_BranchSafe : CertificateConsequences.BranchSafe branch_box_5454 := by
  left; refine ⟨branch_box_5454_nonnegative, ?_⟩
  intro z hz; exact leaf_5454_sound hz

theorem leaf_5455_ok : checkAt 527 1000 box_5455 cert_5455 = true := by
  have h := List.all_eq_true.mp batch_109_02_ok accepted_5455 (by simp [batch_109_02_values])
  exact h
theorem leaf_5455_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5455.profileLo box_5455.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5455_ok
theorem branch_box_5455_nonnegative : ∀ j, 0 ≤ branch_box_5455.lower j ∧ 0 ≤ branch_box_5455.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5455, Box.profileLo, Box.profileHi, box_5455]
theorem leaf_5455_BranchSafe : CertificateConsequences.BranchSafe branch_box_5455 := by
  left; refine ⟨branch_box_5455_nonnegative, ?_⟩
  intro z hz; exact leaf_5455_sound hz

theorem leaf_5456_ok : checkAt 527 1000 box_5456 cert_5456 = true := by
  have h := List.all_eq_true.mp batch_109_03_ok accepted_5456 (by simp [batch_109_03_values])
  exact h
theorem leaf_5456_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5456.profileLo box_5456.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5456_ok
theorem branch_box_5456_nonnegative : ∀ j, 0 ≤ branch_box_5456.lower j ∧ 0 ≤ branch_box_5456.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5456, Box.profileLo, Box.profileHi, box_5456]
theorem leaf_5456_BranchSafe : CertificateConsequences.BranchSafe branch_box_5456 := by
  left; refine ⟨branch_box_5456_nonnegative, ?_⟩
  intro z hz; exact leaf_5456_sound hz

theorem leaf_5463_ok : checkAt 527 1000 box_5463 cert_5463 = true := by
  have h := List.all_eq_true.mp batch_109_04_ok accepted_5463 (by simp [batch_109_04_values])
  exact h
theorem leaf_5463_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5463.profileLo box_5463.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5463_ok
theorem branch_box_5463_nonnegative : ∀ j, 0 ≤ branch_box_5463.lower j ∧ 0 ≤ branch_box_5463.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5463, Box.profileLo, Box.profileHi, box_5463]
theorem leaf_5463_BranchSafe : CertificateConsequences.BranchSafe branch_box_5463 := by
  left; refine ⟨branch_box_5463_nonnegative, ?_⟩
  intro z hz; exact leaf_5463_sound hz

theorem leaf_5464_ok : checkAt 527 1000 box_5464 cert_5464 = true := by
  have h := List.all_eq_true.mp batch_109_05_ok accepted_5464 (by simp [batch_109_05_values])
  exact h
theorem leaf_5464_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5464.profileLo box_5464.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5464_ok
theorem branch_box_5464_nonnegative : ∀ j, 0 ≤ branch_box_5464.lower j ∧ 0 ≤ branch_box_5464.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5464, Box.profileLo, Box.profileHi, box_5464]
theorem leaf_5464_BranchSafe : CertificateConsequences.BranchSafe branch_box_5464 := by
  left; refine ⟨branch_box_5464_nonnegative, ?_⟩
  intro z hz; exact leaf_5464_sound hz

theorem leaf_5468_ok : checkAt 527 1000 box_5468 cert_5468 = true := by
  have h := List.all_eq_true.mp batch_109_06_ok accepted_5468 (by simp [batch_109_06_values])
  exact h
theorem leaf_5468_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5468.profileLo box_5468.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5468_ok
theorem branch_box_5468_nonnegative : ∀ j, 0 ≤ branch_box_5468.lower j ∧ 0 ≤ branch_box_5468.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5468, Box.profileLo, Box.profileHi, box_5468]
theorem leaf_5468_BranchSafe : CertificateConsequences.BranchSafe branch_box_5468 := by
  left; refine ⟨branch_box_5468_nonnegative, ?_⟩
  intro z hz; exact leaf_5468_sound hz

theorem leaf_5469_ok : checkAt 527 1000 box_5469 cert_5469 = true := by
  have h := List.all_eq_true.mp batch_109_07_ok accepted_5469 (by simp [batch_109_07_values])
  exact h
theorem leaf_5469_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5469.profileLo box_5469.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5469_ok
theorem branch_box_5469_nonnegative : ∀ j, 0 ≤ branch_box_5469.lower j ∧ 0 ≤ branch_box_5469.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5469, Box.profileLo, Box.profileHi, box_5469]
theorem leaf_5469_BranchSafe : CertificateConsequences.BranchSafe branch_box_5469 := by
  left; refine ⟨branch_box_5469_nonnegative, ?_⟩
  intro z hz; exact leaf_5469_sound hz

theorem leaf_5470_ok : checkAt 527 1000 box_5470 cert_5470 = true := by
  have h := List.all_eq_true.mp batch_109_08_ok accepted_5470 (by simp [batch_109_08_values])
  exact h
theorem leaf_5470_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5470.profileLo box_5470.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5470_ok
theorem branch_box_5470_nonnegative : ∀ j, 0 ≤ branch_box_5470.lower j ∧ 0 ≤ branch_box_5470.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5470, Box.profileLo, Box.profileHi, box_5470]
theorem leaf_5470_BranchSafe : CertificateConsequences.BranchSafe branch_box_5470 := by
  left; refine ⟨branch_box_5470_nonnegative, ?_⟩
  intro z hz; exact leaf_5470_sound hz

theorem leaf_5471_ok : checkAt 527 1000 box_5471 cert_5471 = true := by
  have h := List.all_eq_true.mp batch_109_09_ok accepted_5471 (by simp [batch_109_09_values])
  exact h
theorem leaf_5471_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5471.profileLo box_5471.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5471_ok
theorem branch_box_5471_nonnegative : ∀ j, 0 ≤ branch_box_5471.lower j ∧ 0 ≤ branch_box_5471.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5471, Box.profileLo, Box.profileHi, box_5471]
theorem leaf_5471_BranchSafe : CertificateConsequences.BranchSafe branch_box_5471 := by
  left; refine ⟨branch_box_5471_nonnegative, ?_⟩
  intro z hz; exact leaf_5471_sound hz

theorem leaf_5472_ok : checkAt 527 1000 box_5472 cert_5472 = true := by
  have h := List.all_eq_true.mp batch_109_10_ok accepted_5472 (by simp [batch_109_10_values])
  exact h
theorem leaf_5472_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5472.profileLo box_5472.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5472_ok
theorem branch_box_5472_nonnegative : ∀ j, 0 ≤ branch_box_5472.lower j ∧ 0 ≤ branch_box_5472.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5472, Box.profileLo, Box.profileHi, box_5472]
theorem leaf_5472_BranchSafe : CertificateConsequences.BranchSafe branch_box_5472 := by
  left; refine ⟨branch_box_5472_nonnegative, ?_⟩
  intro z hz; exact leaf_5472_sound hz

theorem leaf_5475_ok : checkAt 527 1000 box_5475 cert_5475 = true := by
  have h := List.all_eq_true.mp batch_109_11_ok accepted_5475 (by simp [batch_109_11_values])
  exact h
theorem leaf_5475_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5475.profileLo box_5475.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5475_ok
theorem branch_box_5475_nonnegative : ∀ j, 0 ≤ branch_box_5475.lower j ∧ 0 ≤ branch_box_5475.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5475, Box.profileLo, Box.profileHi, box_5475]
theorem leaf_5475_BranchSafe : CertificateConsequences.BranchSafe branch_box_5475 := by
  left; refine ⟨branch_box_5475_nonnegative, ?_⟩
  intro z hz; exact leaf_5475_sound hz

theorem leaf_5477_ok : checkAt 527 1000 box_5477 cert_5477 = true := by
  have h := List.all_eq_true.mp batch_109_12_ok accepted_5477 (by simp [batch_109_12_values])
  exact h
theorem leaf_5477_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5477.profileLo box_5477.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5477_ok
theorem branch_box_5477_nonnegative : ∀ j, 0 ≤ branch_box_5477.lower j ∧ 0 ≤ branch_box_5477.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5477, Box.profileLo, Box.profileHi, box_5477]
theorem leaf_5477_BranchSafe : CertificateConsequences.BranchSafe branch_box_5477 := by
  left; refine ⟨branch_box_5477_nonnegative, ?_⟩
  intro z hz; exact leaf_5477_sound hz

theorem leaf_5478_ok : checkAt 527 1000 box_5478 cert_5478 = true := by
  have h := List.all_eq_true.mp batch_109_13_ok accepted_5478 (by simp [batch_109_13_values])
  exact h
theorem leaf_5478_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5478.profileLo box_5478.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5478_ok
theorem branch_box_5478_nonnegative : ∀ j, 0 ≤ branch_box_5478.lower j ∧ 0 ≤ branch_box_5478.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5478, Box.profileLo, Box.profileHi, box_5478]
theorem leaf_5478_BranchSafe : CertificateConsequences.BranchSafe branch_box_5478 := by
  left; refine ⟨branch_box_5478_nonnegative, ?_⟩
  intro z hz; exact leaf_5478_sound hz

theorem leaf_5479_ok : checkAt 527 1000 box_5479 cert_5479 = true := by
  have h := List.all_eq_true.mp batch_109_14_ok accepted_5479 (by simp [batch_109_14_values])
  exact h
theorem leaf_5479_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5479.profileLo box_5479.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5479_ok
theorem branch_box_5479_nonnegative : ∀ j, 0 ≤ branch_box_5479.lower j ∧ 0 ≤ branch_box_5479.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5479, Box.profileLo, Box.profileHi, box_5479]
theorem leaf_5479_BranchSafe : CertificateConsequences.BranchSafe branch_box_5479 := by
  left; refine ⟨branch_box_5479_nonnegative, ?_⟩
  intro z hz; exact leaf_5479_sound hz

theorem leaf_5480_ok : checkAt 527 1000 box_5480 cert_5480 = true := by
  have h := List.all_eq_true.mp batch_109_15_ok accepted_5480 (by simp [batch_109_15_values])
  exact h
theorem leaf_5480_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5480.profileLo box_5480.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5480_ok
theorem branch_box_5480_nonnegative : ∀ j, 0 ≤ branch_box_5480.lower j ∧ 0 ≤ branch_box_5480.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5480, Box.profileLo, Box.profileHi, box_5480]
theorem leaf_5480_BranchSafe : CertificateConsequences.BranchSafe branch_box_5480 := by
  left; refine ⟨branch_box_5480_nonnegative, ?_⟩
  intro z hz; exact leaf_5480_sound hz

theorem leaf_5487_ok : checkAt 527 1000 box_5487 cert_5487 = true := by
  have h := List.all_eq_true.mp batch_109_16_ok accepted_5487 (by simp [batch_109_16_values])
  exact h
theorem leaf_5487_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5487.profileLo box_5487.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5487_ok
theorem branch_box_5487_nonnegative : ∀ j, 0 ≤ branch_box_5487.lower j ∧ 0 ≤ branch_box_5487.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5487, Box.profileLo, Box.profileHi, box_5487]
theorem leaf_5487_BranchSafe : CertificateConsequences.BranchSafe branch_box_5487 := by
  left; refine ⟨branch_box_5487_nonnegative, ?_⟩
  intro z hz; exact leaf_5487_sound hz

theorem leaf_5488_ok : checkAt 527 1000 box_5488 cert_5488 = true := by
  have h := List.all_eq_true.mp batch_109_17_ok accepted_5488 (by simp [batch_109_17_values])
  exact h
theorem leaf_5488_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5488.profileLo box_5488.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5488_ok
theorem branch_box_5488_nonnegative : ∀ j, 0 ≤ branch_box_5488.lower j ∧ 0 ≤ branch_box_5488.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5488, Box.profileLo, Box.profileHi, box_5488]
theorem leaf_5488_BranchSafe : CertificateConsequences.BranchSafe branch_box_5488 := by
  left; refine ⟨branch_box_5488_nonnegative, ?_⟩
  intro z hz; exact leaf_5488_sound hz

theorem leaf_5489_ok : checkAt 527 1000 box_5489 cert_5489 = true := by
  have h := List.all_eq_true.mp batch_109_18_ok accepted_5489 (by simp [batch_109_18_values])
  exact h
theorem leaf_5489_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5489.profileLo box_5489.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5489_ok
theorem branch_box_5489_nonnegative : ∀ j, 0 ≤ branch_box_5489.lower j ∧ 0 ≤ branch_box_5489.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5489, Box.profileLo, Box.profileHi, box_5489]
theorem leaf_5489_BranchSafe : CertificateConsequences.BranchSafe branch_box_5489 := by
  left; refine ⟨branch_box_5489_nonnegative, ?_⟩
  intro z hz; exact leaf_5489_sound hz

theorem leaf_5490_ok : checkAt 527 1000 box_5490 cert_5490 = true := by
  have h := List.all_eq_true.mp batch_109_19_ok accepted_5490 (by simp [batch_109_19_values])
  exact h
theorem leaf_5490_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5490.profileLo box_5490.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5490_ok
theorem branch_box_5490_nonnegative : ∀ j, 0 ≤ branch_box_5490.lower j ∧ 0 ≤ branch_box_5490.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5490, Box.profileLo, Box.profileHi, box_5490]
theorem leaf_5490_BranchSafe : CertificateConsequences.BranchSafe branch_box_5490 := by
  left; refine ⟨branch_box_5490_nonnegative, ?_⟩
  intro z hz; exact leaf_5490_sound hz

theorem leaf_5492_ok : checkAt 527 1000 box_5492 cert_5492 = true := by
  have h := List.all_eq_true.mp batch_109_20_ok accepted_5492 (by simp [batch_109_20_values])
  exact h
theorem leaf_5492_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5492.profileLo box_5492.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5492_ok
theorem branch_box_5492_nonnegative : ∀ j, 0 ≤ branch_box_5492.lower j ∧ 0 ≤ branch_box_5492.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5492, Box.profileLo, Box.profileHi, box_5492]
theorem leaf_5492_BranchSafe : CertificateConsequences.BranchSafe branch_box_5492 := by
  left; refine ⟨branch_box_5492_nonnegative, ?_⟩
  intro z hz; exact leaf_5492_sound hz

theorem leaf_5493_ok : checkAt 527 1000 box_5493 cert_5493 = true := by
  have h := List.all_eq_true.mp batch_109_21_ok accepted_5493 (by simp [batch_109_21_values])
  exact h
theorem leaf_5493_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5493.profileLo box_5493.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5493_ok
theorem branch_box_5493_nonnegative : ∀ j, 0 ≤ branch_box_5493.lower j ∧ 0 ≤ branch_box_5493.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5493, Box.profileLo, Box.profileHi, box_5493]
theorem leaf_5493_BranchSafe : CertificateConsequences.BranchSafe branch_box_5493 := by
  left; refine ⟨branch_box_5493_nonnegative, ?_⟩
  intro z hz; exact leaf_5493_sound hz

theorem leaf_5494_ok : checkAt 527 1000 box_5494 cert_5494 = true := by
  have h := List.all_eq_true.mp batch_109_22_ok accepted_5494 (by simp [batch_109_22_values])
  exact h
theorem leaf_5494_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5494.profileLo box_5494.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5494_ok
theorem branch_box_5494_nonnegative : ∀ j, 0 ≤ branch_box_5494.lower j ∧ 0 ≤ branch_box_5494.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5494, Box.profileLo, Box.profileHi, box_5494]
theorem leaf_5494_BranchSafe : CertificateConsequences.BranchSafe branch_box_5494 := by
  left; refine ⟨branch_box_5494_nonnegative, ?_⟩
  intro z hz; exact leaf_5494_sound hz

theorem leaf_5499_ok : checkAt 527 1000 box_5499 cert_5499 = true := by
  have h := List.all_eq_true.mp batch_109_23_ok accepted_5499 (by simp [batch_109_23_values])
  exact h
theorem leaf_5499_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5499.profileLo box_5499.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5499_ok
theorem branch_box_5499_nonnegative : ∀ j, 0 ≤ branch_box_5499.lower j ∧ 0 ≤ branch_box_5499.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5499, Box.profileLo, Box.profileHi, box_5499]
theorem leaf_5499_BranchSafe : CertificateConsequences.BranchSafe branch_box_5499 := by
  left; refine ⟨branch_box_5499_nonnegative, ?_⟩
  intro z hz; exact leaf_5499_sound hz

#print axioms batch_109_00_ok
#print axioms leaf_5453_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
