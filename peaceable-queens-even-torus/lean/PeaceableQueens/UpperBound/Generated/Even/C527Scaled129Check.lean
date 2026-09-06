import PeaceableQueens.UpperBound.Generated.Even.C527Scaled129Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_129_00_values : List Bool := [accepted_6453]
theorem batch_129_00_ok : batch_129_00_values.all id = true := by decide

def batch_129_01_values : List Bool := [accepted_6454]
theorem batch_129_01_ok : batch_129_01_values.all id = true := by decide

def batch_129_02_values : List Bool := [accepted_6461]
theorem batch_129_02_ok : batch_129_02_values.all id = true := by decide

def batch_129_03_values : List Bool := [accepted_6462]
theorem batch_129_03_ok : batch_129_03_values.all id = true := by decide

def batch_129_04_values : List Bool := [accepted_6473]
theorem batch_129_04_ok : batch_129_04_values.all id = true := by decide

def batch_129_05_values : List Bool := [accepted_6474]
theorem batch_129_05_ok : batch_129_05_values.all id = true := by decide

def batch_129_06_values : List Bool := [accepted_6475]
theorem batch_129_06_ok : batch_129_06_values.all id = true := by decide

def batch_129_07_values : List Bool := [accepted_6477]
theorem batch_129_07_ok : batch_129_07_values.all id = true := by decide

def batch_129_08_values : List Bool := [accepted_6478]
theorem batch_129_08_ok : batch_129_08_values.all id = true := by decide

def batch_129_09_values : List Bool := [accepted_6479]
theorem batch_129_09_ok : batch_129_09_values.all id = true := by decide

def batch_129_10_values : List Bool := [accepted_6481]
theorem batch_129_10_ok : batch_129_10_values.all id = true := by decide

def batch_129_11_values : List Bool := [accepted_6482]
theorem batch_129_11_ok : batch_129_11_values.all id = true := by decide

def batch_129_12_values : List Bool := [accepted_6483]
theorem batch_129_12_ok : batch_129_12_values.all id = true := by decide

def batch_129_13_values : List Bool := [accepted_6489]
theorem batch_129_13_ok : batch_129_13_values.all id = true := by decide

def batch_129_14_values : List Bool := [accepted_6490]
theorem batch_129_14_ok : batch_129_14_values.all id = true := by decide

def batch_129_15_values : List Bool := [accepted_6491]
theorem batch_129_15_ok : batch_129_15_values.all id = true := by decide

def batch_129_16_values : List Bool := [accepted_6492]
theorem batch_129_16_ok : batch_129_16_values.all id = true := by decide

def batch_129_17_values : List Bool := [accepted_6495]
theorem batch_129_17_ok : batch_129_17_values.all id = true := by decide

def batch_129_18_values : List Bool := [accepted_6496]
theorem batch_129_18_ok : batch_129_18_values.all id = true := by decide

def batch_129_19_values : List Bool := [accepted_6499]
theorem batch_129_19_ok : batch_129_19_values.all id = true := by decide

theorem leaf_6453_ok : checkAt 527 1000 box_6453 cert_6453 = true := by
  have h := List.all_eq_true.mp batch_129_00_ok accepted_6453 (by simp [batch_129_00_values])
  exact h
theorem leaf_6453_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6453.profileLo box_6453.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6453_ok
theorem branch_box_6453_nonnegative : ∀ j, 0 ≤ branch_box_6453.lower j ∧ 0 ≤ branch_box_6453.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6453, Box.profileLo, Box.profileHi, box_6453]
theorem leaf_6453_BranchSafe : CertificateConsequences.BranchSafe branch_box_6453 := by
  left; refine ⟨branch_box_6453_nonnegative, ?_⟩
  intro z hz; exact leaf_6453_sound hz

theorem leaf_6454_ok : checkAt 527 1000 box_6454 cert_6454 = true := by
  have h := List.all_eq_true.mp batch_129_01_ok accepted_6454 (by simp [batch_129_01_values])
  exact h
theorem leaf_6454_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6454.profileLo box_6454.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6454_ok
theorem branch_box_6454_nonnegative : ∀ j, 0 ≤ branch_box_6454.lower j ∧ 0 ≤ branch_box_6454.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6454, Box.profileLo, Box.profileHi, box_6454]
theorem leaf_6454_BranchSafe : CertificateConsequences.BranchSafe branch_box_6454 := by
  left; refine ⟨branch_box_6454_nonnegative, ?_⟩
  intro z hz; exact leaf_6454_sound hz

theorem leaf_6461_ok : checkAt 527 1000 box_6461 cert_6461 = true := by
  have h := List.all_eq_true.mp batch_129_02_ok accepted_6461 (by simp [batch_129_02_values])
  exact h
theorem leaf_6461_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6461.profileLo box_6461.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6461_ok
theorem branch_box_6461_nonnegative : ∀ j, 0 ≤ branch_box_6461.lower j ∧ 0 ≤ branch_box_6461.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6461, Box.profileLo, Box.profileHi, box_6461]
theorem leaf_6461_BranchSafe : CertificateConsequences.BranchSafe branch_box_6461 := by
  left; refine ⟨branch_box_6461_nonnegative, ?_⟩
  intro z hz; exact leaf_6461_sound hz

theorem leaf_6462_ok : checkAt 527 1000 box_6462 cert_6462 = true := by
  have h := List.all_eq_true.mp batch_129_03_ok accepted_6462 (by simp [batch_129_03_values])
  exact h
theorem leaf_6462_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6462.profileLo box_6462.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6462_ok
theorem branch_box_6462_nonnegative : ∀ j, 0 ≤ branch_box_6462.lower j ∧ 0 ≤ branch_box_6462.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6462, Box.profileLo, Box.profileHi, box_6462]
theorem leaf_6462_BranchSafe : CertificateConsequences.BranchSafe branch_box_6462 := by
  left; refine ⟨branch_box_6462_nonnegative, ?_⟩
  intro z hz; exact leaf_6462_sound hz

theorem leaf_6473_ok : checkAt 527 1000 box_6473 cert_6473 = true := by
  have h := List.all_eq_true.mp batch_129_04_ok accepted_6473 (by simp [batch_129_04_values])
  exact h
theorem leaf_6473_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6473.profileLo box_6473.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6473_ok
theorem branch_box_6473_nonnegative : ∀ j, 0 ≤ branch_box_6473.lower j ∧ 0 ≤ branch_box_6473.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6473, Box.profileLo, Box.profileHi, box_6473]
theorem leaf_6473_BranchSafe : CertificateConsequences.BranchSafe branch_box_6473 := by
  left; refine ⟨branch_box_6473_nonnegative, ?_⟩
  intro z hz; exact leaf_6473_sound hz

theorem leaf_6474_ok : checkAt 527 1000 box_6474 cert_6474 = true := by
  have h := List.all_eq_true.mp batch_129_05_ok accepted_6474 (by simp [batch_129_05_values])
  exact h
theorem leaf_6474_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6474.profileLo box_6474.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6474_ok
theorem branch_box_6474_nonnegative : ∀ j, 0 ≤ branch_box_6474.lower j ∧ 0 ≤ branch_box_6474.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6474, Box.profileLo, Box.profileHi, box_6474]
theorem leaf_6474_BranchSafe : CertificateConsequences.BranchSafe branch_box_6474 := by
  left; refine ⟨branch_box_6474_nonnegative, ?_⟩
  intro z hz; exact leaf_6474_sound hz

theorem leaf_6475_ok : checkAt 527 1000 box_6475 cert_6475 = true := by
  have h := List.all_eq_true.mp batch_129_06_ok accepted_6475 (by simp [batch_129_06_values])
  exact h
theorem leaf_6475_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6475.profileLo box_6475.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6475_ok
theorem branch_box_6475_nonnegative : ∀ j, 0 ≤ branch_box_6475.lower j ∧ 0 ≤ branch_box_6475.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6475, Box.profileLo, Box.profileHi, box_6475]
theorem leaf_6475_BranchSafe : CertificateConsequences.BranchSafe branch_box_6475 := by
  left; refine ⟨branch_box_6475_nonnegative, ?_⟩
  intro z hz; exact leaf_6475_sound hz

theorem leaf_6477_ok : checkAt 527 1000 box_6477 cert_6477 = true := by
  have h := List.all_eq_true.mp batch_129_07_ok accepted_6477 (by simp [batch_129_07_values])
  exact h
theorem leaf_6477_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6477.profileLo box_6477.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6477_ok
theorem branch_box_6477_nonnegative : ∀ j, 0 ≤ branch_box_6477.lower j ∧ 0 ≤ branch_box_6477.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6477, Box.profileLo, Box.profileHi, box_6477]
theorem leaf_6477_BranchSafe : CertificateConsequences.BranchSafe branch_box_6477 := by
  left; refine ⟨branch_box_6477_nonnegative, ?_⟩
  intro z hz; exact leaf_6477_sound hz

theorem leaf_6478_ok : checkAt 527 1000 box_6478 cert_6478 = true := by
  have h := List.all_eq_true.mp batch_129_08_ok accepted_6478 (by simp [batch_129_08_values])
  exact h
theorem leaf_6478_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6478.profileLo box_6478.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6478_ok
theorem branch_box_6478_nonnegative : ∀ j, 0 ≤ branch_box_6478.lower j ∧ 0 ≤ branch_box_6478.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6478, Box.profileLo, Box.profileHi, box_6478]
theorem leaf_6478_BranchSafe : CertificateConsequences.BranchSafe branch_box_6478 := by
  left; refine ⟨branch_box_6478_nonnegative, ?_⟩
  intro z hz; exact leaf_6478_sound hz

theorem leaf_6479_ok : checkAt 527 1000 box_6479 cert_6479 = true := by
  have h := List.all_eq_true.mp batch_129_09_ok accepted_6479 (by simp [batch_129_09_values])
  exact h
theorem leaf_6479_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6479.profileLo box_6479.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6479_ok
theorem branch_box_6479_nonnegative : ∀ j, 0 ≤ branch_box_6479.lower j ∧ 0 ≤ branch_box_6479.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6479, Box.profileLo, Box.profileHi, box_6479]
theorem leaf_6479_BranchSafe : CertificateConsequences.BranchSafe branch_box_6479 := by
  left; refine ⟨branch_box_6479_nonnegative, ?_⟩
  intro z hz; exact leaf_6479_sound hz

theorem leaf_6481_ok : checkAt 527 1000 box_6481 cert_6481 = true := by
  have h := List.all_eq_true.mp batch_129_10_ok accepted_6481 (by simp [batch_129_10_values])
  exact h
theorem leaf_6481_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6481.profileLo box_6481.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6481_ok
theorem branch_box_6481_nonnegative : ∀ j, 0 ≤ branch_box_6481.lower j ∧ 0 ≤ branch_box_6481.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6481, Box.profileLo, Box.profileHi, box_6481]
theorem leaf_6481_BranchSafe : CertificateConsequences.BranchSafe branch_box_6481 := by
  left; refine ⟨branch_box_6481_nonnegative, ?_⟩
  intro z hz; exact leaf_6481_sound hz

theorem leaf_6482_ok : checkAt 527 1000 box_6482 cert_6482 = true := by
  have h := List.all_eq_true.mp batch_129_11_ok accepted_6482 (by simp [batch_129_11_values])
  exact h
theorem leaf_6482_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6482.profileLo box_6482.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6482_ok
theorem branch_box_6482_nonnegative : ∀ j, 0 ≤ branch_box_6482.lower j ∧ 0 ≤ branch_box_6482.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6482, Box.profileLo, Box.profileHi, box_6482]
theorem leaf_6482_BranchSafe : CertificateConsequences.BranchSafe branch_box_6482 := by
  left; refine ⟨branch_box_6482_nonnegative, ?_⟩
  intro z hz; exact leaf_6482_sound hz

theorem leaf_6483_ok : checkAt 527 1000 box_6483 cert_6483 = true := by
  have h := List.all_eq_true.mp batch_129_12_ok accepted_6483 (by simp [batch_129_12_values])
  exact h
theorem leaf_6483_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6483.profileLo box_6483.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6483_ok
theorem branch_box_6483_nonnegative : ∀ j, 0 ≤ branch_box_6483.lower j ∧ 0 ≤ branch_box_6483.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6483, Box.profileLo, Box.profileHi, box_6483]
theorem leaf_6483_BranchSafe : CertificateConsequences.BranchSafe branch_box_6483 := by
  left; refine ⟨branch_box_6483_nonnegative, ?_⟩
  intro z hz; exact leaf_6483_sound hz

theorem leaf_6489_ok : checkAt 527 1000 box_6489 cert_6489 = true := by
  have h := List.all_eq_true.mp batch_129_13_ok accepted_6489 (by simp [batch_129_13_values])
  exact h
theorem leaf_6489_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6489.profileLo box_6489.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6489_ok
theorem branch_box_6489_nonnegative : ∀ j, 0 ≤ branch_box_6489.lower j ∧ 0 ≤ branch_box_6489.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6489, Box.profileLo, Box.profileHi, box_6489]
theorem leaf_6489_BranchSafe : CertificateConsequences.BranchSafe branch_box_6489 := by
  left; refine ⟨branch_box_6489_nonnegative, ?_⟩
  intro z hz; exact leaf_6489_sound hz

theorem leaf_6490_ok : checkAt 527 1000 box_6490 cert_6490 = true := by
  have h := List.all_eq_true.mp batch_129_14_ok accepted_6490 (by simp [batch_129_14_values])
  exact h
theorem leaf_6490_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6490.profileLo box_6490.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6490_ok
theorem branch_box_6490_nonnegative : ∀ j, 0 ≤ branch_box_6490.lower j ∧ 0 ≤ branch_box_6490.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6490, Box.profileLo, Box.profileHi, box_6490]
theorem leaf_6490_BranchSafe : CertificateConsequences.BranchSafe branch_box_6490 := by
  left; refine ⟨branch_box_6490_nonnegative, ?_⟩
  intro z hz; exact leaf_6490_sound hz

theorem leaf_6491_ok : checkAt 527 1000 box_6491 cert_6491 = true := by
  have h := List.all_eq_true.mp batch_129_15_ok accepted_6491 (by simp [batch_129_15_values])
  exact h
theorem leaf_6491_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6491.profileLo box_6491.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6491_ok
theorem branch_box_6491_nonnegative : ∀ j, 0 ≤ branch_box_6491.lower j ∧ 0 ≤ branch_box_6491.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6491, Box.profileLo, Box.profileHi, box_6491]
theorem leaf_6491_BranchSafe : CertificateConsequences.BranchSafe branch_box_6491 := by
  left; refine ⟨branch_box_6491_nonnegative, ?_⟩
  intro z hz; exact leaf_6491_sound hz

theorem leaf_6492_ok : checkAt 527 1000 box_6492 cert_6492 = true := by
  have h := List.all_eq_true.mp batch_129_16_ok accepted_6492 (by simp [batch_129_16_values])
  exact h
theorem leaf_6492_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6492.profileLo box_6492.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6492_ok
theorem branch_box_6492_nonnegative : ∀ j, 0 ≤ branch_box_6492.lower j ∧ 0 ≤ branch_box_6492.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6492, Box.profileLo, Box.profileHi, box_6492]
theorem leaf_6492_BranchSafe : CertificateConsequences.BranchSafe branch_box_6492 := by
  left; refine ⟨branch_box_6492_nonnegative, ?_⟩
  intro z hz; exact leaf_6492_sound hz

theorem leaf_6495_ok : checkAt 527 1000 box_6495 cert_6495 = true := by
  have h := List.all_eq_true.mp batch_129_17_ok accepted_6495 (by simp [batch_129_17_values])
  exact h
theorem leaf_6495_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6495.profileLo box_6495.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6495_ok
theorem branch_box_6495_nonnegative : ∀ j, 0 ≤ branch_box_6495.lower j ∧ 0 ≤ branch_box_6495.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6495, Box.profileLo, Box.profileHi, box_6495]
theorem leaf_6495_BranchSafe : CertificateConsequences.BranchSafe branch_box_6495 := by
  left; refine ⟨branch_box_6495_nonnegative, ?_⟩
  intro z hz; exact leaf_6495_sound hz

theorem leaf_6496_ok : checkAt 527 1000 box_6496 cert_6496 = true := by
  have h := List.all_eq_true.mp batch_129_18_ok accepted_6496 (by simp [batch_129_18_values])
  exact h
theorem leaf_6496_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6496.profileLo box_6496.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6496_ok
theorem branch_box_6496_nonnegative : ∀ j, 0 ≤ branch_box_6496.lower j ∧ 0 ≤ branch_box_6496.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6496, Box.profileLo, Box.profileHi, box_6496]
theorem leaf_6496_BranchSafe : CertificateConsequences.BranchSafe branch_box_6496 := by
  left; refine ⟨branch_box_6496_nonnegative, ?_⟩
  intro z hz; exact leaf_6496_sound hz

theorem leaf_6499_ok : checkAt 527 1000 box_6499 cert_6499 = true := by
  have h := List.all_eq_true.mp batch_129_19_ok accepted_6499 (by simp [batch_129_19_values])
  exact h
theorem leaf_6499_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6499.profileLo box_6499.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6499_ok
theorem branch_box_6499_nonnegative : ∀ j, 0 ≤ branch_box_6499.lower j ∧ 0 ≤ branch_box_6499.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6499, Box.profileLo, Box.profileHi, box_6499]
theorem leaf_6499_BranchSafe : CertificateConsequences.BranchSafe branch_box_6499 := by
  left; refine ⟨branch_box_6499_nonnegative, ?_⟩
  intro z hz; exact leaf_6499_sound hz

#print axioms batch_129_00_ok
#print axioms leaf_6453_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
