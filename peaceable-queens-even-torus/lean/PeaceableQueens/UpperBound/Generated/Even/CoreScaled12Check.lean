import PeaceableQueens.UpperBound.Generated.Even.CoreScaled12Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_12_00_values : List Bool := [accepted_600]
theorem batch_12_00_ok : batch_12_00_values.all id = true := by decide

def batch_12_01_values : List Bool := [accepted_601]
theorem batch_12_01_ok : batch_12_01_values.all id = true := by decide

def batch_12_02_values : List Bool := [accepted_608]
theorem batch_12_02_ok : batch_12_02_values.all id = true := by decide

def batch_12_03_values : List Bool := [accepted_610]
theorem batch_12_03_ok : batch_12_03_values.all id = true := by decide

def batch_12_04_values : List Bool := [accepted_612]
theorem batch_12_04_ok : batch_12_04_values.all id = true := by decide

def batch_12_05_values : List Bool := [accepted_614]
theorem batch_12_05_ok : batch_12_05_values.all id = true := by decide

def batch_12_06_values : List Bool := [accepted_616]
theorem batch_12_06_ok : batch_12_06_values.all id = true := by decide

def batch_12_07_values : List Bool := [accepted_618]
theorem batch_12_07_ok : batch_12_07_values.all id = true := by decide

def batch_12_08_values : List Bool := [accepted_620]
theorem batch_12_08_ok : batch_12_08_values.all id = true := by decide

def batch_12_09_values : List Bool := [accepted_621]
theorem batch_12_09_ok : batch_12_09_values.all id = true := by decide

def batch_12_10_values : List Bool := [accepted_623]
theorem batch_12_10_ok : batch_12_10_values.all id = true := by decide

def batch_12_11_values : List Bool := [accepted_627]
theorem batch_12_11_ok : batch_12_11_values.all id = true := by decide

def batch_12_12_values : List Bool := [accepted_630]
theorem batch_12_12_ok : batch_12_12_values.all id = true := by decide

def batch_12_13_values : List Bool := [accepted_632]
theorem batch_12_13_ok : batch_12_13_values.all id = true := by decide

def batch_12_14_values : List Bool := [accepted_634]
theorem batch_12_14_ok : batch_12_14_values.all id = true := by decide

def batch_12_15_values : List Bool := [accepted_635]
theorem batch_12_15_ok : batch_12_15_values.all id = true := by decide

def batch_12_16_values : List Bool := [accepted_637]
theorem batch_12_16_ok : batch_12_16_values.all id = true := by decide

def batch_12_17_values : List Bool := [accepted_639]
theorem batch_12_17_ok : batch_12_17_values.all id = true := by decide

def batch_12_18_values : List Bool := [accepted_642]
theorem batch_12_18_ok : batch_12_18_values.all id = true := by decide

def batch_12_19_values : List Bool := [accepted_644]
theorem batch_12_19_ok : batch_12_19_values.all id = true := by decide

def batch_12_20_values : List Bool := [accepted_648]
theorem batch_12_20_ok : batch_12_20_values.all id = true := by decide

theorem leaf_600_ok : checkAt 527 1000 box_600 cert_600 = true := by
  have h := List.all_eq_true.mp batch_12_00_ok accepted_600 (by simp [batch_12_00_values])
  exact h
theorem leaf_600_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_600.profileLo box_600.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_600_ok
theorem branch_box_600_nonnegative : ∀ j, 0 ≤ branch_box_600.lower j ∧ 0 ≤ branch_box_600.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_600, Box.profileLo, Box.profileHi, box_600]
theorem leaf_600_BranchSafe : CertificateConsequences.BranchSafe branch_box_600 := by
  left; refine ⟨branch_box_600_nonnegative, ?_⟩
  intro z hz; exact leaf_600_sound hz

theorem leaf_601_ok : checkAt 527 1000 box_601 cert_601 = true := by
  have h := List.all_eq_true.mp batch_12_01_ok accepted_601 (by simp [batch_12_01_values])
  exact h
theorem leaf_601_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_601.profileLo box_601.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_601_ok
theorem branch_box_601_nonnegative : ∀ j, 0 ≤ branch_box_601.lower j ∧ 0 ≤ branch_box_601.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_601, Box.profileLo, Box.profileHi, box_601]
theorem leaf_601_BranchSafe : CertificateConsequences.BranchSafe branch_box_601 := by
  left; refine ⟨branch_box_601_nonnegative, ?_⟩
  intro z hz; exact leaf_601_sound hz

theorem leaf_608_ok : checkAt 527 1000 box_608 cert_608 = true := by
  have h := List.all_eq_true.mp batch_12_02_ok accepted_608 (by simp [batch_12_02_values])
  exact h
theorem leaf_608_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_608.profileLo box_608.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_608_ok
theorem branch_box_608_nonnegative : ∀ j, 0 ≤ branch_box_608.lower j ∧ 0 ≤ branch_box_608.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_608, Box.profileLo, Box.profileHi, box_608]
theorem leaf_608_BranchSafe : CertificateConsequences.BranchSafe branch_box_608 := by
  left; refine ⟨branch_box_608_nonnegative, ?_⟩
  intro z hz; exact leaf_608_sound hz

theorem leaf_610_ok : checkAt 527 1000 box_610 cert_610 = true := by
  have h := List.all_eq_true.mp batch_12_03_ok accepted_610 (by simp [batch_12_03_values])
  exact h
theorem leaf_610_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_610.profileLo box_610.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_610_ok
theorem branch_box_610_nonnegative : ∀ j, 0 ≤ branch_box_610.lower j ∧ 0 ≤ branch_box_610.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_610, Box.profileLo, Box.profileHi, box_610]
theorem leaf_610_BranchSafe : CertificateConsequences.BranchSafe branch_box_610 := by
  left; refine ⟨branch_box_610_nonnegative, ?_⟩
  intro z hz; exact leaf_610_sound hz

theorem leaf_612_ok : checkAt 527 1000 box_612 cert_612 = true := by
  have h := List.all_eq_true.mp batch_12_04_ok accepted_612 (by simp [batch_12_04_values])
  exact h
theorem leaf_612_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_612.profileLo box_612.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_612_ok
theorem branch_box_612_nonnegative : ∀ j, 0 ≤ branch_box_612.lower j ∧ 0 ≤ branch_box_612.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_612, Box.profileLo, Box.profileHi, box_612]
theorem leaf_612_BranchSafe : CertificateConsequences.BranchSafe branch_box_612 := by
  left; refine ⟨branch_box_612_nonnegative, ?_⟩
  intro z hz; exact leaf_612_sound hz

theorem leaf_614_ok : checkAt 527 1000 box_614 cert_614 = true := by
  have h := List.all_eq_true.mp batch_12_05_ok accepted_614 (by simp [batch_12_05_values])
  exact h
theorem leaf_614_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_614.profileLo box_614.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_614_ok
theorem branch_box_614_nonnegative : ∀ j, 0 ≤ branch_box_614.lower j ∧ 0 ≤ branch_box_614.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_614, Box.profileLo, Box.profileHi, box_614]
theorem leaf_614_BranchSafe : CertificateConsequences.BranchSafe branch_box_614 := by
  left; refine ⟨branch_box_614_nonnegative, ?_⟩
  intro z hz; exact leaf_614_sound hz

theorem leaf_616_ok : checkAt 527 1000 box_616 cert_616 = true := by
  have h := List.all_eq_true.mp batch_12_06_ok accepted_616 (by simp [batch_12_06_values])
  exact h
theorem leaf_616_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_616.profileLo box_616.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_616_ok
theorem branch_box_616_nonnegative : ∀ j, 0 ≤ branch_box_616.lower j ∧ 0 ≤ branch_box_616.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_616, Box.profileLo, Box.profileHi, box_616]
theorem leaf_616_BranchSafe : CertificateConsequences.BranchSafe branch_box_616 := by
  left; refine ⟨branch_box_616_nonnegative, ?_⟩
  intro z hz; exact leaf_616_sound hz

theorem leaf_618_ok : checkAt 527 1000 box_618 cert_618 = true := by
  have h := List.all_eq_true.mp batch_12_07_ok accepted_618 (by simp [batch_12_07_values])
  exact h
theorem leaf_618_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_618.profileLo box_618.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_618_ok
theorem branch_box_618_nonnegative : ∀ j, 0 ≤ branch_box_618.lower j ∧ 0 ≤ branch_box_618.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_618, Box.profileLo, Box.profileHi, box_618]
theorem leaf_618_BranchSafe : CertificateConsequences.BranchSafe branch_box_618 := by
  left; refine ⟨branch_box_618_nonnegative, ?_⟩
  intro z hz; exact leaf_618_sound hz

theorem leaf_620_ok : checkAt 527 1000 box_620 cert_620 = true := by
  have h := List.all_eq_true.mp batch_12_08_ok accepted_620 (by simp [batch_12_08_values])
  exact h
theorem leaf_620_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_620.profileLo box_620.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_620_ok
theorem branch_box_620_nonnegative : ∀ j, 0 ≤ branch_box_620.lower j ∧ 0 ≤ branch_box_620.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_620, Box.profileLo, Box.profileHi, box_620]
theorem leaf_620_BranchSafe : CertificateConsequences.BranchSafe branch_box_620 := by
  left; refine ⟨branch_box_620_nonnegative, ?_⟩
  intro z hz; exact leaf_620_sound hz

theorem leaf_621_ok : checkAt 527 1000 box_621 cert_621 = true := by
  have h := List.all_eq_true.mp batch_12_09_ok accepted_621 (by simp [batch_12_09_values])
  exact h
theorem leaf_621_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_621.profileLo box_621.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_621_ok
theorem branch_box_621_nonnegative : ∀ j, 0 ≤ branch_box_621.lower j ∧ 0 ≤ branch_box_621.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_621, Box.profileLo, Box.profileHi, box_621]
theorem leaf_621_BranchSafe : CertificateConsequences.BranchSafe branch_box_621 := by
  left; refine ⟨branch_box_621_nonnegative, ?_⟩
  intro z hz; exact leaf_621_sound hz

theorem leaf_623_ok : checkAt 527 1000 box_623 cert_623 = true := by
  have h := List.all_eq_true.mp batch_12_10_ok accepted_623 (by simp [batch_12_10_values])
  exact h
theorem leaf_623_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_623.profileLo box_623.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_623_ok
theorem branch_box_623_nonnegative : ∀ j, 0 ≤ branch_box_623.lower j ∧ 0 ≤ branch_box_623.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_623, Box.profileLo, Box.profileHi, box_623]
theorem leaf_623_BranchSafe : CertificateConsequences.BranchSafe branch_box_623 := by
  left; refine ⟨branch_box_623_nonnegative, ?_⟩
  intro z hz; exact leaf_623_sound hz

theorem leaf_627_ok : checkAt 527 1000 box_627 cert_627 = true := by
  have h := List.all_eq_true.mp batch_12_11_ok accepted_627 (by simp [batch_12_11_values])
  exact h
theorem leaf_627_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_627.profileLo box_627.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_627_ok
theorem branch_box_627_nonnegative : ∀ j, 0 ≤ branch_box_627.lower j ∧ 0 ≤ branch_box_627.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_627, Box.profileLo, Box.profileHi, box_627]
theorem leaf_627_BranchSafe : CertificateConsequences.BranchSafe branch_box_627 := by
  left; refine ⟨branch_box_627_nonnegative, ?_⟩
  intro z hz; exact leaf_627_sound hz

theorem leaf_630_ok : checkAt 527 1000 box_630 cert_630 = true := by
  have h := List.all_eq_true.mp batch_12_12_ok accepted_630 (by simp [batch_12_12_values])
  exact h
theorem leaf_630_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_630.profileLo box_630.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_630_ok
theorem branch_box_630_nonnegative : ∀ j, 0 ≤ branch_box_630.lower j ∧ 0 ≤ branch_box_630.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_630, Box.profileLo, Box.profileHi, box_630]
theorem leaf_630_BranchSafe : CertificateConsequences.BranchSafe branch_box_630 := by
  left; refine ⟨branch_box_630_nonnegative, ?_⟩
  intro z hz; exact leaf_630_sound hz

theorem leaf_632_ok : checkAt 527 1000 box_632 cert_632 = true := by
  have h := List.all_eq_true.mp batch_12_13_ok accepted_632 (by simp [batch_12_13_values])
  exact h
theorem leaf_632_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_632.profileLo box_632.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_632_ok
theorem branch_box_632_nonnegative : ∀ j, 0 ≤ branch_box_632.lower j ∧ 0 ≤ branch_box_632.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_632, Box.profileLo, Box.profileHi, box_632]
theorem leaf_632_BranchSafe : CertificateConsequences.BranchSafe branch_box_632 := by
  left; refine ⟨branch_box_632_nonnegative, ?_⟩
  intro z hz; exact leaf_632_sound hz

theorem leaf_634_ok : checkAt 527 1000 box_634 cert_634 = true := by
  have h := List.all_eq_true.mp batch_12_14_ok accepted_634 (by simp [batch_12_14_values])
  exact h
theorem leaf_634_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_634.profileLo box_634.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_634_ok
theorem branch_box_634_nonnegative : ∀ j, 0 ≤ branch_box_634.lower j ∧ 0 ≤ branch_box_634.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_634, Box.profileLo, Box.profileHi, box_634]
theorem leaf_634_BranchSafe : CertificateConsequences.BranchSafe branch_box_634 := by
  left; refine ⟨branch_box_634_nonnegative, ?_⟩
  intro z hz; exact leaf_634_sound hz

theorem leaf_635_ok : checkAt 527 1000 box_635 cert_635 = true := by
  have h := List.all_eq_true.mp batch_12_15_ok accepted_635 (by simp [batch_12_15_values])
  exact h
theorem leaf_635_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_635.profileLo box_635.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_635_ok
theorem branch_box_635_nonnegative : ∀ j, 0 ≤ branch_box_635.lower j ∧ 0 ≤ branch_box_635.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_635, Box.profileLo, Box.profileHi, box_635]
theorem leaf_635_BranchSafe : CertificateConsequences.BranchSafe branch_box_635 := by
  left; refine ⟨branch_box_635_nonnegative, ?_⟩
  intro z hz; exact leaf_635_sound hz

theorem leaf_637_ok : checkAt 527 1000 box_637 cert_637 = true := by
  have h := List.all_eq_true.mp batch_12_16_ok accepted_637 (by simp [batch_12_16_values])
  exact h
theorem leaf_637_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_637.profileLo box_637.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_637_ok
theorem branch_box_637_nonnegative : ∀ j, 0 ≤ branch_box_637.lower j ∧ 0 ≤ branch_box_637.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_637, Box.profileLo, Box.profileHi, box_637]
theorem leaf_637_BranchSafe : CertificateConsequences.BranchSafe branch_box_637 := by
  left; refine ⟨branch_box_637_nonnegative, ?_⟩
  intro z hz; exact leaf_637_sound hz

theorem leaf_639_ok : checkAt 527 1000 box_639 cert_639 = true := by
  have h := List.all_eq_true.mp batch_12_17_ok accepted_639 (by simp [batch_12_17_values])
  exact h
theorem leaf_639_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_639.profileLo box_639.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_639_ok
theorem branch_box_639_nonnegative : ∀ j, 0 ≤ branch_box_639.lower j ∧ 0 ≤ branch_box_639.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_639, Box.profileLo, Box.profileHi, box_639]
theorem leaf_639_BranchSafe : CertificateConsequences.BranchSafe branch_box_639 := by
  left; refine ⟨branch_box_639_nonnegative, ?_⟩
  intro z hz; exact leaf_639_sound hz

theorem leaf_642_ok : checkAt 527 1000 box_642 cert_642 = true := by
  have h := List.all_eq_true.mp batch_12_18_ok accepted_642 (by simp [batch_12_18_values])
  exact h
theorem leaf_642_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_642.profileLo box_642.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_642_ok
theorem branch_box_642_nonnegative : ∀ j, 0 ≤ branch_box_642.lower j ∧ 0 ≤ branch_box_642.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_642, Box.profileLo, Box.profileHi, box_642]
theorem leaf_642_BranchSafe : CertificateConsequences.BranchSafe branch_box_642 := by
  left; refine ⟨branch_box_642_nonnegative, ?_⟩
  intro z hz; exact leaf_642_sound hz

theorem leaf_644_ok : checkAt 527 1000 box_644 cert_644 = true := by
  have h := List.all_eq_true.mp batch_12_19_ok accepted_644 (by simp [batch_12_19_values])
  exact h
theorem leaf_644_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_644.profileLo box_644.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_644_ok
theorem branch_box_644_nonnegative : ∀ j, 0 ≤ branch_box_644.lower j ∧ 0 ≤ branch_box_644.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_644, Box.profileLo, Box.profileHi, box_644]
theorem leaf_644_BranchSafe : CertificateConsequences.BranchSafe branch_box_644 := by
  left; refine ⟨branch_box_644_nonnegative, ?_⟩
  intro z hz; exact leaf_644_sound hz

theorem leaf_648_ok : checkAt 527 1000 box_648 cert_648 = true := by
  have h := List.all_eq_true.mp batch_12_20_ok accepted_648 (by simp [batch_12_20_values])
  exact h
theorem leaf_648_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_648.profileLo box_648.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_648_ok
theorem branch_box_648_nonnegative : ∀ j, 0 ≤ branch_box_648.lower j ∧ 0 ≤ branch_box_648.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_648, Box.profileLo, Box.profileHi, box_648]
theorem leaf_648_BranchSafe : CertificateConsequences.BranchSafe branch_box_648 := by
  left; refine ⟨branch_box_648_nonnegative, ?_⟩
  intro z hz; exact leaf_648_sound hz

#print axioms batch_12_00_ok
#print axioms leaf_600_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
