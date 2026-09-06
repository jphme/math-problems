import PeaceableQueens.UpperBound.Generated.Even.CoreScaled13Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_13_00_values : List Bool := [accepted_650]
theorem batch_13_00_ok : batch_13_00_values.all id = true := by decide

def batch_13_01_values : List Bool := [accepted_652]
theorem batch_13_01_ok : batch_13_01_values.all id = true := by decide

def batch_13_02_values : List Bool := [accepted_653]
theorem batch_13_02_ok : batch_13_02_values.all id = true := by decide

def batch_13_03_values : List Bool := [accepted_655]
theorem batch_13_03_ok : batch_13_03_values.all id = true := by decide

def batch_13_04_values : List Bool := [accepted_657]
theorem batch_13_04_ok : batch_13_04_values.all id = true := by decide

def batch_13_05_values : List Bool := [accepted_662]
theorem batch_13_05_ok : batch_13_05_values.all id = true := by decide

def batch_13_06_values : List Bool := [accepted_664]
theorem batch_13_06_ok : batch_13_06_values.all id = true := by decide

def batch_13_07_values : List Bool := [accepted_666]
theorem batch_13_07_ok : batch_13_07_values.all id = true := by decide

def batch_13_08_values : List Bool := [accepted_668]
theorem batch_13_08_ok : batch_13_08_values.all id = true := by decide

def batch_13_09_values : List Bool := [accepted_670]
theorem batch_13_09_ok : batch_13_09_values.all id = true := by decide

def batch_13_10_values : List Bool := [accepted_672]
theorem batch_13_10_ok : batch_13_10_values.all id = true := by decide

def batch_13_11_values : List Bool := [accepted_674]
theorem batch_13_11_ok : batch_13_11_values.all id = true := by decide

def batch_13_12_values : List Bool := [accepted_675]
theorem batch_13_12_ok : batch_13_12_values.all id = true := by decide

def batch_13_13_values : List Bool := [accepted_678]
theorem batch_13_13_ok : batch_13_13_values.all id = true := by decide

def batch_13_14_values : List Bool := [accepted_680]
theorem batch_13_14_ok : batch_13_14_values.all id = true := by decide

def batch_13_15_values : List Bool := [accepted_682]
theorem batch_13_15_ok : batch_13_15_values.all id = true := by decide

def batch_13_16_values : List Bool := [accepted_684]
theorem batch_13_16_ok : batch_13_16_values.all id = true := by decide

def batch_13_17_values : List Bool := [accepted_686]
theorem batch_13_17_ok : batch_13_17_values.all id = true := by decide

def batch_13_18_values : List Bool := [accepted_687]
theorem batch_13_18_ok : batch_13_18_values.all id = true := by decide

def batch_13_19_values : List Bool := [accepted_689]
theorem batch_13_19_ok : batch_13_19_values.all id = true := by decide

def batch_13_20_values : List Bool := [accepted_693]
theorem batch_13_20_ok : batch_13_20_values.all id = true := by decide

def batch_13_21_values : List Bool := [accepted_696]
theorem batch_13_21_ok : batch_13_21_values.all id = true := by decide

def batch_13_22_values : List Bool := [accepted_698]
theorem batch_13_22_ok : batch_13_22_values.all id = true := by decide

theorem leaf_650_ok : checkAt 527 1000 box_650 cert_650 = true := by
  have h := List.all_eq_true.mp batch_13_00_ok accepted_650 (by simp [batch_13_00_values])
  exact h
theorem leaf_650_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_650.profileLo box_650.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_650_ok
theorem branch_box_650_nonnegative : ∀ j, 0 ≤ branch_box_650.lower j ∧ 0 ≤ branch_box_650.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_650, Box.profileLo, Box.profileHi, box_650]
theorem leaf_650_BranchSafe : CertificateConsequences.BranchSafe branch_box_650 := by
  left; refine ⟨branch_box_650_nonnegative, ?_⟩
  intro z hz; exact leaf_650_sound hz

theorem leaf_652_ok : checkAt 527 1000 box_652 cert_652 = true := by
  have h := List.all_eq_true.mp batch_13_01_ok accepted_652 (by simp [batch_13_01_values])
  exact h
theorem leaf_652_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_652.profileLo box_652.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_652_ok
theorem branch_box_652_nonnegative : ∀ j, 0 ≤ branch_box_652.lower j ∧ 0 ≤ branch_box_652.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_652, Box.profileLo, Box.profileHi, box_652]
theorem leaf_652_BranchSafe : CertificateConsequences.BranchSafe branch_box_652 := by
  left; refine ⟨branch_box_652_nonnegative, ?_⟩
  intro z hz; exact leaf_652_sound hz

theorem leaf_653_ok : checkAt 527 1000 box_653 cert_653 = true := by
  have h := List.all_eq_true.mp batch_13_02_ok accepted_653 (by simp [batch_13_02_values])
  exact h
theorem leaf_653_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_653.profileLo box_653.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_653_ok
theorem branch_box_653_nonnegative : ∀ j, 0 ≤ branch_box_653.lower j ∧ 0 ≤ branch_box_653.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_653, Box.profileLo, Box.profileHi, box_653]
theorem leaf_653_BranchSafe : CertificateConsequences.BranchSafe branch_box_653 := by
  left; refine ⟨branch_box_653_nonnegative, ?_⟩
  intro z hz; exact leaf_653_sound hz

theorem leaf_655_ok : checkAt 527 1000 box_655 cert_655 = true := by
  have h := List.all_eq_true.mp batch_13_03_ok accepted_655 (by simp [batch_13_03_values])
  exact h
theorem leaf_655_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_655.profileLo box_655.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_655_ok
theorem branch_box_655_nonnegative : ∀ j, 0 ≤ branch_box_655.lower j ∧ 0 ≤ branch_box_655.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_655, Box.profileLo, Box.profileHi, box_655]
theorem leaf_655_BranchSafe : CertificateConsequences.BranchSafe branch_box_655 := by
  left; refine ⟨branch_box_655_nonnegative, ?_⟩
  intro z hz; exact leaf_655_sound hz

theorem leaf_657_ok : checkAt 527 1000 box_657 cert_657 = true := by
  have h := List.all_eq_true.mp batch_13_04_ok accepted_657 (by simp [batch_13_04_values])
  exact h
theorem leaf_657_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_657.profileLo box_657.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_657_ok
theorem branch_box_657_nonnegative : ∀ j, 0 ≤ branch_box_657.lower j ∧ 0 ≤ branch_box_657.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_657, Box.profileLo, Box.profileHi, box_657]
theorem leaf_657_BranchSafe : CertificateConsequences.BranchSafe branch_box_657 := by
  left; refine ⟨branch_box_657_nonnegative, ?_⟩
  intro z hz; exact leaf_657_sound hz

theorem leaf_662_ok : checkAt 527 1000 box_662 cert_662 = true := by
  have h := List.all_eq_true.mp batch_13_05_ok accepted_662 (by simp [batch_13_05_values])
  exact h
theorem leaf_662_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_662.profileLo box_662.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_662_ok
theorem branch_box_662_nonnegative : ∀ j, 0 ≤ branch_box_662.lower j ∧ 0 ≤ branch_box_662.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_662, Box.profileLo, Box.profileHi, box_662]
theorem leaf_662_BranchSafe : CertificateConsequences.BranchSafe branch_box_662 := by
  left; refine ⟨branch_box_662_nonnegative, ?_⟩
  intro z hz; exact leaf_662_sound hz

theorem leaf_664_ok : checkAt 527 1000 box_664 cert_664 = true := by
  have h := List.all_eq_true.mp batch_13_06_ok accepted_664 (by simp [batch_13_06_values])
  exact h
theorem leaf_664_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_664.profileLo box_664.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_664_ok
theorem branch_box_664_nonnegative : ∀ j, 0 ≤ branch_box_664.lower j ∧ 0 ≤ branch_box_664.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_664, Box.profileLo, Box.profileHi, box_664]
theorem leaf_664_BranchSafe : CertificateConsequences.BranchSafe branch_box_664 := by
  left; refine ⟨branch_box_664_nonnegative, ?_⟩
  intro z hz; exact leaf_664_sound hz

theorem leaf_666_ok : checkAt 527 1000 box_666 cert_666 = true := by
  have h := List.all_eq_true.mp batch_13_07_ok accepted_666 (by simp [batch_13_07_values])
  exact h
theorem leaf_666_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_666.profileLo box_666.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_666_ok
theorem branch_box_666_nonnegative : ∀ j, 0 ≤ branch_box_666.lower j ∧ 0 ≤ branch_box_666.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_666, Box.profileLo, Box.profileHi, box_666]
theorem leaf_666_BranchSafe : CertificateConsequences.BranchSafe branch_box_666 := by
  left; refine ⟨branch_box_666_nonnegative, ?_⟩
  intro z hz; exact leaf_666_sound hz

theorem leaf_668_ok : checkAt 527 1000 box_668 cert_668 = true := by
  have h := List.all_eq_true.mp batch_13_08_ok accepted_668 (by simp [batch_13_08_values])
  exact h
theorem leaf_668_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_668.profileLo box_668.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_668_ok
theorem branch_box_668_nonnegative : ∀ j, 0 ≤ branch_box_668.lower j ∧ 0 ≤ branch_box_668.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_668, Box.profileLo, Box.profileHi, box_668]
theorem leaf_668_BranchSafe : CertificateConsequences.BranchSafe branch_box_668 := by
  left; refine ⟨branch_box_668_nonnegative, ?_⟩
  intro z hz; exact leaf_668_sound hz

theorem leaf_670_ok : checkAt 527 1000 box_670 cert_670 = true := by
  have h := List.all_eq_true.mp batch_13_09_ok accepted_670 (by simp [batch_13_09_values])
  exact h
theorem leaf_670_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_670.profileLo box_670.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_670_ok
theorem branch_box_670_nonnegative : ∀ j, 0 ≤ branch_box_670.lower j ∧ 0 ≤ branch_box_670.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_670, Box.profileLo, Box.profileHi, box_670]
theorem leaf_670_BranchSafe : CertificateConsequences.BranchSafe branch_box_670 := by
  left; refine ⟨branch_box_670_nonnegative, ?_⟩
  intro z hz; exact leaf_670_sound hz

theorem leaf_672_ok : checkAt 527 1000 box_672 cert_672 = true := by
  have h := List.all_eq_true.mp batch_13_10_ok accepted_672 (by simp [batch_13_10_values])
  exact h
theorem leaf_672_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_672.profileLo box_672.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_672_ok
theorem branch_box_672_nonnegative : ∀ j, 0 ≤ branch_box_672.lower j ∧ 0 ≤ branch_box_672.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_672, Box.profileLo, Box.profileHi, box_672]
theorem leaf_672_BranchSafe : CertificateConsequences.BranchSafe branch_box_672 := by
  left; refine ⟨branch_box_672_nonnegative, ?_⟩
  intro z hz; exact leaf_672_sound hz

theorem leaf_674_ok : checkAt 527 1000 box_674 cert_674 = true := by
  have h := List.all_eq_true.mp batch_13_11_ok accepted_674 (by simp [batch_13_11_values])
  exact h
theorem leaf_674_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_674.profileLo box_674.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_674_ok
theorem branch_box_674_nonnegative : ∀ j, 0 ≤ branch_box_674.lower j ∧ 0 ≤ branch_box_674.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_674, Box.profileLo, Box.profileHi, box_674]
theorem leaf_674_BranchSafe : CertificateConsequences.BranchSafe branch_box_674 := by
  left; refine ⟨branch_box_674_nonnegative, ?_⟩
  intro z hz; exact leaf_674_sound hz

theorem leaf_675_ok : checkAt 527 1000 box_675 cert_675 = true := by
  have h := List.all_eq_true.mp batch_13_12_ok accepted_675 (by simp [batch_13_12_values])
  exact h
theorem leaf_675_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_675.profileLo box_675.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_675_ok
theorem branch_box_675_nonnegative : ∀ j, 0 ≤ branch_box_675.lower j ∧ 0 ≤ branch_box_675.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_675, Box.profileLo, Box.profileHi, box_675]
theorem leaf_675_BranchSafe : CertificateConsequences.BranchSafe branch_box_675 := by
  left; refine ⟨branch_box_675_nonnegative, ?_⟩
  intro z hz; exact leaf_675_sound hz

theorem leaf_678_ok : checkAt 527 1000 box_678 cert_678 = true := by
  have h := List.all_eq_true.mp batch_13_13_ok accepted_678 (by simp [batch_13_13_values])
  exact h
theorem leaf_678_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_678.profileLo box_678.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_678_ok
theorem branch_box_678_nonnegative : ∀ j, 0 ≤ branch_box_678.lower j ∧ 0 ≤ branch_box_678.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_678, Box.profileLo, Box.profileHi, box_678]
theorem leaf_678_BranchSafe : CertificateConsequences.BranchSafe branch_box_678 := by
  left; refine ⟨branch_box_678_nonnegative, ?_⟩
  intro z hz; exact leaf_678_sound hz

theorem leaf_680_ok : checkAt 527 1000 box_680 cert_680 = true := by
  have h := List.all_eq_true.mp batch_13_14_ok accepted_680 (by simp [batch_13_14_values])
  exact h
theorem leaf_680_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_680.profileLo box_680.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_680_ok
theorem branch_box_680_nonnegative : ∀ j, 0 ≤ branch_box_680.lower j ∧ 0 ≤ branch_box_680.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_680, Box.profileLo, Box.profileHi, box_680]
theorem leaf_680_BranchSafe : CertificateConsequences.BranchSafe branch_box_680 := by
  left; refine ⟨branch_box_680_nonnegative, ?_⟩
  intro z hz; exact leaf_680_sound hz

theorem leaf_682_ok : checkAt 527 1000 box_682 cert_682 = true := by
  have h := List.all_eq_true.mp batch_13_15_ok accepted_682 (by simp [batch_13_15_values])
  exact h
theorem leaf_682_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_682.profileLo box_682.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_682_ok
theorem branch_box_682_nonnegative : ∀ j, 0 ≤ branch_box_682.lower j ∧ 0 ≤ branch_box_682.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_682, Box.profileLo, Box.profileHi, box_682]
theorem leaf_682_BranchSafe : CertificateConsequences.BranchSafe branch_box_682 := by
  left; refine ⟨branch_box_682_nonnegative, ?_⟩
  intro z hz; exact leaf_682_sound hz

theorem leaf_684_ok : checkAt 527 1000 box_684 cert_684 = true := by
  have h := List.all_eq_true.mp batch_13_16_ok accepted_684 (by simp [batch_13_16_values])
  exact h
theorem leaf_684_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_684.profileLo box_684.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_684_ok
theorem branch_box_684_nonnegative : ∀ j, 0 ≤ branch_box_684.lower j ∧ 0 ≤ branch_box_684.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_684, Box.profileLo, Box.profileHi, box_684]
theorem leaf_684_BranchSafe : CertificateConsequences.BranchSafe branch_box_684 := by
  left; refine ⟨branch_box_684_nonnegative, ?_⟩
  intro z hz; exact leaf_684_sound hz

theorem leaf_686_ok : checkAt 527 1000 box_686 cert_686 = true := by
  have h := List.all_eq_true.mp batch_13_17_ok accepted_686 (by simp [batch_13_17_values])
  exact h
theorem leaf_686_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_686.profileLo box_686.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_686_ok
theorem branch_box_686_nonnegative : ∀ j, 0 ≤ branch_box_686.lower j ∧ 0 ≤ branch_box_686.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_686, Box.profileLo, Box.profileHi, box_686]
theorem leaf_686_BranchSafe : CertificateConsequences.BranchSafe branch_box_686 := by
  left; refine ⟨branch_box_686_nonnegative, ?_⟩
  intro z hz; exact leaf_686_sound hz

theorem leaf_687_ok : checkAt 527 1000 box_687 cert_687 = true := by
  have h := List.all_eq_true.mp batch_13_18_ok accepted_687 (by simp [batch_13_18_values])
  exact h
theorem leaf_687_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_687.profileLo box_687.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_687_ok
theorem branch_box_687_nonnegative : ∀ j, 0 ≤ branch_box_687.lower j ∧ 0 ≤ branch_box_687.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_687, Box.profileLo, Box.profileHi, box_687]
theorem leaf_687_BranchSafe : CertificateConsequences.BranchSafe branch_box_687 := by
  left; refine ⟨branch_box_687_nonnegative, ?_⟩
  intro z hz; exact leaf_687_sound hz

theorem leaf_689_ok : checkAt 527 1000 box_689 cert_689 = true := by
  have h := List.all_eq_true.mp batch_13_19_ok accepted_689 (by simp [batch_13_19_values])
  exact h
theorem leaf_689_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_689.profileLo box_689.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_689_ok
theorem branch_box_689_nonnegative : ∀ j, 0 ≤ branch_box_689.lower j ∧ 0 ≤ branch_box_689.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_689, Box.profileLo, Box.profileHi, box_689]
theorem leaf_689_BranchSafe : CertificateConsequences.BranchSafe branch_box_689 := by
  left; refine ⟨branch_box_689_nonnegative, ?_⟩
  intro z hz; exact leaf_689_sound hz

theorem leaf_693_ok : checkAt 527 1000 box_693 cert_693 = true := by
  have h := List.all_eq_true.mp batch_13_20_ok accepted_693 (by simp [batch_13_20_values])
  exact h
theorem leaf_693_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_693.profileLo box_693.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_693_ok
theorem branch_box_693_nonnegative : ∀ j, 0 ≤ branch_box_693.lower j ∧ 0 ≤ branch_box_693.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_693, Box.profileLo, Box.profileHi, box_693]
theorem leaf_693_BranchSafe : CertificateConsequences.BranchSafe branch_box_693 := by
  left; refine ⟨branch_box_693_nonnegative, ?_⟩
  intro z hz; exact leaf_693_sound hz

theorem leaf_696_ok : checkAt 527 1000 box_696 cert_696 = true := by
  have h := List.all_eq_true.mp batch_13_21_ok accepted_696 (by simp [batch_13_21_values])
  exact h
theorem leaf_696_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_696.profileLo box_696.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_696_ok
theorem branch_box_696_nonnegative : ∀ j, 0 ≤ branch_box_696.lower j ∧ 0 ≤ branch_box_696.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_696, Box.profileLo, Box.profileHi, box_696]
theorem leaf_696_BranchSafe : CertificateConsequences.BranchSafe branch_box_696 := by
  left; refine ⟨branch_box_696_nonnegative, ?_⟩
  intro z hz; exact leaf_696_sound hz

theorem leaf_698_ok : checkAt 527 1000 box_698 cert_698 = true := by
  have h := List.all_eq_true.mp batch_13_22_ok accepted_698 (by simp [batch_13_22_values])
  exact h
theorem leaf_698_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_698.profileLo box_698.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_698_ok
theorem branch_box_698_nonnegative : ∀ j, 0 ≤ branch_box_698.lower j ∧ 0 ≤ branch_box_698.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_698, Box.profileLo, Box.profileHi, box_698]
theorem leaf_698_BranchSafe : CertificateConsequences.BranchSafe branch_box_698 := by
  left; refine ⟨branch_box_698_nonnegative, ?_⟩
  intro z hz; exact leaf_698_sound hz

#print axioms batch_13_00_ok
#print axioms leaf_650_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
