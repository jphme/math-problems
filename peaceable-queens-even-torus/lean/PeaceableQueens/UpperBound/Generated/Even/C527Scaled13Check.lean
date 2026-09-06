import PeaceableQueens.UpperBound.Generated.Even.C527Scaled13Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_13_00_values : List Bool := [accepted_652]
theorem batch_13_00_ok : batch_13_00_values.all id = true := by decide

def batch_13_01_values : List Bool := [accepted_653]
theorem batch_13_01_ok : batch_13_01_values.all id = true := by decide

def batch_13_02_values : List Bool := [accepted_654]
theorem batch_13_02_ok : batch_13_02_values.all id = true := by decide

def batch_13_03_values : List Bool := [accepted_655]
theorem batch_13_03_ok : batch_13_03_values.all id = true := by decide

def batch_13_04_values : List Bool := [accepted_656]
theorem batch_13_04_ok : batch_13_04_values.all id = true := by decide

def batch_13_05_values : List Bool := [accepted_659]
theorem batch_13_05_ok : batch_13_05_values.all id = true := by decide

def batch_13_06_values : List Bool := [accepted_666]
theorem batch_13_06_ok : batch_13_06_values.all id = true := by decide

def batch_13_07_values : List Bool := [accepted_670]
theorem batch_13_07_ok : batch_13_07_values.all id = true := by decide

def batch_13_08_values : List Bool := [accepted_672]
theorem batch_13_08_ok : batch_13_08_values.all id = true := by decide

def batch_13_09_values : List Bool := [accepted_673]
theorem batch_13_09_ok : batch_13_09_values.all id = true := by decide

def batch_13_10_values : List Bool := [accepted_674]
theorem batch_13_10_ok : batch_13_10_values.all id = true := by decide

def batch_13_11_values : List Bool := [accepted_675]
theorem batch_13_11_ok : batch_13_11_values.all id = true := by decide

def batch_13_12_values : List Bool := [accepted_676]
theorem batch_13_12_ok : batch_13_12_values.all id = true := by decide

def batch_13_13_values : List Bool := [accepted_677]
theorem batch_13_13_ok : batch_13_13_values.all id = true := by decide

def batch_13_14_values : List Bool := [accepted_678]
theorem batch_13_14_ok : batch_13_14_values.all id = true := by decide

def batch_13_15_values : List Bool := [accepted_681]
theorem batch_13_15_ok : batch_13_15_values.all id = true := by decide

def batch_13_16_values : List Bool := [accepted_683]
theorem batch_13_16_ok : batch_13_16_values.all id = true := by decide

def batch_13_17_values : List Bool := [accepted_684]
theorem batch_13_17_ok : batch_13_17_values.all id = true := by decide

def batch_13_18_values : List Bool := [accepted_685]
theorem batch_13_18_ok : batch_13_18_values.all id = true := by decide

def batch_13_19_values : List Bool := [accepted_690]
theorem batch_13_19_ok : batch_13_19_values.all id = true := by decide

def batch_13_20_values : List Bool := [accepted_691]
theorem batch_13_20_ok : batch_13_20_values.all id = true := by decide

def batch_13_21_values : List Bool := [accepted_692]
theorem batch_13_21_ok : batch_13_21_values.all id = true := by decide

def batch_13_22_values : List Bool := [accepted_694]
theorem batch_13_22_ok : batch_13_22_values.all id = true := by decide

def batch_13_23_values : List Bool := [accepted_695]
theorem batch_13_23_ok : batch_13_23_values.all id = true := by decide

def batch_13_24_values : List Bool := [accepted_696]
theorem batch_13_24_ok : batch_13_24_values.all id = true := by decide

def batch_13_25_values : List Bool := [accepted_699]
theorem batch_13_25_ok : batch_13_25_values.all id = true := by decide

theorem leaf_652_ok : checkAt 527 1000 box_652 cert_652 = true := by
  have h := List.all_eq_true.mp batch_13_00_ok accepted_652 (by simp [batch_13_00_values])
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
  have h := List.all_eq_true.mp batch_13_01_ok accepted_653 (by simp [batch_13_01_values])
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

theorem leaf_654_ok : checkAt 527 1000 box_654 cert_654 = true := by
  have h := List.all_eq_true.mp batch_13_02_ok accepted_654 (by simp [batch_13_02_values])
  exact h
theorem leaf_654_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_654.profileLo box_654.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_654_ok
theorem branch_box_654_nonnegative : ∀ j, 0 ≤ branch_box_654.lower j ∧ 0 ≤ branch_box_654.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_654, Box.profileLo, Box.profileHi, box_654]
theorem leaf_654_BranchSafe : CertificateConsequences.BranchSafe branch_box_654 := by
  left; refine ⟨branch_box_654_nonnegative, ?_⟩
  intro z hz; exact leaf_654_sound hz

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

theorem leaf_656_ok : checkAt 527 1000 box_656 cert_656 = true := by
  have h := List.all_eq_true.mp batch_13_04_ok accepted_656 (by simp [batch_13_04_values])
  exact h
theorem leaf_656_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_656.profileLo box_656.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_656_ok
theorem branch_box_656_nonnegative : ∀ j, 0 ≤ branch_box_656.lower j ∧ 0 ≤ branch_box_656.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_656, Box.profileLo, Box.profileHi, box_656]
theorem leaf_656_BranchSafe : CertificateConsequences.BranchSafe branch_box_656 := by
  left; refine ⟨branch_box_656_nonnegative, ?_⟩
  intro z hz; exact leaf_656_sound hz

theorem leaf_659_ok : checkAt 527 1000 box_659 cert_659 = true := by
  have h := List.all_eq_true.mp batch_13_05_ok accepted_659 (by simp [batch_13_05_values])
  exact h
theorem leaf_659_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_659.profileLo box_659.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_659_ok
theorem branch_box_659_nonnegative : ∀ j, 0 ≤ branch_box_659.lower j ∧ 0 ≤ branch_box_659.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_659, Box.profileLo, Box.profileHi, box_659]
theorem leaf_659_BranchSafe : CertificateConsequences.BranchSafe branch_box_659 := by
  left; refine ⟨branch_box_659_nonnegative, ?_⟩
  intro z hz; exact leaf_659_sound hz

theorem leaf_666_ok : checkAt 527 1000 box_666 cert_666 = true := by
  have h := List.all_eq_true.mp batch_13_06_ok accepted_666 (by simp [batch_13_06_values])
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

theorem leaf_670_ok : checkAt 527 1000 box_670 cert_670 = true := by
  have h := List.all_eq_true.mp batch_13_07_ok accepted_670 (by simp [batch_13_07_values])
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
  have h := List.all_eq_true.mp batch_13_08_ok accepted_672 (by simp [batch_13_08_values])
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

theorem leaf_673_ok : checkAt 527 1000 box_673 cert_673 = true := by
  have h := List.all_eq_true.mp batch_13_09_ok accepted_673 (by simp [batch_13_09_values])
  exact h
theorem leaf_673_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_673.profileLo box_673.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_673_ok
theorem branch_box_673_nonnegative : ∀ j, 0 ≤ branch_box_673.lower j ∧ 0 ≤ branch_box_673.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_673, Box.profileLo, Box.profileHi, box_673]
theorem leaf_673_BranchSafe : CertificateConsequences.BranchSafe branch_box_673 := by
  left; refine ⟨branch_box_673_nonnegative, ?_⟩
  intro z hz; exact leaf_673_sound hz

theorem leaf_674_ok : checkAt 527 1000 box_674 cert_674 = true := by
  have h := List.all_eq_true.mp batch_13_10_ok accepted_674 (by simp [batch_13_10_values])
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
  have h := List.all_eq_true.mp batch_13_11_ok accepted_675 (by simp [batch_13_11_values])
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

theorem leaf_676_ok : checkAt 527 1000 box_676 cert_676 = true := by
  have h := List.all_eq_true.mp batch_13_12_ok accepted_676 (by simp [batch_13_12_values])
  exact h
theorem leaf_676_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_676.profileLo box_676.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_676_ok
theorem branch_box_676_nonnegative : ∀ j, 0 ≤ branch_box_676.lower j ∧ 0 ≤ branch_box_676.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_676, Box.profileLo, Box.profileHi, box_676]
theorem leaf_676_BranchSafe : CertificateConsequences.BranchSafe branch_box_676 := by
  left; refine ⟨branch_box_676_nonnegative, ?_⟩
  intro z hz; exact leaf_676_sound hz

theorem leaf_677_ok : checkAt 527 1000 box_677 cert_677 = true := by
  have h := List.all_eq_true.mp batch_13_13_ok accepted_677 (by simp [batch_13_13_values])
  exact h
theorem leaf_677_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_677.profileLo box_677.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_677_ok
theorem branch_box_677_nonnegative : ∀ j, 0 ≤ branch_box_677.lower j ∧ 0 ≤ branch_box_677.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_677, Box.profileLo, Box.profileHi, box_677]
theorem leaf_677_BranchSafe : CertificateConsequences.BranchSafe branch_box_677 := by
  left; refine ⟨branch_box_677_nonnegative, ?_⟩
  intro z hz; exact leaf_677_sound hz

theorem leaf_678_ok : checkAt 527 1000 box_678 cert_678 = true := by
  have h := List.all_eq_true.mp batch_13_14_ok accepted_678 (by simp [batch_13_14_values])
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

theorem leaf_681_ok : checkAt 527 1000 box_681 cert_681 = true := by
  have h := List.all_eq_true.mp batch_13_15_ok accepted_681 (by simp [batch_13_15_values])
  exact h
theorem leaf_681_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_681.profileLo box_681.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_681_ok
theorem branch_box_681_nonnegative : ∀ j, 0 ≤ branch_box_681.lower j ∧ 0 ≤ branch_box_681.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_681, Box.profileLo, Box.profileHi, box_681]
theorem leaf_681_BranchSafe : CertificateConsequences.BranchSafe branch_box_681 := by
  left; refine ⟨branch_box_681_nonnegative, ?_⟩
  intro z hz; exact leaf_681_sound hz

theorem leaf_683_ok : checkAt 527 1000 box_683 cert_683 = true := by
  have h := List.all_eq_true.mp batch_13_16_ok accepted_683 (by simp [batch_13_16_values])
  exact h
theorem leaf_683_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_683.profileLo box_683.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_683_ok
theorem branch_box_683_nonnegative : ∀ j, 0 ≤ branch_box_683.lower j ∧ 0 ≤ branch_box_683.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_683, Box.profileLo, Box.profileHi, box_683]
theorem leaf_683_BranchSafe : CertificateConsequences.BranchSafe branch_box_683 := by
  left; refine ⟨branch_box_683_nonnegative, ?_⟩
  intro z hz; exact leaf_683_sound hz

theorem leaf_684_ok : checkAt 527 1000 box_684 cert_684 = true := by
  have h := List.all_eq_true.mp batch_13_17_ok accepted_684 (by simp [batch_13_17_values])
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

theorem leaf_685_ok : checkAt 527 1000 box_685 cert_685 = true := by
  have h := List.all_eq_true.mp batch_13_18_ok accepted_685 (by simp [batch_13_18_values])
  exact h
theorem leaf_685_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_685.profileLo box_685.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_685_ok
theorem branch_box_685_nonnegative : ∀ j, 0 ≤ branch_box_685.lower j ∧ 0 ≤ branch_box_685.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_685, Box.profileLo, Box.profileHi, box_685]
theorem leaf_685_BranchSafe : CertificateConsequences.BranchSafe branch_box_685 := by
  left; refine ⟨branch_box_685_nonnegative, ?_⟩
  intro z hz; exact leaf_685_sound hz

theorem leaf_690_ok : checkAt 527 1000 box_690 cert_690 = true := by
  have h := List.all_eq_true.mp batch_13_19_ok accepted_690 (by simp [batch_13_19_values])
  exact h
theorem leaf_690_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_690.profileLo box_690.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_690_ok
theorem branch_box_690_nonnegative : ∀ j, 0 ≤ branch_box_690.lower j ∧ 0 ≤ branch_box_690.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_690, Box.profileLo, Box.profileHi, box_690]
theorem leaf_690_BranchSafe : CertificateConsequences.BranchSafe branch_box_690 := by
  left; refine ⟨branch_box_690_nonnegative, ?_⟩
  intro z hz; exact leaf_690_sound hz

theorem leaf_691_ok : checkAt 527 1000 box_691 cert_691 = true := by
  have h := List.all_eq_true.mp batch_13_20_ok accepted_691 (by simp [batch_13_20_values])
  exact h
theorem leaf_691_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_691.profileLo box_691.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_691_ok
theorem branch_box_691_nonnegative : ∀ j, 0 ≤ branch_box_691.lower j ∧ 0 ≤ branch_box_691.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_691, Box.profileLo, Box.profileHi, box_691]
theorem leaf_691_BranchSafe : CertificateConsequences.BranchSafe branch_box_691 := by
  left; refine ⟨branch_box_691_nonnegative, ?_⟩
  intro z hz; exact leaf_691_sound hz

theorem leaf_692_ok : checkAt 527 1000 box_692 cert_692 = true := by
  have h := List.all_eq_true.mp batch_13_21_ok accepted_692 (by simp [batch_13_21_values])
  exact h
theorem leaf_692_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_692.profileLo box_692.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_692_ok
theorem branch_box_692_nonnegative : ∀ j, 0 ≤ branch_box_692.lower j ∧ 0 ≤ branch_box_692.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_692, Box.profileLo, Box.profileHi, box_692]
theorem leaf_692_BranchSafe : CertificateConsequences.BranchSafe branch_box_692 := by
  left; refine ⟨branch_box_692_nonnegative, ?_⟩
  intro z hz; exact leaf_692_sound hz

theorem leaf_694_ok : checkAt 527 1000 box_694 cert_694 = true := by
  have h := List.all_eq_true.mp batch_13_22_ok accepted_694 (by simp [batch_13_22_values])
  exact h
theorem leaf_694_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_694.profileLo box_694.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_694_ok
theorem branch_box_694_nonnegative : ∀ j, 0 ≤ branch_box_694.lower j ∧ 0 ≤ branch_box_694.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_694, Box.profileLo, Box.profileHi, box_694]
theorem leaf_694_BranchSafe : CertificateConsequences.BranchSafe branch_box_694 := by
  left; refine ⟨branch_box_694_nonnegative, ?_⟩
  intro z hz; exact leaf_694_sound hz

theorem leaf_695_ok : checkAt 527 1000 box_695 cert_695 = true := by
  have h := List.all_eq_true.mp batch_13_23_ok accepted_695 (by simp [batch_13_23_values])
  exact h
theorem leaf_695_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_695.profileLo box_695.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_695_ok
theorem branch_box_695_nonnegative : ∀ j, 0 ≤ branch_box_695.lower j ∧ 0 ≤ branch_box_695.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_695, Box.profileLo, Box.profileHi, box_695]
theorem leaf_695_BranchSafe : CertificateConsequences.BranchSafe branch_box_695 := by
  left; refine ⟨branch_box_695_nonnegative, ?_⟩
  intro z hz; exact leaf_695_sound hz

theorem leaf_696_ok : checkAt 527 1000 box_696 cert_696 = true := by
  have h := List.all_eq_true.mp batch_13_24_ok accepted_696 (by simp [batch_13_24_values])
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

theorem leaf_699_ok : checkAt 527 1000 box_699 cert_699 = true := by
  have h := List.all_eq_true.mp batch_13_25_ok accepted_699 (by simp [batch_13_25_values])
  exact h
theorem leaf_699_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_699.profileLo box_699.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_699_ok
theorem branch_box_699_nonnegative : ∀ j, 0 ≤ branch_box_699.lower j ∧ 0 ≤ branch_box_699.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_699, Box.profileLo, Box.profileHi, box_699]
theorem leaf_699_BranchSafe : CertificateConsequences.BranchSafe branch_box_699 := by
  left; refine ⟨branch_box_699_nonnegative, ?_⟩
  intro z hz; exact leaf_699_sound hz

#print axioms batch_13_00_ok
#print axioms leaf_652_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
