import PeaceableQueens.UpperBound.Generated.Even.C527Scaled73Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_73_00_values : List Bool := [accepted_3653]
theorem batch_73_00_ok : batch_73_00_values.all id = true := by decide

def batch_73_01_values : List Bool := [accepted_3654]
theorem batch_73_01_ok : batch_73_01_values.all id = true := by decide

def batch_73_02_values : List Bool := [accepted_3660]
theorem batch_73_02_ok : batch_73_02_values.all id = true := by decide

def batch_73_03_values : List Bool := [accepted_3662]
theorem batch_73_03_ok : batch_73_03_values.all id = true := by decide

def batch_73_04_values : List Bool := [accepted_3665]
theorem batch_73_04_ok : batch_73_04_values.all id = true := by decide

def batch_73_05_values : List Bool := [accepted_3666]
theorem batch_73_05_ok : batch_73_05_values.all id = true := by decide

def batch_73_06_values : List Bool := [accepted_3667]
theorem batch_73_06_ok : batch_73_06_values.all id = true := by decide

def batch_73_07_values : List Bool := [accepted_3668]
theorem batch_73_07_ok : batch_73_07_values.all id = true := by decide

def batch_73_08_values : List Bool := [accepted_3673]
theorem batch_73_08_ok : batch_73_08_values.all id = true := by decide

def batch_73_09_values : List Bool := [accepted_3675]
theorem batch_73_09_ok : batch_73_09_values.all id = true := by decide

def batch_73_10_values : List Bool := [accepted_3676]
theorem batch_73_10_ok : batch_73_10_values.all id = true := by decide

def batch_73_11_values : List Bool := [accepted_3677]
theorem batch_73_11_ok : batch_73_11_values.all id = true := by decide

def batch_73_12_values : List Bool := [accepted_3679]
theorem batch_73_12_ok : batch_73_12_values.all id = true := by decide

def batch_73_13_values : List Bool := [accepted_3681]
theorem batch_73_13_ok : batch_73_13_values.all id = true := by decide

def batch_73_14_values : List Bool := [accepted_3682]
theorem batch_73_14_ok : batch_73_14_values.all id = true := by decide

def batch_73_15_values : List Bool := [accepted_3683]
theorem batch_73_15_ok : batch_73_15_values.all id = true := by decide

def batch_73_16_values : List Bool := [accepted_3685]
theorem batch_73_16_ok : batch_73_16_values.all id = true := by decide

def batch_73_17_values : List Bool := [accepted_3686]
theorem batch_73_17_ok : batch_73_17_values.all id = true := by decide

def batch_73_18_values : List Bool := [accepted_3687]
theorem batch_73_18_ok : batch_73_18_values.all id = true := by decide

def batch_73_19_values : List Bool := [accepted_3689]
theorem batch_73_19_ok : batch_73_19_values.all id = true := by decide

def batch_73_20_values : List Bool := [accepted_3691]
theorem batch_73_20_ok : batch_73_20_values.all id = true := by decide

def batch_73_21_values : List Bool := [accepted_3692]
theorem batch_73_21_ok : batch_73_21_values.all id = true := by decide

def batch_73_22_values : List Bool := [accepted_3697]
theorem batch_73_22_ok : batch_73_22_values.all id = true := by decide

def batch_73_23_values : List Bool := [accepted_3698]
theorem batch_73_23_ok : batch_73_23_values.all id = true := by decide

theorem leaf_3653_ok : checkAt 527 1000 box_3653 cert_3653 = true := by
  have h := List.all_eq_true.mp batch_73_00_ok accepted_3653 (by simp [batch_73_00_values])
  exact h
theorem leaf_3653_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3653.profileLo box_3653.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3653_ok
theorem branch_box_3653_nonnegative : ∀ j, 0 ≤ branch_box_3653.lower j ∧ 0 ≤ branch_box_3653.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3653, Box.profileLo, Box.profileHi, box_3653]
theorem leaf_3653_BranchSafe : CertificateConsequences.BranchSafe branch_box_3653 := by
  left; refine ⟨branch_box_3653_nonnegative, ?_⟩
  intro z hz; exact leaf_3653_sound hz

theorem leaf_3654_ok : checkAt 527 1000 box_3654 cert_3654 = true := by
  have h := List.all_eq_true.mp batch_73_01_ok accepted_3654 (by simp [batch_73_01_values])
  exact h
theorem leaf_3654_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3654.profileLo box_3654.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3654_ok
theorem branch_box_3654_nonnegative : ∀ j, 0 ≤ branch_box_3654.lower j ∧ 0 ≤ branch_box_3654.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3654, Box.profileLo, Box.profileHi, box_3654]
theorem leaf_3654_BranchSafe : CertificateConsequences.BranchSafe branch_box_3654 := by
  left; refine ⟨branch_box_3654_nonnegative, ?_⟩
  intro z hz; exact leaf_3654_sound hz

theorem leaf_3660_ok : checkAt 527 1000 box_3660 cert_3660 = true := by
  have h := List.all_eq_true.mp batch_73_02_ok accepted_3660 (by simp [batch_73_02_values])
  exact h
theorem leaf_3660_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3660.profileLo box_3660.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3660_ok
theorem branch_box_3660_nonnegative : ∀ j, 0 ≤ branch_box_3660.lower j ∧ 0 ≤ branch_box_3660.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3660, Box.profileLo, Box.profileHi, box_3660]
theorem leaf_3660_BranchSafe : CertificateConsequences.BranchSafe branch_box_3660 := by
  left; refine ⟨branch_box_3660_nonnegative, ?_⟩
  intro z hz; exact leaf_3660_sound hz

theorem leaf_3662_ok : checkAt 527 1000 box_3662 cert_3662 = true := by
  have h := List.all_eq_true.mp batch_73_03_ok accepted_3662 (by simp [batch_73_03_values])
  exact h
theorem leaf_3662_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3662.profileLo box_3662.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3662_ok
theorem branch_box_3662_nonnegative : ∀ j, 0 ≤ branch_box_3662.lower j ∧ 0 ≤ branch_box_3662.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3662, Box.profileLo, Box.profileHi, box_3662]
theorem leaf_3662_BranchSafe : CertificateConsequences.BranchSafe branch_box_3662 := by
  left; refine ⟨branch_box_3662_nonnegative, ?_⟩
  intro z hz; exact leaf_3662_sound hz

theorem leaf_3665_ok : checkAt 527 1000 box_3665 cert_3665 = true := by
  have h := List.all_eq_true.mp batch_73_04_ok accepted_3665 (by simp [batch_73_04_values])
  exact h
theorem leaf_3665_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3665.profileLo box_3665.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3665_ok
theorem branch_box_3665_nonnegative : ∀ j, 0 ≤ branch_box_3665.lower j ∧ 0 ≤ branch_box_3665.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3665, Box.profileLo, Box.profileHi, box_3665]
theorem leaf_3665_BranchSafe : CertificateConsequences.BranchSafe branch_box_3665 := by
  left; refine ⟨branch_box_3665_nonnegative, ?_⟩
  intro z hz; exact leaf_3665_sound hz

theorem leaf_3666_ok : checkAt 527 1000 box_3666 cert_3666 = true := by
  have h := List.all_eq_true.mp batch_73_05_ok accepted_3666 (by simp [batch_73_05_values])
  exact h
theorem leaf_3666_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3666.profileLo box_3666.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3666_ok
theorem branch_box_3666_nonnegative : ∀ j, 0 ≤ branch_box_3666.lower j ∧ 0 ≤ branch_box_3666.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3666, Box.profileLo, Box.profileHi, box_3666]
theorem leaf_3666_BranchSafe : CertificateConsequences.BranchSafe branch_box_3666 := by
  left; refine ⟨branch_box_3666_nonnegative, ?_⟩
  intro z hz; exact leaf_3666_sound hz

theorem leaf_3667_ok : checkAt 527 1000 box_3667 cert_3667 = true := by
  have h := List.all_eq_true.mp batch_73_06_ok accepted_3667 (by simp [batch_73_06_values])
  exact h
theorem leaf_3667_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3667.profileLo box_3667.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3667_ok
theorem branch_box_3667_nonnegative : ∀ j, 0 ≤ branch_box_3667.lower j ∧ 0 ≤ branch_box_3667.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3667, Box.profileLo, Box.profileHi, box_3667]
theorem leaf_3667_BranchSafe : CertificateConsequences.BranchSafe branch_box_3667 := by
  left; refine ⟨branch_box_3667_nonnegative, ?_⟩
  intro z hz; exact leaf_3667_sound hz

theorem leaf_3668_ok : checkAt 527 1000 box_3668 cert_3668 = true := by
  have h := List.all_eq_true.mp batch_73_07_ok accepted_3668 (by simp [batch_73_07_values])
  exact h
theorem leaf_3668_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3668.profileLo box_3668.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3668_ok
theorem branch_box_3668_nonnegative : ∀ j, 0 ≤ branch_box_3668.lower j ∧ 0 ≤ branch_box_3668.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3668, Box.profileLo, Box.profileHi, box_3668]
theorem leaf_3668_BranchSafe : CertificateConsequences.BranchSafe branch_box_3668 := by
  left; refine ⟨branch_box_3668_nonnegative, ?_⟩
  intro z hz; exact leaf_3668_sound hz

theorem leaf_3673_ok : checkAt 527 1000 box_3673 cert_3673 = true := by
  have h := List.all_eq_true.mp batch_73_08_ok accepted_3673 (by simp [batch_73_08_values])
  exact h
theorem leaf_3673_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3673.profileLo box_3673.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3673_ok
theorem branch_box_3673_nonnegative : ∀ j, 0 ≤ branch_box_3673.lower j ∧ 0 ≤ branch_box_3673.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3673, Box.profileLo, Box.profileHi, box_3673]
theorem leaf_3673_BranchSafe : CertificateConsequences.BranchSafe branch_box_3673 := by
  left; refine ⟨branch_box_3673_nonnegative, ?_⟩
  intro z hz; exact leaf_3673_sound hz

theorem leaf_3675_ok : checkAt 527 1000 box_3675 cert_3675 = true := by
  have h := List.all_eq_true.mp batch_73_09_ok accepted_3675 (by simp [batch_73_09_values])
  exact h
theorem leaf_3675_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3675.profileLo box_3675.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3675_ok
theorem branch_box_3675_nonnegative : ∀ j, 0 ≤ branch_box_3675.lower j ∧ 0 ≤ branch_box_3675.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3675, Box.profileLo, Box.profileHi, box_3675]
theorem leaf_3675_BranchSafe : CertificateConsequences.BranchSafe branch_box_3675 := by
  left; refine ⟨branch_box_3675_nonnegative, ?_⟩
  intro z hz; exact leaf_3675_sound hz

theorem leaf_3676_ok : checkAt 527 1000 box_3676 cert_3676 = true := by
  have h := List.all_eq_true.mp batch_73_10_ok accepted_3676 (by simp [batch_73_10_values])
  exact h
theorem leaf_3676_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3676.profileLo box_3676.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3676_ok
theorem branch_box_3676_nonnegative : ∀ j, 0 ≤ branch_box_3676.lower j ∧ 0 ≤ branch_box_3676.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3676, Box.profileLo, Box.profileHi, box_3676]
theorem leaf_3676_BranchSafe : CertificateConsequences.BranchSafe branch_box_3676 := by
  left; refine ⟨branch_box_3676_nonnegative, ?_⟩
  intro z hz; exact leaf_3676_sound hz

theorem leaf_3677_ok : checkAt 527 1000 box_3677 cert_3677 = true := by
  have h := List.all_eq_true.mp batch_73_11_ok accepted_3677 (by simp [batch_73_11_values])
  exact h
theorem leaf_3677_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3677.profileLo box_3677.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3677_ok
theorem branch_box_3677_nonnegative : ∀ j, 0 ≤ branch_box_3677.lower j ∧ 0 ≤ branch_box_3677.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3677, Box.profileLo, Box.profileHi, box_3677]
theorem leaf_3677_BranchSafe : CertificateConsequences.BranchSafe branch_box_3677 := by
  left; refine ⟨branch_box_3677_nonnegative, ?_⟩
  intro z hz; exact leaf_3677_sound hz

theorem leaf_3679_ok : checkAt 527 1000 box_3679 cert_3679 = true := by
  have h := List.all_eq_true.mp batch_73_12_ok accepted_3679 (by simp [batch_73_12_values])
  exact h
theorem leaf_3679_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3679.profileLo box_3679.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3679_ok
theorem branch_box_3679_nonnegative : ∀ j, 0 ≤ branch_box_3679.lower j ∧ 0 ≤ branch_box_3679.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3679, Box.profileLo, Box.profileHi, box_3679]
theorem leaf_3679_BranchSafe : CertificateConsequences.BranchSafe branch_box_3679 := by
  left; refine ⟨branch_box_3679_nonnegative, ?_⟩
  intro z hz; exact leaf_3679_sound hz

theorem leaf_3681_ok : checkAt 527 1000 box_3681 cert_3681 = true := by
  have h := List.all_eq_true.mp batch_73_13_ok accepted_3681 (by simp [batch_73_13_values])
  exact h
theorem leaf_3681_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3681.profileLo box_3681.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3681_ok
theorem branch_box_3681_nonnegative : ∀ j, 0 ≤ branch_box_3681.lower j ∧ 0 ≤ branch_box_3681.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3681, Box.profileLo, Box.profileHi, box_3681]
theorem leaf_3681_BranchSafe : CertificateConsequences.BranchSafe branch_box_3681 := by
  left; refine ⟨branch_box_3681_nonnegative, ?_⟩
  intro z hz; exact leaf_3681_sound hz

theorem leaf_3682_ok : checkAt 527 1000 box_3682 cert_3682 = true := by
  have h := List.all_eq_true.mp batch_73_14_ok accepted_3682 (by simp [batch_73_14_values])
  exact h
theorem leaf_3682_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3682.profileLo box_3682.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3682_ok
theorem branch_box_3682_nonnegative : ∀ j, 0 ≤ branch_box_3682.lower j ∧ 0 ≤ branch_box_3682.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3682, Box.profileLo, Box.profileHi, box_3682]
theorem leaf_3682_BranchSafe : CertificateConsequences.BranchSafe branch_box_3682 := by
  left; refine ⟨branch_box_3682_nonnegative, ?_⟩
  intro z hz; exact leaf_3682_sound hz

theorem leaf_3683_ok : checkAt 527 1000 box_3683 cert_3683 = true := by
  have h := List.all_eq_true.mp batch_73_15_ok accepted_3683 (by simp [batch_73_15_values])
  exact h
theorem leaf_3683_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3683.profileLo box_3683.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3683_ok
theorem branch_box_3683_nonnegative : ∀ j, 0 ≤ branch_box_3683.lower j ∧ 0 ≤ branch_box_3683.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3683, Box.profileLo, Box.profileHi, box_3683]
theorem leaf_3683_BranchSafe : CertificateConsequences.BranchSafe branch_box_3683 := by
  left; refine ⟨branch_box_3683_nonnegative, ?_⟩
  intro z hz; exact leaf_3683_sound hz

theorem leaf_3685_ok : checkAt 527 1000 box_3685 cert_3685 = true := by
  have h := List.all_eq_true.mp batch_73_16_ok accepted_3685 (by simp [batch_73_16_values])
  exact h
theorem leaf_3685_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3685.profileLo box_3685.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3685_ok
theorem branch_box_3685_nonnegative : ∀ j, 0 ≤ branch_box_3685.lower j ∧ 0 ≤ branch_box_3685.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3685, Box.profileLo, Box.profileHi, box_3685]
theorem leaf_3685_BranchSafe : CertificateConsequences.BranchSafe branch_box_3685 := by
  left; refine ⟨branch_box_3685_nonnegative, ?_⟩
  intro z hz; exact leaf_3685_sound hz

theorem leaf_3686_ok : checkAt 527 1000 box_3686 cert_3686 = true := by
  have h := List.all_eq_true.mp batch_73_17_ok accepted_3686 (by simp [batch_73_17_values])
  exact h
theorem leaf_3686_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3686.profileLo box_3686.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3686_ok
theorem branch_box_3686_nonnegative : ∀ j, 0 ≤ branch_box_3686.lower j ∧ 0 ≤ branch_box_3686.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3686, Box.profileLo, Box.profileHi, box_3686]
theorem leaf_3686_BranchSafe : CertificateConsequences.BranchSafe branch_box_3686 := by
  left; refine ⟨branch_box_3686_nonnegative, ?_⟩
  intro z hz; exact leaf_3686_sound hz

theorem leaf_3687_ok : checkAt 527 1000 box_3687 cert_3687 = true := by
  have h := List.all_eq_true.mp batch_73_18_ok accepted_3687 (by simp [batch_73_18_values])
  exact h
theorem leaf_3687_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3687.profileLo box_3687.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3687_ok
theorem branch_box_3687_nonnegative : ∀ j, 0 ≤ branch_box_3687.lower j ∧ 0 ≤ branch_box_3687.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3687, Box.profileLo, Box.profileHi, box_3687]
theorem leaf_3687_BranchSafe : CertificateConsequences.BranchSafe branch_box_3687 := by
  left; refine ⟨branch_box_3687_nonnegative, ?_⟩
  intro z hz; exact leaf_3687_sound hz

theorem leaf_3689_ok : checkAt 527 1000 box_3689 cert_3689 = true := by
  have h := List.all_eq_true.mp batch_73_19_ok accepted_3689 (by simp [batch_73_19_values])
  exact h
theorem leaf_3689_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3689.profileLo box_3689.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3689_ok
theorem branch_box_3689_nonnegative : ∀ j, 0 ≤ branch_box_3689.lower j ∧ 0 ≤ branch_box_3689.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3689, Box.profileLo, Box.profileHi, box_3689]
theorem leaf_3689_BranchSafe : CertificateConsequences.BranchSafe branch_box_3689 := by
  left; refine ⟨branch_box_3689_nonnegative, ?_⟩
  intro z hz; exact leaf_3689_sound hz

theorem leaf_3691_ok : checkAt 527 1000 box_3691 cert_3691 = true := by
  have h := List.all_eq_true.mp batch_73_20_ok accepted_3691 (by simp [batch_73_20_values])
  exact h
theorem leaf_3691_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3691.profileLo box_3691.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3691_ok
theorem branch_box_3691_nonnegative : ∀ j, 0 ≤ branch_box_3691.lower j ∧ 0 ≤ branch_box_3691.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3691, Box.profileLo, Box.profileHi, box_3691]
theorem leaf_3691_BranchSafe : CertificateConsequences.BranchSafe branch_box_3691 := by
  left; refine ⟨branch_box_3691_nonnegative, ?_⟩
  intro z hz; exact leaf_3691_sound hz

theorem leaf_3692_ok : checkAt 527 1000 box_3692 cert_3692 = true := by
  have h := List.all_eq_true.mp batch_73_21_ok accepted_3692 (by simp [batch_73_21_values])
  exact h
theorem leaf_3692_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3692.profileLo box_3692.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3692_ok
theorem branch_box_3692_nonnegative : ∀ j, 0 ≤ branch_box_3692.lower j ∧ 0 ≤ branch_box_3692.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3692, Box.profileLo, Box.profileHi, box_3692]
theorem leaf_3692_BranchSafe : CertificateConsequences.BranchSafe branch_box_3692 := by
  left; refine ⟨branch_box_3692_nonnegative, ?_⟩
  intro z hz; exact leaf_3692_sound hz

theorem leaf_3697_ok : checkAt 527 1000 box_3697 cert_3697 = true := by
  have h := List.all_eq_true.mp batch_73_22_ok accepted_3697 (by simp [batch_73_22_values])
  exact h
theorem leaf_3697_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3697.profileLo box_3697.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3697_ok
theorem branch_box_3697_nonnegative : ∀ j, 0 ≤ branch_box_3697.lower j ∧ 0 ≤ branch_box_3697.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3697, Box.profileLo, Box.profileHi, box_3697]
theorem leaf_3697_BranchSafe : CertificateConsequences.BranchSafe branch_box_3697 := by
  left; refine ⟨branch_box_3697_nonnegative, ?_⟩
  intro z hz; exact leaf_3697_sound hz

theorem leaf_3698_ok : checkAt 527 1000 box_3698 cert_3698 = true := by
  have h := List.all_eq_true.mp batch_73_23_ok accepted_3698 (by simp [batch_73_23_values])
  exact h
theorem leaf_3698_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3698.profileLo box_3698.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3698_ok
theorem branch_box_3698_nonnegative : ∀ j, 0 ≤ branch_box_3698.lower j ∧ 0 ≤ branch_box_3698.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3698, Box.profileLo, Box.profileHi, box_3698]
theorem leaf_3698_BranchSafe : CertificateConsequences.BranchSafe branch_box_3698 := by
  left; refine ⟨branch_box_3698_nonnegative, ?_⟩
  intro z hz; exact leaf_3698_sound hz

#print axioms batch_73_00_ok
#print axioms leaf_3653_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
