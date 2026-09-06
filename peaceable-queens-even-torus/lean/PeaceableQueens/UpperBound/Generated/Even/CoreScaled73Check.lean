import PeaceableQueens.UpperBound.Generated.Even.CoreScaled73Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_73_00_values : List Bool := [accepted_3650]
theorem batch_73_00_ok : batch_73_00_values.all id = true := by decide

def batch_73_01_values : List Bool := [accepted_3654]
theorem batch_73_01_ok : batch_73_01_values.all id = true := by decide

def batch_73_02_values : List Bool := [accepted_3656]
theorem batch_73_02_ok : batch_73_02_values.all id = true := by decide

def batch_73_03_values : List Bool := [accepted_3662]
theorem batch_73_03_ok : batch_73_03_values.all id = true := by decide

def batch_73_04_values : List Bool := [accepted_3664]
theorem batch_73_04_ok : batch_73_04_values.all id = true := by decide

def batch_73_05_values : List Bool := [accepted_3665]
theorem batch_73_05_ok : batch_73_05_values.all id = true := by decide

def batch_73_06_values : List Bool := [accepted_3667]
theorem batch_73_06_ok : batch_73_06_values.all id = true := by decide

def batch_73_07_values : List Bool := [accepted_3676]
theorem batch_73_07_ok : batch_73_07_values.all id = true := by decide

def batch_73_08_values : List Bool := [accepted_3677]
theorem batch_73_08_ok : batch_73_08_values.all id = true := by decide

def batch_73_09_values : List Bool := [accepted_3682]
theorem batch_73_09_ok : batch_73_09_values.all id = true := by decide

def batch_73_10_values : List Bool := [accepted_3683]
theorem batch_73_10_ok : batch_73_10_values.all id = true := by decide

def batch_73_11_values : List Bool := [accepted_3686]
theorem batch_73_11_ok : batch_73_11_values.all id = true := by decide

def batch_73_12_values : List Bool := [accepted_3687]
theorem batch_73_12_ok : batch_73_12_values.all id = true := by decide

def batch_73_13_values : List Bool := [accepted_3690]
theorem batch_73_13_ok : batch_73_13_values.all id = true := by decide

def batch_73_14_values : List Bool := [accepted_3692]
theorem batch_73_14_ok : batch_73_14_values.all id = true := by decide

def batch_73_15_values : List Bool := [accepted_3696]
theorem batch_73_15_ok : batch_73_15_values.all id = true := by decide

def batch_73_16_values : List Bool := [accepted_3697]
theorem batch_73_16_ok : batch_73_16_values.all id = true := by decide

theorem leaf_3650_ok : checkAt 527 1000 box_3650 cert_3650 = true := by
  have h := List.all_eq_true.mp batch_73_00_ok accepted_3650 (by simp [batch_73_00_values])
  exact h
theorem leaf_3650_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3650.profileLo box_3650.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3650_ok
theorem branch_box_3650_nonnegative : ∀ j, 0 ≤ branch_box_3650.lower j ∧ 0 ≤ branch_box_3650.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3650, Box.profileLo, Box.profileHi, box_3650]
theorem leaf_3650_BranchSafe : CertificateConsequences.BranchSafe branch_box_3650 := by
  left; refine ⟨branch_box_3650_nonnegative, ?_⟩
  intro z hz; exact leaf_3650_sound hz

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

theorem leaf_3656_ok : checkAt 527 1000 box_3656 cert_3656 = true := by
  have h := List.all_eq_true.mp batch_73_02_ok accepted_3656 (by simp [batch_73_02_values])
  exact h
theorem leaf_3656_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3656.profileLo box_3656.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3656_ok
theorem branch_box_3656_nonnegative : ∀ j, 0 ≤ branch_box_3656.lower j ∧ 0 ≤ branch_box_3656.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3656, Box.profileLo, Box.profileHi, box_3656]
theorem leaf_3656_BranchSafe : CertificateConsequences.BranchSafe branch_box_3656 := by
  left; refine ⟨branch_box_3656_nonnegative, ?_⟩
  intro z hz; exact leaf_3656_sound hz

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

theorem leaf_3664_ok : checkAt 527 1000 box_3664 cert_3664 = true := by
  have h := List.all_eq_true.mp batch_73_04_ok accepted_3664 (by simp [batch_73_04_values])
  exact h
theorem leaf_3664_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3664.profileLo box_3664.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3664_ok
theorem branch_box_3664_nonnegative : ∀ j, 0 ≤ branch_box_3664.lower j ∧ 0 ≤ branch_box_3664.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3664, Box.profileLo, Box.profileHi, box_3664]
theorem leaf_3664_BranchSafe : CertificateConsequences.BranchSafe branch_box_3664 := by
  left; refine ⟨branch_box_3664_nonnegative, ?_⟩
  intro z hz; exact leaf_3664_sound hz

theorem leaf_3665_ok : checkAt 527 1000 box_3665 cert_3665 = true := by
  have h := List.all_eq_true.mp batch_73_05_ok accepted_3665 (by simp [batch_73_05_values])
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

theorem leaf_3676_ok : checkAt 527 1000 box_3676 cert_3676 = true := by
  have h := List.all_eq_true.mp batch_73_07_ok accepted_3676 (by simp [batch_73_07_values])
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
  have h := List.all_eq_true.mp batch_73_08_ok accepted_3677 (by simp [batch_73_08_values])
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

theorem leaf_3682_ok : checkAt 527 1000 box_3682 cert_3682 = true := by
  have h := List.all_eq_true.mp batch_73_09_ok accepted_3682 (by simp [batch_73_09_values])
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
  have h := List.all_eq_true.mp batch_73_10_ok accepted_3683 (by simp [batch_73_10_values])
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

theorem leaf_3686_ok : checkAt 527 1000 box_3686 cert_3686 = true := by
  have h := List.all_eq_true.mp batch_73_11_ok accepted_3686 (by simp [batch_73_11_values])
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
  have h := List.all_eq_true.mp batch_73_12_ok accepted_3687 (by simp [batch_73_12_values])
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

theorem leaf_3690_ok : checkAt 527 1000 box_3690 cert_3690 = true := by
  have h := List.all_eq_true.mp batch_73_13_ok accepted_3690 (by simp [batch_73_13_values])
  exact h
theorem leaf_3690_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3690.profileLo box_3690.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3690_ok
theorem branch_box_3690_nonnegative : ∀ j, 0 ≤ branch_box_3690.lower j ∧ 0 ≤ branch_box_3690.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3690, Box.profileLo, Box.profileHi, box_3690]
theorem leaf_3690_BranchSafe : CertificateConsequences.BranchSafe branch_box_3690 := by
  left; refine ⟨branch_box_3690_nonnegative, ?_⟩
  intro z hz; exact leaf_3690_sound hz

theorem leaf_3692_ok : checkAt 527 1000 box_3692 cert_3692 = true := by
  have h := List.all_eq_true.mp batch_73_14_ok accepted_3692 (by simp [batch_73_14_values])
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

theorem leaf_3696_ok : checkAt 527 1000 box_3696 cert_3696 = true := by
  have h := List.all_eq_true.mp batch_73_15_ok accepted_3696 (by simp [batch_73_15_values])
  exact h
theorem leaf_3696_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3696.profileLo box_3696.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3696_ok
theorem branch_box_3696_nonnegative : ∀ j, 0 ≤ branch_box_3696.lower j ∧ 0 ≤ branch_box_3696.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3696, Box.profileLo, Box.profileHi, box_3696]
theorem leaf_3696_BranchSafe : CertificateConsequences.BranchSafe branch_box_3696 := by
  left; refine ⟨branch_box_3696_nonnegative, ?_⟩
  intro z hz; exact leaf_3696_sound hz

theorem leaf_3697_ok : checkAt 527 1000 box_3697 cert_3697 = true := by
  have h := List.all_eq_true.mp batch_73_16_ok accepted_3697 (by simp [batch_73_16_values])
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

#print axioms batch_73_00_ok
#print axioms leaf_3650_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
