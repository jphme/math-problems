import PeaceableQueens.UpperBound.Generated.Even.C527Scaled133Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_133_00_values : List Bool := [accepted_6650]
theorem batch_133_00_ok : batch_133_00_values.all id = true := by decide

def batch_133_01_values : List Bool := [accepted_6652]
theorem batch_133_01_ok : batch_133_01_values.all id = true := by decide

def batch_133_02_values : List Bool := [accepted_6653]
theorem batch_133_02_ok : batch_133_02_values.all id = true := by decide

def batch_133_03_values : List Bool := [accepted_6654]
theorem batch_133_03_ok : batch_133_03_values.all id = true := by decide

def batch_133_04_values : List Bool := [accepted_6655]
theorem batch_133_04_ok : batch_133_04_values.all id = true := by decide

def batch_133_05_values : List Bool := [accepted_6656]
theorem batch_133_05_ok : batch_133_05_values.all id = true := by decide

def batch_133_06_values : List Bool := [accepted_6663]
theorem batch_133_06_ok : batch_133_06_values.all id = true := by decide

def batch_133_07_values : List Bool := [accepted_6664]
theorem batch_133_07_ok : batch_133_07_values.all id = true := by decide

def batch_133_08_values : List Bool := [accepted_6666]
theorem batch_133_08_ok : batch_133_08_values.all id = true := by decide

def batch_133_09_values : List Bool := [accepted_6667]
theorem batch_133_09_ok : batch_133_09_values.all id = true := by decide

def batch_133_10_values : List Bool := [accepted_6668]
theorem batch_133_10_ok : batch_133_10_values.all id = true := by decide

def batch_133_11_values : List Bool := [accepted_6670]
theorem batch_133_11_ok : batch_133_11_values.all id = true := by decide

def batch_133_12_values : List Bool := [accepted_6671]
theorem batch_133_12_ok : batch_133_12_values.all id = true := by decide

def batch_133_13_values : List Bool := [accepted_6672]
theorem batch_133_13_ok : batch_133_13_values.all id = true := by decide

def batch_133_14_values : List Bool := [accepted_6679]
theorem batch_133_14_ok : batch_133_14_values.all id = true := by decide

def batch_133_15_values : List Bool := [accepted_6680]
theorem batch_133_15_ok : batch_133_15_values.all id = true := by decide

def batch_133_16_values : List Bool := [accepted_6682]
theorem batch_133_16_ok : batch_133_16_values.all id = true := by decide

def batch_133_17_values : List Bool := [accepted_6683]
theorem batch_133_17_ok : batch_133_17_values.all id = true := by decide

def batch_133_18_values : List Bool := [accepted_6684]
theorem batch_133_18_ok : batch_133_18_values.all id = true := by decide

def batch_133_19_values : List Bool := [accepted_6687]
theorem batch_133_19_ok : batch_133_19_values.all id = true := by decide

def batch_133_20_values : List Bool := [accepted_6688]
theorem batch_133_20_ok : batch_133_20_values.all id = true := by decide

def batch_133_21_values : List Bool := [accepted_6690]
theorem batch_133_21_ok : batch_133_21_values.all id = true := by decide

def batch_133_22_values : List Bool := [accepted_6691]
theorem batch_133_22_ok : batch_133_22_values.all id = true := by decide

def batch_133_23_values : List Bool := [accepted_6692]
theorem batch_133_23_ok : batch_133_23_values.all id = true := by decide

def batch_133_24_values : List Bool := [accepted_6698]
theorem batch_133_24_ok : batch_133_24_values.all id = true := by decide

def batch_133_25_values : List Bool := [accepted_6699]
theorem batch_133_25_ok : batch_133_25_values.all id = true := by decide

theorem leaf_6650_ok : checkAt 527 1000 box_6650 cert_6650 = true := by
  have h := List.all_eq_true.mp batch_133_00_ok accepted_6650 (by simp [batch_133_00_values])
  exact h
theorem leaf_6650_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6650.profileLo box_6650.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6650_ok
theorem branch_box_6650_nonnegative : ∀ j, 0 ≤ branch_box_6650.lower j ∧ 0 ≤ branch_box_6650.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6650, Box.profileLo, Box.profileHi, box_6650]
theorem leaf_6650_BranchSafe : CertificateConsequences.BranchSafe branch_box_6650 := by
  left; refine ⟨branch_box_6650_nonnegative, ?_⟩
  intro z hz; exact leaf_6650_sound hz

theorem leaf_6652_ok : checkAt 527 1000 box_6652 cert_6652 = true := by
  have h := List.all_eq_true.mp batch_133_01_ok accepted_6652 (by simp [batch_133_01_values])
  exact h
theorem leaf_6652_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6652.profileLo box_6652.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6652_ok
theorem branch_box_6652_nonnegative : ∀ j, 0 ≤ branch_box_6652.lower j ∧ 0 ≤ branch_box_6652.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6652, Box.profileLo, Box.profileHi, box_6652]
theorem leaf_6652_BranchSafe : CertificateConsequences.BranchSafe branch_box_6652 := by
  left; refine ⟨branch_box_6652_nonnegative, ?_⟩
  intro z hz; exact leaf_6652_sound hz

theorem leaf_6653_ok : checkAt 527 1000 box_6653 cert_6653 = true := by
  have h := List.all_eq_true.mp batch_133_02_ok accepted_6653 (by simp [batch_133_02_values])
  exact h
theorem leaf_6653_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6653.profileLo box_6653.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6653_ok
theorem branch_box_6653_nonnegative : ∀ j, 0 ≤ branch_box_6653.lower j ∧ 0 ≤ branch_box_6653.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6653, Box.profileLo, Box.profileHi, box_6653]
theorem leaf_6653_BranchSafe : CertificateConsequences.BranchSafe branch_box_6653 := by
  left; refine ⟨branch_box_6653_nonnegative, ?_⟩
  intro z hz; exact leaf_6653_sound hz

theorem leaf_6654_ok : checkAt 527 1000 box_6654 cert_6654 = true := by
  have h := List.all_eq_true.mp batch_133_03_ok accepted_6654 (by simp [batch_133_03_values])
  exact h
theorem leaf_6654_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6654.profileLo box_6654.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6654_ok
theorem branch_box_6654_nonnegative : ∀ j, 0 ≤ branch_box_6654.lower j ∧ 0 ≤ branch_box_6654.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6654, Box.profileLo, Box.profileHi, box_6654]
theorem leaf_6654_BranchSafe : CertificateConsequences.BranchSafe branch_box_6654 := by
  left; refine ⟨branch_box_6654_nonnegative, ?_⟩
  intro z hz; exact leaf_6654_sound hz

theorem leaf_6655_ok : checkAt 527 1000 box_6655 cert_6655 = true := by
  have h := List.all_eq_true.mp batch_133_04_ok accepted_6655 (by simp [batch_133_04_values])
  exact h
theorem leaf_6655_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6655.profileLo box_6655.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6655_ok
theorem branch_box_6655_nonnegative : ∀ j, 0 ≤ branch_box_6655.lower j ∧ 0 ≤ branch_box_6655.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6655, Box.profileLo, Box.profileHi, box_6655]
theorem leaf_6655_BranchSafe : CertificateConsequences.BranchSafe branch_box_6655 := by
  left; refine ⟨branch_box_6655_nonnegative, ?_⟩
  intro z hz; exact leaf_6655_sound hz

theorem leaf_6656_ok : checkAt 527 1000 box_6656 cert_6656 = true := by
  have h := List.all_eq_true.mp batch_133_05_ok accepted_6656 (by simp [batch_133_05_values])
  exact h
theorem leaf_6656_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6656.profileLo box_6656.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6656_ok
theorem branch_box_6656_nonnegative : ∀ j, 0 ≤ branch_box_6656.lower j ∧ 0 ≤ branch_box_6656.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6656, Box.profileLo, Box.profileHi, box_6656]
theorem leaf_6656_BranchSafe : CertificateConsequences.BranchSafe branch_box_6656 := by
  left; refine ⟨branch_box_6656_nonnegative, ?_⟩
  intro z hz; exact leaf_6656_sound hz

theorem leaf_6663_ok : checkAt 527 1000 box_6663 cert_6663 = true := by
  have h := List.all_eq_true.mp batch_133_06_ok accepted_6663 (by simp [batch_133_06_values])
  exact h
theorem leaf_6663_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6663.profileLo box_6663.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6663_ok
theorem branch_box_6663_nonnegative : ∀ j, 0 ≤ branch_box_6663.lower j ∧ 0 ≤ branch_box_6663.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6663, Box.profileLo, Box.profileHi, box_6663]
theorem leaf_6663_BranchSafe : CertificateConsequences.BranchSafe branch_box_6663 := by
  left; refine ⟨branch_box_6663_nonnegative, ?_⟩
  intro z hz; exact leaf_6663_sound hz

theorem leaf_6664_ok : checkAt 527 1000 box_6664 cert_6664 = true := by
  have h := List.all_eq_true.mp batch_133_07_ok accepted_6664 (by simp [batch_133_07_values])
  exact h
theorem leaf_6664_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6664.profileLo box_6664.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6664_ok
theorem branch_box_6664_nonnegative : ∀ j, 0 ≤ branch_box_6664.lower j ∧ 0 ≤ branch_box_6664.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6664, Box.profileLo, Box.profileHi, box_6664]
theorem leaf_6664_BranchSafe : CertificateConsequences.BranchSafe branch_box_6664 := by
  left; refine ⟨branch_box_6664_nonnegative, ?_⟩
  intro z hz; exact leaf_6664_sound hz

theorem leaf_6666_ok : checkAt 527 1000 box_6666 cert_6666 = true := by
  have h := List.all_eq_true.mp batch_133_08_ok accepted_6666 (by simp [batch_133_08_values])
  exact h
theorem leaf_6666_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6666.profileLo box_6666.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6666_ok
theorem branch_box_6666_nonnegative : ∀ j, 0 ≤ branch_box_6666.lower j ∧ 0 ≤ branch_box_6666.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6666, Box.profileLo, Box.profileHi, box_6666]
theorem leaf_6666_BranchSafe : CertificateConsequences.BranchSafe branch_box_6666 := by
  left; refine ⟨branch_box_6666_nonnegative, ?_⟩
  intro z hz; exact leaf_6666_sound hz

theorem leaf_6667_ok : checkAt 527 1000 box_6667 cert_6667 = true := by
  have h := List.all_eq_true.mp batch_133_09_ok accepted_6667 (by simp [batch_133_09_values])
  exact h
theorem leaf_6667_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6667.profileLo box_6667.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6667_ok
theorem branch_box_6667_nonnegative : ∀ j, 0 ≤ branch_box_6667.lower j ∧ 0 ≤ branch_box_6667.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6667, Box.profileLo, Box.profileHi, box_6667]
theorem leaf_6667_BranchSafe : CertificateConsequences.BranchSafe branch_box_6667 := by
  left; refine ⟨branch_box_6667_nonnegative, ?_⟩
  intro z hz; exact leaf_6667_sound hz

theorem leaf_6668_ok : checkAt 527 1000 box_6668 cert_6668 = true := by
  have h := List.all_eq_true.mp batch_133_10_ok accepted_6668 (by simp [batch_133_10_values])
  exact h
theorem leaf_6668_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6668.profileLo box_6668.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6668_ok
theorem branch_box_6668_nonnegative : ∀ j, 0 ≤ branch_box_6668.lower j ∧ 0 ≤ branch_box_6668.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6668, Box.profileLo, Box.profileHi, box_6668]
theorem leaf_6668_BranchSafe : CertificateConsequences.BranchSafe branch_box_6668 := by
  left; refine ⟨branch_box_6668_nonnegative, ?_⟩
  intro z hz; exact leaf_6668_sound hz

theorem leaf_6670_ok : checkAt 527 1000 box_6670 cert_6670 = true := by
  have h := List.all_eq_true.mp batch_133_11_ok accepted_6670 (by simp [batch_133_11_values])
  exact h
theorem leaf_6670_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6670.profileLo box_6670.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6670_ok
theorem branch_box_6670_nonnegative : ∀ j, 0 ≤ branch_box_6670.lower j ∧ 0 ≤ branch_box_6670.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6670, Box.profileLo, Box.profileHi, box_6670]
theorem leaf_6670_BranchSafe : CertificateConsequences.BranchSafe branch_box_6670 := by
  left; refine ⟨branch_box_6670_nonnegative, ?_⟩
  intro z hz; exact leaf_6670_sound hz

theorem leaf_6671_ok : checkAt 527 1000 box_6671 cert_6671 = true := by
  have h := List.all_eq_true.mp batch_133_12_ok accepted_6671 (by simp [batch_133_12_values])
  exact h
theorem leaf_6671_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6671.profileLo box_6671.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6671_ok
theorem branch_box_6671_nonnegative : ∀ j, 0 ≤ branch_box_6671.lower j ∧ 0 ≤ branch_box_6671.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6671, Box.profileLo, Box.profileHi, box_6671]
theorem leaf_6671_BranchSafe : CertificateConsequences.BranchSafe branch_box_6671 := by
  left; refine ⟨branch_box_6671_nonnegative, ?_⟩
  intro z hz; exact leaf_6671_sound hz

theorem leaf_6672_ok : checkAt 527 1000 box_6672 cert_6672 = true := by
  have h := List.all_eq_true.mp batch_133_13_ok accepted_6672 (by simp [batch_133_13_values])
  exact h
theorem leaf_6672_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6672.profileLo box_6672.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6672_ok
theorem branch_box_6672_nonnegative : ∀ j, 0 ≤ branch_box_6672.lower j ∧ 0 ≤ branch_box_6672.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6672, Box.profileLo, Box.profileHi, box_6672]
theorem leaf_6672_BranchSafe : CertificateConsequences.BranchSafe branch_box_6672 := by
  left; refine ⟨branch_box_6672_nonnegative, ?_⟩
  intro z hz; exact leaf_6672_sound hz

theorem leaf_6679_ok : checkAt 527 1000 box_6679 cert_6679 = true := by
  have h := List.all_eq_true.mp batch_133_14_ok accepted_6679 (by simp [batch_133_14_values])
  exact h
theorem leaf_6679_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6679.profileLo box_6679.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6679_ok
theorem branch_box_6679_nonnegative : ∀ j, 0 ≤ branch_box_6679.lower j ∧ 0 ≤ branch_box_6679.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6679, Box.profileLo, Box.profileHi, box_6679]
theorem leaf_6679_BranchSafe : CertificateConsequences.BranchSafe branch_box_6679 := by
  left; refine ⟨branch_box_6679_nonnegative, ?_⟩
  intro z hz; exact leaf_6679_sound hz

theorem leaf_6680_ok : checkAt 527 1000 box_6680 cert_6680 = true := by
  have h := List.all_eq_true.mp batch_133_15_ok accepted_6680 (by simp [batch_133_15_values])
  exact h
theorem leaf_6680_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6680.profileLo box_6680.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6680_ok
theorem branch_box_6680_nonnegative : ∀ j, 0 ≤ branch_box_6680.lower j ∧ 0 ≤ branch_box_6680.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6680, Box.profileLo, Box.profileHi, box_6680]
theorem leaf_6680_BranchSafe : CertificateConsequences.BranchSafe branch_box_6680 := by
  left; refine ⟨branch_box_6680_nonnegative, ?_⟩
  intro z hz; exact leaf_6680_sound hz

theorem leaf_6682_ok : checkAt 527 1000 box_6682 cert_6682 = true := by
  have h := List.all_eq_true.mp batch_133_16_ok accepted_6682 (by simp [batch_133_16_values])
  exact h
theorem leaf_6682_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6682.profileLo box_6682.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6682_ok
theorem branch_box_6682_nonnegative : ∀ j, 0 ≤ branch_box_6682.lower j ∧ 0 ≤ branch_box_6682.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6682, Box.profileLo, Box.profileHi, box_6682]
theorem leaf_6682_BranchSafe : CertificateConsequences.BranchSafe branch_box_6682 := by
  left; refine ⟨branch_box_6682_nonnegative, ?_⟩
  intro z hz; exact leaf_6682_sound hz

theorem leaf_6683_ok : checkAt 527 1000 box_6683 cert_6683 = true := by
  have h := List.all_eq_true.mp batch_133_17_ok accepted_6683 (by simp [batch_133_17_values])
  exact h
theorem leaf_6683_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6683.profileLo box_6683.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6683_ok
theorem branch_box_6683_nonnegative : ∀ j, 0 ≤ branch_box_6683.lower j ∧ 0 ≤ branch_box_6683.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6683, Box.profileLo, Box.profileHi, box_6683]
theorem leaf_6683_BranchSafe : CertificateConsequences.BranchSafe branch_box_6683 := by
  left; refine ⟨branch_box_6683_nonnegative, ?_⟩
  intro z hz; exact leaf_6683_sound hz

theorem leaf_6684_ok : checkAt 527 1000 box_6684 cert_6684 = true := by
  have h := List.all_eq_true.mp batch_133_18_ok accepted_6684 (by simp [batch_133_18_values])
  exact h
theorem leaf_6684_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6684.profileLo box_6684.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6684_ok
theorem branch_box_6684_nonnegative : ∀ j, 0 ≤ branch_box_6684.lower j ∧ 0 ≤ branch_box_6684.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6684, Box.profileLo, Box.profileHi, box_6684]
theorem leaf_6684_BranchSafe : CertificateConsequences.BranchSafe branch_box_6684 := by
  left; refine ⟨branch_box_6684_nonnegative, ?_⟩
  intro z hz; exact leaf_6684_sound hz

theorem leaf_6687_ok : checkAt 527 1000 box_6687 cert_6687 = true := by
  have h := List.all_eq_true.mp batch_133_19_ok accepted_6687 (by simp [batch_133_19_values])
  exact h
theorem leaf_6687_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6687.profileLo box_6687.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6687_ok
theorem branch_box_6687_nonnegative : ∀ j, 0 ≤ branch_box_6687.lower j ∧ 0 ≤ branch_box_6687.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6687, Box.profileLo, Box.profileHi, box_6687]
theorem leaf_6687_BranchSafe : CertificateConsequences.BranchSafe branch_box_6687 := by
  left; refine ⟨branch_box_6687_nonnegative, ?_⟩
  intro z hz; exact leaf_6687_sound hz

theorem leaf_6688_ok : checkAt 527 1000 box_6688 cert_6688 = true := by
  have h := List.all_eq_true.mp batch_133_20_ok accepted_6688 (by simp [batch_133_20_values])
  exact h
theorem leaf_6688_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6688.profileLo box_6688.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6688_ok
theorem branch_box_6688_nonnegative : ∀ j, 0 ≤ branch_box_6688.lower j ∧ 0 ≤ branch_box_6688.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6688, Box.profileLo, Box.profileHi, box_6688]
theorem leaf_6688_BranchSafe : CertificateConsequences.BranchSafe branch_box_6688 := by
  left; refine ⟨branch_box_6688_nonnegative, ?_⟩
  intro z hz; exact leaf_6688_sound hz

theorem leaf_6690_ok : checkAt 527 1000 box_6690 cert_6690 = true := by
  have h := List.all_eq_true.mp batch_133_21_ok accepted_6690 (by simp [batch_133_21_values])
  exact h
theorem leaf_6690_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6690.profileLo box_6690.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6690_ok
theorem branch_box_6690_nonnegative : ∀ j, 0 ≤ branch_box_6690.lower j ∧ 0 ≤ branch_box_6690.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6690, Box.profileLo, Box.profileHi, box_6690]
theorem leaf_6690_BranchSafe : CertificateConsequences.BranchSafe branch_box_6690 := by
  left; refine ⟨branch_box_6690_nonnegative, ?_⟩
  intro z hz; exact leaf_6690_sound hz

theorem leaf_6691_ok : checkAt 527 1000 box_6691 cert_6691 = true := by
  have h := List.all_eq_true.mp batch_133_22_ok accepted_6691 (by simp [batch_133_22_values])
  exact h
theorem leaf_6691_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6691.profileLo box_6691.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6691_ok
theorem branch_box_6691_nonnegative : ∀ j, 0 ≤ branch_box_6691.lower j ∧ 0 ≤ branch_box_6691.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6691, Box.profileLo, Box.profileHi, box_6691]
theorem leaf_6691_BranchSafe : CertificateConsequences.BranchSafe branch_box_6691 := by
  left; refine ⟨branch_box_6691_nonnegative, ?_⟩
  intro z hz; exact leaf_6691_sound hz

theorem leaf_6692_ok : checkAt 527 1000 box_6692 cert_6692 = true := by
  have h := List.all_eq_true.mp batch_133_23_ok accepted_6692 (by simp [batch_133_23_values])
  exact h
theorem leaf_6692_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6692.profileLo box_6692.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6692_ok
theorem branch_box_6692_nonnegative : ∀ j, 0 ≤ branch_box_6692.lower j ∧ 0 ≤ branch_box_6692.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6692, Box.profileLo, Box.profileHi, box_6692]
theorem leaf_6692_BranchSafe : CertificateConsequences.BranchSafe branch_box_6692 := by
  left; refine ⟨branch_box_6692_nonnegative, ?_⟩
  intro z hz; exact leaf_6692_sound hz

theorem leaf_6698_ok : checkAt 527 1000 box_6698 cert_6698 = true := by
  have h := List.all_eq_true.mp batch_133_24_ok accepted_6698 (by simp [batch_133_24_values])
  exact h
theorem leaf_6698_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6698.profileLo box_6698.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6698_ok
theorem branch_box_6698_nonnegative : ∀ j, 0 ≤ branch_box_6698.lower j ∧ 0 ≤ branch_box_6698.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6698, Box.profileLo, Box.profileHi, box_6698]
theorem leaf_6698_BranchSafe : CertificateConsequences.BranchSafe branch_box_6698 := by
  left; refine ⟨branch_box_6698_nonnegative, ?_⟩
  intro z hz; exact leaf_6698_sound hz

theorem leaf_6699_ok : checkAt 527 1000 box_6699 cert_6699 = true := by
  have h := List.all_eq_true.mp batch_133_25_ok accepted_6699 (by simp [batch_133_25_values])
  exact h
theorem leaf_6699_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6699.profileLo box_6699.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6699_ok
theorem branch_box_6699_nonnegative : ∀ j, 0 ≤ branch_box_6699.lower j ∧ 0 ≤ branch_box_6699.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6699, Box.profileLo, Box.profileHi, box_6699]
theorem leaf_6699_BranchSafe : CertificateConsequences.BranchSafe branch_box_6699 := by
  left; refine ⟨branch_box_6699_nonnegative, ?_⟩
  intro z hz; exact leaf_6699_sound hz

#print axioms batch_133_00_ok
#print axioms leaf_6650_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
