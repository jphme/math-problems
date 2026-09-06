import PeaceableQueens.UpperBound.Generated.Even.C527Scaled113Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_113_00_values : List Bool := [accepted_5650]
theorem batch_113_00_ok : batch_113_00_values.all id = true := by decide

def batch_113_01_values : List Bool := [accepted_5653]
theorem batch_113_01_ok : batch_113_01_values.all id = true := by decide

def batch_113_02_values : List Bool := [accepted_5657]
theorem batch_113_02_ok : batch_113_02_values.all id = true := by decide

def batch_113_03_values : List Bool := [accepted_5658]
theorem batch_113_03_ok : batch_113_03_values.all id = true := by decide

def batch_113_04_values : List Bool := [accepted_5659]
theorem batch_113_04_ok : batch_113_04_values.all id = true := by decide

def batch_113_05_values : List Bool := [accepted_5661]
theorem batch_113_05_ok : batch_113_05_values.all id = true := by decide

def batch_113_06_values : List Bool := [accepted_5662]
theorem batch_113_06_ok : batch_113_06_values.all id = true := by decide

def batch_113_07_values : List Bool := [accepted_5669]
theorem batch_113_07_ok : batch_113_07_values.all id = true := by decide

def batch_113_08_values : List Bool := [accepted_5670]
theorem batch_113_08_ok : batch_113_08_values.all id = true := by decide

def batch_113_09_values : List Bool := [accepted_5671]
theorem batch_113_09_ok : batch_113_09_values.all id = true := by decide

def batch_113_10_values : List Bool := [accepted_5672]
theorem batch_113_10_ok : batch_113_10_values.all id = true := by decide

def batch_113_11_values : List Bool := [accepted_5673]
theorem batch_113_11_ok : batch_113_11_values.all id = true := by decide

def batch_113_12_values : List Bool := [accepted_5676]
theorem batch_113_12_ok : batch_113_12_values.all id = true := by decide

def batch_113_13_values : List Bool := [accepted_5677]
theorem batch_113_13_ok : batch_113_13_values.all id = true := by decide

def batch_113_14_values : List Bool := [accepted_5678]
theorem batch_113_14_ok : batch_113_14_values.all id = true := by decide

def batch_113_15_values : List Bool := [accepted_5683]
theorem batch_113_15_ok : batch_113_15_values.all id = true := by decide

def batch_113_16_values : List Bool := [accepted_5684]
theorem batch_113_16_ok : batch_113_16_values.all id = true := by decide

def batch_113_17_values : List Bool := [accepted_5685]
theorem batch_113_17_ok : batch_113_17_values.all id = true := by decide

def batch_113_18_values : List Bool := [accepted_5687]
theorem batch_113_18_ok : batch_113_18_values.all id = true := by decide

def batch_113_19_values : List Bool := [accepted_5689]
theorem batch_113_19_ok : batch_113_19_values.all id = true := by decide

def batch_113_20_values : List Bool := [accepted_5690]
theorem batch_113_20_ok : batch_113_20_values.all id = true := by decide

def batch_113_21_values : List Bool := [accepted_5695]
theorem batch_113_21_ok : batch_113_21_values.all id = true := by decide

def batch_113_22_values : List Bool := [accepted_5696]
theorem batch_113_22_ok : batch_113_22_values.all id = true := by decide

def batch_113_23_values : List Bool := [accepted_5697]
theorem batch_113_23_ok : batch_113_23_values.all id = true := by decide

def batch_113_24_values : List Bool := [accepted_5699]
theorem batch_113_24_ok : batch_113_24_values.all id = true := by decide

theorem leaf_5650_ok : checkAt 527 1000 box_5650 cert_5650 = true := by
  have h := List.all_eq_true.mp batch_113_00_ok accepted_5650 (by simp [batch_113_00_values])
  exact h
theorem leaf_5650_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5650.profileLo box_5650.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5650_ok
theorem branch_box_5650_nonnegative : ∀ j, 0 ≤ branch_box_5650.lower j ∧ 0 ≤ branch_box_5650.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5650, Box.profileLo, Box.profileHi, box_5650]
theorem leaf_5650_BranchSafe : CertificateConsequences.BranchSafe branch_box_5650 := by
  left; refine ⟨branch_box_5650_nonnegative, ?_⟩
  intro z hz; exact leaf_5650_sound hz

theorem leaf_5653_ok : checkAt 527 1000 box_5653 cert_5653 = true := by
  have h := List.all_eq_true.mp batch_113_01_ok accepted_5653 (by simp [batch_113_01_values])
  exact h
theorem leaf_5653_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5653.profileLo box_5653.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5653_ok
theorem branch_box_5653_nonnegative : ∀ j, 0 ≤ branch_box_5653.lower j ∧ 0 ≤ branch_box_5653.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5653, Box.profileLo, Box.profileHi, box_5653]
theorem leaf_5653_BranchSafe : CertificateConsequences.BranchSafe branch_box_5653 := by
  left; refine ⟨branch_box_5653_nonnegative, ?_⟩
  intro z hz; exact leaf_5653_sound hz

theorem leaf_5657_ok : checkAt 527 1000 box_5657 cert_5657 = true := by
  have h := List.all_eq_true.mp batch_113_02_ok accepted_5657 (by simp [batch_113_02_values])
  exact h
theorem leaf_5657_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5657.profileLo box_5657.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5657_ok
theorem branch_box_5657_nonnegative : ∀ j, 0 ≤ branch_box_5657.lower j ∧ 0 ≤ branch_box_5657.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5657, Box.profileLo, Box.profileHi, box_5657]
theorem leaf_5657_BranchSafe : CertificateConsequences.BranchSafe branch_box_5657 := by
  left; refine ⟨branch_box_5657_nonnegative, ?_⟩
  intro z hz; exact leaf_5657_sound hz

theorem leaf_5658_ok : checkAt 527 1000 box_5658 cert_5658 = true := by
  have h := List.all_eq_true.mp batch_113_03_ok accepted_5658 (by simp [batch_113_03_values])
  exact h
theorem leaf_5658_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5658.profileLo box_5658.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5658_ok
theorem branch_box_5658_nonnegative : ∀ j, 0 ≤ branch_box_5658.lower j ∧ 0 ≤ branch_box_5658.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5658, Box.profileLo, Box.profileHi, box_5658]
theorem leaf_5658_BranchSafe : CertificateConsequences.BranchSafe branch_box_5658 := by
  left; refine ⟨branch_box_5658_nonnegative, ?_⟩
  intro z hz; exact leaf_5658_sound hz

theorem leaf_5659_ok : checkAt 527 1000 box_5659 cert_5659 = true := by
  have h := List.all_eq_true.mp batch_113_04_ok accepted_5659 (by simp [batch_113_04_values])
  exact h
theorem leaf_5659_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5659.profileLo box_5659.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5659_ok
theorem branch_box_5659_nonnegative : ∀ j, 0 ≤ branch_box_5659.lower j ∧ 0 ≤ branch_box_5659.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5659, Box.profileLo, Box.profileHi, box_5659]
theorem leaf_5659_BranchSafe : CertificateConsequences.BranchSafe branch_box_5659 := by
  left; refine ⟨branch_box_5659_nonnegative, ?_⟩
  intro z hz; exact leaf_5659_sound hz

theorem leaf_5661_ok : checkAt 527 1000 box_5661 cert_5661 = true := by
  have h := List.all_eq_true.mp batch_113_05_ok accepted_5661 (by simp [batch_113_05_values])
  exact h
theorem leaf_5661_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5661.profileLo box_5661.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5661_ok
theorem branch_box_5661_nonnegative : ∀ j, 0 ≤ branch_box_5661.lower j ∧ 0 ≤ branch_box_5661.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5661, Box.profileLo, Box.profileHi, box_5661]
theorem leaf_5661_BranchSafe : CertificateConsequences.BranchSafe branch_box_5661 := by
  left; refine ⟨branch_box_5661_nonnegative, ?_⟩
  intro z hz; exact leaf_5661_sound hz

theorem leaf_5662_ok : checkAt 527 1000 box_5662 cert_5662 = true := by
  have h := List.all_eq_true.mp batch_113_06_ok accepted_5662 (by simp [batch_113_06_values])
  exact h
theorem leaf_5662_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5662.profileLo box_5662.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5662_ok
theorem branch_box_5662_nonnegative : ∀ j, 0 ≤ branch_box_5662.lower j ∧ 0 ≤ branch_box_5662.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5662, Box.profileLo, Box.profileHi, box_5662]
theorem leaf_5662_BranchSafe : CertificateConsequences.BranchSafe branch_box_5662 := by
  left; refine ⟨branch_box_5662_nonnegative, ?_⟩
  intro z hz; exact leaf_5662_sound hz

theorem leaf_5669_ok : checkAt 527 1000 box_5669 cert_5669 = true := by
  have h := List.all_eq_true.mp batch_113_07_ok accepted_5669 (by simp [batch_113_07_values])
  exact h
theorem leaf_5669_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5669.profileLo box_5669.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5669_ok
theorem branch_box_5669_nonnegative : ∀ j, 0 ≤ branch_box_5669.lower j ∧ 0 ≤ branch_box_5669.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5669, Box.profileLo, Box.profileHi, box_5669]
theorem leaf_5669_BranchSafe : CertificateConsequences.BranchSafe branch_box_5669 := by
  left; refine ⟨branch_box_5669_nonnegative, ?_⟩
  intro z hz; exact leaf_5669_sound hz

theorem leaf_5670_ok : checkAt 527 1000 box_5670 cert_5670 = true := by
  have h := List.all_eq_true.mp batch_113_08_ok accepted_5670 (by simp [batch_113_08_values])
  exact h
theorem leaf_5670_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5670.profileLo box_5670.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5670_ok
theorem branch_box_5670_nonnegative : ∀ j, 0 ≤ branch_box_5670.lower j ∧ 0 ≤ branch_box_5670.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5670, Box.profileLo, Box.profileHi, box_5670]
theorem leaf_5670_BranchSafe : CertificateConsequences.BranchSafe branch_box_5670 := by
  left; refine ⟨branch_box_5670_nonnegative, ?_⟩
  intro z hz; exact leaf_5670_sound hz

theorem leaf_5671_ok : checkAt 527 1000 box_5671 cert_5671 = true := by
  have h := List.all_eq_true.mp batch_113_09_ok accepted_5671 (by simp [batch_113_09_values])
  exact h
theorem leaf_5671_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5671.profileLo box_5671.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5671_ok
theorem branch_box_5671_nonnegative : ∀ j, 0 ≤ branch_box_5671.lower j ∧ 0 ≤ branch_box_5671.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5671, Box.profileLo, Box.profileHi, box_5671]
theorem leaf_5671_BranchSafe : CertificateConsequences.BranchSafe branch_box_5671 := by
  left; refine ⟨branch_box_5671_nonnegative, ?_⟩
  intro z hz; exact leaf_5671_sound hz

theorem leaf_5672_ok : checkAt 527 1000 box_5672 cert_5672 = true := by
  have h := List.all_eq_true.mp batch_113_10_ok accepted_5672 (by simp [batch_113_10_values])
  exact h
theorem leaf_5672_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5672.profileLo box_5672.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5672_ok
theorem branch_box_5672_nonnegative : ∀ j, 0 ≤ branch_box_5672.lower j ∧ 0 ≤ branch_box_5672.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5672, Box.profileLo, Box.profileHi, box_5672]
theorem leaf_5672_BranchSafe : CertificateConsequences.BranchSafe branch_box_5672 := by
  left; refine ⟨branch_box_5672_nonnegative, ?_⟩
  intro z hz; exact leaf_5672_sound hz

theorem leaf_5673_ok : checkAt 527 1000 box_5673 cert_5673 = true := by
  have h := List.all_eq_true.mp batch_113_11_ok accepted_5673 (by simp [batch_113_11_values])
  exact h
theorem leaf_5673_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5673.profileLo box_5673.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5673_ok
theorem branch_box_5673_nonnegative : ∀ j, 0 ≤ branch_box_5673.lower j ∧ 0 ≤ branch_box_5673.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5673, Box.profileLo, Box.profileHi, box_5673]
theorem leaf_5673_BranchSafe : CertificateConsequences.BranchSafe branch_box_5673 := by
  left; refine ⟨branch_box_5673_nonnegative, ?_⟩
  intro z hz; exact leaf_5673_sound hz

theorem leaf_5676_ok : checkAt 527 1000 box_5676 cert_5676 = true := by
  have h := List.all_eq_true.mp batch_113_12_ok accepted_5676 (by simp [batch_113_12_values])
  exact h
theorem leaf_5676_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5676.profileLo box_5676.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5676_ok
theorem branch_box_5676_nonnegative : ∀ j, 0 ≤ branch_box_5676.lower j ∧ 0 ≤ branch_box_5676.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5676, Box.profileLo, Box.profileHi, box_5676]
theorem leaf_5676_BranchSafe : CertificateConsequences.BranchSafe branch_box_5676 := by
  left; refine ⟨branch_box_5676_nonnegative, ?_⟩
  intro z hz; exact leaf_5676_sound hz

theorem leaf_5677_ok : checkAt 527 1000 box_5677 cert_5677 = true := by
  have h := List.all_eq_true.mp batch_113_13_ok accepted_5677 (by simp [batch_113_13_values])
  exact h
theorem leaf_5677_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5677.profileLo box_5677.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5677_ok
theorem branch_box_5677_nonnegative : ∀ j, 0 ≤ branch_box_5677.lower j ∧ 0 ≤ branch_box_5677.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5677, Box.profileLo, Box.profileHi, box_5677]
theorem leaf_5677_BranchSafe : CertificateConsequences.BranchSafe branch_box_5677 := by
  left; refine ⟨branch_box_5677_nonnegative, ?_⟩
  intro z hz; exact leaf_5677_sound hz

theorem leaf_5678_ok : checkAt 527 1000 box_5678 cert_5678 = true := by
  have h := List.all_eq_true.mp batch_113_14_ok accepted_5678 (by simp [batch_113_14_values])
  exact h
theorem leaf_5678_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5678.profileLo box_5678.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5678_ok
theorem branch_box_5678_nonnegative : ∀ j, 0 ≤ branch_box_5678.lower j ∧ 0 ≤ branch_box_5678.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5678, Box.profileLo, Box.profileHi, box_5678]
theorem leaf_5678_BranchSafe : CertificateConsequences.BranchSafe branch_box_5678 := by
  left; refine ⟨branch_box_5678_nonnegative, ?_⟩
  intro z hz; exact leaf_5678_sound hz

theorem leaf_5683_ok : checkAt 527 1000 box_5683 cert_5683 = true := by
  have h := List.all_eq_true.mp batch_113_15_ok accepted_5683 (by simp [batch_113_15_values])
  exact h
theorem leaf_5683_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5683.profileLo box_5683.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5683_ok
theorem branch_box_5683_nonnegative : ∀ j, 0 ≤ branch_box_5683.lower j ∧ 0 ≤ branch_box_5683.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5683, Box.profileLo, Box.profileHi, box_5683]
theorem leaf_5683_BranchSafe : CertificateConsequences.BranchSafe branch_box_5683 := by
  left; refine ⟨branch_box_5683_nonnegative, ?_⟩
  intro z hz; exact leaf_5683_sound hz

theorem leaf_5684_ok : checkAt 527 1000 box_5684 cert_5684 = true := by
  have h := List.all_eq_true.mp batch_113_16_ok accepted_5684 (by simp [batch_113_16_values])
  exact h
theorem leaf_5684_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5684.profileLo box_5684.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5684_ok
theorem branch_box_5684_nonnegative : ∀ j, 0 ≤ branch_box_5684.lower j ∧ 0 ≤ branch_box_5684.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5684, Box.profileLo, Box.profileHi, box_5684]
theorem leaf_5684_BranchSafe : CertificateConsequences.BranchSafe branch_box_5684 := by
  left; refine ⟨branch_box_5684_nonnegative, ?_⟩
  intro z hz; exact leaf_5684_sound hz

theorem leaf_5685_ok : checkAt 527 1000 box_5685 cert_5685 = true := by
  have h := List.all_eq_true.mp batch_113_17_ok accepted_5685 (by simp [batch_113_17_values])
  exact h
theorem leaf_5685_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5685.profileLo box_5685.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5685_ok
theorem branch_box_5685_nonnegative : ∀ j, 0 ≤ branch_box_5685.lower j ∧ 0 ≤ branch_box_5685.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5685, Box.profileLo, Box.profileHi, box_5685]
theorem leaf_5685_BranchSafe : CertificateConsequences.BranchSafe branch_box_5685 := by
  left; refine ⟨branch_box_5685_nonnegative, ?_⟩
  intro z hz; exact leaf_5685_sound hz

theorem leaf_5687_ok : checkAt 527 1000 box_5687 cert_5687 = true := by
  have h := List.all_eq_true.mp batch_113_18_ok accepted_5687 (by simp [batch_113_18_values])
  exact h
theorem leaf_5687_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5687.profileLo box_5687.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5687_ok
theorem branch_box_5687_nonnegative : ∀ j, 0 ≤ branch_box_5687.lower j ∧ 0 ≤ branch_box_5687.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5687, Box.profileLo, Box.profileHi, box_5687]
theorem leaf_5687_BranchSafe : CertificateConsequences.BranchSafe branch_box_5687 := by
  left; refine ⟨branch_box_5687_nonnegative, ?_⟩
  intro z hz; exact leaf_5687_sound hz

theorem leaf_5689_ok : checkAt 527 1000 box_5689 cert_5689 = true := by
  have h := List.all_eq_true.mp batch_113_19_ok accepted_5689 (by simp [batch_113_19_values])
  exact h
theorem leaf_5689_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5689.profileLo box_5689.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5689_ok
theorem branch_box_5689_nonnegative : ∀ j, 0 ≤ branch_box_5689.lower j ∧ 0 ≤ branch_box_5689.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5689, Box.profileLo, Box.profileHi, box_5689]
theorem leaf_5689_BranchSafe : CertificateConsequences.BranchSafe branch_box_5689 := by
  left; refine ⟨branch_box_5689_nonnegative, ?_⟩
  intro z hz; exact leaf_5689_sound hz

theorem leaf_5690_ok : checkAt 527 1000 box_5690 cert_5690 = true := by
  have h := List.all_eq_true.mp batch_113_20_ok accepted_5690 (by simp [batch_113_20_values])
  exact h
theorem leaf_5690_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5690.profileLo box_5690.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5690_ok
theorem branch_box_5690_nonnegative : ∀ j, 0 ≤ branch_box_5690.lower j ∧ 0 ≤ branch_box_5690.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5690, Box.profileLo, Box.profileHi, box_5690]
theorem leaf_5690_BranchSafe : CertificateConsequences.BranchSafe branch_box_5690 := by
  left; refine ⟨branch_box_5690_nonnegative, ?_⟩
  intro z hz; exact leaf_5690_sound hz

theorem leaf_5695_ok : checkAt 527 1000 box_5695 cert_5695 = true := by
  have h := List.all_eq_true.mp batch_113_21_ok accepted_5695 (by simp [batch_113_21_values])
  exact h
theorem leaf_5695_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5695.profileLo box_5695.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5695_ok
theorem branch_box_5695_nonnegative : ∀ j, 0 ≤ branch_box_5695.lower j ∧ 0 ≤ branch_box_5695.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5695, Box.profileLo, Box.profileHi, box_5695]
theorem leaf_5695_BranchSafe : CertificateConsequences.BranchSafe branch_box_5695 := by
  left; refine ⟨branch_box_5695_nonnegative, ?_⟩
  intro z hz; exact leaf_5695_sound hz

theorem leaf_5696_ok : checkAt 527 1000 box_5696 cert_5696 = true := by
  have h := List.all_eq_true.mp batch_113_22_ok accepted_5696 (by simp [batch_113_22_values])
  exact h
theorem leaf_5696_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5696.profileLo box_5696.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5696_ok
theorem branch_box_5696_nonnegative : ∀ j, 0 ≤ branch_box_5696.lower j ∧ 0 ≤ branch_box_5696.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5696, Box.profileLo, Box.profileHi, box_5696]
theorem leaf_5696_BranchSafe : CertificateConsequences.BranchSafe branch_box_5696 := by
  left; refine ⟨branch_box_5696_nonnegative, ?_⟩
  intro z hz; exact leaf_5696_sound hz

theorem leaf_5697_ok : checkAt 527 1000 box_5697 cert_5697 = true := by
  have h := List.all_eq_true.mp batch_113_23_ok accepted_5697 (by simp [batch_113_23_values])
  exact h
theorem leaf_5697_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5697.profileLo box_5697.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5697_ok
theorem branch_box_5697_nonnegative : ∀ j, 0 ≤ branch_box_5697.lower j ∧ 0 ≤ branch_box_5697.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5697, Box.profileLo, Box.profileHi, box_5697]
theorem leaf_5697_BranchSafe : CertificateConsequences.BranchSafe branch_box_5697 := by
  left; refine ⟨branch_box_5697_nonnegative, ?_⟩
  intro z hz; exact leaf_5697_sound hz

theorem leaf_5699_ok : checkAt 527 1000 box_5699 cert_5699 = true := by
  have h := List.all_eq_true.mp batch_113_24_ok accepted_5699 (by simp [batch_113_24_values])
  exact h
theorem leaf_5699_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5699.profileLo box_5699.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5699_ok
theorem branch_box_5699_nonnegative : ∀ j, 0 ≤ branch_box_5699.lower j ∧ 0 ≤ branch_box_5699.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5699, Box.profileLo, Box.profileHi, box_5699]
theorem leaf_5699_BranchSafe : CertificateConsequences.BranchSafe branch_box_5699 := by
  left; refine ⟨branch_box_5699_nonnegative, ?_⟩
  intro z hz; exact leaf_5699_sound hz

#print axioms batch_113_00_ok
#print axioms leaf_5650_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
