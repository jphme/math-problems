import PeaceableQueens.UpperBound.Generated.Even.C527Scaled93Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_93_00_values : List Bool := [accepted_4655]
theorem batch_93_00_ok : batch_93_00_values.all id = true := by decide

def batch_93_01_values : List Bool := [accepted_4656]
theorem batch_93_01_ok : batch_93_01_values.all id = true := by decide

def batch_93_02_values : List Bool := [accepted_4657]
theorem batch_93_02_ok : batch_93_02_values.all id = true := by decide

def batch_93_03_values : List Bool := [accepted_4659]
theorem batch_93_03_ok : batch_93_03_values.all id = true := by decide

def batch_93_04_values : List Bool := [accepted_4660]
theorem batch_93_04_ok : batch_93_04_values.all id = true := by decide

def batch_93_05_values : List Bool := [accepted_4666]
theorem batch_93_05_ok : batch_93_05_values.all id = true := by decide

def batch_93_06_values : List Bool := [accepted_4667]
theorem batch_93_06_ok : batch_93_06_values.all id = true := by decide

def batch_93_07_values : List Bool := [accepted_4668]
theorem batch_93_07_ok : batch_93_07_values.all id = true := by decide

def batch_93_08_values : List Bool := [accepted_4669]
theorem batch_93_08_ok : batch_93_08_values.all id = true := by decide

def batch_93_09_values : List Bool := [accepted_4670]
theorem batch_93_09_ok : batch_93_09_values.all id = true := by decide

def batch_93_10_values : List Bool := [accepted_4675]
theorem batch_93_10_ok : batch_93_10_values.all id = true := by decide

def batch_93_11_values : List Bool := [accepted_4676]
theorem batch_93_11_ok : batch_93_11_values.all id = true := by decide

def batch_93_12_values : List Bool := [accepted_4677]
theorem batch_93_12_ok : batch_93_12_values.all id = true := by decide

def batch_93_13_values : List Bool := [accepted_4678]
theorem batch_93_13_ok : batch_93_13_values.all id = true := by decide

def batch_93_14_values : List Bool := [accepted_4679]
theorem batch_93_14_ok : batch_93_14_values.all id = true := by decide

def batch_93_15_values : List Bool := [accepted_4681]
theorem batch_93_15_ok : batch_93_15_values.all id = true := by decide

def batch_93_16_values : List Bool := [accepted_4682]
theorem batch_93_16_ok : batch_93_16_values.all id = true := by decide

def batch_93_17_values : List Bool := [accepted_4683]
theorem batch_93_17_ok : batch_93_17_values.all id = true := by decide

def batch_93_18_values : List Bool := [accepted_4685]
theorem batch_93_18_ok : batch_93_18_values.all id = true := by decide

def batch_93_19_values : List Bool := [accepted_4687]
theorem batch_93_19_ok : batch_93_19_values.all id = true := by decide

def batch_93_20_values : List Bool := [accepted_4689]
theorem batch_93_20_ok : batch_93_20_values.all id = true := by decide

def batch_93_21_values : List Bool := [accepted_4690]
theorem batch_93_21_ok : batch_93_21_values.all id = true := by decide

def batch_93_22_values : List Bool := [accepted_4699]
theorem batch_93_22_ok : batch_93_22_values.all id = true := by decide

theorem leaf_4655_ok : checkAt 527 1000 box_4655 cert_4655 = true := by
  have h := List.all_eq_true.mp batch_93_00_ok accepted_4655 (by simp [batch_93_00_values])
  exact h
theorem leaf_4655_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4655.profileLo box_4655.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4655_ok
theorem branch_box_4655_nonnegative : ∀ j, 0 ≤ branch_box_4655.lower j ∧ 0 ≤ branch_box_4655.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4655, Box.profileLo, Box.profileHi, box_4655]
theorem leaf_4655_BranchSafe : CertificateConsequences.BranchSafe branch_box_4655 := by
  left; refine ⟨branch_box_4655_nonnegative, ?_⟩
  intro z hz; exact leaf_4655_sound hz

theorem leaf_4656_ok : checkAt 527 1000 box_4656 cert_4656 = true := by
  have h := List.all_eq_true.mp batch_93_01_ok accepted_4656 (by simp [batch_93_01_values])
  exact h
theorem leaf_4656_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4656.profileLo box_4656.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4656_ok
theorem branch_box_4656_nonnegative : ∀ j, 0 ≤ branch_box_4656.lower j ∧ 0 ≤ branch_box_4656.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4656, Box.profileLo, Box.profileHi, box_4656]
theorem leaf_4656_BranchSafe : CertificateConsequences.BranchSafe branch_box_4656 := by
  left; refine ⟨branch_box_4656_nonnegative, ?_⟩
  intro z hz; exact leaf_4656_sound hz

theorem leaf_4657_ok : checkAt 527 1000 box_4657 cert_4657 = true := by
  have h := List.all_eq_true.mp batch_93_02_ok accepted_4657 (by simp [batch_93_02_values])
  exact h
theorem leaf_4657_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4657.profileLo box_4657.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4657_ok
theorem branch_box_4657_nonnegative : ∀ j, 0 ≤ branch_box_4657.lower j ∧ 0 ≤ branch_box_4657.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4657, Box.profileLo, Box.profileHi, box_4657]
theorem leaf_4657_BranchSafe : CertificateConsequences.BranchSafe branch_box_4657 := by
  left; refine ⟨branch_box_4657_nonnegative, ?_⟩
  intro z hz; exact leaf_4657_sound hz

theorem leaf_4659_ok : checkAt 527 1000 box_4659 cert_4659 = true := by
  have h := List.all_eq_true.mp batch_93_03_ok accepted_4659 (by simp [batch_93_03_values])
  exact h
theorem leaf_4659_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4659.profileLo box_4659.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4659_ok
theorem branch_box_4659_nonnegative : ∀ j, 0 ≤ branch_box_4659.lower j ∧ 0 ≤ branch_box_4659.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4659, Box.profileLo, Box.profileHi, box_4659]
theorem leaf_4659_BranchSafe : CertificateConsequences.BranchSafe branch_box_4659 := by
  left; refine ⟨branch_box_4659_nonnegative, ?_⟩
  intro z hz; exact leaf_4659_sound hz

theorem leaf_4660_ok : checkAt 527 1000 box_4660 cert_4660 = true := by
  have h := List.all_eq_true.mp batch_93_04_ok accepted_4660 (by simp [batch_93_04_values])
  exact h
theorem leaf_4660_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4660.profileLo box_4660.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4660_ok
theorem branch_box_4660_nonnegative : ∀ j, 0 ≤ branch_box_4660.lower j ∧ 0 ≤ branch_box_4660.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4660, Box.profileLo, Box.profileHi, box_4660]
theorem leaf_4660_BranchSafe : CertificateConsequences.BranchSafe branch_box_4660 := by
  left; refine ⟨branch_box_4660_nonnegative, ?_⟩
  intro z hz; exact leaf_4660_sound hz

theorem leaf_4666_ok : checkAt 527 1000 box_4666 cert_4666 = true := by
  have h := List.all_eq_true.mp batch_93_05_ok accepted_4666 (by simp [batch_93_05_values])
  exact h
theorem leaf_4666_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4666.profileLo box_4666.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4666_ok
theorem branch_box_4666_nonnegative : ∀ j, 0 ≤ branch_box_4666.lower j ∧ 0 ≤ branch_box_4666.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4666, Box.profileLo, Box.profileHi, box_4666]
theorem leaf_4666_BranchSafe : CertificateConsequences.BranchSafe branch_box_4666 := by
  left; refine ⟨branch_box_4666_nonnegative, ?_⟩
  intro z hz; exact leaf_4666_sound hz

theorem leaf_4667_ok : checkAt 527 1000 box_4667 cert_4667 = true := by
  have h := List.all_eq_true.mp batch_93_06_ok accepted_4667 (by simp [batch_93_06_values])
  exact h
theorem leaf_4667_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4667.profileLo box_4667.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4667_ok
theorem branch_box_4667_nonnegative : ∀ j, 0 ≤ branch_box_4667.lower j ∧ 0 ≤ branch_box_4667.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4667, Box.profileLo, Box.profileHi, box_4667]
theorem leaf_4667_BranchSafe : CertificateConsequences.BranchSafe branch_box_4667 := by
  left; refine ⟨branch_box_4667_nonnegative, ?_⟩
  intro z hz; exact leaf_4667_sound hz

theorem leaf_4668_ok : checkAt 527 1000 box_4668 cert_4668 = true := by
  have h := List.all_eq_true.mp batch_93_07_ok accepted_4668 (by simp [batch_93_07_values])
  exact h
theorem leaf_4668_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4668.profileLo box_4668.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4668_ok
theorem branch_box_4668_nonnegative : ∀ j, 0 ≤ branch_box_4668.lower j ∧ 0 ≤ branch_box_4668.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4668, Box.profileLo, Box.profileHi, box_4668]
theorem leaf_4668_BranchSafe : CertificateConsequences.BranchSafe branch_box_4668 := by
  left; refine ⟨branch_box_4668_nonnegative, ?_⟩
  intro z hz; exact leaf_4668_sound hz

theorem leaf_4669_ok : checkAt 527 1000 box_4669 cert_4669 = true := by
  have h := List.all_eq_true.mp batch_93_08_ok accepted_4669 (by simp [batch_93_08_values])
  exact h
theorem leaf_4669_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4669.profileLo box_4669.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4669_ok
theorem branch_box_4669_nonnegative : ∀ j, 0 ≤ branch_box_4669.lower j ∧ 0 ≤ branch_box_4669.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4669, Box.profileLo, Box.profileHi, box_4669]
theorem leaf_4669_BranchSafe : CertificateConsequences.BranchSafe branch_box_4669 := by
  left; refine ⟨branch_box_4669_nonnegative, ?_⟩
  intro z hz; exact leaf_4669_sound hz

theorem leaf_4670_ok : checkAt 527 1000 box_4670 cert_4670 = true := by
  have h := List.all_eq_true.mp batch_93_09_ok accepted_4670 (by simp [batch_93_09_values])
  exact h
theorem leaf_4670_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4670.profileLo box_4670.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4670_ok
theorem branch_box_4670_nonnegative : ∀ j, 0 ≤ branch_box_4670.lower j ∧ 0 ≤ branch_box_4670.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4670, Box.profileLo, Box.profileHi, box_4670]
theorem leaf_4670_BranchSafe : CertificateConsequences.BranchSafe branch_box_4670 := by
  left; refine ⟨branch_box_4670_nonnegative, ?_⟩
  intro z hz; exact leaf_4670_sound hz

theorem leaf_4675_ok : checkAt 527 1000 box_4675 cert_4675 = true := by
  have h := List.all_eq_true.mp batch_93_10_ok accepted_4675 (by simp [batch_93_10_values])
  exact h
theorem leaf_4675_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4675.profileLo box_4675.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4675_ok
theorem branch_box_4675_nonnegative : ∀ j, 0 ≤ branch_box_4675.lower j ∧ 0 ≤ branch_box_4675.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4675, Box.profileLo, Box.profileHi, box_4675]
theorem leaf_4675_BranchSafe : CertificateConsequences.BranchSafe branch_box_4675 := by
  left; refine ⟨branch_box_4675_nonnegative, ?_⟩
  intro z hz; exact leaf_4675_sound hz

theorem leaf_4676_ok : checkAt 527 1000 box_4676 cert_4676 = true := by
  have h := List.all_eq_true.mp batch_93_11_ok accepted_4676 (by simp [batch_93_11_values])
  exact h
theorem leaf_4676_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4676.profileLo box_4676.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4676_ok
theorem branch_box_4676_nonnegative : ∀ j, 0 ≤ branch_box_4676.lower j ∧ 0 ≤ branch_box_4676.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4676, Box.profileLo, Box.profileHi, box_4676]
theorem leaf_4676_BranchSafe : CertificateConsequences.BranchSafe branch_box_4676 := by
  left; refine ⟨branch_box_4676_nonnegative, ?_⟩
  intro z hz; exact leaf_4676_sound hz

theorem leaf_4677_ok : checkAt 527 1000 box_4677 cert_4677 = true := by
  have h := List.all_eq_true.mp batch_93_12_ok accepted_4677 (by simp [batch_93_12_values])
  exact h
theorem leaf_4677_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4677.profileLo box_4677.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4677_ok
theorem branch_box_4677_nonnegative : ∀ j, 0 ≤ branch_box_4677.lower j ∧ 0 ≤ branch_box_4677.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4677, Box.profileLo, Box.profileHi, box_4677]
theorem leaf_4677_BranchSafe : CertificateConsequences.BranchSafe branch_box_4677 := by
  left; refine ⟨branch_box_4677_nonnegative, ?_⟩
  intro z hz; exact leaf_4677_sound hz

theorem leaf_4678_ok : checkAt 527 1000 box_4678 cert_4678 = true := by
  have h := List.all_eq_true.mp batch_93_13_ok accepted_4678 (by simp [batch_93_13_values])
  exact h
theorem leaf_4678_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4678.profileLo box_4678.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4678_ok
theorem branch_box_4678_nonnegative : ∀ j, 0 ≤ branch_box_4678.lower j ∧ 0 ≤ branch_box_4678.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4678, Box.profileLo, Box.profileHi, box_4678]
theorem leaf_4678_BranchSafe : CertificateConsequences.BranchSafe branch_box_4678 := by
  left; refine ⟨branch_box_4678_nonnegative, ?_⟩
  intro z hz; exact leaf_4678_sound hz

theorem leaf_4679_ok : checkAt 527 1000 box_4679 cert_4679 = true := by
  have h := List.all_eq_true.mp batch_93_14_ok accepted_4679 (by simp [batch_93_14_values])
  exact h
theorem leaf_4679_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4679.profileLo box_4679.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4679_ok
theorem branch_box_4679_nonnegative : ∀ j, 0 ≤ branch_box_4679.lower j ∧ 0 ≤ branch_box_4679.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4679, Box.profileLo, Box.profileHi, box_4679]
theorem leaf_4679_BranchSafe : CertificateConsequences.BranchSafe branch_box_4679 := by
  left; refine ⟨branch_box_4679_nonnegative, ?_⟩
  intro z hz; exact leaf_4679_sound hz

theorem leaf_4681_ok : checkAt 527 1000 box_4681 cert_4681 = true := by
  have h := List.all_eq_true.mp batch_93_15_ok accepted_4681 (by simp [batch_93_15_values])
  exact h
theorem leaf_4681_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4681.profileLo box_4681.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4681_ok
theorem branch_box_4681_nonnegative : ∀ j, 0 ≤ branch_box_4681.lower j ∧ 0 ≤ branch_box_4681.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4681, Box.profileLo, Box.profileHi, box_4681]
theorem leaf_4681_BranchSafe : CertificateConsequences.BranchSafe branch_box_4681 := by
  left; refine ⟨branch_box_4681_nonnegative, ?_⟩
  intro z hz; exact leaf_4681_sound hz

theorem leaf_4682_ok : checkAt 527 1000 box_4682 cert_4682 = true := by
  have h := List.all_eq_true.mp batch_93_16_ok accepted_4682 (by simp [batch_93_16_values])
  exact h
theorem leaf_4682_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4682.profileLo box_4682.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4682_ok
theorem branch_box_4682_nonnegative : ∀ j, 0 ≤ branch_box_4682.lower j ∧ 0 ≤ branch_box_4682.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4682, Box.profileLo, Box.profileHi, box_4682]
theorem leaf_4682_BranchSafe : CertificateConsequences.BranchSafe branch_box_4682 := by
  left; refine ⟨branch_box_4682_nonnegative, ?_⟩
  intro z hz; exact leaf_4682_sound hz

theorem leaf_4683_ok : checkAt 527 1000 box_4683 cert_4683 = true := by
  have h := List.all_eq_true.mp batch_93_17_ok accepted_4683 (by simp [batch_93_17_values])
  exact h
theorem leaf_4683_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4683.profileLo box_4683.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4683_ok
theorem branch_box_4683_nonnegative : ∀ j, 0 ≤ branch_box_4683.lower j ∧ 0 ≤ branch_box_4683.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4683, Box.profileLo, Box.profileHi, box_4683]
theorem leaf_4683_BranchSafe : CertificateConsequences.BranchSafe branch_box_4683 := by
  left; refine ⟨branch_box_4683_nonnegative, ?_⟩
  intro z hz; exact leaf_4683_sound hz

theorem leaf_4685_ok : checkAt 527 1000 box_4685 cert_4685 = true := by
  have h := List.all_eq_true.mp batch_93_18_ok accepted_4685 (by simp [batch_93_18_values])
  exact h
theorem leaf_4685_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4685.profileLo box_4685.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4685_ok
theorem branch_box_4685_nonnegative : ∀ j, 0 ≤ branch_box_4685.lower j ∧ 0 ≤ branch_box_4685.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4685, Box.profileLo, Box.profileHi, box_4685]
theorem leaf_4685_BranchSafe : CertificateConsequences.BranchSafe branch_box_4685 := by
  left; refine ⟨branch_box_4685_nonnegative, ?_⟩
  intro z hz; exact leaf_4685_sound hz

theorem leaf_4687_ok : checkAt 527 1000 box_4687 cert_4687 = true := by
  have h := List.all_eq_true.mp batch_93_19_ok accepted_4687 (by simp [batch_93_19_values])
  exact h
theorem leaf_4687_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4687.profileLo box_4687.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4687_ok
theorem branch_box_4687_nonnegative : ∀ j, 0 ≤ branch_box_4687.lower j ∧ 0 ≤ branch_box_4687.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4687, Box.profileLo, Box.profileHi, box_4687]
theorem leaf_4687_BranchSafe : CertificateConsequences.BranchSafe branch_box_4687 := by
  left; refine ⟨branch_box_4687_nonnegative, ?_⟩
  intro z hz; exact leaf_4687_sound hz

theorem leaf_4689_ok : checkAt 527 1000 box_4689 cert_4689 = true := by
  have h := List.all_eq_true.mp batch_93_20_ok accepted_4689 (by simp [batch_93_20_values])
  exact h
theorem leaf_4689_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4689.profileLo box_4689.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4689_ok
theorem branch_box_4689_nonnegative : ∀ j, 0 ≤ branch_box_4689.lower j ∧ 0 ≤ branch_box_4689.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4689, Box.profileLo, Box.profileHi, box_4689]
theorem leaf_4689_BranchSafe : CertificateConsequences.BranchSafe branch_box_4689 := by
  left; refine ⟨branch_box_4689_nonnegative, ?_⟩
  intro z hz; exact leaf_4689_sound hz

theorem leaf_4690_ok : checkAt 527 1000 box_4690 cert_4690 = true := by
  have h := List.all_eq_true.mp batch_93_21_ok accepted_4690 (by simp [batch_93_21_values])
  exact h
theorem leaf_4690_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4690.profileLo box_4690.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4690_ok
theorem branch_box_4690_nonnegative : ∀ j, 0 ≤ branch_box_4690.lower j ∧ 0 ≤ branch_box_4690.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4690, Box.profileLo, Box.profileHi, box_4690]
theorem leaf_4690_BranchSafe : CertificateConsequences.BranchSafe branch_box_4690 := by
  left; refine ⟨branch_box_4690_nonnegative, ?_⟩
  intro z hz; exact leaf_4690_sound hz

theorem leaf_4699_ok : checkAt 527 1000 box_4699 cert_4699 = true := by
  have h := List.all_eq_true.mp batch_93_22_ok accepted_4699 (by simp [batch_93_22_values])
  exact h
theorem leaf_4699_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4699.profileLo box_4699.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4699_ok
theorem branch_box_4699_nonnegative : ∀ j, 0 ≤ branch_box_4699.lower j ∧ 0 ≤ branch_box_4699.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4699, Box.profileLo, Box.profileHi, box_4699]
theorem leaf_4699_BranchSafe : CertificateConsequences.BranchSafe branch_box_4699 := by
  left; refine ⟨branch_box_4699_nonnegative, ?_⟩
  intro z hz; exact leaf_4699_sound hz

#print axioms batch_93_00_ok
#print axioms leaf_4655_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
