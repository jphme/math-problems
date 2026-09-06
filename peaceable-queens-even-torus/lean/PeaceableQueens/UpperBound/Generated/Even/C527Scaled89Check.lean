import PeaceableQueens.UpperBound.Generated.Even.C527Scaled89Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_89_00_values : List Bool := [accepted_4451]
theorem batch_89_00_ok : batch_89_00_values.all id = true := by decide

def batch_89_01_values : List Bool := [accepted_4452]
theorem batch_89_01_ok : batch_89_01_values.all id = true := by decide

def batch_89_02_values : List Bool := [accepted_4456]
theorem batch_89_02_ok : batch_89_02_values.all id = true := by decide

def batch_89_03_values : List Bool := [accepted_4457]
theorem batch_89_03_ok : batch_89_03_values.all id = true := by decide

def batch_89_04_values : List Bool := [accepted_4458]
theorem batch_89_04_ok : batch_89_04_values.all id = true := by decide

def batch_89_05_values : List Bool := [accepted_4460]
theorem batch_89_05_ok : batch_89_05_values.all id = true := by decide

def batch_89_06_values : List Bool := [accepted_4461]
theorem batch_89_06_ok : batch_89_06_values.all id = true := by decide

def batch_89_07_values : List Bool := [accepted_4463]
theorem batch_89_07_ok : batch_89_07_values.all id = true := by decide

def batch_89_08_values : List Bool := [accepted_4464]
theorem batch_89_08_ok : batch_89_08_values.all id = true := by decide

def batch_89_09_values : List Bool := [accepted_4471]
theorem batch_89_09_ok : batch_89_09_values.all id = true := by decide

def batch_89_10_values : List Bool := [accepted_4472]
theorem batch_89_10_ok : batch_89_10_values.all id = true := by decide

def batch_89_11_values : List Bool := [accepted_4473]
theorem batch_89_11_ok : batch_89_11_values.all id = true := by decide

def batch_89_12_values : List Bool := [accepted_4475]
theorem batch_89_12_ok : batch_89_12_values.all id = true := by decide

def batch_89_13_values : List Bool := [accepted_4476]
theorem batch_89_13_ok : batch_89_13_values.all id = true := by decide

def batch_89_14_values : List Bool := [accepted_4478]
theorem batch_89_14_ok : batch_89_14_values.all id = true := by decide

def batch_89_15_values : List Bool := [accepted_4479]
theorem batch_89_15_ok : batch_89_15_values.all id = true := by decide

def batch_89_16_values : List Bool := [accepted_4480]
theorem batch_89_16_ok : batch_89_16_values.all id = true := by decide

def batch_89_17_values : List Bool := [accepted_4487]
theorem batch_89_17_ok : batch_89_17_values.all id = true := by decide

def batch_89_18_values : List Bool := [accepted_4490]
theorem batch_89_18_ok : batch_89_18_values.all id = true := by decide

def batch_89_19_values : List Bool := [accepted_4491]
theorem batch_89_19_ok : batch_89_19_values.all id = true := by decide

def batch_89_20_values : List Bool := [accepted_4495]
theorem batch_89_20_ok : batch_89_20_values.all id = true := by decide

def batch_89_21_values : List Bool := [accepted_4496]
theorem batch_89_21_ok : batch_89_21_values.all id = true := by decide

def batch_89_22_values : List Bool := [accepted_4497]
theorem batch_89_22_ok : batch_89_22_values.all id = true := by decide

def batch_89_23_values : List Bool := [accepted_4498]
theorem batch_89_23_ok : batch_89_23_values.all id = true := by decide

theorem leaf_4451_ok : checkAt 527 1000 box_4451 cert_4451 = true := by
  have h := List.all_eq_true.mp batch_89_00_ok accepted_4451 (by simp [batch_89_00_values])
  exact h
theorem leaf_4451_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4451.profileLo box_4451.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4451_ok
theorem branch_box_4451_nonnegative : ∀ j, 0 ≤ branch_box_4451.lower j ∧ 0 ≤ branch_box_4451.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4451, Box.profileLo, Box.profileHi, box_4451]
theorem leaf_4451_BranchSafe : CertificateConsequences.BranchSafe branch_box_4451 := by
  left; refine ⟨branch_box_4451_nonnegative, ?_⟩
  intro z hz; exact leaf_4451_sound hz

theorem leaf_4452_ok : checkAt 527 1000 box_4452 cert_4452 = true := by
  have h := List.all_eq_true.mp batch_89_01_ok accepted_4452 (by simp [batch_89_01_values])
  exact h
theorem leaf_4452_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4452.profileLo box_4452.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4452_ok
theorem branch_box_4452_nonnegative : ∀ j, 0 ≤ branch_box_4452.lower j ∧ 0 ≤ branch_box_4452.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4452, Box.profileLo, Box.profileHi, box_4452]
theorem leaf_4452_BranchSafe : CertificateConsequences.BranchSafe branch_box_4452 := by
  left; refine ⟨branch_box_4452_nonnegative, ?_⟩
  intro z hz; exact leaf_4452_sound hz

theorem leaf_4456_ok : checkAt 527 1000 box_4456 cert_4456 = true := by
  have h := List.all_eq_true.mp batch_89_02_ok accepted_4456 (by simp [batch_89_02_values])
  exact h
theorem leaf_4456_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4456.profileLo box_4456.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4456_ok
theorem branch_box_4456_nonnegative : ∀ j, 0 ≤ branch_box_4456.lower j ∧ 0 ≤ branch_box_4456.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4456, Box.profileLo, Box.profileHi, box_4456]
theorem leaf_4456_BranchSafe : CertificateConsequences.BranchSafe branch_box_4456 := by
  left; refine ⟨branch_box_4456_nonnegative, ?_⟩
  intro z hz; exact leaf_4456_sound hz

theorem leaf_4457_ok : checkAt 527 1000 box_4457 cert_4457 = true := by
  have h := List.all_eq_true.mp batch_89_03_ok accepted_4457 (by simp [batch_89_03_values])
  exact h
theorem leaf_4457_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4457.profileLo box_4457.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4457_ok
theorem branch_box_4457_nonnegative : ∀ j, 0 ≤ branch_box_4457.lower j ∧ 0 ≤ branch_box_4457.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4457, Box.profileLo, Box.profileHi, box_4457]
theorem leaf_4457_BranchSafe : CertificateConsequences.BranchSafe branch_box_4457 := by
  left; refine ⟨branch_box_4457_nonnegative, ?_⟩
  intro z hz; exact leaf_4457_sound hz

theorem leaf_4458_ok : checkAt 527 1000 box_4458 cert_4458 = true := by
  have h := List.all_eq_true.mp batch_89_04_ok accepted_4458 (by simp [batch_89_04_values])
  exact h
theorem leaf_4458_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4458.profileLo box_4458.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4458_ok
theorem branch_box_4458_nonnegative : ∀ j, 0 ≤ branch_box_4458.lower j ∧ 0 ≤ branch_box_4458.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4458, Box.profileLo, Box.profileHi, box_4458]
theorem leaf_4458_BranchSafe : CertificateConsequences.BranchSafe branch_box_4458 := by
  left; refine ⟨branch_box_4458_nonnegative, ?_⟩
  intro z hz; exact leaf_4458_sound hz

theorem leaf_4460_ok : checkAt 527 1000 box_4460 cert_4460 = true := by
  have h := List.all_eq_true.mp batch_89_05_ok accepted_4460 (by simp [batch_89_05_values])
  exact h
theorem leaf_4460_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4460.profileLo box_4460.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4460_ok
theorem branch_box_4460_nonnegative : ∀ j, 0 ≤ branch_box_4460.lower j ∧ 0 ≤ branch_box_4460.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4460, Box.profileLo, Box.profileHi, box_4460]
theorem leaf_4460_BranchSafe : CertificateConsequences.BranchSafe branch_box_4460 := by
  left; refine ⟨branch_box_4460_nonnegative, ?_⟩
  intro z hz; exact leaf_4460_sound hz

theorem leaf_4461_ok : checkAt 527 1000 box_4461 cert_4461 = true := by
  have h := List.all_eq_true.mp batch_89_06_ok accepted_4461 (by simp [batch_89_06_values])
  exact h
theorem leaf_4461_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4461.profileLo box_4461.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4461_ok
theorem branch_box_4461_nonnegative : ∀ j, 0 ≤ branch_box_4461.lower j ∧ 0 ≤ branch_box_4461.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4461, Box.profileLo, Box.profileHi, box_4461]
theorem leaf_4461_BranchSafe : CertificateConsequences.BranchSafe branch_box_4461 := by
  left; refine ⟨branch_box_4461_nonnegative, ?_⟩
  intro z hz; exact leaf_4461_sound hz

theorem leaf_4463_ok : checkAt 527 1000 box_4463 cert_4463 = true := by
  have h := List.all_eq_true.mp batch_89_07_ok accepted_4463 (by simp [batch_89_07_values])
  exact h
theorem leaf_4463_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4463.profileLo box_4463.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4463_ok
theorem branch_box_4463_nonnegative : ∀ j, 0 ≤ branch_box_4463.lower j ∧ 0 ≤ branch_box_4463.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4463, Box.profileLo, Box.profileHi, box_4463]
theorem leaf_4463_BranchSafe : CertificateConsequences.BranchSafe branch_box_4463 := by
  left; refine ⟨branch_box_4463_nonnegative, ?_⟩
  intro z hz; exact leaf_4463_sound hz

theorem leaf_4464_ok : checkAt 527 1000 box_4464 cert_4464 = true := by
  have h := List.all_eq_true.mp batch_89_08_ok accepted_4464 (by simp [batch_89_08_values])
  exact h
theorem leaf_4464_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4464.profileLo box_4464.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4464_ok
theorem branch_box_4464_nonnegative : ∀ j, 0 ≤ branch_box_4464.lower j ∧ 0 ≤ branch_box_4464.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4464, Box.profileLo, Box.profileHi, box_4464]
theorem leaf_4464_BranchSafe : CertificateConsequences.BranchSafe branch_box_4464 := by
  left; refine ⟨branch_box_4464_nonnegative, ?_⟩
  intro z hz; exact leaf_4464_sound hz

theorem leaf_4471_ok : checkAt 527 1000 box_4471 cert_4471 = true := by
  have h := List.all_eq_true.mp batch_89_09_ok accepted_4471 (by simp [batch_89_09_values])
  exact h
theorem leaf_4471_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4471.profileLo box_4471.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4471_ok
theorem branch_box_4471_nonnegative : ∀ j, 0 ≤ branch_box_4471.lower j ∧ 0 ≤ branch_box_4471.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4471, Box.profileLo, Box.profileHi, box_4471]
theorem leaf_4471_BranchSafe : CertificateConsequences.BranchSafe branch_box_4471 := by
  left; refine ⟨branch_box_4471_nonnegative, ?_⟩
  intro z hz; exact leaf_4471_sound hz

theorem leaf_4472_ok : checkAt 527 1000 box_4472 cert_4472 = true := by
  have h := List.all_eq_true.mp batch_89_10_ok accepted_4472 (by simp [batch_89_10_values])
  exact h
theorem leaf_4472_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4472.profileLo box_4472.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4472_ok
theorem branch_box_4472_nonnegative : ∀ j, 0 ≤ branch_box_4472.lower j ∧ 0 ≤ branch_box_4472.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4472, Box.profileLo, Box.profileHi, box_4472]
theorem leaf_4472_BranchSafe : CertificateConsequences.BranchSafe branch_box_4472 := by
  left; refine ⟨branch_box_4472_nonnegative, ?_⟩
  intro z hz; exact leaf_4472_sound hz

theorem leaf_4473_ok : checkAt 527 1000 box_4473 cert_4473 = true := by
  have h := List.all_eq_true.mp batch_89_11_ok accepted_4473 (by simp [batch_89_11_values])
  exact h
theorem leaf_4473_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4473.profileLo box_4473.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4473_ok
theorem branch_box_4473_nonnegative : ∀ j, 0 ≤ branch_box_4473.lower j ∧ 0 ≤ branch_box_4473.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4473, Box.profileLo, Box.profileHi, box_4473]
theorem leaf_4473_BranchSafe : CertificateConsequences.BranchSafe branch_box_4473 := by
  left; refine ⟨branch_box_4473_nonnegative, ?_⟩
  intro z hz; exact leaf_4473_sound hz

theorem leaf_4475_ok : checkAt 527 1000 box_4475 cert_4475 = true := by
  have h := List.all_eq_true.mp batch_89_12_ok accepted_4475 (by simp [batch_89_12_values])
  exact h
theorem leaf_4475_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4475.profileLo box_4475.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4475_ok
theorem branch_box_4475_nonnegative : ∀ j, 0 ≤ branch_box_4475.lower j ∧ 0 ≤ branch_box_4475.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4475, Box.profileLo, Box.profileHi, box_4475]
theorem leaf_4475_BranchSafe : CertificateConsequences.BranchSafe branch_box_4475 := by
  left; refine ⟨branch_box_4475_nonnegative, ?_⟩
  intro z hz; exact leaf_4475_sound hz

theorem leaf_4476_ok : checkAt 527 1000 box_4476 cert_4476 = true := by
  have h := List.all_eq_true.mp batch_89_13_ok accepted_4476 (by simp [batch_89_13_values])
  exact h
theorem leaf_4476_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4476.profileLo box_4476.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4476_ok
theorem branch_box_4476_nonnegative : ∀ j, 0 ≤ branch_box_4476.lower j ∧ 0 ≤ branch_box_4476.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4476, Box.profileLo, Box.profileHi, box_4476]
theorem leaf_4476_BranchSafe : CertificateConsequences.BranchSafe branch_box_4476 := by
  left; refine ⟨branch_box_4476_nonnegative, ?_⟩
  intro z hz; exact leaf_4476_sound hz

theorem leaf_4478_ok : checkAt 527 1000 box_4478 cert_4478 = true := by
  have h := List.all_eq_true.mp batch_89_14_ok accepted_4478 (by simp [batch_89_14_values])
  exact h
theorem leaf_4478_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4478.profileLo box_4478.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4478_ok
theorem branch_box_4478_nonnegative : ∀ j, 0 ≤ branch_box_4478.lower j ∧ 0 ≤ branch_box_4478.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4478, Box.profileLo, Box.profileHi, box_4478]
theorem leaf_4478_BranchSafe : CertificateConsequences.BranchSafe branch_box_4478 := by
  left; refine ⟨branch_box_4478_nonnegative, ?_⟩
  intro z hz; exact leaf_4478_sound hz

theorem leaf_4479_ok : checkAt 527 1000 box_4479 cert_4479 = true := by
  have h := List.all_eq_true.mp batch_89_15_ok accepted_4479 (by simp [batch_89_15_values])
  exact h
theorem leaf_4479_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4479.profileLo box_4479.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4479_ok
theorem branch_box_4479_nonnegative : ∀ j, 0 ≤ branch_box_4479.lower j ∧ 0 ≤ branch_box_4479.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4479, Box.profileLo, Box.profileHi, box_4479]
theorem leaf_4479_BranchSafe : CertificateConsequences.BranchSafe branch_box_4479 := by
  left; refine ⟨branch_box_4479_nonnegative, ?_⟩
  intro z hz; exact leaf_4479_sound hz

theorem leaf_4480_ok : checkAt 527 1000 box_4480 cert_4480 = true := by
  have h := List.all_eq_true.mp batch_89_16_ok accepted_4480 (by simp [batch_89_16_values])
  exact h
theorem leaf_4480_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4480.profileLo box_4480.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4480_ok
theorem branch_box_4480_nonnegative : ∀ j, 0 ≤ branch_box_4480.lower j ∧ 0 ≤ branch_box_4480.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4480, Box.profileLo, Box.profileHi, box_4480]
theorem leaf_4480_BranchSafe : CertificateConsequences.BranchSafe branch_box_4480 := by
  left; refine ⟨branch_box_4480_nonnegative, ?_⟩
  intro z hz; exact leaf_4480_sound hz

theorem leaf_4487_ok : checkAt 527 1000 box_4487 cert_4487 = true := by
  have h := List.all_eq_true.mp batch_89_17_ok accepted_4487 (by simp [batch_89_17_values])
  exact h
theorem leaf_4487_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4487.profileLo box_4487.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4487_ok
theorem branch_box_4487_nonnegative : ∀ j, 0 ≤ branch_box_4487.lower j ∧ 0 ≤ branch_box_4487.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4487, Box.profileLo, Box.profileHi, box_4487]
theorem leaf_4487_BranchSafe : CertificateConsequences.BranchSafe branch_box_4487 := by
  left; refine ⟨branch_box_4487_nonnegative, ?_⟩
  intro z hz; exact leaf_4487_sound hz

theorem leaf_4490_ok : checkAt 527 1000 box_4490 cert_4490 = true := by
  have h := List.all_eq_true.mp batch_89_18_ok accepted_4490 (by simp [batch_89_18_values])
  exact h
theorem leaf_4490_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4490.profileLo box_4490.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4490_ok
theorem branch_box_4490_nonnegative : ∀ j, 0 ≤ branch_box_4490.lower j ∧ 0 ≤ branch_box_4490.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4490, Box.profileLo, Box.profileHi, box_4490]
theorem leaf_4490_BranchSafe : CertificateConsequences.BranchSafe branch_box_4490 := by
  left; refine ⟨branch_box_4490_nonnegative, ?_⟩
  intro z hz; exact leaf_4490_sound hz

theorem leaf_4491_ok : checkAt 527 1000 box_4491 cert_4491 = true := by
  have h := List.all_eq_true.mp batch_89_19_ok accepted_4491 (by simp [batch_89_19_values])
  exact h
theorem leaf_4491_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4491.profileLo box_4491.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4491_ok
theorem branch_box_4491_nonnegative : ∀ j, 0 ≤ branch_box_4491.lower j ∧ 0 ≤ branch_box_4491.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4491, Box.profileLo, Box.profileHi, box_4491]
theorem leaf_4491_BranchSafe : CertificateConsequences.BranchSafe branch_box_4491 := by
  left; refine ⟨branch_box_4491_nonnegative, ?_⟩
  intro z hz; exact leaf_4491_sound hz

theorem leaf_4495_ok : checkAt 527 1000 box_4495 cert_4495 = true := by
  have h := List.all_eq_true.mp batch_89_20_ok accepted_4495 (by simp [batch_89_20_values])
  exact h
theorem leaf_4495_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4495.profileLo box_4495.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4495_ok
theorem branch_box_4495_nonnegative : ∀ j, 0 ≤ branch_box_4495.lower j ∧ 0 ≤ branch_box_4495.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4495, Box.profileLo, Box.profileHi, box_4495]
theorem leaf_4495_BranchSafe : CertificateConsequences.BranchSafe branch_box_4495 := by
  left; refine ⟨branch_box_4495_nonnegative, ?_⟩
  intro z hz; exact leaf_4495_sound hz

theorem leaf_4496_ok : checkAt 527 1000 box_4496 cert_4496 = true := by
  have h := List.all_eq_true.mp batch_89_21_ok accepted_4496 (by simp [batch_89_21_values])
  exact h
theorem leaf_4496_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4496.profileLo box_4496.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4496_ok
theorem branch_box_4496_nonnegative : ∀ j, 0 ≤ branch_box_4496.lower j ∧ 0 ≤ branch_box_4496.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4496, Box.profileLo, Box.profileHi, box_4496]
theorem leaf_4496_BranchSafe : CertificateConsequences.BranchSafe branch_box_4496 := by
  left; refine ⟨branch_box_4496_nonnegative, ?_⟩
  intro z hz; exact leaf_4496_sound hz

theorem leaf_4497_ok : checkAt 527 1000 box_4497 cert_4497 = true := by
  have h := List.all_eq_true.mp batch_89_22_ok accepted_4497 (by simp [batch_89_22_values])
  exact h
theorem leaf_4497_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4497.profileLo box_4497.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4497_ok
theorem branch_box_4497_nonnegative : ∀ j, 0 ≤ branch_box_4497.lower j ∧ 0 ≤ branch_box_4497.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4497, Box.profileLo, Box.profileHi, box_4497]
theorem leaf_4497_BranchSafe : CertificateConsequences.BranchSafe branch_box_4497 := by
  left; refine ⟨branch_box_4497_nonnegative, ?_⟩
  intro z hz; exact leaf_4497_sound hz

theorem leaf_4498_ok : checkAt 527 1000 box_4498 cert_4498 = true := by
  have h := List.all_eq_true.mp batch_89_23_ok accepted_4498 (by simp [batch_89_23_values])
  exact h
theorem leaf_4498_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4498.profileLo box_4498.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4498_ok
theorem branch_box_4498_nonnegative : ∀ j, 0 ≤ branch_box_4498.lower j ∧ 0 ≤ branch_box_4498.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4498, Box.profileLo, Box.profileHi, box_4498]
theorem leaf_4498_BranchSafe : CertificateConsequences.BranchSafe branch_box_4498 := by
  left; refine ⟨branch_box_4498_nonnegative, ?_⟩
  intro z hz; exact leaf_4498_sound hz

#print axioms batch_89_00_ok
#print axioms leaf_4451_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
