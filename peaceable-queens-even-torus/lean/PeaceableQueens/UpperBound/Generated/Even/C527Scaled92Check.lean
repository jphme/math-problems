import PeaceableQueens.UpperBound.Generated.Even.C527Scaled92Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_92_00_values : List Bool := [accepted_4600]
theorem batch_92_00_ok : batch_92_00_values.all id = true := by decide

def batch_92_01_values : List Bool := [accepted_4601]
theorem batch_92_01_ok : batch_92_01_values.all id = true := by decide

def batch_92_02_values : List Bool := [accepted_4603]
theorem batch_92_02_ok : batch_92_02_values.all id = true := by decide

def batch_92_03_values : List Bool := [accepted_4604]
theorem batch_92_03_ok : batch_92_03_values.all id = true := by decide

def batch_92_04_values : List Bool := [accepted_4606]
theorem batch_92_04_ok : batch_92_04_values.all id = true := by decide

def batch_92_05_values : List Bool := [accepted_4607]
theorem batch_92_05_ok : batch_92_05_values.all id = true := by decide

def batch_92_06_values : List Bool := [accepted_4609]
theorem batch_92_06_ok : batch_92_06_values.all id = true := by decide

def batch_92_07_values : List Bool := [accepted_4610]
theorem batch_92_07_ok : batch_92_07_values.all id = true := by decide

def batch_92_08_values : List Bool := [accepted_4615]
theorem batch_92_08_ok : batch_92_08_values.all id = true := by decide

def batch_92_09_values : List Bool := [accepted_4616]
theorem batch_92_09_ok : batch_92_09_values.all id = true := by decide

def batch_92_10_values : List Bool := [accepted_4618]
theorem batch_92_10_ok : batch_92_10_values.all id = true := by decide

def batch_92_11_values : List Bool := [accepted_4619]
theorem batch_92_11_ok : batch_92_11_values.all id = true := by decide

def batch_92_12_values : List Bool := [accepted_4620]
theorem batch_92_12_ok : batch_92_12_values.all id = true := by decide

def batch_92_13_values : List Bool := [accepted_4623]
theorem batch_92_13_ok : batch_92_13_values.all id = true := by decide

def batch_92_14_values : List Bool := [accepted_4624]
theorem batch_92_14_ok : batch_92_14_values.all id = true := by decide

def batch_92_15_values : List Bool := [accepted_4627]
theorem batch_92_15_ok : batch_92_15_values.all id = true := by decide

def batch_92_16_values : List Bool := [accepted_4629]
theorem batch_92_16_ok : batch_92_16_values.all id = true := by decide

def batch_92_17_values : List Bool := [accepted_4630]
theorem batch_92_17_ok : batch_92_17_values.all id = true := by decide

def batch_92_18_values : List Bool := [accepted_4631]
theorem batch_92_18_ok : batch_92_18_values.all id = true := by decide

def batch_92_19_values : List Bool := [accepted_4632]
theorem batch_92_19_ok : batch_92_19_values.all id = true := by decide

def batch_92_20_values : List Bool := [accepted_4638]
theorem batch_92_20_ok : batch_92_20_values.all id = true := by decide

def batch_92_21_values : List Bool := [accepted_4639]
theorem batch_92_21_ok : batch_92_21_values.all id = true := by decide

def batch_92_22_values : List Bool := [accepted_4640]
theorem batch_92_22_ok : batch_92_22_values.all id = true := by decide

def batch_92_23_values : List Bool := [accepted_4642]
theorem batch_92_23_ok : batch_92_23_values.all id = true := by decide

def batch_92_24_values : List Bool := [accepted_4643]
theorem batch_92_24_ok : batch_92_24_values.all id = true := by decide

def batch_92_25_values : List Bool := [accepted_4645]
theorem batch_92_25_ok : batch_92_25_values.all id = true := by decide

def batch_92_26_values : List Bool := [accepted_4646]
theorem batch_92_26_ok : batch_92_26_values.all id = true := by decide

def batch_92_27_values : List Bool := [accepted_4647]
theorem batch_92_27_ok : batch_92_27_values.all id = true := by decide

def batch_92_28_values : List Bool := [accepted_4648]
theorem batch_92_28_ok : batch_92_28_values.all id = true := by decide

theorem leaf_4600_ok : checkAt 527 1000 box_4600 cert_4600 = true := by
  have h := List.all_eq_true.mp batch_92_00_ok accepted_4600 (by simp [batch_92_00_values])
  exact h
theorem leaf_4600_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4600.profileLo box_4600.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4600_ok
theorem branch_box_4600_nonnegative : ∀ j, 0 ≤ branch_box_4600.lower j ∧ 0 ≤ branch_box_4600.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4600, Box.profileLo, Box.profileHi, box_4600]
theorem leaf_4600_BranchSafe : CertificateConsequences.BranchSafe branch_box_4600 := by
  left; refine ⟨branch_box_4600_nonnegative, ?_⟩
  intro z hz; exact leaf_4600_sound hz

theorem leaf_4601_ok : checkAt 527 1000 box_4601 cert_4601 = true := by
  have h := List.all_eq_true.mp batch_92_01_ok accepted_4601 (by simp [batch_92_01_values])
  exact h
theorem leaf_4601_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4601.profileLo box_4601.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4601_ok
theorem branch_box_4601_nonnegative : ∀ j, 0 ≤ branch_box_4601.lower j ∧ 0 ≤ branch_box_4601.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4601, Box.profileLo, Box.profileHi, box_4601]
theorem leaf_4601_BranchSafe : CertificateConsequences.BranchSafe branch_box_4601 := by
  left; refine ⟨branch_box_4601_nonnegative, ?_⟩
  intro z hz; exact leaf_4601_sound hz

theorem leaf_4603_ok : checkAt 527 1000 box_4603 cert_4603 = true := by
  have h := List.all_eq_true.mp batch_92_02_ok accepted_4603 (by simp [batch_92_02_values])
  exact h
theorem leaf_4603_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4603.profileLo box_4603.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4603_ok
theorem branch_box_4603_nonnegative : ∀ j, 0 ≤ branch_box_4603.lower j ∧ 0 ≤ branch_box_4603.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4603, Box.profileLo, Box.profileHi, box_4603]
theorem leaf_4603_BranchSafe : CertificateConsequences.BranchSafe branch_box_4603 := by
  left; refine ⟨branch_box_4603_nonnegative, ?_⟩
  intro z hz; exact leaf_4603_sound hz

theorem leaf_4604_ok : checkAt 527 1000 box_4604 cert_4604 = true := by
  have h := List.all_eq_true.mp batch_92_03_ok accepted_4604 (by simp [batch_92_03_values])
  exact h
theorem leaf_4604_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4604.profileLo box_4604.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4604_ok
theorem branch_box_4604_nonnegative : ∀ j, 0 ≤ branch_box_4604.lower j ∧ 0 ≤ branch_box_4604.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4604, Box.profileLo, Box.profileHi, box_4604]
theorem leaf_4604_BranchSafe : CertificateConsequences.BranchSafe branch_box_4604 := by
  left; refine ⟨branch_box_4604_nonnegative, ?_⟩
  intro z hz; exact leaf_4604_sound hz

theorem leaf_4606_ok : checkAt 527 1000 box_4606 cert_4606 = true := by
  have h := List.all_eq_true.mp batch_92_04_ok accepted_4606 (by simp [batch_92_04_values])
  exact h
theorem leaf_4606_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4606.profileLo box_4606.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4606_ok
theorem branch_box_4606_nonnegative : ∀ j, 0 ≤ branch_box_4606.lower j ∧ 0 ≤ branch_box_4606.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4606, Box.profileLo, Box.profileHi, box_4606]
theorem leaf_4606_BranchSafe : CertificateConsequences.BranchSafe branch_box_4606 := by
  left; refine ⟨branch_box_4606_nonnegative, ?_⟩
  intro z hz; exact leaf_4606_sound hz

theorem leaf_4607_ok : checkAt 527 1000 box_4607 cert_4607 = true := by
  have h := List.all_eq_true.mp batch_92_05_ok accepted_4607 (by simp [batch_92_05_values])
  exact h
theorem leaf_4607_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4607.profileLo box_4607.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4607_ok
theorem branch_box_4607_nonnegative : ∀ j, 0 ≤ branch_box_4607.lower j ∧ 0 ≤ branch_box_4607.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4607, Box.profileLo, Box.profileHi, box_4607]
theorem leaf_4607_BranchSafe : CertificateConsequences.BranchSafe branch_box_4607 := by
  left; refine ⟨branch_box_4607_nonnegative, ?_⟩
  intro z hz; exact leaf_4607_sound hz

theorem leaf_4609_ok : checkAt 527 1000 box_4609 cert_4609 = true := by
  have h := List.all_eq_true.mp batch_92_06_ok accepted_4609 (by simp [batch_92_06_values])
  exact h
theorem leaf_4609_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4609.profileLo box_4609.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4609_ok
theorem branch_box_4609_nonnegative : ∀ j, 0 ≤ branch_box_4609.lower j ∧ 0 ≤ branch_box_4609.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4609, Box.profileLo, Box.profileHi, box_4609]
theorem leaf_4609_BranchSafe : CertificateConsequences.BranchSafe branch_box_4609 := by
  left; refine ⟨branch_box_4609_nonnegative, ?_⟩
  intro z hz; exact leaf_4609_sound hz

theorem leaf_4610_ok : checkAt 527 1000 box_4610 cert_4610 = true := by
  have h := List.all_eq_true.mp batch_92_07_ok accepted_4610 (by simp [batch_92_07_values])
  exact h
theorem leaf_4610_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4610.profileLo box_4610.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4610_ok
theorem branch_box_4610_nonnegative : ∀ j, 0 ≤ branch_box_4610.lower j ∧ 0 ≤ branch_box_4610.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4610, Box.profileLo, Box.profileHi, box_4610]
theorem leaf_4610_BranchSafe : CertificateConsequences.BranchSafe branch_box_4610 := by
  left; refine ⟨branch_box_4610_nonnegative, ?_⟩
  intro z hz; exact leaf_4610_sound hz

theorem leaf_4615_ok : checkAt 527 1000 box_4615 cert_4615 = true := by
  have h := List.all_eq_true.mp batch_92_08_ok accepted_4615 (by simp [batch_92_08_values])
  exact h
theorem leaf_4615_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4615.profileLo box_4615.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4615_ok
theorem branch_box_4615_nonnegative : ∀ j, 0 ≤ branch_box_4615.lower j ∧ 0 ≤ branch_box_4615.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4615, Box.profileLo, Box.profileHi, box_4615]
theorem leaf_4615_BranchSafe : CertificateConsequences.BranchSafe branch_box_4615 := by
  left; refine ⟨branch_box_4615_nonnegative, ?_⟩
  intro z hz; exact leaf_4615_sound hz

theorem leaf_4616_ok : checkAt 527 1000 box_4616 cert_4616 = true := by
  have h := List.all_eq_true.mp batch_92_09_ok accepted_4616 (by simp [batch_92_09_values])
  exact h
theorem leaf_4616_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4616.profileLo box_4616.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4616_ok
theorem branch_box_4616_nonnegative : ∀ j, 0 ≤ branch_box_4616.lower j ∧ 0 ≤ branch_box_4616.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4616, Box.profileLo, Box.profileHi, box_4616]
theorem leaf_4616_BranchSafe : CertificateConsequences.BranchSafe branch_box_4616 := by
  left; refine ⟨branch_box_4616_nonnegative, ?_⟩
  intro z hz; exact leaf_4616_sound hz

theorem leaf_4618_ok : checkAt 527 1000 box_4618 cert_4618 = true := by
  have h := List.all_eq_true.mp batch_92_10_ok accepted_4618 (by simp [batch_92_10_values])
  exact h
theorem leaf_4618_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4618.profileLo box_4618.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4618_ok
theorem branch_box_4618_nonnegative : ∀ j, 0 ≤ branch_box_4618.lower j ∧ 0 ≤ branch_box_4618.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4618, Box.profileLo, Box.profileHi, box_4618]
theorem leaf_4618_BranchSafe : CertificateConsequences.BranchSafe branch_box_4618 := by
  left; refine ⟨branch_box_4618_nonnegative, ?_⟩
  intro z hz; exact leaf_4618_sound hz

theorem leaf_4619_ok : checkAt 527 1000 box_4619 cert_4619 = true := by
  have h := List.all_eq_true.mp batch_92_11_ok accepted_4619 (by simp [batch_92_11_values])
  exact h
theorem leaf_4619_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4619.profileLo box_4619.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4619_ok
theorem branch_box_4619_nonnegative : ∀ j, 0 ≤ branch_box_4619.lower j ∧ 0 ≤ branch_box_4619.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4619, Box.profileLo, Box.profileHi, box_4619]
theorem leaf_4619_BranchSafe : CertificateConsequences.BranchSafe branch_box_4619 := by
  left; refine ⟨branch_box_4619_nonnegative, ?_⟩
  intro z hz; exact leaf_4619_sound hz

theorem leaf_4620_ok : checkAt 527 1000 box_4620 cert_4620 = true := by
  have h := List.all_eq_true.mp batch_92_12_ok accepted_4620 (by simp [batch_92_12_values])
  exact h
theorem leaf_4620_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4620.profileLo box_4620.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4620_ok
theorem branch_box_4620_nonnegative : ∀ j, 0 ≤ branch_box_4620.lower j ∧ 0 ≤ branch_box_4620.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4620, Box.profileLo, Box.profileHi, box_4620]
theorem leaf_4620_BranchSafe : CertificateConsequences.BranchSafe branch_box_4620 := by
  left; refine ⟨branch_box_4620_nonnegative, ?_⟩
  intro z hz; exact leaf_4620_sound hz

theorem leaf_4623_ok : checkAt 527 1000 box_4623 cert_4623 = true := by
  have h := List.all_eq_true.mp batch_92_13_ok accepted_4623 (by simp [batch_92_13_values])
  exact h
theorem leaf_4623_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4623.profileLo box_4623.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4623_ok
theorem branch_box_4623_nonnegative : ∀ j, 0 ≤ branch_box_4623.lower j ∧ 0 ≤ branch_box_4623.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4623, Box.profileLo, Box.profileHi, box_4623]
theorem leaf_4623_BranchSafe : CertificateConsequences.BranchSafe branch_box_4623 := by
  left; refine ⟨branch_box_4623_nonnegative, ?_⟩
  intro z hz; exact leaf_4623_sound hz

theorem leaf_4624_ok : checkAt 527 1000 box_4624 cert_4624 = true := by
  have h := List.all_eq_true.mp batch_92_14_ok accepted_4624 (by simp [batch_92_14_values])
  exact h
theorem leaf_4624_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4624.profileLo box_4624.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4624_ok
theorem branch_box_4624_nonnegative : ∀ j, 0 ≤ branch_box_4624.lower j ∧ 0 ≤ branch_box_4624.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4624, Box.profileLo, Box.profileHi, box_4624]
theorem leaf_4624_BranchSafe : CertificateConsequences.BranchSafe branch_box_4624 := by
  left; refine ⟨branch_box_4624_nonnegative, ?_⟩
  intro z hz; exact leaf_4624_sound hz

theorem leaf_4627_ok : checkAt 527 1000 box_4627 cert_4627 = true := by
  have h := List.all_eq_true.mp batch_92_15_ok accepted_4627 (by simp [batch_92_15_values])
  exact h
theorem leaf_4627_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4627.profileLo box_4627.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4627_ok
theorem branch_box_4627_nonnegative : ∀ j, 0 ≤ branch_box_4627.lower j ∧ 0 ≤ branch_box_4627.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4627, Box.profileLo, Box.profileHi, box_4627]
theorem leaf_4627_BranchSafe : CertificateConsequences.BranchSafe branch_box_4627 := by
  left; refine ⟨branch_box_4627_nonnegative, ?_⟩
  intro z hz; exact leaf_4627_sound hz

theorem leaf_4629_ok : checkAt 527 1000 box_4629 cert_4629 = true := by
  have h := List.all_eq_true.mp batch_92_16_ok accepted_4629 (by simp [batch_92_16_values])
  exact h
theorem leaf_4629_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4629.profileLo box_4629.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4629_ok
theorem branch_box_4629_nonnegative : ∀ j, 0 ≤ branch_box_4629.lower j ∧ 0 ≤ branch_box_4629.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4629, Box.profileLo, Box.profileHi, box_4629]
theorem leaf_4629_BranchSafe : CertificateConsequences.BranchSafe branch_box_4629 := by
  left; refine ⟨branch_box_4629_nonnegative, ?_⟩
  intro z hz; exact leaf_4629_sound hz

theorem leaf_4630_ok : checkAt 527 1000 box_4630 cert_4630 = true := by
  have h := List.all_eq_true.mp batch_92_17_ok accepted_4630 (by simp [batch_92_17_values])
  exact h
theorem leaf_4630_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4630.profileLo box_4630.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4630_ok
theorem branch_box_4630_nonnegative : ∀ j, 0 ≤ branch_box_4630.lower j ∧ 0 ≤ branch_box_4630.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4630, Box.profileLo, Box.profileHi, box_4630]
theorem leaf_4630_BranchSafe : CertificateConsequences.BranchSafe branch_box_4630 := by
  left; refine ⟨branch_box_4630_nonnegative, ?_⟩
  intro z hz; exact leaf_4630_sound hz

theorem leaf_4631_ok : checkAt 527 1000 box_4631 cert_4631 = true := by
  have h := List.all_eq_true.mp batch_92_18_ok accepted_4631 (by simp [batch_92_18_values])
  exact h
theorem leaf_4631_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4631.profileLo box_4631.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4631_ok
theorem branch_box_4631_nonnegative : ∀ j, 0 ≤ branch_box_4631.lower j ∧ 0 ≤ branch_box_4631.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4631, Box.profileLo, Box.profileHi, box_4631]
theorem leaf_4631_BranchSafe : CertificateConsequences.BranchSafe branch_box_4631 := by
  left; refine ⟨branch_box_4631_nonnegative, ?_⟩
  intro z hz; exact leaf_4631_sound hz

theorem leaf_4632_ok : checkAt 527 1000 box_4632 cert_4632 = true := by
  have h := List.all_eq_true.mp batch_92_19_ok accepted_4632 (by simp [batch_92_19_values])
  exact h
theorem leaf_4632_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4632.profileLo box_4632.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4632_ok
theorem branch_box_4632_nonnegative : ∀ j, 0 ≤ branch_box_4632.lower j ∧ 0 ≤ branch_box_4632.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4632, Box.profileLo, Box.profileHi, box_4632]
theorem leaf_4632_BranchSafe : CertificateConsequences.BranchSafe branch_box_4632 := by
  left; refine ⟨branch_box_4632_nonnegative, ?_⟩
  intro z hz; exact leaf_4632_sound hz

theorem leaf_4638_ok : checkAt 527 1000 box_4638 cert_4638 = true := by
  have h := List.all_eq_true.mp batch_92_20_ok accepted_4638 (by simp [batch_92_20_values])
  exact h
theorem leaf_4638_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4638.profileLo box_4638.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4638_ok
theorem branch_box_4638_nonnegative : ∀ j, 0 ≤ branch_box_4638.lower j ∧ 0 ≤ branch_box_4638.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4638, Box.profileLo, Box.profileHi, box_4638]
theorem leaf_4638_BranchSafe : CertificateConsequences.BranchSafe branch_box_4638 := by
  left; refine ⟨branch_box_4638_nonnegative, ?_⟩
  intro z hz; exact leaf_4638_sound hz

theorem leaf_4639_ok : checkAt 527 1000 box_4639 cert_4639 = true := by
  have h := List.all_eq_true.mp batch_92_21_ok accepted_4639 (by simp [batch_92_21_values])
  exact h
theorem leaf_4639_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4639.profileLo box_4639.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4639_ok
theorem branch_box_4639_nonnegative : ∀ j, 0 ≤ branch_box_4639.lower j ∧ 0 ≤ branch_box_4639.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4639, Box.profileLo, Box.profileHi, box_4639]
theorem leaf_4639_BranchSafe : CertificateConsequences.BranchSafe branch_box_4639 := by
  left; refine ⟨branch_box_4639_nonnegative, ?_⟩
  intro z hz; exact leaf_4639_sound hz

theorem leaf_4640_ok : checkAt 527 1000 box_4640 cert_4640 = true := by
  have h := List.all_eq_true.mp batch_92_22_ok accepted_4640 (by simp [batch_92_22_values])
  exact h
theorem leaf_4640_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4640.profileLo box_4640.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4640_ok
theorem branch_box_4640_nonnegative : ∀ j, 0 ≤ branch_box_4640.lower j ∧ 0 ≤ branch_box_4640.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4640, Box.profileLo, Box.profileHi, box_4640]
theorem leaf_4640_BranchSafe : CertificateConsequences.BranchSafe branch_box_4640 := by
  left; refine ⟨branch_box_4640_nonnegative, ?_⟩
  intro z hz; exact leaf_4640_sound hz

theorem leaf_4642_ok : checkAt 527 1000 box_4642 cert_4642 = true := by
  have h := List.all_eq_true.mp batch_92_23_ok accepted_4642 (by simp [batch_92_23_values])
  exact h
theorem leaf_4642_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4642.profileLo box_4642.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4642_ok
theorem branch_box_4642_nonnegative : ∀ j, 0 ≤ branch_box_4642.lower j ∧ 0 ≤ branch_box_4642.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4642, Box.profileLo, Box.profileHi, box_4642]
theorem leaf_4642_BranchSafe : CertificateConsequences.BranchSafe branch_box_4642 := by
  left; refine ⟨branch_box_4642_nonnegative, ?_⟩
  intro z hz; exact leaf_4642_sound hz

theorem leaf_4643_ok : checkAt 527 1000 box_4643 cert_4643 = true := by
  have h := List.all_eq_true.mp batch_92_24_ok accepted_4643 (by simp [batch_92_24_values])
  exact h
theorem leaf_4643_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4643.profileLo box_4643.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4643_ok
theorem branch_box_4643_nonnegative : ∀ j, 0 ≤ branch_box_4643.lower j ∧ 0 ≤ branch_box_4643.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4643, Box.profileLo, Box.profileHi, box_4643]
theorem leaf_4643_BranchSafe : CertificateConsequences.BranchSafe branch_box_4643 := by
  left; refine ⟨branch_box_4643_nonnegative, ?_⟩
  intro z hz; exact leaf_4643_sound hz

theorem leaf_4645_ok : checkAt 527 1000 box_4645 cert_4645 = true := by
  have h := List.all_eq_true.mp batch_92_25_ok accepted_4645 (by simp [batch_92_25_values])
  exact h
theorem leaf_4645_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4645.profileLo box_4645.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4645_ok
theorem branch_box_4645_nonnegative : ∀ j, 0 ≤ branch_box_4645.lower j ∧ 0 ≤ branch_box_4645.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4645, Box.profileLo, Box.profileHi, box_4645]
theorem leaf_4645_BranchSafe : CertificateConsequences.BranchSafe branch_box_4645 := by
  left; refine ⟨branch_box_4645_nonnegative, ?_⟩
  intro z hz; exact leaf_4645_sound hz

theorem leaf_4646_ok : checkAt 527 1000 box_4646 cert_4646 = true := by
  have h := List.all_eq_true.mp batch_92_26_ok accepted_4646 (by simp [batch_92_26_values])
  exact h
theorem leaf_4646_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4646.profileLo box_4646.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4646_ok
theorem branch_box_4646_nonnegative : ∀ j, 0 ≤ branch_box_4646.lower j ∧ 0 ≤ branch_box_4646.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4646, Box.profileLo, Box.profileHi, box_4646]
theorem leaf_4646_BranchSafe : CertificateConsequences.BranchSafe branch_box_4646 := by
  left; refine ⟨branch_box_4646_nonnegative, ?_⟩
  intro z hz; exact leaf_4646_sound hz

theorem leaf_4647_ok : checkAt 527 1000 box_4647 cert_4647 = true := by
  have h := List.all_eq_true.mp batch_92_27_ok accepted_4647 (by simp [batch_92_27_values])
  exact h
theorem leaf_4647_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4647.profileLo box_4647.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4647_ok
theorem branch_box_4647_nonnegative : ∀ j, 0 ≤ branch_box_4647.lower j ∧ 0 ≤ branch_box_4647.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4647, Box.profileLo, Box.profileHi, box_4647]
theorem leaf_4647_BranchSafe : CertificateConsequences.BranchSafe branch_box_4647 := by
  left; refine ⟨branch_box_4647_nonnegative, ?_⟩
  intro z hz; exact leaf_4647_sound hz

theorem leaf_4648_ok : checkAt 527 1000 box_4648 cert_4648 = true := by
  have h := List.all_eq_true.mp batch_92_28_ok accepted_4648 (by simp [batch_92_28_values])
  exact h
theorem leaf_4648_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4648.profileLo box_4648.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4648_ok
theorem branch_box_4648_nonnegative : ∀ j, 0 ≤ branch_box_4648.lower j ∧ 0 ≤ branch_box_4648.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4648, Box.profileLo, Box.profileHi, box_4648]
theorem leaf_4648_BranchSafe : CertificateConsequences.BranchSafe branch_box_4648 := by
  left; refine ⟨branch_box_4648_nonnegative, ?_⟩
  intro z hz; exact leaf_4648_sound hz

#print axioms batch_92_00_ok
#print axioms leaf_4600_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
