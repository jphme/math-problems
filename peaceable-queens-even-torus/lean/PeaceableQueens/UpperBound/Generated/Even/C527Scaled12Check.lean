import PeaceableQueens.UpperBound.Generated.Even.C527Scaled12Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_12_00_values : List Bool := [accepted_600]
theorem batch_12_00_ok : batch_12_00_values.all id = true := by decide

def batch_12_01_values : List Bool := [accepted_601]
theorem batch_12_01_ok : batch_12_01_values.all id = true := by decide

def batch_12_02_values : List Bool := [accepted_603]
theorem batch_12_02_ok : batch_12_02_values.all id = true := by decide

def batch_12_03_values : List Bool := [accepted_604]
theorem batch_12_03_ok : batch_12_03_values.all id = true := by decide

def batch_12_04_values : List Bool := [accepted_607]
theorem batch_12_04_ok : batch_12_04_values.all id = true := by decide

def batch_12_05_values : List Bool := [accepted_608]
theorem batch_12_05_ok : batch_12_05_values.all id = true := by decide

def batch_12_06_values : List Bool := [accepted_609]
theorem batch_12_06_ok : batch_12_06_values.all id = true := by decide

def batch_12_07_values : List Bool := [accepted_611]
theorem batch_12_07_ok : batch_12_07_values.all id = true := by decide

def batch_12_08_values : List Bool := [accepted_613]
theorem batch_12_08_ok : batch_12_08_values.all id = true := by decide

def batch_12_09_values : List Bool := [accepted_615]
theorem batch_12_09_ok : batch_12_09_values.all id = true := by decide

def batch_12_10_values : List Bool := [accepted_616]
theorem batch_12_10_ok : batch_12_10_values.all id = true := by decide

def batch_12_11_values : List Bool := [accepted_625]
theorem batch_12_11_ok : batch_12_11_values.all id = true := by decide

def batch_12_12_values : List Bool := [accepted_626]
theorem batch_12_12_ok : batch_12_12_values.all id = true := by decide

def batch_12_13_values : List Bool := [accepted_631]
theorem batch_12_13_ok : batch_12_13_values.all id = true := by decide

def batch_12_14_values : List Bool := [accepted_633]
theorem batch_12_14_ok : batch_12_14_values.all id = true := by decide

def batch_12_15_values : List Bool := [accepted_634]
theorem batch_12_15_ok : batch_12_15_values.all id = true := by decide

def batch_12_16_values : List Bool := [accepted_635]
theorem batch_12_16_ok : batch_12_16_values.all id = true := by decide

def batch_12_17_values : List Bool := [accepted_636]
theorem batch_12_17_ok : batch_12_17_values.all id = true := by decide

def batch_12_18_values : List Bool := [accepted_639]
theorem batch_12_18_ok : batch_12_18_values.all id = true := by decide

def batch_12_19_values : List Bool := [accepted_640]
theorem batch_12_19_ok : batch_12_19_values.all id = true := by decide

def batch_12_20_values : List Bool := [accepted_641]
theorem batch_12_20_ok : batch_12_20_values.all id = true := by decide

def batch_12_21_values : List Bool := [accepted_642]
theorem batch_12_21_ok : batch_12_21_values.all id = true := by decide

def batch_12_22_values : List Bool := [accepted_647]
theorem batch_12_22_ok : batch_12_22_values.all id = true := by decide

def batch_12_23_values : List Bool := [accepted_648]
theorem batch_12_23_ok : batch_12_23_values.all id = true := by decide

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

theorem leaf_603_ok : checkAt 527 1000 box_603 cert_603 = true := by
  have h := List.all_eq_true.mp batch_12_02_ok accepted_603 (by simp [batch_12_02_values])
  exact h
theorem leaf_603_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_603.profileLo box_603.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_603_ok
theorem branch_box_603_nonnegative : ∀ j, 0 ≤ branch_box_603.lower j ∧ 0 ≤ branch_box_603.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_603, Box.profileLo, Box.profileHi, box_603]
theorem leaf_603_BranchSafe : CertificateConsequences.BranchSafe branch_box_603 := by
  left; refine ⟨branch_box_603_nonnegative, ?_⟩
  intro z hz; exact leaf_603_sound hz

theorem leaf_604_ok : checkAt 527 1000 box_604 cert_604 = true := by
  have h := List.all_eq_true.mp batch_12_03_ok accepted_604 (by simp [batch_12_03_values])
  exact h
theorem leaf_604_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_604.profileLo box_604.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_604_ok
theorem branch_box_604_nonnegative : ∀ j, 0 ≤ branch_box_604.lower j ∧ 0 ≤ branch_box_604.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_604, Box.profileLo, Box.profileHi, box_604]
theorem leaf_604_BranchSafe : CertificateConsequences.BranchSafe branch_box_604 := by
  left; refine ⟨branch_box_604_nonnegative, ?_⟩
  intro z hz; exact leaf_604_sound hz

theorem leaf_607_ok : checkAt 527 1000 box_607 cert_607 = true := by
  have h := List.all_eq_true.mp batch_12_04_ok accepted_607 (by simp [batch_12_04_values])
  exact h
theorem leaf_607_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_607.profileLo box_607.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_607_ok
theorem branch_box_607_nonnegative : ∀ j, 0 ≤ branch_box_607.lower j ∧ 0 ≤ branch_box_607.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_607, Box.profileLo, Box.profileHi, box_607]
theorem leaf_607_BranchSafe : CertificateConsequences.BranchSafe branch_box_607 := by
  left; refine ⟨branch_box_607_nonnegative, ?_⟩
  intro z hz; exact leaf_607_sound hz

theorem leaf_608_ok : checkAt 527 1000 box_608 cert_608 = true := by
  have h := List.all_eq_true.mp batch_12_05_ok accepted_608 (by simp [batch_12_05_values])
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

theorem leaf_609_ok : checkAt 527 1000 box_609 cert_609 = true := by
  have h := List.all_eq_true.mp batch_12_06_ok accepted_609 (by simp [batch_12_06_values])
  exact h
theorem leaf_609_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_609.profileLo box_609.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_609_ok
theorem branch_box_609_nonnegative : ∀ j, 0 ≤ branch_box_609.lower j ∧ 0 ≤ branch_box_609.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_609, Box.profileLo, Box.profileHi, box_609]
theorem leaf_609_BranchSafe : CertificateConsequences.BranchSafe branch_box_609 := by
  left; refine ⟨branch_box_609_nonnegative, ?_⟩
  intro z hz; exact leaf_609_sound hz

theorem leaf_611_ok : checkAt 527 1000 box_611 cert_611 = true := by
  have h := List.all_eq_true.mp batch_12_07_ok accepted_611 (by simp [batch_12_07_values])
  exact h
theorem leaf_611_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_611.profileLo box_611.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_611_ok
theorem branch_box_611_nonnegative : ∀ j, 0 ≤ branch_box_611.lower j ∧ 0 ≤ branch_box_611.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_611, Box.profileLo, Box.profileHi, box_611]
theorem leaf_611_BranchSafe : CertificateConsequences.BranchSafe branch_box_611 := by
  left; refine ⟨branch_box_611_nonnegative, ?_⟩
  intro z hz; exact leaf_611_sound hz

theorem leaf_613_ok : checkAt 527 1000 box_613 cert_613 = true := by
  have h := List.all_eq_true.mp batch_12_08_ok accepted_613 (by simp [batch_12_08_values])
  exact h
theorem leaf_613_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_613.profileLo box_613.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_613_ok
theorem branch_box_613_nonnegative : ∀ j, 0 ≤ branch_box_613.lower j ∧ 0 ≤ branch_box_613.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_613, Box.profileLo, Box.profileHi, box_613]
theorem leaf_613_BranchSafe : CertificateConsequences.BranchSafe branch_box_613 := by
  left; refine ⟨branch_box_613_nonnegative, ?_⟩
  intro z hz; exact leaf_613_sound hz

theorem leaf_615_ok : checkAt 527 1000 box_615 cert_615 = true := by
  have h := List.all_eq_true.mp batch_12_09_ok accepted_615 (by simp [batch_12_09_values])
  exact h
theorem leaf_615_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_615.profileLo box_615.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_615_ok
theorem branch_box_615_nonnegative : ∀ j, 0 ≤ branch_box_615.lower j ∧ 0 ≤ branch_box_615.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_615, Box.profileLo, Box.profileHi, box_615]
theorem leaf_615_BranchSafe : CertificateConsequences.BranchSafe branch_box_615 := by
  left; refine ⟨branch_box_615_nonnegative, ?_⟩
  intro z hz; exact leaf_615_sound hz

theorem leaf_616_ok : checkAt 527 1000 box_616 cert_616 = true := by
  have h := List.all_eq_true.mp batch_12_10_ok accepted_616 (by simp [batch_12_10_values])
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

theorem leaf_625_ok : checkAt 527 1000 box_625 cert_625 = true := by
  have h := List.all_eq_true.mp batch_12_11_ok accepted_625 (by simp [batch_12_11_values])
  exact h
theorem leaf_625_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_625.profileLo box_625.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_625_ok
theorem branch_box_625_nonnegative : ∀ j, 0 ≤ branch_box_625.lower j ∧ 0 ≤ branch_box_625.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_625, Box.profileLo, Box.profileHi, box_625]
theorem leaf_625_BranchSafe : CertificateConsequences.BranchSafe branch_box_625 := by
  left; refine ⟨branch_box_625_nonnegative, ?_⟩
  intro z hz; exact leaf_625_sound hz

theorem leaf_626_ok : checkAt 527 1000 box_626 cert_626 = true := by
  have h := List.all_eq_true.mp batch_12_12_ok accepted_626 (by simp [batch_12_12_values])
  exact h
theorem leaf_626_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_626.profileLo box_626.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_626_ok
theorem branch_box_626_nonnegative : ∀ j, 0 ≤ branch_box_626.lower j ∧ 0 ≤ branch_box_626.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_626, Box.profileLo, Box.profileHi, box_626]
theorem leaf_626_BranchSafe : CertificateConsequences.BranchSafe branch_box_626 := by
  left; refine ⟨branch_box_626_nonnegative, ?_⟩
  intro z hz; exact leaf_626_sound hz

theorem leaf_631_ok : checkAt 527 1000 box_631 cert_631 = true := by
  have h := List.all_eq_true.mp batch_12_13_ok accepted_631 (by simp [batch_12_13_values])
  exact h
theorem leaf_631_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_631.profileLo box_631.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_631_ok
theorem branch_box_631_nonnegative : ∀ j, 0 ≤ branch_box_631.lower j ∧ 0 ≤ branch_box_631.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_631, Box.profileLo, Box.profileHi, box_631]
theorem leaf_631_BranchSafe : CertificateConsequences.BranchSafe branch_box_631 := by
  left; refine ⟨branch_box_631_nonnegative, ?_⟩
  intro z hz; exact leaf_631_sound hz

theorem leaf_633_ok : checkAt 527 1000 box_633 cert_633 = true := by
  have h := List.all_eq_true.mp batch_12_14_ok accepted_633 (by simp [batch_12_14_values])
  exact h
theorem leaf_633_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_633.profileLo box_633.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_633_ok
theorem branch_box_633_nonnegative : ∀ j, 0 ≤ branch_box_633.lower j ∧ 0 ≤ branch_box_633.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_633, Box.profileLo, Box.profileHi, box_633]
theorem leaf_633_BranchSafe : CertificateConsequences.BranchSafe branch_box_633 := by
  left; refine ⟨branch_box_633_nonnegative, ?_⟩
  intro z hz; exact leaf_633_sound hz

theorem leaf_634_ok : checkAt 527 1000 box_634 cert_634 = true := by
  have h := List.all_eq_true.mp batch_12_15_ok accepted_634 (by simp [batch_12_15_values])
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
  have h := List.all_eq_true.mp batch_12_16_ok accepted_635 (by simp [batch_12_16_values])
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

theorem leaf_636_ok : checkAt 527 1000 box_636 cert_636 = true := by
  have h := List.all_eq_true.mp batch_12_17_ok accepted_636 (by simp [batch_12_17_values])
  exact h
theorem leaf_636_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_636.profileLo box_636.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_636_ok
theorem branch_box_636_nonnegative : ∀ j, 0 ≤ branch_box_636.lower j ∧ 0 ≤ branch_box_636.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_636, Box.profileLo, Box.profileHi, box_636]
theorem leaf_636_BranchSafe : CertificateConsequences.BranchSafe branch_box_636 := by
  left; refine ⟨branch_box_636_nonnegative, ?_⟩
  intro z hz; exact leaf_636_sound hz

theorem leaf_639_ok : checkAt 527 1000 box_639 cert_639 = true := by
  have h := List.all_eq_true.mp batch_12_18_ok accepted_639 (by simp [batch_12_18_values])
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

theorem leaf_640_ok : checkAt 527 1000 box_640 cert_640 = true := by
  have h := List.all_eq_true.mp batch_12_19_ok accepted_640 (by simp [batch_12_19_values])
  exact h
theorem leaf_640_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_640.profileLo box_640.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_640_ok
theorem branch_box_640_nonnegative : ∀ j, 0 ≤ branch_box_640.lower j ∧ 0 ≤ branch_box_640.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_640, Box.profileLo, Box.profileHi, box_640]
theorem leaf_640_BranchSafe : CertificateConsequences.BranchSafe branch_box_640 := by
  left; refine ⟨branch_box_640_nonnegative, ?_⟩
  intro z hz; exact leaf_640_sound hz

theorem leaf_641_ok : checkAt 527 1000 box_641 cert_641 = true := by
  have h := List.all_eq_true.mp batch_12_20_ok accepted_641 (by simp [batch_12_20_values])
  exact h
theorem leaf_641_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_641.profileLo box_641.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_641_ok
theorem branch_box_641_nonnegative : ∀ j, 0 ≤ branch_box_641.lower j ∧ 0 ≤ branch_box_641.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_641, Box.profileLo, Box.profileHi, box_641]
theorem leaf_641_BranchSafe : CertificateConsequences.BranchSafe branch_box_641 := by
  left; refine ⟨branch_box_641_nonnegative, ?_⟩
  intro z hz; exact leaf_641_sound hz

theorem leaf_642_ok : checkAt 527 1000 box_642 cert_642 = true := by
  have h := List.all_eq_true.mp batch_12_21_ok accepted_642 (by simp [batch_12_21_values])
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

theorem leaf_647_ok : checkAt 527 1000 box_647 cert_647 = true := by
  have h := List.all_eq_true.mp batch_12_22_ok accepted_647 (by simp [batch_12_22_values])
  exact h
theorem leaf_647_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_647.profileLo box_647.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_647_ok
theorem branch_box_647_nonnegative : ∀ j, 0 ≤ branch_box_647.lower j ∧ 0 ≤ branch_box_647.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_647, Box.profileLo, Box.profileHi, box_647]
theorem leaf_647_BranchSafe : CertificateConsequences.BranchSafe branch_box_647 := by
  left; refine ⟨branch_box_647_nonnegative, ?_⟩
  intro z hz; exact leaf_647_sound hz

theorem leaf_648_ok : checkAt 527 1000 box_648 cert_648 = true := by
  have h := List.all_eq_true.mp batch_12_23_ok accepted_648 (by simp [batch_12_23_values])
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
end PeaceableQueens.UpperBound.Generated.Even.C527
