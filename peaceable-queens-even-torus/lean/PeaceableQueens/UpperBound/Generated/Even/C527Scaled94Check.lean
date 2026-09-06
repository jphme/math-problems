import PeaceableQueens.UpperBound.Generated.Even.C527Scaled94Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_94_00_values : List Bool := [accepted_4700]
theorem batch_94_00_ok : batch_94_00_values.all id = true := by decide

def batch_94_01_values : List Bool := [accepted_4701]
theorem batch_94_01_ok : batch_94_01_values.all id = true := by decide

def batch_94_02_values : List Bool := [accepted_4702]
theorem batch_94_02_ok : batch_94_02_values.all id = true := by decide

def batch_94_03_values : List Bool := [accepted_4705]
theorem batch_94_03_ok : batch_94_03_values.all id = true := by decide

def batch_94_04_values : List Bool := [accepted_4707]
theorem batch_94_04_ok : batch_94_04_values.all id = true := by decide

def batch_94_05_values : List Bool := [accepted_4708]
theorem batch_94_05_ok : batch_94_05_values.all id = true := by decide

def batch_94_06_values : List Bool := [accepted_4709]
theorem batch_94_06_ok : batch_94_06_values.all id = true := by decide

def batch_94_07_values : List Bool := [accepted_4710]
theorem batch_94_07_ok : batch_94_07_values.all id = true := by decide

def batch_94_08_values : List Bool := [accepted_4711]
theorem batch_94_08_ok : batch_94_08_values.all id = true := by decide

def batch_94_09_values : List Bool := [accepted_4715]
theorem batch_94_09_ok : batch_94_09_values.all id = true := by decide

def batch_94_10_values : List Bool := [accepted_4716]
theorem batch_94_10_ok : batch_94_10_values.all id = true := by decide

def batch_94_11_values : List Bool := [accepted_4717]
theorem batch_94_11_ok : batch_94_11_values.all id = true := by decide

def batch_94_12_values : List Bool := [accepted_4718]
theorem batch_94_12_ok : batch_94_12_values.all id = true := by decide

def batch_94_13_values : List Bool := [accepted_4721]
theorem batch_94_13_ok : batch_94_13_values.all id = true := by decide

def batch_94_14_values : List Bool := [accepted_4722]
theorem batch_94_14_ok : batch_94_14_values.all id = true := by decide

def batch_94_15_values : List Bool := [accepted_4725]
theorem batch_94_15_ok : batch_94_15_values.all id = true := by decide

def batch_94_16_values : List Bool := [accepted_4726]
theorem batch_94_16_ok : batch_94_16_values.all id = true := by decide

def batch_94_17_values : List Bool := [accepted_4727]
theorem batch_94_17_ok : batch_94_17_values.all id = true := by decide

def batch_94_18_values : List Bool := [accepted_4729]
theorem batch_94_18_ok : batch_94_18_values.all id = true := by decide

def batch_94_19_values : List Bool := [accepted_4730]
theorem batch_94_19_ok : batch_94_19_values.all id = true := by decide

def batch_94_20_values : List Bool := [accepted_4739]
theorem batch_94_20_ok : batch_94_20_values.all id = true := by decide

def batch_94_21_values : List Bool := [accepted_4740]
theorem batch_94_21_ok : batch_94_21_values.all id = true := by decide

def batch_94_22_values : List Bool := [accepted_4741]
theorem batch_94_22_ok : batch_94_22_values.all id = true := by decide

def batch_94_23_values : List Bool := [accepted_4743]
theorem batch_94_23_ok : batch_94_23_values.all id = true := by decide

def batch_94_24_values : List Bool := [accepted_4744]
theorem batch_94_24_ok : batch_94_24_values.all id = true := by decide

def batch_94_25_values : List Bool := [accepted_4745]
theorem batch_94_25_ok : batch_94_25_values.all id = true := by decide

def batch_94_26_values : List Bool := [accepted_4746]
theorem batch_94_26_ok : batch_94_26_values.all id = true := by decide

def batch_94_27_values : List Bool := [accepted_4747]
theorem batch_94_27_ok : batch_94_27_values.all id = true := by decide

def batch_94_28_values : List Bool := [accepted_4749]
theorem batch_94_28_ok : batch_94_28_values.all id = true := by decide

theorem leaf_4700_ok : checkAt 527 1000 box_4700 cert_4700 = true := by
  have h := List.all_eq_true.mp batch_94_00_ok accepted_4700 (by simp [batch_94_00_values])
  exact h
theorem leaf_4700_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4700.profileLo box_4700.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4700_ok
theorem branch_box_4700_nonnegative : ∀ j, 0 ≤ branch_box_4700.lower j ∧ 0 ≤ branch_box_4700.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4700, Box.profileLo, Box.profileHi, box_4700]
theorem leaf_4700_BranchSafe : CertificateConsequences.BranchSafe branch_box_4700 := by
  left; refine ⟨branch_box_4700_nonnegative, ?_⟩
  intro z hz; exact leaf_4700_sound hz

theorem leaf_4701_ok : checkAt 527 1000 box_4701 cert_4701 = true := by
  have h := List.all_eq_true.mp batch_94_01_ok accepted_4701 (by simp [batch_94_01_values])
  exact h
theorem leaf_4701_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4701.profileLo box_4701.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4701_ok
theorem branch_box_4701_nonnegative : ∀ j, 0 ≤ branch_box_4701.lower j ∧ 0 ≤ branch_box_4701.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4701, Box.profileLo, Box.profileHi, box_4701]
theorem leaf_4701_BranchSafe : CertificateConsequences.BranchSafe branch_box_4701 := by
  left; refine ⟨branch_box_4701_nonnegative, ?_⟩
  intro z hz; exact leaf_4701_sound hz

theorem leaf_4702_ok : checkAt 527 1000 box_4702 cert_4702 = true := by
  have h := List.all_eq_true.mp batch_94_02_ok accepted_4702 (by simp [batch_94_02_values])
  exact h
theorem leaf_4702_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4702.profileLo box_4702.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4702_ok
theorem branch_box_4702_nonnegative : ∀ j, 0 ≤ branch_box_4702.lower j ∧ 0 ≤ branch_box_4702.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4702, Box.profileLo, Box.profileHi, box_4702]
theorem leaf_4702_BranchSafe : CertificateConsequences.BranchSafe branch_box_4702 := by
  left; refine ⟨branch_box_4702_nonnegative, ?_⟩
  intro z hz; exact leaf_4702_sound hz

theorem leaf_4705_ok : checkAt 527 1000 box_4705 cert_4705 = true := by
  have h := List.all_eq_true.mp batch_94_03_ok accepted_4705 (by simp [batch_94_03_values])
  exact h
theorem leaf_4705_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4705.profileLo box_4705.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4705_ok
theorem branch_box_4705_nonnegative : ∀ j, 0 ≤ branch_box_4705.lower j ∧ 0 ≤ branch_box_4705.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4705, Box.profileLo, Box.profileHi, box_4705]
theorem leaf_4705_BranchSafe : CertificateConsequences.BranchSafe branch_box_4705 := by
  left; refine ⟨branch_box_4705_nonnegative, ?_⟩
  intro z hz; exact leaf_4705_sound hz

theorem leaf_4707_ok : checkAt 527 1000 box_4707 cert_4707 = true := by
  have h := List.all_eq_true.mp batch_94_04_ok accepted_4707 (by simp [batch_94_04_values])
  exact h
theorem leaf_4707_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4707.profileLo box_4707.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4707_ok
theorem branch_box_4707_nonnegative : ∀ j, 0 ≤ branch_box_4707.lower j ∧ 0 ≤ branch_box_4707.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4707, Box.profileLo, Box.profileHi, box_4707]
theorem leaf_4707_BranchSafe : CertificateConsequences.BranchSafe branch_box_4707 := by
  left; refine ⟨branch_box_4707_nonnegative, ?_⟩
  intro z hz; exact leaf_4707_sound hz

theorem leaf_4708_ok : checkAt 527 1000 box_4708 cert_4708 = true := by
  have h := List.all_eq_true.mp batch_94_05_ok accepted_4708 (by simp [batch_94_05_values])
  exact h
theorem leaf_4708_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4708.profileLo box_4708.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4708_ok
theorem branch_box_4708_nonnegative : ∀ j, 0 ≤ branch_box_4708.lower j ∧ 0 ≤ branch_box_4708.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4708, Box.profileLo, Box.profileHi, box_4708]
theorem leaf_4708_BranchSafe : CertificateConsequences.BranchSafe branch_box_4708 := by
  left; refine ⟨branch_box_4708_nonnegative, ?_⟩
  intro z hz; exact leaf_4708_sound hz

theorem leaf_4709_ok : checkAt 527 1000 box_4709 cert_4709 = true := by
  have h := List.all_eq_true.mp batch_94_06_ok accepted_4709 (by simp [batch_94_06_values])
  exact h
theorem leaf_4709_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4709.profileLo box_4709.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4709_ok
theorem branch_box_4709_nonnegative : ∀ j, 0 ≤ branch_box_4709.lower j ∧ 0 ≤ branch_box_4709.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4709, Box.profileLo, Box.profileHi, box_4709]
theorem leaf_4709_BranchSafe : CertificateConsequences.BranchSafe branch_box_4709 := by
  left; refine ⟨branch_box_4709_nonnegative, ?_⟩
  intro z hz; exact leaf_4709_sound hz

theorem leaf_4710_ok : checkAt 527 1000 box_4710 cert_4710 = true := by
  have h := List.all_eq_true.mp batch_94_07_ok accepted_4710 (by simp [batch_94_07_values])
  exact h
theorem leaf_4710_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4710.profileLo box_4710.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4710_ok
theorem branch_box_4710_nonnegative : ∀ j, 0 ≤ branch_box_4710.lower j ∧ 0 ≤ branch_box_4710.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4710, Box.profileLo, Box.profileHi, box_4710]
theorem leaf_4710_BranchSafe : CertificateConsequences.BranchSafe branch_box_4710 := by
  left; refine ⟨branch_box_4710_nonnegative, ?_⟩
  intro z hz; exact leaf_4710_sound hz

theorem leaf_4711_ok : checkAt 527 1000 box_4711 cert_4711 = true := by
  have h := List.all_eq_true.mp batch_94_08_ok accepted_4711 (by simp [batch_94_08_values])
  exact h
theorem leaf_4711_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4711.profileLo box_4711.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4711_ok
theorem branch_box_4711_nonnegative : ∀ j, 0 ≤ branch_box_4711.lower j ∧ 0 ≤ branch_box_4711.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4711, Box.profileLo, Box.profileHi, box_4711]
theorem leaf_4711_BranchSafe : CertificateConsequences.BranchSafe branch_box_4711 := by
  left; refine ⟨branch_box_4711_nonnegative, ?_⟩
  intro z hz; exact leaf_4711_sound hz

theorem leaf_4715_ok : checkAt 527 1000 box_4715 cert_4715 = true := by
  have h := List.all_eq_true.mp batch_94_09_ok accepted_4715 (by simp [batch_94_09_values])
  exact h
theorem leaf_4715_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4715.profileLo box_4715.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4715_ok
theorem branch_box_4715_nonnegative : ∀ j, 0 ≤ branch_box_4715.lower j ∧ 0 ≤ branch_box_4715.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4715, Box.profileLo, Box.profileHi, box_4715]
theorem leaf_4715_BranchSafe : CertificateConsequences.BranchSafe branch_box_4715 := by
  left; refine ⟨branch_box_4715_nonnegative, ?_⟩
  intro z hz; exact leaf_4715_sound hz

theorem leaf_4716_ok : checkAt 527 1000 box_4716 cert_4716 = true := by
  have h := List.all_eq_true.mp batch_94_10_ok accepted_4716 (by simp [batch_94_10_values])
  exact h
theorem leaf_4716_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4716.profileLo box_4716.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4716_ok
theorem branch_box_4716_nonnegative : ∀ j, 0 ≤ branch_box_4716.lower j ∧ 0 ≤ branch_box_4716.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4716, Box.profileLo, Box.profileHi, box_4716]
theorem leaf_4716_BranchSafe : CertificateConsequences.BranchSafe branch_box_4716 := by
  left; refine ⟨branch_box_4716_nonnegative, ?_⟩
  intro z hz; exact leaf_4716_sound hz

theorem leaf_4717_ok : checkAt 527 1000 box_4717 cert_4717 = true := by
  have h := List.all_eq_true.mp batch_94_11_ok accepted_4717 (by simp [batch_94_11_values])
  exact h
theorem leaf_4717_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4717.profileLo box_4717.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4717_ok
theorem branch_box_4717_nonnegative : ∀ j, 0 ≤ branch_box_4717.lower j ∧ 0 ≤ branch_box_4717.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4717, Box.profileLo, Box.profileHi, box_4717]
theorem leaf_4717_BranchSafe : CertificateConsequences.BranchSafe branch_box_4717 := by
  left; refine ⟨branch_box_4717_nonnegative, ?_⟩
  intro z hz; exact leaf_4717_sound hz

theorem leaf_4718_ok : checkAt 527 1000 box_4718 cert_4718 = true := by
  have h := List.all_eq_true.mp batch_94_12_ok accepted_4718 (by simp [batch_94_12_values])
  exact h
theorem leaf_4718_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4718.profileLo box_4718.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4718_ok
theorem branch_box_4718_nonnegative : ∀ j, 0 ≤ branch_box_4718.lower j ∧ 0 ≤ branch_box_4718.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4718, Box.profileLo, Box.profileHi, box_4718]
theorem leaf_4718_BranchSafe : CertificateConsequences.BranchSafe branch_box_4718 := by
  left; refine ⟨branch_box_4718_nonnegative, ?_⟩
  intro z hz; exact leaf_4718_sound hz

theorem leaf_4721_ok : checkAt 527 1000 box_4721 cert_4721 = true := by
  have h := List.all_eq_true.mp batch_94_13_ok accepted_4721 (by simp [batch_94_13_values])
  exact h
theorem leaf_4721_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4721.profileLo box_4721.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4721_ok
theorem branch_box_4721_nonnegative : ∀ j, 0 ≤ branch_box_4721.lower j ∧ 0 ≤ branch_box_4721.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4721, Box.profileLo, Box.profileHi, box_4721]
theorem leaf_4721_BranchSafe : CertificateConsequences.BranchSafe branch_box_4721 := by
  left; refine ⟨branch_box_4721_nonnegative, ?_⟩
  intro z hz; exact leaf_4721_sound hz

theorem leaf_4722_ok : checkAt 527 1000 box_4722 cert_4722 = true := by
  have h := List.all_eq_true.mp batch_94_14_ok accepted_4722 (by simp [batch_94_14_values])
  exact h
theorem leaf_4722_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4722.profileLo box_4722.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4722_ok
theorem branch_box_4722_nonnegative : ∀ j, 0 ≤ branch_box_4722.lower j ∧ 0 ≤ branch_box_4722.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4722, Box.profileLo, Box.profileHi, box_4722]
theorem leaf_4722_BranchSafe : CertificateConsequences.BranchSafe branch_box_4722 := by
  left; refine ⟨branch_box_4722_nonnegative, ?_⟩
  intro z hz; exact leaf_4722_sound hz

theorem leaf_4725_ok : checkAt 527 1000 box_4725 cert_4725 = true := by
  have h := List.all_eq_true.mp batch_94_15_ok accepted_4725 (by simp [batch_94_15_values])
  exact h
theorem leaf_4725_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4725.profileLo box_4725.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4725_ok
theorem branch_box_4725_nonnegative : ∀ j, 0 ≤ branch_box_4725.lower j ∧ 0 ≤ branch_box_4725.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4725, Box.profileLo, Box.profileHi, box_4725]
theorem leaf_4725_BranchSafe : CertificateConsequences.BranchSafe branch_box_4725 := by
  left; refine ⟨branch_box_4725_nonnegative, ?_⟩
  intro z hz; exact leaf_4725_sound hz

theorem leaf_4726_ok : checkAt 527 1000 box_4726 cert_4726 = true := by
  have h := List.all_eq_true.mp batch_94_16_ok accepted_4726 (by simp [batch_94_16_values])
  exact h
theorem leaf_4726_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4726.profileLo box_4726.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4726_ok
theorem branch_box_4726_nonnegative : ∀ j, 0 ≤ branch_box_4726.lower j ∧ 0 ≤ branch_box_4726.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4726, Box.profileLo, Box.profileHi, box_4726]
theorem leaf_4726_BranchSafe : CertificateConsequences.BranchSafe branch_box_4726 := by
  left; refine ⟨branch_box_4726_nonnegative, ?_⟩
  intro z hz; exact leaf_4726_sound hz

theorem leaf_4727_ok : checkAt 527 1000 box_4727 cert_4727 = true := by
  have h := List.all_eq_true.mp batch_94_17_ok accepted_4727 (by simp [batch_94_17_values])
  exact h
theorem leaf_4727_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4727.profileLo box_4727.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4727_ok
theorem branch_box_4727_nonnegative : ∀ j, 0 ≤ branch_box_4727.lower j ∧ 0 ≤ branch_box_4727.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4727, Box.profileLo, Box.profileHi, box_4727]
theorem leaf_4727_BranchSafe : CertificateConsequences.BranchSafe branch_box_4727 := by
  left; refine ⟨branch_box_4727_nonnegative, ?_⟩
  intro z hz; exact leaf_4727_sound hz

theorem leaf_4729_ok : checkAt 527 1000 box_4729 cert_4729 = true := by
  have h := List.all_eq_true.mp batch_94_18_ok accepted_4729 (by simp [batch_94_18_values])
  exact h
theorem leaf_4729_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4729.profileLo box_4729.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4729_ok
theorem branch_box_4729_nonnegative : ∀ j, 0 ≤ branch_box_4729.lower j ∧ 0 ≤ branch_box_4729.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4729, Box.profileLo, Box.profileHi, box_4729]
theorem leaf_4729_BranchSafe : CertificateConsequences.BranchSafe branch_box_4729 := by
  left; refine ⟨branch_box_4729_nonnegative, ?_⟩
  intro z hz; exact leaf_4729_sound hz

theorem leaf_4730_ok : checkAt 527 1000 box_4730 cert_4730 = true := by
  have h := List.all_eq_true.mp batch_94_19_ok accepted_4730 (by simp [batch_94_19_values])
  exact h
theorem leaf_4730_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4730.profileLo box_4730.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4730_ok
theorem branch_box_4730_nonnegative : ∀ j, 0 ≤ branch_box_4730.lower j ∧ 0 ≤ branch_box_4730.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4730, Box.profileLo, Box.profileHi, box_4730]
theorem leaf_4730_BranchSafe : CertificateConsequences.BranchSafe branch_box_4730 := by
  left; refine ⟨branch_box_4730_nonnegative, ?_⟩
  intro z hz; exact leaf_4730_sound hz

theorem leaf_4739_ok : checkAt 527 1000 box_4739 cert_4739 = true := by
  have h := List.all_eq_true.mp batch_94_20_ok accepted_4739 (by simp [batch_94_20_values])
  exact h
theorem leaf_4739_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4739.profileLo box_4739.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4739_ok
theorem branch_box_4739_nonnegative : ∀ j, 0 ≤ branch_box_4739.lower j ∧ 0 ≤ branch_box_4739.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4739, Box.profileLo, Box.profileHi, box_4739]
theorem leaf_4739_BranchSafe : CertificateConsequences.BranchSafe branch_box_4739 := by
  left; refine ⟨branch_box_4739_nonnegative, ?_⟩
  intro z hz; exact leaf_4739_sound hz

theorem leaf_4740_ok : checkAt 527 1000 box_4740 cert_4740 = true := by
  have h := List.all_eq_true.mp batch_94_21_ok accepted_4740 (by simp [batch_94_21_values])
  exact h
theorem leaf_4740_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4740.profileLo box_4740.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4740_ok
theorem branch_box_4740_nonnegative : ∀ j, 0 ≤ branch_box_4740.lower j ∧ 0 ≤ branch_box_4740.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4740, Box.profileLo, Box.profileHi, box_4740]
theorem leaf_4740_BranchSafe : CertificateConsequences.BranchSafe branch_box_4740 := by
  left; refine ⟨branch_box_4740_nonnegative, ?_⟩
  intro z hz; exact leaf_4740_sound hz

theorem leaf_4741_ok : checkAt 527 1000 box_4741 cert_4741 = true := by
  have h := List.all_eq_true.mp batch_94_22_ok accepted_4741 (by simp [batch_94_22_values])
  exact h
theorem leaf_4741_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4741.profileLo box_4741.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4741_ok
theorem branch_box_4741_nonnegative : ∀ j, 0 ≤ branch_box_4741.lower j ∧ 0 ≤ branch_box_4741.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4741, Box.profileLo, Box.profileHi, box_4741]
theorem leaf_4741_BranchSafe : CertificateConsequences.BranchSafe branch_box_4741 := by
  left; refine ⟨branch_box_4741_nonnegative, ?_⟩
  intro z hz; exact leaf_4741_sound hz

theorem leaf_4743_ok : checkAt 527 1000 box_4743 cert_4743 = true := by
  have h := List.all_eq_true.mp batch_94_23_ok accepted_4743 (by simp [batch_94_23_values])
  exact h
theorem leaf_4743_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4743.profileLo box_4743.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4743_ok
theorem branch_box_4743_nonnegative : ∀ j, 0 ≤ branch_box_4743.lower j ∧ 0 ≤ branch_box_4743.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4743, Box.profileLo, Box.profileHi, box_4743]
theorem leaf_4743_BranchSafe : CertificateConsequences.BranchSafe branch_box_4743 := by
  left; refine ⟨branch_box_4743_nonnegative, ?_⟩
  intro z hz; exact leaf_4743_sound hz

theorem leaf_4744_ok : checkAt 527 1000 box_4744 cert_4744 = true := by
  have h := List.all_eq_true.mp batch_94_24_ok accepted_4744 (by simp [batch_94_24_values])
  exact h
theorem leaf_4744_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4744.profileLo box_4744.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4744_ok
theorem branch_box_4744_nonnegative : ∀ j, 0 ≤ branch_box_4744.lower j ∧ 0 ≤ branch_box_4744.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4744, Box.profileLo, Box.profileHi, box_4744]
theorem leaf_4744_BranchSafe : CertificateConsequences.BranchSafe branch_box_4744 := by
  left; refine ⟨branch_box_4744_nonnegative, ?_⟩
  intro z hz; exact leaf_4744_sound hz

theorem leaf_4745_ok : checkAt 527 1000 box_4745 cert_4745 = true := by
  have h := List.all_eq_true.mp batch_94_25_ok accepted_4745 (by simp [batch_94_25_values])
  exact h
theorem leaf_4745_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4745.profileLo box_4745.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4745_ok
theorem branch_box_4745_nonnegative : ∀ j, 0 ≤ branch_box_4745.lower j ∧ 0 ≤ branch_box_4745.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4745, Box.profileLo, Box.profileHi, box_4745]
theorem leaf_4745_BranchSafe : CertificateConsequences.BranchSafe branch_box_4745 := by
  left; refine ⟨branch_box_4745_nonnegative, ?_⟩
  intro z hz; exact leaf_4745_sound hz

theorem leaf_4746_ok : checkAt 527 1000 box_4746 cert_4746 = true := by
  have h := List.all_eq_true.mp batch_94_26_ok accepted_4746 (by simp [batch_94_26_values])
  exact h
theorem leaf_4746_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4746.profileLo box_4746.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4746_ok
theorem branch_box_4746_nonnegative : ∀ j, 0 ≤ branch_box_4746.lower j ∧ 0 ≤ branch_box_4746.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4746, Box.profileLo, Box.profileHi, box_4746]
theorem leaf_4746_BranchSafe : CertificateConsequences.BranchSafe branch_box_4746 := by
  left; refine ⟨branch_box_4746_nonnegative, ?_⟩
  intro z hz; exact leaf_4746_sound hz

theorem leaf_4747_ok : checkAt 527 1000 box_4747 cert_4747 = true := by
  have h := List.all_eq_true.mp batch_94_27_ok accepted_4747 (by simp [batch_94_27_values])
  exact h
theorem leaf_4747_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4747.profileLo box_4747.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4747_ok
theorem branch_box_4747_nonnegative : ∀ j, 0 ≤ branch_box_4747.lower j ∧ 0 ≤ branch_box_4747.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4747, Box.profileLo, Box.profileHi, box_4747]
theorem leaf_4747_BranchSafe : CertificateConsequences.BranchSafe branch_box_4747 := by
  left; refine ⟨branch_box_4747_nonnegative, ?_⟩
  intro z hz; exact leaf_4747_sound hz

theorem leaf_4749_ok : checkAt 527 1000 box_4749 cert_4749 = true := by
  have h := List.all_eq_true.mp batch_94_28_ok accepted_4749 (by simp [batch_94_28_values])
  exact h
theorem leaf_4749_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4749.profileLo box_4749.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4749_ok
theorem branch_box_4749_nonnegative : ∀ j, 0 ≤ branch_box_4749.lower j ∧ 0 ≤ branch_box_4749.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4749, Box.profileLo, Box.profileHi, box_4749]
theorem leaf_4749_BranchSafe : CertificateConsequences.BranchSafe branch_box_4749 := by
  left; refine ⟨branch_box_4749_nonnegative, ?_⟩
  intro z hz; exact leaf_4749_sound hz

#print axioms batch_94_00_ok
#print axioms leaf_4700_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
