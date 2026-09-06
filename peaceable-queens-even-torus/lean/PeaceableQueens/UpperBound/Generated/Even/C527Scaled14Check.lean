import PeaceableQueens.UpperBound.Generated.Even.C527Scaled14Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_14_00_values : List Bool := [accepted_701]
theorem batch_14_00_ok : batch_14_00_values.all id = true := by decide

def batch_14_01_values : List Bool := [accepted_702]
theorem batch_14_01_ok : batch_14_01_values.all id = true := by decide

def batch_14_02_values : List Bool := [accepted_703]
theorem batch_14_02_ok : batch_14_02_values.all id = true := by decide

def batch_14_03_values : List Bool := [accepted_705]
theorem batch_14_03_ok : batch_14_03_values.all id = true := by decide

def batch_14_04_values : List Bool := [accepted_706]
theorem batch_14_04_ok : batch_14_04_values.all id = true := by decide

def batch_14_05_values : List Bool := [accepted_711]
theorem batch_14_05_ok : batch_14_05_values.all id = true := by decide

def batch_14_06_values : List Bool := [accepted_712]
theorem batch_14_06_ok : batch_14_06_values.all id = true := by decide

def batch_14_07_values : List Bool := [accepted_713]
theorem batch_14_07_ok : batch_14_07_values.all id = true := by decide

def batch_14_08_values : List Bool := [accepted_714]
theorem batch_14_08_ok : batch_14_08_values.all id = true := by decide

def batch_14_09_values : List Bool := [accepted_715]
theorem batch_14_09_ok : batch_14_09_values.all id = true := by decide

def batch_14_10_values : List Bool := [accepted_717]
theorem batch_14_10_ok : batch_14_10_values.all id = true := by decide

def batch_14_11_values : List Bool := [accepted_718]
theorem batch_14_11_ok : batch_14_11_values.all id = true := by decide

def batch_14_12_values : List Bool := [accepted_721]
theorem batch_14_12_ok : batch_14_12_values.all id = true := by decide

def batch_14_13_values : List Bool := [accepted_723]
theorem batch_14_13_ok : batch_14_13_values.all id = true := by decide

def batch_14_14_values : List Bool := [accepted_724]
theorem batch_14_14_ok : batch_14_14_values.all id = true := by decide

def batch_14_15_values : List Bool := [accepted_727]
theorem batch_14_15_ok : batch_14_15_values.all id = true := by decide

def batch_14_16_values : List Bool := [accepted_729]
theorem batch_14_16_ok : batch_14_16_values.all id = true := by decide

def batch_14_17_values : List Bool := [accepted_730]
theorem batch_14_17_ok : batch_14_17_values.all id = true := by decide

def batch_14_18_values : List Bool := [accepted_731]
theorem batch_14_18_ok : batch_14_18_values.all id = true := by decide

def batch_14_19_values : List Bool := [accepted_733]
theorem batch_14_19_ok : batch_14_19_values.all id = true := by decide

def batch_14_20_values : List Bool := [accepted_734]
theorem batch_14_20_ok : batch_14_20_values.all id = true := by decide

theorem leaf_701_ok : checkAt 527 1000 box_701 cert_701 = true := by
  have h := List.all_eq_true.mp batch_14_00_ok accepted_701 (by simp [batch_14_00_values])
  exact h
theorem leaf_701_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_701.profileLo box_701.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_701_ok
theorem branch_box_701_nonnegative : ∀ j, 0 ≤ branch_box_701.lower j ∧ 0 ≤ branch_box_701.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_701, Box.profileLo, Box.profileHi, box_701]
theorem leaf_701_BranchSafe : CertificateConsequences.BranchSafe branch_box_701 := by
  left; refine ⟨branch_box_701_nonnegative, ?_⟩
  intro z hz; exact leaf_701_sound hz

theorem leaf_702_ok : checkAt 527 1000 box_702 cert_702 = true := by
  have h := List.all_eq_true.mp batch_14_01_ok accepted_702 (by simp [batch_14_01_values])
  exact h
theorem leaf_702_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_702.profileLo box_702.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_702_ok
theorem branch_box_702_nonnegative : ∀ j, 0 ≤ branch_box_702.lower j ∧ 0 ≤ branch_box_702.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_702, Box.profileLo, Box.profileHi, box_702]
theorem leaf_702_BranchSafe : CertificateConsequences.BranchSafe branch_box_702 := by
  left; refine ⟨branch_box_702_nonnegative, ?_⟩
  intro z hz; exact leaf_702_sound hz

theorem leaf_703_ok : checkAt 527 1000 box_703 cert_703 = true := by
  have h := List.all_eq_true.mp batch_14_02_ok accepted_703 (by simp [batch_14_02_values])
  exact h
theorem leaf_703_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_703.profileLo box_703.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_703_ok
theorem branch_box_703_nonnegative : ∀ j, 0 ≤ branch_box_703.lower j ∧ 0 ≤ branch_box_703.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_703, Box.profileLo, Box.profileHi, box_703]
theorem leaf_703_BranchSafe : CertificateConsequences.BranchSafe branch_box_703 := by
  left; refine ⟨branch_box_703_nonnegative, ?_⟩
  intro z hz; exact leaf_703_sound hz

theorem leaf_705_ok : checkAt 527 1000 box_705 cert_705 = true := by
  have h := List.all_eq_true.mp batch_14_03_ok accepted_705 (by simp [batch_14_03_values])
  exact h
theorem leaf_705_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_705.profileLo box_705.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_705_ok
theorem branch_box_705_nonnegative : ∀ j, 0 ≤ branch_box_705.lower j ∧ 0 ≤ branch_box_705.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_705, Box.profileLo, Box.profileHi, box_705]
theorem leaf_705_BranchSafe : CertificateConsequences.BranchSafe branch_box_705 := by
  left; refine ⟨branch_box_705_nonnegative, ?_⟩
  intro z hz; exact leaf_705_sound hz

theorem leaf_706_ok : checkAt 527 1000 box_706 cert_706 = true := by
  have h := List.all_eq_true.mp batch_14_04_ok accepted_706 (by simp [batch_14_04_values])
  exact h
theorem leaf_706_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_706.profileLo box_706.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_706_ok
theorem branch_box_706_nonnegative : ∀ j, 0 ≤ branch_box_706.lower j ∧ 0 ≤ branch_box_706.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_706, Box.profileLo, Box.profileHi, box_706]
theorem leaf_706_BranchSafe : CertificateConsequences.BranchSafe branch_box_706 := by
  left; refine ⟨branch_box_706_nonnegative, ?_⟩
  intro z hz; exact leaf_706_sound hz

theorem leaf_711_ok : checkAt 527 1000 box_711 cert_711 = true := by
  have h := List.all_eq_true.mp batch_14_05_ok accepted_711 (by simp [batch_14_05_values])
  exact h
theorem leaf_711_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_711.profileLo box_711.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_711_ok
theorem branch_box_711_nonnegative : ∀ j, 0 ≤ branch_box_711.lower j ∧ 0 ≤ branch_box_711.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_711, Box.profileLo, Box.profileHi, box_711]
theorem leaf_711_BranchSafe : CertificateConsequences.BranchSafe branch_box_711 := by
  left; refine ⟨branch_box_711_nonnegative, ?_⟩
  intro z hz; exact leaf_711_sound hz

theorem leaf_712_ok : checkAt 527 1000 box_712 cert_712 = true := by
  have h := List.all_eq_true.mp batch_14_06_ok accepted_712 (by simp [batch_14_06_values])
  exact h
theorem leaf_712_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_712.profileLo box_712.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_712_ok
theorem branch_box_712_nonnegative : ∀ j, 0 ≤ branch_box_712.lower j ∧ 0 ≤ branch_box_712.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_712, Box.profileLo, Box.profileHi, box_712]
theorem leaf_712_BranchSafe : CertificateConsequences.BranchSafe branch_box_712 := by
  left; refine ⟨branch_box_712_nonnegative, ?_⟩
  intro z hz; exact leaf_712_sound hz

theorem leaf_713_ok : checkAt 527 1000 box_713 cert_713 = true := by
  have h := List.all_eq_true.mp batch_14_07_ok accepted_713 (by simp [batch_14_07_values])
  exact h
theorem leaf_713_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_713.profileLo box_713.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_713_ok
theorem branch_box_713_nonnegative : ∀ j, 0 ≤ branch_box_713.lower j ∧ 0 ≤ branch_box_713.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_713, Box.profileLo, Box.profileHi, box_713]
theorem leaf_713_BranchSafe : CertificateConsequences.BranchSafe branch_box_713 := by
  left; refine ⟨branch_box_713_nonnegative, ?_⟩
  intro z hz; exact leaf_713_sound hz

theorem leaf_714_ok : checkAt 527 1000 box_714 cert_714 = true := by
  have h := List.all_eq_true.mp batch_14_08_ok accepted_714 (by simp [batch_14_08_values])
  exact h
theorem leaf_714_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_714.profileLo box_714.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_714_ok
theorem branch_box_714_nonnegative : ∀ j, 0 ≤ branch_box_714.lower j ∧ 0 ≤ branch_box_714.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_714, Box.profileLo, Box.profileHi, box_714]
theorem leaf_714_BranchSafe : CertificateConsequences.BranchSafe branch_box_714 := by
  left; refine ⟨branch_box_714_nonnegative, ?_⟩
  intro z hz; exact leaf_714_sound hz

theorem leaf_715_ok : checkAt 527 1000 box_715 cert_715 = true := by
  have h := List.all_eq_true.mp batch_14_09_ok accepted_715 (by simp [batch_14_09_values])
  exact h
theorem leaf_715_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_715.profileLo box_715.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_715_ok
theorem branch_box_715_nonnegative : ∀ j, 0 ≤ branch_box_715.lower j ∧ 0 ≤ branch_box_715.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_715, Box.profileLo, Box.profileHi, box_715]
theorem leaf_715_BranchSafe : CertificateConsequences.BranchSafe branch_box_715 := by
  left; refine ⟨branch_box_715_nonnegative, ?_⟩
  intro z hz; exact leaf_715_sound hz

theorem leaf_717_ok : checkAt 527 1000 box_717 cert_717 = true := by
  have h := List.all_eq_true.mp batch_14_10_ok accepted_717 (by simp [batch_14_10_values])
  exact h
theorem leaf_717_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_717.profileLo box_717.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_717_ok
theorem branch_box_717_nonnegative : ∀ j, 0 ≤ branch_box_717.lower j ∧ 0 ≤ branch_box_717.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_717, Box.profileLo, Box.profileHi, box_717]
theorem leaf_717_BranchSafe : CertificateConsequences.BranchSafe branch_box_717 := by
  left; refine ⟨branch_box_717_nonnegative, ?_⟩
  intro z hz; exact leaf_717_sound hz

theorem leaf_718_ok : checkAt 527 1000 box_718 cert_718 = true := by
  have h := List.all_eq_true.mp batch_14_11_ok accepted_718 (by simp [batch_14_11_values])
  exact h
theorem leaf_718_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_718.profileLo box_718.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_718_ok
theorem branch_box_718_nonnegative : ∀ j, 0 ≤ branch_box_718.lower j ∧ 0 ≤ branch_box_718.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_718, Box.profileLo, Box.profileHi, box_718]
theorem leaf_718_BranchSafe : CertificateConsequences.BranchSafe branch_box_718 := by
  left; refine ⟨branch_box_718_nonnegative, ?_⟩
  intro z hz; exact leaf_718_sound hz

theorem leaf_721_ok : checkAt 527 1000 box_721 cert_721 = true := by
  have h := List.all_eq_true.mp batch_14_12_ok accepted_721 (by simp [batch_14_12_values])
  exact h
theorem leaf_721_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_721.profileLo box_721.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_721_ok
theorem branch_box_721_nonnegative : ∀ j, 0 ≤ branch_box_721.lower j ∧ 0 ≤ branch_box_721.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_721, Box.profileLo, Box.profileHi, box_721]
theorem leaf_721_BranchSafe : CertificateConsequences.BranchSafe branch_box_721 := by
  left; refine ⟨branch_box_721_nonnegative, ?_⟩
  intro z hz; exact leaf_721_sound hz

theorem leaf_723_ok : checkAt 527 1000 box_723 cert_723 = true := by
  have h := List.all_eq_true.mp batch_14_13_ok accepted_723 (by simp [batch_14_13_values])
  exact h
theorem leaf_723_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_723.profileLo box_723.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_723_ok
theorem branch_box_723_nonnegative : ∀ j, 0 ≤ branch_box_723.lower j ∧ 0 ≤ branch_box_723.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_723, Box.profileLo, Box.profileHi, box_723]
theorem leaf_723_BranchSafe : CertificateConsequences.BranchSafe branch_box_723 := by
  left; refine ⟨branch_box_723_nonnegative, ?_⟩
  intro z hz; exact leaf_723_sound hz

theorem leaf_724_ok : checkAt 527 1000 box_724 cert_724 = true := by
  have h := List.all_eq_true.mp batch_14_14_ok accepted_724 (by simp [batch_14_14_values])
  exact h
theorem leaf_724_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_724.profileLo box_724.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_724_ok
theorem branch_box_724_nonnegative : ∀ j, 0 ≤ branch_box_724.lower j ∧ 0 ≤ branch_box_724.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_724, Box.profileLo, Box.profileHi, box_724]
theorem leaf_724_BranchSafe : CertificateConsequences.BranchSafe branch_box_724 := by
  left; refine ⟨branch_box_724_nonnegative, ?_⟩
  intro z hz; exact leaf_724_sound hz

theorem leaf_727_ok : checkAt 527 1000 box_727 cert_727 = true := by
  have h := List.all_eq_true.mp batch_14_15_ok accepted_727 (by simp [batch_14_15_values])
  exact h
theorem leaf_727_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_727.profileLo box_727.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_727_ok
theorem branch_box_727_nonnegative : ∀ j, 0 ≤ branch_box_727.lower j ∧ 0 ≤ branch_box_727.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_727, Box.profileLo, Box.profileHi, box_727]
theorem leaf_727_BranchSafe : CertificateConsequences.BranchSafe branch_box_727 := by
  left; refine ⟨branch_box_727_nonnegative, ?_⟩
  intro z hz; exact leaf_727_sound hz

theorem leaf_729_ok : checkAt 527 1000 box_729 cert_729 = true := by
  have h := List.all_eq_true.mp batch_14_16_ok accepted_729 (by simp [batch_14_16_values])
  exact h
theorem leaf_729_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_729.profileLo box_729.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_729_ok
theorem branch_box_729_nonnegative : ∀ j, 0 ≤ branch_box_729.lower j ∧ 0 ≤ branch_box_729.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_729, Box.profileLo, Box.profileHi, box_729]
theorem leaf_729_BranchSafe : CertificateConsequences.BranchSafe branch_box_729 := by
  left; refine ⟨branch_box_729_nonnegative, ?_⟩
  intro z hz; exact leaf_729_sound hz

theorem leaf_730_ok : checkAt 527 1000 box_730 cert_730 = true := by
  have h := List.all_eq_true.mp batch_14_17_ok accepted_730 (by simp [batch_14_17_values])
  exact h
theorem leaf_730_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_730.profileLo box_730.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_730_ok
theorem branch_box_730_nonnegative : ∀ j, 0 ≤ branch_box_730.lower j ∧ 0 ≤ branch_box_730.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_730, Box.profileLo, Box.profileHi, box_730]
theorem leaf_730_BranchSafe : CertificateConsequences.BranchSafe branch_box_730 := by
  left; refine ⟨branch_box_730_nonnegative, ?_⟩
  intro z hz; exact leaf_730_sound hz

theorem leaf_731_ok : checkAt 527 1000 box_731 cert_731 = true := by
  have h := List.all_eq_true.mp batch_14_18_ok accepted_731 (by simp [batch_14_18_values])
  exact h
theorem leaf_731_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_731.profileLo box_731.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_731_ok
theorem branch_box_731_nonnegative : ∀ j, 0 ≤ branch_box_731.lower j ∧ 0 ≤ branch_box_731.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_731, Box.profileLo, Box.profileHi, box_731]
theorem leaf_731_BranchSafe : CertificateConsequences.BranchSafe branch_box_731 := by
  left; refine ⟨branch_box_731_nonnegative, ?_⟩
  intro z hz; exact leaf_731_sound hz

theorem leaf_733_ok : checkAt 527 1000 box_733 cert_733 = true := by
  have h := List.all_eq_true.mp batch_14_19_ok accepted_733 (by simp [batch_14_19_values])
  exact h
theorem leaf_733_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_733.profileLo box_733.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_733_ok
theorem branch_box_733_nonnegative : ∀ j, 0 ≤ branch_box_733.lower j ∧ 0 ≤ branch_box_733.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_733, Box.profileLo, Box.profileHi, box_733]
theorem leaf_733_BranchSafe : CertificateConsequences.BranchSafe branch_box_733 := by
  left; refine ⟨branch_box_733_nonnegative, ?_⟩
  intro z hz; exact leaf_733_sound hz

theorem leaf_734_ok : checkAt 527 1000 box_734 cert_734 = true := by
  have h := List.all_eq_true.mp batch_14_20_ok accepted_734 (by simp [batch_14_20_values])
  exact h
theorem leaf_734_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_734.profileLo box_734.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_734_ok
theorem branch_box_734_nonnegative : ∀ j, 0 ≤ branch_box_734.lower j ∧ 0 ≤ branch_box_734.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_734, Box.profileLo, Box.profileHi, box_734]
theorem leaf_734_BranchSafe : CertificateConsequences.BranchSafe branch_box_734 := by
  left; refine ⟨branch_box_734_nonnegative, ?_⟩
  intro z hz; exact leaf_734_sound hz

#print axioms batch_14_00_ok
#print axioms leaf_701_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
