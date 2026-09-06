import PeaceableQueens.UpperBound.Generated.Even.C527Scaled114Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_114_00_values : List Bool := [accepted_5700]
theorem batch_114_00_ok : batch_114_00_values.all id = true := by decide

def batch_114_01_values : List Bool := [accepted_5703]
theorem batch_114_01_ok : batch_114_01_values.all id = true := by decide

def batch_114_02_values : List Bool := [accepted_5704]
theorem batch_114_02_ok : batch_114_02_values.all id = true := by decide

def batch_114_03_values : List Bool := [accepted_5706]
theorem batch_114_03_ok : batch_114_03_values.all id = true := by decide

def batch_114_04_values : List Bool := [accepted_5707]
theorem batch_114_04_ok : batch_114_04_values.all id = true := by decide

def batch_114_05_values : List Bool := [accepted_5708]
theorem batch_114_05_ok : batch_114_05_values.all id = true := by decide

def batch_114_06_values : List Bool := [accepted_5718]
theorem batch_114_06_ok : batch_114_06_values.all id = true := by decide

def batch_114_07_values : List Bool := [accepted_5719]
theorem batch_114_07_ok : batch_114_07_values.all id = true := by decide

def batch_114_08_values : List Bool := [accepted_5720]
theorem batch_114_08_ok : batch_114_08_values.all id = true := by decide

def batch_114_09_values : List Bool := [accepted_5721]
theorem batch_114_09_ok : batch_114_09_values.all id = true := by decide

def batch_114_10_values : List Bool := [accepted_5723]
theorem batch_114_10_ok : batch_114_10_values.all id = true := by decide

def batch_114_11_values : List Bool := [accepted_5724]
theorem batch_114_11_ok : batch_114_11_values.all id = true := by decide

def batch_114_12_values : List Bool := [accepted_5729]
theorem batch_114_12_ok : batch_114_12_values.all id = true := by decide

def batch_114_13_values : List Bool := [accepted_5730]
theorem batch_114_13_ok : batch_114_13_values.all id = true := by decide

def batch_114_14_values : List Bool := [accepted_5731]
theorem batch_114_14_ok : batch_114_14_values.all id = true := by decide

def batch_114_15_values : List Bool := [accepted_5734]
theorem batch_114_15_ok : batch_114_15_values.all id = true := by decide

def batch_114_16_values : List Bool := [accepted_5735]
theorem batch_114_16_ok : batch_114_16_values.all id = true := by decide

def batch_114_17_values : List Bool := [accepted_5736]
theorem batch_114_17_ok : batch_114_17_values.all id = true := by decide

def batch_114_18_values : List Bool := [accepted_5737]
theorem batch_114_18_ok : batch_114_18_values.all id = true := by decide

def batch_114_19_values : List Bool := [accepted_5739]
theorem batch_114_19_ok : batch_114_19_values.all id = true := by decide

def batch_114_20_values : List Bool := [accepted_5743]
theorem batch_114_20_ok : batch_114_20_values.all id = true := by decide

def batch_114_21_values : List Bool := [accepted_5744]
theorem batch_114_21_ok : batch_114_21_values.all id = true := by decide

def batch_114_22_values : List Bool := [accepted_5749]
theorem batch_114_22_ok : batch_114_22_values.all id = true := by decide

theorem leaf_5700_ok : checkAt 527 1000 box_5700 cert_5700 = true := by
  have h := List.all_eq_true.mp batch_114_00_ok accepted_5700 (by simp [batch_114_00_values])
  exact h
theorem leaf_5700_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5700.profileLo box_5700.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5700_ok
theorem branch_box_5700_nonnegative : ∀ j, 0 ≤ branch_box_5700.lower j ∧ 0 ≤ branch_box_5700.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5700, Box.profileLo, Box.profileHi, box_5700]
theorem leaf_5700_BranchSafe : CertificateConsequences.BranchSafe branch_box_5700 := by
  left; refine ⟨branch_box_5700_nonnegative, ?_⟩
  intro z hz; exact leaf_5700_sound hz

theorem leaf_5703_ok : checkAt 527 1000 box_5703 cert_5703 = true := by
  have h := List.all_eq_true.mp batch_114_01_ok accepted_5703 (by simp [batch_114_01_values])
  exact h
theorem leaf_5703_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5703.profileLo box_5703.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5703_ok
theorem branch_box_5703_nonnegative : ∀ j, 0 ≤ branch_box_5703.lower j ∧ 0 ≤ branch_box_5703.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5703, Box.profileLo, Box.profileHi, box_5703]
theorem leaf_5703_BranchSafe : CertificateConsequences.BranchSafe branch_box_5703 := by
  left; refine ⟨branch_box_5703_nonnegative, ?_⟩
  intro z hz; exact leaf_5703_sound hz

theorem leaf_5704_ok : checkAt 527 1000 box_5704 cert_5704 = true := by
  have h := List.all_eq_true.mp batch_114_02_ok accepted_5704 (by simp [batch_114_02_values])
  exact h
theorem leaf_5704_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5704.profileLo box_5704.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5704_ok
theorem branch_box_5704_nonnegative : ∀ j, 0 ≤ branch_box_5704.lower j ∧ 0 ≤ branch_box_5704.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5704, Box.profileLo, Box.profileHi, box_5704]
theorem leaf_5704_BranchSafe : CertificateConsequences.BranchSafe branch_box_5704 := by
  left; refine ⟨branch_box_5704_nonnegative, ?_⟩
  intro z hz; exact leaf_5704_sound hz

theorem leaf_5706_ok : checkAt 527 1000 box_5706 cert_5706 = true := by
  have h := List.all_eq_true.mp batch_114_03_ok accepted_5706 (by simp [batch_114_03_values])
  exact h
theorem leaf_5706_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5706.profileLo box_5706.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5706_ok
theorem branch_box_5706_nonnegative : ∀ j, 0 ≤ branch_box_5706.lower j ∧ 0 ≤ branch_box_5706.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5706, Box.profileLo, Box.profileHi, box_5706]
theorem leaf_5706_BranchSafe : CertificateConsequences.BranchSafe branch_box_5706 := by
  left; refine ⟨branch_box_5706_nonnegative, ?_⟩
  intro z hz; exact leaf_5706_sound hz

theorem leaf_5707_ok : checkAt 527 1000 box_5707 cert_5707 = true := by
  have h := List.all_eq_true.mp batch_114_04_ok accepted_5707 (by simp [batch_114_04_values])
  exact h
theorem leaf_5707_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5707.profileLo box_5707.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5707_ok
theorem branch_box_5707_nonnegative : ∀ j, 0 ≤ branch_box_5707.lower j ∧ 0 ≤ branch_box_5707.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5707, Box.profileLo, Box.profileHi, box_5707]
theorem leaf_5707_BranchSafe : CertificateConsequences.BranchSafe branch_box_5707 := by
  left; refine ⟨branch_box_5707_nonnegative, ?_⟩
  intro z hz; exact leaf_5707_sound hz

theorem leaf_5708_ok : checkAt 527 1000 box_5708 cert_5708 = true := by
  have h := List.all_eq_true.mp batch_114_05_ok accepted_5708 (by simp [batch_114_05_values])
  exact h
theorem leaf_5708_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5708.profileLo box_5708.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5708_ok
theorem branch_box_5708_nonnegative : ∀ j, 0 ≤ branch_box_5708.lower j ∧ 0 ≤ branch_box_5708.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5708, Box.profileLo, Box.profileHi, box_5708]
theorem leaf_5708_BranchSafe : CertificateConsequences.BranchSafe branch_box_5708 := by
  left; refine ⟨branch_box_5708_nonnegative, ?_⟩
  intro z hz; exact leaf_5708_sound hz

theorem leaf_5718_ok : checkAt 527 1000 box_5718 cert_5718 = true := by
  have h := List.all_eq_true.mp batch_114_06_ok accepted_5718 (by simp [batch_114_06_values])
  exact h
theorem leaf_5718_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5718.profileLo box_5718.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5718_ok
theorem branch_box_5718_nonnegative : ∀ j, 0 ≤ branch_box_5718.lower j ∧ 0 ≤ branch_box_5718.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5718, Box.profileLo, Box.profileHi, box_5718]
theorem leaf_5718_BranchSafe : CertificateConsequences.BranchSafe branch_box_5718 := by
  left; refine ⟨branch_box_5718_nonnegative, ?_⟩
  intro z hz; exact leaf_5718_sound hz

theorem leaf_5719_ok : checkAt 527 1000 box_5719 cert_5719 = true := by
  have h := List.all_eq_true.mp batch_114_07_ok accepted_5719 (by simp [batch_114_07_values])
  exact h
theorem leaf_5719_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5719.profileLo box_5719.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5719_ok
theorem branch_box_5719_nonnegative : ∀ j, 0 ≤ branch_box_5719.lower j ∧ 0 ≤ branch_box_5719.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5719, Box.profileLo, Box.profileHi, box_5719]
theorem leaf_5719_BranchSafe : CertificateConsequences.BranchSafe branch_box_5719 := by
  left; refine ⟨branch_box_5719_nonnegative, ?_⟩
  intro z hz; exact leaf_5719_sound hz

theorem leaf_5720_ok : checkAt 527 1000 box_5720 cert_5720 = true := by
  have h := List.all_eq_true.mp batch_114_08_ok accepted_5720 (by simp [batch_114_08_values])
  exact h
theorem leaf_5720_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5720.profileLo box_5720.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5720_ok
theorem branch_box_5720_nonnegative : ∀ j, 0 ≤ branch_box_5720.lower j ∧ 0 ≤ branch_box_5720.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5720, Box.profileLo, Box.profileHi, box_5720]
theorem leaf_5720_BranchSafe : CertificateConsequences.BranchSafe branch_box_5720 := by
  left; refine ⟨branch_box_5720_nonnegative, ?_⟩
  intro z hz; exact leaf_5720_sound hz

theorem leaf_5721_ok : checkAt 527 1000 box_5721 cert_5721 = true := by
  have h := List.all_eq_true.mp batch_114_09_ok accepted_5721 (by simp [batch_114_09_values])
  exact h
theorem leaf_5721_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5721.profileLo box_5721.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5721_ok
theorem branch_box_5721_nonnegative : ∀ j, 0 ≤ branch_box_5721.lower j ∧ 0 ≤ branch_box_5721.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5721, Box.profileLo, Box.profileHi, box_5721]
theorem leaf_5721_BranchSafe : CertificateConsequences.BranchSafe branch_box_5721 := by
  left; refine ⟨branch_box_5721_nonnegative, ?_⟩
  intro z hz; exact leaf_5721_sound hz

theorem leaf_5723_ok : checkAt 527 1000 box_5723 cert_5723 = true := by
  have h := List.all_eq_true.mp batch_114_10_ok accepted_5723 (by simp [batch_114_10_values])
  exact h
theorem leaf_5723_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5723.profileLo box_5723.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5723_ok
theorem branch_box_5723_nonnegative : ∀ j, 0 ≤ branch_box_5723.lower j ∧ 0 ≤ branch_box_5723.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5723, Box.profileLo, Box.profileHi, box_5723]
theorem leaf_5723_BranchSafe : CertificateConsequences.BranchSafe branch_box_5723 := by
  left; refine ⟨branch_box_5723_nonnegative, ?_⟩
  intro z hz; exact leaf_5723_sound hz

theorem leaf_5724_ok : checkAt 527 1000 box_5724 cert_5724 = true := by
  have h := List.all_eq_true.mp batch_114_11_ok accepted_5724 (by simp [batch_114_11_values])
  exact h
theorem leaf_5724_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5724.profileLo box_5724.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5724_ok
theorem branch_box_5724_nonnegative : ∀ j, 0 ≤ branch_box_5724.lower j ∧ 0 ≤ branch_box_5724.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5724, Box.profileLo, Box.profileHi, box_5724]
theorem leaf_5724_BranchSafe : CertificateConsequences.BranchSafe branch_box_5724 := by
  left; refine ⟨branch_box_5724_nonnegative, ?_⟩
  intro z hz; exact leaf_5724_sound hz

theorem leaf_5729_ok : checkAt 527 1000 box_5729 cert_5729 = true := by
  have h := List.all_eq_true.mp batch_114_12_ok accepted_5729 (by simp [batch_114_12_values])
  exact h
theorem leaf_5729_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5729.profileLo box_5729.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5729_ok
theorem branch_box_5729_nonnegative : ∀ j, 0 ≤ branch_box_5729.lower j ∧ 0 ≤ branch_box_5729.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5729, Box.profileLo, Box.profileHi, box_5729]
theorem leaf_5729_BranchSafe : CertificateConsequences.BranchSafe branch_box_5729 := by
  left; refine ⟨branch_box_5729_nonnegative, ?_⟩
  intro z hz; exact leaf_5729_sound hz

theorem leaf_5730_ok : checkAt 527 1000 box_5730 cert_5730 = true := by
  have h := List.all_eq_true.mp batch_114_13_ok accepted_5730 (by simp [batch_114_13_values])
  exact h
theorem leaf_5730_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5730.profileLo box_5730.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5730_ok
theorem branch_box_5730_nonnegative : ∀ j, 0 ≤ branch_box_5730.lower j ∧ 0 ≤ branch_box_5730.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5730, Box.profileLo, Box.profileHi, box_5730]
theorem leaf_5730_BranchSafe : CertificateConsequences.BranchSafe branch_box_5730 := by
  left; refine ⟨branch_box_5730_nonnegative, ?_⟩
  intro z hz; exact leaf_5730_sound hz

theorem leaf_5731_ok : checkAt 527 1000 box_5731 cert_5731 = true := by
  have h := List.all_eq_true.mp batch_114_14_ok accepted_5731 (by simp [batch_114_14_values])
  exact h
theorem leaf_5731_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5731.profileLo box_5731.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5731_ok
theorem branch_box_5731_nonnegative : ∀ j, 0 ≤ branch_box_5731.lower j ∧ 0 ≤ branch_box_5731.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5731, Box.profileLo, Box.profileHi, box_5731]
theorem leaf_5731_BranchSafe : CertificateConsequences.BranchSafe branch_box_5731 := by
  left; refine ⟨branch_box_5731_nonnegative, ?_⟩
  intro z hz; exact leaf_5731_sound hz

theorem leaf_5734_ok : checkAt 527 1000 box_5734 cert_5734 = true := by
  have h := List.all_eq_true.mp batch_114_15_ok accepted_5734 (by simp [batch_114_15_values])
  exact h
theorem leaf_5734_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5734.profileLo box_5734.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5734_ok
theorem branch_box_5734_nonnegative : ∀ j, 0 ≤ branch_box_5734.lower j ∧ 0 ≤ branch_box_5734.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5734, Box.profileLo, Box.profileHi, box_5734]
theorem leaf_5734_BranchSafe : CertificateConsequences.BranchSafe branch_box_5734 := by
  left; refine ⟨branch_box_5734_nonnegative, ?_⟩
  intro z hz; exact leaf_5734_sound hz

theorem leaf_5735_ok : checkAt 527 1000 box_5735 cert_5735 = true := by
  have h := List.all_eq_true.mp batch_114_16_ok accepted_5735 (by simp [batch_114_16_values])
  exact h
theorem leaf_5735_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5735.profileLo box_5735.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5735_ok
theorem branch_box_5735_nonnegative : ∀ j, 0 ≤ branch_box_5735.lower j ∧ 0 ≤ branch_box_5735.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5735, Box.profileLo, Box.profileHi, box_5735]
theorem leaf_5735_BranchSafe : CertificateConsequences.BranchSafe branch_box_5735 := by
  left; refine ⟨branch_box_5735_nonnegative, ?_⟩
  intro z hz; exact leaf_5735_sound hz

theorem leaf_5736_ok : checkAt 527 1000 box_5736 cert_5736 = true := by
  have h := List.all_eq_true.mp batch_114_17_ok accepted_5736 (by simp [batch_114_17_values])
  exact h
theorem leaf_5736_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5736.profileLo box_5736.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5736_ok
theorem branch_box_5736_nonnegative : ∀ j, 0 ≤ branch_box_5736.lower j ∧ 0 ≤ branch_box_5736.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5736, Box.profileLo, Box.profileHi, box_5736]
theorem leaf_5736_BranchSafe : CertificateConsequences.BranchSafe branch_box_5736 := by
  left; refine ⟨branch_box_5736_nonnegative, ?_⟩
  intro z hz; exact leaf_5736_sound hz

theorem leaf_5737_ok : checkAt 527 1000 box_5737 cert_5737 = true := by
  have h := List.all_eq_true.mp batch_114_18_ok accepted_5737 (by simp [batch_114_18_values])
  exact h
theorem leaf_5737_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5737.profileLo box_5737.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5737_ok
theorem branch_box_5737_nonnegative : ∀ j, 0 ≤ branch_box_5737.lower j ∧ 0 ≤ branch_box_5737.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5737, Box.profileLo, Box.profileHi, box_5737]
theorem leaf_5737_BranchSafe : CertificateConsequences.BranchSafe branch_box_5737 := by
  left; refine ⟨branch_box_5737_nonnegative, ?_⟩
  intro z hz; exact leaf_5737_sound hz

theorem leaf_5739_ok : checkAt 527 1000 box_5739 cert_5739 = true := by
  have h := List.all_eq_true.mp batch_114_19_ok accepted_5739 (by simp [batch_114_19_values])
  exact h
theorem leaf_5739_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5739.profileLo box_5739.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5739_ok
theorem branch_box_5739_nonnegative : ∀ j, 0 ≤ branch_box_5739.lower j ∧ 0 ≤ branch_box_5739.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5739, Box.profileLo, Box.profileHi, box_5739]
theorem leaf_5739_BranchSafe : CertificateConsequences.BranchSafe branch_box_5739 := by
  left; refine ⟨branch_box_5739_nonnegative, ?_⟩
  intro z hz; exact leaf_5739_sound hz

theorem leaf_5743_ok : checkAt 527 1000 box_5743 cert_5743 = true := by
  have h := List.all_eq_true.mp batch_114_20_ok accepted_5743 (by simp [batch_114_20_values])
  exact h
theorem leaf_5743_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5743.profileLo box_5743.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5743_ok
theorem branch_box_5743_nonnegative : ∀ j, 0 ≤ branch_box_5743.lower j ∧ 0 ≤ branch_box_5743.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5743, Box.profileLo, Box.profileHi, box_5743]
theorem leaf_5743_BranchSafe : CertificateConsequences.BranchSafe branch_box_5743 := by
  left; refine ⟨branch_box_5743_nonnegative, ?_⟩
  intro z hz; exact leaf_5743_sound hz

theorem leaf_5744_ok : checkAt 527 1000 box_5744 cert_5744 = true := by
  have h := List.all_eq_true.mp batch_114_21_ok accepted_5744 (by simp [batch_114_21_values])
  exact h
theorem leaf_5744_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5744.profileLo box_5744.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5744_ok
theorem branch_box_5744_nonnegative : ∀ j, 0 ≤ branch_box_5744.lower j ∧ 0 ≤ branch_box_5744.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5744, Box.profileLo, Box.profileHi, box_5744]
theorem leaf_5744_BranchSafe : CertificateConsequences.BranchSafe branch_box_5744 := by
  left; refine ⟨branch_box_5744_nonnegative, ?_⟩
  intro z hz; exact leaf_5744_sound hz

theorem leaf_5749_ok : checkAt 527 1000 box_5749 cert_5749 = true := by
  have h := List.all_eq_true.mp batch_114_22_ok accepted_5749 (by simp [batch_114_22_values])
  exact h
theorem leaf_5749_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5749.profileLo box_5749.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5749_ok
theorem branch_box_5749_nonnegative : ∀ j, 0 ≤ branch_box_5749.lower j ∧ 0 ≤ branch_box_5749.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5749, Box.profileLo, Box.profileHi, box_5749]
theorem leaf_5749_BranchSafe : CertificateConsequences.BranchSafe branch_box_5749 := by
  left; refine ⟨branch_box_5749_nonnegative, ?_⟩
  intro z hz; exact leaf_5749_sound hz

#print axioms batch_114_00_ok
#print axioms leaf_5700_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
