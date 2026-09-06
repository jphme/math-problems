import PeaceableQueens.UpperBound.Generated.Even.C527Scaled54Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_54_00_values : List Bool := [accepted_2700]
theorem batch_54_00_ok : batch_54_00_values.all id = true := by decide

def batch_54_01_values : List Bool := [accepted_2701]
theorem batch_54_01_ok : batch_54_01_values.all id = true := by decide

def batch_54_02_values : List Bool := [accepted_2703]
theorem batch_54_02_ok : batch_54_02_values.all id = true := by decide

def batch_54_03_values : List Bool := [accepted_2704]
theorem batch_54_03_ok : batch_54_03_values.all id = true := by decide

def batch_54_04_values : List Bool := [accepted_2707]
theorem batch_54_04_ok : batch_54_04_values.all id = true := by decide

def batch_54_05_values : List Bool := [accepted_2708]
theorem batch_54_05_ok : batch_54_05_values.all id = true := by decide

def batch_54_06_values : List Bool := [accepted_2709]
theorem batch_54_06_ok : batch_54_06_values.all id = true := by decide

def batch_54_07_values : List Bool := [accepted_2710]
theorem batch_54_07_ok : batch_54_07_values.all id = true := by decide

def batch_54_08_values : List Bool := [accepted_2713]
theorem batch_54_08_ok : batch_54_08_values.all id = true := by decide

def batch_54_09_values : List Bool := [accepted_2717]
theorem batch_54_09_ok : batch_54_09_values.all id = true := by decide

def batch_54_10_values : List Bool := [accepted_2719]
theorem batch_54_10_ok : batch_54_10_values.all id = true := by decide

def batch_54_11_values : List Bool := [accepted_2720]
theorem batch_54_11_ok : batch_54_11_values.all id = true := by decide

def batch_54_12_values : List Bool := [accepted_2721]
theorem batch_54_12_ok : batch_54_12_values.all id = true := by decide

def batch_54_13_values : List Bool := [accepted_2725]
theorem batch_54_13_ok : batch_54_13_values.all id = true := by decide

def batch_54_14_values : List Bool := [accepted_2727]
theorem batch_54_14_ok : batch_54_14_values.all id = true := by decide

def batch_54_15_values : List Bool := [accepted_2728]
theorem batch_54_15_ok : batch_54_15_values.all id = true := by decide

def batch_54_16_values : List Bool := [accepted_2729]
theorem batch_54_16_ok : batch_54_16_values.all id = true := by decide

def batch_54_17_values : List Bool := [accepted_2732]
theorem batch_54_17_ok : batch_54_17_values.all id = true := by decide

def batch_54_18_values : List Bool := [accepted_2733]
theorem batch_54_18_ok : batch_54_18_values.all id = true := by decide

def batch_54_19_values : List Bool := [accepted_2734]
theorem batch_54_19_ok : batch_54_19_values.all id = true := by decide

def batch_54_20_values : List Bool := [accepted_2735]
theorem batch_54_20_ok : batch_54_20_values.all id = true := by decide

def batch_54_21_values : List Bool := [accepted_2738]
theorem batch_54_21_ok : batch_54_21_values.all id = true := by decide

def batch_54_22_values : List Bool := [accepted_2740]
theorem batch_54_22_ok : batch_54_22_values.all id = true := by decide

def batch_54_23_values : List Bool := [accepted_2741]
theorem batch_54_23_ok : batch_54_23_values.all id = true := by decide

def batch_54_24_values : List Bool := [accepted_2742]
theorem batch_54_24_ok : batch_54_24_values.all id = true := by decide

def batch_54_25_values : List Bool := [accepted_2749]
theorem batch_54_25_ok : batch_54_25_values.all id = true := by decide

theorem leaf_2700_ok : checkAt 527 1000 box_2700 cert_2700 = true := by
  have h := List.all_eq_true.mp batch_54_00_ok accepted_2700 (by simp [batch_54_00_values])
  exact h
theorem leaf_2700_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2700.profileLo box_2700.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2700_ok
theorem branch_box_2700_nonnegative : ∀ j, 0 ≤ branch_box_2700.lower j ∧ 0 ≤ branch_box_2700.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2700, Box.profileLo, Box.profileHi, box_2700]
theorem leaf_2700_BranchSafe : CertificateConsequences.BranchSafe branch_box_2700 := by
  left; refine ⟨branch_box_2700_nonnegative, ?_⟩
  intro z hz; exact leaf_2700_sound hz

theorem leaf_2701_ok : checkAt 527 1000 box_2701 cert_2701 = true := by
  have h := List.all_eq_true.mp batch_54_01_ok accepted_2701 (by simp [batch_54_01_values])
  exact h
theorem leaf_2701_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2701.profileLo box_2701.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2701_ok
theorem branch_box_2701_nonnegative : ∀ j, 0 ≤ branch_box_2701.lower j ∧ 0 ≤ branch_box_2701.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2701, Box.profileLo, Box.profileHi, box_2701]
theorem leaf_2701_BranchSafe : CertificateConsequences.BranchSafe branch_box_2701 := by
  left; refine ⟨branch_box_2701_nonnegative, ?_⟩
  intro z hz; exact leaf_2701_sound hz

theorem leaf_2703_ok : checkAt 527 1000 box_2703 cert_2703 = true := by
  have h := List.all_eq_true.mp batch_54_02_ok accepted_2703 (by simp [batch_54_02_values])
  exact h
theorem leaf_2703_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2703.profileLo box_2703.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2703_ok
theorem branch_box_2703_nonnegative : ∀ j, 0 ≤ branch_box_2703.lower j ∧ 0 ≤ branch_box_2703.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2703, Box.profileLo, Box.profileHi, box_2703]
theorem leaf_2703_BranchSafe : CertificateConsequences.BranchSafe branch_box_2703 := by
  left; refine ⟨branch_box_2703_nonnegative, ?_⟩
  intro z hz; exact leaf_2703_sound hz

theorem leaf_2704_ok : checkAt 527 1000 box_2704 cert_2704 = true := by
  have h := List.all_eq_true.mp batch_54_03_ok accepted_2704 (by simp [batch_54_03_values])
  exact h
theorem leaf_2704_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2704.profileLo box_2704.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2704_ok
theorem branch_box_2704_nonnegative : ∀ j, 0 ≤ branch_box_2704.lower j ∧ 0 ≤ branch_box_2704.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2704, Box.profileLo, Box.profileHi, box_2704]
theorem leaf_2704_BranchSafe : CertificateConsequences.BranchSafe branch_box_2704 := by
  left; refine ⟨branch_box_2704_nonnegative, ?_⟩
  intro z hz; exact leaf_2704_sound hz

theorem leaf_2707_ok : checkAt 527 1000 box_2707 cert_2707 = true := by
  have h := List.all_eq_true.mp batch_54_04_ok accepted_2707 (by simp [batch_54_04_values])
  exact h
theorem leaf_2707_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2707.profileLo box_2707.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2707_ok
theorem branch_box_2707_nonnegative : ∀ j, 0 ≤ branch_box_2707.lower j ∧ 0 ≤ branch_box_2707.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2707, Box.profileLo, Box.profileHi, box_2707]
theorem leaf_2707_BranchSafe : CertificateConsequences.BranchSafe branch_box_2707 := by
  left; refine ⟨branch_box_2707_nonnegative, ?_⟩
  intro z hz; exact leaf_2707_sound hz

theorem leaf_2708_ok : checkAt 527 1000 box_2708 cert_2708 = true := by
  have h := List.all_eq_true.mp batch_54_05_ok accepted_2708 (by simp [batch_54_05_values])
  exact h
theorem leaf_2708_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2708.profileLo box_2708.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2708_ok
theorem branch_box_2708_nonnegative : ∀ j, 0 ≤ branch_box_2708.lower j ∧ 0 ≤ branch_box_2708.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2708, Box.profileLo, Box.profileHi, box_2708]
theorem leaf_2708_BranchSafe : CertificateConsequences.BranchSafe branch_box_2708 := by
  left; refine ⟨branch_box_2708_nonnegative, ?_⟩
  intro z hz; exact leaf_2708_sound hz

theorem leaf_2709_ok : checkAt 527 1000 box_2709 cert_2709 = true := by
  have h := List.all_eq_true.mp batch_54_06_ok accepted_2709 (by simp [batch_54_06_values])
  exact h
theorem leaf_2709_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2709.profileLo box_2709.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2709_ok
theorem branch_box_2709_nonnegative : ∀ j, 0 ≤ branch_box_2709.lower j ∧ 0 ≤ branch_box_2709.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2709, Box.profileLo, Box.profileHi, box_2709]
theorem leaf_2709_BranchSafe : CertificateConsequences.BranchSafe branch_box_2709 := by
  left; refine ⟨branch_box_2709_nonnegative, ?_⟩
  intro z hz; exact leaf_2709_sound hz

theorem leaf_2710_ok : checkAt 527 1000 box_2710 cert_2710 = true := by
  have h := List.all_eq_true.mp batch_54_07_ok accepted_2710 (by simp [batch_54_07_values])
  exact h
theorem leaf_2710_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2710.profileLo box_2710.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2710_ok
theorem branch_box_2710_nonnegative : ∀ j, 0 ≤ branch_box_2710.lower j ∧ 0 ≤ branch_box_2710.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2710, Box.profileLo, Box.profileHi, box_2710]
theorem leaf_2710_BranchSafe : CertificateConsequences.BranchSafe branch_box_2710 := by
  left; refine ⟨branch_box_2710_nonnegative, ?_⟩
  intro z hz; exact leaf_2710_sound hz

theorem leaf_2713_ok : checkAt 527 1000 box_2713 cert_2713 = true := by
  have h := List.all_eq_true.mp batch_54_08_ok accepted_2713 (by simp [batch_54_08_values])
  exact h
theorem leaf_2713_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2713.profileLo box_2713.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2713_ok
theorem branch_box_2713_nonnegative : ∀ j, 0 ≤ branch_box_2713.lower j ∧ 0 ≤ branch_box_2713.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2713, Box.profileLo, Box.profileHi, box_2713]
theorem leaf_2713_BranchSafe : CertificateConsequences.BranchSafe branch_box_2713 := by
  left; refine ⟨branch_box_2713_nonnegative, ?_⟩
  intro z hz; exact leaf_2713_sound hz

theorem leaf_2717_ok : checkAt 527 1000 box_2717 cert_2717 = true := by
  have h := List.all_eq_true.mp batch_54_09_ok accepted_2717 (by simp [batch_54_09_values])
  exact h
theorem leaf_2717_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2717.profileLo box_2717.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2717_ok
theorem branch_box_2717_nonnegative : ∀ j, 0 ≤ branch_box_2717.lower j ∧ 0 ≤ branch_box_2717.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2717, Box.profileLo, Box.profileHi, box_2717]
theorem leaf_2717_BranchSafe : CertificateConsequences.BranchSafe branch_box_2717 := by
  left; refine ⟨branch_box_2717_nonnegative, ?_⟩
  intro z hz; exact leaf_2717_sound hz

theorem leaf_2719_ok : checkAt 527 1000 box_2719 cert_2719 = true := by
  have h := List.all_eq_true.mp batch_54_10_ok accepted_2719 (by simp [batch_54_10_values])
  exact h
theorem leaf_2719_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2719.profileLo box_2719.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2719_ok
theorem branch_box_2719_nonnegative : ∀ j, 0 ≤ branch_box_2719.lower j ∧ 0 ≤ branch_box_2719.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2719, Box.profileLo, Box.profileHi, box_2719]
theorem leaf_2719_BranchSafe : CertificateConsequences.BranchSafe branch_box_2719 := by
  left; refine ⟨branch_box_2719_nonnegative, ?_⟩
  intro z hz; exact leaf_2719_sound hz

theorem leaf_2720_ok : checkAt 527 1000 box_2720 cert_2720 = true := by
  have h := List.all_eq_true.mp batch_54_11_ok accepted_2720 (by simp [batch_54_11_values])
  exact h
theorem leaf_2720_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2720.profileLo box_2720.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2720_ok
theorem branch_box_2720_nonnegative : ∀ j, 0 ≤ branch_box_2720.lower j ∧ 0 ≤ branch_box_2720.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2720, Box.profileLo, Box.profileHi, box_2720]
theorem leaf_2720_BranchSafe : CertificateConsequences.BranchSafe branch_box_2720 := by
  left; refine ⟨branch_box_2720_nonnegative, ?_⟩
  intro z hz; exact leaf_2720_sound hz

theorem leaf_2721_ok : checkAt 527 1000 box_2721 cert_2721 = true := by
  have h := List.all_eq_true.mp batch_54_12_ok accepted_2721 (by simp [batch_54_12_values])
  exact h
theorem leaf_2721_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2721.profileLo box_2721.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2721_ok
theorem branch_box_2721_nonnegative : ∀ j, 0 ≤ branch_box_2721.lower j ∧ 0 ≤ branch_box_2721.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2721, Box.profileLo, Box.profileHi, box_2721]
theorem leaf_2721_BranchSafe : CertificateConsequences.BranchSafe branch_box_2721 := by
  left; refine ⟨branch_box_2721_nonnegative, ?_⟩
  intro z hz; exact leaf_2721_sound hz

theorem leaf_2725_ok : checkAt 527 1000 box_2725 cert_2725 = true := by
  have h := List.all_eq_true.mp batch_54_13_ok accepted_2725 (by simp [batch_54_13_values])
  exact h
theorem leaf_2725_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2725.profileLo box_2725.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2725_ok
theorem branch_box_2725_nonnegative : ∀ j, 0 ≤ branch_box_2725.lower j ∧ 0 ≤ branch_box_2725.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2725, Box.profileLo, Box.profileHi, box_2725]
theorem leaf_2725_BranchSafe : CertificateConsequences.BranchSafe branch_box_2725 := by
  left; refine ⟨branch_box_2725_nonnegative, ?_⟩
  intro z hz; exact leaf_2725_sound hz

theorem leaf_2727_ok : checkAt 527 1000 box_2727 cert_2727 = true := by
  have h := List.all_eq_true.mp batch_54_14_ok accepted_2727 (by simp [batch_54_14_values])
  exact h
theorem leaf_2727_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2727.profileLo box_2727.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2727_ok
theorem branch_box_2727_nonnegative : ∀ j, 0 ≤ branch_box_2727.lower j ∧ 0 ≤ branch_box_2727.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2727, Box.profileLo, Box.profileHi, box_2727]
theorem leaf_2727_BranchSafe : CertificateConsequences.BranchSafe branch_box_2727 := by
  left; refine ⟨branch_box_2727_nonnegative, ?_⟩
  intro z hz; exact leaf_2727_sound hz

theorem leaf_2728_ok : checkAt 527 1000 box_2728 cert_2728 = true := by
  have h := List.all_eq_true.mp batch_54_15_ok accepted_2728 (by simp [batch_54_15_values])
  exact h
theorem leaf_2728_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2728.profileLo box_2728.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2728_ok
theorem branch_box_2728_nonnegative : ∀ j, 0 ≤ branch_box_2728.lower j ∧ 0 ≤ branch_box_2728.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2728, Box.profileLo, Box.profileHi, box_2728]
theorem leaf_2728_BranchSafe : CertificateConsequences.BranchSafe branch_box_2728 := by
  left; refine ⟨branch_box_2728_nonnegative, ?_⟩
  intro z hz; exact leaf_2728_sound hz

theorem leaf_2729_ok : checkAt 527 1000 box_2729 cert_2729 = true := by
  have h := List.all_eq_true.mp batch_54_16_ok accepted_2729 (by simp [batch_54_16_values])
  exact h
theorem leaf_2729_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2729.profileLo box_2729.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2729_ok
theorem branch_box_2729_nonnegative : ∀ j, 0 ≤ branch_box_2729.lower j ∧ 0 ≤ branch_box_2729.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2729, Box.profileLo, Box.profileHi, box_2729]
theorem leaf_2729_BranchSafe : CertificateConsequences.BranchSafe branch_box_2729 := by
  left; refine ⟨branch_box_2729_nonnegative, ?_⟩
  intro z hz; exact leaf_2729_sound hz

theorem leaf_2732_ok : checkAt 527 1000 box_2732 cert_2732 = true := by
  have h := List.all_eq_true.mp batch_54_17_ok accepted_2732 (by simp [batch_54_17_values])
  exact h
theorem leaf_2732_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2732.profileLo box_2732.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2732_ok
theorem branch_box_2732_nonnegative : ∀ j, 0 ≤ branch_box_2732.lower j ∧ 0 ≤ branch_box_2732.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2732, Box.profileLo, Box.profileHi, box_2732]
theorem leaf_2732_BranchSafe : CertificateConsequences.BranchSafe branch_box_2732 := by
  left; refine ⟨branch_box_2732_nonnegative, ?_⟩
  intro z hz; exact leaf_2732_sound hz

theorem leaf_2733_ok : checkAt 527 1000 box_2733 cert_2733 = true := by
  have h := List.all_eq_true.mp batch_54_18_ok accepted_2733 (by simp [batch_54_18_values])
  exact h
theorem leaf_2733_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2733.profileLo box_2733.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2733_ok
theorem branch_box_2733_nonnegative : ∀ j, 0 ≤ branch_box_2733.lower j ∧ 0 ≤ branch_box_2733.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2733, Box.profileLo, Box.profileHi, box_2733]
theorem leaf_2733_BranchSafe : CertificateConsequences.BranchSafe branch_box_2733 := by
  left; refine ⟨branch_box_2733_nonnegative, ?_⟩
  intro z hz; exact leaf_2733_sound hz

theorem leaf_2734_ok : checkAt 527 1000 box_2734 cert_2734 = true := by
  have h := List.all_eq_true.mp batch_54_19_ok accepted_2734 (by simp [batch_54_19_values])
  exact h
theorem leaf_2734_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2734.profileLo box_2734.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2734_ok
theorem branch_box_2734_nonnegative : ∀ j, 0 ≤ branch_box_2734.lower j ∧ 0 ≤ branch_box_2734.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2734, Box.profileLo, Box.profileHi, box_2734]
theorem leaf_2734_BranchSafe : CertificateConsequences.BranchSafe branch_box_2734 := by
  left; refine ⟨branch_box_2734_nonnegative, ?_⟩
  intro z hz; exact leaf_2734_sound hz

theorem leaf_2735_ok : checkAt 527 1000 box_2735 cert_2735 = true := by
  have h := List.all_eq_true.mp batch_54_20_ok accepted_2735 (by simp [batch_54_20_values])
  exact h
theorem leaf_2735_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2735.profileLo box_2735.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2735_ok
theorem branch_box_2735_nonnegative : ∀ j, 0 ≤ branch_box_2735.lower j ∧ 0 ≤ branch_box_2735.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2735, Box.profileLo, Box.profileHi, box_2735]
theorem leaf_2735_BranchSafe : CertificateConsequences.BranchSafe branch_box_2735 := by
  left; refine ⟨branch_box_2735_nonnegative, ?_⟩
  intro z hz; exact leaf_2735_sound hz

theorem leaf_2738_ok : checkAt 527 1000 box_2738 cert_2738 = true := by
  have h := List.all_eq_true.mp batch_54_21_ok accepted_2738 (by simp [batch_54_21_values])
  exact h
theorem leaf_2738_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2738.profileLo box_2738.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2738_ok
theorem branch_box_2738_nonnegative : ∀ j, 0 ≤ branch_box_2738.lower j ∧ 0 ≤ branch_box_2738.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2738, Box.profileLo, Box.profileHi, box_2738]
theorem leaf_2738_BranchSafe : CertificateConsequences.BranchSafe branch_box_2738 := by
  left; refine ⟨branch_box_2738_nonnegative, ?_⟩
  intro z hz; exact leaf_2738_sound hz

theorem leaf_2740_ok : checkAt 527 1000 box_2740 cert_2740 = true := by
  have h := List.all_eq_true.mp batch_54_22_ok accepted_2740 (by simp [batch_54_22_values])
  exact h
theorem leaf_2740_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2740.profileLo box_2740.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2740_ok
theorem branch_box_2740_nonnegative : ∀ j, 0 ≤ branch_box_2740.lower j ∧ 0 ≤ branch_box_2740.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2740, Box.profileLo, Box.profileHi, box_2740]
theorem leaf_2740_BranchSafe : CertificateConsequences.BranchSafe branch_box_2740 := by
  left; refine ⟨branch_box_2740_nonnegative, ?_⟩
  intro z hz; exact leaf_2740_sound hz

theorem leaf_2741_ok : checkAt 527 1000 box_2741 cert_2741 = true := by
  have h := List.all_eq_true.mp batch_54_23_ok accepted_2741 (by simp [batch_54_23_values])
  exact h
theorem leaf_2741_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2741.profileLo box_2741.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2741_ok
theorem branch_box_2741_nonnegative : ∀ j, 0 ≤ branch_box_2741.lower j ∧ 0 ≤ branch_box_2741.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2741, Box.profileLo, Box.profileHi, box_2741]
theorem leaf_2741_BranchSafe : CertificateConsequences.BranchSafe branch_box_2741 := by
  left; refine ⟨branch_box_2741_nonnegative, ?_⟩
  intro z hz; exact leaf_2741_sound hz

theorem leaf_2742_ok : checkAt 527 1000 box_2742 cert_2742 = true := by
  have h := List.all_eq_true.mp batch_54_24_ok accepted_2742 (by simp [batch_54_24_values])
  exact h
theorem leaf_2742_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2742.profileLo box_2742.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2742_ok
theorem branch_box_2742_nonnegative : ∀ j, 0 ≤ branch_box_2742.lower j ∧ 0 ≤ branch_box_2742.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2742, Box.profileLo, Box.profileHi, box_2742]
theorem leaf_2742_BranchSafe : CertificateConsequences.BranchSafe branch_box_2742 := by
  left; refine ⟨branch_box_2742_nonnegative, ?_⟩
  intro z hz; exact leaf_2742_sound hz

theorem leaf_2749_ok : checkAt 527 1000 box_2749 cert_2749 = true := by
  have h := List.all_eq_true.mp batch_54_25_ok accepted_2749 (by simp [batch_54_25_values])
  exact h
theorem leaf_2749_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2749.profileLo box_2749.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2749_ok
theorem branch_box_2749_nonnegative : ∀ j, 0 ≤ branch_box_2749.lower j ∧ 0 ≤ branch_box_2749.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2749, Box.profileLo, Box.profileHi, box_2749]
theorem leaf_2749_BranchSafe : CertificateConsequences.BranchSafe branch_box_2749 := by
  left; refine ⟨branch_box_2749_nonnegative, ?_⟩
  intro z hz; exact leaf_2749_sound hz

#print axioms batch_54_00_ok
#print axioms leaf_2700_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
