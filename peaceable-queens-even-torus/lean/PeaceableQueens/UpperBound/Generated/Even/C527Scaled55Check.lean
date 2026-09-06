import PeaceableQueens.UpperBound.Generated.Even.C527Scaled55Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_55_00_values : List Bool := [accepted_2751]
theorem batch_55_00_ok : batch_55_00_values.all id = true := by decide

def batch_55_01_values : List Bool := [accepted_2752]
theorem batch_55_01_ok : batch_55_01_values.all id = true := by decide

def batch_55_02_values : List Bool := [accepted_2754]
theorem batch_55_02_ok : batch_55_02_values.all id = true := by decide

def batch_55_03_values : List Bool := [accepted_2755]
theorem batch_55_03_ok : batch_55_03_values.all id = true := by decide

def batch_55_04_values : List Bool := [accepted_2756]
theorem batch_55_04_ok : batch_55_04_values.all id = true := by decide

def batch_55_05_values : List Bool := [accepted_2759]
theorem batch_55_05_ok : batch_55_05_values.all id = true := by decide

def batch_55_06_values : List Bool := [accepted_2760]
theorem batch_55_06_ok : batch_55_06_values.all id = true := by decide

def batch_55_07_values : List Bool := [accepted_2761]
theorem batch_55_07_ok : batch_55_07_values.all id = true := by decide

def batch_55_08_values : List Bool := [accepted_2762]
theorem batch_55_08_ok : batch_55_08_values.all id = true := by decide

def batch_55_09_values : List Bool := [accepted_2767]
theorem batch_55_09_ok : batch_55_09_values.all id = true := by decide

def batch_55_10_values : List Bool := [accepted_2769]
theorem batch_55_10_ok : batch_55_10_values.all id = true := by decide

def batch_55_11_values : List Bool := [accepted_2770]
theorem batch_55_11_ok : batch_55_11_values.all id = true := by decide

def batch_55_12_values : List Bool := [accepted_2772]
theorem batch_55_12_ok : batch_55_12_values.all id = true := by decide

def batch_55_13_values : List Bool := [accepted_2773]
theorem batch_55_13_ok : batch_55_13_values.all id = true := by decide

def batch_55_14_values : List Bool := [accepted_2774]
theorem batch_55_14_ok : batch_55_14_values.all id = true := by decide

def batch_55_15_values : List Bool := [accepted_2778]
theorem batch_55_15_ok : batch_55_15_values.all id = true := by decide

def batch_55_16_values : List Bool := [accepted_2780]
theorem batch_55_16_ok : batch_55_16_values.all id = true := by decide

def batch_55_17_values : List Bool := [accepted_2781]
theorem batch_55_17_ok : batch_55_17_values.all id = true := by decide

def batch_55_18_values : List Bool := [accepted_2783]
theorem batch_55_18_ok : batch_55_18_values.all id = true := by decide

def batch_55_19_values : List Bool := [accepted_2784]
theorem batch_55_19_ok : batch_55_19_values.all id = true := by decide

def batch_55_20_values : List Bool := [accepted_2786]
theorem batch_55_20_ok : batch_55_20_values.all id = true := by decide

def batch_55_21_values : List Bool := [accepted_2788]
theorem batch_55_21_ok : batch_55_21_values.all id = true := by decide

def batch_55_22_values : List Bool := [accepted_2792]
theorem batch_55_22_ok : batch_55_22_values.all id = true := by decide

def batch_55_23_values : List Bool := [accepted_2793]
theorem batch_55_23_ok : batch_55_23_values.all id = true := by decide

def batch_55_24_values : List Bool := [accepted_2794]
theorem batch_55_24_ok : batch_55_24_values.all id = true := by decide

def batch_55_25_values : List Bool := [accepted_2795]
theorem batch_55_25_ok : batch_55_25_values.all id = true := by decide

def batch_55_26_values : List Bool := [accepted_2796]
theorem batch_55_26_ok : batch_55_26_values.all id = true := by decide

theorem leaf_2751_ok : checkAt 527 1000 box_2751 cert_2751 = true := by
  have h := List.all_eq_true.mp batch_55_00_ok accepted_2751 (by simp [batch_55_00_values])
  exact h
theorem leaf_2751_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2751.profileLo box_2751.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2751_ok
theorem branch_box_2751_nonnegative : ∀ j, 0 ≤ branch_box_2751.lower j ∧ 0 ≤ branch_box_2751.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2751, Box.profileLo, Box.profileHi, box_2751]
theorem leaf_2751_BranchSafe : CertificateConsequences.BranchSafe branch_box_2751 := by
  left; refine ⟨branch_box_2751_nonnegative, ?_⟩
  intro z hz; exact leaf_2751_sound hz

theorem leaf_2752_ok : checkAt 527 1000 box_2752 cert_2752 = true := by
  have h := List.all_eq_true.mp batch_55_01_ok accepted_2752 (by simp [batch_55_01_values])
  exact h
theorem leaf_2752_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2752.profileLo box_2752.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2752_ok
theorem branch_box_2752_nonnegative : ∀ j, 0 ≤ branch_box_2752.lower j ∧ 0 ≤ branch_box_2752.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2752, Box.profileLo, Box.profileHi, box_2752]
theorem leaf_2752_BranchSafe : CertificateConsequences.BranchSafe branch_box_2752 := by
  left; refine ⟨branch_box_2752_nonnegative, ?_⟩
  intro z hz; exact leaf_2752_sound hz

theorem leaf_2754_ok : checkAt 527 1000 box_2754 cert_2754 = true := by
  have h := List.all_eq_true.mp batch_55_02_ok accepted_2754 (by simp [batch_55_02_values])
  exact h
theorem leaf_2754_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2754.profileLo box_2754.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2754_ok
theorem branch_box_2754_nonnegative : ∀ j, 0 ≤ branch_box_2754.lower j ∧ 0 ≤ branch_box_2754.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2754, Box.profileLo, Box.profileHi, box_2754]
theorem leaf_2754_BranchSafe : CertificateConsequences.BranchSafe branch_box_2754 := by
  left; refine ⟨branch_box_2754_nonnegative, ?_⟩
  intro z hz; exact leaf_2754_sound hz

theorem leaf_2755_ok : checkAt 527 1000 box_2755 cert_2755 = true := by
  have h := List.all_eq_true.mp batch_55_03_ok accepted_2755 (by simp [batch_55_03_values])
  exact h
theorem leaf_2755_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2755.profileLo box_2755.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2755_ok
theorem branch_box_2755_nonnegative : ∀ j, 0 ≤ branch_box_2755.lower j ∧ 0 ≤ branch_box_2755.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2755, Box.profileLo, Box.profileHi, box_2755]
theorem leaf_2755_BranchSafe : CertificateConsequences.BranchSafe branch_box_2755 := by
  left; refine ⟨branch_box_2755_nonnegative, ?_⟩
  intro z hz; exact leaf_2755_sound hz

theorem leaf_2756_ok : checkAt 527 1000 box_2756 cert_2756 = true := by
  have h := List.all_eq_true.mp batch_55_04_ok accepted_2756 (by simp [batch_55_04_values])
  exact h
theorem leaf_2756_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2756.profileLo box_2756.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2756_ok
theorem branch_box_2756_nonnegative : ∀ j, 0 ≤ branch_box_2756.lower j ∧ 0 ≤ branch_box_2756.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2756, Box.profileLo, Box.profileHi, box_2756]
theorem leaf_2756_BranchSafe : CertificateConsequences.BranchSafe branch_box_2756 := by
  left; refine ⟨branch_box_2756_nonnegative, ?_⟩
  intro z hz; exact leaf_2756_sound hz

theorem leaf_2759_ok : checkAt 527 1000 box_2759 cert_2759 = true := by
  have h := List.all_eq_true.mp batch_55_05_ok accepted_2759 (by simp [batch_55_05_values])
  exact h
theorem leaf_2759_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2759.profileLo box_2759.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2759_ok
theorem branch_box_2759_nonnegative : ∀ j, 0 ≤ branch_box_2759.lower j ∧ 0 ≤ branch_box_2759.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2759, Box.profileLo, Box.profileHi, box_2759]
theorem leaf_2759_BranchSafe : CertificateConsequences.BranchSafe branch_box_2759 := by
  left; refine ⟨branch_box_2759_nonnegative, ?_⟩
  intro z hz; exact leaf_2759_sound hz

theorem leaf_2760_ok : checkAt 527 1000 box_2760 cert_2760 = true := by
  have h := List.all_eq_true.mp batch_55_06_ok accepted_2760 (by simp [batch_55_06_values])
  exact h
theorem leaf_2760_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2760.profileLo box_2760.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2760_ok
theorem branch_box_2760_nonnegative : ∀ j, 0 ≤ branch_box_2760.lower j ∧ 0 ≤ branch_box_2760.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2760, Box.profileLo, Box.profileHi, box_2760]
theorem leaf_2760_BranchSafe : CertificateConsequences.BranchSafe branch_box_2760 := by
  left; refine ⟨branch_box_2760_nonnegative, ?_⟩
  intro z hz; exact leaf_2760_sound hz

theorem leaf_2761_ok : checkAt 527 1000 box_2761 cert_2761 = true := by
  have h := List.all_eq_true.mp batch_55_07_ok accepted_2761 (by simp [batch_55_07_values])
  exact h
theorem leaf_2761_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2761.profileLo box_2761.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2761_ok
theorem branch_box_2761_nonnegative : ∀ j, 0 ≤ branch_box_2761.lower j ∧ 0 ≤ branch_box_2761.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2761, Box.profileLo, Box.profileHi, box_2761]
theorem leaf_2761_BranchSafe : CertificateConsequences.BranchSafe branch_box_2761 := by
  left; refine ⟨branch_box_2761_nonnegative, ?_⟩
  intro z hz; exact leaf_2761_sound hz

theorem leaf_2762_ok : checkAt 527 1000 box_2762 cert_2762 = true := by
  have h := List.all_eq_true.mp batch_55_08_ok accepted_2762 (by simp [batch_55_08_values])
  exact h
theorem leaf_2762_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2762.profileLo box_2762.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2762_ok
theorem branch_box_2762_nonnegative : ∀ j, 0 ≤ branch_box_2762.lower j ∧ 0 ≤ branch_box_2762.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2762, Box.profileLo, Box.profileHi, box_2762]
theorem leaf_2762_BranchSafe : CertificateConsequences.BranchSafe branch_box_2762 := by
  left; refine ⟨branch_box_2762_nonnegative, ?_⟩
  intro z hz; exact leaf_2762_sound hz

theorem leaf_2767_ok : checkAt 527 1000 box_2767 cert_2767 = true := by
  have h := List.all_eq_true.mp batch_55_09_ok accepted_2767 (by simp [batch_55_09_values])
  exact h
theorem leaf_2767_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2767.profileLo box_2767.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2767_ok
theorem branch_box_2767_nonnegative : ∀ j, 0 ≤ branch_box_2767.lower j ∧ 0 ≤ branch_box_2767.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2767, Box.profileLo, Box.profileHi, box_2767]
theorem leaf_2767_BranchSafe : CertificateConsequences.BranchSafe branch_box_2767 := by
  left; refine ⟨branch_box_2767_nonnegative, ?_⟩
  intro z hz; exact leaf_2767_sound hz

theorem leaf_2769_ok : checkAt 527 1000 box_2769 cert_2769 = true := by
  have h := List.all_eq_true.mp batch_55_10_ok accepted_2769 (by simp [batch_55_10_values])
  exact h
theorem leaf_2769_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2769.profileLo box_2769.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2769_ok
theorem branch_box_2769_nonnegative : ∀ j, 0 ≤ branch_box_2769.lower j ∧ 0 ≤ branch_box_2769.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2769, Box.profileLo, Box.profileHi, box_2769]
theorem leaf_2769_BranchSafe : CertificateConsequences.BranchSafe branch_box_2769 := by
  left; refine ⟨branch_box_2769_nonnegative, ?_⟩
  intro z hz; exact leaf_2769_sound hz

theorem leaf_2770_ok : checkAt 527 1000 box_2770 cert_2770 = true := by
  have h := List.all_eq_true.mp batch_55_11_ok accepted_2770 (by simp [batch_55_11_values])
  exact h
theorem leaf_2770_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2770.profileLo box_2770.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2770_ok
theorem branch_box_2770_nonnegative : ∀ j, 0 ≤ branch_box_2770.lower j ∧ 0 ≤ branch_box_2770.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2770, Box.profileLo, Box.profileHi, box_2770]
theorem leaf_2770_BranchSafe : CertificateConsequences.BranchSafe branch_box_2770 := by
  left; refine ⟨branch_box_2770_nonnegative, ?_⟩
  intro z hz; exact leaf_2770_sound hz

theorem leaf_2772_ok : checkAt 527 1000 box_2772 cert_2772 = true := by
  have h := List.all_eq_true.mp batch_55_12_ok accepted_2772 (by simp [batch_55_12_values])
  exact h
theorem leaf_2772_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2772.profileLo box_2772.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2772_ok
theorem branch_box_2772_nonnegative : ∀ j, 0 ≤ branch_box_2772.lower j ∧ 0 ≤ branch_box_2772.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2772, Box.profileLo, Box.profileHi, box_2772]
theorem leaf_2772_BranchSafe : CertificateConsequences.BranchSafe branch_box_2772 := by
  left; refine ⟨branch_box_2772_nonnegative, ?_⟩
  intro z hz; exact leaf_2772_sound hz

theorem leaf_2773_ok : checkAt 527 1000 box_2773 cert_2773 = true := by
  have h := List.all_eq_true.mp batch_55_13_ok accepted_2773 (by simp [batch_55_13_values])
  exact h
theorem leaf_2773_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2773.profileLo box_2773.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2773_ok
theorem branch_box_2773_nonnegative : ∀ j, 0 ≤ branch_box_2773.lower j ∧ 0 ≤ branch_box_2773.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2773, Box.profileLo, Box.profileHi, box_2773]
theorem leaf_2773_BranchSafe : CertificateConsequences.BranchSafe branch_box_2773 := by
  left; refine ⟨branch_box_2773_nonnegative, ?_⟩
  intro z hz; exact leaf_2773_sound hz

theorem leaf_2774_ok : checkAt 527 1000 box_2774 cert_2774 = true := by
  have h := List.all_eq_true.mp batch_55_14_ok accepted_2774 (by simp [batch_55_14_values])
  exact h
theorem leaf_2774_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2774.profileLo box_2774.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2774_ok
theorem branch_box_2774_nonnegative : ∀ j, 0 ≤ branch_box_2774.lower j ∧ 0 ≤ branch_box_2774.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2774, Box.profileLo, Box.profileHi, box_2774]
theorem leaf_2774_BranchSafe : CertificateConsequences.BranchSafe branch_box_2774 := by
  left; refine ⟨branch_box_2774_nonnegative, ?_⟩
  intro z hz; exact leaf_2774_sound hz

theorem leaf_2778_ok : checkAt 527 1000 box_2778 cert_2778 = true := by
  have h := List.all_eq_true.mp batch_55_15_ok accepted_2778 (by simp [batch_55_15_values])
  exact h
theorem leaf_2778_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2778.profileLo box_2778.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2778_ok
theorem branch_box_2778_nonnegative : ∀ j, 0 ≤ branch_box_2778.lower j ∧ 0 ≤ branch_box_2778.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2778, Box.profileLo, Box.profileHi, box_2778]
theorem leaf_2778_BranchSafe : CertificateConsequences.BranchSafe branch_box_2778 := by
  left; refine ⟨branch_box_2778_nonnegative, ?_⟩
  intro z hz; exact leaf_2778_sound hz

theorem leaf_2780_ok : checkAt 527 1000 box_2780 cert_2780 = true := by
  have h := List.all_eq_true.mp batch_55_16_ok accepted_2780 (by simp [batch_55_16_values])
  exact h
theorem leaf_2780_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2780.profileLo box_2780.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2780_ok
theorem branch_box_2780_nonnegative : ∀ j, 0 ≤ branch_box_2780.lower j ∧ 0 ≤ branch_box_2780.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2780, Box.profileLo, Box.profileHi, box_2780]
theorem leaf_2780_BranchSafe : CertificateConsequences.BranchSafe branch_box_2780 := by
  left; refine ⟨branch_box_2780_nonnegative, ?_⟩
  intro z hz; exact leaf_2780_sound hz

theorem leaf_2781_ok : checkAt 527 1000 box_2781 cert_2781 = true := by
  have h := List.all_eq_true.mp batch_55_17_ok accepted_2781 (by simp [batch_55_17_values])
  exact h
theorem leaf_2781_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2781.profileLo box_2781.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2781_ok
theorem branch_box_2781_nonnegative : ∀ j, 0 ≤ branch_box_2781.lower j ∧ 0 ≤ branch_box_2781.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2781, Box.profileLo, Box.profileHi, box_2781]
theorem leaf_2781_BranchSafe : CertificateConsequences.BranchSafe branch_box_2781 := by
  left; refine ⟨branch_box_2781_nonnegative, ?_⟩
  intro z hz; exact leaf_2781_sound hz

theorem leaf_2783_ok : checkAt 527 1000 box_2783 cert_2783 = true := by
  have h := List.all_eq_true.mp batch_55_18_ok accepted_2783 (by simp [batch_55_18_values])
  exact h
theorem leaf_2783_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2783.profileLo box_2783.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2783_ok
theorem branch_box_2783_nonnegative : ∀ j, 0 ≤ branch_box_2783.lower j ∧ 0 ≤ branch_box_2783.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2783, Box.profileLo, Box.profileHi, box_2783]
theorem leaf_2783_BranchSafe : CertificateConsequences.BranchSafe branch_box_2783 := by
  left; refine ⟨branch_box_2783_nonnegative, ?_⟩
  intro z hz; exact leaf_2783_sound hz

theorem leaf_2784_ok : checkAt 527 1000 box_2784 cert_2784 = true := by
  have h := List.all_eq_true.mp batch_55_19_ok accepted_2784 (by simp [batch_55_19_values])
  exact h
theorem leaf_2784_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2784.profileLo box_2784.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2784_ok
theorem branch_box_2784_nonnegative : ∀ j, 0 ≤ branch_box_2784.lower j ∧ 0 ≤ branch_box_2784.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2784, Box.profileLo, Box.profileHi, box_2784]
theorem leaf_2784_BranchSafe : CertificateConsequences.BranchSafe branch_box_2784 := by
  left; refine ⟨branch_box_2784_nonnegative, ?_⟩
  intro z hz; exact leaf_2784_sound hz

theorem leaf_2786_ok : checkAt 527 1000 box_2786 cert_2786 = true := by
  have h := List.all_eq_true.mp batch_55_20_ok accepted_2786 (by simp [batch_55_20_values])
  exact h
theorem leaf_2786_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2786.profileLo box_2786.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2786_ok
theorem branch_box_2786_nonnegative : ∀ j, 0 ≤ branch_box_2786.lower j ∧ 0 ≤ branch_box_2786.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2786, Box.profileLo, Box.profileHi, box_2786]
theorem leaf_2786_BranchSafe : CertificateConsequences.BranchSafe branch_box_2786 := by
  left; refine ⟨branch_box_2786_nonnegative, ?_⟩
  intro z hz; exact leaf_2786_sound hz

theorem leaf_2788_ok : checkAt 527 1000 box_2788 cert_2788 = true := by
  have h := List.all_eq_true.mp batch_55_21_ok accepted_2788 (by simp [batch_55_21_values])
  exact h
theorem leaf_2788_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2788.profileLo box_2788.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2788_ok
theorem branch_box_2788_nonnegative : ∀ j, 0 ≤ branch_box_2788.lower j ∧ 0 ≤ branch_box_2788.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2788, Box.profileLo, Box.profileHi, box_2788]
theorem leaf_2788_BranchSafe : CertificateConsequences.BranchSafe branch_box_2788 := by
  left; refine ⟨branch_box_2788_nonnegative, ?_⟩
  intro z hz; exact leaf_2788_sound hz

theorem leaf_2792_ok : checkAt 527 1000 box_2792 cert_2792 = true := by
  have h := List.all_eq_true.mp batch_55_22_ok accepted_2792 (by simp [batch_55_22_values])
  exact h
theorem leaf_2792_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2792.profileLo box_2792.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2792_ok
theorem branch_box_2792_nonnegative : ∀ j, 0 ≤ branch_box_2792.lower j ∧ 0 ≤ branch_box_2792.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2792, Box.profileLo, Box.profileHi, box_2792]
theorem leaf_2792_BranchSafe : CertificateConsequences.BranchSafe branch_box_2792 := by
  left; refine ⟨branch_box_2792_nonnegative, ?_⟩
  intro z hz; exact leaf_2792_sound hz

theorem leaf_2793_ok : checkAt 527 1000 box_2793 cert_2793 = true := by
  have h := List.all_eq_true.mp batch_55_23_ok accepted_2793 (by simp [batch_55_23_values])
  exact h
theorem leaf_2793_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2793.profileLo box_2793.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2793_ok
theorem branch_box_2793_nonnegative : ∀ j, 0 ≤ branch_box_2793.lower j ∧ 0 ≤ branch_box_2793.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2793, Box.profileLo, Box.profileHi, box_2793]
theorem leaf_2793_BranchSafe : CertificateConsequences.BranchSafe branch_box_2793 := by
  left; refine ⟨branch_box_2793_nonnegative, ?_⟩
  intro z hz; exact leaf_2793_sound hz

theorem leaf_2794_ok : checkAt 527 1000 box_2794 cert_2794 = true := by
  have h := List.all_eq_true.mp batch_55_24_ok accepted_2794 (by simp [batch_55_24_values])
  exact h
theorem leaf_2794_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2794.profileLo box_2794.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2794_ok
theorem branch_box_2794_nonnegative : ∀ j, 0 ≤ branch_box_2794.lower j ∧ 0 ≤ branch_box_2794.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2794, Box.profileLo, Box.profileHi, box_2794]
theorem leaf_2794_BranchSafe : CertificateConsequences.BranchSafe branch_box_2794 := by
  left; refine ⟨branch_box_2794_nonnegative, ?_⟩
  intro z hz; exact leaf_2794_sound hz

theorem leaf_2795_ok : checkAt 527 1000 box_2795 cert_2795 = true := by
  have h := List.all_eq_true.mp batch_55_25_ok accepted_2795 (by simp [batch_55_25_values])
  exact h
theorem leaf_2795_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2795.profileLo box_2795.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2795_ok
theorem branch_box_2795_nonnegative : ∀ j, 0 ≤ branch_box_2795.lower j ∧ 0 ≤ branch_box_2795.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2795, Box.profileLo, Box.profileHi, box_2795]
theorem leaf_2795_BranchSafe : CertificateConsequences.BranchSafe branch_box_2795 := by
  left; refine ⟨branch_box_2795_nonnegative, ?_⟩
  intro z hz; exact leaf_2795_sound hz

theorem leaf_2796_ok : checkAt 527 1000 box_2796 cert_2796 = true := by
  have h := List.all_eq_true.mp batch_55_26_ok accepted_2796 (by simp [batch_55_26_values])
  exact h
theorem leaf_2796_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2796.profileLo box_2796.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2796_ok
theorem branch_box_2796_nonnegative : ∀ j, 0 ≤ branch_box_2796.lower j ∧ 0 ≤ branch_box_2796.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2796, Box.profileLo, Box.profileHi, box_2796]
theorem leaf_2796_BranchSafe : CertificateConsequences.BranchSafe branch_box_2796 := by
  left; refine ⟨branch_box_2796_nonnegative, ?_⟩
  intro z hz; exact leaf_2796_sound hz

#print axioms batch_55_00_ok
#print axioms leaf_2751_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
