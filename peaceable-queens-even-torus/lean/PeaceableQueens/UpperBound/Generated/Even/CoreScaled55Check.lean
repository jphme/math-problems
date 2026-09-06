import PeaceableQueens.UpperBound.Generated.Even.CoreScaled55Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_55_00_values : List Bool := [accepted_2750]
theorem batch_55_00_ok : batch_55_00_values.all id = true := by decide

def batch_55_01_values : List Bool := [accepted_2752]
theorem batch_55_01_ok : batch_55_01_values.all id = true := by decide

def batch_55_02_values : List Bool := [accepted_2765]
theorem batch_55_02_ok : batch_55_02_values.all id = true := by decide

def batch_55_03_values : List Bool := [accepted_2767]
theorem batch_55_03_ok : batch_55_03_values.all id = true := by decide

def batch_55_04_values : List Bool := [accepted_2769]
theorem batch_55_04_ok : batch_55_04_values.all id = true := by decide

def batch_55_05_values : List Bool := [accepted_2771]
theorem batch_55_05_ok : batch_55_05_values.all id = true := by decide

def batch_55_06_values : List Bool := [accepted_2775]
theorem batch_55_06_ok : batch_55_06_values.all id = true := by decide

def batch_55_07_values : List Bool := [accepted_2779]
theorem batch_55_07_ok : batch_55_07_values.all id = true := by decide

def batch_55_08_values : List Bool := [accepted_2781]
theorem batch_55_08_ok : batch_55_08_values.all id = true := by decide

def batch_55_09_values : List Bool := [accepted_2784]
theorem batch_55_09_ok : batch_55_09_values.all id = true := by decide

def batch_55_10_values : List Bool := [accepted_2785]
theorem batch_55_10_ok : batch_55_10_values.all id = true := by decide

def batch_55_11_values : List Bool := [accepted_2787]
theorem batch_55_11_ok : batch_55_11_values.all id = true := by decide

def batch_55_12_values : List Bool := [accepted_2789]
theorem batch_55_12_ok : batch_55_12_values.all id = true := by decide

def batch_55_13_values : List Bool := [accepted_2794]
theorem batch_55_13_ok : batch_55_13_values.all id = true := by decide

def batch_55_14_values : List Bool := [accepted_2796]
theorem batch_55_14_ok : batch_55_14_values.all id = true := by decide

def batch_55_15_values : List Bool := [accepted_2799]
theorem batch_55_15_ok : batch_55_15_values.all id = true := by decide

theorem leaf_2750_ok : checkAt 527 1000 box_2750 cert_2750 = true := by
  have h := List.all_eq_true.mp batch_55_00_ok accepted_2750 (by simp [batch_55_00_values])
  exact h
theorem leaf_2750_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2750.profileLo box_2750.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2750_ok
theorem branch_box_2750_nonnegative : ∀ j, 0 ≤ branch_box_2750.lower j ∧ 0 ≤ branch_box_2750.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2750, Box.profileLo, Box.profileHi, box_2750]
theorem leaf_2750_BranchSafe : CertificateConsequences.BranchSafe branch_box_2750 := by
  left; refine ⟨branch_box_2750_nonnegative, ?_⟩
  intro z hz; exact leaf_2750_sound hz

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

theorem leaf_2765_ok : checkAt 527 1000 box_2765 cert_2765 = true := by
  have h := List.all_eq_true.mp batch_55_02_ok accepted_2765 (by simp [batch_55_02_values])
  exact h
theorem leaf_2765_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2765.profileLo box_2765.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2765_ok
theorem branch_box_2765_nonnegative : ∀ j, 0 ≤ branch_box_2765.lower j ∧ 0 ≤ branch_box_2765.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2765, Box.profileLo, Box.profileHi, box_2765]
theorem leaf_2765_BranchSafe : CertificateConsequences.BranchSafe branch_box_2765 := by
  left; refine ⟨branch_box_2765_nonnegative, ?_⟩
  intro z hz; exact leaf_2765_sound hz

theorem leaf_2767_ok : checkAt 527 1000 box_2767 cert_2767 = true := by
  have h := List.all_eq_true.mp batch_55_03_ok accepted_2767 (by simp [batch_55_03_values])
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
  have h := List.all_eq_true.mp batch_55_04_ok accepted_2769 (by simp [batch_55_04_values])
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

theorem leaf_2771_ok : checkAt 527 1000 box_2771 cert_2771 = true := by
  have h := List.all_eq_true.mp batch_55_05_ok accepted_2771 (by simp [batch_55_05_values])
  exact h
theorem leaf_2771_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2771.profileLo box_2771.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2771_ok
theorem branch_box_2771_nonnegative : ∀ j, 0 ≤ branch_box_2771.lower j ∧ 0 ≤ branch_box_2771.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2771, Box.profileLo, Box.profileHi, box_2771]
theorem leaf_2771_BranchSafe : CertificateConsequences.BranchSafe branch_box_2771 := by
  left; refine ⟨branch_box_2771_nonnegative, ?_⟩
  intro z hz; exact leaf_2771_sound hz

theorem leaf_2775_ok : checkAt 527 1000 box_2775 cert_2775 = true := by
  have h := List.all_eq_true.mp batch_55_06_ok accepted_2775 (by simp [batch_55_06_values])
  exact h
theorem leaf_2775_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2775.profileLo box_2775.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2775_ok
theorem branch_box_2775_nonnegative : ∀ j, 0 ≤ branch_box_2775.lower j ∧ 0 ≤ branch_box_2775.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2775, Box.profileLo, Box.profileHi, box_2775]
theorem leaf_2775_BranchSafe : CertificateConsequences.BranchSafe branch_box_2775 := by
  left; refine ⟨branch_box_2775_nonnegative, ?_⟩
  intro z hz; exact leaf_2775_sound hz

theorem leaf_2779_ok : checkAt 527 1000 box_2779 cert_2779 = true := by
  have h := List.all_eq_true.mp batch_55_07_ok accepted_2779 (by simp [batch_55_07_values])
  exact h
theorem leaf_2779_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2779.profileLo box_2779.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2779_ok
theorem branch_box_2779_nonnegative : ∀ j, 0 ≤ branch_box_2779.lower j ∧ 0 ≤ branch_box_2779.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2779, Box.profileLo, Box.profileHi, box_2779]
theorem leaf_2779_BranchSafe : CertificateConsequences.BranchSafe branch_box_2779 := by
  left; refine ⟨branch_box_2779_nonnegative, ?_⟩
  intro z hz; exact leaf_2779_sound hz

theorem leaf_2781_ok : checkAt 527 1000 box_2781 cert_2781 = true := by
  have h := List.all_eq_true.mp batch_55_08_ok accepted_2781 (by simp [batch_55_08_values])
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

theorem leaf_2784_ok : checkAt 527 1000 box_2784 cert_2784 = true := by
  have h := List.all_eq_true.mp batch_55_09_ok accepted_2784 (by simp [batch_55_09_values])
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

theorem leaf_2785_ok : checkAt 527 1000 box_2785 cert_2785 = true := by
  have h := List.all_eq_true.mp batch_55_10_ok accepted_2785 (by simp [batch_55_10_values])
  exact h
theorem leaf_2785_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2785.profileLo box_2785.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2785_ok
theorem branch_box_2785_nonnegative : ∀ j, 0 ≤ branch_box_2785.lower j ∧ 0 ≤ branch_box_2785.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2785, Box.profileLo, Box.profileHi, box_2785]
theorem leaf_2785_BranchSafe : CertificateConsequences.BranchSafe branch_box_2785 := by
  left; refine ⟨branch_box_2785_nonnegative, ?_⟩
  intro z hz; exact leaf_2785_sound hz

theorem leaf_2787_ok : checkAt 527 1000 box_2787 cert_2787 = true := by
  have h := List.all_eq_true.mp batch_55_11_ok accepted_2787 (by simp [batch_55_11_values])
  exact h
theorem leaf_2787_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2787.profileLo box_2787.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2787_ok
theorem branch_box_2787_nonnegative : ∀ j, 0 ≤ branch_box_2787.lower j ∧ 0 ≤ branch_box_2787.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2787, Box.profileLo, Box.profileHi, box_2787]
theorem leaf_2787_BranchSafe : CertificateConsequences.BranchSafe branch_box_2787 := by
  left; refine ⟨branch_box_2787_nonnegative, ?_⟩
  intro z hz; exact leaf_2787_sound hz

theorem leaf_2789_ok : checkAt 527 1000 box_2789 cert_2789 = true := by
  have h := List.all_eq_true.mp batch_55_12_ok accepted_2789 (by simp [batch_55_12_values])
  exact h
theorem leaf_2789_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2789.profileLo box_2789.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2789_ok
theorem branch_box_2789_nonnegative : ∀ j, 0 ≤ branch_box_2789.lower j ∧ 0 ≤ branch_box_2789.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2789, Box.profileLo, Box.profileHi, box_2789]
theorem leaf_2789_BranchSafe : CertificateConsequences.BranchSafe branch_box_2789 := by
  left; refine ⟨branch_box_2789_nonnegative, ?_⟩
  intro z hz; exact leaf_2789_sound hz

theorem leaf_2794_ok : checkAt 527 1000 box_2794 cert_2794 = true := by
  have h := List.all_eq_true.mp batch_55_13_ok accepted_2794 (by simp [batch_55_13_values])
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

theorem leaf_2796_ok : checkAt 527 1000 box_2796 cert_2796 = true := by
  have h := List.all_eq_true.mp batch_55_14_ok accepted_2796 (by simp [batch_55_14_values])
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

theorem leaf_2799_ok : checkAt 527 1000 box_2799 cert_2799 = true := by
  have h := List.all_eq_true.mp batch_55_15_ok accepted_2799 (by simp [batch_55_15_values])
  exact h
theorem leaf_2799_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2799.profileLo box_2799.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2799_ok
theorem branch_box_2799_nonnegative : ∀ j, 0 ≤ branch_box_2799.lower j ∧ 0 ≤ branch_box_2799.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2799, Box.profileLo, Box.profileHi, box_2799]
theorem leaf_2799_BranchSafe : CertificateConsequences.BranchSafe branch_box_2799 := by
  left; refine ⟨branch_box_2799_nonnegative, ?_⟩
  intro z hz; exact leaf_2799_sound hz

#print axioms batch_55_00_ok
#print axioms leaf_2750_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
