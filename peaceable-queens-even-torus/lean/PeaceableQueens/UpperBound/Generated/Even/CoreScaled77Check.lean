import PeaceableQueens.UpperBound.Generated.Even.CoreScaled77Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_77_00_values : List Bool := [accepted_3850]
theorem batch_77_00_ok : batch_77_00_values.all id = true := by decide

def batch_77_01_values : List Bool := [accepted_3852]
theorem batch_77_01_ok : batch_77_01_values.all id = true := by decide

def batch_77_02_values : List Bool := [accepted_3854]
theorem batch_77_02_ok : batch_77_02_values.all id = true := by decide

def batch_77_03_values : List Bool := [accepted_3856]
theorem batch_77_03_ok : batch_77_03_values.all id = true := by decide

def batch_77_04_values : List Bool := [accepted_3858]
theorem batch_77_04_ok : batch_77_04_values.all id = true := by decide

def batch_77_05_values : List Bool := [accepted_3859]
theorem batch_77_05_ok : batch_77_05_values.all id = true := by decide

def batch_77_06_values : List Bool := [accepted_3870]
theorem batch_77_06_ok : batch_77_06_values.all id = true := by decide

def batch_77_07_values : List Bool := [accepted_3872]
theorem batch_77_07_ok : batch_77_07_values.all id = true := by decide

def batch_77_08_values : List Bool := [accepted_3874]
theorem batch_77_08_ok : batch_77_08_values.all id = true := by decide

def batch_77_09_values : List Bool := [accepted_3876]
theorem batch_77_09_ok : batch_77_09_values.all id = true := by decide

def batch_77_10_values : List Bool := [accepted_3882]
theorem batch_77_10_ok : batch_77_10_values.all id = true := by decide

def batch_77_11_values : List Bool := [accepted_3884]
theorem batch_77_11_ok : batch_77_11_values.all id = true := by decide

def batch_77_12_values : List Bool := [accepted_3886]
theorem batch_77_12_ok : batch_77_12_values.all id = true := by decide

def batch_77_13_values : List Bool := [accepted_3888]
theorem batch_77_13_ok : batch_77_13_values.all id = true := by decide

def batch_77_14_values : List Bool := [accepted_3890]
theorem batch_77_14_ok : batch_77_14_values.all id = true := by decide

def batch_77_15_values : List Bool := [accepted_3891]
theorem batch_77_15_ok : batch_77_15_values.all id = true := by decide

def batch_77_16_values : List Bool := [accepted_3894]
theorem batch_77_16_ok : batch_77_16_values.all id = true := by decide

def batch_77_17_values : List Bool := [accepted_3898]
theorem batch_77_17_ok : batch_77_17_values.all id = true := by decide

theorem leaf_3850_ok : checkAt 527 1000 box_3850 cert_3850 = true := by
  have h := List.all_eq_true.mp batch_77_00_ok accepted_3850 (by simp [batch_77_00_values])
  exact h
theorem leaf_3850_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3850.profileLo box_3850.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3850_ok
theorem branch_box_3850_nonnegative : ∀ j, 0 ≤ branch_box_3850.lower j ∧ 0 ≤ branch_box_3850.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3850, Box.profileLo, Box.profileHi, box_3850]
theorem leaf_3850_BranchSafe : CertificateConsequences.BranchSafe branch_box_3850 := by
  left; refine ⟨branch_box_3850_nonnegative, ?_⟩
  intro z hz; exact leaf_3850_sound hz

theorem leaf_3852_ok : checkAt 527 1000 box_3852 cert_3852 = true := by
  have h := List.all_eq_true.mp batch_77_01_ok accepted_3852 (by simp [batch_77_01_values])
  exact h
theorem leaf_3852_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3852.profileLo box_3852.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3852_ok
theorem branch_box_3852_nonnegative : ∀ j, 0 ≤ branch_box_3852.lower j ∧ 0 ≤ branch_box_3852.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3852, Box.profileLo, Box.profileHi, box_3852]
theorem leaf_3852_BranchSafe : CertificateConsequences.BranchSafe branch_box_3852 := by
  left; refine ⟨branch_box_3852_nonnegative, ?_⟩
  intro z hz; exact leaf_3852_sound hz

theorem leaf_3854_ok : checkAt 527 1000 box_3854 cert_3854 = true := by
  have h := List.all_eq_true.mp batch_77_02_ok accepted_3854 (by simp [batch_77_02_values])
  exact h
theorem leaf_3854_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3854.profileLo box_3854.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3854_ok
theorem branch_box_3854_nonnegative : ∀ j, 0 ≤ branch_box_3854.lower j ∧ 0 ≤ branch_box_3854.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3854, Box.profileLo, Box.profileHi, box_3854]
theorem leaf_3854_BranchSafe : CertificateConsequences.BranchSafe branch_box_3854 := by
  left; refine ⟨branch_box_3854_nonnegative, ?_⟩
  intro z hz; exact leaf_3854_sound hz

theorem leaf_3856_ok : checkAt 527 1000 box_3856 cert_3856 = true := by
  have h := List.all_eq_true.mp batch_77_03_ok accepted_3856 (by simp [batch_77_03_values])
  exact h
theorem leaf_3856_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3856.profileLo box_3856.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3856_ok
theorem branch_box_3856_nonnegative : ∀ j, 0 ≤ branch_box_3856.lower j ∧ 0 ≤ branch_box_3856.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3856, Box.profileLo, Box.profileHi, box_3856]
theorem leaf_3856_BranchSafe : CertificateConsequences.BranchSafe branch_box_3856 := by
  left; refine ⟨branch_box_3856_nonnegative, ?_⟩
  intro z hz; exact leaf_3856_sound hz

theorem leaf_3858_ok : checkAt 527 1000 box_3858 cert_3858 = true := by
  have h := List.all_eq_true.mp batch_77_04_ok accepted_3858 (by simp [batch_77_04_values])
  exact h
theorem leaf_3858_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3858.profileLo box_3858.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3858_ok
theorem branch_box_3858_nonnegative : ∀ j, 0 ≤ branch_box_3858.lower j ∧ 0 ≤ branch_box_3858.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3858, Box.profileLo, Box.profileHi, box_3858]
theorem leaf_3858_BranchSafe : CertificateConsequences.BranchSafe branch_box_3858 := by
  left; refine ⟨branch_box_3858_nonnegative, ?_⟩
  intro z hz; exact leaf_3858_sound hz

theorem leaf_3859_ok : checkAt 527 1000 box_3859 cert_3859 = true := by
  have h := List.all_eq_true.mp batch_77_05_ok accepted_3859 (by simp [batch_77_05_values])
  exact h
theorem leaf_3859_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3859.profileLo box_3859.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3859_ok
theorem branch_box_3859_nonnegative : ∀ j, 0 ≤ branch_box_3859.lower j ∧ 0 ≤ branch_box_3859.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3859, Box.profileLo, Box.profileHi, box_3859]
theorem leaf_3859_BranchSafe : CertificateConsequences.BranchSafe branch_box_3859 := by
  left; refine ⟨branch_box_3859_nonnegative, ?_⟩
  intro z hz; exact leaf_3859_sound hz

theorem leaf_3870_ok : checkAt 527 1000 box_3870 cert_3870 = true := by
  have h := List.all_eq_true.mp batch_77_06_ok accepted_3870 (by simp [batch_77_06_values])
  exact h
theorem leaf_3870_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3870.profileLo box_3870.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3870_ok
theorem branch_box_3870_nonnegative : ∀ j, 0 ≤ branch_box_3870.lower j ∧ 0 ≤ branch_box_3870.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3870, Box.profileLo, Box.profileHi, box_3870]
theorem leaf_3870_BranchSafe : CertificateConsequences.BranchSafe branch_box_3870 := by
  left; refine ⟨branch_box_3870_nonnegative, ?_⟩
  intro z hz; exact leaf_3870_sound hz

theorem leaf_3872_ok : checkAt 527 1000 box_3872 cert_3872 = true := by
  have h := List.all_eq_true.mp batch_77_07_ok accepted_3872 (by simp [batch_77_07_values])
  exact h
theorem leaf_3872_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3872.profileLo box_3872.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3872_ok
theorem branch_box_3872_nonnegative : ∀ j, 0 ≤ branch_box_3872.lower j ∧ 0 ≤ branch_box_3872.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3872, Box.profileLo, Box.profileHi, box_3872]
theorem leaf_3872_BranchSafe : CertificateConsequences.BranchSafe branch_box_3872 := by
  left; refine ⟨branch_box_3872_nonnegative, ?_⟩
  intro z hz; exact leaf_3872_sound hz

theorem leaf_3874_ok : checkAt 527 1000 box_3874 cert_3874 = true := by
  have h := List.all_eq_true.mp batch_77_08_ok accepted_3874 (by simp [batch_77_08_values])
  exact h
theorem leaf_3874_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3874.profileLo box_3874.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3874_ok
theorem branch_box_3874_nonnegative : ∀ j, 0 ≤ branch_box_3874.lower j ∧ 0 ≤ branch_box_3874.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3874, Box.profileLo, Box.profileHi, box_3874]
theorem leaf_3874_BranchSafe : CertificateConsequences.BranchSafe branch_box_3874 := by
  left; refine ⟨branch_box_3874_nonnegative, ?_⟩
  intro z hz; exact leaf_3874_sound hz

theorem leaf_3876_ok : checkAt 527 1000 box_3876 cert_3876 = true := by
  have h := List.all_eq_true.mp batch_77_09_ok accepted_3876 (by simp [batch_77_09_values])
  exact h
theorem leaf_3876_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3876.profileLo box_3876.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3876_ok
theorem branch_box_3876_nonnegative : ∀ j, 0 ≤ branch_box_3876.lower j ∧ 0 ≤ branch_box_3876.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3876, Box.profileLo, Box.profileHi, box_3876]
theorem leaf_3876_BranchSafe : CertificateConsequences.BranchSafe branch_box_3876 := by
  left; refine ⟨branch_box_3876_nonnegative, ?_⟩
  intro z hz; exact leaf_3876_sound hz

theorem leaf_3882_ok : checkAt 527 1000 box_3882 cert_3882 = true := by
  have h := List.all_eq_true.mp batch_77_10_ok accepted_3882 (by simp [batch_77_10_values])
  exact h
theorem leaf_3882_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3882.profileLo box_3882.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3882_ok
theorem branch_box_3882_nonnegative : ∀ j, 0 ≤ branch_box_3882.lower j ∧ 0 ≤ branch_box_3882.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3882, Box.profileLo, Box.profileHi, box_3882]
theorem leaf_3882_BranchSafe : CertificateConsequences.BranchSafe branch_box_3882 := by
  left; refine ⟨branch_box_3882_nonnegative, ?_⟩
  intro z hz; exact leaf_3882_sound hz

theorem leaf_3884_ok : checkAt 527 1000 box_3884 cert_3884 = true := by
  have h := List.all_eq_true.mp batch_77_11_ok accepted_3884 (by simp [batch_77_11_values])
  exact h
theorem leaf_3884_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3884.profileLo box_3884.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3884_ok
theorem branch_box_3884_nonnegative : ∀ j, 0 ≤ branch_box_3884.lower j ∧ 0 ≤ branch_box_3884.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3884, Box.profileLo, Box.profileHi, box_3884]
theorem leaf_3884_BranchSafe : CertificateConsequences.BranchSafe branch_box_3884 := by
  left; refine ⟨branch_box_3884_nonnegative, ?_⟩
  intro z hz; exact leaf_3884_sound hz

theorem leaf_3886_ok : checkAt 527 1000 box_3886 cert_3886 = true := by
  have h := List.all_eq_true.mp batch_77_12_ok accepted_3886 (by simp [batch_77_12_values])
  exact h
theorem leaf_3886_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3886.profileLo box_3886.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3886_ok
theorem branch_box_3886_nonnegative : ∀ j, 0 ≤ branch_box_3886.lower j ∧ 0 ≤ branch_box_3886.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3886, Box.profileLo, Box.profileHi, box_3886]
theorem leaf_3886_BranchSafe : CertificateConsequences.BranchSafe branch_box_3886 := by
  left; refine ⟨branch_box_3886_nonnegative, ?_⟩
  intro z hz; exact leaf_3886_sound hz

theorem leaf_3888_ok : checkAt 527 1000 box_3888 cert_3888 = true := by
  have h := List.all_eq_true.mp batch_77_13_ok accepted_3888 (by simp [batch_77_13_values])
  exact h
theorem leaf_3888_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3888.profileLo box_3888.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3888_ok
theorem branch_box_3888_nonnegative : ∀ j, 0 ≤ branch_box_3888.lower j ∧ 0 ≤ branch_box_3888.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3888, Box.profileLo, Box.profileHi, box_3888]
theorem leaf_3888_BranchSafe : CertificateConsequences.BranchSafe branch_box_3888 := by
  left; refine ⟨branch_box_3888_nonnegative, ?_⟩
  intro z hz; exact leaf_3888_sound hz

theorem leaf_3890_ok : checkAt 527 1000 box_3890 cert_3890 = true := by
  have h := List.all_eq_true.mp batch_77_14_ok accepted_3890 (by simp [batch_77_14_values])
  exact h
theorem leaf_3890_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3890.profileLo box_3890.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3890_ok
theorem branch_box_3890_nonnegative : ∀ j, 0 ≤ branch_box_3890.lower j ∧ 0 ≤ branch_box_3890.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3890, Box.profileLo, Box.profileHi, box_3890]
theorem leaf_3890_BranchSafe : CertificateConsequences.BranchSafe branch_box_3890 := by
  left; refine ⟨branch_box_3890_nonnegative, ?_⟩
  intro z hz; exact leaf_3890_sound hz

theorem leaf_3891_ok : checkAt 527 1000 box_3891 cert_3891 = true := by
  have h := List.all_eq_true.mp batch_77_15_ok accepted_3891 (by simp [batch_77_15_values])
  exact h
theorem leaf_3891_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3891.profileLo box_3891.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3891_ok
theorem branch_box_3891_nonnegative : ∀ j, 0 ≤ branch_box_3891.lower j ∧ 0 ≤ branch_box_3891.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3891, Box.profileLo, Box.profileHi, box_3891]
theorem leaf_3891_BranchSafe : CertificateConsequences.BranchSafe branch_box_3891 := by
  left; refine ⟨branch_box_3891_nonnegative, ?_⟩
  intro z hz; exact leaf_3891_sound hz

theorem leaf_3894_ok : checkAt 527 1000 box_3894 cert_3894 = true := by
  have h := List.all_eq_true.mp batch_77_16_ok accepted_3894 (by simp [batch_77_16_values])
  exact h
theorem leaf_3894_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3894.profileLo box_3894.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3894_ok
theorem branch_box_3894_nonnegative : ∀ j, 0 ≤ branch_box_3894.lower j ∧ 0 ≤ branch_box_3894.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3894, Box.profileLo, Box.profileHi, box_3894]
theorem leaf_3894_BranchSafe : CertificateConsequences.BranchSafe branch_box_3894 := by
  left; refine ⟨branch_box_3894_nonnegative, ?_⟩
  intro z hz; exact leaf_3894_sound hz

theorem leaf_3898_ok : checkAt 527 1000 box_3898 cert_3898 = true := by
  have h := List.all_eq_true.mp batch_77_17_ok accepted_3898 (by simp [batch_77_17_values])
  exact h
theorem leaf_3898_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3898.profileLo box_3898.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3898_ok
theorem branch_box_3898_nonnegative : ∀ j, 0 ≤ branch_box_3898.lower j ∧ 0 ≤ branch_box_3898.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3898, Box.profileLo, Box.profileHi, box_3898]
theorem leaf_3898_BranchSafe : CertificateConsequences.BranchSafe branch_box_3898 := by
  left; refine ⟨branch_box_3898_nonnegative, ?_⟩
  intro z hz; exact leaf_3898_sound hz

#print axioms batch_77_00_ok
#print axioms leaf_3850_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
