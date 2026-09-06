import PeaceableQueens.UpperBound.Generated.Even.CoreScaled57Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_57_00_values : List Bool := [accepted_2851]
theorem batch_57_00_ok : batch_57_00_values.all id = true := by decide

def batch_57_01_values : List Bool := [accepted_2858]
theorem batch_57_01_ok : batch_57_01_values.all id = true := by decide

def batch_57_02_values : List Bool := [accepted_2860]
theorem batch_57_02_ok : batch_57_02_values.all id = true := by decide

def batch_57_03_values : List Bool := [accepted_2862]
theorem batch_57_03_ok : batch_57_03_values.all id = true := by decide

def batch_57_04_values : List Bool := [accepted_2864]
theorem batch_57_04_ok : batch_57_04_values.all id = true := by decide

def batch_57_05_values : List Bool := [accepted_2866]
theorem batch_57_05_ok : batch_57_05_values.all id = true := by decide

def batch_57_06_values : List Bool := [accepted_2867]
theorem batch_57_06_ok : batch_57_06_values.all id = true := by decide

def batch_57_07_values : List Bool := [accepted_2870]
theorem batch_57_07_ok : batch_57_07_values.all id = true := by decide

def batch_57_08_values : List Bool := [accepted_2872]
theorem batch_57_08_ok : batch_57_08_values.all id = true := by decide

def batch_57_09_values : List Bool := [accepted_2874]
theorem batch_57_09_ok : batch_57_09_values.all id = true := by decide

def batch_57_10_values : List Bool := [accepted_2875]
theorem batch_57_10_ok : batch_57_10_values.all id = true := by decide

def batch_57_11_values : List Bool := [accepted_2877]
theorem batch_57_11_ok : batch_57_11_values.all id = true := by decide

def batch_57_12_values : List Bool := [accepted_2887]
theorem batch_57_12_ok : batch_57_12_values.all id = true := by decide

def batch_57_13_values : List Bool := [accepted_2894]
theorem batch_57_13_ok : batch_57_13_values.all id = true := by decide

def batch_57_14_values : List Bool := [accepted_2896]
theorem batch_57_14_ok : batch_57_14_values.all id = true := by decide

def batch_57_15_values : List Bool := [accepted_2897]
theorem batch_57_15_ok : batch_57_15_values.all id = true := by decide

theorem leaf_2851_ok : checkAt 527 1000 box_2851 cert_2851 = true := by
  have h := List.all_eq_true.mp batch_57_00_ok accepted_2851 (by simp [batch_57_00_values])
  exact h
theorem leaf_2851_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2851.profileLo box_2851.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2851_ok
theorem branch_box_2851_nonnegative : ∀ j, 0 ≤ branch_box_2851.lower j ∧ 0 ≤ branch_box_2851.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2851, Box.profileLo, Box.profileHi, box_2851]
theorem leaf_2851_BranchSafe : CertificateConsequences.BranchSafe branch_box_2851 := by
  left; refine ⟨branch_box_2851_nonnegative, ?_⟩
  intro z hz; exact leaf_2851_sound hz

theorem leaf_2858_ok : checkAt 527 1000 box_2858 cert_2858 = true := by
  have h := List.all_eq_true.mp batch_57_01_ok accepted_2858 (by simp [batch_57_01_values])
  exact h
theorem leaf_2858_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2858.profileLo box_2858.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2858_ok
theorem branch_box_2858_nonnegative : ∀ j, 0 ≤ branch_box_2858.lower j ∧ 0 ≤ branch_box_2858.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2858, Box.profileLo, Box.profileHi, box_2858]
theorem leaf_2858_BranchSafe : CertificateConsequences.BranchSafe branch_box_2858 := by
  left; refine ⟨branch_box_2858_nonnegative, ?_⟩
  intro z hz; exact leaf_2858_sound hz

theorem leaf_2860_ok : checkAt 527 1000 box_2860 cert_2860 = true := by
  have h := List.all_eq_true.mp batch_57_02_ok accepted_2860 (by simp [batch_57_02_values])
  exact h
theorem leaf_2860_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2860.profileLo box_2860.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2860_ok
theorem branch_box_2860_nonnegative : ∀ j, 0 ≤ branch_box_2860.lower j ∧ 0 ≤ branch_box_2860.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2860, Box.profileLo, Box.profileHi, box_2860]
theorem leaf_2860_BranchSafe : CertificateConsequences.BranchSafe branch_box_2860 := by
  left; refine ⟨branch_box_2860_nonnegative, ?_⟩
  intro z hz; exact leaf_2860_sound hz

theorem leaf_2862_ok : checkAt 527 1000 box_2862 cert_2862 = true := by
  have h := List.all_eq_true.mp batch_57_03_ok accepted_2862 (by simp [batch_57_03_values])
  exact h
theorem leaf_2862_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2862.profileLo box_2862.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2862_ok
theorem branch_box_2862_nonnegative : ∀ j, 0 ≤ branch_box_2862.lower j ∧ 0 ≤ branch_box_2862.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2862, Box.profileLo, Box.profileHi, box_2862]
theorem leaf_2862_BranchSafe : CertificateConsequences.BranchSafe branch_box_2862 := by
  left; refine ⟨branch_box_2862_nonnegative, ?_⟩
  intro z hz; exact leaf_2862_sound hz

theorem leaf_2864_ok : checkAt 527 1000 box_2864 cert_2864 = true := by
  have h := List.all_eq_true.mp batch_57_04_ok accepted_2864 (by simp [batch_57_04_values])
  exact h
theorem leaf_2864_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2864.profileLo box_2864.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2864_ok
theorem branch_box_2864_nonnegative : ∀ j, 0 ≤ branch_box_2864.lower j ∧ 0 ≤ branch_box_2864.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2864, Box.profileLo, Box.profileHi, box_2864]
theorem leaf_2864_BranchSafe : CertificateConsequences.BranchSafe branch_box_2864 := by
  left; refine ⟨branch_box_2864_nonnegative, ?_⟩
  intro z hz; exact leaf_2864_sound hz

theorem leaf_2866_ok : checkAt 527 1000 box_2866 cert_2866 = true := by
  have h := List.all_eq_true.mp batch_57_05_ok accepted_2866 (by simp [batch_57_05_values])
  exact h
theorem leaf_2866_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2866.profileLo box_2866.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2866_ok
theorem branch_box_2866_nonnegative : ∀ j, 0 ≤ branch_box_2866.lower j ∧ 0 ≤ branch_box_2866.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2866, Box.profileLo, Box.profileHi, box_2866]
theorem leaf_2866_BranchSafe : CertificateConsequences.BranchSafe branch_box_2866 := by
  left; refine ⟨branch_box_2866_nonnegative, ?_⟩
  intro z hz; exact leaf_2866_sound hz

theorem leaf_2867_ok : checkAt 527 1000 box_2867 cert_2867 = true := by
  have h := List.all_eq_true.mp batch_57_06_ok accepted_2867 (by simp [batch_57_06_values])
  exact h
theorem leaf_2867_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2867.profileLo box_2867.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2867_ok
theorem branch_box_2867_nonnegative : ∀ j, 0 ≤ branch_box_2867.lower j ∧ 0 ≤ branch_box_2867.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2867, Box.profileLo, Box.profileHi, box_2867]
theorem leaf_2867_BranchSafe : CertificateConsequences.BranchSafe branch_box_2867 := by
  left; refine ⟨branch_box_2867_nonnegative, ?_⟩
  intro z hz; exact leaf_2867_sound hz

theorem leaf_2870_ok : checkAt 527 1000 box_2870 cert_2870 = true := by
  have h := List.all_eq_true.mp batch_57_07_ok accepted_2870 (by simp [batch_57_07_values])
  exact h
theorem leaf_2870_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2870.profileLo box_2870.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2870_ok
theorem branch_box_2870_nonnegative : ∀ j, 0 ≤ branch_box_2870.lower j ∧ 0 ≤ branch_box_2870.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2870, Box.profileLo, Box.profileHi, box_2870]
theorem leaf_2870_BranchSafe : CertificateConsequences.BranchSafe branch_box_2870 := by
  left; refine ⟨branch_box_2870_nonnegative, ?_⟩
  intro z hz; exact leaf_2870_sound hz

theorem leaf_2872_ok : checkAt 527 1000 box_2872 cert_2872 = true := by
  have h := List.all_eq_true.mp batch_57_08_ok accepted_2872 (by simp [batch_57_08_values])
  exact h
theorem leaf_2872_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2872.profileLo box_2872.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2872_ok
theorem branch_box_2872_nonnegative : ∀ j, 0 ≤ branch_box_2872.lower j ∧ 0 ≤ branch_box_2872.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2872, Box.profileLo, Box.profileHi, box_2872]
theorem leaf_2872_BranchSafe : CertificateConsequences.BranchSafe branch_box_2872 := by
  left; refine ⟨branch_box_2872_nonnegative, ?_⟩
  intro z hz; exact leaf_2872_sound hz

theorem leaf_2874_ok : checkAt 527 1000 box_2874 cert_2874 = true := by
  have h := List.all_eq_true.mp batch_57_09_ok accepted_2874 (by simp [batch_57_09_values])
  exact h
theorem leaf_2874_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2874.profileLo box_2874.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2874_ok
theorem branch_box_2874_nonnegative : ∀ j, 0 ≤ branch_box_2874.lower j ∧ 0 ≤ branch_box_2874.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2874, Box.profileLo, Box.profileHi, box_2874]
theorem leaf_2874_BranchSafe : CertificateConsequences.BranchSafe branch_box_2874 := by
  left; refine ⟨branch_box_2874_nonnegative, ?_⟩
  intro z hz; exact leaf_2874_sound hz

theorem leaf_2875_ok : checkAt 527 1000 box_2875 cert_2875 = true := by
  have h := List.all_eq_true.mp batch_57_10_ok accepted_2875 (by simp [batch_57_10_values])
  exact h
theorem leaf_2875_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2875.profileLo box_2875.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2875_ok
theorem branch_box_2875_nonnegative : ∀ j, 0 ≤ branch_box_2875.lower j ∧ 0 ≤ branch_box_2875.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2875, Box.profileLo, Box.profileHi, box_2875]
theorem leaf_2875_BranchSafe : CertificateConsequences.BranchSafe branch_box_2875 := by
  left; refine ⟨branch_box_2875_nonnegative, ?_⟩
  intro z hz; exact leaf_2875_sound hz

theorem leaf_2877_ok : checkAt 527 1000 box_2877 cert_2877 = true := by
  have h := List.all_eq_true.mp batch_57_11_ok accepted_2877 (by simp [batch_57_11_values])
  exact h
theorem leaf_2877_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2877.profileLo box_2877.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2877_ok
theorem branch_box_2877_nonnegative : ∀ j, 0 ≤ branch_box_2877.lower j ∧ 0 ≤ branch_box_2877.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2877, Box.profileLo, Box.profileHi, box_2877]
theorem leaf_2877_BranchSafe : CertificateConsequences.BranchSafe branch_box_2877 := by
  left; refine ⟨branch_box_2877_nonnegative, ?_⟩
  intro z hz; exact leaf_2877_sound hz

theorem leaf_2887_ok : checkAt 527 1000 box_2887 cert_2887 = true := by
  have h := List.all_eq_true.mp batch_57_12_ok accepted_2887 (by simp [batch_57_12_values])
  exact h
theorem leaf_2887_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2887.profileLo box_2887.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2887_ok
theorem branch_box_2887_nonnegative : ∀ j, 0 ≤ branch_box_2887.lower j ∧ 0 ≤ branch_box_2887.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2887, Box.profileLo, Box.profileHi, box_2887]
theorem leaf_2887_BranchSafe : CertificateConsequences.BranchSafe branch_box_2887 := by
  left; refine ⟨branch_box_2887_nonnegative, ?_⟩
  intro z hz; exact leaf_2887_sound hz

theorem leaf_2894_ok : checkAt 527 1000 box_2894 cert_2894 = true := by
  have h := List.all_eq_true.mp batch_57_13_ok accepted_2894 (by simp [batch_57_13_values])
  exact h
theorem leaf_2894_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2894.profileLo box_2894.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2894_ok
theorem branch_box_2894_nonnegative : ∀ j, 0 ≤ branch_box_2894.lower j ∧ 0 ≤ branch_box_2894.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2894, Box.profileLo, Box.profileHi, box_2894]
theorem leaf_2894_BranchSafe : CertificateConsequences.BranchSafe branch_box_2894 := by
  left; refine ⟨branch_box_2894_nonnegative, ?_⟩
  intro z hz; exact leaf_2894_sound hz

theorem leaf_2896_ok : checkAt 527 1000 box_2896 cert_2896 = true := by
  have h := List.all_eq_true.mp batch_57_14_ok accepted_2896 (by simp [batch_57_14_values])
  exact h
theorem leaf_2896_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2896.profileLo box_2896.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2896_ok
theorem branch_box_2896_nonnegative : ∀ j, 0 ≤ branch_box_2896.lower j ∧ 0 ≤ branch_box_2896.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2896, Box.profileLo, Box.profileHi, box_2896]
theorem leaf_2896_BranchSafe : CertificateConsequences.BranchSafe branch_box_2896 := by
  left; refine ⟨branch_box_2896_nonnegative, ?_⟩
  intro z hz; exact leaf_2896_sound hz

theorem leaf_2897_ok : checkAt 527 1000 box_2897 cert_2897 = true := by
  have h := List.all_eq_true.mp batch_57_15_ok accepted_2897 (by simp [batch_57_15_values])
  exact h
theorem leaf_2897_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2897.profileLo box_2897.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2897_ok
theorem branch_box_2897_nonnegative : ∀ j, 0 ≤ branch_box_2897.lower j ∧ 0 ≤ branch_box_2897.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2897, Box.profileLo, Box.profileHi, box_2897]
theorem leaf_2897_BranchSafe : CertificateConsequences.BranchSafe branch_box_2897 := by
  left; refine ⟨branch_box_2897_nonnegative, ?_⟩
  intro z hz; exact leaf_2897_sound hz

#print axioms batch_57_00_ok
#print axioms leaf_2851_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
