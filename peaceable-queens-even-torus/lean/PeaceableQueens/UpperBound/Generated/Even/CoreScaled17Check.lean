import PeaceableQueens.UpperBound.Generated.Even.CoreScaled17Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_17_00_values : List Bool := [accepted_850]
theorem batch_17_00_ok : batch_17_00_values.all id = true := by decide

def batch_17_01_values : List Bool := [accepted_852]
theorem batch_17_01_ok : batch_17_01_values.all id = true := by decide

def batch_17_02_values : List Bool := [accepted_860]
theorem batch_17_02_ok : batch_17_02_values.all id = true := by decide

def batch_17_03_values : List Bool := [accepted_862]
theorem batch_17_03_ok : batch_17_03_values.all id = true := by decide

def batch_17_04_values : List Bool := [accepted_864]
theorem batch_17_04_ok : batch_17_04_values.all id = true := by decide

def batch_17_05_values : List Bool := [accepted_865]
theorem batch_17_05_ok : batch_17_05_values.all id = true := by decide

def batch_17_06_values : List Bool := [accepted_867]
theorem batch_17_06_ok : batch_17_06_values.all id = true := by decide

def batch_17_07_values : List Bool := [accepted_872]
theorem batch_17_07_ok : batch_17_07_values.all id = true := by decide

def batch_17_08_values : List Bool := [accepted_875]
theorem batch_17_08_ok : batch_17_08_values.all id = true := by decide

def batch_17_09_values : List Bool := [accepted_877]
theorem batch_17_09_ok : batch_17_09_values.all id = true := by decide

def batch_17_10_values : List Bool := [accepted_879]
theorem batch_17_10_ok : batch_17_10_values.all id = true := by decide

def batch_17_11_values : List Bool := [accepted_885]
theorem batch_17_11_ok : batch_17_11_values.all id = true := by decide

def batch_17_12_values : List Bool := [accepted_887]
theorem batch_17_12_ok : batch_17_12_values.all id = true := by decide

def batch_17_13_values : List Bool := [accepted_889]
theorem batch_17_13_ok : batch_17_13_values.all id = true := by decide

def batch_17_14_values : List Bool := [accepted_893]
theorem batch_17_14_ok : batch_17_14_values.all id = true := by decide

def batch_17_15_values : List Bool := [accepted_895]
theorem batch_17_15_ok : batch_17_15_values.all id = true := by decide

def batch_17_16_values : List Bool := [accepted_897]
theorem batch_17_16_ok : batch_17_16_values.all id = true := by decide

def batch_17_17_values : List Bool := [accepted_899]
theorem batch_17_17_ok : batch_17_17_values.all id = true := by decide

theorem leaf_850_ok : checkAt 527 1000 box_850 cert_850 = true := by
  have h := List.all_eq_true.mp batch_17_00_ok accepted_850 (by simp [batch_17_00_values])
  exact h
theorem leaf_850_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_850.profileLo box_850.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_850_ok
theorem branch_box_850_nonnegative : ∀ j, 0 ≤ branch_box_850.lower j ∧ 0 ≤ branch_box_850.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_850, Box.profileLo, Box.profileHi, box_850]
theorem leaf_850_BranchSafe : CertificateConsequences.BranchSafe branch_box_850 := by
  left; refine ⟨branch_box_850_nonnegative, ?_⟩
  intro z hz; exact leaf_850_sound hz

theorem leaf_852_ok : checkAt 527 1000 box_852 cert_852 = true := by
  have h := List.all_eq_true.mp batch_17_01_ok accepted_852 (by simp [batch_17_01_values])
  exact h
theorem leaf_852_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_852.profileLo box_852.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_852_ok
theorem branch_box_852_nonnegative : ∀ j, 0 ≤ branch_box_852.lower j ∧ 0 ≤ branch_box_852.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_852, Box.profileLo, Box.profileHi, box_852]
theorem leaf_852_BranchSafe : CertificateConsequences.BranchSafe branch_box_852 := by
  left; refine ⟨branch_box_852_nonnegative, ?_⟩
  intro z hz; exact leaf_852_sound hz

theorem leaf_860_ok : checkAt 527 1000 box_860 cert_860 = true := by
  have h := List.all_eq_true.mp batch_17_02_ok accepted_860 (by simp [batch_17_02_values])
  exact h
theorem leaf_860_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_860.profileLo box_860.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_860_ok
theorem branch_box_860_nonnegative : ∀ j, 0 ≤ branch_box_860.lower j ∧ 0 ≤ branch_box_860.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_860, Box.profileLo, Box.profileHi, box_860]
theorem leaf_860_BranchSafe : CertificateConsequences.BranchSafe branch_box_860 := by
  left; refine ⟨branch_box_860_nonnegative, ?_⟩
  intro z hz; exact leaf_860_sound hz

theorem leaf_862_ok : checkAt 527 1000 box_862 cert_862 = true := by
  have h := List.all_eq_true.mp batch_17_03_ok accepted_862 (by simp [batch_17_03_values])
  exact h
theorem leaf_862_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_862.profileLo box_862.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_862_ok
theorem branch_box_862_nonnegative : ∀ j, 0 ≤ branch_box_862.lower j ∧ 0 ≤ branch_box_862.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_862, Box.profileLo, Box.profileHi, box_862]
theorem leaf_862_BranchSafe : CertificateConsequences.BranchSafe branch_box_862 := by
  left; refine ⟨branch_box_862_nonnegative, ?_⟩
  intro z hz; exact leaf_862_sound hz

theorem leaf_864_ok : checkAt 527 1000 box_864 cert_864 = true := by
  have h := List.all_eq_true.mp batch_17_04_ok accepted_864 (by simp [batch_17_04_values])
  exact h
theorem leaf_864_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_864.profileLo box_864.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_864_ok
theorem branch_box_864_nonnegative : ∀ j, 0 ≤ branch_box_864.lower j ∧ 0 ≤ branch_box_864.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_864, Box.profileLo, Box.profileHi, box_864]
theorem leaf_864_BranchSafe : CertificateConsequences.BranchSafe branch_box_864 := by
  left; refine ⟨branch_box_864_nonnegative, ?_⟩
  intro z hz; exact leaf_864_sound hz

theorem leaf_865_ok : checkAt 527 1000 box_865 cert_865 = true := by
  have h := List.all_eq_true.mp batch_17_05_ok accepted_865 (by simp [batch_17_05_values])
  exact h
theorem leaf_865_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_865.profileLo box_865.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_865_ok
theorem branch_box_865_nonnegative : ∀ j, 0 ≤ branch_box_865.lower j ∧ 0 ≤ branch_box_865.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_865, Box.profileLo, Box.profileHi, box_865]
theorem leaf_865_BranchSafe : CertificateConsequences.BranchSafe branch_box_865 := by
  left; refine ⟨branch_box_865_nonnegative, ?_⟩
  intro z hz; exact leaf_865_sound hz

theorem leaf_867_ok : checkAt 527 1000 box_867 cert_867 = true := by
  have h := List.all_eq_true.mp batch_17_06_ok accepted_867 (by simp [batch_17_06_values])
  exact h
theorem leaf_867_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_867.profileLo box_867.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_867_ok
theorem branch_box_867_nonnegative : ∀ j, 0 ≤ branch_box_867.lower j ∧ 0 ≤ branch_box_867.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_867, Box.profileLo, Box.profileHi, box_867]
theorem leaf_867_BranchSafe : CertificateConsequences.BranchSafe branch_box_867 := by
  left; refine ⟨branch_box_867_nonnegative, ?_⟩
  intro z hz; exact leaf_867_sound hz

theorem leaf_872_ok : checkAt 527 1000 box_872 cert_872 = true := by
  have h := List.all_eq_true.mp batch_17_07_ok accepted_872 (by simp [batch_17_07_values])
  exact h
theorem leaf_872_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_872.profileLo box_872.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_872_ok
theorem branch_box_872_nonnegative : ∀ j, 0 ≤ branch_box_872.lower j ∧ 0 ≤ branch_box_872.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_872, Box.profileLo, Box.profileHi, box_872]
theorem leaf_872_BranchSafe : CertificateConsequences.BranchSafe branch_box_872 := by
  left; refine ⟨branch_box_872_nonnegative, ?_⟩
  intro z hz; exact leaf_872_sound hz

theorem leaf_875_ok : checkAt 527 1000 box_875 cert_875 = true := by
  have h := List.all_eq_true.mp batch_17_08_ok accepted_875 (by simp [batch_17_08_values])
  exact h
theorem leaf_875_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_875.profileLo box_875.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_875_ok
theorem branch_box_875_nonnegative : ∀ j, 0 ≤ branch_box_875.lower j ∧ 0 ≤ branch_box_875.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_875, Box.profileLo, Box.profileHi, box_875]
theorem leaf_875_BranchSafe : CertificateConsequences.BranchSafe branch_box_875 := by
  left; refine ⟨branch_box_875_nonnegative, ?_⟩
  intro z hz; exact leaf_875_sound hz

theorem leaf_877_ok : checkAt 527 1000 box_877 cert_877 = true := by
  have h := List.all_eq_true.mp batch_17_09_ok accepted_877 (by simp [batch_17_09_values])
  exact h
theorem leaf_877_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_877.profileLo box_877.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_877_ok
theorem branch_box_877_nonnegative : ∀ j, 0 ≤ branch_box_877.lower j ∧ 0 ≤ branch_box_877.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_877, Box.profileLo, Box.profileHi, box_877]
theorem leaf_877_BranchSafe : CertificateConsequences.BranchSafe branch_box_877 := by
  left; refine ⟨branch_box_877_nonnegative, ?_⟩
  intro z hz; exact leaf_877_sound hz

theorem leaf_879_ok : checkAt 527 1000 box_879 cert_879 = true := by
  have h := List.all_eq_true.mp batch_17_10_ok accepted_879 (by simp [batch_17_10_values])
  exact h
theorem leaf_879_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_879.profileLo box_879.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_879_ok
theorem branch_box_879_nonnegative : ∀ j, 0 ≤ branch_box_879.lower j ∧ 0 ≤ branch_box_879.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_879, Box.profileLo, Box.profileHi, box_879]
theorem leaf_879_BranchSafe : CertificateConsequences.BranchSafe branch_box_879 := by
  left; refine ⟨branch_box_879_nonnegative, ?_⟩
  intro z hz; exact leaf_879_sound hz

theorem leaf_885_ok : checkAt 527 1000 box_885 cert_885 = true := by
  have h := List.all_eq_true.mp batch_17_11_ok accepted_885 (by simp [batch_17_11_values])
  exact h
theorem leaf_885_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_885.profileLo box_885.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_885_ok
theorem branch_box_885_nonnegative : ∀ j, 0 ≤ branch_box_885.lower j ∧ 0 ≤ branch_box_885.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_885, Box.profileLo, Box.profileHi, box_885]
theorem leaf_885_BranchSafe : CertificateConsequences.BranchSafe branch_box_885 := by
  left; refine ⟨branch_box_885_nonnegative, ?_⟩
  intro z hz; exact leaf_885_sound hz

theorem leaf_887_ok : checkAt 527 1000 box_887 cert_887 = true := by
  have h := List.all_eq_true.mp batch_17_12_ok accepted_887 (by simp [batch_17_12_values])
  exact h
theorem leaf_887_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_887.profileLo box_887.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_887_ok
theorem branch_box_887_nonnegative : ∀ j, 0 ≤ branch_box_887.lower j ∧ 0 ≤ branch_box_887.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_887, Box.profileLo, Box.profileHi, box_887]
theorem leaf_887_BranchSafe : CertificateConsequences.BranchSafe branch_box_887 := by
  left; refine ⟨branch_box_887_nonnegative, ?_⟩
  intro z hz; exact leaf_887_sound hz

theorem leaf_889_ok : checkAt 527 1000 box_889 cert_889 = true := by
  have h := List.all_eq_true.mp batch_17_13_ok accepted_889 (by simp [batch_17_13_values])
  exact h
theorem leaf_889_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_889.profileLo box_889.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_889_ok
theorem branch_box_889_nonnegative : ∀ j, 0 ≤ branch_box_889.lower j ∧ 0 ≤ branch_box_889.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_889, Box.profileLo, Box.profileHi, box_889]
theorem leaf_889_BranchSafe : CertificateConsequences.BranchSafe branch_box_889 := by
  left; refine ⟨branch_box_889_nonnegative, ?_⟩
  intro z hz; exact leaf_889_sound hz

theorem leaf_893_ok : checkAt 527 1000 box_893 cert_893 = true := by
  have h := List.all_eq_true.mp batch_17_14_ok accepted_893 (by simp [batch_17_14_values])
  exact h
theorem leaf_893_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_893.profileLo box_893.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_893_ok
theorem branch_box_893_nonnegative : ∀ j, 0 ≤ branch_box_893.lower j ∧ 0 ≤ branch_box_893.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_893, Box.profileLo, Box.profileHi, box_893]
theorem leaf_893_BranchSafe : CertificateConsequences.BranchSafe branch_box_893 := by
  left; refine ⟨branch_box_893_nonnegative, ?_⟩
  intro z hz; exact leaf_893_sound hz

theorem leaf_895_ok : checkAt 527 1000 box_895 cert_895 = true := by
  have h := List.all_eq_true.mp batch_17_15_ok accepted_895 (by simp [batch_17_15_values])
  exact h
theorem leaf_895_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_895.profileLo box_895.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_895_ok
theorem branch_box_895_nonnegative : ∀ j, 0 ≤ branch_box_895.lower j ∧ 0 ≤ branch_box_895.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_895, Box.profileLo, Box.profileHi, box_895]
theorem leaf_895_BranchSafe : CertificateConsequences.BranchSafe branch_box_895 := by
  left; refine ⟨branch_box_895_nonnegative, ?_⟩
  intro z hz; exact leaf_895_sound hz

theorem leaf_897_ok : checkAt 527 1000 box_897 cert_897 = true := by
  have h := List.all_eq_true.mp batch_17_16_ok accepted_897 (by simp [batch_17_16_values])
  exact h
theorem leaf_897_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_897.profileLo box_897.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_897_ok
theorem branch_box_897_nonnegative : ∀ j, 0 ≤ branch_box_897.lower j ∧ 0 ≤ branch_box_897.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_897, Box.profileLo, Box.profileHi, box_897]
theorem leaf_897_BranchSafe : CertificateConsequences.BranchSafe branch_box_897 := by
  left; refine ⟨branch_box_897_nonnegative, ?_⟩
  intro z hz; exact leaf_897_sound hz

theorem leaf_899_ok : checkAt 527 1000 box_899 cert_899 = true := by
  have h := List.all_eq_true.mp batch_17_17_ok accepted_899 (by simp [batch_17_17_values])
  exact h
theorem leaf_899_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_899.profileLo box_899.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_899_ok
theorem branch_box_899_nonnegative : ∀ j, 0 ≤ branch_box_899.lower j ∧ 0 ≤ branch_box_899.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_899, Box.profileLo, Box.profileHi, box_899]
theorem leaf_899_BranchSafe : CertificateConsequences.BranchSafe branch_box_899 := by
  left; refine ⟨branch_box_899_nonnegative, ?_⟩
  intro z hz; exact leaf_899_sound hz

#print axioms batch_17_00_ok
#print axioms leaf_850_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
