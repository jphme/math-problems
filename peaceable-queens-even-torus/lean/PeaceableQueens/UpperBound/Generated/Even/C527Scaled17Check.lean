import PeaceableQueens.UpperBound.Generated.Even.C527Scaled17Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_17_00_values : List Bool := [accepted_851]
theorem batch_17_00_ok : batch_17_00_values.all id = true := by decide

def batch_17_01_values : List Bool := [accepted_852]
theorem batch_17_01_ok : batch_17_01_values.all id = true := by decide

def batch_17_02_values : List Bool := [accepted_853]
theorem batch_17_02_ok : batch_17_02_values.all id = true := by decide

def batch_17_03_values : List Bool := [accepted_854]
theorem batch_17_03_ok : batch_17_03_values.all id = true := by decide

def batch_17_04_values : List Bool := [accepted_857]
theorem batch_17_04_ok : batch_17_04_values.all id = true := by decide

def batch_17_05_values : List Bool := [accepted_858]
theorem batch_17_05_ok : batch_17_05_values.all id = true := by decide

def batch_17_06_values : List Bool := [accepted_861]
theorem batch_17_06_ok : batch_17_06_values.all id = true := by decide

def batch_17_07_values : List Bool := [accepted_862]
theorem batch_17_07_ok : batch_17_07_values.all id = true := by decide

def batch_17_08_values : List Bool := [accepted_863]
theorem batch_17_08_ok : batch_17_08_values.all id = true := by decide

def batch_17_09_values : List Bool := [accepted_865]
theorem batch_17_09_ok : batch_17_09_values.all id = true := by decide

def batch_17_10_values : List Bool := [accepted_867]
theorem batch_17_10_ok : batch_17_10_values.all id = true := by decide

def batch_17_11_values : List Bool := [accepted_869]
theorem batch_17_11_ok : batch_17_11_values.all id = true := by decide

def batch_17_12_values : List Bool := [accepted_870]
theorem batch_17_12_ok : batch_17_12_values.all id = true := by decide

def batch_17_13_values : List Bool := [accepted_879]
theorem batch_17_13_ok : batch_17_13_values.all id = true := by decide

def batch_17_14_values : List Bool := [accepted_880]
theorem batch_17_14_ok : batch_17_14_values.all id = true := by decide

def batch_17_15_values : List Bool := [accepted_881]
theorem batch_17_15_ok : batch_17_15_values.all id = true := by decide

def batch_17_16_values : List Bool := [accepted_882]
theorem batch_17_16_ok : batch_17_16_values.all id = true := by decide

def batch_17_17_values : List Bool := [accepted_891]
theorem batch_17_17_ok : batch_17_17_values.all id = true := by decide

def batch_17_18_values : List Bool := [accepted_893]
theorem batch_17_18_ok : batch_17_18_values.all id = true := by decide

def batch_17_19_values : List Bool := [accepted_894]
theorem batch_17_19_ok : batch_17_19_values.all id = true := by decide

def batch_17_20_values : List Bool := [accepted_895]
theorem batch_17_20_ok : batch_17_20_values.all id = true := by decide

def batch_17_21_values : List Bool := [accepted_896]
theorem batch_17_21_ok : batch_17_21_values.all id = true := by decide

def batch_17_22_values : List Bool := [accepted_897]
theorem batch_17_22_ok : batch_17_22_values.all id = true := by decide

def batch_17_23_values : List Bool := [accepted_898]
theorem batch_17_23_ok : batch_17_23_values.all id = true := by decide

def batch_17_24_values : List Bool := [accepted_899]
theorem batch_17_24_ok : batch_17_24_values.all id = true := by decide

theorem leaf_851_ok : checkAt 527 1000 box_851 cert_851 = true := by
  have h := List.all_eq_true.mp batch_17_00_ok accepted_851 (by simp [batch_17_00_values])
  exact h
theorem leaf_851_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_851.profileLo box_851.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_851_ok
theorem branch_box_851_nonnegative : ∀ j, 0 ≤ branch_box_851.lower j ∧ 0 ≤ branch_box_851.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_851, Box.profileLo, Box.profileHi, box_851]
theorem leaf_851_BranchSafe : CertificateConsequences.BranchSafe branch_box_851 := by
  left; refine ⟨branch_box_851_nonnegative, ?_⟩
  intro z hz; exact leaf_851_sound hz

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

theorem leaf_853_ok : checkAt 527 1000 box_853 cert_853 = true := by
  have h := List.all_eq_true.mp batch_17_02_ok accepted_853 (by simp [batch_17_02_values])
  exact h
theorem leaf_853_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_853.profileLo box_853.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_853_ok
theorem branch_box_853_nonnegative : ∀ j, 0 ≤ branch_box_853.lower j ∧ 0 ≤ branch_box_853.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_853, Box.profileLo, Box.profileHi, box_853]
theorem leaf_853_BranchSafe : CertificateConsequences.BranchSafe branch_box_853 := by
  left; refine ⟨branch_box_853_nonnegative, ?_⟩
  intro z hz; exact leaf_853_sound hz

theorem leaf_854_ok : checkAt 527 1000 box_854 cert_854 = true := by
  have h := List.all_eq_true.mp batch_17_03_ok accepted_854 (by simp [batch_17_03_values])
  exact h
theorem leaf_854_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_854.profileLo box_854.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_854_ok
theorem branch_box_854_nonnegative : ∀ j, 0 ≤ branch_box_854.lower j ∧ 0 ≤ branch_box_854.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_854, Box.profileLo, Box.profileHi, box_854]
theorem leaf_854_BranchSafe : CertificateConsequences.BranchSafe branch_box_854 := by
  left; refine ⟨branch_box_854_nonnegative, ?_⟩
  intro z hz; exact leaf_854_sound hz

theorem leaf_857_ok : checkAt 527 1000 box_857 cert_857 = true := by
  have h := List.all_eq_true.mp batch_17_04_ok accepted_857 (by simp [batch_17_04_values])
  exact h
theorem leaf_857_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_857.profileLo box_857.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_857_ok
theorem branch_box_857_nonnegative : ∀ j, 0 ≤ branch_box_857.lower j ∧ 0 ≤ branch_box_857.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_857, Box.profileLo, Box.profileHi, box_857]
theorem leaf_857_BranchSafe : CertificateConsequences.BranchSafe branch_box_857 := by
  left; refine ⟨branch_box_857_nonnegative, ?_⟩
  intro z hz; exact leaf_857_sound hz

theorem leaf_858_ok : checkAt 527 1000 box_858 cert_858 = true := by
  have h := List.all_eq_true.mp batch_17_05_ok accepted_858 (by simp [batch_17_05_values])
  exact h
theorem leaf_858_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_858.profileLo box_858.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_858_ok
theorem branch_box_858_nonnegative : ∀ j, 0 ≤ branch_box_858.lower j ∧ 0 ≤ branch_box_858.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_858, Box.profileLo, Box.profileHi, box_858]
theorem leaf_858_BranchSafe : CertificateConsequences.BranchSafe branch_box_858 := by
  left; refine ⟨branch_box_858_nonnegative, ?_⟩
  intro z hz; exact leaf_858_sound hz

theorem leaf_861_ok : checkAt 527 1000 box_861 cert_861 = true := by
  have h := List.all_eq_true.mp batch_17_06_ok accepted_861 (by simp [batch_17_06_values])
  exact h
theorem leaf_861_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_861.profileLo box_861.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_861_ok
theorem branch_box_861_nonnegative : ∀ j, 0 ≤ branch_box_861.lower j ∧ 0 ≤ branch_box_861.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_861, Box.profileLo, Box.profileHi, box_861]
theorem leaf_861_BranchSafe : CertificateConsequences.BranchSafe branch_box_861 := by
  left; refine ⟨branch_box_861_nonnegative, ?_⟩
  intro z hz; exact leaf_861_sound hz

theorem leaf_862_ok : checkAt 527 1000 box_862 cert_862 = true := by
  have h := List.all_eq_true.mp batch_17_07_ok accepted_862 (by simp [batch_17_07_values])
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

theorem leaf_863_ok : checkAt 527 1000 box_863 cert_863 = true := by
  have h := List.all_eq_true.mp batch_17_08_ok accepted_863 (by simp [batch_17_08_values])
  exact h
theorem leaf_863_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_863.profileLo box_863.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_863_ok
theorem branch_box_863_nonnegative : ∀ j, 0 ≤ branch_box_863.lower j ∧ 0 ≤ branch_box_863.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_863, Box.profileLo, Box.profileHi, box_863]
theorem leaf_863_BranchSafe : CertificateConsequences.BranchSafe branch_box_863 := by
  left; refine ⟨branch_box_863_nonnegative, ?_⟩
  intro z hz; exact leaf_863_sound hz

theorem leaf_865_ok : checkAt 527 1000 box_865 cert_865 = true := by
  have h := List.all_eq_true.mp batch_17_09_ok accepted_865 (by simp [batch_17_09_values])
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
  have h := List.all_eq_true.mp batch_17_10_ok accepted_867 (by simp [batch_17_10_values])
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

theorem leaf_869_ok : checkAt 527 1000 box_869 cert_869 = true := by
  have h := List.all_eq_true.mp batch_17_11_ok accepted_869 (by simp [batch_17_11_values])
  exact h
theorem leaf_869_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_869.profileLo box_869.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_869_ok
theorem branch_box_869_nonnegative : ∀ j, 0 ≤ branch_box_869.lower j ∧ 0 ≤ branch_box_869.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_869, Box.profileLo, Box.profileHi, box_869]
theorem leaf_869_BranchSafe : CertificateConsequences.BranchSafe branch_box_869 := by
  left; refine ⟨branch_box_869_nonnegative, ?_⟩
  intro z hz; exact leaf_869_sound hz

theorem leaf_870_ok : checkAt 527 1000 box_870 cert_870 = true := by
  have h := List.all_eq_true.mp batch_17_12_ok accepted_870 (by simp [batch_17_12_values])
  exact h
theorem leaf_870_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_870.profileLo box_870.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_870_ok
theorem branch_box_870_nonnegative : ∀ j, 0 ≤ branch_box_870.lower j ∧ 0 ≤ branch_box_870.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_870, Box.profileLo, Box.profileHi, box_870]
theorem leaf_870_BranchSafe : CertificateConsequences.BranchSafe branch_box_870 := by
  left; refine ⟨branch_box_870_nonnegative, ?_⟩
  intro z hz; exact leaf_870_sound hz

theorem leaf_879_ok : checkAt 527 1000 box_879 cert_879 = true := by
  have h := List.all_eq_true.mp batch_17_13_ok accepted_879 (by simp [batch_17_13_values])
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

theorem leaf_880_ok : checkAt 527 1000 box_880 cert_880 = true := by
  have h := List.all_eq_true.mp batch_17_14_ok accepted_880 (by simp [batch_17_14_values])
  exact h
theorem leaf_880_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_880.profileLo box_880.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_880_ok
theorem branch_box_880_nonnegative : ∀ j, 0 ≤ branch_box_880.lower j ∧ 0 ≤ branch_box_880.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_880, Box.profileLo, Box.profileHi, box_880]
theorem leaf_880_BranchSafe : CertificateConsequences.BranchSafe branch_box_880 := by
  left; refine ⟨branch_box_880_nonnegative, ?_⟩
  intro z hz; exact leaf_880_sound hz

theorem leaf_881_ok : checkAt 527 1000 box_881 cert_881 = true := by
  have h := List.all_eq_true.mp batch_17_15_ok accepted_881 (by simp [batch_17_15_values])
  exact h
theorem leaf_881_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_881.profileLo box_881.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_881_ok
theorem branch_box_881_nonnegative : ∀ j, 0 ≤ branch_box_881.lower j ∧ 0 ≤ branch_box_881.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_881, Box.profileLo, Box.profileHi, box_881]
theorem leaf_881_BranchSafe : CertificateConsequences.BranchSafe branch_box_881 := by
  left; refine ⟨branch_box_881_nonnegative, ?_⟩
  intro z hz; exact leaf_881_sound hz

theorem leaf_882_ok : checkAt 527 1000 box_882 cert_882 = true := by
  have h := List.all_eq_true.mp batch_17_16_ok accepted_882 (by simp [batch_17_16_values])
  exact h
theorem leaf_882_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_882.profileLo box_882.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_882_ok
theorem branch_box_882_nonnegative : ∀ j, 0 ≤ branch_box_882.lower j ∧ 0 ≤ branch_box_882.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_882, Box.profileLo, Box.profileHi, box_882]
theorem leaf_882_BranchSafe : CertificateConsequences.BranchSafe branch_box_882 := by
  left; refine ⟨branch_box_882_nonnegative, ?_⟩
  intro z hz; exact leaf_882_sound hz

theorem leaf_891_ok : checkAt 527 1000 box_891 cert_891 = true := by
  have h := List.all_eq_true.mp batch_17_17_ok accepted_891 (by simp [batch_17_17_values])
  exact h
theorem leaf_891_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_891.profileLo box_891.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_891_ok
theorem branch_box_891_nonnegative : ∀ j, 0 ≤ branch_box_891.lower j ∧ 0 ≤ branch_box_891.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_891, Box.profileLo, Box.profileHi, box_891]
theorem leaf_891_BranchSafe : CertificateConsequences.BranchSafe branch_box_891 := by
  left; refine ⟨branch_box_891_nonnegative, ?_⟩
  intro z hz; exact leaf_891_sound hz

theorem leaf_893_ok : checkAt 527 1000 box_893 cert_893 = true := by
  have h := List.all_eq_true.mp batch_17_18_ok accepted_893 (by simp [batch_17_18_values])
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

theorem leaf_894_ok : checkAt 527 1000 box_894 cert_894 = true := by
  have h := List.all_eq_true.mp batch_17_19_ok accepted_894 (by simp [batch_17_19_values])
  exact h
theorem leaf_894_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_894.profileLo box_894.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_894_ok
theorem branch_box_894_nonnegative : ∀ j, 0 ≤ branch_box_894.lower j ∧ 0 ≤ branch_box_894.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_894, Box.profileLo, Box.profileHi, box_894]
theorem leaf_894_BranchSafe : CertificateConsequences.BranchSafe branch_box_894 := by
  left; refine ⟨branch_box_894_nonnegative, ?_⟩
  intro z hz; exact leaf_894_sound hz

theorem leaf_895_ok : checkAt 527 1000 box_895 cert_895 = true := by
  have h := List.all_eq_true.mp batch_17_20_ok accepted_895 (by simp [batch_17_20_values])
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

theorem leaf_896_ok : checkAt 527 1000 box_896 cert_896 = true := by
  have h := List.all_eq_true.mp batch_17_21_ok accepted_896 (by simp [batch_17_21_values])
  exact h
theorem leaf_896_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_896.profileLo box_896.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_896_ok
theorem branch_box_896_nonnegative : ∀ j, 0 ≤ branch_box_896.lower j ∧ 0 ≤ branch_box_896.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_896, Box.profileLo, Box.profileHi, box_896]
theorem leaf_896_BranchSafe : CertificateConsequences.BranchSafe branch_box_896 := by
  left; refine ⟨branch_box_896_nonnegative, ?_⟩
  intro z hz; exact leaf_896_sound hz

theorem leaf_897_ok : checkAt 527 1000 box_897 cert_897 = true := by
  have h := List.all_eq_true.mp batch_17_22_ok accepted_897 (by simp [batch_17_22_values])
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

theorem leaf_898_ok : checkAt 527 1000 box_898 cert_898 = true := by
  have h := List.all_eq_true.mp batch_17_23_ok accepted_898 (by simp [batch_17_23_values])
  exact h
theorem leaf_898_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_898.profileLo box_898.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_898_ok
theorem branch_box_898_nonnegative : ∀ j, 0 ≤ branch_box_898.lower j ∧ 0 ≤ branch_box_898.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_898, Box.profileLo, Box.profileHi, box_898]
theorem leaf_898_BranchSafe : CertificateConsequences.BranchSafe branch_box_898 := by
  left; refine ⟨branch_box_898_nonnegative, ?_⟩
  intro z hz; exact leaf_898_sound hz

theorem leaf_899_ok : checkAt 527 1000 box_899 cert_899 = true := by
  have h := List.all_eq_true.mp batch_17_24_ok accepted_899 (by simp [batch_17_24_values])
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
#print axioms leaf_851_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
