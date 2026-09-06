import PeaceableQueens.UpperBound.Generated.Even.C527Scaled137Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_137_00_values : List Bool := [accepted_6850]
theorem batch_137_00_ok : batch_137_00_values.all id = true := by decide

def batch_137_01_values : List Bool := [accepted_6855]
theorem batch_137_01_ok : batch_137_01_values.all id = true := by decide

def batch_137_02_values : List Bool := [accepted_6856]
theorem batch_137_02_ok : batch_137_02_values.all id = true := by decide

def batch_137_03_values : List Bool := [accepted_6859]
theorem batch_137_03_ok : batch_137_03_values.all id = true := by decide

def batch_137_04_values : List Bool := [accepted_6861]
theorem batch_137_04_ok : batch_137_04_values.all id = true := by decide

def batch_137_05_values : List Bool := [accepted_6862]
theorem batch_137_05_ok : batch_137_05_values.all id = true := by decide

def batch_137_06_values : List Bool := [accepted_6863]
theorem batch_137_06_ok : batch_137_06_values.all id = true := by decide

def batch_137_07_values : List Bool := [accepted_6865]
theorem batch_137_07_ok : batch_137_07_values.all id = true := by decide

def batch_137_08_values : List Bool := [accepted_6876]
theorem batch_137_08_ok : batch_137_08_values.all id = true := by decide

def batch_137_09_values : List Bool := [accepted_6877]
theorem batch_137_09_ok : batch_137_09_values.all id = true := by decide

def batch_137_10_values : List Bool := [accepted_6878]
theorem batch_137_10_ok : batch_137_10_values.all id = true := by decide

def batch_137_11_values : List Bool := [accepted_6886]
theorem batch_137_11_ok : batch_137_11_values.all id = true := by decide

def batch_137_12_values : List Bool := [accepted_6887]
theorem batch_137_12_ok : batch_137_12_values.all id = true := by decide

def batch_137_13_values : List Bool := [accepted_6888]
theorem batch_137_13_ok : batch_137_13_values.all id = true := by decide

def batch_137_14_values : List Bool := [accepted_6893]
theorem batch_137_14_ok : batch_137_14_values.all id = true := by decide

def batch_137_15_values : List Bool := [accepted_6895]
theorem batch_137_15_ok : batch_137_15_values.all id = true := by decide

def batch_137_16_values : List Bool := [accepted_6896]
theorem batch_137_16_ok : batch_137_16_values.all id = true := by decide

theorem leaf_6850_ok : checkAt 527 1000 box_6850 cert_6850 = true := by
  have h := List.all_eq_true.mp batch_137_00_ok accepted_6850 (by simp [batch_137_00_values])
  exact h
theorem leaf_6850_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6850.profileLo box_6850.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6850_ok
theorem branch_box_6850_nonnegative : ∀ j, 0 ≤ branch_box_6850.lower j ∧ 0 ≤ branch_box_6850.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6850, Box.profileLo, Box.profileHi, box_6850]
theorem leaf_6850_BranchSafe : CertificateConsequences.BranchSafe branch_box_6850 := by
  left; refine ⟨branch_box_6850_nonnegative, ?_⟩
  intro z hz; exact leaf_6850_sound hz

theorem leaf_6855_ok : checkAt 527 1000 box_6855 cert_6855 = true := by
  have h := List.all_eq_true.mp batch_137_01_ok accepted_6855 (by simp [batch_137_01_values])
  exact h
theorem leaf_6855_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6855.profileLo box_6855.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6855_ok
theorem branch_box_6855_nonnegative : ∀ j, 0 ≤ branch_box_6855.lower j ∧ 0 ≤ branch_box_6855.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6855, Box.profileLo, Box.profileHi, box_6855]
theorem leaf_6855_BranchSafe : CertificateConsequences.BranchSafe branch_box_6855 := by
  left; refine ⟨branch_box_6855_nonnegative, ?_⟩
  intro z hz; exact leaf_6855_sound hz

theorem leaf_6856_ok : checkAt 527 1000 box_6856 cert_6856 = true := by
  have h := List.all_eq_true.mp batch_137_02_ok accepted_6856 (by simp [batch_137_02_values])
  exact h
theorem leaf_6856_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6856.profileLo box_6856.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6856_ok
theorem branch_box_6856_nonnegative : ∀ j, 0 ≤ branch_box_6856.lower j ∧ 0 ≤ branch_box_6856.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6856, Box.profileLo, Box.profileHi, box_6856]
theorem leaf_6856_BranchSafe : CertificateConsequences.BranchSafe branch_box_6856 := by
  left; refine ⟨branch_box_6856_nonnegative, ?_⟩
  intro z hz; exact leaf_6856_sound hz

theorem leaf_6859_ok : checkAt 527 1000 box_6859 cert_6859 = true := by
  have h := List.all_eq_true.mp batch_137_03_ok accepted_6859 (by simp [batch_137_03_values])
  exact h
theorem leaf_6859_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6859.profileLo box_6859.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6859_ok
theorem branch_box_6859_nonnegative : ∀ j, 0 ≤ branch_box_6859.lower j ∧ 0 ≤ branch_box_6859.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6859, Box.profileLo, Box.profileHi, box_6859]
theorem leaf_6859_BranchSafe : CertificateConsequences.BranchSafe branch_box_6859 := by
  left; refine ⟨branch_box_6859_nonnegative, ?_⟩
  intro z hz; exact leaf_6859_sound hz

theorem leaf_6861_ok : checkAt 527 1000 box_6861 cert_6861 = true := by
  have h := List.all_eq_true.mp batch_137_04_ok accepted_6861 (by simp [batch_137_04_values])
  exact h
theorem leaf_6861_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6861.profileLo box_6861.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6861_ok
theorem branch_box_6861_nonnegative : ∀ j, 0 ≤ branch_box_6861.lower j ∧ 0 ≤ branch_box_6861.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6861, Box.profileLo, Box.profileHi, box_6861]
theorem leaf_6861_BranchSafe : CertificateConsequences.BranchSafe branch_box_6861 := by
  left; refine ⟨branch_box_6861_nonnegative, ?_⟩
  intro z hz; exact leaf_6861_sound hz

theorem leaf_6862_ok : checkAt 527 1000 box_6862 cert_6862 = true := by
  have h := List.all_eq_true.mp batch_137_05_ok accepted_6862 (by simp [batch_137_05_values])
  exact h
theorem leaf_6862_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6862.profileLo box_6862.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6862_ok
theorem branch_box_6862_nonnegative : ∀ j, 0 ≤ branch_box_6862.lower j ∧ 0 ≤ branch_box_6862.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6862, Box.profileLo, Box.profileHi, box_6862]
theorem leaf_6862_BranchSafe : CertificateConsequences.BranchSafe branch_box_6862 := by
  left; refine ⟨branch_box_6862_nonnegative, ?_⟩
  intro z hz; exact leaf_6862_sound hz

theorem leaf_6863_ok : checkAt 527 1000 box_6863 cert_6863 = true := by
  have h := List.all_eq_true.mp batch_137_06_ok accepted_6863 (by simp [batch_137_06_values])
  exact h
theorem leaf_6863_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6863.profileLo box_6863.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6863_ok
theorem branch_box_6863_nonnegative : ∀ j, 0 ≤ branch_box_6863.lower j ∧ 0 ≤ branch_box_6863.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6863, Box.profileLo, Box.profileHi, box_6863]
theorem leaf_6863_BranchSafe : CertificateConsequences.BranchSafe branch_box_6863 := by
  left; refine ⟨branch_box_6863_nonnegative, ?_⟩
  intro z hz; exact leaf_6863_sound hz

theorem leaf_6865_ok : checkAt 527 1000 box_6865 cert_6865 = true := by
  have h := List.all_eq_true.mp batch_137_07_ok accepted_6865 (by simp [batch_137_07_values])
  exact h
theorem leaf_6865_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6865.profileLo box_6865.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6865_ok
theorem branch_box_6865_nonnegative : ∀ j, 0 ≤ branch_box_6865.lower j ∧ 0 ≤ branch_box_6865.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6865, Box.profileLo, Box.profileHi, box_6865]
theorem leaf_6865_BranchSafe : CertificateConsequences.BranchSafe branch_box_6865 := by
  left; refine ⟨branch_box_6865_nonnegative, ?_⟩
  intro z hz; exact leaf_6865_sound hz

theorem leaf_6876_ok : checkAt 527 1000 box_6876 cert_6876 = true := by
  have h := List.all_eq_true.mp batch_137_08_ok accepted_6876 (by simp [batch_137_08_values])
  exact h
theorem leaf_6876_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6876.profileLo box_6876.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6876_ok
theorem branch_box_6876_nonnegative : ∀ j, 0 ≤ branch_box_6876.lower j ∧ 0 ≤ branch_box_6876.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6876, Box.profileLo, Box.profileHi, box_6876]
theorem leaf_6876_BranchSafe : CertificateConsequences.BranchSafe branch_box_6876 := by
  left; refine ⟨branch_box_6876_nonnegative, ?_⟩
  intro z hz; exact leaf_6876_sound hz

theorem leaf_6877_ok : checkAt 527 1000 box_6877 cert_6877 = true := by
  have h := List.all_eq_true.mp batch_137_09_ok accepted_6877 (by simp [batch_137_09_values])
  exact h
theorem leaf_6877_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6877.profileLo box_6877.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6877_ok
theorem branch_box_6877_nonnegative : ∀ j, 0 ≤ branch_box_6877.lower j ∧ 0 ≤ branch_box_6877.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6877, Box.profileLo, Box.profileHi, box_6877]
theorem leaf_6877_BranchSafe : CertificateConsequences.BranchSafe branch_box_6877 := by
  left; refine ⟨branch_box_6877_nonnegative, ?_⟩
  intro z hz; exact leaf_6877_sound hz

theorem leaf_6878_ok : checkAt 527 1000 box_6878 cert_6878 = true := by
  have h := List.all_eq_true.mp batch_137_10_ok accepted_6878 (by simp [batch_137_10_values])
  exact h
theorem leaf_6878_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6878.profileLo box_6878.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6878_ok
theorem branch_box_6878_nonnegative : ∀ j, 0 ≤ branch_box_6878.lower j ∧ 0 ≤ branch_box_6878.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6878, Box.profileLo, Box.profileHi, box_6878]
theorem leaf_6878_BranchSafe : CertificateConsequences.BranchSafe branch_box_6878 := by
  left; refine ⟨branch_box_6878_nonnegative, ?_⟩
  intro z hz; exact leaf_6878_sound hz

theorem leaf_6886_ok : checkAt 527 1000 box_6886 cert_6886 = true := by
  have h := List.all_eq_true.mp batch_137_11_ok accepted_6886 (by simp [batch_137_11_values])
  exact h
theorem leaf_6886_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6886.profileLo box_6886.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6886_ok
theorem branch_box_6886_nonnegative : ∀ j, 0 ≤ branch_box_6886.lower j ∧ 0 ≤ branch_box_6886.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6886, Box.profileLo, Box.profileHi, box_6886]
theorem leaf_6886_BranchSafe : CertificateConsequences.BranchSafe branch_box_6886 := by
  left; refine ⟨branch_box_6886_nonnegative, ?_⟩
  intro z hz; exact leaf_6886_sound hz

theorem leaf_6887_ok : checkAt 527 1000 box_6887 cert_6887 = true := by
  have h := List.all_eq_true.mp batch_137_12_ok accepted_6887 (by simp [batch_137_12_values])
  exact h
theorem leaf_6887_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6887.profileLo box_6887.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6887_ok
theorem branch_box_6887_nonnegative : ∀ j, 0 ≤ branch_box_6887.lower j ∧ 0 ≤ branch_box_6887.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6887, Box.profileLo, Box.profileHi, box_6887]
theorem leaf_6887_BranchSafe : CertificateConsequences.BranchSafe branch_box_6887 := by
  left; refine ⟨branch_box_6887_nonnegative, ?_⟩
  intro z hz; exact leaf_6887_sound hz

theorem leaf_6888_ok : checkAt 527 1000 box_6888 cert_6888 = true := by
  have h := List.all_eq_true.mp batch_137_13_ok accepted_6888 (by simp [batch_137_13_values])
  exact h
theorem leaf_6888_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6888.profileLo box_6888.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6888_ok
theorem branch_box_6888_nonnegative : ∀ j, 0 ≤ branch_box_6888.lower j ∧ 0 ≤ branch_box_6888.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6888, Box.profileLo, Box.profileHi, box_6888]
theorem leaf_6888_BranchSafe : CertificateConsequences.BranchSafe branch_box_6888 := by
  left; refine ⟨branch_box_6888_nonnegative, ?_⟩
  intro z hz; exact leaf_6888_sound hz

theorem leaf_6893_ok : checkAt 527 1000 box_6893 cert_6893 = true := by
  have h := List.all_eq_true.mp batch_137_14_ok accepted_6893 (by simp [batch_137_14_values])
  exact h
theorem leaf_6893_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6893.profileLo box_6893.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6893_ok
theorem branch_box_6893_nonnegative : ∀ j, 0 ≤ branch_box_6893.lower j ∧ 0 ≤ branch_box_6893.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6893, Box.profileLo, Box.profileHi, box_6893]
theorem leaf_6893_BranchSafe : CertificateConsequences.BranchSafe branch_box_6893 := by
  left; refine ⟨branch_box_6893_nonnegative, ?_⟩
  intro z hz; exact leaf_6893_sound hz

theorem leaf_6895_ok : checkAt 527 1000 box_6895 cert_6895 = true := by
  have h := List.all_eq_true.mp batch_137_15_ok accepted_6895 (by simp [batch_137_15_values])
  exact h
theorem leaf_6895_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6895.profileLo box_6895.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6895_ok
theorem branch_box_6895_nonnegative : ∀ j, 0 ≤ branch_box_6895.lower j ∧ 0 ≤ branch_box_6895.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6895, Box.profileLo, Box.profileHi, box_6895]
theorem leaf_6895_BranchSafe : CertificateConsequences.BranchSafe branch_box_6895 := by
  left; refine ⟨branch_box_6895_nonnegative, ?_⟩
  intro z hz; exact leaf_6895_sound hz

theorem leaf_6896_ok : checkAt 527 1000 box_6896 cert_6896 = true := by
  have h := List.all_eq_true.mp batch_137_16_ok accepted_6896 (by simp [batch_137_16_values])
  exact h
theorem leaf_6896_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6896.profileLo box_6896.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6896_ok
theorem branch_box_6896_nonnegative : ∀ j, 0 ≤ branch_box_6896.lower j ∧ 0 ≤ branch_box_6896.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6896, Box.profileLo, Box.profileHi, box_6896]
theorem leaf_6896_BranchSafe : CertificateConsequences.BranchSafe branch_box_6896 := by
  left; refine ⟨branch_box_6896_nonnegative, ?_⟩
  intro z hz; exact leaf_6896_sound hz

#print axioms batch_137_00_ok
#print axioms leaf_6850_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
