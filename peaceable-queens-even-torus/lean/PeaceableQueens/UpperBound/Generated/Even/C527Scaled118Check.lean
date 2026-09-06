import PeaceableQueens.UpperBound.Generated.Even.C527Scaled118Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_118_00_values : List Bool := [accepted_5900]
theorem batch_118_00_ok : batch_118_00_values.all id = true := by decide

def batch_118_01_values : List Bool := [accepted_5901]
theorem batch_118_01_ok : batch_118_01_values.all id = true := by decide

def batch_118_02_values : List Bool := [accepted_5910]
theorem batch_118_02_ok : batch_118_02_values.all id = true := by decide

def batch_118_03_values : List Bool := [accepted_5914]
theorem batch_118_03_ok : batch_118_03_values.all id = true := by decide

def batch_118_04_values : List Bool := [accepted_5917]
theorem batch_118_04_ok : batch_118_04_values.all id = true := by decide

def batch_118_05_values : List Bool := [accepted_5918]
theorem batch_118_05_ok : batch_118_05_values.all id = true := by decide

def batch_118_06_values : List Bool := [accepted_5920]
theorem batch_118_06_ok : batch_118_06_values.all id = true := by decide

def batch_118_07_values : List Bool := [accepted_5922]
theorem batch_118_07_ok : batch_118_07_values.all id = true := by decide

def batch_118_08_values : List Bool := [accepted_5925]
theorem batch_118_08_ok : batch_118_08_values.all id = true := by decide

def batch_118_09_values : List Bool := [accepted_5926]
theorem batch_118_09_ok : batch_118_09_values.all id = true := by decide

def batch_118_10_values : List Bool := [accepted_5928]
theorem batch_118_10_ok : batch_118_10_values.all id = true := by decide

def batch_118_11_values : List Bool := [accepted_5929]
theorem batch_118_11_ok : batch_118_11_values.all id = true := by decide

def batch_118_12_values : List Bool := [accepted_5932]
theorem batch_118_12_ok : batch_118_12_values.all id = true := by decide

def batch_118_13_values : List Bool := [accepted_5934]
theorem batch_118_13_ok : batch_118_13_values.all id = true := by decide

def batch_118_14_values : List Bool := [accepted_5935]
theorem batch_118_14_ok : batch_118_14_values.all id = true := by decide

def batch_118_15_values : List Bool := [accepted_5936]
theorem batch_118_15_ok : batch_118_15_values.all id = true := by decide

def batch_118_16_values : List Bool := [accepted_5943]
theorem batch_118_16_ok : batch_118_16_values.all id = true := by decide

def batch_118_17_values : List Bool := [accepted_5945]
theorem batch_118_17_ok : batch_118_17_values.all id = true := by decide

def batch_118_18_values : List Bool := [accepted_5946]
theorem batch_118_18_ok : batch_118_18_values.all id = true := by decide

theorem leaf_5900_ok : checkAt 527 1000 box_5900 cert_5900 = true := by
  have h := List.all_eq_true.mp batch_118_00_ok accepted_5900 (by simp [batch_118_00_values])
  exact h
theorem leaf_5900_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5900.profileLo box_5900.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5900_ok
theorem branch_box_5900_nonnegative : ∀ j, 0 ≤ branch_box_5900.lower j ∧ 0 ≤ branch_box_5900.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5900, Box.profileLo, Box.profileHi, box_5900]
theorem leaf_5900_BranchSafe : CertificateConsequences.BranchSafe branch_box_5900 := by
  left; refine ⟨branch_box_5900_nonnegative, ?_⟩
  intro z hz; exact leaf_5900_sound hz

theorem leaf_5901_ok : checkAt 527 1000 box_5901 cert_5901 = true := by
  have h := List.all_eq_true.mp batch_118_01_ok accepted_5901 (by simp [batch_118_01_values])
  exact h
theorem leaf_5901_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5901.profileLo box_5901.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5901_ok
theorem branch_box_5901_nonnegative : ∀ j, 0 ≤ branch_box_5901.lower j ∧ 0 ≤ branch_box_5901.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5901, Box.profileLo, Box.profileHi, box_5901]
theorem leaf_5901_BranchSafe : CertificateConsequences.BranchSafe branch_box_5901 := by
  left; refine ⟨branch_box_5901_nonnegative, ?_⟩
  intro z hz; exact leaf_5901_sound hz

theorem leaf_5910_ok : checkAt 527 1000 box_5910 cert_5910 = true := by
  have h := List.all_eq_true.mp batch_118_02_ok accepted_5910 (by simp [batch_118_02_values])
  exact h
theorem leaf_5910_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5910.profileLo box_5910.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5910_ok
theorem branch_box_5910_nonnegative : ∀ j, 0 ≤ branch_box_5910.lower j ∧ 0 ≤ branch_box_5910.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5910, Box.profileLo, Box.profileHi, box_5910]
theorem leaf_5910_BranchSafe : CertificateConsequences.BranchSafe branch_box_5910 := by
  left; refine ⟨branch_box_5910_nonnegative, ?_⟩
  intro z hz; exact leaf_5910_sound hz

theorem leaf_5914_ok : checkAt 527 1000 box_5914 cert_5914 = true := by
  have h := List.all_eq_true.mp batch_118_03_ok accepted_5914 (by simp [batch_118_03_values])
  exact h
theorem leaf_5914_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5914.profileLo box_5914.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5914_ok
theorem branch_box_5914_nonnegative : ∀ j, 0 ≤ branch_box_5914.lower j ∧ 0 ≤ branch_box_5914.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5914, Box.profileLo, Box.profileHi, box_5914]
theorem leaf_5914_BranchSafe : CertificateConsequences.BranchSafe branch_box_5914 := by
  left; refine ⟨branch_box_5914_nonnegative, ?_⟩
  intro z hz; exact leaf_5914_sound hz

theorem leaf_5917_ok : checkAt 527 1000 box_5917 cert_5917 = true := by
  have h := List.all_eq_true.mp batch_118_04_ok accepted_5917 (by simp [batch_118_04_values])
  exact h
theorem leaf_5917_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5917.profileLo box_5917.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5917_ok
theorem branch_box_5917_nonnegative : ∀ j, 0 ≤ branch_box_5917.lower j ∧ 0 ≤ branch_box_5917.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5917, Box.profileLo, Box.profileHi, box_5917]
theorem leaf_5917_BranchSafe : CertificateConsequences.BranchSafe branch_box_5917 := by
  left; refine ⟨branch_box_5917_nonnegative, ?_⟩
  intro z hz; exact leaf_5917_sound hz

theorem leaf_5918_ok : checkAt 527 1000 box_5918 cert_5918 = true := by
  have h := List.all_eq_true.mp batch_118_05_ok accepted_5918 (by simp [batch_118_05_values])
  exact h
theorem leaf_5918_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5918.profileLo box_5918.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5918_ok
theorem branch_box_5918_nonnegative : ∀ j, 0 ≤ branch_box_5918.lower j ∧ 0 ≤ branch_box_5918.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5918, Box.profileLo, Box.profileHi, box_5918]
theorem leaf_5918_BranchSafe : CertificateConsequences.BranchSafe branch_box_5918 := by
  left; refine ⟨branch_box_5918_nonnegative, ?_⟩
  intro z hz; exact leaf_5918_sound hz

theorem leaf_5920_ok : checkAt 527 1000 box_5920 cert_5920 = true := by
  have h := List.all_eq_true.mp batch_118_06_ok accepted_5920 (by simp [batch_118_06_values])
  exact h
theorem leaf_5920_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5920.profileLo box_5920.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5920_ok
theorem branch_box_5920_nonnegative : ∀ j, 0 ≤ branch_box_5920.lower j ∧ 0 ≤ branch_box_5920.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5920, Box.profileLo, Box.profileHi, box_5920]
theorem leaf_5920_BranchSafe : CertificateConsequences.BranchSafe branch_box_5920 := by
  left; refine ⟨branch_box_5920_nonnegative, ?_⟩
  intro z hz; exact leaf_5920_sound hz

theorem leaf_5922_ok : checkAt 527 1000 box_5922 cert_5922 = true := by
  have h := List.all_eq_true.mp batch_118_07_ok accepted_5922 (by simp [batch_118_07_values])
  exact h
theorem leaf_5922_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5922.profileLo box_5922.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5922_ok
theorem branch_box_5922_nonnegative : ∀ j, 0 ≤ branch_box_5922.lower j ∧ 0 ≤ branch_box_5922.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5922, Box.profileLo, Box.profileHi, box_5922]
theorem leaf_5922_BranchSafe : CertificateConsequences.BranchSafe branch_box_5922 := by
  left; refine ⟨branch_box_5922_nonnegative, ?_⟩
  intro z hz; exact leaf_5922_sound hz

theorem leaf_5925_ok : checkAt 527 1000 box_5925 cert_5925 = true := by
  have h := List.all_eq_true.mp batch_118_08_ok accepted_5925 (by simp [batch_118_08_values])
  exact h
theorem leaf_5925_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5925.profileLo box_5925.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5925_ok
theorem branch_box_5925_nonnegative : ∀ j, 0 ≤ branch_box_5925.lower j ∧ 0 ≤ branch_box_5925.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5925, Box.profileLo, Box.profileHi, box_5925]
theorem leaf_5925_BranchSafe : CertificateConsequences.BranchSafe branch_box_5925 := by
  left; refine ⟨branch_box_5925_nonnegative, ?_⟩
  intro z hz; exact leaf_5925_sound hz

theorem leaf_5926_ok : checkAt 527 1000 box_5926 cert_5926 = true := by
  have h := List.all_eq_true.mp batch_118_09_ok accepted_5926 (by simp [batch_118_09_values])
  exact h
theorem leaf_5926_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5926.profileLo box_5926.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5926_ok
theorem branch_box_5926_nonnegative : ∀ j, 0 ≤ branch_box_5926.lower j ∧ 0 ≤ branch_box_5926.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5926, Box.profileLo, Box.profileHi, box_5926]
theorem leaf_5926_BranchSafe : CertificateConsequences.BranchSafe branch_box_5926 := by
  left; refine ⟨branch_box_5926_nonnegative, ?_⟩
  intro z hz; exact leaf_5926_sound hz

theorem leaf_5928_ok : checkAt 527 1000 box_5928 cert_5928 = true := by
  have h := List.all_eq_true.mp batch_118_10_ok accepted_5928 (by simp [batch_118_10_values])
  exact h
theorem leaf_5928_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5928.profileLo box_5928.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5928_ok
theorem branch_box_5928_nonnegative : ∀ j, 0 ≤ branch_box_5928.lower j ∧ 0 ≤ branch_box_5928.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5928, Box.profileLo, Box.profileHi, box_5928]
theorem leaf_5928_BranchSafe : CertificateConsequences.BranchSafe branch_box_5928 := by
  left; refine ⟨branch_box_5928_nonnegative, ?_⟩
  intro z hz; exact leaf_5928_sound hz

theorem leaf_5929_ok : checkAt 527 1000 box_5929 cert_5929 = true := by
  have h := List.all_eq_true.mp batch_118_11_ok accepted_5929 (by simp [batch_118_11_values])
  exact h
theorem leaf_5929_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5929.profileLo box_5929.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5929_ok
theorem branch_box_5929_nonnegative : ∀ j, 0 ≤ branch_box_5929.lower j ∧ 0 ≤ branch_box_5929.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5929, Box.profileLo, Box.profileHi, box_5929]
theorem leaf_5929_BranchSafe : CertificateConsequences.BranchSafe branch_box_5929 := by
  left; refine ⟨branch_box_5929_nonnegative, ?_⟩
  intro z hz; exact leaf_5929_sound hz

theorem leaf_5932_ok : checkAt 527 1000 box_5932 cert_5932 = true := by
  have h := List.all_eq_true.mp batch_118_12_ok accepted_5932 (by simp [batch_118_12_values])
  exact h
theorem leaf_5932_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5932.profileLo box_5932.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5932_ok
theorem branch_box_5932_nonnegative : ∀ j, 0 ≤ branch_box_5932.lower j ∧ 0 ≤ branch_box_5932.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5932, Box.profileLo, Box.profileHi, box_5932]
theorem leaf_5932_BranchSafe : CertificateConsequences.BranchSafe branch_box_5932 := by
  left; refine ⟨branch_box_5932_nonnegative, ?_⟩
  intro z hz; exact leaf_5932_sound hz

theorem leaf_5934_ok : checkAt 527 1000 box_5934 cert_5934 = true := by
  have h := List.all_eq_true.mp batch_118_13_ok accepted_5934 (by simp [batch_118_13_values])
  exact h
theorem leaf_5934_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5934.profileLo box_5934.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5934_ok
theorem branch_box_5934_nonnegative : ∀ j, 0 ≤ branch_box_5934.lower j ∧ 0 ≤ branch_box_5934.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5934, Box.profileLo, Box.profileHi, box_5934]
theorem leaf_5934_BranchSafe : CertificateConsequences.BranchSafe branch_box_5934 := by
  left; refine ⟨branch_box_5934_nonnegative, ?_⟩
  intro z hz; exact leaf_5934_sound hz

theorem leaf_5935_ok : checkAt 527 1000 box_5935 cert_5935 = true := by
  have h := List.all_eq_true.mp batch_118_14_ok accepted_5935 (by simp [batch_118_14_values])
  exact h
theorem leaf_5935_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5935.profileLo box_5935.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5935_ok
theorem branch_box_5935_nonnegative : ∀ j, 0 ≤ branch_box_5935.lower j ∧ 0 ≤ branch_box_5935.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5935, Box.profileLo, Box.profileHi, box_5935]
theorem leaf_5935_BranchSafe : CertificateConsequences.BranchSafe branch_box_5935 := by
  left; refine ⟨branch_box_5935_nonnegative, ?_⟩
  intro z hz; exact leaf_5935_sound hz

theorem leaf_5936_ok : checkAt 527 1000 box_5936 cert_5936 = true := by
  have h := List.all_eq_true.mp batch_118_15_ok accepted_5936 (by simp [batch_118_15_values])
  exact h
theorem leaf_5936_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5936.profileLo box_5936.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5936_ok
theorem branch_box_5936_nonnegative : ∀ j, 0 ≤ branch_box_5936.lower j ∧ 0 ≤ branch_box_5936.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5936, Box.profileLo, Box.profileHi, box_5936]
theorem leaf_5936_BranchSafe : CertificateConsequences.BranchSafe branch_box_5936 := by
  left; refine ⟨branch_box_5936_nonnegative, ?_⟩
  intro z hz; exact leaf_5936_sound hz

theorem leaf_5943_ok : checkAt 527 1000 box_5943 cert_5943 = true := by
  have h := List.all_eq_true.mp batch_118_16_ok accepted_5943 (by simp [batch_118_16_values])
  exact h
theorem leaf_5943_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5943.profileLo box_5943.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5943_ok
theorem branch_box_5943_nonnegative : ∀ j, 0 ≤ branch_box_5943.lower j ∧ 0 ≤ branch_box_5943.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5943, Box.profileLo, Box.profileHi, box_5943]
theorem leaf_5943_BranchSafe : CertificateConsequences.BranchSafe branch_box_5943 := by
  left; refine ⟨branch_box_5943_nonnegative, ?_⟩
  intro z hz; exact leaf_5943_sound hz

theorem leaf_5945_ok : checkAt 527 1000 box_5945 cert_5945 = true := by
  have h := List.all_eq_true.mp batch_118_17_ok accepted_5945 (by simp [batch_118_17_values])
  exact h
theorem leaf_5945_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5945.profileLo box_5945.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5945_ok
theorem branch_box_5945_nonnegative : ∀ j, 0 ≤ branch_box_5945.lower j ∧ 0 ≤ branch_box_5945.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5945, Box.profileLo, Box.profileHi, box_5945]
theorem leaf_5945_BranchSafe : CertificateConsequences.BranchSafe branch_box_5945 := by
  left; refine ⟨branch_box_5945_nonnegative, ?_⟩
  intro z hz; exact leaf_5945_sound hz

theorem leaf_5946_ok : checkAt 527 1000 box_5946 cert_5946 = true := by
  have h := List.all_eq_true.mp batch_118_18_ok accepted_5946 (by simp [batch_118_18_values])
  exact h
theorem leaf_5946_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5946.profileLo box_5946.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5946_ok
theorem branch_box_5946_nonnegative : ∀ j, 0 ≤ branch_box_5946.lower j ∧ 0 ≤ branch_box_5946.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5946, Box.profileLo, Box.profileHi, box_5946]
theorem leaf_5946_BranchSafe : CertificateConsequences.BranchSafe branch_box_5946 := by
  left; refine ⟨branch_box_5946_nonnegative, ?_⟩
  intro z hz; exact leaf_5946_sound hz

#print axioms batch_118_00_ok
#print axioms leaf_5900_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
