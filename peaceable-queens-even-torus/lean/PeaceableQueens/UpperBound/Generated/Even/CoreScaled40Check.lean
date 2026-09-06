import PeaceableQueens.UpperBound.Generated.Even.CoreScaled40Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_40_00_values : List Bool := [accepted_2000]
theorem batch_40_00_ok : batch_40_00_values.all id = true := by decide

def batch_40_01_values : List Bool := [accepted_2002]
theorem batch_40_01_ok : batch_40_01_values.all id = true := by decide

def batch_40_02_values : List Bool := [accepted_2003]
theorem batch_40_02_ok : batch_40_02_values.all id = true := by decide

def batch_40_03_values : List Bool := [accepted_2005]
theorem batch_40_03_ok : batch_40_03_values.all id = true := by decide

def batch_40_04_values : List Bool := [accepted_2010]
theorem batch_40_04_ok : batch_40_04_values.all id = true := by decide

def batch_40_05_values : List Bool := [accepted_2011]
theorem batch_40_05_ok : batch_40_05_values.all id = true := by decide

def batch_40_06_values : List Bool := [accepted_2023]
theorem batch_40_06_ok : batch_40_06_values.all id = true := by decide

def batch_40_07_values : List Bool := [accepted_2025]
theorem batch_40_07_ok : batch_40_07_values.all id = true := by decide

def batch_40_08_values : List Bool := [accepted_2031]
theorem batch_40_08_ok : batch_40_08_values.all id = true := by decide

def batch_40_09_values : List Bool := [accepted_2033]
theorem batch_40_09_ok : batch_40_09_values.all id = true := by decide

def batch_40_10_values : List Bool := [accepted_2036]
theorem batch_40_10_ok : batch_40_10_values.all id = true := by decide

def batch_40_11_values : List Bool := [accepted_2047]
theorem batch_40_11_ok : batch_40_11_values.all id = true := by decide

def batch_40_12_values : List Bool := [accepted_2049]
theorem batch_40_12_ok : batch_40_12_values.all id = true := by decide

theorem leaf_2000_ok : checkAt 527 1000 box_2000 cert_2000 = true := by
  have h := List.all_eq_true.mp batch_40_00_ok accepted_2000 (by simp [batch_40_00_values])
  exact h
theorem leaf_2000_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2000.profileLo box_2000.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2000_ok
theorem branch_box_2000_nonnegative : ∀ j, 0 ≤ branch_box_2000.lower j ∧ 0 ≤ branch_box_2000.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2000, Box.profileLo, Box.profileHi, box_2000]
theorem leaf_2000_BranchSafe : CertificateConsequences.BranchSafe branch_box_2000 := by
  left; refine ⟨branch_box_2000_nonnegative, ?_⟩
  intro z hz; exact leaf_2000_sound hz

theorem leaf_2002_ok : checkAt 527 1000 box_2002 cert_2002 = true := by
  have h := List.all_eq_true.mp batch_40_01_ok accepted_2002 (by simp [batch_40_01_values])
  exact h
theorem leaf_2002_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2002.profileLo box_2002.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2002_ok
theorem branch_box_2002_nonnegative : ∀ j, 0 ≤ branch_box_2002.lower j ∧ 0 ≤ branch_box_2002.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2002, Box.profileLo, Box.profileHi, box_2002]
theorem leaf_2002_BranchSafe : CertificateConsequences.BranchSafe branch_box_2002 := by
  left; refine ⟨branch_box_2002_nonnegative, ?_⟩
  intro z hz; exact leaf_2002_sound hz

theorem leaf_2003_ok : checkAt 527 1000 box_2003 cert_2003 = true := by
  have h := List.all_eq_true.mp batch_40_02_ok accepted_2003 (by simp [batch_40_02_values])
  exact h
theorem leaf_2003_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2003.profileLo box_2003.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2003_ok
theorem branch_box_2003_nonnegative : ∀ j, 0 ≤ branch_box_2003.lower j ∧ 0 ≤ branch_box_2003.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2003, Box.profileLo, Box.profileHi, box_2003]
theorem leaf_2003_BranchSafe : CertificateConsequences.BranchSafe branch_box_2003 := by
  left; refine ⟨branch_box_2003_nonnegative, ?_⟩
  intro z hz; exact leaf_2003_sound hz

theorem leaf_2005_ok : checkAt 527 1000 box_2005 cert_2005 = true := by
  have h := List.all_eq_true.mp batch_40_03_ok accepted_2005 (by simp [batch_40_03_values])
  exact h
theorem leaf_2005_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2005.profileLo box_2005.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2005_ok
theorem branch_box_2005_nonnegative : ∀ j, 0 ≤ branch_box_2005.lower j ∧ 0 ≤ branch_box_2005.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2005, Box.profileLo, Box.profileHi, box_2005]
theorem leaf_2005_BranchSafe : CertificateConsequences.BranchSafe branch_box_2005 := by
  left; refine ⟨branch_box_2005_nonnegative, ?_⟩
  intro z hz; exact leaf_2005_sound hz

theorem leaf_2010_ok : checkAt 527 1000 box_2010 cert_2010 = true := by
  have h := List.all_eq_true.mp batch_40_04_ok accepted_2010 (by simp [batch_40_04_values])
  exact h
theorem leaf_2010_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2010.profileLo box_2010.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2010_ok
theorem branch_box_2010_nonnegative : ∀ j, 0 ≤ branch_box_2010.lower j ∧ 0 ≤ branch_box_2010.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2010, Box.profileLo, Box.profileHi, box_2010]
theorem leaf_2010_BranchSafe : CertificateConsequences.BranchSafe branch_box_2010 := by
  left; refine ⟨branch_box_2010_nonnegative, ?_⟩
  intro z hz; exact leaf_2010_sound hz

theorem leaf_2011_ok : checkAt 527 1000 box_2011 cert_2011 = true := by
  have h := List.all_eq_true.mp batch_40_05_ok accepted_2011 (by simp [batch_40_05_values])
  exact h
theorem leaf_2011_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2011.profileLo box_2011.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2011_ok
theorem branch_box_2011_nonnegative : ∀ j, 0 ≤ branch_box_2011.lower j ∧ 0 ≤ branch_box_2011.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2011, Box.profileLo, Box.profileHi, box_2011]
theorem leaf_2011_BranchSafe : CertificateConsequences.BranchSafe branch_box_2011 := by
  left; refine ⟨branch_box_2011_nonnegative, ?_⟩
  intro z hz; exact leaf_2011_sound hz

theorem leaf_2023_ok : checkAt 527 1000 box_2023 cert_2023 = true := by
  have h := List.all_eq_true.mp batch_40_06_ok accepted_2023 (by simp [batch_40_06_values])
  exact h
theorem leaf_2023_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2023.profileLo box_2023.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2023_ok
theorem branch_box_2023_nonnegative : ∀ j, 0 ≤ branch_box_2023.lower j ∧ 0 ≤ branch_box_2023.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2023, Box.profileLo, Box.profileHi, box_2023]
theorem leaf_2023_BranchSafe : CertificateConsequences.BranchSafe branch_box_2023 := by
  left; refine ⟨branch_box_2023_nonnegative, ?_⟩
  intro z hz; exact leaf_2023_sound hz

theorem leaf_2025_ok : checkAt 527 1000 box_2025 cert_2025 = true := by
  have h := List.all_eq_true.mp batch_40_07_ok accepted_2025 (by simp [batch_40_07_values])
  exact h
theorem leaf_2025_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2025.profileLo box_2025.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2025_ok
theorem branch_box_2025_nonnegative : ∀ j, 0 ≤ branch_box_2025.lower j ∧ 0 ≤ branch_box_2025.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2025, Box.profileLo, Box.profileHi, box_2025]
theorem leaf_2025_BranchSafe : CertificateConsequences.BranchSafe branch_box_2025 := by
  left; refine ⟨branch_box_2025_nonnegative, ?_⟩
  intro z hz; exact leaf_2025_sound hz

theorem leaf_2031_ok : checkAt 527 1000 box_2031 cert_2031 = true := by
  have h := List.all_eq_true.mp batch_40_08_ok accepted_2031 (by simp [batch_40_08_values])
  exact h
theorem leaf_2031_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2031.profileLo box_2031.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2031_ok
theorem branch_box_2031_nonnegative : ∀ j, 0 ≤ branch_box_2031.lower j ∧ 0 ≤ branch_box_2031.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2031, Box.profileLo, Box.profileHi, box_2031]
theorem leaf_2031_BranchSafe : CertificateConsequences.BranchSafe branch_box_2031 := by
  left; refine ⟨branch_box_2031_nonnegative, ?_⟩
  intro z hz; exact leaf_2031_sound hz

theorem leaf_2033_ok : checkAt 527 1000 box_2033 cert_2033 = true := by
  have h := List.all_eq_true.mp batch_40_09_ok accepted_2033 (by simp [batch_40_09_values])
  exact h
theorem leaf_2033_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2033.profileLo box_2033.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2033_ok
theorem branch_box_2033_nonnegative : ∀ j, 0 ≤ branch_box_2033.lower j ∧ 0 ≤ branch_box_2033.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2033, Box.profileLo, Box.profileHi, box_2033]
theorem leaf_2033_BranchSafe : CertificateConsequences.BranchSafe branch_box_2033 := by
  left; refine ⟨branch_box_2033_nonnegative, ?_⟩
  intro z hz; exact leaf_2033_sound hz

theorem leaf_2036_ok : checkAt 527 1000 box_2036 cert_2036 = true := by
  have h := List.all_eq_true.mp batch_40_10_ok accepted_2036 (by simp [batch_40_10_values])
  exact h
theorem leaf_2036_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2036.profileLo box_2036.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2036_ok
theorem branch_box_2036_nonnegative : ∀ j, 0 ≤ branch_box_2036.lower j ∧ 0 ≤ branch_box_2036.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2036, Box.profileLo, Box.profileHi, box_2036]
theorem leaf_2036_BranchSafe : CertificateConsequences.BranchSafe branch_box_2036 := by
  left; refine ⟨branch_box_2036_nonnegative, ?_⟩
  intro z hz; exact leaf_2036_sound hz

theorem leaf_2047_ok : checkAt 527 1000 box_2047 cert_2047 = true := by
  have h := List.all_eq_true.mp batch_40_11_ok accepted_2047 (by simp [batch_40_11_values])
  exact h
theorem leaf_2047_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2047.profileLo box_2047.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2047_ok
theorem branch_box_2047_nonnegative : ∀ j, 0 ≤ branch_box_2047.lower j ∧ 0 ≤ branch_box_2047.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2047, Box.profileLo, Box.profileHi, box_2047]
theorem leaf_2047_BranchSafe : CertificateConsequences.BranchSafe branch_box_2047 := by
  left; refine ⟨branch_box_2047_nonnegative, ?_⟩
  intro z hz; exact leaf_2047_sound hz

theorem leaf_2049_ok : checkAt 527 1000 box_2049 cert_2049 = true := by
  have h := List.all_eq_true.mp batch_40_12_ok accepted_2049 (by simp [batch_40_12_values])
  exact h
theorem leaf_2049_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2049.profileLo box_2049.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2049_ok
theorem branch_box_2049_nonnegative : ∀ j, 0 ≤ branch_box_2049.lower j ∧ 0 ≤ branch_box_2049.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2049, Box.profileLo, Box.profileHi, box_2049]
theorem leaf_2049_BranchSafe : CertificateConsequences.BranchSafe branch_box_2049 := by
  left; refine ⟨branch_box_2049_nonnegative, ?_⟩
  intro z hz; exact leaf_2049_sound hz

#print axioms batch_40_00_ok
#print axioms leaf_2000_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
