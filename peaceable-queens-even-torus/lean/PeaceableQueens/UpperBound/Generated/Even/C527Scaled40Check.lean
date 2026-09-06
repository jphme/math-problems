import PeaceableQueens.UpperBound.Generated.Even.C527Scaled40Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_40_00_values : List Bool := [accepted_2002]
theorem batch_40_00_ok : batch_40_00_values.all id = true := by decide

def batch_40_01_values : List Bool := [accepted_2004]
theorem batch_40_01_ok : batch_40_01_values.all id = true := by decide

def batch_40_02_values : List Bool := [accepted_2005]
theorem batch_40_02_ok : batch_40_02_values.all id = true := by decide

def batch_40_03_values : List Bool := [accepted_2006]
theorem batch_40_03_ok : batch_40_03_values.all id = true := by decide

def batch_40_04_values : List Bool := [accepted_2016]
theorem batch_40_04_ok : batch_40_04_values.all id = true := by decide

def batch_40_05_values : List Bool := [accepted_2018]
theorem batch_40_05_ok : batch_40_05_values.all id = true := by decide

def batch_40_06_values : List Bool := [accepted_2019]
theorem batch_40_06_ok : batch_40_06_values.all id = true := by decide

def batch_40_07_values : List Bool := [accepted_2020]
theorem batch_40_07_ok : batch_40_07_values.all id = true := by decide

def batch_40_08_values : List Bool := [accepted_2024]
theorem batch_40_08_ok : batch_40_08_values.all id = true := by decide

def batch_40_09_values : List Bool := [accepted_2025]
theorem batch_40_09_ok : batch_40_09_values.all id = true := by decide

def batch_40_10_values : List Bool := [accepted_2026]
theorem batch_40_10_ok : batch_40_10_values.all id = true := by decide

def batch_40_11_values : List Bool := [accepted_2029]
theorem batch_40_11_ok : batch_40_11_values.all id = true := by decide

def batch_40_12_values : List Bool := [accepted_2031]
theorem batch_40_12_ok : batch_40_12_values.all id = true := by decide

def batch_40_13_values : List Bool := [accepted_2032]
theorem batch_40_13_ok : batch_40_13_values.all id = true := by decide

def batch_40_14_values : List Bool := [accepted_2033]
theorem batch_40_14_ok : batch_40_14_values.all id = true := by decide

def batch_40_15_values : List Bool := [accepted_2034]
theorem batch_40_15_ok : batch_40_15_values.all id = true := by decide

def batch_40_16_values : List Bool := [accepted_2038]
theorem batch_40_16_ok : batch_40_16_values.all id = true := by decide

def batch_40_17_values : List Bool := [accepted_2039]
theorem batch_40_17_ok : batch_40_17_values.all id = true := by decide

def batch_40_18_values : List Bool := [accepted_2040]
theorem batch_40_18_ok : batch_40_18_values.all id = true := by decide

def batch_40_19_values : List Bool := [accepted_2044]
theorem batch_40_19_ok : batch_40_19_values.all id = true := by decide

def batch_40_20_values : List Bool := [accepted_2045]
theorem batch_40_20_ok : batch_40_20_values.all id = true := by decide

def batch_40_21_values : List Bool := [accepted_2047]
theorem batch_40_21_ok : batch_40_21_values.all id = true := by decide

def batch_40_22_values : List Bool := [accepted_2048]
theorem batch_40_22_ok : batch_40_22_values.all id = true := by decide

def batch_40_23_values : List Bool := [accepted_2049]
theorem batch_40_23_ok : batch_40_23_values.all id = true := by decide

theorem leaf_2002_ok : checkAt 527 1000 box_2002 cert_2002 = true := by
  have h := List.all_eq_true.mp batch_40_00_ok accepted_2002 (by simp [batch_40_00_values])
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

theorem leaf_2004_ok : checkAt 527 1000 box_2004 cert_2004 = true := by
  have h := List.all_eq_true.mp batch_40_01_ok accepted_2004 (by simp [batch_40_01_values])
  exact h
theorem leaf_2004_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2004.profileLo box_2004.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2004_ok
theorem branch_box_2004_nonnegative : ∀ j, 0 ≤ branch_box_2004.lower j ∧ 0 ≤ branch_box_2004.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2004, Box.profileLo, Box.profileHi, box_2004]
theorem leaf_2004_BranchSafe : CertificateConsequences.BranchSafe branch_box_2004 := by
  left; refine ⟨branch_box_2004_nonnegative, ?_⟩
  intro z hz; exact leaf_2004_sound hz

theorem leaf_2005_ok : checkAt 527 1000 box_2005 cert_2005 = true := by
  have h := List.all_eq_true.mp batch_40_02_ok accepted_2005 (by simp [batch_40_02_values])
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

theorem leaf_2006_ok : checkAt 527 1000 box_2006 cert_2006 = true := by
  have h := List.all_eq_true.mp batch_40_03_ok accepted_2006 (by simp [batch_40_03_values])
  exact h
theorem leaf_2006_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2006.profileLo box_2006.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2006_ok
theorem branch_box_2006_nonnegative : ∀ j, 0 ≤ branch_box_2006.lower j ∧ 0 ≤ branch_box_2006.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2006, Box.profileLo, Box.profileHi, box_2006]
theorem leaf_2006_BranchSafe : CertificateConsequences.BranchSafe branch_box_2006 := by
  left; refine ⟨branch_box_2006_nonnegative, ?_⟩
  intro z hz; exact leaf_2006_sound hz

theorem leaf_2016_ok : checkAt 527 1000 box_2016 cert_2016 = true := by
  have h := List.all_eq_true.mp batch_40_04_ok accepted_2016 (by simp [batch_40_04_values])
  exact h
theorem leaf_2016_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2016.profileLo box_2016.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2016_ok
theorem branch_box_2016_nonnegative : ∀ j, 0 ≤ branch_box_2016.lower j ∧ 0 ≤ branch_box_2016.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2016, Box.profileLo, Box.profileHi, box_2016]
theorem leaf_2016_BranchSafe : CertificateConsequences.BranchSafe branch_box_2016 := by
  left; refine ⟨branch_box_2016_nonnegative, ?_⟩
  intro z hz; exact leaf_2016_sound hz

theorem leaf_2018_ok : checkAt 527 1000 box_2018 cert_2018 = true := by
  have h := List.all_eq_true.mp batch_40_05_ok accepted_2018 (by simp [batch_40_05_values])
  exact h
theorem leaf_2018_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2018.profileLo box_2018.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2018_ok
theorem branch_box_2018_nonnegative : ∀ j, 0 ≤ branch_box_2018.lower j ∧ 0 ≤ branch_box_2018.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2018, Box.profileLo, Box.profileHi, box_2018]
theorem leaf_2018_BranchSafe : CertificateConsequences.BranchSafe branch_box_2018 := by
  left; refine ⟨branch_box_2018_nonnegative, ?_⟩
  intro z hz; exact leaf_2018_sound hz

theorem leaf_2019_ok : checkAt 527 1000 box_2019 cert_2019 = true := by
  have h := List.all_eq_true.mp batch_40_06_ok accepted_2019 (by simp [batch_40_06_values])
  exact h
theorem leaf_2019_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2019.profileLo box_2019.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2019_ok
theorem branch_box_2019_nonnegative : ∀ j, 0 ≤ branch_box_2019.lower j ∧ 0 ≤ branch_box_2019.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2019, Box.profileLo, Box.profileHi, box_2019]
theorem leaf_2019_BranchSafe : CertificateConsequences.BranchSafe branch_box_2019 := by
  left; refine ⟨branch_box_2019_nonnegative, ?_⟩
  intro z hz; exact leaf_2019_sound hz

theorem leaf_2020_ok : checkAt 527 1000 box_2020 cert_2020 = true := by
  have h := List.all_eq_true.mp batch_40_07_ok accepted_2020 (by simp [batch_40_07_values])
  exact h
theorem leaf_2020_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2020.profileLo box_2020.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2020_ok
theorem branch_box_2020_nonnegative : ∀ j, 0 ≤ branch_box_2020.lower j ∧ 0 ≤ branch_box_2020.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2020, Box.profileLo, Box.profileHi, box_2020]
theorem leaf_2020_BranchSafe : CertificateConsequences.BranchSafe branch_box_2020 := by
  left; refine ⟨branch_box_2020_nonnegative, ?_⟩
  intro z hz; exact leaf_2020_sound hz

theorem leaf_2024_ok : checkAt 527 1000 box_2024 cert_2024 = true := by
  have h := List.all_eq_true.mp batch_40_08_ok accepted_2024 (by simp [batch_40_08_values])
  exact h
theorem leaf_2024_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2024.profileLo box_2024.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2024_ok
theorem branch_box_2024_nonnegative : ∀ j, 0 ≤ branch_box_2024.lower j ∧ 0 ≤ branch_box_2024.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2024, Box.profileLo, Box.profileHi, box_2024]
theorem leaf_2024_BranchSafe : CertificateConsequences.BranchSafe branch_box_2024 := by
  left; refine ⟨branch_box_2024_nonnegative, ?_⟩
  intro z hz; exact leaf_2024_sound hz

theorem leaf_2025_ok : checkAt 527 1000 box_2025 cert_2025 = true := by
  have h := List.all_eq_true.mp batch_40_09_ok accepted_2025 (by simp [batch_40_09_values])
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

theorem leaf_2026_ok : checkAt 527 1000 box_2026 cert_2026 = true := by
  have h := List.all_eq_true.mp batch_40_10_ok accepted_2026 (by simp [batch_40_10_values])
  exact h
theorem leaf_2026_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2026.profileLo box_2026.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2026_ok
theorem branch_box_2026_nonnegative : ∀ j, 0 ≤ branch_box_2026.lower j ∧ 0 ≤ branch_box_2026.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2026, Box.profileLo, Box.profileHi, box_2026]
theorem leaf_2026_BranchSafe : CertificateConsequences.BranchSafe branch_box_2026 := by
  left; refine ⟨branch_box_2026_nonnegative, ?_⟩
  intro z hz; exact leaf_2026_sound hz

theorem leaf_2029_ok : checkAt 527 1000 box_2029 cert_2029 = true := by
  have h := List.all_eq_true.mp batch_40_11_ok accepted_2029 (by simp [batch_40_11_values])
  exact h
theorem leaf_2029_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2029.profileLo box_2029.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2029_ok
theorem branch_box_2029_nonnegative : ∀ j, 0 ≤ branch_box_2029.lower j ∧ 0 ≤ branch_box_2029.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2029, Box.profileLo, Box.profileHi, box_2029]
theorem leaf_2029_BranchSafe : CertificateConsequences.BranchSafe branch_box_2029 := by
  left; refine ⟨branch_box_2029_nonnegative, ?_⟩
  intro z hz; exact leaf_2029_sound hz

theorem leaf_2031_ok : checkAt 527 1000 box_2031 cert_2031 = true := by
  have h := List.all_eq_true.mp batch_40_12_ok accepted_2031 (by simp [batch_40_12_values])
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

theorem leaf_2032_ok : checkAt 527 1000 box_2032 cert_2032 = true := by
  have h := List.all_eq_true.mp batch_40_13_ok accepted_2032 (by simp [batch_40_13_values])
  exact h
theorem leaf_2032_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2032.profileLo box_2032.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2032_ok
theorem branch_box_2032_nonnegative : ∀ j, 0 ≤ branch_box_2032.lower j ∧ 0 ≤ branch_box_2032.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2032, Box.profileLo, Box.profileHi, box_2032]
theorem leaf_2032_BranchSafe : CertificateConsequences.BranchSafe branch_box_2032 := by
  left; refine ⟨branch_box_2032_nonnegative, ?_⟩
  intro z hz; exact leaf_2032_sound hz

theorem leaf_2033_ok : checkAt 527 1000 box_2033 cert_2033 = true := by
  have h := List.all_eq_true.mp batch_40_14_ok accepted_2033 (by simp [batch_40_14_values])
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

theorem leaf_2034_ok : checkAt 527 1000 box_2034 cert_2034 = true := by
  have h := List.all_eq_true.mp batch_40_15_ok accepted_2034 (by simp [batch_40_15_values])
  exact h
theorem leaf_2034_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2034.profileLo box_2034.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2034_ok
theorem branch_box_2034_nonnegative : ∀ j, 0 ≤ branch_box_2034.lower j ∧ 0 ≤ branch_box_2034.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2034, Box.profileLo, Box.profileHi, box_2034]
theorem leaf_2034_BranchSafe : CertificateConsequences.BranchSafe branch_box_2034 := by
  left; refine ⟨branch_box_2034_nonnegative, ?_⟩
  intro z hz; exact leaf_2034_sound hz

theorem leaf_2038_ok : checkAt 527 1000 box_2038 cert_2038 = true := by
  have h := List.all_eq_true.mp batch_40_16_ok accepted_2038 (by simp [batch_40_16_values])
  exact h
theorem leaf_2038_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2038.profileLo box_2038.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2038_ok
theorem branch_box_2038_nonnegative : ∀ j, 0 ≤ branch_box_2038.lower j ∧ 0 ≤ branch_box_2038.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2038, Box.profileLo, Box.profileHi, box_2038]
theorem leaf_2038_BranchSafe : CertificateConsequences.BranchSafe branch_box_2038 := by
  left; refine ⟨branch_box_2038_nonnegative, ?_⟩
  intro z hz; exact leaf_2038_sound hz

theorem leaf_2039_ok : checkAt 527 1000 box_2039 cert_2039 = true := by
  have h := List.all_eq_true.mp batch_40_17_ok accepted_2039 (by simp [batch_40_17_values])
  exact h
theorem leaf_2039_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2039.profileLo box_2039.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2039_ok
theorem branch_box_2039_nonnegative : ∀ j, 0 ≤ branch_box_2039.lower j ∧ 0 ≤ branch_box_2039.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2039, Box.profileLo, Box.profileHi, box_2039]
theorem leaf_2039_BranchSafe : CertificateConsequences.BranchSafe branch_box_2039 := by
  left; refine ⟨branch_box_2039_nonnegative, ?_⟩
  intro z hz; exact leaf_2039_sound hz

theorem leaf_2040_ok : checkAt 527 1000 box_2040 cert_2040 = true := by
  have h := List.all_eq_true.mp batch_40_18_ok accepted_2040 (by simp [batch_40_18_values])
  exact h
theorem leaf_2040_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2040.profileLo box_2040.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2040_ok
theorem branch_box_2040_nonnegative : ∀ j, 0 ≤ branch_box_2040.lower j ∧ 0 ≤ branch_box_2040.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2040, Box.profileLo, Box.profileHi, box_2040]
theorem leaf_2040_BranchSafe : CertificateConsequences.BranchSafe branch_box_2040 := by
  left; refine ⟨branch_box_2040_nonnegative, ?_⟩
  intro z hz; exact leaf_2040_sound hz

theorem leaf_2044_ok : checkAt 527 1000 box_2044 cert_2044 = true := by
  have h := List.all_eq_true.mp batch_40_19_ok accepted_2044 (by simp [batch_40_19_values])
  exact h
theorem leaf_2044_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2044.profileLo box_2044.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2044_ok
theorem branch_box_2044_nonnegative : ∀ j, 0 ≤ branch_box_2044.lower j ∧ 0 ≤ branch_box_2044.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2044, Box.profileLo, Box.profileHi, box_2044]
theorem leaf_2044_BranchSafe : CertificateConsequences.BranchSafe branch_box_2044 := by
  left; refine ⟨branch_box_2044_nonnegative, ?_⟩
  intro z hz; exact leaf_2044_sound hz

theorem leaf_2045_ok : checkAt 527 1000 box_2045 cert_2045 = true := by
  have h := List.all_eq_true.mp batch_40_20_ok accepted_2045 (by simp [batch_40_20_values])
  exact h
theorem leaf_2045_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2045.profileLo box_2045.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2045_ok
theorem branch_box_2045_nonnegative : ∀ j, 0 ≤ branch_box_2045.lower j ∧ 0 ≤ branch_box_2045.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2045, Box.profileLo, Box.profileHi, box_2045]
theorem leaf_2045_BranchSafe : CertificateConsequences.BranchSafe branch_box_2045 := by
  left; refine ⟨branch_box_2045_nonnegative, ?_⟩
  intro z hz; exact leaf_2045_sound hz

theorem leaf_2047_ok : checkAt 527 1000 box_2047 cert_2047 = true := by
  have h := List.all_eq_true.mp batch_40_21_ok accepted_2047 (by simp [batch_40_21_values])
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

theorem leaf_2048_ok : checkAt 527 1000 box_2048 cert_2048 = true := by
  have h := List.all_eq_true.mp batch_40_22_ok accepted_2048 (by simp [batch_40_22_values])
  exact h
theorem leaf_2048_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2048.profileLo box_2048.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2048_ok
theorem branch_box_2048_nonnegative : ∀ j, 0 ≤ branch_box_2048.lower j ∧ 0 ≤ branch_box_2048.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2048, Box.profileLo, Box.profileHi, box_2048]
theorem leaf_2048_BranchSafe : CertificateConsequences.BranchSafe branch_box_2048 := by
  left; refine ⟨branch_box_2048_nonnegative, ?_⟩
  intro z hz; exact leaf_2048_sound hz

theorem leaf_2049_ok : checkAt 527 1000 box_2049 cert_2049 = true := by
  have h := List.all_eq_true.mp batch_40_23_ok accepted_2049 (by simp [batch_40_23_values])
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
#print axioms leaf_2002_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
