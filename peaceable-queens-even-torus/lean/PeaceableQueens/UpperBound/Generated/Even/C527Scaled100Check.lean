import PeaceableQueens.UpperBound.Generated.Even.C527Scaled100Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_100_00_values : List Bool := [accepted_5000]
theorem batch_100_00_ok : batch_100_00_values.all id = true := by decide

def batch_100_01_values : List Bool := [accepted_5001]
theorem batch_100_01_ok : batch_100_01_values.all id = true := by decide

def batch_100_02_values : List Bool := [accepted_5002]
theorem batch_100_02_ok : batch_100_02_values.all id = true := by decide

def batch_100_03_values : List Bool := [accepted_5003]
theorem batch_100_03_ok : batch_100_03_values.all id = true := by decide

def batch_100_04_values : List Bool := [accepted_5004]
theorem batch_100_04_ok : batch_100_04_values.all id = true := by decide

def batch_100_05_values : List Bool := [accepted_5009]
theorem batch_100_05_ok : batch_100_05_values.all id = true := by decide

def batch_100_06_values : List Bool := [accepted_5011]
theorem batch_100_06_ok : batch_100_06_values.all id = true := by decide

def batch_100_07_values : List Bool := [accepted_5012]
theorem batch_100_07_ok : batch_100_07_values.all id = true := by decide

def batch_100_08_values : List Bool := [accepted_5013]
theorem batch_100_08_ok : batch_100_08_values.all id = true := by decide

def batch_100_09_values : List Bool := [accepted_5014]
theorem batch_100_09_ok : batch_100_09_values.all id = true := by decide

def batch_100_10_values : List Bool := [accepted_5016]
theorem batch_100_10_ok : batch_100_10_values.all id = true := by decide

def batch_100_11_values : List Bool := [accepted_5018]
theorem batch_100_11_ok : batch_100_11_values.all id = true := by decide

def batch_100_12_values : List Bool := [accepted_5019]
theorem batch_100_12_ok : batch_100_12_values.all id = true := by decide

def batch_100_13_values : List Bool := [accepted_5020]
theorem batch_100_13_ok : batch_100_13_values.all id = true := by decide

def batch_100_14_values : List Bool := [accepted_5027]
theorem batch_100_14_ok : batch_100_14_values.all id = true := by decide

def batch_100_15_values : List Bool := [accepted_5029]
theorem batch_100_15_ok : batch_100_15_values.all id = true := by decide

def batch_100_16_values : List Bool := [accepted_5030]
theorem batch_100_16_ok : batch_100_16_values.all id = true := by decide

def batch_100_17_values : List Bool := [accepted_5031]
theorem batch_100_17_ok : batch_100_17_values.all id = true := by decide

def batch_100_18_values : List Bool := [accepted_5032]
theorem batch_100_18_ok : batch_100_18_values.all id = true := by decide

def batch_100_19_values : List Bool := [accepted_5033]
theorem batch_100_19_ok : batch_100_19_values.all id = true := by decide

def batch_100_20_values : List Bool := [accepted_5034]
theorem batch_100_20_ok : batch_100_20_values.all id = true := by decide

def batch_100_21_values : List Bool := [accepted_5037]
theorem batch_100_21_ok : batch_100_21_values.all id = true := by decide

def batch_100_22_values : List Bool := [accepted_5039]
theorem batch_100_22_ok : batch_100_22_values.all id = true := by decide

def batch_100_23_values : List Bool := [accepted_5041]
theorem batch_100_23_ok : batch_100_23_values.all id = true := by decide

def batch_100_24_values : List Bool := [accepted_5042]
theorem batch_100_24_ok : batch_100_24_values.all id = true := by decide

def batch_100_25_values : List Bool := [accepted_5044]
theorem batch_100_25_ok : batch_100_25_values.all id = true := by decide

def batch_100_26_values : List Bool := [accepted_5045]
theorem batch_100_26_ok : batch_100_26_values.all id = true := by decide

def batch_100_27_values : List Bool := [accepted_5046]
theorem batch_100_27_ok : batch_100_27_values.all id = true := by decide

theorem leaf_5000_ok : checkAt 527 1000 box_5000 cert_5000 = true := by
  have h := List.all_eq_true.mp batch_100_00_ok accepted_5000 (by simp [batch_100_00_values])
  exact h
theorem leaf_5000_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5000.profileLo box_5000.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5000_ok
theorem branch_box_5000_nonnegative : ∀ j, 0 ≤ branch_box_5000.lower j ∧ 0 ≤ branch_box_5000.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5000, Box.profileLo, Box.profileHi, box_5000]
theorem leaf_5000_BranchSafe : CertificateConsequences.BranchSafe branch_box_5000 := by
  left; refine ⟨branch_box_5000_nonnegative, ?_⟩
  intro z hz; exact leaf_5000_sound hz

theorem leaf_5001_ok : checkAt 527 1000 box_5001 cert_5001 = true := by
  have h := List.all_eq_true.mp batch_100_01_ok accepted_5001 (by simp [batch_100_01_values])
  exact h
theorem leaf_5001_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5001.profileLo box_5001.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5001_ok
theorem branch_box_5001_nonnegative : ∀ j, 0 ≤ branch_box_5001.lower j ∧ 0 ≤ branch_box_5001.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5001, Box.profileLo, Box.profileHi, box_5001]
theorem leaf_5001_BranchSafe : CertificateConsequences.BranchSafe branch_box_5001 := by
  left; refine ⟨branch_box_5001_nonnegative, ?_⟩
  intro z hz; exact leaf_5001_sound hz

theorem leaf_5002_ok : checkAt 527 1000 box_5002 cert_5002 = true := by
  have h := List.all_eq_true.mp batch_100_02_ok accepted_5002 (by simp [batch_100_02_values])
  exact h
theorem leaf_5002_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5002.profileLo box_5002.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5002_ok
theorem branch_box_5002_nonnegative : ∀ j, 0 ≤ branch_box_5002.lower j ∧ 0 ≤ branch_box_5002.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5002, Box.profileLo, Box.profileHi, box_5002]
theorem leaf_5002_BranchSafe : CertificateConsequences.BranchSafe branch_box_5002 := by
  left; refine ⟨branch_box_5002_nonnegative, ?_⟩
  intro z hz; exact leaf_5002_sound hz

theorem leaf_5003_ok : checkAt 527 1000 box_5003 cert_5003 = true := by
  have h := List.all_eq_true.mp batch_100_03_ok accepted_5003 (by simp [batch_100_03_values])
  exact h
theorem leaf_5003_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5003.profileLo box_5003.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5003_ok
theorem branch_box_5003_nonnegative : ∀ j, 0 ≤ branch_box_5003.lower j ∧ 0 ≤ branch_box_5003.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5003, Box.profileLo, Box.profileHi, box_5003]
theorem leaf_5003_BranchSafe : CertificateConsequences.BranchSafe branch_box_5003 := by
  left; refine ⟨branch_box_5003_nonnegative, ?_⟩
  intro z hz; exact leaf_5003_sound hz

theorem leaf_5004_ok : checkAt 527 1000 box_5004 cert_5004 = true := by
  have h := List.all_eq_true.mp batch_100_04_ok accepted_5004 (by simp [batch_100_04_values])
  exact h
theorem leaf_5004_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5004.profileLo box_5004.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5004_ok
theorem branch_box_5004_nonnegative : ∀ j, 0 ≤ branch_box_5004.lower j ∧ 0 ≤ branch_box_5004.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5004, Box.profileLo, Box.profileHi, box_5004]
theorem leaf_5004_BranchSafe : CertificateConsequences.BranchSafe branch_box_5004 := by
  left; refine ⟨branch_box_5004_nonnegative, ?_⟩
  intro z hz; exact leaf_5004_sound hz

theorem leaf_5009_ok : checkAt 527 1000 box_5009 cert_5009 = true := by
  have h := List.all_eq_true.mp batch_100_05_ok accepted_5009 (by simp [batch_100_05_values])
  exact h
theorem leaf_5009_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5009.profileLo box_5009.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5009_ok
theorem branch_box_5009_nonnegative : ∀ j, 0 ≤ branch_box_5009.lower j ∧ 0 ≤ branch_box_5009.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5009, Box.profileLo, Box.profileHi, box_5009]
theorem leaf_5009_BranchSafe : CertificateConsequences.BranchSafe branch_box_5009 := by
  left; refine ⟨branch_box_5009_nonnegative, ?_⟩
  intro z hz; exact leaf_5009_sound hz

theorem leaf_5011_ok : checkAt 527 1000 box_5011 cert_5011 = true := by
  have h := List.all_eq_true.mp batch_100_06_ok accepted_5011 (by simp [batch_100_06_values])
  exact h
theorem leaf_5011_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5011.profileLo box_5011.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5011_ok
theorem branch_box_5011_nonnegative : ∀ j, 0 ≤ branch_box_5011.lower j ∧ 0 ≤ branch_box_5011.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5011, Box.profileLo, Box.profileHi, box_5011]
theorem leaf_5011_BranchSafe : CertificateConsequences.BranchSafe branch_box_5011 := by
  left; refine ⟨branch_box_5011_nonnegative, ?_⟩
  intro z hz; exact leaf_5011_sound hz

theorem leaf_5012_ok : checkAt 527 1000 box_5012 cert_5012 = true := by
  have h := List.all_eq_true.mp batch_100_07_ok accepted_5012 (by simp [batch_100_07_values])
  exact h
theorem leaf_5012_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5012.profileLo box_5012.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5012_ok
theorem branch_box_5012_nonnegative : ∀ j, 0 ≤ branch_box_5012.lower j ∧ 0 ≤ branch_box_5012.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5012, Box.profileLo, Box.profileHi, box_5012]
theorem leaf_5012_BranchSafe : CertificateConsequences.BranchSafe branch_box_5012 := by
  left; refine ⟨branch_box_5012_nonnegative, ?_⟩
  intro z hz; exact leaf_5012_sound hz

theorem leaf_5013_ok : checkAt 527 1000 box_5013 cert_5013 = true := by
  have h := List.all_eq_true.mp batch_100_08_ok accepted_5013 (by simp [batch_100_08_values])
  exact h
theorem leaf_5013_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5013.profileLo box_5013.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5013_ok
theorem branch_box_5013_nonnegative : ∀ j, 0 ≤ branch_box_5013.lower j ∧ 0 ≤ branch_box_5013.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5013, Box.profileLo, Box.profileHi, box_5013]
theorem leaf_5013_BranchSafe : CertificateConsequences.BranchSafe branch_box_5013 := by
  left; refine ⟨branch_box_5013_nonnegative, ?_⟩
  intro z hz; exact leaf_5013_sound hz

theorem leaf_5014_ok : checkAt 527 1000 box_5014 cert_5014 = true := by
  have h := List.all_eq_true.mp batch_100_09_ok accepted_5014 (by simp [batch_100_09_values])
  exact h
theorem leaf_5014_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5014.profileLo box_5014.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5014_ok
theorem branch_box_5014_nonnegative : ∀ j, 0 ≤ branch_box_5014.lower j ∧ 0 ≤ branch_box_5014.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5014, Box.profileLo, Box.profileHi, box_5014]
theorem leaf_5014_BranchSafe : CertificateConsequences.BranchSafe branch_box_5014 := by
  left; refine ⟨branch_box_5014_nonnegative, ?_⟩
  intro z hz; exact leaf_5014_sound hz

theorem leaf_5016_ok : checkAt 527 1000 box_5016 cert_5016 = true := by
  have h := List.all_eq_true.mp batch_100_10_ok accepted_5016 (by simp [batch_100_10_values])
  exact h
theorem leaf_5016_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5016.profileLo box_5016.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5016_ok
theorem branch_box_5016_nonnegative : ∀ j, 0 ≤ branch_box_5016.lower j ∧ 0 ≤ branch_box_5016.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5016, Box.profileLo, Box.profileHi, box_5016]
theorem leaf_5016_BranchSafe : CertificateConsequences.BranchSafe branch_box_5016 := by
  left; refine ⟨branch_box_5016_nonnegative, ?_⟩
  intro z hz; exact leaf_5016_sound hz

theorem leaf_5018_ok : checkAt 527 1000 box_5018 cert_5018 = true := by
  have h := List.all_eq_true.mp batch_100_11_ok accepted_5018 (by simp [batch_100_11_values])
  exact h
theorem leaf_5018_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5018.profileLo box_5018.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5018_ok
theorem branch_box_5018_nonnegative : ∀ j, 0 ≤ branch_box_5018.lower j ∧ 0 ≤ branch_box_5018.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5018, Box.profileLo, Box.profileHi, box_5018]
theorem leaf_5018_BranchSafe : CertificateConsequences.BranchSafe branch_box_5018 := by
  left; refine ⟨branch_box_5018_nonnegative, ?_⟩
  intro z hz; exact leaf_5018_sound hz

theorem leaf_5019_ok : checkAt 527 1000 box_5019 cert_5019 = true := by
  have h := List.all_eq_true.mp batch_100_12_ok accepted_5019 (by simp [batch_100_12_values])
  exact h
theorem leaf_5019_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5019.profileLo box_5019.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5019_ok
theorem branch_box_5019_nonnegative : ∀ j, 0 ≤ branch_box_5019.lower j ∧ 0 ≤ branch_box_5019.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5019, Box.profileLo, Box.profileHi, box_5019]
theorem leaf_5019_BranchSafe : CertificateConsequences.BranchSafe branch_box_5019 := by
  left; refine ⟨branch_box_5019_nonnegative, ?_⟩
  intro z hz; exact leaf_5019_sound hz

theorem leaf_5020_ok : checkAt 527 1000 box_5020 cert_5020 = true := by
  have h := List.all_eq_true.mp batch_100_13_ok accepted_5020 (by simp [batch_100_13_values])
  exact h
theorem leaf_5020_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5020.profileLo box_5020.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5020_ok
theorem branch_box_5020_nonnegative : ∀ j, 0 ≤ branch_box_5020.lower j ∧ 0 ≤ branch_box_5020.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5020, Box.profileLo, Box.profileHi, box_5020]
theorem leaf_5020_BranchSafe : CertificateConsequences.BranchSafe branch_box_5020 := by
  left; refine ⟨branch_box_5020_nonnegative, ?_⟩
  intro z hz; exact leaf_5020_sound hz

theorem leaf_5027_ok : checkAt 527 1000 box_5027 cert_5027 = true := by
  have h := List.all_eq_true.mp batch_100_14_ok accepted_5027 (by simp [batch_100_14_values])
  exact h
theorem leaf_5027_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5027.profileLo box_5027.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5027_ok
theorem branch_box_5027_nonnegative : ∀ j, 0 ≤ branch_box_5027.lower j ∧ 0 ≤ branch_box_5027.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5027, Box.profileLo, Box.profileHi, box_5027]
theorem leaf_5027_BranchSafe : CertificateConsequences.BranchSafe branch_box_5027 := by
  left; refine ⟨branch_box_5027_nonnegative, ?_⟩
  intro z hz; exact leaf_5027_sound hz

theorem leaf_5029_ok : checkAt 527 1000 box_5029 cert_5029 = true := by
  have h := List.all_eq_true.mp batch_100_15_ok accepted_5029 (by simp [batch_100_15_values])
  exact h
theorem leaf_5029_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5029.profileLo box_5029.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5029_ok
theorem branch_box_5029_nonnegative : ∀ j, 0 ≤ branch_box_5029.lower j ∧ 0 ≤ branch_box_5029.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5029, Box.profileLo, Box.profileHi, box_5029]
theorem leaf_5029_BranchSafe : CertificateConsequences.BranchSafe branch_box_5029 := by
  left; refine ⟨branch_box_5029_nonnegative, ?_⟩
  intro z hz; exact leaf_5029_sound hz

theorem leaf_5030_ok : checkAt 527 1000 box_5030 cert_5030 = true := by
  have h := List.all_eq_true.mp batch_100_16_ok accepted_5030 (by simp [batch_100_16_values])
  exact h
theorem leaf_5030_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5030.profileLo box_5030.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5030_ok
theorem branch_box_5030_nonnegative : ∀ j, 0 ≤ branch_box_5030.lower j ∧ 0 ≤ branch_box_5030.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5030, Box.profileLo, Box.profileHi, box_5030]
theorem leaf_5030_BranchSafe : CertificateConsequences.BranchSafe branch_box_5030 := by
  left; refine ⟨branch_box_5030_nonnegative, ?_⟩
  intro z hz; exact leaf_5030_sound hz

theorem leaf_5031_ok : checkAt 527 1000 box_5031 cert_5031 = true := by
  have h := List.all_eq_true.mp batch_100_17_ok accepted_5031 (by simp [batch_100_17_values])
  exact h
theorem leaf_5031_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5031.profileLo box_5031.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5031_ok
theorem branch_box_5031_nonnegative : ∀ j, 0 ≤ branch_box_5031.lower j ∧ 0 ≤ branch_box_5031.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5031, Box.profileLo, Box.profileHi, box_5031]
theorem leaf_5031_BranchSafe : CertificateConsequences.BranchSafe branch_box_5031 := by
  left; refine ⟨branch_box_5031_nonnegative, ?_⟩
  intro z hz; exact leaf_5031_sound hz

theorem leaf_5032_ok : checkAt 527 1000 box_5032 cert_5032 = true := by
  have h := List.all_eq_true.mp batch_100_18_ok accepted_5032 (by simp [batch_100_18_values])
  exact h
theorem leaf_5032_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5032.profileLo box_5032.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5032_ok
theorem branch_box_5032_nonnegative : ∀ j, 0 ≤ branch_box_5032.lower j ∧ 0 ≤ branch_box_5032.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5032, Box.profileLo, Box.profileHi, box_5032]
theorem leaf_5032_BranchSafe : CertificateConsequences.BranchSafe branch_box_5032 := by
  left; refine ⟨branch_box_5032_nonnegative, ?_⟩
  intro z hz; exact leaf_5032_sound hz

theorem leaf_5033_ok : checkAt 527 1000 box_5033 cert_5033 = true := by
  have h := List.all_eq_true.mp batch_100_19_ok accepted_5033 (by simp [batch_100_19_values])
  exact h
theorem leaf_5033_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5033.profileLo box_5033.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5033_ok
theorem branch_box_5033_nonnegative : ∀ j, 0 ≤ branch_box_5033.lower j ∧ 0 ≤ branch_box_5033.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5033, Box.profileLo, Box.profileHi, box_5033]
theorem leaf_5033_BranchSafe : CertificateConsequences.BranchSafe branch_box_5033 := by
  left; refine ⟨branch_box_5033_nonnegative, ?_⟩
  intro z hz; exact leaf_5033_sound hz

theorem leaf_5034_ok : checkAt 527 1000 box_5034 cert_5034 = true := by
  have h := List.all_eq_true.mp batch_100_20_ok accepted_5034 (by simp [batch_100_20_values])
  exact h
theorem leaf_5034_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5034.profileLo box_5034.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5034_ok
theorem branch_box_5034_nonnegative : ∀ j, 0 ≤ branch_box_5034.lower j ∧ 0 ≤ branch_box_5034.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5034, Box.profileLo, Box.profileHi, box_5034]
theorem leaf_5034_BranchSafe : CertificateConsequences.BranchSafe branch_box_5034 := by
  left; refine ⟨branch_box_5034_nonnegative, ?_⟩
  intro z hz; exact leaf_5034_sound hz

theorem leaf_5037_ok : checkAt 527 1000 box_5037 cert_5037 = true := by
  have h := List.all_eq_true.mp batch_100_21_ok accepted_5037 (by simp [batch_100_21_values])
  exact h
theorem leaf_5037_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5037.profileLo box_5037.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5037_ok
theorem branch_box_5037_nonnegative : ∀ j, 0 ≤ branch_box_5037.lower j ∧ 0 ≤ branch_box_5037.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5037, Box.profileLo, Box.profileHi, box_5037]
theorem leaf_5037_BranchSafe : CertificateConsequences.BranchSafe branch_box_5037 := by
  left; refine ⟨branch_box_5037_nonnegative, ?_⟩
  intro z hz; exact leaf_5037_sound hz

theorem leaf_5039_ok : checkAt 527 1000 box_5039 cert_5039 = true := by
  have h := List.all_eq_true.mp batch_100_22_ok accepted_5039 (by simp [batch_100_22_values])
  exact h
theorem leaf_5039_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5039.profileLo box_5039.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5039_ok
theorem branch_box_5039_nonnegative : ∀ j, 0 ≤ branch_box_5039.lower j ∧ 0 ≤ branch_box_5039.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5039, Box.profileLo, Box.profileHi, box_5039]
theorem leaf_5039_BranchSafe : CertificateConsequences.BranchSafe branch_box_5039 := by
  left; refine ⟨branch_box_5039_nonnegative, ?_⟩
  intro z hz; exact leaf_5039_sound hz

theorem leaf_5041_ok : checkAt 527 1000 box_5041 cert_5041 = true := by
  have h := List.all_eq_true.mp batch_100_23_ok accepted_5041 (by simp [batch_100_23_values])
  exact h
theorem leaf_5041_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5041.profileLo box_5041.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5041_ok
theorem branch_box_5041_nonnegative : ∀ j, 0 ≤ branch_box_5041.lower j ∧ 0 ≤ branch_box_5041.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5041, Box.profileLo, Box.profileHi, box_5041]
theorem leaf_5041_BranchSafe : CertificateConsequences.BranchSafe branch_box_5041 := by
  left; refine ⟨branch_box_5041_nonnegative, ?_⟩
  intro z hz; exact leaf_5041_sound hz

theorem leaf_5042_ok : checkAt 527 1000 box_5042 cert_5042 = true := by
  have h := List.all_eq_true.mp batch_100_24_ok accepted_5042 (by simp [batch_100_24_values])
  exact h
theorem leaf_5042_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5042.profileLo box_5042.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5042_ok
theorem branch_box_5042_nonnegative : ∀ j, 0 ≤ branch_box_5042.lower j ∧ 0 ≤ branch_box_5042.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5042, Box.profileLo, Box.profileHi, box_5042]
theorem leaf_5042_BranchSafe : CertificateConsequences.BranchSafe branch_box_5042 := by
  left; refine ⟨branch_box_5042_nonnegative, ?_⟩
  intro z hz; exact leaf_5042_sound hz

theorem leaf_5044_ok : checkAt 527 1000 box_5044 cert_5044 = true := by
  have h := List.all_eq_true.mp batch_100_25_ok accepted_5044 (by simp [batch_100_25_values])
  exact h
theorem leaf_5044_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5044.profileLo box_5044.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5044_ok
theorem branch_box_5044_nonnegative : ∀ j, 0 ≤ branch_box_5044.lower j ∧ 0 ≤ branch_box_5044.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5044, Box.profileLo, Box.profileHi, box_5044]
theorem leaf_5044_BranchSafe : CertificateConsequences.BranchSafe branch_box_5044 := by
  left; refine ⟨branch_box_5044_nonnegative, ?_⟩
  intro z hz; exact leaf_5044_sound hz

theorem leaf_5045_ok : checkAt 527 1000 box_5045 cert_5045 = true := by
  have h := List.all_eq_true.mp batch_100_26_ok accepted_5045 (by simp [batch_100_26_values])
  exact h
theorem leaf_5045_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5045.profileLo box_5045.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5045_ok
theorem branch_box_5045_nonnegative : ∀ j, 0 ≤ branch_box_5045.lower j ∧ 0 ≤ branch_box_5045.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5045, Box.profileLo, Box.profileHi, box_5045]
theorem leaf_5045_BranchSafe : CertificateConsequences.BranchSafe branch_box_5045 := by
  left; refine ⟨branch_box_5045_nonnegative, ?_⟩
  intro z hz; exact leaf_5045_sound hz

theorem leaf_5046_ok : checkAt 527 1000 box_5046 cert_5046 = true := by
  have h := List.all_eq_true.mp batch_100_27_ok accepted_5046 (by simp [batch_100_27_values])
  exact h
theorem leaf_5046_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5046.profileLo box_5046.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5046_ok
theorem branch_box_5046_nonnegative : ∀ j, 0 ≤ branch_box_5046.lower j ∧ 0 ≤ branch_box_5046.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5046, Box.profileLo, Box.profileHi, box_5046]
theorem leaf_5046_BranchSafe : CertificateConsequences.BranchSafe branch_box_5046 := by
  left; refine ⟨branch_box_5046_nonnegative, ?_⟩
  intro z hz; exact leaf_5046_sound hz

#print axioms batch_100_00_ok
#print axioms leaf_5000_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
