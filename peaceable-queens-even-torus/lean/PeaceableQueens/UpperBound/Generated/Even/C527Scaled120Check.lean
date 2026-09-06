import PeaceableQueens.UpperBound.Generated.Even.C527Scaled120Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_120_00_values : List Bool := [accepted_6000]
theorem batch_120_00_ok : batch_120_00_values.all id = true := by decide

def batch_120_01_values : List Bool := [accepted_6001]
theorem batch_120_01_ok : batch_120_01_values.all id = true := by decide

def batch_120_02_values : List Bool := [accepted_6002]
theorem batch_120_02_ok : batch_120_02_values.all id = true := by decide

def batch_120_03_values : List Bool := [accepted_6005]
theorem batch_120_03_ok : batch_120_03_values.all id = true := by decide

def batch_120_04_values : List Bool := [accepted_6007]
theorem batch_120_04_ok : batch_120_04_values.all id = true := by decide

def batch_120_05_values : List Bool := [accepted_6008]
theorem batch_120_05_ok : batch_120_05_values.all id = true := by decide

def batch_120_06_values : List Bool := [accepted_6009]
theorem batch_120_06_ok : batch_120_06_values.all id = true := by decide

def batch_120_07_values : List Bool := [accepted_6010]
theorem batch_120_07_ok : batch_120_07_values.all id = true := by decide

def batch_120_08_values : List Bool := [accepted_6011]
theorem batch_120_08_ok : batch_120_08_values.all id = true := by decide

def batch_120_09_values : List Bool := [accepted_6015]
theorem batch_120_09_ok : batch_120_09_values.all id = true := by decide

def batch_120_10_values : List Bool := [accepted_6017]
theorem batch_120_10_ok : batch_120_10_values.all id = true := by decide

def batch_120_11_values : List Bool := [accepted_6019]
theorem batch_120_11_ok : batch_120_11_values.all id = true := by decide

def batch_120_12_values : List Bool := [accepted_6021]
theorem batch_120_12_ok : batch_120_12_values.all id = true := by decide

def batch_120_13_values : List Bool := [accepted_6026]
theorem batch_120_13_ok : batch_120_13_values.all id = true := by decide

def batch_120_14_values : List Bool := [accepted_6027]
theorem batch_120_14_ok : batch_120_14_values.all id = true := by decide

def batch_120_15_values : List Bool := [accepted_6028]
theorem batch_120_15_ok : batch_120_15_values.all id = true := by decide

def batch_120_16_values : List Bool := [accepted_6031]
theorem batch_120_16_ok : batch_120_16_values.all id = true := by decide

def batch_120_17_values : List Bool := [accepted_6033]
theorem batch_120_17_ok : batch_120_17_values.all id = true := by decide

def batch_120_18_values : List Bool := [accepted_6035]
theorem batch_120_18_ok : batch_120_18_values.all id = true := by decide

def batch_120_19_values : List Bool := [accepted_6037]
theorem batch_120_19_ok : batch_120_19_values.all id = true := by decide

def batch_120_20_values : List Bool := [accepted_6040]
theorem batch_120_20_ok : batch_120_20_values.all id = true := by decide

def batch_120_21_values : List Bool := [accepted_6041]
theorem batch_120_21_ok : batch_120_21_values.all id = true := by decide

def batch_120_22_values : List Bool := [accepted_6042]
theorem batch_120_22_ok : batch_120_22_values.all id = true := by decide

def batch_120_23_values : List Bool := [accepted_6045]
theorem batch_120_23_ok : batch_120_23_values.all id = true := by decide

def batch_120_24_values : List Bool := [accepted_6049]
theorem batch_120_24_ok : batch_120_24_values.all id = true := by decide

theorem leaf_6000_ok : checkAt 527 1000 box_6000 cert_6000 = true := by
  have h := List.all_eq_true.mp batch_120_00_ok accepted_6000 (by simp [batch_120_00_values])
  exact h
theorem leaf_6000_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6000.profileLo box_6000.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6000_ok
theorem branch_box_6000_nonnegative : ∀ j, 0 ≤ branch_box_6000.lower j ∧ 0 ≤ branch_box_6000.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6000, Box.profileLo, Box.profileHi, box_6000]
theorem leaf_6000_BranchSafe : CertificateConsequences.BranchSafe branch_box_6000 := by
  left; refine ⟨branch_box_6000_nonnegative, ?_⟩
  intro z hz; exact leaf_6000_sound hz

theorem leaf_6001_ok : checkAt 527 1000 box_6001 cert_6001 = true := by
  have h := List.all_eq_true.mp batch_120_01_ok accepted_6001 (by simp [batch_120_01_values])
  exact h
theorem leaf_6001_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6001.profileLo box_6001.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6001_ok
theorem branch_box_6001_nonnegative : ∀ j, 0 ≤ branch_box_6001.lower j ∧ 0 ≤ branch_box_6001.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6001, Box.profileLo, Box.profileHi, box_6001]
theorem leaf_6001_BranchSafe : CertificateConsequences.BranchSafe branch_box_6001 := by
  left; refine ⟨branch_box_6001_nonnegative, ?_⟩
  intro z hz; exact leaf_6001_sound hz

theorem leaf_6002_ok : checkAt 527 1000 box_6002 cert_6002 = true := by
  have h := List.all_eq_true.mp batch_120_02_ok accepted_6002 (by simp [batch_120_02_values])
  exact h
theorem leaf_6002_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6002.profileLo box_6002.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6002_ok
theorem branch_box_6002_nonnegative : ∀ j, 0 ≤ branch_box_6002.lower j ∧ 0 ≤ branch_box_6002.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6002, Box.profileLo, Box.profileHi, box_6002]
theorem leaf_6002_BranchSafe : CertificateConsequences.BranchSafe branch_box_6002 := by
  left; refine ⟨branch_box_6002_nonnegative, ?_⟩
  intro z hz; exact leaf_6002_sound hz

theorem leaf_6005_ok : checkAt 527 1000 box_6005 cert_6005 = true := by
  have h := List.all_eq_true.mp batch_120_03_ok accepted_6005 (by simp [batch_120_03_values])
  exact h
theorem leaf_6005_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6005.profileLo box_6005.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6005_ok
theorem branch_box_6005_nonnegative : ∀ j, 0 ≤ branch_box_6005.lower j ∧ 0 ≤ branch_box_6005.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6005, Box.profileLo, Box.profileHi, box_6005]
theorem leaf_6005_BranchSafe : CertificateConsequences.BranchSafe branch_box_6005 := by
  left; refine ⟨branch_box_6005_nonnegative, ?_⟩
  intro z hz; exact leaf_6005_sound hz

theorem leaf_6007_ok : checkAt 527 1000 box_6007 cert_6007 = true := by
  have h := List.all_eq_true.mp batch_120_04_ok accepted_6007 (by simp [batch_120_04_values])
  exact h
theorem leaf_6007_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6007.profileLo box_6007.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6007_ok
theorem branch_box_6007_nonnegative : ∀ j, 0 ≤ branch_box_6007.lower j ∧ 0 ≤ branch_box_6007.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6007, Box.profileLo, Box.profileHi, box_6007]
theorem leaf_6007_BranchSafe : CertificateConsequences.BranchSafe branch_box_6007 := by
  left; refine ⟨branch_box_6007_nonnegative, ?_⟩
  intro z hz; exact leaf_6007_sound hz

theorem leaf_6008_ok : checkAt 527 1000 box_6008 cert_6008 = true := by
  have h := List.all_eq_true.mp batch_120_05_ok accepted_6008 (by simp [batch_120_05_values])
  exact h
theorem leaf_6008_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6008.profileLo box_6008.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6008_ok
theorem branch_box_6008_nonnegative : ∀ j, 0 ≤ branch_box_6008.lower j ∧ 0 ≤ branch_box_6008.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6008, Box.profileLo, Box.profileHi, box_6008]
theorem leaf_6008_BranchSafe : CertificateConsequences.BranchSafe branch_box_6008 := by
  left; refine ⟨branch_box_6008_nonnegative, ?_⟩
  intro z hz; exact leaf_6008_sound hz

theorem leaf_6009_ok : checkAt 527 1000 box_6009 cert_6009 = true := by
  have h := List.all_eq_true.mp batch_120_06_ok accepted_6009 (by simp [batch_120_06_values])
  exact h
theorem leaf_6009_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6009.profileLo box_6009.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6009_ok
theorem branch_box_6009_nonnegative : ∀ j, 0 ≤ branch_box_6009.lower j ∧ 0 ≤ branch_box_6009.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6009, Box.profileLo, Box.profileHi, box_6009]
theorem leaf_6009_BranchSafe : CertificateConsequences.BranchSafe branch_box_6009 := by
  left; refine ⟨branch_box_6009_nonnegative, ?_⟩
  intro z hz; exact leaf_6009_sound hz

theorem leaf_6010_ok : checkAt 527 1000 box_6010 cert_6010 = true := by
  have h := List.all_eq_true.mp batch_120_07_ok accepted_6010 (by simp [batch_120_07_values])
  exact h
theorem leaf_6010_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6010.profileLo box_6010.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6010_ok
theorem branch_box_6010_nonnegative : ∀ j, 0 ≤ branch_box_6010.lower j ∧ 0 ≤ branch_box_6010.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6010, Box.profileLo, Box.profileHi, box_6010]
theorem leaf_6010_BranchSafe : CertificateConsequences.BranchSafe branch_box_6010 := by
  left; refine ⟨branch_box_6010_nonnegative, ?_⟩
  intro z hz; exact leaf_6010_sound hz

theorem leaf_6011_ok : checkAt 527 1000 box_6011 cert_6011 = true := by
  have h := List.all_eq_true.mp batch_120_08_ok accepted_6011 (by simp [batch_120_08_values])
  exact h
theorem leaf_6011_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6011.profileLo box_6011.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6011_ok
theorem branch_box_6011_nonnegative : ∀ j, 0 ≤ branch_box_6011.lower j ∧ 0 ≤ branch_box_6011.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6011, Box.profileLo, Box.profileHi, box_6011]
theorem leaf_6011_BranchSafe : CertificateConsequences.BranchSafe branch_box_6011 := by
  left; refine ⟨branch_box_6011_nonnegative, ?_⟩
  intro z hz; exact leaf_6011_sound hz

theorem leaf_6015_ok : checkAt 527 1000 box_6015 cert_6015 = true := by
  have h := List.all_eq_true.mp batch_120_09_ok accepted_6015 (by simp [batch_120_09_values])
  exact h
theorem leaf_6015_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6015.profileLo box_6015.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6015_ok
theorem branch_box_6015_nonnegative : ∀ j, 0 ≤ branch_box_6015.lower j ∧ 0 ≤ branch_box_6015.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6015, Box.profileLo, Box.profileHi, box_6015]
theorem leaf_6015_BranchSafe : CertificateConsequences.BranchSafe branch_box_6015 := by
  left; refine ⟨branch_box_6015_nonnegative, ?_⟩
  intro z hz; exact leaf_6015_sound hz

theorem leaf_6017_ok : checkAt 527 1000 box_6017 cert_6017 = true := by
  have h := List.all_eq_true.mp batch_120_10_ok accepted_6017 (by simp [batch_120_10_values])
  exact h
theorem leaf_6017_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6017.profileLo box_6017.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6017_ok
theorem branch_box_6017_nonnegative : ∀ j, 0 ≤ branch_box_6017.lower j ∧ 0 ≤ branch_box_6017.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6017, Box.profileLo, Box.profileHi, box_6017]
theorem leaf_6017_BranchSafe : CertificateConsequences.BranchSafe branch_box_6017 := by
  left; refine ⟨branch_box_6017_nonnegative, ?_⟩
  intro z hz; exact leaf_6017_sound hz

theorem leaf_6019_ok : checkAt 527 1000 box_6019 cert_6019 = true := by
  have h := List.all_eq_true.mp batch_120_11_ok accepted_6019 (by simp [batch_120_11_values])
  exact h
theorem leaf_6019_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6019.profileLo box_6019.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6019_ok
theorem branch_box_6019_nonnegative : ∀ j, 0 ≤ branch_box_6019.lower j ∧ 0 ≤ branch_box_6019.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6019, Box.profileLo, Box.profileHi, box_6019]
theorem leaf_6019_BranchSafe : CertificateConsequences.BranchSafe branch_box_6019 := by
  left; refine ⟨branch_box_6019_nonnegative, ?_⟩
  intro z hz; exact leaf_6019_sound hz

theorem leaf_6021_ok : checkAt 527 1000 box_6021 cert_6021 = true := by
  have h := List.all_eq_true.mp batch_120_12_ok accepted_6021 (by simp [batch_120_12_values])
  exact h
theorem leaf_6021_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6021.profileLo box_6021.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6021_ok
theorem branch_box_6021_nonnegative : ∀ j, 0 ≤ branch_box_6021.lower j ∧ 0 ≤ branch_box_6021.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6021, Box.profileLo, Box.profileHi, box_6021]
theorem leaf_6021_BranchSafe : CertificateConsequences.BranchSafe branch_box_6021 := by
  left; refine ⟨branch_box_6021_nonnegative, ?_⟩
  intro z hz; exact leaf_6021_sound hz

theorem leaf_6026_ok : checkAt 527 1000 box_6026 cert_6026 = true := by
  have h := List.all_eq_true.mp batch_120_13_ok accepted_6026 (by simp [batch_120_13_values])
  exact h
theorem leaf_6026_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6026.profileLo box_6026.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6026_ok
theorem branch_box_6026_nonnegative : ∀ j, 0 ≤ branch_box_6026.lower j ∧ 0 ≤ branch_box_6026.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6026, Box.profileLo, Box.profileHi, box_6026]
theorem leaf_6026_BranchSafe : CertificateConsequences.BranchSafe branch_box_6026 := by
  left; refine ⟨branch_box_6026_nonnegative, ?_⟩
  intro z hz; exact leaf_6026_sound hz

theorem leaf_6027_ok : checkAt 527 1000 box_6027 cert_6027 = true := by
  have h := List.all_eq_true.mp batch_120_14_ok accepted_6027 (by simp [batch_120_14_values])
  exact h
theorem leaf_6027_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6027.profileLo box_6027.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6027_ok
theorem branch_box_6027_nonnegative : ∀ j, 0 ≤ branch_box_6027.lower j ∧ 0 ≤ branch_box_6027.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6027, Box.profileLo, Box.profileHi, box_6027]
theorem leaf_6027_BranchSafe : CertificateConsequences.BranchSafe branch_box_6027 := by
  left; refine ⟨branch_box_6027_nonnegative, ?_⟩
  intro z hz; exact leaf_6027_sound hz

theorem leaf_6028_ok : checkAt 527 1000 box_6028 cert_6028 = true := by
  have h := List.all_eq_true.mp batch_120_15_ok accepted_6028 (by simp [batch_120_15_values])
  exact h
theorem leaf_6028_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6028.profileLo box_6028.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6028_ok
theorem branch_box_6028_nonnegative : ∀ j, 0 ≤ branch_box_6028.lower j ∧ 0 ≤ branch_box_6028.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6028, Box.profileLo, Box.profileHi, box_6028]
theorem leaf_6028_BranchSafe : CertificateConsequences.BranchSafe branch_box_6028 := by
  left; refine ⟨branch_box_6028_nonnegative, ?_⟩
  intro z hz; exact leaf_6028_sound hz

theorem leaf_6031_ok : checkAt 527 1000 box_6031 cert_6031 = true := by
  have h := List.all_eq_true.mp batch_120_16_ok accepted_6031 (by simp [batch_120_16_values])
  exact h
theorem leaf_6031_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6031.profileLo box_6031.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6031_ok
theorem branch_box_6031_nonnegative : ∀ j, 0 ≤ branch_box_6031.lower j ∧ 0 ≤ branch_box_6031.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6031, Box.profileLo, Box.profileHi, box_6031]
theorem leaf_6031_BranchSafe : CertificateConsequences.BranchSafe branch_box_6031 := by
  left; refine ⟨branch_box_6031_nonnegative, ?_⟩
  intro z hz; exact leaf_6031_sound hz

theorem leaf_6033_ok : checkAt 527 1000 box_6033 cert_6033 = true := by
  have h := List.all_eq_true.mp batch_120_17_ok accepted_6033 (by simp [batch_120_17_values])
  exact h
theorem leaf_6033_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6033.profileLo box_6033.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6033_ok
theorem branch_box_6033_nonnegative : ∀ j, 0 ≤ branch_box_6033.lower j ∧ 0 ≤ branch_box_6033.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6033, Box.profileLo, Box.profileHi, box_6033]
theorem leaf_6033_BranchSafe : CertificateConsequences.BranchSafe branch_box_6033 := by
  left; refine ⟨branch_box_6033_nonnegative, ?_⟩
  intro z hz; exact leaf_6033_sound hz

theorem leaf_6035_ok : checkAt 527 1000 box_6035 cert_6035 = true := by
  have h := List.all_eq_true.mp batch_120_18_ok accepted_6035 (by simp [batch_120_18_values])
  exact h
theorem leaf_6035_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6035.profileLo box_6035.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6035_ok
theorem branch_box_6035_nonnegative : ∀ j, 0 ≤ branch_box_6035.lower j ∧ 0 ≤ branch_box_6035.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6035, Box.profileLo, Box.profileHi, box_6035]
theorem leaf_6035_BranchSafe : CertificateConsequences.BranchSafe branch_box_6035 := by
  left; refine ⟨branch_box_6035_nonnegative, ?_⟩
  intro z hz; exact leaf_6035_sound hz

theorem leaf_6037_ok : checkAt 527 1000 box_6037 cert_6037 = true := by
  have h := List.all_eq_true.mp batch_120_19_ok accepted_6037 (by simp [batch_120_19_values])
  exact h
theorem leaf_6037_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6037.profileLo box_6037.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6037_ok
theorem branch_box_6037_nonnegative : ∀ j, 0 ≤ branch_box_6037.lower j ∧ 0 ≤ branch_box_6037.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6037, Box.profileLo, Box.profileHi, box_6037]
theorem leaf_6037_BranchSafe : CertificateConsequences.BranchSafe branch_box_6037 := by
  left; refine ⟨branch_box_6037_nonnegative, ?_⟩
  intro z hz; exact leaf_6037_sound hz

theorem leaf_6040_ok : checkAt 527 1000 box_6040 cert_6040 = true := by
  have h := List.all_eq_true.mp batch_120_20_ok accepted_6040 (by simp [batch_120_20_values])
  exact h
theorem leaf_6040_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6040.profileLo box_6040.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6040_ok
theorem branch_box_6040_nonnegative : ∀ j, 0 ≤ branch_box_6040.lower j ∧ 0 ≤ branch_box_6040.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6040, Box.profileLo, Box.profileHi, box_6040]
theorem leaf_6040_BranchSafe : CertificateConsequences.BranchSafe branch_box_6040 := by
  left; refine ⟨branch_box_6040_nonnegative, ?_⟩
  intro z hz; exact leaf_6040_sound hz

theorem leaf_6041_ok : checkAt 527 1000 box_6041 cert_6041 = true := by
  have h := List.all_eq_true.mp batch_120_21_ok accepted_6041 (by simp [batch_120_21_values])
  exact h
theorem leaf_6041_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6041.profileLo box_6041.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6041_ok
theorem branch_box_6041_nonnegative : ∀ j, 0 ≤ branch_box_6041.lower j ∧ 0 ≤ branch_box_6041.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6041, Box.profileLo, Box.profileHi, box_6041]
theorem leaf_6041_BranchSafe : CertificateConsequences.BranchSafe branch_box_6041 := by
  left; refine ⟨branch_box_6041_nonnegative, ?_⟩
  intro z hz; exact leaf_6041_sound hz

theorem leaf_6042_ok : checkAt 527 1000 box_6042 cert_6042 = true := by
  have h := List.all_eq_true.mp batch_120_22_ok accepted_6042 (by simp [batch_120_22_values])
  exact h
theorem leaf_6042_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6042.profileLo box_6042.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6042_ok
theorem branch_box_6042_nonnegative : ∀ j, 0 ≤ branch_box_6042.lower j ∧ 0 ≤ branch_box_6042.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6042, Box.profileLo, Box.profileHi, box_6042]
theorem leaf_6042_BranchSafe : CertificateConsequences.BranchSafe branch_box_6042 := by
  left; refine ⟨branch_box_6042_nonnegative, ?_⟩
  intro z hz; exact leaf_6042_sound hz

theorem leaf_6045_ok : checkAt 527 1000 box_6045 cert_6045 = true := by
  have h := List.all_eq_true.mp batch_120_23_ok accepted_6045 (by simp [batch_120_23_values])
  exact h
theorem leaf_6045_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6045.profileLo box_6045.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6045_ok
theorem branch_box_6045_nonnegative : ∀ j, 0 ≤ branch_box_6045.lower j ∧ 0 ≤ branch_box_6045.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6045, Box.profileLo, Box.profileHi, box_6045]
theorem leaf_6045_BranchSafe : CertificateConsequences.BranchSafe branch_box_6045 := by
  left; refine ⟨branch_box_6045_nonnegative, ?_⟩
  intro z hz; exact leaf_6045_sound hz

theorem leaf_6049_ok : checkAt 527 1000 box_6049 cert_6049 = true := by
  have h := List.all_eq_true.mp batch_120_24_ok accepted_6049 (by simp [batch_120_24_values])
  exact h
theorem leaf_6049_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6049.profileLo box_6049.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6049_ok
theorem branch_box_6049_nonnegative : ∀ j, 0 ≤ branch_box_6049.lower j ∧ 0 ≤ branch_box_6049.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6049, Box.profileLo, Box.profileHi, box_6049]
theorem leaf_6049_BranchSafe : CertificateConsequences.BranchSafe branch_box_6049 := by
  left; refine ⟨branch_box_6049_nonnegative, ?_⟩
  intro z hz; exact leaf_6049_sound hz

#print axioms batch_120_00_ok
#print axioms leaf_6000_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
