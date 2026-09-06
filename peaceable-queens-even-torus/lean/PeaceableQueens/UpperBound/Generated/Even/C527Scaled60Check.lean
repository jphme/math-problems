import PeaceableQueens.UpperBound.Generated.Even.C527Scaled60Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_60_00_values : List Bool := [accepted_3000]
theorem batch_60_00_ok : batch_60_00_values.all id = true := by decide

def batch_60_01_values : List Bool := [accepted_3006]
theorem batch_60_01_ok : batch_60_01_values.all id = true := by decide

def batch_60_02_values : List Bool := [accepted_3007]
theorem batch_60_02_ok : batch_60_02_values.all id = true := by decide

def batch_60_03_values : List Bool := [accepted_3008]
theorem batch_60_03_ok : batch_60_03_values.all id = true := by decide

def batch_60_04_values : List Bool := [accepted_3013]
theorem batch_60_04_ok : batch_60_04_values.all id = true := by decide

def batch_60_05_values : List Bool := [accepted_3014]
theorem batch_60_05_ok : batch_60_05_values.all id = true := by decide

def batch_60_06_values : List Bool := [accepted_3015]
theorem batch_60_06_ok : batch_60_06_values.all id = true := by decide

def batch_60_07_values : List Bool := [accepted_3016]
theorem batch_60_07_ok : batch_60_07_values.all id = true := by decide

def batch_60_08_values : List Bool := [accepted_3019]
theorem batch_60_08_ok : batch_60_08_values.all id = true := by decide

def batch_60_09_values : List Bool := [accepted_3020]
theorem batch_60_09_ok : batch_60_09_values.all id = true := by decide

def batch_60_10_values : List Bool := [accepted_3021]
theorem batch_60_10_ok : batch_60_10_values.all id = true := by decide

def batch_60_11_values : List Bool := [accepted_3022]
theorem batch_60_11_ok : batch_60_11_values.all id = true := by decide

def batch_60_12_values : List Bool := [accepted_3025]
theorem batch_60_12_ok : batch_60_12_values.all id = true := by decide

def batch_60_13_values : List Bool := [accepted_3026]
theorem batch_60_13_ok : batch_60_13_values.all id = true := by decide

def batch_60_14_values : List Bool := [accepted_3029]
theorem batch_60_14_ok : batch_60_14_values.all id = true := by decide

def batch_60_15_values : List Bool := [accepted_3030]
theorem batch_60_15_ok : batch_60_15_values.all id = true := by decide

def batch_60_16_values : List Bool := [accepted_3033]
theorem batch_60_16_ok : batch_60_16_values.all id = true := by decide

def batch_60_17_values : List Bool := [accepted_3035]
theorem batch_60_17_ok : batch_60_17_values.all id = true := by decide

def batch_60_18_values : List Bool := [accepted_3037]
theorem batch_60_18_ok : batch_60_18_values.all id = true := by decide

def batch_60_19_values : List Bool := [accepted_3038]
theorem batch_60_19_ok : batch_60_19_values.all id = true := by decide

def batch_60_20_values : List Bool := [accepted_3042]
theorem batch_60_20_ok : batch_60_20_values.all id = true := by decide

def batch_60_21_values : List Bool := [accepted_3043]
theorem batch_60_21_ok : batch_60_21_values.all id = true := by decide

def batch_60_22_values : List Bool := [accepted_3044]
theorem batch_60_22_ok : batch_60_22_values.all id = true := by decide

def batch_60_23_values : List Bool := [accepted_3047]
theorem batch_60_23_ok : batch_60_23_values.all id = true := by decide

theorem leaf_3000_ok : checkAt 527 1000 box_3000 cert_3000 = true := by
  have h := List.all_eq_true.mp batch_60_00_ok accepted_3000 (by simp [batch_60_00_values])
  exact h
theorem leaf_3000_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3000.profileLo box_3000.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3000_ok
theorem branch_box_3000_nonnegative : ∀ j, 0 ≤ branch_box_3000.lower j ∧ 0 ≤ branch_box_3000.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3000, Box.profileLo, Box.profileHi, box_3000]
theorem leaf_3000_BranchSafe : CertificateConsequences.BranchSafe branch_box_3000 := by
  left; refine ⟨branch_box_3000_nonnegative, ?_⟩
  intro z hz; exact leaf_3000_sound hz

theorem leaf_3006_ok : checkAt 527 1000 box_3006 cert_3006 = true := by
  have h := List.all_eq_true.mp batch_60_01_ok accepted_3006 (by simp [batch_60_01_values])
  exact h
theorem leaf_3006_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3006.profileLo box_3006.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3006_ok
theorem branch_box_3006_nonnegative : ∀ j, 0 ≤ branch_box_3006.lower j ∧ 0 ≤ branch_box_3006.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3006, Box.profileLo, Box.profileHi, box_3006]
theorem leaf_3006_BranchSafe : CertificateConsequences.BranchSafe branch_box_3006 := by
  left; refine ⟨branch_box_3006_nonnegative, ?_⟩
  intro z hz; exact leaf_3006_sound hz

theorem leaf_3007_ok : checkAt 527 1000 box_3007 cert_3007 = true := by
  have h := List.all_eq_true.mp batch_60_02_ok accepted_3007 (by simp [batch_60_02_values])
  exact h
theorem leaf_3007_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3007.profileLo box_3007.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3007_ok
theorem branch_box_3007_nonnegative : ∀ j, 0 ≤ branch_box_3007.lower j ∧ 0 ≤ branch_box_3007.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3007, Box.profileLo, Box.profileHi, box_3007]
theorem leaf_3007_BranchSafe : CertificateConsequences.BranchSafe branch_box_3007 := by
  left; refine ⟨branch_box_3007_nonnegative, ?_⟩
  intro z hz; exact leaf_3007_sound hz

theorem leaf_3008_ok : checkAt 527 1000 box_3008 cert_3008 = true := by
  have h := List.all_eq_true.mp batch_60_03_ok accepted_3008 (by simp [batch_60_03_values])
  exact h
theorem leaf_3008_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3008.profileLo box_3008.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3008_ok
theorem branch_box_3008_nonnegative : ∀ j, 0 ≤ branch_box_3008.lower j ∧ 0 ≤ branch_box_3008.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3008, Box.profileLo, Box.profileHi, box_3008]
theorem leaf_3008_BranchSafe : CertificateConsequences.BranchSafe branch_box_3008 := by
  left; refine ⟨branch_box_3008_nonnegative, ?_⟩
  intro z hz; exact leaf_3008_sound hz

theorem leaf_3013_ok : checkAt 527 1000 box_3013 cert_3013 = true := by
  have h := List.all_eq_true.mp batch_60_04_ok accepted_3013 (by simp [batch_60_04_values])
  exact h
theorem leaf_3013_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3013.profileLo box_3013.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3013_ok
theorem branch_box_3013_nonnegative : ∀ j, 0 ≤ branch_box_3013.lower j ∧ 0 ≤ branch_box_3013.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3013, Box.profileLo, Box.profileHi, box_3013]
theorem leaf_3013_BranchSafe : CertificateConsequences.BranchSafe branch_box_3013 := by
  left; refine ⟨branch_box_3013_nonnegative, ?_⟩
  intro z hz; exact leaf_3013_sound hz

theorem leaf_3014_ok : checkAt 527 1000 box_3014 cert_3014 = true := by
  have h := List.all_eq_true.mp batch_60_05_ok accepted_3014 (by simp [batch_60_05_values])
  exact h
theorem leaf_3014_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3014.profileLo box_3014.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3014_ok
theorem branch_box_3014_nonnegative : ∀ j, 0 ≤ branch_box_3014.lower j ∧ 0 ≤ branch_box_3014.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3014, Box.profileLo, Box.profileHi, box_3014]
theorem leaf_3014_BranchSafe : CertificateConsequences.BranchSafe branch_box_3014 := by
  left; refine ⟨branch_box_3014_nonnegative, ?_⟩
  intro z hz; exact leaf_3014_sound hz

theorem leaf_3015_ok : checkAt 527 1000 box_3015 cert_3015 = true := by
  have h := List.all_eq_true.mp batch_60_06_ok accepted_3015 (by simp [batch_60_06_values])
  exact h
theorem leaf_3015_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3015.profileLo box_3015.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3015_ok
theorem branch_box_3015_nonnegative : ∀ j, 0 ≤ branch_box_3015.lower j ∧ 0 ≤ branch_box_3015.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3015, Box.profileLo, Box.profileHi, box_3015]
theorem leaf_3015_BranchSafe : CertificateConsequences.BranchSafe branch_box_3015 := by
  left; refine ⟨branch_box_3015_nonnegative, ?_⟩
  intro z hz; exact leaf_3015_sound hz

theorem leaf_3016_ok : checkAt 527 1000 box_3016 cert_3016 = true := by
  have h := List.all_eq_true.mp batch_60_07_ok accepted_3016 (by simp [batch_60_07_values])
  exact h
theorem leaf_3016_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3016.profileLo box_3016.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3016_ok
theorem branch_box_3016_nonnegative : ∀ j, 0 ≤ branch_box_3016.lower j ∧ 0 ≤ branch_box_3016.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3016, Box.profileLo, Box.profileHi, box_3016]
theorem leaf_3016_BranchSafe : CertificateConsequences.BranchSafe branch_box_3016 := by
  left; refine ⟨branch_box_3016_nonnegative, ?_⟩
  intro z hz; exact leaf_3016_sound hz

theorem leaf_3019_ok : checkAt 527 1000 box_3019 cert_3019 = true := by
  have h := List.all_eq_true.mp batch_60_08_ok accepted_3019 (by simp [batch_60_08_values])
  exact h
theorem leaf_3019_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3019.profileLo box_3019.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3019_ok
theorem branch_box_3019_nonnegative : ∀ j, 0 ≤ branch_box_3019.lower j ∧ 0 ≤ branch_box_3019.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3019, Box.profileLo, Box.profileHi, box_3019]
theorem leaf_3019_BranchSafe : CertificateConsequences.BranchSafe branch_box_3019 := by
  left; refine ⟨branch_box_3019_nonnegative, ?_⟩
  intro z hz; exact leaf_3019_sound hz

theorem leaf_3020_ok : checkAt 527 1000 box_3020 cert_3020 = true := by
  have h := List.all_eq_true.mp batch_60_09_ok accepted_3020 (by simp [batch_60_09_values])
  exact h
theorem leaf_3020_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3020.profileLo box_3020.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3020_ok
theorem branch_box_3020_nonnegative : ∀ j, 0 ≤ branch_box_3020.lower j ∧ 0 ≤ branch_box_3020.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3020, Box.profileLo, Box.profileHi, box_3020]
theorem leaf_3020_BranchSafe : CertificateConsequences.BranchSafe branch_box_3020 := by
  left; refine ⟨branch_box_3020_nonnegative, ?_⟩
  intro z hz; exact leaf_3020_sound hz

theorem leaf_3021_ok : checkAt 527 1000 box_3021 cert_3021 = true := by
  have h := List.all_eq_true.mp batch_60_10_ok accepted_3021 (by simp [batch_60_10_values])
  exact h
theorem leaf_3021_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3021.profileLo box_3021.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3021_ok
theorem branch_box_3021_nonnegative : ∀ j, 0 ≤ branch_box_3021.lower j ∧ 0 ≤ branch_box_3021.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3021, Box.profileLo, Box.profileHi, box_3021]
theorem leaf_3021_BranchSafe : CertificateConsequences.BranchSafe branch_box_3021 := by
  left; refine ⟨branch_box_3021_nonnegative, ?_⟩
  intro z hz; exact leaf_3021_sound hz

theorem leaf_3022_ok : checkAt 527 1000 box_3022 cert_3022 = true := by
  have h := List.all_eq_true.mp batch_60_11_ok accepted_3022 (by simp [batch_60_11_values])
  exact h
theorem leaf_3022_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3022.profileLo box_3022.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3022_ok
theorem branch_box_3022_nonnegative : ∀ j, 0 ≤ branch_box_3022.lower j ∧ 0 ≤ branch_box_3022.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3022, Box.profileLo, Box.profileHi, box_3022]
theorem leaf_3022_BranchSafe : CertificateConsequences.BranchSafe branch_box_3022 := by
  left; refine ⟨branch_box_3022_nonnegative, ?_⟩
  intro z hz; exact leaf_3022_sound hz

theorem leaf_3025_ok : checkAt 527 1000 box_3025 cert_3025 = true := by
  have h := List.all_eq_true.mp batch_60_12_ok accepted_3025 (by simp [batch_60_12_values])
  exact h
theorem leaf_3025_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3025.profileLo box_3025.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3025_ok
theorem branch_box_3025_nonnegative : ∀ j, 0 ≤ branch_box_3025.lower j ∧ 0 ≤ branch_box_3025.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3025, Box.profileLo, Box.profileHi, box_3025]
theorem leaf_3025_BranchSafe : CertificateConsequences.BranchSafe branch_box_3025 := by
  left; refine ⟨branch_box_3025_nonnegative, ?_⟩
  intro z hz; exact leaf_3025_sound hz

theorem leaf_3026_ok : checkAt 527 1000 box_3026 cert_3026 = true := by
  have h := List.all_eq_true.mp batch_60_13_ok accepted_3026 (by simp [batch_60_13_values])
  exact h
theorem leaf_3026_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3026.profileLo box_3026.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3026_ok
theorem branch_box_3026_nonnegative : ∀ j, 0 ≤ branch_box_3026.lower j ∧ 0 ≤ branch_box_3026.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3026, Box.profileLo, Box.profileHi, box_3026]
theorem leaf_3026_BranchSafe : CertificateConsequences.BranchSafe branch_box_3026 := by
  left; refine ⟨branch_box_3026_nonnegative, ?_⟩
  intro z hz; exact leaf_3026_sound hz

theorem leaf_3029_ok : checkAt 527 1000 box_3029 cert_3029 = true := by
  have h := List.all_eq_true.mp batch_60_14_ok accepted_3029 (by simp [batch_60_14_values])
  exact h
theorem leaf_3029_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3029.profileLo box_3029.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3029_ok
theorem branch_box_3029_nonnegative : ∀ j, 0 ≤ branch_box_3029.lower j ∧ 0 ≤ branch_box_3029.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3029, Box.profileLo, Box.profileHi, box_3029]
theorem leaf_3029_BranchSafe : CertificateConsequences.BranchSafe branch_box_3029 := by
  left; refine ⟨branch_box_3029_nonnegative, ?_⟩
  intro z hz; exact leaf_3029_sound hz

theorem leaf_3030_ok : checkAt 527 1000 box_3030 cert_3030 = true := by
  have h := List.all_eq_true.mp batch_60_15_ok accepted_3030 (by simp [batch_60_15_values])
  exact h
theorem leaf_3030_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3030.profileLo box_3030.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3030_ok
theorem branch_box_3030_nonnegative : ∀ j, 0 ≤ branch_box_3030.lower j ∧ 0 ≤ branch_box_3030.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3030, Box.profileLo, Box.profileHi, box_3030]
theorem leaf_3030_BranchSafe : CertificateConsequences.BranchSafe branch_box_3030 := by
  left; refine ⟨branch_box_3030_nonnegative, ?_⟩
  intro z hz; exact leaf_3030_sound hz

theorem leaf_3033_ok : checkAt 527 1000 box_3033 cert_3033 = true := by
  have h := List.all_eq_true.mp batch_60_16_ok accepted_3033 (by simp [batch_60_16_values])
  exact h
theorem leaf_3033_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3033.profileLo box_3033.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3033_ok
theorem branch_box_3033_nonnegative : ∀ j, 0 ≤ branch_box_3033.lower j ∧ 0 ≤ branch_box_3033.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3033, Box.profileLo, Box.profileHi, box_3033]
theorem leaf_3033_BranchSafe : CertificateConsequences.BranchSafe branch_box_3033 := by
  left; refine ⟨branch_box_3033_nonnegative, ?_⟩
  intro z hz; exact leaf_3033_sound hz

theorem leaf_3035_ok : checkAt 527 1000 box_3035 cert_3035 = true := by
  have h := List.all_eq_true.mp batch_60_17_ok accepted_3035 (by simp [batch_60_17_values])
  exact h
theorem leaf_3035_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3035.profileLo box_3035.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3035_ok
theorem branch_box_3035_nonnegative : ∀ j, 0 ≤ branch_box_3035.lower j ∧ 0 ≤ branch_box_3035.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3035, Box.profileLo, Box.profileHi, box_3035]
theorem leaf_3035_BranchSafe : CertificateConsequences.BranchSafe branch_box_3035 := by
  left; refine ⟨branch_box_3035_nonnegative, ?_⟩
  intro z hz; exact leaf_3035_sound hz

theorem leaf_3037_ok : checkAt 527 1000 box_3037 cert_3037 = true := by
  have h := List.all_eq_true.mp batch_60_18_ok accepted_3037 (by simp [batch_60_18_values])
  exact h
theorem leaf_3037_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3037.profileLo box_3037.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3037_ok
theorem branch_box_3037_nonnegative : ∀ j, 0 ≤ branch_box_3037.lower j ∧ 0 ≤ branch_box_3037.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3037, Box.profileLo, Box.profileHi, box_3037]
theorem leaf_3037_BranchSafe : CertificateConsequences.BranchSafe branch_box_3037 := by
  left; refine ⟨branch_box_3037_nonnegative, ?_⟩
  intro z hz; exact leaf_3037_sound hz

theorem leaf_3038_ok : checkAt 527 1000 box_3038 cert_3038 = true := by
  have h := List.all_eq_true.mp batch_60_19_ok accepted_3038 (by simp [batch_60_19_values])
  exact h
theorem leaf_3038_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3038.profileLo box_3038.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3038_ok
theorem branch_box_3038_nonnegative : ∀ j, 0 ≤ branch_box_3038.lower j ∧ 0 ≤ branch_box_3038.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3038, Box.profileLo, Box.profileHi, box_3038]
theorem leaf_3038_BranchSafe : CertificateConsequences.BranchSafe branch_box_3038 := by
  left; refine ⟨branch_box_3038_nonnegative, ?_⟩
  intro z hz; exact leaf_3038_sound hz

theorem leaf_3042_ok : checkAt 527 1000 box_3042 cert_3042 = true := by
  have h := List.all_eq_true.mp batch_60_20_ok accepted_3042 (by simp [batch_60_20_values])
  exact h
theorem leaf_3042_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3042.profileLo box_3042.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3042_ok
theorem branch_box_3042_nonnegative : ∀ j, 0 ≤ branch_box_3042.lower j ∧ 0 ≤ branch_box_3042.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3042, Box.profileLo, Box.profileHi, box_3042]
theorem leaf_3042_BranchSafe : CertificateConsequences.BranchSafe branch_box_3042 := by
  left; refine ⟨branch_box_3042_nonnegative, ?_⟩
  intro z hz; exact leaf_3042_sound hz

theorem leaf_3043_ok : checkAt 527 1000 box_3043 cert_3043 = true := by
  have h := List.all_eq_true.mp batch_60_21_ok accepted_3043 (by simp [batch_60_21_values])
  exact h
theorem leaf_3043_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3043.profileLo box_3043.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3043_ok
theorem branch_box_3043_nonnegative : ∀ j, 0 ≤ branch_box_3043.lower j ∧ 0 ≤ branch_box_3043.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3043, Box.profileLo, Box.profileHi, box_3043]
theorem leaf_3043_BranchSafe : CertificateConsequences.BranchSafe branch_box_3043 := by
  left; refine ⟨branch_box_3043_nonnegative, ?_⟩
  intro z hz; exact leaf_3043_sound hz

theorem leaf_3044_ok : checkAt 527 1000 box_3044 cert_3044 = true := by
  have h := List.all_eq_true.mp batch_60_22_ok accepted_3044 (by simp [batch_60_22_values])
  exact h
theorem leaf_3044_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3044.profileLo box_3044.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3044_ok
theorem branch_box_3044_nonnegative : ∀ j, 0 ≤ branch_box_3044.lower j ∧ 0 ≤ branch_box_3044.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3044, Box.profileLo, Box.profileHi, box_3044]
theorem leaf_3044_BranchSafe : CertificateConsequences.BranchSafe branch_box_3044 := by
  left; refine ⟨branch_box_3044_nonnegative, ?_⟩
  intro z hz; exact leaf_3044_sound hz

theorem leaf_3047_ok : checkAt 527 1000 box_3047 cert_3047 = true := by
  have h := List.all_eq_true.mp batch_60_23_ok accepted_3047 (by simp [batch_60_23_values])
  exact h
theorem leaf_3047_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3047.profileLo box_3047.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3047_ok
theorem branch_box_3047_nonnegative : ∀ j, 0 ≤ branch_box_3047.lower j ∧ 0 ≤ branch_box_3047.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3047, Box.profileLo, Box.profileHi, box_3047]
theorem leaf_3047_BranchSafe : CertificateConsequences.BranchSafe branch_box_3047 := by
  left; refine ⟨branch_box_3047_nonnegative, ?_⟩
  intro z hz; exact leaf_3047_sound hz

#print axioms batch_60_00_ok
#print axioms leaf_3000_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
