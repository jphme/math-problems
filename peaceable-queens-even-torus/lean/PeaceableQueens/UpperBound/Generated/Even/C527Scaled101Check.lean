import PeaceableQueens.UpperBound.Generated.Even.C527Scaled101Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_101_00_values : List Bool := [accepted_5055]
theorem batch_101_00_ok : batch_101_00_values.all id = true := by decide

def batch_101_01_values : List Bool := [accepted_5057]
theorem batch_101_01_ok : batch_101_01_values.all id = true := by decide

def batch_101_02_values : List Bool := [accepted_5058]
theorem batch_101_02_ok : batch_101_02_values.all id = true := by decide

def batch_101_03_values : List Bool := [accepted_5062]
theorem batch_101_03_ok : batch_101_03_values.all id = true := by decide

def batch_101_04_values : List Bool := [accepted_5063]
theorem batch_101_04_ok : batch_101_04_values.all id = true := by decide

def batch_101_05_values : List Bool := [accepted_5064]
theorem batch_101_05_ok : batch_101_05_values.all id = true := by decide

def batch_101_06_values : List Bool := [accepted_5066]
theorem batch_101_06_ok : batch_101_06_values.all id = true := by decide

def batch_101_07_values : List Bool := [accepted_5067]
theorem batch_101_07_ok : batch_101_07_values.all id = true := by decide

def batch_101_08_values : List Bool := [accepted_5068]
theorem batch_101_08_ok : batch_101_08_values.all id = true := by decide

def batch_101_09_values : List Bool := [accepted_5074]
theorem batch_101_09_ok : batch_101_09_values.all id = true := by decide

def batch_101_10_values : List Bool := [accepted_5075]
theorem batch_101_10_ok : batch_101_10_values.all id = true := by decide

def batch_101_11_values : List Bool := [accepted_5076]
theorem batch_101_11_ok : batch_101_11_values.all id = true := by decide

def batch_101_12_values : List Bool := [accepted_5077]
theorem batch_101_12_ok : batch_101_12_values.all id = true := by decide

def batch_101_13_values : List Bool := [accepted_5081]
theorem batch_101_13_ok : batch_101_13_values.all id = true := by decide

def batch_101_14_values : List Bool := [accepted_5083]
theorem batch_101_14_ok : batch_101_14_values.all id = true := by decide

def batch_101_15_values : List Bool := [accepted_5084]
theorem batch_101_15_ok : batch_101_15_values.all id = true := by decide

def batch_101_16_values : List Bool := [accepted_5085]
theorem batch_101_16_ok : batch_101_16_values.all id = true := by decide

def batch_101_17_values : List Bool := [accepted_5086]
theorem batch_101_17_ok : batch_101_17_values.all id = true := by decide

def batch_101_18_values : List Bool := [accepted_5091]
theorem batch_101_18_ok : batch_101_18_values.all id = true := by decide

def batch_101_19_values : List Bool := [accepted_5092]
theorem batch_101_19_ok : batch_101_19_values.all id = true := by decide

def batch_101_20_values : List Bool := [accepted_5094]
theorem batch_101_20_ok : batch_101_20_values.all id = true := by decide

def batch_101_21_values : List Bool := [accepted_5095]
theorem batch_101_21_ok : batch_101_21_values.all id = true := by decide

def batch_101_22_values : List Bool := [accepted_5096]
theorem batch_101_22_ok : batch_101_22_values.all id = true := by decide

def batch_101_23_values : List Bool := [accepted_5097]
theorem batch_101_23_ok : batch_101_23_values.all id = true := by decide

def batch_101_24_values : List Bool := [accepted_5098]
theorem batch_101_24_ok : batch_101_24_values.all id = true := by decide

theorem leaf_5055_ok : checkAt 527 1000 box_5055 cert_5055 = true := by
  have h := List.all_eq_true.mp batch_101_00_ok accepted_5055 (by simp [batch_101_00_values])
  exact h
theorem leaf_5055_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5055.profileLo box_5055.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5055_ok
theorem branch_box_5055_nonnegative : ∀ j, 0 ≤ branch_box_5055.lower j ∧ 0 ≤ branch_box_5055.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5055, Box.profileLo, Box.profileHi, box_5055]
theorem leaf_5055_BranchSafe : CertificateConsequences.BranchSafe branch_box_5055 := by
  left; refine ⟨branch_box_5055_nonnegative, ?_⟩
  intro z hz; exact leaf_5055_sound hz

theorem leaf_5057_ok : checkAt 527 1000 box_5057 cert_5057 = true := by
  have h := List.all_eq_true.mp batch_101_01_ok accepted_5057 (by simp [batch_101_01_values])
  exact h
theorem leaf_5057_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5057.profileLo box_5057.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5057_ok
theorem branch_box_5057_nonnegative : ∀ j, 0 ≤ branch_box_5057.lower j ∧ 0 ≤ branch_box_5057.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5057, Box.profileLo, Box.profileHi, box_5057]
theorem leaf_5057_BranchSafe : CertificateConsequences.BranchSafe branch_box_5057 := by
  left; refine ⟨branch_box_5057_nonnegative, ?_⟩
  intro z hz; exact leaf_5057_sound hz

theorem leaf_5058_ok : checkAt 527 1000 box_5058 cert_5058 = true := by
  have h := List.all_eq_true.mp batch_101_02_ok accepted_5058 (by simp [batch_101_02_values])
  exact h
theorem leaf_5058_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5058.profileLo box_5058.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5058_ok
theorem branch_box_5058_nonnegative : ∀ j, 0 ≤ branch_box_5058.lower j ∧ 0 ≤ branch_box_5058.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5058, Box.profileLo, Box.profileHi, box_5058]
theorem leaf_5058_BranchSafe : CertificateConsequences.BranchSafe branch_box_5058 := by
  left; refine ⟨branch_box_5058_nonnegative, ?_⟩
  intro z hz; exact leaf_5058_sound hz

theorem leaf_5062_ok : checkAt 527 1000 box_5062 cert_5062 = true := by
  have h := List.all_eq_true.mp batch_101_03_ok accepted_5062 (by simp [batch_101_03_values])
  exact h
theorem leaf_5062_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5062.profileLo box_5062.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5062_ok
theorem branch_box_5062_nonnegative : ∀ j, 0 ≤ branch_box_5062.lower j ∧ 0 ≤ branch_box_5062.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5062, Box.profileLo, Box.profileHi, box_5062]
theorem leaf_5062_BranchSafe : CertificateConsequences.BranchSafe branch_box_5062 := by
  left; refine ⟨branch_box_5062_nonnegative, ?_⟩
  intro z hz; exact leaf_5062_sound hz

theorem leaf_5063_ok : checkAt 527 1000 box_5063 cert_5063 = true := by
  have h := List.all_eq_true.mp batch_101_04_ok accepted_5063 (by simp [batch_101_04_values])
  exact h
theorem leaf_5063_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5063.profileLo box_5063.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5063_ok
theorem branch_box_5063_nonnegative : ∀ j, 0 ≤ branch_box_5063.lower j ∧ 0 ≤ branch_box_5063.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5063, Box.profileLo, Box.profileHi, box_5063]
theorem leaf_5063_BranchSafe : CertificateConsequences.BranchSafe branch_box_5063 := by
  left; refine ⟨branch_box_5063_nonnegative, ?_⟩
  intro z hz; exact leaf_5063_sound hz

theorem leaf_5064_ok : checkAt 527 1000 box_5064 cert_5064 = true := by
  have h := List.all_eq_true.mp batch_101_05_ok accepted_5064 (by simp [batch_101_05_values])
  exact h
theorem leaf_5064_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5064.profileLo box_5064.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5064_ok
theorem branch_box_5064_nonnegative : ∀ j, 0 ≤ branch_box_5064.lower j ∧ 0 ≤ branch_box_5064.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5064, Box.profileLo, Box.profileHi, box_5064]
theorem leaf_5064_BranchSafe : CertificateConsequences.BranchSafe branch_box_5064 := by
  left; refine ⟨branch_box_5064_nonnegative, ?_⟩
  intro z hz; exact leaf_5064_sound hz

theorem leaf_5066_ok : checkAt 527 1000 box_5066 cert_5066 = true := by
  have h := List.all_eq_true.mp batch_101_06_ok accepted_5066 (by simp [batch_101_06_values])
  exact h
theorem leaf_5066_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5066.profileLo box_5066.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5066_ok
theorem branch_box_5066_nonnegative : ∀ j, 0 ≤ branch_box_5066.lower j ∧ 0 ≤ branch_box_5066.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5066, Box.profileLo, Box.profileHi, box_5066]
theorem leaf_5066_BranchSafe : CertificateConsequences.BranchSafe branch_box_5066 := by
  left; refine ⟨branch_box_5066_nonnegative, ?_⟩
  intro z hz; exact leaf_5066_sound hz

theorem leaf_5067_ok : checkAt 527 1000 box_5067 cert_5067 = true := by
  have h := List.all_eq_true.mp batch_101_07_ok accepted_5067 (by simp [batch_101_07_values])
  exact h
theorem leaf_5067_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5067.profileLo box_5067.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5067_ok
theorem branch_box_5067_nonnegative : ∀ j, 0 ≤ branch_box_5067.lower j ∧ 0 ≤ branch_box_5067.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5067, Box.profileLo, Box.profileHi, box_5067]
theorem leaf_5067_BranchSafe : CertificateConsequences.BranchSafe branch_box_5067 := by
  left; refine ⟨branch_box_5067_nonnegative, ?_⟩
  intro z hz; exact leaf_5067_sound hz

theorem leaf_5068_ok : checkAt 527 1000 box_5068 cert_5068 = true := by
  have h := List.all_eq_true.mp batch_101_08_ok accepted_5068 (by simp [batch_101_08_values])
  exact h
theorem leaf_5068_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5068.profileLo box_5068.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5068_ok
theorem branch_box_5068_nonnegative : ∀ j, 0 ≤ branch_box_5068.lower j ∧ 0 ≤ branch_box_5068.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5068, Box.profileLo, Box.profileHi, box_5068]
theorem leaf_5068_BranchSafe : CertificateConsequences.BranchSafe branch_box_5068 := by
  left; refine ⟨branch_box_5068_nonnegative, ?_⟩
  intro z hz; exact leaf_5068_sound hz

theorem leaf_5074_ok : checkAt 527 1000 box_5074 cert_5074 = true := by
  have h := List.all_eq_true.mp batch_101_09_ok accepted_5074 (by simp [batch_101_09_values])
  exact h
theorem leaf_5074_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5074.profileLo box_5074.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5074_ok
theorem branch_box_5074_nonnegative : ∀ j, 0 ≤ branch_box_5074.lower j ∧ 0 ≤ branch_box_5074.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5074, Box.profileLo, Box.profileHi, box_5074]
theorem leaf_5074_BranchSafe : CertificateConsequences.BranchSafe branch_box_5074 := by
  left; refine ⟨branch_box_5074_nonnegative, ?_⟩
  intro z hz; exact leaf_5074_sound hz

theorem leaf_5075_ok : checkAt 527 1000 box_5075 cert_5075 = true := by
  have h := List.all_eq_true.mp batch_101_10_ok accepted_5075 (by simp [batch_101_10_values])
  exact h
theorem leaf_5075_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5075.profileLo box_5075.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5075_ok
theorem branch_box_5075_nonnegative : ∀ j, 0 ≤ branch_box_5075.lower j ∧ 0 ≤ branch_box_5075.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5075, Box.profileLo, Box.profileHi, box_5075]
theorem leaf_5075_BranchSafe : CertificateConsequences.BranchSafe branch_box_5075 := by
  left; refine ⟨branch_box_5075_nonnegative, ?_⟩
  intro z hz; exact leaf_5075_sound hz

theorem leaf_5076_ok : checkAt 527 1000 box_5076 cert_5076 = true := by
  have h := List.all_eq_true.mp batch_101_11_ok accepted_5076 (by simp [batch_101_11_values])
  exact h
theorem leaf_5076_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5076.profileLo box_5076.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5076_ok
theorem branch_box_5076_nonnegative : ∀ j, 0 ≤ branch_box_5076.lower j ∧ 0 ≤ branch_box_5076.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5076, Box.profileLo, Box.profileHi, box_5076]
theorem leaf_5076_BranchSafe : CertificateConsequences.BranchSafe branch_box_5076 := by
  left; refine ⟨branch_box_5076_nonnegative, ?_⟩
  intro z hz; exact leaf_5076_sound hz

theorem leaf_5077_ok : checkAt 527 1000 box_5077 cert_5077 = true := by
  have h := List.all_eq_true.mp batch_101_12_ok accepted_5077 (by simp [batch_101_12_values])
  exact h
theorem leaf_5077_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5077.profileLo box_5077.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5077_ok
theorem branch_box_5077_nonnegative : ∀ j, 0 ≤ branch_box_5077.lower j ∧ 0 ≤ branch_box_5077.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5077, Box.profileLo, Box.profileHi, box_5077]
theorem leaf_5077_BranchSafe : CertificateConsequences.BranchSafe branch_box_5077 := by
  left; refine ⟨branch_box_5077_nonnegative, ?_⟩
  intro z hz; exact leaf_5077_sound hz

theorem leaf_5081_ok : checkAt 527 1000 box_5081 cert_5081 = true := by
  have h := List.all_eq_true.mp batch_101_13_ok accepted_5081 (by simp [batch_101_13_values])
  exact h
theorem leaf_5081_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5081.profileLo box_5081.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5081_ok
theorem branch_box_5081_nonnegative : ∀ j, 0 ≤ branch_box_5081.lower j ∧ 0 ≤ branch_box_5081.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5081, Box.profileLo, Box.profileHi, box_5081]
theorem leaf_5081_BranchSafe : CertificateConsequences.BranchSafe branch_box_5081 := by
  left; refine ⟨branch_box_5081_nonnegative, ?_⟩
  intro z hz; exact leaf_5081_sound hz

theorem leaf_5083_ok : checkAt 527 1000 box_5083 cert_5083 = true := by
  have h := List.all_eq_true.mp batch_101_14_ok accepted_5083 (by simp [batch_101_14_values])
  exact h
theorem leaf_5083_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5083.profileLo box_5083.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5083_ok
theorem branch_box_5083_nonnegative : ∀ j, 0 ≤ branch_box_5083.lower j ∧ 0 ≤ branch_box_5083.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5083, Box.profileLo, Box.profileHi, box_5083]
theorem leaf_5083_BranchSafe : CertificateConsequences.BranchSafe branch_box_5083 := by
  left; refine ⟨branch_box_5083_nonnegative, ?_⟩
  intro z hz; exact leaf_5083_sound hz

theorem leaf_5084_ok : checkAt 527 1000 box_5084 cert_5084 = true := by
  have h := List.all_eq_true.mp batch_101_15_ok accepted_5084 (by simp [batch_101_15_values])
  exact h
theorem leaf_5084_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5084.profileLo box_5084.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5084_ok
theorem branch_box_5084_nonnegative : ∀ j, 0 ≤ branch_box_5084.lower j ∧ 0 ≤ branch_box_5084.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5084, Box.profileLo, Box.profileHi, box_5084]
theorem leaf_5084_BranchSafe : CertificateConsequences.BranchSafe branch_box_5084 := by
  left; refine ⟨branch_box_5084_nonnegative, ?_⟩
  intro z hz; exact leaf_5084_sound hz

theorem leaf_5085_ok : checkAt 527 1000 box_5085 cert_5085 = true := by
  have h := List.all_eq_true.mp batch_101_16_ok accepted_5085 (by simp [batch_101_16_values])
  exact h
theorem leaf_5085_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5085.profileLo box_5085.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5085_ok
theorem branch_box_5085_nonnegative : ∀ j, 0 ≤ branch_box_5085.lower j ∧ 0 ≤ branch_box_5085.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5085, Box.profileLo, Box.profileHi, box_5085]
theorem leaf_5085_BranchSafe : CertificateConsequences.BranchSafe branch_box_5085 := by
  left; refine ⟨branch_box_5085_nonnegative, ?_⟩
  intro z hz; exact leaf_5085_sound hz

theorem leaf_5086_ok : checkAt 527 1000 box_5086 cert_5086 = true := by
  have h := List.all_eq_true.mp batch_101_17_ok accepted_5086 (by simp [batch_101_17_values])
  exact h
theorem leaf_5086_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5086.profileLo box_5086.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5086_ok
theorem branch_box_5086_nonnegative : ∀ j, 0 ≤ branch_box_5086.lower j ∧ 0 ≤ branch_box_5086.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5086, Box.profileLo, Box.profileHi, box_5086]
theorem leaf_5086_BranchSafe : CertificateConsequences.BranchSafe branch_box_5086 := by
  left; refine ⟨branch_box_5086_nonnegative, ?_⟩
  intro z hz; exact leaf_5086_sound hz

theorem leaf_5091_ok : checkAt 527 1000 box_5091 cert_5091 = true := by
  have h := List.all_eq_true.mp batch_101_18_ok accepted_5091 (by simp [batch_101_18_values])
  exact h
theorem leaf_5091_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5091.profileLo box_5091.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5091_ok
theorem branch_box_5091_nonnegative : ∀ j, 0 ≤ branch_box_5091.lower j ∧ 0 ≤ branch_box_5091.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5091, Box.profileLo, Box.profileHi, box_5091]
theorem leaf_5091_BranchSafe : CertificateConsequences.BranchSafe branch_box_5091 := by
  left; refine ⟨branch_box_5091_nonnegative, ?_⟩
  intro z hz; exact leaf_5091_sound hz

theorem leaf_5092_ok : checkAt 527 1000 box_5092 cert_5092 = true := by
  have h := List.all_eq_true.mp batch_101_19_ok accepted_5092 (by simp [batch_101_19_values])
  exact h
theorem leaf_5092_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5092.profileLo box_5092.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5092_ok
theorem branch_box_5092_nonnegative : ∀ j, 0 ≤ branch_box_5092.lower j ∧ 0 ≤ branch_box_5092.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5092, Box.profileLo, Box.profileHi, box_5092]
theorem leaf_5092_BranchSafe : CertificateConsequences.BranchSafe branch_box_5092 := by
  left; refine ⟨branch_box_5092_nonnegative, ?_⟩
  intro z hz; exact leaf_5092_sound hz

theorem leaf_5094_ok : checkAt 527 1000 box_5094 cert_5094 = true := by
  have h := List.all_eq_true.mp batch_101_20_ok accepted_5094 (by simp [batch_101_20_values])
  exact h
theorem leaf_5094_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5094.profileLo box_5094.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5094_ok
theorem branch_box_5094_nonnegative : ∀ j, 0 ≤ branch_box_5094.lower j ∧ 0 ≤ branch_box_5094.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5094, Box.profileLo, Box.profileHi, box_5094]
theorem leaf_5094_BranchSafe : CertificateConsequences.BranchSafe branch_box_5094 := by
  left; refine ⟨branch_box_5094_nonnegative, ?_⟩
  intro z hz; exact leaf_5094_sound hz

theorem leaf_5095_ok : checkAt 527 1000 box_5095 cert_5095 = true := by
  have h := List.all_eq_true.mp batch_101_21_ok accepted_5095 (by simp [batch_101_21_values])
  exact h
theorem leaf_5095_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5095.profileLo box_5095.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5095_ok
theorem branch_box_5095_nonnegative : ∀ j, 0 ≤ branch_box_5095.lower j ∧ 0 ≤ branch_box_5095.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5095, Box.profileLo, Box.profileHi, box_5095]
theorem leaf_5095_BranchSafe : CertificateConsequences.BranchSafe branch_box_5095 := by
  left; refine ⟨branch_box_5095_nonnegative, ?_⟩
  intro z hz; exact leaf_5095_sound hz

theorem leaf_5096_ok : checkAt 527 1000 box_5096 cert_5096 = true := by
  have h := List.all_eq_true.mp batch_101_22_ok accepted_5096 (by simp [batch_101_22_values])
  exact h
theorem leaf_5096_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5096.profileLo box_5096.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5096_ok
theorem branch_box_5096_nonnegative : ∀ j, 0 ≤ branch_box_5096.lower j ∧ 0 ≤ branch_box_5096.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5096, Box.profileLo, Box.profileHi, box_5096]
theorem leaf_5096_BranchSafe : CertificateConsequences.BranchSafe branch_box_5096 := by
  left; refine ⟨branch_box_5096_nonnegative, ?_⟩
  intro z hz; exact leaf_5096_sound hz

theorem leaf_5097_ok : checkAt 527 1000 box_5097 cert_5097 = true := by
  have h := List.all_eq_true.mp batch_101_23_ok accepted_5097 (by simp [batch_101_23_values])
  exact h
theorem leaf_5097_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5097.profileLo box_5097.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5097_ok
theorem branch_box_5097_nonnegative : ∀ j, 0 ≤ branch_box_5097.lower j ∧ 0 ≤ branch_box_5097.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5097, Box.profileLo, Box.profileHi, box_5097]
theorem leaf_5097_BranchSafe : CertificateConsequences.BranchSafe branch_box_5097 := by
  left; refine ⟨branch_box_5097_nonnegative, ?_⟩
  intro z hz; exact leaf_5097_sound hz

theorem leaf_5098_ok : checkAt 527 1000 box_5098 cert_5098 = true := by
  have h := List.all_eq_true.mp batch_101_24_ok accepted_5098 (by simp [batch_101_24_values])
  exact h
theorem leaf_5098_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5098.profileLo box_5098.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5098_ok
theorem branch_box_5098_nonnegative : ∀ j, 0 ≤ branch_box_5098.lower j ∧ 0 ≤ branch_box_5098.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5098, Box.profileLo, Box.profileHi, box_5098]
theorem leaf_5098_BranchSafe : CertificateConsequences.BranchSafe branch_box_5098 := by
  left; refine ⟨branch_box_5098_nonnegative, ?_⟩
  intro z hz; exact leaf_5098_sound hz

#print axioms batch_101_00_ok
#print axioms leaf_5055_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
