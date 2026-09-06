import PeaceableQueens.UpperBound.Generated.Even.C527Scaled104Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_104_00_values : List Bool := [accepted_5200]
theorem batch_104_00_ok : batch_104_00_values.all id = true := by decide

def batch_104_01_values : List Bool := [accepted_5201]
theorem batch_104_01_ok : batch_104_01_values.all id = true := by decide

def batch_104_02_values : List Bool := [accepted_5203]
theorem batch_104_02_ok : batch_104_02_values.all id = true := by decide

def batch_104_03_values : List Bool := [accepted_5204]
theorem batch_104_03_ok : batch_104_03_values.all id = true := by decide

def batch_104_04_values : List Bool := [accepted_5205]
theorem batch_104_04_ok : batch_104_04_values.all id = true := by decide

def batch_104_05_values : List Bool := [accepted_5207]
theorem batch_104_05_ok : batch_104_05_values.all id = true := by decide

def batch_104_06_values : List Bool := [accepted_5208]
theorem batch_104_06_ok : batch_104_06_values.all id = true := by decide

def batch_104_07_values : List Bool := [accepted_5211]
theorem batch_104_07_ok : batch_104_07_values.all id = true := by decide

def batch_104_08_values : List Bool := [accepted_5212]
theorem batch_104_08_ok : batch_104_08_values.all id = true := by decide

def batch_104_09_values : List Bool := [accepted_5213]
theorem batch_104_09_ok : batch_104_09_values.all id = true := by decide

def batch_104_10_values : List Bool := [accepted_5215]
theorem batch_104_10_ok : batch_104_10_values.all id = true := by decide

def batch_104_11_values : List Bool := [accepted_5216]
theorem batch_104_11_ok : batch_104_11_values.all id = true := by decide

def batch_104_12_values : List Bool := [accepted_5223]
theorem batch_104_12_ok : batch_104_12_values.all id = true := by decide

def batch_104_13_values : List Bool := [accepted_5224]
theorem batch_104_13_ok : batch_104_13_values.all id = true := by decide

def batch_104_14_values : List Bool := [accepted_5225]
theorem batch_104_14_ok : batch_104_14_values.all id = true := by decide

def batch_104_15_values : List Bool := [accepted_5228]
theorem batch_104_15_ok : batch_104_15_values.all id = true := by decide

def batch_104_16_values : List Bool := [accepted_5229]
theorem batch_104_16_ok : batch_104_16_values.all id = true := by decide

def batch_104_17_values : List Bool := [accepted_5230]
theorem batch_104_17_ok : batch_104_17_values.all id = true := by decide

def batch_104_18_values : List Bool := [accepted_5235]
theorem batch_104_18_ok : batch_104_18_values.all id = true := by decide

def batch_104_19_values : List Bool := [accepted_5236]
theorem batch_104_19_ok : batch_104_19_values.all id = true := by decide

def batch_104_20_values : List Bool := [accepted_5241]
theorem batch_104_20_ok : batch_104_20_values.all id = true := by decide

def batch_104_21_values : List Bool := [accepted_5243]
theorem batch_104_21_ok : batch_104_21_values.all id = true := by decide

def batch_104_22_values : List Bool := [accepted_5244]
theorem batch_104_22_ok : batch_104_22_values.all id = true := by decide

def batch_104_23_values : List Bool := [accepted_5245]
theorem batch_104_23_ok : batch_104_23_values.all id = true := by decide

def batch_104_24_values : List Bool := [accepted_5247]
theorem batch_104_24_ok : batch_104_24_values.all id = true := by decide

def batch_104_25_values : List Bool := [accepted_5249]
theorem batch_104_25_ok : batch_104_25_values.all id = true := by decide

theorem leaf_5200_ok : checkAt 527 1000 box_5200 cert_5200 = true := by
  have h := List.all_eq_true.mp batch_104_00_ok accepted_5200 (by simp [batch_104_00_values])
  exact h
theorem leaf_5200_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5200.profileLo box_5200.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5200_ok
theorem branch_box_5200_nonnegative : ∀ j, 0 ≤ branch_box_5200.lower j ∧ 0 ≤ branch_box_5200.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5200, Box.profileLo, Box.profileHi, box_5200]
theorem leaf_5200_BranchSafe : CertificateConsequences.BranchSafe branch_box_5200 := by
  left; refine ⟨branch_box_5200_nonnegative, ?_⟩
  intro z hz; exact leaf_5200_sound hz

theorem leaf_5201_ok : checkAt 527 1000 box_5201 cert_5201 = true := by
  have h := List.all_eq_true.mp batch_104_01_ok accepted_5201 (by simp [batch_104_01_values])
  exact h
theorem leaf_5201_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5201.profileLo box_5201.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5201_ok
theorem branch_box_5201_nonnegative : ∀ j, 0 ≤ branch_box_5201.lower j ∧ 0 ≤ branch_box_5201.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5201, Box.profileLo, Box.profileHi, box_5201]
theorem leaf_5201_BranchSafe : CertificateConsequences.BranchSafe branch_box_5201 := by
  left; refine ⟨branch_box_5201_nonnegative, ?_⟩
  intro z hz; exact leaf_5201_sound hz

theorem leaf_5203_ok : checkAt 527 1000 box_5203 cert_5203 = true := by
  have h := List.all_eq_true.mp batch_104_02_ok accepted_5203 (by simp [batch_104_02_values])
  exact h
theorem leaf_5203_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5203.profileLo box_5203.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5203_ok
theorem branch_box_5203_nonnegative : ∀ j, 0 ≤ branch_box_5203.lower j ∧ 0 ≤ branch_box_5203.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5203, Box.profileLo, Box.profileHi, box_5203]
theorem leaf_5203_BranchSafe : CertificateConsequences.BranchSafe branch_box_5203 := by
  left; refine ⟨branch_box_5203_nonnegative, ?_⟩
  intro z hz; exact leaf_5203_sound hz

theorem leaf_5204_ok : checkAt 527 1000 box_5204 cert_5204 = true := by
  have h := List.all_eq_true.mp batch_104_03_ok accepted_5204 (by simp [batch_104_03_values])
  exact h
theorem leaf_5204_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5204.profileLo box_5204.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5204_ok
theorem branch_box_5204_nonnegative : ∀ j, 0 ≤ branch_box_5204.lower j ∧ 0 ≤ branch_box_5204.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5204, Box.profileLo, Box.profileHi, box_5204]
theorem leaf_5204_BranchSafe : CertificateConsequences.BranchSafe branch_box_5204 := by
  left; refine ⟨branch_box_5204_nonnegative, ?_⟩
  intro z hz; exact leaf_5204_sound hz

theorem leaf_5205_ok : checkAt 527 1000 box_5205 cert_5205 = true := by
  have h := List.all_eq_true.mp batch_104_04_ok accepted_5205 (by simp [batch_104_04_values])
  exact h
theorem leaf_5205_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5205.profileLo box_5205.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5205_ok
theorem branch_box_5205_nonnegative : ∀ j, 0 ≤ branch_box_5205.lower j ∧ 0 ≤ branch_box_5205.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5205, Box.profileLo, Box.profileHi, box_5205]
theorem leaf_5205_BranchSafe : CertificateConsequences.BranchSafe branch_box_5205 := by
  left; refine ⟨branch_box_5205_nonnegative, ?_⟩
  intro z hz; exact leaf_5205_sound hz

theorem leaf_5207_ok : checkAt 527 1000 box_5207 cert_5207 = true := by
  have h := List.all_eq_true.mp batch_104_05_ok accepted_5207 (by simp [batch_104_05_values])
  exact h
theorem leaf_5207_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5207.profileLo box_5207.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5207_ok
theorem branch_box_5207_nonnegative : ∀ j, 0 ≤ branch_box_5207.lower j ∧ 0 ≤ branch_box_5207.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5207, Box.profileLo, Box.profileHi, box_5207]
theorem leaf_5207_BranchSafe : CertificateConsequences.BranchSafe branch_box_5207 := by
  left; refine ⟨branch_box_5207_nonnegative, ?_⟩
  intro z hz; exact leaf_5207_sound hz

theorem leaf_5208_ok : checkAt 527 1000 box_5208 cert_5208 = true := by
  have h := List.all_eq_true.mp batch_104_06_ok accepted_5208 (by simp [batch_104_06_values])
  exact h
theorem leaf_5208_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5208.profileLo box_5208.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5208_ok
theorem branch_box_5208_nonnegative : ∀ j, 0 ≤ branch_box_5208.lower j ∧ 0 ≤ branch_box_5208.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5208, Box.profileLo, Box.profileHi, box_5208]
theorem leaf_5208_BranchSafe : CertificateConsequences.BranchSafe branch_box_5208 := by
  left; refine ⟨branch_box_5208_nonnegative, ?_⟩
  intro z hz; exact leaf_5208_sound hz

theorem leaf_5211_ok : checkAt 527 1000 box_5211 cert_5211 = true := by
  have h := List.all_eq_true.mp batch_104_07_ok accepted_5211 (by simp [batch_104_07_values])
  exact h
theorem leaf_5211_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5211.profileLo box_5211.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5211_ok
theorem branch_box_5211_nonnegative : ∀ j, 0 ≤ branch_box_5211.lower j ∧ 0 ≤ branch_box_5211.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5211, Box.profileLo, Box.profileHi, box_5211]
theorem leaf_5211_BranchSafe : CertificateConsequences.BranchSafe branch_box_5211 := by
  left; refine ⟨branch_box_5211_nonnegative, ?_⟩
  intro z hz; exact leaf_5211_sound hz

theorem leaf_5212_ok : checkAt 527 1000 box_5212 cert_5212 = true := by
  have h := List.all_eq_true.mp batch_104_08_ok accepted_5212 (by simp [batch_104_08_values])
  exact h
theorem leaf_5212_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5212.profileLo box_5212.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5212_ok
theorem branch_box_5212_nonnegative : ∀ j, 0 ≤ branch_box_5212.lower j ∧ 0 ≤ branch_box_5212.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5212, Box.profileLo, Box.profileHi, box_5212]
theorem leaf_5212_BranchSafe : CertificateConsequences.BranchSafe branch_box_5212 := by
  left; refine ⟨branch_box_5212_nonnegative, ?_⟩
  intro z hz; exact leaf_5212_sound hz

theorem leaf_5213_ok : checkAt 527 1000 box_5213 cert_5213 = true := by
  have h := List.all_eq_true.mp batch_104_09_ok accepted_5213 (by simp [batch_104_09_values])
  exact h
theorem leaf_5213_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5213.profileLo box_5213.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5213_ok
theorem branch_box_5213_nonnegative : ∀ j, 0 ≤ branch_box_5213.lower j ∧ 0 ≤ branch_box_5213.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5213, Box.profileLo, Box.profileHi, box_5213]
theorem leaf_5213_BranchSafe : CertificateConsequences.BranchSafe branch_box_5213 := by
  left; refine ⟨branch_box_5213_nonnegative, ?_⟩
  intro z hz; exact leaf_5213_sound hz

theorem leaf_5215_ok : checkAt 527 1000 box_5215 cert_5215 = true := by
  have h := List.all_eq_true.mp batch_104_10_ok accepted_5215 (by simp [batch_104_10_values])
  exact h
theorem leaf_5215_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5215.profileLo box_5215.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5215_ok
theorem branch_box_5215_nonnegative : ∀ j, 0 ≤ branch_box_5215.lower j ∧ 0 ≤ branch_box_5215.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5215, Box.profileLo, Box.profileHi, box_5215]
theorem leaf_5215_BranchSafe : CertificateConsequences.BranchSafe branch_box_5215 := by
  left; refine ⟨branch_box_5215_nonnegative, ?_⟩
  intro z hz; exact leaf_5215_sound hz

theorem leaf_5216_ok : checkAt 527 1000 box_5216 cert_5216 = true := by
  have h := List.all_eq_true.mp batch_104_11_ok accepted_5216 (by simp [batch_104_11_values])
  exact h
theorem leaf_5216_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5216.profileLo box_5216.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5216_ok
theorem branch_box_5216_nonnegative : ∀ j, 0 ≤ branch_box_5216.lower j ∧ 0 ≤ branch_box_5216.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5216, Box.profileLo, Box.profileHi, box_5216]
theorem leaf_5216_BranchSafe : CertificateConsequences.BranchSafe branch_box_5216 := by
  left; refine ⟨branch_box_5216_nonnegative, ?_⟩
  intro z hz; exact leaf_5216_sound hz

theorem leaf_5223_ok : checkAt 527 1000 box_5223 cert_5223 = true := by
  have h := List.all_eq_true.mp batch_104_12_ok accepted_5223 (by simp [batch_104_12_values])
  exact h
theorem leaf_5223_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5223.profileLo box_5223.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5223_ok
theorem branch_box_5223_nonnegative : ∀ j, 0 ≤ branch_box_5223.lower j ∧ 0 ≤ branch_box_5223.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5223, Box.profileLo, Box.profileHi, box_5223]
theorem leaf_5223_BranchSafe : CertificateConsequences.BranchSafe branch_box_5223 := by
  left; refine ⟨branch_box_5223_nonnegative, ?_⟩
  intro z hz; exact leaf_5223_sound hz

theorem leaf_5224_ok : checkAt 527 1000 box_5224 cert_5224 = true := by
  have h := List.all_eq_true.mp batch_104_13_ok accepted_5224 (by simp [batch_104_13_values])
  exact h
theorem leaf_5224_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5224.profileLo box_5224.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5224_ok
theorem branch_box_5224_nonnegative : ∀ j, 0 ≤ branch_box_5224.lower j ∧ 0 ≤ branch_box_5224.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5224, Box.profileLo, Box.profileHi, box_5224]
theorem leaf_5224_BranchSafe : CertificateConsequences.BranchSafe branch_box_5224 := by
  left; refine ⟨branch_box_5224_nonnegative, ?_⟩
  intro z hz; exact leaf_5224_sound hz

theorem leaf_5225_ok : checkAt 527 1000 box_5225 cert_5225 = true := by
  have h := List.all_eq_true.mp batch_104_14_ok accepted_5225 (by simp [batch_104_14_values])
  exact h
theorem leaf_5225_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5225.profileLo box_5225.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5225_ok
theorem branch_box_5225_nonnegative : ∀ j, 0 ≤ branch_box_5225.lower j ∧ 0 ≤ branch_box_5225.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5225, Box.profileLo, Box.profileHi, box_5225]
theorem leaf_5225_BranchSafe : CertificateConsequences.BranchSafe branch_box_5225 := by
  left; refine ⟨branch_box_5225_nonnegative, ?_⟩
  intro z hz; exact leaf_5225_sound hz

theorem leaf_5228_ok : checkAt 527 1000 box_5228 cert_5228 = true := by
  have h := List.all_eq_true.mp batch_104_15_ok accepted_5228 (by simp [batch_104_15_values])
  exact h
theorem leaf_5228_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5228.profileLo box_5228.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5228_ok
theorem branch_box_5228_nonnegative : ∀ j, 0 ≤ branch_box_5228.lower j ∧ 0 ≤ branch_box_5228.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5228, Box.profileLo, Box.profileHi, box_5228]
theorem leaf_5228_BranchSafe : CertificateConsequences.BranchSafe branch_box_5228 := by
  left; refine ⟨branch_box_5228_nonnegative, ?_⟩
  intro z hz; exact leaf_5228_sound hz

theorem leaf_5229_ok : checkAt 527 1000 box_5229 cert_5229 = true := by
  have h := List.all_eq_true.mp batch_104_16_ok accepted_5229 (by simp [batch_104_16_values])
  exact h
theorem leaf_5229_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5229.profileLo box_5229.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5229_ok
theorem branch_box_5229_nonnegative : ∀ j, 0 ≤ branch_box_5229.lower j ∧ 0 ≤ branch_box_5229.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5229, Box.profileLo, Box.profileHi, box_5229]
theorem leaf_5229_BranchSafe : CertificateConsequences.BranchSafe branch_box_5229 := by
  left; refine ⟨branch_box_5229_nonnegative, ?_⟩
  intro z hz; exact leaf_5229_sound hz

theorem leaf_5230_ok : checkAt 527 1000 box_5230 cert_5230 = true := by
  have h := List.all_eq_true.mp batch_104_17_ok accepted_5230 (by simp [batch_104_17_values])
  exact h
theorem leaf_5230_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5230.profileLo box_5230.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5230_ok
theorem branch_box_5230_nonnegative : ∀ j, 0 ≤ branch_box_5230.lower j ∧ 0 ≤ branch_box_5230.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5230, Box.profileLo, Box.profileHi, box_5230]
theorem leaf_5230_BranchSafe : CertificateConsequences.BranchSafe branch_box_5230 := by
  left; refine ⟨branch_box_5230_nonnegative, ?_⟩
  intro z hz; exact leaf_5230_sound hz

theorem leaf_5235_ok : checkAt 527 1000 box_5235 cert_5235 = true := by
  have h := List.all_eq_true.mp batch_104_18_ok accepted_5235 (by simp [batch_104_18_values])
  exact h
theorem leaf_5235_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5235.profileLo box_5235.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5235_ok
theorem branch_box_5235_nonnegative : ∀ j, 0 ≤ branch_box_5235.lower j ∧ 0 ≤ branch_box_5235.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5235, Box.profileLo, Box.profileHi, box_5235]
theorem leaf_5235_BranchSafe : CertificateConsequences.BranchSafe branch_box_5235 := by
  left; refine ⟨branch_box_5235_nonnegative, ?_⟩
  intro z hz; exact leaf_5235_sound hz

theorem leaf_5236_ok : checkAt 527 1000 box_5236 cert_5236 = true := by
  have h := List.all_eq_true.mp batch_104_19_ok accepted_5236 (by simp [batch_104_19_values])
  exact h
theorem leaf_5236_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5236.profileLo box_5236.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5236_ok
theorem branch_box_5236_nonnegative : ∀ j, 0 ≤ branch_box_5236.lower j ∧ 0 ≤ branch_box_5236.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5236, Box.profileLo, Box.profileHi, box_5236]
theorem leaf_5236_BranchSafe : CertificateConsequences.BranchSafe branch_box_5236 := by
  left; refine ⟨branch_box_5236_nonnegative, ?_⟩
  intro z hz; exact leaf_5236_sound hz

theorem leaf_5241_ok : checkAt 527 1000 box_5241 cert_5241 = true := by
  have h := List.all_eq_true.mp batch_104_20_ok accepted_5241 (by simp [batch_104_20_values])
  exact h
theorem leaf_5241_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5241.profileLo box_5241.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5241_ok
theorem branch_box_5241_nonnegative : ∀ j, 0 ≤ branch_box_5241.lower j ∧ 0 ≤ branch_box_5241.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5241, Box.profileLo, Box.profileHi, box_5241]
theorem leaf_5241_BranchSafe : CertificateConsequences.BranchSafe branch_box_5241 := by
  left; refine ⟨branch_box_5241_nonnegative, ?_⟩
  intro z hz; exact leaf_5241_sound hz

theorem leaf_5243_ok : checkAt 527 1000 box_5243 cert_5243 = true := by
  have h := List.all_eq_true.mp batch_104_21_ok accepted_5243 (by simp [batch_104_21_values])
  exact h
theorem leaf_5243_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5243.profileLo box_5243.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5243_ok
theorem branch_box_5243_nonnegative : ∀ j, 0 ≤ branch_box_5243.lower j ∧ 0 ≤ branch_box_5243.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5243, Box.profileLo, Box.profileHi, box_5243]
theorem leaf_5243_BranchSafe : CertificateConsequences.BranchSafe branch_box_5243 := by
  left; refine ⟨branch_box_5243_nonnegative, ?_⟩
  intro z hz; exact leaf_5243_sound hz

theorem leaf_5244_ok : checkAt 527 1000 box_5244 cert_5244 = true := by
  have h := List.all_eq_true.mp batch_104_22_ok accepted_5244 (by simp [batch_104_22_values])
  exact h
theorem leaf_5244_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5244.profileLo box_5244.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5244_ok
theorem branch_box_5244_nonnegative : ∀ j, 0 ≤ branch_box_5244.lower j ∧ 0 ≤ branch_box_5244.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5244, Box.profileLo, Box.profileHi, box_5244]
theorem leaf_5244_BranchSafe : CertificateConsequences.BranchSafe branch_box_5244 := by
  left; refine ⟨branch_box_5244_nonnegative, ?_⟩
  intro z hz; exact leaf_5244_sound hz

theorem leaf_5245_ok : checkAt 527 1000 box_5245 cert_5245 = true := by
  have h := List.all_eq_true.mp batch_104_23_ok accepted_5245 (by simp [batch_104_23_values])
  exact h
theorem leaf_5245_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5245.profileLo box_5245.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5245_ok
theorem branch_box_5245_nonnegative : ∀ j, 0 ≤ branch_box_5245.lower j ∧ 0 ≤ branch_box_5245.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5245, Box.profileLo, Box.profileHi, box_5245]
theorem leaf_5245_BranchSafe : CertificateConsequences.BranchSafe branch_box_5245 := by
  left; refine ⟨branch_box_5245_nonnegative, ?_⟩
  intro z hz; exact leaf_5245_sound hz

theorem leaf_5247_ok : checkAt 527 1000 box_5247 cert_5247 = true := by
  have h := List.all_eq_true.mp batch_104_24_ok accepted_5247 (by simp [batch_104_24_values])
  exact h
theorem leaf_5247_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5247.profileLo box_5247.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5247_ok
theorem branch_box_5247_nonnegative : ∀ j, 0 ≤ branch_box_5247.lower j ∧ 0 ≤ branch_box_5247.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5247, Box.profileLo, Box.profileHi, box_5247]
theorem leaf_5247_BranchSafe : CertificateConsequences.BranchSafe branch_box_5247 := by
  left; refine ⟨branch_box_5247_nonnegative, ?_⟩
  intro z hz; exact leaf_5247_sound hz

theorem leaf_5249_ok : checkAt 527 1000 box_5249 cert_5249 = true := by
  have h := List.all_eq_true.mp batch_104_25_ok accepted_5249 (by simp [batch_104_25_values])
  exact h
theorem leaf_5249_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5249.profileLo box_5249.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5249_ok
theorem branch_box_5249_nonnegative : ∀ j, 0 ≤ branch_box_5249.lower j ∧ 0 ≤ branch_box_5249.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5249, Box.profileLo, Box.profileHi, box_5249]
theorem leaf_5249_BranchSafe : CertificateConsequences.BranchSafe branch_box_5249 := by
  left; refine ⟨branch_box_5249_nonnegative, ?_⟩
  intro z hz; exact leaf_5249_sound hz

#print axioms batch_104_00_ok
#print axioms leaf_5200_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
