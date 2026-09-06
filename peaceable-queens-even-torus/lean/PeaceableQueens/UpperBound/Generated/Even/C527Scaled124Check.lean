import PeaceableQueens.UpperBound.Generated.Even.C527Scaled124Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_124_00_values : List Bool := [accepted_6201]
theorem batch_124_00_ok : batch_124_00_values.all id = true := by decide

def batch_124_01_values : List Bool := [accepted_6205]
theorem batch_124_01_ok : batch_124_01_values.all id = true := by decide

def batch_124_02_values : List Bool := [accepted_6206]
theorem batch_124_02_ok : batch_124_02_values.all id = true := by decide

def batch_124_03_values : List Bool := [accepted_6211]
theorem batch_124_03_ok : batch_124_03_values.all id = true := by decide

def batch_124_04_values : List Bool := [accepted_6213]
theorem batch_124_04_ok : batch_124_04_values.all id = true := by decide

def batch_124_05_values : List Bool := [accepted_6214]
theorem batch_124_05_ok : batch_124_05_values.all id = true := by decide

def batch_124_06_values : List Bool := [accepted_6215]
theorem batch_124_06_ok : batch_124_06_values.all id = true := by decide

def batch_124_07_values : List Bool := [accepted_6216]
theorem batch_124_07_ok : batch_124_07_values.all id = true := by decide

def batch_124_08_values : List Bool := [accepted_6221]
theorem batch_124_08_ok : batch_124_08_values.all id = true := by decide

def batch_124_09_values : List Bool := [accepted_6223]
theorem batch_124_09_ok : batch_124_09_values.all id = true := by decide

def batch_124_10_values : List Bool := [accepted_6224]
theorem batch_124_10_ok : batch_124_10_values.all id = true := by decide

def batch_124_11_values : List Bool := [accepted_6227]
theorem batch_124_11_ok : batch_124_11_values.all id = true := by decide

def batch_124_12_values : List Bool := [accepted_6229]
theorem batch_124_12_ok : batch_124_12_values.all id = true := by decide

def batch_124_13_values : List Bool := [accepted_6230]
theorem batch_124_13_ok : batch_124_13_values.all id = true := by decide

def batch_124_14_values : List Bool := [accepted_6231]
theorem batch_124_14_ok : batch_124_14_values.all id = true := by decide

def batch_124_15_values : List Bool := [accepted_6235]
theorem batch_124_15_ok : batch_124_15_values.all id = true := by decide

def batch_124_16_values : List Bool := [accepted_6236]
theorem batch_124_16_ok : batch_124_16_values.all id = true := by decide

def batch_124_17_values : List Bool := [accepted_6242]
theorem batch_124_17_ok : batch_124_17_values.all id = true := by decide

def batch_124_18_values : List Bool := [accepted_6243]
theorem batch_124_18_ok : batch_124_18_values.all id = true := by decide

def batch_124_19_values : List Bool := [accepted_6244]
theorem batch_124_19_ok : batch_124_19_values.all id = true := by decide

def batch_124_20_values : List Bool := [accepted_6245]
theorem batch_124_20_ok : batch_124_20_values.all id = true := by decide

def batch_124_21_values : List Bool := [accepted_6247]
theorem batch_124_21_ok : batch_124_21_values.all id = true := by decide

def batch_124_22_values : List Bool := [accepted_6248]
theorem batch_124_22_ok : batch_124_22_values.all id = true := by decide

theorem leaf_6201_ok : checkAt 527 1000 box_6201 cert_6201 = true := by
  have h := List.all_eq_true.mp batch_124_00_ok accepted_6201 (by simp [batch_124_00_values])
  exact h
theorem leaf_6201_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6201.profileLo box_6201.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6201_ok
theorem branch_box_6201_nonnegative : ∀ j, 0 ≤ branch_box_6201.lower j ∧ 0 ≤ branch_box_6201.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6201, Box.profileLo, Box.profileHi, box_6201]
theorem leaf_6201_BranchSafe : CertificateConsequences.BranchSafe branch_box_6201 := by
  left; refine ⟨branch_box_6201_nonnegative, ?_⟩
  intro z hz; exact leaf_6201_sound hz

theorem leaf_6205_ok : checkAt 527 1000 box_6205 cert_6205 = true := by
  have h := List.all_eq_true.mp batch_124_01_ok accepted_6205 (by simp [batch_124_01_values])
  exact h
theorem leaf_6205_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6205.profileLo box_6205.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6205_ok
theorem branch_box_6205_nonnegative : ∀ j, 0 ≤ branch_box_6205.lower j ∧ 0 ≤ branch_box_6205.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6205, Box.profileLo, Box.profileHi, box_6205]
theorem leaf_6205_BranchSafe : CertificateConsequences.BranchSafe branch_box_6205 := by
  left; refine ⟨branch_box_6205_nonnegative, ?_⟩
  intro z hz; exact leaf_6205_sound hz

theorem leaf_6206_ok : checkAt 527 1000 box_6206 cert_6206 = true := by
  have h := List.all_eq_true.mp batch_124_02_ok accepted_6206 (by simp [batch_124_02_values])
  exact h
theorem leaf_6206_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6206.profileLo box_6206.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6206_ok
theorem branch_box_6206_nonnegative : ∀ j, 0 ≤ branch_box_6206.lower j ∧ 0 ≤ branch_box_6206.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6206, Box.profileLo, Box.profileHi, box_6206]
theorem leaf_6206_BranchSafe : CertificateConsequences.BranchSafe branch_box_6206 := by
  left; refine ⟨branch_box_6206_nonnegative, ?_⟩
  intro z hz; exact leaf_6206_sound hz

theorem leaf_6211_ok : checkAt 527 1000 box_6211 cert_6211 = true := by
  have h := List.all_eq_true.mp batch_124_03_ok accepted_6211 (by simp [batch_124_03_values])
  exact h
theorem leaf_6211_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6211.profileLo box_6211.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6211_ok
theorem branch_box_6211_nonnegative : ∀ j, 0 ≤ branch_box_6211.lower j ∧ 0 ≤ branch_box_6211.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6211, Box.profileLo, Box.profileHi, box_6211]
theorem leaf_6211_BranchSafe : CertificateConsequences.BranchSafe branch_box_6211 := by
  left; refine ⟨branch_box_6211_nonnegative, ?_⟩
  intro z hz; exact leaf_6211_sound hz

theorem leaf_6213_ok : checkAt 527 1000 box_6213 cert_6213 = true := by
  have h := List.all_eq_true.mp batch_124_04_ok accepted_6213 (by simp [batch_124_04_values])
  exact h
theorem leaf_6213_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6213.profileLo box_6213.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6213_ok
theorem branch_box_6213_nonnegative : ∀ j, 0 ≤ branch_box_6213.lower j ∧ 0 ≤ branch_box_6213.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6213, Box.profileLo, Box.profileHi, box_6213]
theorem leaf_6213_BranchSafe : CertificateConsequences.BranchSafe branch_box_6213 := by
  left; refine ⟨branch_box_6213_nonnegative, ?_⟩
  intro z hz; exact leaf_6213_sound hz

theorem leaf_6214_ok : checkAt 527 1000 box_6214 cert_6214 = true := by
  have h := List.all_eq_true.mp batch_124_05_ok accepted_6214 (by simp [batch_124_05_values])
  exact h
theorem leaf_6214_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6214.profileLo box_6214.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6214_ok
theorem branch_box_6214_nonnegative : ∀ j, 0 ≤ branch_box_6214.lower j ∧ 0 ≤ branch_box_6214.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6214, Box.profileLo, Box.profileHi, box_6214]
theorem leaf_6214_BranchSafe : CertificateConsequences.BranchSafe branch_box_6214 := by
  left; refine ⟨branch_box_6214_nonnegative, ?_⟩
  intro z hz; exact leaf_6214_sound hz

theorem leaf_6215_ok : checkAt 527 1000 box_6215 cert_6215 = true := by
  have h := List.all_eq_true.mp batch_124_06_ok accepted_6215 (by simp [batch_124_06_values])
  exact h
theorem leaf_6215_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6215.profileLo box_6215.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6215_ok
theorem branch_box_6215_nonnegative : ∀ j, 0 ≤ branch_box_6215.lower j ∧ 0 ≤ branch_box_6215.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6215, Box.profileLo, Box.profileHi, box_6215]
theorem leaf_6215_BranchSafe : CertificateConsequences.BranchSafe branch_box_6215 := by
  left; refine ⟨branch_box_6215_nonnegative, ?_⟩
  intro z hz; exact leaf_6215_sound hz

theorem leaf_6216_ok : checkAt 527 1000 box_6216 cert_6216 = true := by
  have h := List.all_eq_true.mp batch_124_07_ok accepted_6216 (by simp [batch_124_07_values])
  exact h
theorem leaf_6216_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6216.profileLo box_6216.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6216_ok
theorem branch_box_6216_nonnegative : ∀ j, 0 ≤ branch_box_6216.lower j ∧ 0 ≤ branch_box_6216.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6216, Box.profileLo, Box.profileHi, box_6216]
theorem leaf_6216_BranchSafe : CertificateConsequences.BranchSafe branch_box_6216 := by
  left; refine ⟨branch_box_6216_nonnegative, ?_⟩
  intro z hz; exact leaf_6216_sound hz

theorem leaf_6221_ok : checkAt 527 1000 box_6221 cert_6221 = true := by
  have h := List.all_eq_true.mp batch_124_08_ok accepted_6221 (by simp [batch_124_08_values])
  exact h
theorem leaf_6221_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6221.profileLo box_6221.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6221_ok
theorem branch_box_6221_nonnegative : ∀ j, 0 ≤ branch_box_6221.lower j ∧ 0 ≤ branch_box_6221.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6221, Box.profileLo, Box.profileHi, box_6221]
theorem leaf_6221_BranchSafe : CertificateConsequences.BranchSafe branch_box_6221 := by
  left; refine ⟨branch_box_6221_nonnegative, ?_⟩
  intro z hz; exact leaf_6221_sound hz

theorem leaf_6223_ok : checkAt 527 1000 box_6223 cert_6223 = true := by
  have h := List.all_eq_true.mp batch_124_09_ok accepted_6223 (by simp [batch_124_09_values])
  exact h
theorem leaf_6223_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6223.profileLo box_6223.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6223_ok
theorem branch_box_6223_nonnegative : ∀ j, 0 ≤ branch_box_6223.lower j ∧ 0 ≤ branch_box_6223.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6223, Box.profileLo, Box.profileHi, box_6223]
theorem leaf_6223_BranchSafe : CertificateConsequences.BranchSafe branch_box_6223 := by
  left; refine ⟨branch_box_6223_nonnegative, ?_⟩
  intro z hz; exact leaf_6223_sound hz

theorem leaf_6224_ok : checkAt 527 1000 box_6224 cert_6224 = true := by
  have h := List.all_eq_true.mp batch_124_10_ok accepted_6224 (by simp [batch_124_10_values])
  exact h
theorem leaf_6224_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6224.profileLo box_6224.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6224_ok
theorem branch_box_6224_nonnegative : ∀ j, 0 ≤ branch_box_6224.lower j ∧ 0 ≤ branch_box_6224.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6224, Box.profileLo, Box.profileHi, box_6224]
theorem leaf_6224_BranchSafe : CertificateConsequences.BranchSafe branch_box_6224 := by
  left; refine ⟨branch_box_6224_nonnegative, ?_⟩
  intro z hz; exact leaf_6224_sound hz

theorem leaf_6227_ok : checkAt 527 1000 box_6227 cert_6227 = true := by
  have h := List.all_eq_true.mp batch_124_11_ok accepted_6227 (by simp [batch_124_11_values])
  exact h
theorem leaf_6227_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6227.profileLo box_6227.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6227_ok
theorem branch_box_6227_nonnegative : ∀ j, 0 ≤ branch_box_6227.lower j ∧ 0 ≤ branch_box_6227.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6227, Box.profileLo, Box.profileHi, box_6227]
theorem leaf_6227_BranchSafe : CertificateConsequences.BranchSafe branch_box_6227 := by
  left; refine ⟨branch_box_6227_nonnegative, ?_⟩
  intro z hz; exact leaf_6227_sound hz

theorem leaf_6229_ok : checkAt 527 1000 box_6229 cert_6229 = true := by
  have h := List.all_eq_true.mp batch_124_12_ok accepted_6229 (by simp [batch_124_12_values])
  exact h
theorem leaf_6229_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6229.profileLo box_6229.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6229_ok
theorem branch_box_6229_nonnegative : ∀ j, 0 ≤ branch_box_6229.lower j ∧ 0 ≤ branch_box_6229.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6229, Box.profileLo, Box.profileHi, box_6229]
theorem leaf_6229_BranchSafe : CertificateConsequences.BranchSafe branch_box_6229 := by
  left; refine ⟨branch_box_6229_nonnegative, ?_⟩
  intro z hz; exact leaf_6229_sound hz

theorem leaf_6230_ok : checkAt 527 1000 box_6230 cert_6230 = true := by
  have h := List.all_eq_true.mp batch_124_13_ok accepted_6230 (by simp [batch_124_13_values])
  exact h
theorem leaf_6230_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6230.profileLo box_6230.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6230_ok
theorem branch_box_6230_nonnegative : ∀ j, 0 ≤ branch_box_6230.lower j ∧ 0 ≤ branch_box_6230.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6230, Box.profileLo, Box.profileHi, box_6230]
theorem leaf_6230_BranchSafe : CertificateConsequences.BranchSafe branch_box_6230 := by
  left; refine ⟨branch_box_6230_nonnegative, ?_⟩
  intro z hz; exact leaf_6230_sound hz

theorem leaf_6231_ok : checkAt 527 1000 box_6231 cert_6231 = true := by
  have h := List.all_eq_true.mp batch_124_14_ok accepted_6231 (by simp [batch_124_14_values])
  exact h
theorem leaf_6231_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6231.profileLo box_6231.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6231_ok
theorem branch_box_6231_nonnegative : ∀ j, 0 ≤ branch_box_6231.lower j ∧ 0 ≤ branch_box_6231.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6231, Box.profileLo, Box.profileHi, box_6231]
theorem leaf_6231_BranchSafe : CertificateConsequences.BranchSafe branch_box_6231 := by
  left; refine ⟨branch_box_6231_nonnegative, ?_⟩
  intro z hz; exact leaf_6231_sound hz

theorem leaf_6235_ok : checkAt 527 1000 box_6235 cert_6235 = true := by
  have h := List.all_eq_true.mp batch_124_15_ok accepted_6235 (by simp [batch_124_15_values])
  exact h
theorem leaf_6235_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6235.profileLo box_6235.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6235_ok
theorem branch_box_6235_nonnegative : ∀ j, 0 ≤ branch_box_6235.lower j ∧ 0 ≤ branch_box_6235.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6235, Box.profileLo, Box.profileHi, box_6235]
theorem leaf_6235_BranchSafe : CertificateConsequences.BranchSafe branch_box_6235 := by
  left; refine ⟨branch_box_6235_nonnegative, ?_⟩
  intro z hz; exact leaf_6235_sound hz

theorem leaf_6236_ok : checkAt 527 1000 box_6236 cert_6236 = true := by
  have h := List.all_eq_true.mp batch_124_16_ok accepted_6236 (by simp [batch_124_16_values])
  exact h
theorem leaf_6236_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6236.profileLo box_6236.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6236_ok
theorem branch_box_6236_nonnegative : ∀ j, 0 ≤ branch_box_6236.lower j ∧ 0 ≤ branch_box_6236.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6236, Box.profileLo, Box.profileHi, box_6236]
theorem leaf_6236_BranchSafe : CertificateConsequences.BranchSafe branch_box_6236 := by
  left; refine ⟨branch_box_6236_nonnegative, ?_⟩
  intro z hz; exact leaf_6236_sound hz

theorem leaf_6242_ok : checkAt 527 1000 box_6242 cert_6242 = true := by
  have h := List.all_eq_true.mp batch_124_17_ok accepted_6242 (by simp [batch_124_17_values])
  exact h
theorem leaf_6242_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6242.profileLo box_6242.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6242_ok
theorem branch_box_6242_nonnegative : ∀ j, 0 ≤ branch_box_6242.lower j ∧ 0 ≤ branch_box_6242.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6242, Box.profileLo, Box.profileHi, box_6242]
theorem leaf_6242_BranchSafe : CertificateConsequences.BranchSafe branch_box_6242 := by
  left; refine ⟨branch_box_6242_nonnegative, ?_⟩
  intro z hz; exact leaf_6242_sound hz

theorem leaf_6243_ok : checkAt 527 1000 box_6243 cert_6243 = true := by
  have h := List.all_eq_true.mp batch_124_18_ok accepted_6243 (by simp [batch_124_18_values])
  exact h
theorem leaf_6243_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6243.profileLo box_6243.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6243_ok
theorem branch_box_6243_nonnegative : ∀ j, 0 ≤ branch_box_6243.lower j ∧ 0 ≤ branch_box_6243.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6243, Box.profileLo, Box.profileHi, box_6243]
theorem leaf_6243_BranchSafe : CertificateConsequences.BranchSafe branch_box_6243 := by
  left; refine ⟨branch_box_6243_nonnegative, ?_⟩
  intro z hz; exact leaf_6243_sound hz

theorem leaf_6244_ok : checkAt 527 1000 box_6244 cert_6244 = true := by
  have h := List.all_eq_true.mp batch_124_19_ok accepted_6244 (by simp [batch_124_19_values])
  exact h
theorem leaf_6244_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6244.profileLo box_6244.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6244_ok
theorem branch_box_6244_nonnegative : ∀ j, 0 ≤ branch_box_6244.lower j ∧ 0 ≤ branch_box_6244.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6244, Box.profileLo, Box.profileHi, box_6244]
theorem leaf_6244_BranchSafe : CertificateConsequences.BranchSafe branch_box_6244 := by
  left; refine ⟨branch_box_6244_nonnegative, ?_⟩
  intro z hz; exact leaf_6244_sound hz

theorem leaf_6245_ok : checkAt 527 1000 box_6245 cert_6245 = true := by
  have h := List.all_eq_true.mp batch_124_20_ok accepted_6245 (by simp [batch_124_20_values])
  exact h
theorem leaf_6245_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6245.profileLo box_6245.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6245_ok
theorem branch_box_6245_nonnegative : ∀ j, 0 ≤ branch_box_6245.lower j ∧ 0 ≤ branch_box_6245.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6245, Box.profileLo, Box.profileHi, box_6245]
theorem leaf_6245_BranchSafe : CertificateConsequences.BranchSafe branch_box_6245 := by
  left; refine ⟨branch_box_6245_nonnegative, ?_⟩
  intro z hz; exact leaf_6245_sound hz

theorem leaf_6247_ok : checkAt 527 1000 box_6247 cert_6247 = true := by
  have h := List.all_eq_true.mp batch_124_21_ok accepted_6247 (by simp [batch_124_21_values])
  exact h
theorem leaf_6247_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6247.profileLo box_6247.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6247_ok
theorem branch_box_6247_nonnegative : ∀ j, 0 ≤ branch_box_6247.lower j ∧ 0 ≤ branch_box_6247.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6247, Box.profileLo, Box.profileHi, box_6247]
theorem leaf_6247_BranchSafe : CertificateConsequences.BranchSafe branch_box_6247 := by
  left; refine ⟨branch_box_6247_nonnegative, ?_⟩
  intro z hz; exact leaf_6247_sound hz

theorem leaf_6248_ok : checkAt 527 1000 box_6248 cert_6248 = true := by
  have h := List.all_eq_true.mp batch_124_22_ok accepted_6248 (by simp [batch_124_22_values])
  exact h
theorem leaf_6248_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6248.profileLo box_6248.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6248_ok
theorem branch_box_6248_nonnegative : ∀ j, 0 ≤ branch_box_6248.lower j ∧ 0 ≤ branch_box_6248.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6248, Box.profileLo, Box.profileHi, box_6248]
theorem leaf_6248_BranchSafe : CertificateConsequences.BranchSafe branch_box_6248 := by
  left; refine ⟨branch_box_6248_nonnegative, ?_⟩
  intro z hz; exact leaf_6248_sound hz

#print axioms batch_124_00_ok
#print axioms leaf_6201_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
