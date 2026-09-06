import PeaceableQueens.UpperBound.Generated.Even.C527Scaled44Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_44_00_values : List Bool := [accepted_2202]
theorem batch_44_00_ok : batch_44_00_values.all id = true := by decide

def batch_44_01_values : List Bool := [accepted_2204]
theorem batch_44_01_ok : batch_44_01_values.all id = true := by decide

def batch_44_02_values : List Bool := [accepted_2205]
theorem batch_44_02_ok : batch_44_02_values.all id = true := by decide

def batch_44_03_values : List Bool := [accepted_2206]
theorem batch_44_03_ok : batch_44_03_values.all id = true := by decide

def batch_44_04_values : List Bool := [accepted_2207]
theorem batch_44_04_ok : batch_44_04_values.all id = true := by decide

def batch_44_05_values : List Bool := [accepted_2208]
theorem batch_44_05_ok : batch_44_05_values.all id = true := by decide

def batch_44_06_values : List Bool := [accepted_2210]
theorem batch_44_06_ok : batch_44_06_values.all id = true := by decide

def batch_44_07_values : List Bool := [accepted_2211]
theorem batch_44_07_ok : batch_44_07_values.all id = true := by decide

def batch_44_08_values : List Bool := [accepted_2212]
theorem batch_44_08_ok : batch_44_08_values.all id = true := by decide

def batch_44_09_values : List Bool := [accepted_2227]
theorem batch_44_09_ok : batch_44_09_values.all id = true := by decide

def batch_44_10_values : List Bool := [accepted_2229]
theorem batch_44_10_ok : batch_44_10_values.all id = true := by decide

def batch_44_11_values : List Bool := [accepted_2230]
theorem batch_44_11_ok : batch_44_11_values.all id = true := by decide

def batch_44_12_values : List Bool := [accepted_2231]
theorem batch_44_12_ok : batch_44_12_values.all id = true := by decide

def batch_44_13_values : List Bool := [accepted_2233]
theorem batch_44_13_ok : batch_44_13_values.all id = true := by decide

def batch_44_14_values : List Bool := [accepted_2234]
theorem batch_44_14_ok : batch_44_14_values.all id = true := by decide

def batch_44_15_values : List Bool := [accepted_2239]
theorem batch_44_15_ok : batch_44_15_values.all id = true := by decide

def batch_44_16_values : List Bool := [accepted_2240]
theorem batch_44_16_ok : batch_44_16_values.all id = true := by decide

def batch_44_17_values : List Bool := [accepted_2241]
theorem batch_44_17_ok : batch_44_17_values.all id = true := by decide

def batch_44_18_values : List Bool := [accepted_2242]
theorem batch_44_18_ok : batch_44_18_values.all id = true := by decide

def batch_44_19_values : List Bool := [accepted_2243]
theorem batch_44_19_ok : batch_44_19_values.all id = true := by decide

def batch_44_20_values : List Bool := [accepted_2245]
theorem batch_44_20_ok : batch_44_20_values.all id = true := by decide

def batch_44_21_values : List Bool := [accepted_2246]
theorem batch_44_21_ok : batch_44_21_values.all id = true := by decide

def batch_44_22_values : List Bool := [accepted_2249]
theorem batch_44_22_ok : batch_44_22_values.all id = true := by decide

theorem leaf_2202_ok : checkAt 527 1000 box_2202 cert_2202 = true := by
  have h := List.all_eq_true.mp batch_44_00_ok accepted_2202 (by simp [batch_44_00_values])
  exact h
theorem leaf_2202_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2202.profileLo box_2202.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2202_ok
theorem branch_box_2202_nonnegative : ∀ j, 0 ≤ branch_box_2202.lower j ∧ 0 ≤ branch_box_2202.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2202, Box.profileLo, Box.profileHi, box_2202]
theorem leaf_2202_BranchSafe : CertificateConsequences.BranchSafe branch_box_2202 := by
  left; refine ⟨branch_box_2202_nonnegative, ?_⟩
  intro z hz; exact leaf_2202_sound hz

theorem leaf_2204_ok : checkAt 527 1000 box_2204 cert_2204 = true := by
  have h := List.all_eq_true.mp batch_44_01_ok accepted_2204 (by simp [batch_44_01_values])
  exact h
theorem leaf_2204_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2204.profileLo box_2204.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2204_ok
theorem branch_box_2204_nonnegative : ∀ j, 0 ≤ branch_box_2204.lower j ∧ 0 ≤ branch_box_2204.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2204, Box.profileLo, Box.profileHi, box_2204]
theorem leaf_2204_BranchSafe : CertificateConsequences.BranchSafe branch_box_2204 := by
  left; refine ⟨branch_box_2204_nonnegative, ?_⟩
  intro z hz; exact leaf_2204_sound hz

theorem leaf_2205_ok : checkAt 527 1000 box_2205 cert_2205 = true := by
  have h := List.all_eq_true.mp batch_44_02_ok accepted_2205 (by simp [batch_44_02_values])
  exact h
theorem leaf_2205_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2205.profileLo box_2205.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2205_ok
theorem branch_box_2205_nonnegative : ∀ j, 0 ≤ branch_box_2205.lower j ∧ 0 ≤ branch_box_2205.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2205, Box.profileLo, Box.profileHi, box_2205]
theorem leaf_2205_BranchSafe : CertificateConsequences.BranchSafe branch_box_2205 := by
  left; refine ⟨branch_box_2205_nonnegative, ?_⟩
  intro z hz; exact leaf_2205_sound hz

theorem leaf_2206_ok : checkAt 527 1000 box_2206 cert_2206 = true := by
  have h := List.all_eq_true.mp batch_44_03_ok accepted_2206 (by simp [batch_44_03_values])
  exact h
theorem leaf_2206_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2206.profileLo box_2206.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2206_ok
theorem branch_box_2206_nonnegative : ∀ j, 0 ≤ branch_box_2206.lower j ∧ 0 ≤ branch_box_2206.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2206, Box.profileLo, Box.profileHi, box_2206]
theorem leaf_2206_BranchSafe : CertificateConsequences.BranchSafe branch_box_2206 := by
  left; refine ⟨branch_box_2206_nonnegative, ?_⟩
  intro z hz; exact leaf_2206_sound hz

theorem leaf_2207_ok : checkAt 527 1000 box_2207 cert_2207 = true := by
  have h := List.all_eq_true.mp batch_44_04_ok accepted_2207 (by simp [batch_44_04_values])
  exact h
theorem leaf_2207_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2207.profileLo box_2207.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2207_ok
theorem branch_box_2207_nonnegative : ∀ j, 0 ≤ branch_box_2207.lower j ∧ 0 ≤ branch_box_2207.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2207, Box.profileLo, Box.profileHi, box_2207]
theorem leaf_2207_BranchSafe : CertificateConsequences.BranchSafe branch_box_2207 := by
  left; refine ⟨branch_box_2207_nonnegative, ?_⟩
  intro z hz; exact leaf_2207_sound hz

theorem leaf_2208_ok : checkAt 527 1000 box_2208 cert_2208 = true := by
  have h := List.all_eq_true.mp batch_44_05_ok accepted_2208 (by simp [batch_44_05_values])
  exact h
theorem leaf_2208_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2208.profileLo box_2208.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2208_ok
theorem branch_box_2208_nonnegative : ∀ j, 0 ≤ branch_box_2208.lower j ∧ 0 ≤ branch_box_2208.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2208, Box.profileLo, Box.profileHi, box_2208]
theorem leaf_2208_BranchSafe : CertificateConsequences.BranchSafe branch_box_2208 := by
  left; refine ⟨branch_box_2208_nonnegative, ?_⟩
  intro z hz; exact leaf_2208_sound hz

theorem leaf_2210_ok : checkAt 527 1000 box_2210 cert_2210 = true := by
  have h := List.all_eq_true.mp batch_44_06_ok accepted_2210 (by simp [batch_44_06_values])
  exact h
theorem leaf_2210_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2210.profileLo box_2210.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2210_ok
theorem branch_box_2210_nonnegative : ∀ j, 0 ≤ branch_box_2210.lower j ∧ 0 ≤ branch_box_2210.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2210, Box.profileLo, Box.profileHi, box_2210]
theorem leaf_2210_BranchSafe : CertificateConsequences.BranchSafe branch_box_2210 := by
  left; refine ⟨branch_box_2210_nonnegative, ?_⟩
  intro z hz; exact leaf_2210_sound hz

theorem leaf_2211_ok : checkAt 527 1000 box_2211 cert_2211 = true := by
  have h := List.all_eq_true.mp batch_44_07_ok accepted_2211 (by simp [batch_44_07_values])
  exact h
theorem leaf_2211_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2211.profileLo box_2211.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2211_ok
theorem branch_box_2211_nonnegative : ∀ j, 0 ≤ branch_box_2211.lower j ∧ 0 ≤ branch_box_2211.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2211, Box.profileLo, Box.profileHi, box_2211]
theorem leaf_2211_BranchSafe : CertificateConsequences.BranchSafe branch_box_2211 := by
  left; refine ⟨branch_box_2211_nonnegative, ?_⟩
  intro z hz; exact leaf_2211_sound hz

theorem leaf_2212_ok : checkAt 527 1000 box_2212 cert_2212 = true := by
  have h := List.all_eq_true.mp batch_44_08_ok accepted_2212 (by simp [batch_44_08_values])
  exact h
theorem leaf_2212_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2212.profileLo box_2212.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2212_ok
theorem branch_box_2212_nonnegative : ∀ j, 0 ≤ branch_box_2212.lower j ∧ 0 ≤ branch_box_2212.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2212, Box.profileLo, Box.profileHi, box_2212]
theorem leaf_2212_BranchSafe : CertificateConsequences.BranchSafe branch_box_2212 := by
  left; refine ⟨branch_box_2212_nonnegative, ?_⟩
  intro z hz; exact leaf_2212_sound hz

theorem leaf_2227_ok : checkAt 527 1000 box_2227 cert_2227 = true := by
  have h := List.all_eq_true.mp batch_44_09_ok accepted_2227 (by simp [batch_44_09_values])
  exact h
theorem leaf_2227_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2227.profileLo box_2227.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2227_ok
theorem branch_box_2227_nonnegative : ∀ j, 0 ≤ branch_box_2227.lower j ∧ 0 ≤ branch_box_2227.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2227, Box.profileLo, Box.profileHi, box_2227]
theorem leaf_2227_BranchSafe : CertificateConsequences.BranchSafe branch_box_2227 := by
  left; refine ⟨branch_box_2227_nonnegative, ?_⟩
  intro z hz; exact leaf_2227_sound hz

theorem leaf_2229_ok : checkAt 527 1000 box_2229 cert_2229 = true := by
  have h := List.all_eq_true.mp batch_44_10_ok accepted_2229 (by simp [batch_44_10_values])
  exact h
theorem leaf_2229_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2229.profileLo box_2229.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2229_ok
theorem branch_box_2229_nonnegative : ∀ j, 0 ≤ branch_box_2229.lower j ∧ 0 ≤ branch_box_2229.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2229, Box.profileLo, Box.profileHi, box_2229]
theorem leaf_2229_BranchSafe : CertificateConsequences.BranchSafe branch_box_2229 := by
  left; refine ⟨branch_box_2229_nonnegative, ?_⟩
  intro z hz; exact leaf_2229_sound hz

theorem leaf_2230_ok : checkAt 527 1000 box_2230 cert_2230 = true := by
  have h := List.all_eq_true.mp batch_44_11_ok accepted_2230 (by simp [batch_44_11_values])
  exact h
theorem leaf_2230_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2230.profileLo box_2230.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2230_ok
theorem branch_box_2230_nonnegative : ∀ j, 0 ≤ branch_box_2230.lower j ∧ 0 ≤ branch_box_2230.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2230, Box.profileLo, Box.profileHi, box_2230]
theorem leaf_2230_BranchSafe : CertificateConsequences.BranchSafe branch_box_2230 := by
  left; refine ⟨branch_box_2230_nonnegative, ?_⟩
  intro z hz; exact leaf_2230_sound hz

theorem leaf_2231_ok : checkAt 527 1000 box_2231 cert_2231 = true := by
  have h := List.all_eq_true.mp batch_44_12_ok accepted_2231 (by simp [batch_44_12_values])
  exact h
theorem leaf_2231_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2231.profileLo box_2231.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2231_ok
theorem branch_box_2231_nonnegative : ∀ j, 0 ≤ branch_box_2231.lower j ∧ 0 ≤ branch_box_2231.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2231, Box.profileLo, Box.profileHi, box_2231]
theorem leaf_2231_BranchSafe : CertificateConsequences.BranchSafe branch_box_2231 := by
  left; refine ⟨branch_box_2231_nonnegative, ?_⟩
  intro z hz; exact leaf_2231_sound hz

theorem leaf_2233_ok : checkAt 527 1000 box_2233 cert_2233 = true := by
  have h := List.all_eq_true.mp batch_44_13_ok accepted_2233 (by simp [batch_44_13_values])
  exact h
theorem leaf_2233_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2233.profileLo box_2233.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2233_ok
theorem branch_box_2233_nonnegative : ∀ j, 0 ≤ branch_box_2233.lower j ∧ 0 ≤ branch_box_2233.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2233, Box.profileLo, Box.profileHi, box_2233]
theorem leaf_2233_BranchSafe : CertificateConsequences.BranchSafe branch_box_2233 := by
  left; refine ⟨branch_box_2233_nonnegative, ?_⟩
  intro z hz; exact leaf_2233_sound hz

theorem leaf_2234_ok : checkAt 527 1000 box_2234 cert_2234 = true := by
  have h := List.all_eq_true.mp batch_44_14_ok accepted_2234 (by simp [batch_44_14_values])
  exact h
theorem leaf_2234_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2234.profileLo box_2234.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2234_ok
theorem branch_box_2234_nonnegative : ∀ j, 0 ≤ branch_box_2234.lower j ∧ 0 ≤ branch_box_2234.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2234, Box.profileLo, Box.profileHi, box_2234]
theorem leaf_2234_BranchSafe : CertificateConsequences.BranchSafe branch_box_2234 := by
  left; refine ⟨branch_box_2234_nonnegative, ?_⟩
  intro z hz; exact leaf_2234_sound hz

theorem leaf_2239_ok : checkAt 527 1000 box_2239 cert_2239 = true := by
  have h := List.all_eq_true.mp batch_44_15_ok accepted_2239 (by simp [batch_44_15_values])
  exact h
theorem leaf_2239_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2239.profileLo box_2239.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2239_ok
theorem branch_box_2239_nonnegative : ∀ j, 0 ≤ branch_box_2239.lower j ∧ 0 ≤ branch_box_2239.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2239, Box.profileLo, Box.profileHi, box_2239]
theorem leaf_2239_BranchSafe : CertificateConsequences.BranchSafe branch_box_2239 := by
  left; refine ⟨branch_box_2239_nonnegative, ?_⟩
  intro z hz; exact leaf_2239_sound hz

theorem leaf_2240_ok : checkAt 527 1000 box_2240 cert_2240 = true := by
  have h := List.all_eq_true.mp batch_44_16_ok accepted_2240 (by simp [batch_44_16_values])
  exact h
theorem leaf_2240_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2240.profileLo box_2240.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2240_ok
theorem branch_box_2240_nonnegative : ∀ j, 0 ≤ branch_box_2240.lower j ∧ 0 ≤ branch_box_2240.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2240, Box.profileLo, Box.profileHi, box_2240]
theorem leaf_2240_BranchSafe : CertificateConsequences.BranchSafe branch_box_2240 := by
  left; refine ⟨branch_box_2240_nonnegative, ?_⟩
  intro z hz; exact leaf_2240_sound hz

theorem leaf_2241_ok : checkAt 527 1000 box_2241 cert_2241 = true := by
  have h := List.all_eq_true.mp batch_44_17_ok accepted_2241 (by simp [batch_44_17_values])
  exact h
theorem leaf_2241_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2241.profileLo box_2241.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2241_ok
theorem branch_box_2241_nonnegative : ∀ j, 0 ≤ branch_box_2241.lower j ∧ 0 ≤ branch_box_2241.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2241, Box.profileLo, Box.profileHi, box_2241]
theorem leaf_2241_BranchSafe : CertificateConsequences.BranchSafe branch_box_2241 := by
  left; refine ⟨branch_box_2241_nonnegative, ?_⟩
  intro z hz; exact leaf_2241_sound hz

theorem leaf_2242_ok : checkAt 527 1000 box_2242 cert_2242 = true := by
  have h := List.all_eq_true.mp batch_44_18_ok accepted_2242 (by simp [batch_44_18_values])
  exact h
theorem leaf_2242_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2242.profileLo box_2242.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2242_ok
theorem branch_box_2242_nonnegative : ∀ j, 0 ≤ branch_box_2242.lower j ∧ 0 ≤ branch_box_2242.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2242, Box.profileLo, Box.profileHi, box_2242]
theorem leaf_2242_BranchSafe : CertificateConsequences.BranchSafe branch_box_2242 := by
  left; refine ⟨branch_box_2242_nonnegative, ?_⟩
  intro z hz; exact leaf_2242_sound hz

theorem leaf_2243_ok : checkAt 527 1000 box_2243 cert_2243 = true := by
  have h := List.all_eq_true.mp batch_44_19_ok accepted_2243 (by simp [batch_44_19_values])
  exact h
theorem leaf_2243_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2243.profileLo box_2243.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2243_ok
theorem branch_box_2243_nonnegative : ∀ j, 0 ≤ branch_box_2243.lower j ∧ 0 ≤ branch_box_2243.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2243, Box.profileLo, Box.profileHi, box_2243]
theorem leaf_2243_BranchSafe : CertificateConsequences.BranchSafe branch_box_2243 := by
  left; refine ⟨branch_box_2243_nonnegative, ?_⟩
  intro z hz; exact leaf_2243_sound hz

theorem leaf_2245_ok : checkAt 527 1000 box_2245 cert_2245 = true := by
  have h := List.all_eq_true.mp batch_44_20_ok accepted_2245 (by simp [batch_44_20_values])
  exact h
theorem leaf_2245_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2245.profileLo box_2245.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2245_ok
theorem branch_box_2245_nonnegative : ∀ j, 0 ≤ branch_box_2245.lower j ∧ 0 ≤ branch_box_2245.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2245, Box.profileLo, Box.profileHi, box_2245]
theorem leaf_2245_BranchSafe : CertificateConsequences.BranchSafe branch_box_2245 := by
  left; refine ⟨branch_box_2245_nonnegative, ?_⟩
  intro z hz; exact leaf_2245_sound hz

theorem leaf_2246_ok : checkAt 527 1000 box_2246 cert_2246 = true := by
  have h := List.all_eq_true.mp batch_44_21_ok accepted_2246 (by simp [batch_44_21_values])
  exact h
theorem leaf_2246_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2246.profileLo box_2246.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2246_ok
theorem branch_box_2246_nonnegative : ∀ j, 0 ≤ branch_box_2246.lower j ∧ 0 ≤ branch_box_2246.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2246, Box.profileLo, Box.profileHi, box_2246]
theorem leaf_2246_BranchSafe : CertificateConsequences.BranchSafe branch_box_2246 := by
  left; refine ⟨branch_box_2246_nonnegative, ?_⟩
  intro z hz; exact leaf_2246_sound hz

theorem leaf_2249_ok : checkAt 527 1000 box_2249 cert_2249 = true := by
  have h := List.all_eq_true.mp batch_44_22_ok accepted_2249 (by simp [batch_44_22_values])
  exact h
theorem leaf_2249_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2249.profileLo box_2249.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2249_ok
theorem branch_box_2249_nonnegative : ∀ j, 0 ≤ branch_box_2249.lower j ∧ 0 ≤ branch_box_2249.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2249, Box.profileLo, Box.profileHi, box_2249]
theorem leaf_2249_BranchSafe : CertificateConsequences.BranchSafe branch_box_2249 := by
  left; refine ⟨branch_box_2249_nonnegative, ?_⟩
  intro z hz; exact leaf_2249_sound hz

#print axioms batch_44_00_ok
#print axioms leaf_2202_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
