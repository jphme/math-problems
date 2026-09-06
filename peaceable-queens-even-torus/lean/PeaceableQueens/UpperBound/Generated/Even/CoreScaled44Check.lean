import PeaceableQueens.UpperBound.Generated.Even.CoreScaled44Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_44_00_values : List Bool := [accepted_2200]
theorem batch_44_00_ok : batch_44_00_values.all id = true := by decide

def batch_44_01_values : List Bool := [accepted_2202]
theorem batch_44_01_ok : batch_44_01_values.all id = true := by decide

def batch_44_02_values : List Bool := [accepted_2204]
theorem batch_44_02_ok : batch_44_02_values.all id = true := by decide

def batch_44_03_values : List Bool := [accepted_2205]
theorem batch_44_03_ok : batch_44_03_values.all id = true := by decide

def batch_44_04_values : List Bool := [accepted_2208]
theorem batch_44_04_ok : batch_44_04_values.all id = true := by decide

def batch_44_05_values : List Bool := [accepted_2210]
theorem batch_44_05_ok : batch_44_05_values.all id = true := by decide

def batch_44_06_values : List Bool := [accepted_2212]
theorem batch_44_06_ok : batch_44_06_values.all id = true := by decide

def batch_44_07_values : List Bool := [accepted_2213]
theorem batch_44_07_ok : batch_44_07_values.all id = true := by decide

def batch_44_08_values : List Bool := [accepted_2215]
theorem batch_44_08_ok : batch_44_08_values.all id = true := by decide

def batch_44_09_values : List Bool := [accepted_2222]
theorem batch_44_09_ok : batch_44_09_values.all id = true := by decide

def batch_44_10_values : List Bool := [accepted_2224]
theorem batch_44_10_ok : batch_44_10_values.all id = true := by decide

def batch_44_11_values : List Bool := [accepted_2225]
theorem batch_44_11_ok : batch_44_11_values.all id = true := by decide

def batch_44_12_values : List Bool := [accepted_2230]
theorem batch_44_12_ok : batch_44_12_values.all id = true := by decide

def batch_44_13_values : List Bool := [accepted_2232]
theorem batch_44_13_ok : batch_44_13_values.all id = true := by decide

def batch_44_14_values : List Bool := [accepted_2234]
theorem batch_44_14_ok : batch_44_14_values.all id = true := by decide

def batch_44_15_values : List Bool := [accepted_2235]
theorem batch_44_15_ok : batch_44_15_values.all id = true := by decide

def batch_44_16_values : List Bool := [accepted_2238]
theorem batch_44_16_ok : batch_44_16_values.all id = true := by decide

def batch_44_17_values : List Bool := [accepted_2240]
theorem batch_44_17_ok : batch_44_17_values.all id = true := by decide

def batch_44_18_values : List Bool := [accepted_2242]
theorem batch_44_18_ok : batch_44_18_values.all id = true := by decide

def batch_44_19_values : List Bool := [accepted_2244]
theorem batch_44_19_ok : batch_44_19_values.all id = true := by decide

def batch_44_20_values : List Bool := [accepted_2246]
theorem batch_44_20_ok : batch_44_20_values.all id = true := by decide

def batch_44_21_values : List Bool := [accepted_2248]
theorem batch_44_21_ok : batch_44_21_values.all id = true := by decide

def batch_44_22_values : List Bool := [accepted_2249]
theorem batch_44_22_ok : batch_44_22_values.all id = true := by decide

theorem leaf_2200_ok : checkAt 527 1000 box_2200 cert_2200 = true := by
  have h := List.all_eq_true.mp batch_44_00_ok accepted_2200 (by simp [batch_44_00_values])
  exact h
theorem leaf_2200_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2200.profileLo box_2200.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2200_ok
theorem branch_box_2200_nonnegative : ∀ j, 0 ≤ branch_box_2200.lower j ∧ 0 ≤ branch_box_2200.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2200, Box.profileLo, Box.profileHi, box_2200]
theorem leaf_2200_BranchSafe : CertificateConsequences.BranchSafe branch_box_2200 := by
  left; refine ⟨branch_box_2200_nonnegative, ?_⟩
  intro z hz; exact leaf_2200_sound hz

theorem leaf_2202_ok : checkAt 527 1000 box_2202 cert_2202 = true := by
  have h := List.all_eq_true.mp batch_44_01_ok accepted_2202 (by simp [batch_44_01_values])
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
  have h := List.all_eq_true.mp batch_44_02_ok accepted_2204 (by simp [batch_44_02_values])
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
  have h := List.all_eq_true.mp batch_44_03_ok accepted_2205 (by simp [batch_44_03_values])
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

theorem leaf_2208_ok : checkAt 527 1000 box_2208 cert_2208 = true := by
  have h := List.all_eq_true.mp batch_44_04_ok accepted_2208 (by simp [batch_44_04_values])
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
  have h := List.all_eq_true.mp batch_44_05_ok accepted_2210 (by simp [batch_44_05_values])
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

theorem leaf_2212_ok : checkAt 527 1000 box_2212 cert_2212 = true := by
  have h := List.all_eq_true.mp batch_44_06_ok accepted_2212 (by simp [batch_44_06_values])
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

theorem leaf_2213_ok : checkAt 527 1000 box_2213 cert_2213 = true := by
  have h := List.all_eq_true.mp batch_44_07_ok accepted_2213 (by simp [batch_44_07_values])
  exact h
theorem leaf_2213_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2213.profileLo box_2213.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2213_ok
theorem branch_box_2213_nonnegative : ∀ j, 0 ≤ branch_box_2213.lower j ∧ 0 ≤ branch_box_2213.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2213, Box.profileLo, Box.profileHi, box_2213]
theorem leaf_2213_BranchSafe : CertificateConsequences.BranchSafe branch_box_2213 := by
  left; refine ⟨branch_box_2213_nonnegative, ?_⟩
  intro z hz; exact leaf_2213_sound hz

theorem leaf_2215_ok : checkAt 527 1000 box_2215 cert_2215 = true := by
  have h := List.all_eq_true.mp batch_44_08_ok accepted_2215 (by simp [batch_44_08_values])
  exact h
theorem leaf_2215_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2215.profileLo box_2215.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2215_ok
theorem branch_box_2215_nonnegative : ∀ j, 0 ≤ branch_box_2215.lower j ∧ 0 ≤ branch_box_2215.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2215, Box.profileLo, Box.profileHi, box_2215]
theorem leaf_2215_BranchSafe : CertificateConsequences.BranchSafe branch_box_2215 := by
  left; refine ⟨branch_box_2215_nonnegative, ?_⟩
  intro z hz; exact leaf_2215_sound hz

theorem leaf_2222_ok : checkAt 527 1000 box_2222 cert_2222 = true := by
  have h := List.all_eq_true.mp batch_44_09_ok accepted_2222 (by simp [batch_44_09_values])
  exact h
theorem leaf_2222_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2222.profileLo box_2222.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2222_ok
theorem branch_box_2222_nonnegative : ∀ j, 0 ≤ branch_box_2222.lower j ∧ 0 ≤ branch_box_2222.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2222, Box.profileLo, Box.profileHi, box_2222]
theorem leaf_2222_BranchSafe : CertificateConsequences.BranchSafe branch_box_2222 := by
  left; refine ⟨branch_box_2222_nonnegative, ?_⟩
  intro z hz; exact leaf_2222_sound hz

theorem leaf_2224_ok : checkAt 527 1000 box_2224 cert_2224 = true := by
  have h := List.all_eq_true.mp batch_44_10_ok accepted_2224 (by simp [batch_44_10_values])
  exact h
theorem leaf_2224_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2224.profileLo box_2224.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2224_ok
theorem branch_box_2224_nonnegative : ∀ j, 0 ≤ branch_box_2224.lower j ∧ 0 ≤ branch_box_2224.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2224, Box.profileLo, Box.profileHi, box_2224]
theorem leaf_2224_BranchSafe : CertificateConsequences.BranchSafe branch_box_2224 := by
  left; refine ⟨branch_box_2224_nonnegative, ?_⟩
  intro z hz; exact leaf_2224_sound hz

theorem leaf_2225_ok : checkAt 527 1000 box_2225 cert_2225 = true := by
  have h := List.all_eq_true.mp batch_44_11_ok accepted_2225 (by simp [batch_44_11_values])
  exact h
theorem leaf_2225_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2225.profileLo box_2225.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2225_ok
theorem branch_box_2225_nonnegative : ∀ j, 0 ≤ branch_box_2225.lower j ∧ 0 ≤ branch_box_2225.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2225, Box.profileLo, Box.profileHi, box_2225]
theorem leaf_2225_BranchSafe : CertificateConsequences.BranchSafe branch_box_2225 := by
  left; refine ⟨branch_box_2225_nonnegative, ?_⟩
  intro z hz; exact leaf_2225_sound hz

theorem leaf_2230_ok : checkAt 527 1000 box_2230 cert_2230 = true := by
  have h := List.all_eq_true.mp batch_44_12_ok accepted_2230 (by simp [batch_44_12_values])
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

theorem leaf_2232_ok : checkAt 527 1000 box_2232 cert_2232 = true := by
  have h := List.all_eq_true.mp batch_44_13_ok accepted_2232 (by simp [batch_44_13_values])
  exact h
theorem leaf_2232_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2232.profileLo box_2232.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2232_ok
theorem branch_box_2232_nonnegative : ∀ j, 0 ≤ branch_box_2232.lower j ∧ 0 ≤ branch_box_2232.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2232, Box.profileLo, Box.profileHi, box_2232]
theorem leaf_2232_BranchSafe : CertificateConsequences.BranchSafe branch_box_2232 := by
  left; refine ⟨branch_box_2232_nonnegative, ?_⟩
  intro z hz; exact leaf_2232_sound hz

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

theorem leaf_2235_ok : checkAt 527 1000 box_2235 cert_2235 = true := by
  have h := List.all_eq_true.mp batch_44_15_ok accepted_2235 (by simp [batch_44_15_values])
  exact h
theorem leaf_2235_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2235.profileLo box_2235.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2235_ok
theorem branch_box_2235_nonnegative : ∀ j, 0 ≤ branch_box_2235.lower j ∧ 0 ≤ branch_box_2235.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2235, Box.profileLo, Box.profileHi, box_2235]
theorem leaf_2235_BranchSafe : CertificateConsequences.BranchSafe branch_box_2235 := by
  left; refine ⟨branch_box_2235_nonnegative, ?_⟩
  intro z hz; exact leaf_2235_sound hz

theorem leaf_2238_ok : checkAt 527 1000 box_2238 cert_2238 = true := by
  have h := List.all_eq_true.mp batch_44_16_ok accepted_2238 (by simp [batch_44_16_values])
  exact h
theorem leaf_2238_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2238.profileLo box_2238.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2238_ok
theorem branch_box_2238_nonnegative : ∀ j, 0 ≤ branch_box_2238.lower j ∧ 0 ≤ branch_box_2238.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2238, Box.profileLo, Box.profileHi, box_2238]
theorem leaf_2238_BranchSafe : CertificateConsequences.BranchSafe branch_box_2238 := by
  left; refine ⟨branch_box_2238_nonnegative, ?_⟩
  intro z hz; exact leaf_2238_sound hz

theorem leaf_2240_ok : checkAt 527 1000 box_2240 cert_2240 = true := by
  have h := List.all_eq_true.mp batch_44_17_ok accepted_2240 (by simp [batch_44_17_values])
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

theorem leaf_2244_ok : checkAt 527 1000 box_2244 cert_2244 = true := by
  have h := List.all_eq_true.mp batch_44_19_ok accepted_2244 (by simp [batch_44_19_values])
  exact h
theorem leaf_2244_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2244.profileLo box_2244.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2244_ok
theorem branch_box_2244_nonnegative : ∀ j, 0 ≤ branch_box_2244.lower j ∧ 0 ≤ branch_box_2244.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2244, Box.profileLo, Box.profileHi, box_2244]
theorem leaf_2244_BranchSafe : CertificateConsequences.BranchSafe branch_box_2244 := by
  left; refine ⟨branch_box_2244_nonnegative, ?_⟩
  intro z hz; exact leaf_2244_sound hz

theorem leaf_2246_ok : checkAt 527 1000 box_2246 cert_2246 = true := by
  have h := List.all_eq_true.mp batch_44_20_ok accepted_2246 (by simp [batch_44_20_values])
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

theorem leaf_2248_ok : checkAt 527 1000 box_2248 cert_2248 = true := by
  have h := List.all_eq_true.mp batch_44_21_ok accepted_2248 (by simp [batch_44_21_values])
  exact h
theorem leaf_2248_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2248.profileLo box_2248.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2248_ok
theorem branch_box_2248_nonnegative : ∀ j, 0 ≤ branch_box_2248.lower j ∧ 0 ≤ branch_box_2248.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2248, Box.profileLo, Box.profileHi, box_2248]
theorem leaf_2248_BranchSafe : CertificateConsequences.BranchSafe branch_box_2248 := by
  left; refine ⟨branch_box_2248_nonnegative, ?_⟩
  intro z hz; exact leaf_2248_sound hz

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
#print axioms leaf_2200_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
