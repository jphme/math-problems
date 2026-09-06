import PeaceableQueens.UpperBound.Generated.Even.C527Scaled45Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_45_00_values : List Bool := [accepted_2250]
theorem batch_45_00_ok : batch_45_00_values.all id = true := by decide

def batch_45_01_values : List Bool := [accepted_2253]
theorem batch_45_01_ok : batch_45_01_values.all id = true := by decide

def batch_45_02_values : List Bool := [accepted_2254]
theorem batch_45_02_ok : batch_45_02_values.all id = true := by decide

def batch_45_03_values : List Bool := [accepted_2255]
theorem batch_45_03_ok : batch_45_03_values.all id = true := by decide

def batch_45_04_values : List Bool := [accepted_2256]
theorem batch_45_04_ok : batch_45_04_values.all id = true := by decide

def batch_45_05_values : List Bool := [accepted_2261]
theorem batch_45_05_ok : batch_45_05_values.all id = true := by decide

def batch_45_06_values : List Bool := [accepted_2262]
theorem batch_45_06_ok : batch_45_06_values.all id = true := by decide

def batch_45_07_values : List Bool := [accepted_2263]
theorem batch_45_07_ok : batch_45_07_values.all id = true := by decide

def batch_45_08_values : List Bool := [accepted_2264]
theorem batch_45_08_ok : batch_45_08_values.all id = true := by decide

def batch_45_09_values : List Bool := [accepted_2265]
theorem batch_45_09_ok : batch_45_09_values.all id = true := by decide

def batch_45_10_values : List Bool := [accepted_2267]
theorem batch_45_10_ok : batch_45_10_values.all id = true := by decide

def batch_45_11_values : List Bool := [accepted_2268]
theorem batch_45_11_ok : batch_45_11_values.all id = true := by decide

def batch_45_12_values : List Bool := [accepted_2276]
theorem batch_45_12_ok : batch_45_12_values.all id = true := by decide

def batch_45_13_values : List Bool := [accepted_2277]
theorem batch_45_13_ok : batch_45_13_values.all id = true := by decide

def batch_45_14_values : List Bool := [accepted_2278]
theorem batch_45_14_ok : batch_45_14_values.all id = true := by decide

def batch_45_15_values : List Bool := [accepted_2279]
theorem batch_45_15_ok : batch_45_15_values.all id = true := by decide

def batch_45_16_values : List Bool := [accepted_2281]
theorem batch_45_16_ok : batch_45_16_values.all id = true := by decide

def batch_45_17_values : List Bool := [accepted_2282]
theorem batch_45_17_ok : batch_45_17_values.all id = true := by decide

def batch_45_18_values : List Bool := [accepted_2283]
theorem batch_45_18_ok : batch_45_18_values.all id = true := by decide

def batch_45_19_values : List Bool := [accepted_2285]
theorem batch_45_19_ok : batch_45_19_values.all id = true := by decide

def batch_45_20_values : List Bool := [accepted_2286]
theorem batch_45_20_ok : batch_45_20_values.all id = true := by decide

def batch_45_21_values : List Bool := [accepted_2288]
theorem batch_45_21_ok : batch_45_21_values.all id = true := by decide

def batch_45_22_values : List Bool := [accepted_2291]
theorem batch_45_22_ok : batch_45_22_values.all id = true := by decide

def batch_45_23_values : List Bool := [accepted_2293]
theorem batch_45_23_ok : batch_45_23_values.all id = true := by decide

def batch_45_24_values : List Bool := [accepted_2294]
theorem batch_45_24_ok : batch_45_24_values.all id = true := by decide

def batch_45_25_values : List Bool := [accepted_2295]
theorem batch_45_25_ok : batch_45_25_values.all id = true := by decide

def batch_45_26_values : List Bool := [accepted_2297]
theorem batch_45_26_ok : batch_45_26_values.all id = true := by decide

def batch_45_27_values : List Bool := [accepted_2298]
theorem batch_45_27_ok : batch_45_27_values.all id = true := by decide

theorem leaf_2250_ok : checkAt 527 1000 box_2250 cert_2250 = true := by
  have h := List.all_eq_true.mp batch_45_00_ok accepted_2250 (by simp [batch_45_00_values])
  exact h
theorem leaf_2250_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2250.profileLo box_2250.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2250_ok
theorem branch_box_2250_nonnegative : ∀ j, 0 ≤ branch_box_2250.lower j ∧ 0 ≤ branch_box_2250.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2250, Box.profileLo, Box.profileHi, box_2250]
theorem leaf_2250_BranchSafe : CertificateConsequences.BranchSafe branch_box_2250 := by
  left; refine ⟨branch_box_2250_nonnegative, ?_⟩
  intro z hz; exact leaf_2250_sound hz

theorem leaf_2253_ok : checkAt 527 1000 box_2253 cert_2253 = true := by
  have h := List.all_eq_true.mp batch_45_01_ok accepted_2253 (by simp [batch_45_01_values])
  exact h
theorem leaf_2253_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2253.profileLo box_2253.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2253_ok
theorem branch_box_2253_nonnegative : ∀ j, 0 ≤ branch_box_2253.lower j ∧ 0 ≤ branch_box_2253.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2253, Box.profileLo, Box.profileHi, box_2253]
theorem leaf_2253_BranchSafe : CertificateConsequences.BranchSafe branch_box_2253 := by
  left; refine ⟨branch_box_2253_nonnegative, ?_⟩
  intro z hz; exact leaf_2253_sound hz

theorem leaf_2254_ok : checkAt 527 1000 box_2254 cert_2254 = true := by
  have h := List.all_eq_true.mp batch_45_02_ok accepted_2254 (by simp [batch_45_02_values])
  exact h
theorem leaf_2254_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2254.profileLo box_2254.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2254_ok
theorem branch_box_2254_nonnegative : ∀ j, 0 ≤ branch_box_2254.lower j ∧ 0 ≤ branch_box_2254.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2254, Box.profileLo, Box.profileHi, box_2254]
theorem leaf_2254_BranchSafe : CertificateConsequences.BranchSafe branch_box_2254 := by
  left; refine ⟨branch_box_2254_nonnegative, ?_⟩
  intro z hz; exact leaf_2254_sound hz

theorem leaf_2255_ok : checkAt 527 1000 box_2255 cert_2255 = true := by
  have h := List.all_eq_true.mp batch_45_03_ok accepted_2255 (by simp [batch_45_03_values])
  exact h
theorem leaf_2255_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2255.profileLo box_2255.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2255_ok
theorem branch_box_2255_nonnegative : ∀ j, 0 ≤ branch_box_2255.lower j ∧ 0 ≤ branch_box_2255.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2255, Box.profileLo, Box.profileHi, box_2255]
theorem leaf_2255_BranchSafe : CertificateConsequences.BranchSafe branch_box_2255 := by
  left; refine ⟨branch_box_2255_nonnegative, ?_⟩
  intro z hz; exact leaf_2255_sound hz

theorem leaf_2256_ok : checkAt 527 1000 box_2256 cert_2256 = true := by
  have h := List.all_eq_true.mp batch_45_04_ok accepted_2256 (by simp [batch_45_04_values])
  exact h
theorem leaf_2256_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2256.profileLo box_2256.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2256_ok
theorem branch_box_2256_nonnegative : ∀ j, 0 ≤ branch_box_2256.lower j ∧ 0 ≤ branch_box_2256.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2256, Box.profileLo, Box.profileHi, box_2256]
theorem leaf_2256_BranchSafe : CertificateConsequences.BranchSafe branch_box_2256 := by
  left; refine ⟨branch_box_2256_nonnegative, ?_⟩
  intro z hz; exact leaf_2256_sound hz

theorem leaf_2261_ok : checkAt 527 1000 box_2261 cert_2261 = true := by
  have h := List.all_eq_true.mp batch_45_05_ok accepted_2261 (by simp [batch_45_05_values])
  exact h
theorem leaf_2261_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2261.profileLo box_2261.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2261_ok
theorem branch_box_2261_nonnegative : ∀ j, 0 ≤ branch_box_2261.lower j ∧ 0 ≤ branch_box_2261.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2261, Box.profileLo, Box.profileHi, box_2261]
theorem leaf_2261_BranchSafe : CertificateConsequences.BranchSafe branch_box_2261 := by
  left; refine ⟨branch_box_2261_nonnegative, ?_⟩
  intro z hz; exact leaf_2261_sound hz

theorem leaf_2262_ok : checkAt 527 1000 box_2262 cert_2262 = true := by
  have h := List.all_eq_true.mp batch_45_06_ok accepted_2262 (by simp [batch_45_06_values])
  exact h
theorem leaf_2262_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2262.profileLo box_2262.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2262_ok
theorem branch_box_2262_nonnegative : ∀ j, 0 ≤ branch_box_2262.lower j ∧ 0 ≤ branch_box_2262.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2262, Box.profileLo, Box.profileHi, box_2262]
theorem leaf_2262_BranchSafe : CertificateConsequences.BranchSafe branch_box_2262 := by
  left; refine ⟨branch_box_2262_nonnegative, ?_⟩
  intro z hz; exact leaf_2262_sound hz

theorem leaf_2263_ok : checkAt 527 1000 box_2263 cert_2263 = true := by
  have h := List.all_eq_true.mp batch_45_07_ok accepted_2263 (by simp [batch_45_07_values])
  exact h
theorem leaf_2263_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2263.profileLo box_2263.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2263_ok
theorem branch_box_2263_nonnegative : ∀ j, 0 ≤ branch_box_2263.lower j ∧ 0 ≤ branch_box_2263.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2263, Box.profileLo, Box.profileHi, box_2263]
theorem leaf_2263_BranchSafe : CertificateConsequences.BranchSafe branch_box_2263 := by
  left; refine ⟨branch_box_2263_nonnegative, ?_⟩
  intro z hz; exact leaf_2263_sound hz

theorem leaf_2264_ok : checkAt 527 1000 box_2264 cert_2264 = true := by
  have h := List.all_eq_true.mp batch_45_08_ok accepted_2264 (by simp [batch_45_08_values])
  exact h
theorem leaf_2264_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2264.profileLo box_2264.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2264_ok
theorem branch_box_2264_nonnegative : ∀ j, 0 ≤ branch_box_2264.lower j ∧ 0 ≤ branch_box_2264.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2264, Box.profileLo, Box.profileHi, box_2264]
theorem leaf_2264_BranchSafe : CertificateConsequences.BranchSafe branch_box_2264 := by
  left; refine ⟨branch_box_2264_nonnegative, ?_⟩
  intro z hz; exact leaf_2264_sound hz

theorem leaf_2265_ok : checkAt 527 1000 box_2265 cert_2265 = true := by
  have h := List.all_eq_true.mp batch_45_09_ok accepted_2265 (by simp [batch_45_09_values])
  exact h
theorem leaf_2265_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2265.profileLo box_2265.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2265_ok
theorem branch_box_2265_nonnegative : ∀ j, 0 ≤ branch_box_2265.lower j ∧ 0 ≤ branch_box_2265.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2265, Box.profileLo, Box.profileHi, box_2265]
theorem leaf_2265_BranchSafe : CertificateConsequences.BranchSafe branch_box_2265 := by
  left; refine ⟨branch_box_2265_nonnegative, ?_⟩
  intro z hz; exact leaf_2265_sound hz

theorem leaf_2267_ok : checkAt 527 1000 box_2267 cert_2267 = true := by
  have h := List.all_eq_true.mp batch_45_10_ok accepted_2267 (by simp [batch_45_10_values])
  exact h
theorem leaf_2267_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2267.profileLo box_2267.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2267_ok
theorem branch_box_2267_nonnegative : ∀ j, 0 ≤ branch_box_2267.lower j ∧ 0 ≤ branch_box_2267.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2267, Box.profileLo, Box.profileHi, box_2267]
theorem leaf_2267_BranchSafe : CertificateConsequences.BranchSafe branch_box_2267 := by
  left; refine ⟨branch_box_2267_nonnegative, ?_⟩
  intro z hz; exact leaf_2267_sound hz

theorem leaf_2268_ok : checkAt 527 1000 box_2268 cert_2268 = true := by
  have h := List.all_eq_true.mp batch_45_11_ok accepted_2268 (by simp [batch_45_11_values])
  exact h
theorem leaf_2268_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2268.profileLo box_2268.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2268_ok
theorem branch_box_2268_nonnegative : ∀ j, 0 ≤ branch_box_2268.lower j ∧ 0 ≤ branch_box_2268.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2268, Box.profileLo, Box.profileHi, box_2268]
theorem leaf_2268_BranchSafe : CertificateConsequences.BranchSafe branch_box_2268 := by
  left; refine ⟨branch_box_2268_nonnegative, ?_⟩
  intro z hz; exact leaf_2268_sound hz

theorem leaf_2276_ok : checkAt 527 1000 box_2276 cert_2276 = true := by
  have h := List.all_eq_true.mp batch_45_12_ok accepted_2276 (by simp [batch_45_12_values])
  exact h
theorem leaf_2276_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2276.profileLo box_2276.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2276_ok
theorem branch_box_2276_nonnegative : ∀ j, 0 ≤ branch_box_2276.lower j ∧ 0 ≤ branch_box_2276.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2276, Box.profileLo, Box.profileHi, box_2276]
theorem leaf_2276_BranchSafe : CertificateConsequences.BranchSafe branch_box_2276 := by
  left; refine ⟨branch_box_2276_nonnegative, ?_⟩
  intro z hz; exact leaf_2276_sound hz

theorem leaf_2277_ok : checkAt 527 1000 box_2277 cert_2277 = true := by
  have h := List.all_eq_true.mp batch_45_13_ok accepted_2277 (by simp [batch_45_13_values])
  exact h
theorem leaf_2277_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2277.profileLo box_2277.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2277_ok
theorem branch_box_2277_nonnegative : ∀ j, 0 ≤ branch_box_2277.lower j ∧ 0 ≤ branch_box_2277.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2277, Box.profileLo, Box.profileHi, box_2277]
theorem leaf_2277_BranchSafe : CertificateConsequences.BranchSafe branch_box_2277 := by
  left; refine ⟨branch_box_2277_nonnegative, ?_⟩
  intro z hz; exact leaf_2277_sound hz

theorem leaf_2278_ok : checkAt 527 1000 box_2278 cert_2278 = true := by
  have h := List.all_eq_true.mp batch_45_14_ok accepted_2278 (by simp [batch_45_14_values])
  exact h
theorem leaf_2278_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2278.profileLo box_2278.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2278_ok
theorem branch_box_2278_nonnegative : ∀ j, 0 ≤ branch_box_2278.lower j ∧ 0 ≤ branch_box_2278.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2278, Box.profileLo, Box.profileHi, box_2278]
theorem leaf_2278_BranchSafe : CertificateConsequences.BranchSafe branch_box_2278 := by
  left; refine ⟨branch_box_2278_nonnegative, ?_⟩
  intro z hz; exact leaf_2278_sound hz

theorem leaf_2279_ok : checkAt 527 1000 box_2279 cert_2279 = true := by
  have h := List.all_eq_true.mp batch_45_15_ok accepted_2279 (by simp [batch_45_15_values])
  exact h
theorem leaf_2279_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2279.profileLo box_2279.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2279_ok
theorem branch_box_2279_nonnegative : ∀ j, 0 ≤ branch_box_2279.lower j ∧ 0 ≤ branch_box_2279.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2279, Box.profileLo, Box.profileHi, box_2279]
theorem leaf_2279_BranchSafe : CertificateConsequences.BranchSafe branch_box_2279 := by
  left; refine ⟨branch_box_2279_nonnegative, ?_⟩
  intro z hz; exact leaf_2279_sound hz

theorem leaf_2281_ok : checkAt 527 1000 box_2281 cert_2281 = true := by
  have h := List.all_eq_true.mp batch_45_16_ok accepted_2281 (by simp [batch_45_16_values])
  exact h
theorem leaf_2281_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2281.profileLo box_2281.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2281_ok
theorem branch_box_2281_nonnegative : ∀ j, 0 ≤ branch_box_2281.lower j ∧ 0 ≤ branch_box_2281.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2281, Box.profileLo, Box.profileHi, box_2281]
theorem leaf_2281_BranchSafe : CertificateConsequences.BranchSafe branch_box_2281 := by
  left; refine ⟨branch_box_2281_nonnegative, ?_⟩
  intro z hz; exact leaf_2281_sound hz

theorem leaf_2282_ok : checkAt 527 1000 box_2282 cert_2282 = true := by
  have h := List.all_eq_true.mp batch_45_17_ok accepted_2282 (by simp [batch_45_17_values])
  exact h
theorem leaf_2282_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2282.profileLo box_2282.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2282_ok
theorem branch_box_2282_nonnegative : ∀ j, 0 ≤ branch_box_2282.lower j ∧ 0 ≤ branch_box_2282.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2282, Box.profileLo, Box.profileHi, box_2282]
theorem leaf_2282_BranchSafe : CertificateConsequences.BranchSafe branch_box_2282 := by
  left; refine ⟨branch_box_2282_nonnegative, ?_⟩
  intro z hz; exact leaf_2282_sound hz

theorem leaf_2283_ok : checkAt 527 1000 box_2283 cert_2283 = true := by
  have h := List.all_eq_true.mp batch_45_18_ok accepted_2283 (by simp [batch_45_18_values])
  exact h
theorem leaf_2283_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2283.profileLo box_2283.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2283_ok
theorem branch_box_2283_nonnegative : ∀ j, 0 ≤ branch_box_2283.lower j ∧ 0 ≤ branch_box_2283.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2283, Box.profileLo, Box.profileHi, box_2283]
theorem leaf_2283_BranchSafe : CertificateConsequences.BranchSafe branch_box_2283 := by
  left; refine ⟨branch_box_2283_nonnegative, ?_⟩
  intro z hz; exact leaf_2283_sound hz

theorem leaf_2285_ok : checkAt 527 1000 box_2285 cert_2285 = true := by
  have h := List.all_eq_true.mp batch_45_19_ok accepted_2285 (by simp [batch_45_19_values])
  exact h
theorem leaf_2285_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2285.profileLo box_2285.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2285_ok
theorem branch_box_2285_nonnegative : ∀ j, 0 ≤ branch_box_2285.lower j ∧ 0 ≤ branch_box_2285.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2285, Box.profileLo, Box.profileHi, box_2285]
theorem leaf_2285_BranchSafe : CertificateConsequences.BranchSafe branch_box_2285 := by
  left; refine ⟨branch_box_2285_nonnegative, ?_⟩
  intro z hz; exact leaf_2285_sound hz

theorem leaf_2286_ok : checkAt 527 1000 box_2286 cert_2286 = true := by
  have h := List.all_eq_true.mp batch_45_20_ok accepted_2286 (by simp [batch_45_20_values])
  exact h
theorem leaf_2286_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2286.profileLo box_2286.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2286_ok
theorem branch_box_2286_nonnegative : ∀ j, 0 ≤ branch_box_2286.lower j ∧ 0 ≤ branch_box_2286.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2286, Box.profileLo, Box.profileHi, box_2286]
theorem leaf_2286_BranchSafe : CertificateConsequences.BranchSafe branch_box_2286 := by
  left; refine ⟨branch_box_2286_nonnegative, ?_⟩
  intro z hz; exact leaf_2286_sound hz

theorem leaf_2288_ok : checkAt 527 1000 box_2288 cert_2288 = true := by
  have h := List.all_eq_true.mp batch_45_21_ok accepted_2288 (by simp [batch_45_21_values])
  exact h
theorem leaf_2288_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2288.profileLo box_2288.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2288_ok
theorem branch_box_2288_nonnegative : ∀ j, 0 ≤ branch_box_2288.lower j ∧ 0 ≤ branch_box_2288.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2288, Box.profileLo, Box.profileHi, box_2288]
theorem leaf_2288_BranchSafe : CertificateConsequences.BranchSafe branch_box_2288 := by
  left; refine ⟨branch_box_2288_nonnegative, ?_⟩
  intro z hz; exact leaf_2288_sound hz

theorem leaf_2291_ok : checkAt 527 1000 box_2291 cert_2291 = true := by
  have h := List.all_eq_true.mp batch_45_22_ok accepted_2291 (by simp [batch_45_22_values])
  exact h
theorem leaf_2291_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2291.profileLo box_2291.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2291_ok
theorem branch_box_2291_nonnegative : ∀ j, 0 ≤ branch_box_2291.lower j ∧ 0 ≤ branch_box_2291.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2291, Box.profileLo, Box.profileHi, box_2291]
theorem leaf_2291_BranchSafe : CertificateConsequences.BranchSafe branch_box_2291 := by
  left; refine ⟨branch_box_2291_nonnegative, ?_⟩
  intro z hz; exact leaf_2291_sound hz

theorem leaf_2293_ok : checkAt 527 1000 box_2293 cert_2293 = true := by
  have h := List.all_eq_true.mp batch_45_23_ok accepted_2293 (by simp [batch_45_23_values])
  exact h
theorem leaf_2293_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2293.profileLo box_2293.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2293_ok
theorem branch_box_2293_nonnegative : ∀ j, 0 ≤ branch_box_2293.lower j ∧ 0 ≤ branch_box_2293.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2293, Box.profileLo, Box.profileHi, box_2293]
theorem leaf_2293_BranchSafe : CertificateConsequences.BranchSafe branch_box_2293 := by
  left; refine ⟨branch_box_2293_nonnegative, ?_⟩
  intro z hz; exact leaf_2293_sound hz

theorem leaf_2294_ok : checkAt 527 1000 box_2294 cert_2294 = true := by
  have h := List.all_eq_true.mp batch_45_24_ok accepted_2294 (by simp [batch_45_24_values])
  exact h
theorem leaf_2294_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2294.profileLo box_2294.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2294_ok
theorem branch_box_2294_nonnegative : ∀ j, 0 ≤ branch_box_2294.lower j ∧ 0 ≤ branch_box_2294.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2294, Box.profileLo, Box.profileHi, box_2294]
theorem leaf_2294_BranchSafe : CertificateConsequences.BranchSafe branch_box_2294 := by
  left; refine ⟨branch_box_2294_nonnegative, ?_⟩
  intro z hz; exact leaf_2294_sound hz

theorem leaf_2295_ok : checkAt 527 1000 box_2295 cert_2295 = true := by
  have h := List.all_eq_true.mp batch_45_25_ok accepted_2295 (by simp [batch_45_25_values])
  exact h
theorem leaf_2295_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2295.profileLo box_2295.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2295_ok
theorem branch_box_2295_nonnegative : ∀ j, 0 ≤ branch_box_2295.lower j ∧ 0 ≤ branch_box_2295.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2295, Box.profileLo, Box.profileHi, box_2295]
theorem leaf_2295_BranchSafe : CertificateConsequences.BranchSafe branch_box_2295 := by
  left; refine ⟨branch_box_2295_nonnegative, ?_⟩
  intro z hz; exact leaf_2295_sound hz

theorem leaf_2297_ok : checkAt 527 1000 box_2297 cert_2297 = true := by
  have h := List.all_eq_true.mp batch_45_26_ok accepted_2297 (by simp [batch_45_26_values])
  exact h
theorem leaf_2297_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2297.profileLo box_2297.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2297_ok
theorem branch_box_2297_nonnegative : ∀ j, 0 ≤ branch_box_2297.lower j ∧ 0 ≤ branch_box_2297.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2297, Box.profileLo, Box.profileHi, box_2297]
theorem leaf_2297_BranchSafe : CertificateConsequences.BranchSafe branch_box_2297 := by
  left; refine ⟨branch_box_2297_nonnegative, ?_⟩
  intro z hz; exact leaf_2297_sound hz

theorem leaf_2298_ok : checkAt 527 1000 box_2298 cert_2298 = true := by
  have h := List.all_eq_true.mp batch_45_27_ok accepted_2298 (by simp [batch_45_27_values])
  exact h
theorem leaf_2298_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2298.profileLo box_2298.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2298_ok
theorem branch_box_2298_nonnegative : ∀ j, 0 ≤ branch_box_2298.lower j ∧ 0 ≤ branch_box_2298.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2298, Box.profileLo, Box.profileHi, box_2298]
theorem leaf_2298_BranchSafe : CertificateConsequences.BranchSafe branch_box_2298 := by
  left; refine ⟨branch_box_2298_nonnegative, ?_⟩
  intro z hz; exact leaf_2298_sound hz

#print axioms batch_45_00_ok
#print axioms leaf_2250_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
