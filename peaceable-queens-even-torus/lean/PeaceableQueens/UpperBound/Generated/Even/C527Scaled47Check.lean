import PeaceableQueens.UpperBound.Generated.Even.C527Scaled47Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_47_00_values : List Bool := [accepted_2350]
theorem batch_47_00_ok : batch_47_00_values.all id = true := by decide

def batch_47_01_values : List Bool := [accepted_2351]
theorem batch_47_01_ok : batch_47_01_values.all id = true := by decide

def batch_47_02_values : List Bool := [accepted_2353]
theorem batch_47_02_ok : batch_47_02_values.all id = true := by decide

def batch_47_03_values : List Bool := [accepted_2354]
theorem batch_47_03_ok : batch_47_03_values.all id = true := by decide

def batch_47_04_values : List Bool := [accepted_2359]
theorem batch_47_04_ok : batch_47_04_values.all id = true := by decide

def batch_47_05_values : List Bool := [accepted_2360]
theorem batch_47_05_ok : batch_47_05_values.all id = true := by decide

def batch_47_06_values : List Bool := [accepted_2364]
theorem batch_47_06_ok : batch_47_06_values.all id = true := by decide

def batch_47_07_values : List Bool := [accepted_2365]
theorem batch_47_07_ok : batch_47_07_values.all id = true := by decide

def batch_47_08_values : List Bool := [accepted_2366]
theorem batch_47_08_ok : batch_47_08_values.all id = true := by decide

def batch_47_09_values : List Bool := [accepted_2367]
theorem batch_47_09_ok : batch_47_09_values.all id = true := by decide

def batch_47_10_values : List Bool := [accepted_2368]
theorem batch_47_10_ok : batch_47_10_values.all id = true := by decide

def batch_47_11_values : List Bool := [accepted_2373]
theorem batch_47_11_ok : batch_47_11_values.all id = true := by decide

def batch_47_12_values : List Bool := [accepted_2374]
theorem batch_47_12_ok : batch_47_12_values.all id = true := by decide

def batch_47_13_values : List Bool := [accepted_2375]
theorem batch_47_13_ok : batch_47_13_values.all id = true := by decide

def batch_47_14_values : List Bool := [accepted_2377]
theorem batch_47_14_ok : batch_47_14_values.all id = true := by decide

def batch_47_15_values : List Bool := [accepted_2378]
theorem batch_47_15_ok : batch_47_15_values.all id = true := by decide

def batch_47_16_values : List Bool := [accepted_2380]
theorem batch_47_16_ok : batch_47_16_values.all id = true := by decide

def batch_47_17_values : List Bool := [accepted_2381]
theorem batch_47_17_ok : batch_47_17_values.all id = true := by decide

def batch_47_18_values : List Bool := [accepted_2382]
theorem batch_47_18_ok : batch_47_18_values.all id = true := by decide

def batch_47_19_values : List Bool := [accepted_2385]
theorem batch_47_19_ok : batch_47_19_values.all id = true := by decide

def batch_47_20_values : List Bool := [accepted_2387]
theorem batch_47_20_ok : batch_47_20_values.all id = true := by decide

def batch_47_21_values : List Bool := [accepted_2389]
theorem batch_47_21_ok : batch_47_21_values.all id = true := by decide

def batch_47_22_values : List Bool := [accepted_2390]
theorem batch_47_22_ok : batch_47_22_values.all id = true := by decide

def batch_47_23_values : List Bool := [accepted_2393]
theorem batch_47_23_ok : batch_47_23_values.all id = true := by decide

def batch_47_24_values : List Bool := [accepted_2394]
theorem batch_47_24_ok : batch_47_24_values.all id = true := by decide

def batch_47_25_values : List Bool := [accepted_2397]
theorem batch_47_25_ok : batch_47_25_values.all id = true := by decide

def batch_47_26_values : List Bool := [accepted_2398]
theorem batch_47_26_ok : batch_47_26_values.all id = true := by decide

def batch_47_27_values : List Bool := [accepted_2399]
theorem batch_47_27_ok : batch_47_27_values.all id = true := by decide

theorem leaf_2350_ok : checkAt 527 1000 box_2350 cert_2350 = true := by
  have h := List.all_eq_true.mp batch_47_00_ok accepted_2350 (by simp [batch_47_00_values])
  exact h
theorem leaf_2350_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2350.profileLo box_2350.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2350_ok
theorem branch_box_2350_nonnegative : ∀ j, 0 ≤ branch_box_2350.lower j ∧ 0 ≤ branch_box_2350.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2350, Box.profileLo, Box.profileHi, box_2350]
theorem leaf_2350_BranchSafe : CertificateConsequences.BranchSafe branch_box_2350 := by
  left; refine ⟨branch_box_2350_nonnegative, ?_⟩
  intro z hz; exact leaf_2350_sound hz

theorem leaf_2351_ok : checkAt 527 1000 box_2351 cert_2351 = true := by
  have h := List.all_eq_true.mp batch_47_01_ok accepted_2351 (by simp [batch_47_01_values])
  exact h
theorem leaf_2351_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2351.profileLo box_2351.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2351_ok
theorem branch_box_2351_nonnegative : ∀ j, 0 ≤ branch_box_2351.lower j ∧ 0 ≤ branch_box_2351.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2351, Box.profileLo, Box.profileHi, box_2351]
theorem leaf_2351_BranchSafe : CertificateConsequences.BranchSafe branch_box_2351 := by
  left; refine ⟨branch_box_2351_nonnegative, ?_⟩
  intro z hz; exact leaf_2351_sound hz

theorem leaf_2353_ok : checkAt 527 1000 box_2353 cert_2353 = true := by
  have h := List.all_eq_true.mp batch_47_02_ok accepted_2353 (by simp [batch_47_02_values])
  exact h
theorem leaf_2353_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2353.profileLo box_2353.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2353_ok
theorem branch_box_2353_nonnegative : ∀ j, 0 ≤ branch_box_2353.lower j ∧ 0 ≤ branch_box_2353.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2353, Box.profileLo, Box.profileHi, box_2353]
theorem leaf_2353_BranchSafe : CertificateConsequences.BranchSafe branch_box_2353 := by
  left; refine ⟨branch_box_2353_nonnegative, ?_⟩
  intro z hz; exact leaf_2353_sound hz

theorem leaf_2354_ok : checkAt 527 1000 box_2354 cert_2354 = true := by
  have h := List.all_eq_true.mp batch_47_03_ok accepted_2354 (by simp [batch_47_03_values])
  exact h
theorem leaf_2354_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2354.profileLo box_2354.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2354_ok
theorem branch_box_2354_nonnegative : ∀ j, 0 ≤ branch_box_2354.lower j ∧ 0 ≤ branch_box_2354.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2354, Box.profileLo, Box.profileHi, box_2354]
theorem leaf_2354_BranchSafe : CertificateConsequences.BranchSafe branch_box_2354 := by
  left; refine ⟨branch_box_2354_nonnegative, ?_⟩
  intro z hz; exact leaf_2354_sound hz

theorem leaf_2359_ok : checkAt 527 1000 box_2359 cert_2359 = true := by
  have h := List.all_eq_true.mp batch_47_04_ok accepted_2359 (by simp [batch_47_04_values])
  exact h
theorem leaf_2359_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2359.profileLo box_2359.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2359_ok
theorem branch_box_2359_nonnegative : ∀ j, 0 ≤ branch_box_2359.lower j ∧ 0 ≤ branch_box_2359.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2359, Box.profileLo, Box.profileHi, box_2359]
theorem leaf_2359_BranchSafe : CertificateConsequences.BranchSafe branch_box_2359 := by
  left; refine ⟨branch_box_2359_nonnegative, ?_⟩
  intro z hz; exact leaf_2359_sound hz

theorem leaf_2360_ok : checkAt 527 1000 box_2360 cert_2360 = true := by
  have h := List.all_eq_true.mp batch_47_05_ok accepted_2360 (by simp [batch_47_05_values])
  exact h
theorem leaf_2360_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2360.profileLo box_2360.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2360_ok
theorem branch_box_2360_nonnegative : ∀ j, 0 ≤ branch_box_2360.lower j ∧ 0 ≤ branch_box_2360.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2360, Box.profileLo, Box.profileHi, box_2360]
theorem leaf_2360_BranchSafe : CertificateConsequences.BranchSafe branch_box_2360 := by
  left; refine ⟨branch_box_2360_nonnegative, ?_⟩
  intro z hz; exact leaf_2360_sound hz

theorem leaf_2364_ok : checkAt 527 1000 box_2364 cert_2364 = true := by
  have h := List.all_eq_true.mp batch_47_06_ok accepted_2364 (by simp [batch_47_06_values])
  exact h
theorem leaf_2364_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2364.profileLo box_2364.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2364_ok
theorem branch_box_2364_nonnegative : ∀ j, 0 ≤ branch_box_2364.lower j ∧ 0 ≤ branch_box_2364.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2364, Box.profileLo, Box.profileHi, box_2364]
theorem leaf_2364_BranchSafe : CertificateConsequences.BranchSafe branch_box_2364 := by
  left; refine ⟨branch_box_2364_nonnegative, ?_⟩
  intro z hz; exact leaf_2364_sound hz

theorem leaf_2365_ok : checkAt 527 1000 box_2365 cert_2365 = true := by
  have h := List.all_eq_true.mp batch_47_07_ok accepted_2365 (by simp [batch_47_07_values])
  exact h
theorem leaf_2365_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2365.profileLo box_2365.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2365_ok
theorem branch_box_2365_nonnegative : ∀ j, 0 ≤ branch_box_2365.lower j ∧ 0 ≤ branch_box_2365.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2365, Box.profileLo, Box.profileHi, box_2365]
theorem leaf_2365_BranchSafe : CertificateConsequences.BranchSafe branch_box_2365 := by
  left; refine ⟨branch_box_2365_nonnegative, ?_⟩
  intro z hz; exact leaf_2365_sound hz

theorem leaf_2366_ok : checkAt 527 1000 box_2366 cert_2366 = true := by
  have h := List.all_eq_true.mp batch_47_08_ok accepted_2366 (by simp [batch_47_08_values])
  exact h
theorem leaf_2366_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2366.profileLo box_2366.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2366_ok
theorem branch_box_2366_nonnegative : ∀ j, 0 ≤ branch_box_2366.lower j ∧ 0 ≤ branch_box_2366.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2366, Box.profileLo, Box.profileHi, box_2366]
theorem leaf_2366_BranchSafe : CertificateConsequences.BranchSafe branch_box_2366 := by
  left; refine ⟨branch_box_2366_nonnegative, ?_⟩
  intro z hz; exact leaf_2366_sound hz

theorem leaf_2367_ok : checkAt 527 1000 box_2367 cert_2367 = true := by
  have h := List.all_eq_true.mp batch_47_09_ok accepted_2367 (by simp [batch_47_09_values])
  exact h
theorem leaf_2367_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2367.profileLo box_2367.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2367_ok
theorem branch_box_2367_nonnegative : ∀ j, 0 ≤ branch_box_2367.lower j ∧ 0 ≤ branch_box_2367.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2367, Box.profileLo, Box.profileHi, box_2367]
theorem leaf_2367_BranchSafe : CertificateConsequences.BranchSafe branch_box_2367 := by
  left; refine ⟨branch_box_2367_nonnegative, ?_⟩
  intro z hz; exact leaf_2367_sound hz

theorem leaf_2368_ok : checkAt 527 1000 box_2368 cert_2368 = true := by
  have h := List.all_eq_true.mp batch_47_10_ok accepted_2368 (by simp [batch_47_10_values])
  exact h
theorem leaf_2368_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2368.profileLo box_2368.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2368_ok
theorem branch_box_2368_nonnegative : ∀ j, 0 ≤ branch_box_2368.lower j ∧ 0 ≤ branch_box_2368.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2368, Box.profileLo, Box.profileHi, box_2368]
theorem leaf_2368_BranchSafe : CertificateConsequences.BranchSafe branch_box_2368 := by
  left; refine ⟨branch_box_2368_nonnegative, ?_⟩
  intro z hz; exact leaf_2368_sound hz

theorem leaf_2373_ok : checkAt 527 1000 box_2373 cert_2373 = true := by
  have h := List.all_eq_true.mp batch_47_11_ok accepted_2373 (by simp [batch_47_11_values])
  exact h
theorem leaf_2373_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2373.profileLo box_2373.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2373_ok
theorem branch_box_2373_nonnegative : ∀ j, 0 ≤ branch_box_2373.lower j ∧ 0 ≤ branch_box_2373.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2373, Box.profileLo, Box.profileHi, box_2373]
theorem leaf_2373_BranchSafe : CertificateConsequences.BranchSafe branch_box_2373 := by
  left; refine ⟨branch_box_2373_nonnegative, ?_⟩
  intro z hz; exact leaf_2373_sound hz

theorem leaf_2374_ok : checkAt 527 1000 box_2374 cert_2374 = true := by
  have h := List.all_eq_true.mp batch_47_12_ok accepted_2374 (by simp [batch_47_12_values])
  exact h
theorem leaf_2374_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2374.profileLo box_2374.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2374_ok
theorem branch_box_2374_nonnegative : ∀ j, 0 ≤ branch_box_2374.lower j ∧ 0 ≤ branch_box_2374.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2374, Box.profileLo, Box.profileHi, box_2374]
theorem leaf_2374_BranchSafe : CertificateConsequences.BranchSafe branch_box_2374 := by
  left; refine ⟨branch_box_2374_nonnegative, ?_⟩
  intro z hz; exact leaf_2374_sound hz

theorem leaf_2375_ok : checkAt 527 1000 box_2375 cert_2375 = true := by
  have h := List.all_eq_true.mp batch_47_13_ok accepted_2375 (by simp [batch_47_13_values])
  exact h
theorem leaf_2375_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2375.profileLo box_2375.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2375_ok
theorem branch_box_2375_nonnegative : ∀ j, 0 ≤ branch_box_2375.lower j ∧ 0 ≤ branch_box_2375.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2375, Box.profileLo, Box.profileHi, box_2375]
theorem leaf_2375_BranchSafe : CertificateConsequences.BranchSafe branch_box_2375 := by
  left; refine ⟨branch_box_2375_nonnegative, ?_⟩
  intro z hz; exact leaf_2375_sound hz

theorem leaf_2377_ok : checkAt 527 1000 box_2377 cert_2377 = true := by
  have h := List.all_eq_true.mp batch_47_14_ok accepted_2377 (by simp [batch_47_14_values])
  exact h
theorem leaf_2377_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2377.profileLo box_2377.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2377_ok
theorem branch_box_2377_nonnegative : ∀ j, 0 ≤ branch_box_2377.lower j ∧ 0 ≤ branch_box_2377.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2377, Box.profileLo, Box.profileHi, box_2377]
theorem leaf_2377_BranchSafe : CertificateConsequences.BranchSafe branch_box_2377 := by
  left; refine ⟨branch_box_2377_nonnegative, ?_⟩
  intro z hz; exact leaf_2377_sound hz

theorem leaf_2378_ok : checkAt 527 1000 box_2378 cert_2378 = true := by
  have h := List.all_eq_true.mp batch_47_15_ok accepted_2378 (by simp [batch_47_15_values])
  exact h
theorem leaf_2378_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2378.profileLo box_2378.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2378_ok
theorem branch_box_2378_nonnegative : ∀ j, 0 ≤ branch_box_2378.lower j ∧ 0 ≤ branch_box_2378.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2378, Box.profileLo, Box.profileHi, box_2378]
theorem leaf_2378_BranchSafe : CertificateConsequences.BranchSafe branch_box_2378 := by
  left; refine ⟨branch_box_2378_nonnegative, ?_⟩
  intro z hz; exact leaf_2378_sound hz

theorem leaf_2380_ok : checkAt 527 1000 box_2380 cert_2380 = true := by
  have h := List.all_eq_true.mp batch_47_16_ok accepted_2380 (by simp [batch_47_16_values])
  exact h
theorem leaf_2380_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2380.profileLo box_2380.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2380_ok
theorem branch_box_2380_nonnegative : ∀ j, 0 ≤ branch_box_2380.lower j ∧ 0 ≤ branch_box_2380.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2380, Box.profileLo, Box.profileHi, box_2380]
theorem leaf_2380_BranchSafe : CertificateConsequences.BranchSafe branch_box_2380 := by
  left; refine ⟨branch_box_2380_nonnegative, ?_⟩
  intro z hz; exact leaf_2380_sound hz

theorem leaf_2381_ok : checkAt 527 1000 box_2381 cert_2381 = true := by
  have h := List.all_eq_true.mp batch_47_17_ok accepted_2381 (by simp [batch_47_17_values])
  exact h
theorem leaf_2381_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2381.profileLo box_2381.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2381_ok
theorem branch_box_2381_nonnegative : ∀ j, 0 ≤ branch_box_2381.lower j ∧ 0 ≤ branch_box_2381.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2381, Box.profileLo, Box.profileHi, box_2381]
theorem leaf_2381_BranchSafe : CertificateConsequences.BranchSafe branch_box_2381 := by
  left; refine ⟨branch_box_2381_nonnegative, ?_⟩
  intro z hz; exact leaf_2381_sound hz

theorem leaf_2382_ok : checkAt 527 1000 box_2382 cert_2382 = true := by
  have h := List.all_eq_true.mp batch_47_18_ok accepted_2382 (by simp [batch_47_18_values])
  exact h
theorem leaf_2382_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2382.profileLo box_2382.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2382_ok
theorem branch_box_2382_nonnegative : ∀ j, 0 ≤ branch_box_2382.lower j ∧ 0 ≤ branch_box_2382.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2382, Box.profileLo, Box.profileHi, box_2382]
theorem leaf_2382_BranchSafe : CertificateConsequences.BranchSafe branch_box_2382 := by
  left; refine ⟨branch_box_2382_nonnegative, ?_⟩
  intro z hz; exact leaf_2382_sound hz

theorem leaf_2385_ok : checkAt 527 1000 box_2385 cert_2385 = true := by
  have h := List.all_eq_true.mp batch_47_19_ok accepted_2385 (by simp [batch_47_19_values])
  exact h
theorem leaf_2385_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2385.profileLo box_2385.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2385_ok
theorem branch_box_2385_nonnegative : ∀ j, 0 ≤ branch_box_2385.lower j ∧ 0 ≤ branch_box_2385.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2385, Box.profileLo, Box.profileHi, box_2385]
theorem leaf_2385_BranchSafe : CertificateConsequences.BranchSafe branch_box_2385 := by
  left; refine ⟨branch_box_2385_nonnegative, ?_⟩
  intro z hz; exact leaf_2385_sound hz

theorem leaf_2387_ok : checkAt 527 1000 box_2387 cert_2387 = true := by
  have h := List.all_eq_true.mp batch_47_20_ok accepted_2387 (by simp [batch_47_20_values])
  exact h
theorem leaf_2387_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2387.profileLo box_2387.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2387_ok
theorem branch_box_2387_nonnegative : ∀ j, 0 ≤ branch_box_2387.lower j ∧ 0 ≤ branch_box_2387.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2387, Box.profileLo, Box.profileHi, box_2387]
theorem leaf_2387_BranchSafe : CertificateConsequences.BranchSafe branch_box_2387 := by
  left; refine ⟨branch_box_2387_nonnegative, ?_⟩
  intro z hz; exact leaf_2387_sound hz

theorem leaf_2389_ok : checkAt 527 1000 box_2389 cert_2389 = true := by
  have h := List.all_eq_true.mp batch_47_21_ok accepted_2389 (by simp [batch_47_21_values])
  exact h
theorem leaf_2389_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2389.profileLo box_2389.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2389_ok
theorem branch_box_2389_nonnegative : ∀ j, 0 ≤ branch_box_2389.lower j ∧ 0 ≤ branch_box_2389.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2389, Box.profileLo, Box.profileHi, box_2389]
theorem leaf_2389_BranchSafe : CertificateConsequences.BranchSafe branch_box_2389 := by
  left; refine ⟨branch_box_2389_nonnegative, ?_⟩
  intro z hz; exact leaf_2389_sound hz

theorem leaf_2390_ok : checkAt 527 1000 box_2390 cert_2390 = true := by
  have h := List.all_eq_true.mp batch_47_22_ok accepted_2390 (by simp [batch_47_22_values])
  exact h
theorem leaf_2390_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2390.profileLo box_2390.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2390_ok
theorem branch_box_2390_nonnegative : ∀ j, 0 ≤ branch_box_2390.lower j ∧ 0 ≤ branch_box_2390.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2390, Box.profileLo, Box.profileHi, box_2390]
theorem leaf_2390_BranchSafe : CertificateConsequences.BranchSafe branch_box_2390 := by
  left; refine ⟨branch_box_2390_nonnegative, ?_⟩
  intro z hz; exact leaf_2390_sound hz

theorem leaf_2393_ok : checkAt 527 1000 box_2393 cert_2393 = true := by
  have h := List.all_eq_true.mp batch_47_23_ok accepted_2393 (by simp [batch_47_23_values])
  exact h
theorem leaf_2393_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2393.profileLo box_2393.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2393_ok
theorem branch_box_2393_nonnegative : ∀ j, 0 ≤ branch_box_2393.lower j ∧ 0 ≤ branch_box_2393.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2393, Box.profileLo, Box.profileHi, box_2393]
theorem leaf_2393_BranchSafe : CertificateConsequences.BranchSafe branch_box_2393 := by
  left; refine ⟨branch_box_2393_nonnegative, ?_⟩
  intro z hz; exact leaf_2393_sound hz

theorem leaf_2394_ok : checkAt 527 1000 box_2394 cert_2394 = true := by
  have h := List.all_eq_true.mp batch_47_24_ok accepted_2394 (by simp [batch_47_24_values])
  exact h
theorem leaf_2394_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2394.profileLo box_2394.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2394_ok
theorem branch_box_2394_nonnegative : ∀ j, 0 ≤ branch_box_2394.lower j ∧ 0 ≤ branch_box_2394.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2394, Box.profileLo, Box.profileHi, box_2394]
theorem leaf_2394_BranchSafe : CertificateConsequences.BranchSafe branch_box_2394 := by
  left; refine ⟨branch_box_2394_nonnegative, ?_⟩
  intro z hz; exact leaf_2394_sound hz

theorem leaf_2397_ok : checkAt 527 1000 box_2397 cert_2397 = true := by
  have h := List.all_eq_true.mp batch_47_25_ok accepted_2397 (by simp [batch_47_25_values])
  exact h
theorem leaf_2397_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2397.profileLo box_2397.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2397_ok
theorem branch_box_2397_nonnegative : ∀ j, 0 ≤ branch_box_2397.lower j ∧ 0 ≤ branch_box_2397.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2397, Box.profileLo, Box.profileHi, box_2397]
theorem leaf_2397_BranchSafe : CertificateConsequences.BranchSafe branch_box_2397 := by
  left; refine ⟨branch_box_2397_nonnegative, ?_⟩
  intro z hz; exact leaf_2397_sound hz

theorem leaf_2398_ok : checkAt 527 1000 box_2398 cert_2398 = true := by
  have h := List.all_eq_true.mp batch_47_26_ok accepted_2398 (by simp [batch_47_26_values])
  exact h
theorem leaf_2398_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2398.profileLo box_2398.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2398_ok
theorem branch_box_2398_nonnegative : ∀ j, 0 ≤ branch_box_2398.lower j ∧ 0 ≤ branch_box_2398.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2398, Box.profileLo, Box.profileHi, box_2398]
theorem leaf_2398_BranchSafe : CertificateConsequences.BranchSafe branch_box_2398 := by
  left; refine ⟨branch_box_2398_nonnegative, ?_⟩
  intro z hz; exact leaf_2398_sound hz

theorem leaf_2399_ok : checkAt 527 1000 box_2399 cert_2399 = true := by
  have h := List.all_eq_true.mp batch_47_27_ok accepted_2399 (by simp [batch_47_27_values])
  exact h
theorem leaf_2399_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2399.profileLo box_2399.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2399_ok
theorem branch_box_2399_nonnegative : ∀ j, 0 ≤ branch_box_2399.lower j ∧ 0 ≤ branch_box_2399.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2399, Box.profileLo, Box.profileHi, box_2399]
theorem leaf_2399_BranchSafe : CertificateConsequences.BranchSafe branch_box_2399 := by
  left; refine ⟨branch_box_2399_nonnegative, ?_⟩
  intro z hz; exact leaf_2399_sound hz

#print axioms batch_47_00_ok
#print axioms leaf_2350_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
