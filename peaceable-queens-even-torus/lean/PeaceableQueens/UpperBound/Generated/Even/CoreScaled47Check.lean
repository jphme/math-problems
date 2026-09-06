import PeaceableQueens.UpperBound.Generated.Even.CoreScaled47Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_47_00_values : List Bool := [accepted_2352]
theorem batch_47_00_ok : batch_47_00_values.all id = true := by decide

def batch_47_01_values : List Bool := [accepted_2354]
theorem batch_47_01_ok : batch_47_01_values.all id = true := by decide

def batch_47_02_values : List Bool := [accepted_2355]
theorem batch_47_02_ok : batch_47_02_values.all id = true := by decide

def batch_47_03_values : List Bool := [accepted_2358]
theorem batch_47_03_ok : batch_47_03_values.all id = true := by decide

def batch_47_04_values : List Bool := [accepted_2360]
theorem batch_47_04_ok : batch_47_04_values.all id = true := by decide

def batch_47_05_values : List Bool := [accepted_2361]
theorem batch_47_05_ok : batch_47_05_values.all id = true := by decide

def batch_47_06_values : List Bool := [accepted_2364]
theorem batch_47_06_ok : batch_47_06_values.all id = true := by decide

def batch_47_07_values : List Bool := [accepted_2366]
theorem batch_47_07_ok : batch_47_07_values.all id = true := by decide

def batch_47_08_values : List Bool := [accepted_2368]
theorem batch_47_08_ok : batch_47_08_values.all id = true := by decide

def batch_47_09_values : List Bool := [accepted_2370]
theorem batch_47_09_ok : batch_47_09_values.all id = true := by decide

def batch_47_10_values : List Bool := [accepted_2372]
theorem batch_47_10_ok : batch_47_10_values.all id = true := by decide

def batch_47_11_values : List Bool := [accepted_2373]
theorem batch_47_11_ok : batch_47_11_values.all id = true := by decide

def batch_47_12_values : List Bool := [accepted_2376]
theorem batch_47_12_ok : batch_47_12_values.all id = true := by decide

def batch_47_13_values : List Bool := [accepted_2378]
theorem batch_47_13_ok : batch_47_13_values.all id = true := by decide

def batch_47_14_values : List Bool := [accepted_2380]
theorem batch_47_14_ok : batch_47_14_values.all id = true := by decide

def batch_47_15_values : List Bool := [accepted_2384]
theorem batch_47_15_ok : batch_47_15_values.all id = true := by decide

def batch_47_16_values : List Bool := [accepted_2389]
theorem batch_47_16_ok : batch_47_16_values.all id = true := by decide

def batch_47_17_values : List Bool := [accepted_2396]
theorem batch_47_17_ok : batch_47_17_values.all id = true := by decide

def batch_47_18_values : List Bool := [accepted_2397]
theorem batch_47_18_ok : batch_47_18_values.all id = true := by decide

def batch_47_19_values : List Bool := [accepted_2399]
theorem batch_47_19_ok : batch_47_19_values.all id = true := by decide

theorem leaf_2352_ok : checkAt 527 1000 box_2352 cert_2352 = true := by
  have h := List.all_eq_true.mp batch_47_00_ok accepted_2352 (by simp [batch_47_00_values])
  exact h
theorem leaf_2352_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2352.profileLo box_2352.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2352_ok
theorem branch_box_2352_nonnegative : ∀ j, 0 ≤ branch_box_2352.lower j ∧ 0 ≤ branch_box_2352.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2352, Box.profileLo, Box.profileHi, box_2352]
theorem leaf_2352_BranchSafe : CertificateConsequences.BranchSafe branch_box_2352 := by
  left; refine ⟨branch_box_2352_nonnegative, ?_⟩
  intro z hz; exact leaf_2352_sound hz

theorem leaf_2354_ok : checkAt 527 1000 box_2354 cert_2354 = true := by
  have h := List.all_eq_true.mp batch_47_01_ok accepted_2354 (by simp [batch_47_01_values])
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

theorem leaf_2355_ok : checkAt 527 1000 box_2355 cert_2355 = true := by
  have h := List.all_eq_true.mp batch_47_02_ok accepted_2355 (by simp [batch_47_02_values])
  exact h
theorem leaf_2355_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2355.profileLo box_2355.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2355_ok
theorem branch_box_2355_nonnegative : ∀ j, 0 ≤ branch_box_2355.lower j ∧ 0 ≤ branch_box_2355.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2355, Box.profileLo, Box.profileHi, box_2355]
theorem leaf_2355_BranchSafe : CertificateConsequences.BranchSafe branch_box_2355 := by
  left; refine ⟨branch_box_2355_nonnegative, ?_⟩
  intro z hz; exact leaf_2355_sound hz

theorem leaf_2358_ok : checkAt 527 1000 box_2358 cert_2358 = true := by
  have h := List.all_eq_true.mp batch_47_03_ok accepted_2358 (by simp [batch_47_03_values])
  exact h
theorem leaf_2358_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2358.profileLo box_2358.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2358_ok
theorem branch_box_2358_nonnegative : ∀ j, 0 ≤ branch_box_2358.lower j ∧ 0 ≤ branch_box_2358.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2358, Box.profileLo, Box.profileHi, box_2358]
theorem leaf_2358_BranchSafe : CertificateConsequences.BranchSafe branch_box_2358 := by
  left; refine ⟨branch_box_2358_nonnegative, ?_⟩
  intro z hz; exact leaf_2358_sound hz

theorem leaf_2360_ok : checkAt 527 1000 box_2360 cert_2360 = true := by
  have h := List.all_eq_true.mp batch_47_04_ok accepted_2360 (by simp [batch_47_04_values])
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

theorem leaf_2361_ok : checkAt 527 1000 box_2361 cert_2361 = true := by
  have h := List.all_eq_true.mp batch_47_05_ok accepted_2361 (by simp [batch_47_05_values])
  exact h
theorem leaf_2361_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2361.profileLo box_2361.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2361_ok
theorem branch_box_2361_nonnegative : ∀ j, 0 ≤ branch_box_2361.lower j ∧ 0 ≤ branch_box_2361.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2361, Box.profileLo, Box.profileHi, box_2361]
theorem leaf_2361_BranchSafe : CertificateConsequences.BranchSafe branch_box_2361 := by
  left; refine ⟨branch_box_2361_nonnegative, ?_⟩
  intro z hz; exact leaf_2361_sound hz

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

theorem leaf_2366_ok : checkAt 527 1000 box_2366 cert_2366 = true := by
  have h := List.all_eq_true.mp batch_47_07_ok accepted_2366 (by simp [batch_47_07_values])
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

theorem leaf_2368_ok : checkAt 527 1000 box_2368 cert_2368 = true := by
  have h := List.all_eq_true.mp batch_47_08_ok accepted_2368 (by simp [batch_47_08_values])
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

theorem leaf_2370_ok : checkAt 527 1000 box_2370 cert_2370 = true := by
  have h := List.all_eq_true.mp batch_47_09_ok accepted_2370 (by simp [batch_47_09_values])
  exact h
theorem leaf_2370_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2370.profileLo box_2370.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2370_ok
theorem branch_box_2370_nonnegative : ∀ j, 0 ≤ branch_box_2370.lower j ∧ 0 ≤ branch_box_2370.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2370, Box.profileLo, Box.profileHi, box_2370]
theorem leaf_2370_BranchSafe : CertificateConsequences.BranchSafe branch_box_2370 := by
  left; refine ⟨branch_box_2370_nonnegative, ?_⟩
  intro z hz; exact leaf_2370_sound hz

theorem leaf_2372_ok : checkAt 527 1000 box_2372 cert_2372 = true := by
  have h := List.all_eq_true.mp batch_47_10_ok accepted_2372 (by simp [batch_47_10_values])
  exact h
theorem leaf_2372_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2372.profileLo box_2372.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2372_ok
theorem branch_box_2372_nonnegative : ∀ j, 0 ≤ branch_box_2372.lower j ∧ 0 ≤ branch_box_2372.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2372, Box.profileLo, Box.profileHi, box_2372]
theorem leaf_2372_BranchSafe : CertificateConsequences.BranchSafe branch_box_2372 := by
  left; refine ⟨branch_box_2372_nonnegative, ?_⟩
  intro z hz; exact leaf_2372_sound hz

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

theorem leaf_2376_ok : checkAt 527 1000 box_2376 cert_2376 = true := by
  have h := List.all_eq_true.mp batch_47_12_ok accepted_2376 (by simp [batch_47_12_values])
  exact h
theorem leaf_2376_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2376.profileLo box_2376.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2376_ok
theorem branch_box_2376_nonnegative : ∀ j, 0 ≤ branch_box_2376.lower j ∧ 0 ≤ branch_box_2376.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2376, Box.profileLo, Box.profileHi, box_2376]
theorem leaf_2376_BranchSafe : CertificateConsequences.BranchSafe branch_box_2376 := by
  left; refine ⟨branch_box_2376_nonnegative, ?_⟩
  intro z hz; exact leaf_2376_sound hz

theorem leaf_2378_ok : checkAt 527 1000 box_2378 cert_2378 = true := by
  have h := List.all_eq_true.mp batch_47_13_ok accepted_2378 (by simp [batch_47_13_values])
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
  have h := List.all_eq_true.mp batch_47_14_ok accepted_2380 (by simp [batch_47_14_values])
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

theorem leaf_2384_ok : checkAt 527 1000 box_2384 cert_2384 = true := by
  have h := List.all_eq_true.mp batch_47_15_ok accepted_2384 (by simp [batch_47_15_values])
  exact h
theorem leaf_2384_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2384.profileLo box_2384.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2384_ok
theorem branch_box_2384_nonnegative : ∀ j, 0 ≤ branch_box_2384.lower j ∧ 0 ≤ branch_box_2384.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2384, Box.profileLo, Box.profileHi, box_2384]
theorem leaf_2384_BranchSafe : CertificateConsequences.BranchSafe branch_box_2384 := by
  left; refine ⟨branch_box_2384_nonnegative, ?_⟩
  intro z hz; exact leaf_2384_sound hz

theorem leaf_2389_ok : checkAt 527 1000 box_2389 cert_2389 = true := by
  have h := List.all_eq_true.mp batch_47_16_ok accepted_2389 (by simp [batch_47_16_values])
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

theorem leaf_2396_ok : checkAt 527 1000 box_2396 cert_2396 = true := by
  have h := List.all_eq_true.mp batch_47_17_ok accepted_2396 (by simp [batch_47_17_values])
  exact h
theorem leaf_2396_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2396.profileLo box_2396.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2396_ok
theorem branch_box_2396_nonnegative : ∀ j, 0 ≤ branch_box_2396.lower j ∧ 0 ≤ branch_box_2396.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2396, Box.profileLo, Box.profileHi, box_2396]
theorem leaf_2396_BranchSafe : CertificateConsequences.BranchSafe branch_box_2396 := by
  left; refine ⟨branch_box_2396_nonnegative, ?_⟩
  intro z hz; exact leaf_2396_sound hz

theorem leaf_2397_ok : checkAt 527 1000 box_2397 cert_2397 = true := by
  have h := List.all_eq_true.mp batch_47_18_ok accepted_2397 (by simp [batch_47_18_values])
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

theorem leaf_2399_ok : checkAt 527 1000 box_2399 cert_2399 = true := by
  have h := List.all_eq_true.mp batch_47_19_ok accepted_2399 (by simp [batch_47_19_values])
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
#print axioms leaf_2352_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
