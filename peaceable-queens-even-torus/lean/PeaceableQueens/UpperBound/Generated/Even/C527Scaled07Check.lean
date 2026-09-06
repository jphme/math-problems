import PeaceableQueens.UpperBound.Generated.Even.C527Scaled07Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_07_00_values : List Bool := [accepted_350]
theorem batch_07_00_ok : batch_07_00_values.all id = true := by decide

def batch_07_01_values : List Bool := [accepted_356]
theorem batch_07_01_ok : batch_07_01_values.all id = true := by decide

def batch_07_02_values : List Bool := [accepted_357]
theorem batch_07_02_ok : batch_07_02_values.all id = true := by decide

def batch_07_03_values : List Bool := [accepted_358]
theorem batch_07_03_ok : batch_07_03_values.all id = true := by decide

def batch_07_04_values : List Bool := [accepted_362]
theorem batch_07_04_ok : batch_07_04_values.all id = true := by decide

def batch_07_05_values : List Bool := [accepted_364]
theorem batch_07_05_ok : batch_07_05_values.all id = true := by decide

def batch_07_06_values : List Bool := [accepted_365]
theorem batch_07_06_ok : batch_07_06_values.all id = true := by decide

def batch_07_07_values : List Bool := [accepted_367]
theorem batch_07_07_ok : batch_07_07_values.all id = true := by decide

def batch_07_08_values : List Bool := [accepted_368]
theorem batch_07_08_ok : batch_07_08_values.all id = true := by decide

def batch_07_09_values : List Bool := [accepted_370]
theorem batch_07_09_ok : batch_07_09_values.all id = true := by decide

def batch_07_10_values : List Bool := [accepted_371]
theorem batch_07_10_ok : batch_07_10_values.all id = true := by decide

def batch_07_11_values : List Bool := [accepted_372]
theorem batch_07_11_ok : batch_07_11_values.all id = true := by decide

def batch_07_12_values : List Bool := [accepted_377]
theorem batch_07_12_ok : batch_07_12_values.all id = true := by decide

def batch_07_13_values : List Bool := [accepted_378]
theorem batch_07_13_ok : batch_07_13_values.all id = true := by decide

def batch_07_14_values : List Bool := [accepted_386]
theorem batch_07_14_ok : batch_07_14_values.all id = true := by decide

def batch_07_15_values : List Bool := [accepted_387]
theorem batch_07_15_ok : batch_07_15_values.all id = true := by decide

def batch_07_16_values : List Bool := [accepted_388]
theorem batch_07_16_ok : batch_07_16_values.all id = true := by decide

def batch_07_17_values : List Bool := [accepted_389]
theorem batch_07_17_ok : batch_07_17_values.all id = true := by decide

def batch_07_18_values : List Bool := [accepted_391]
theorem batch_07_18_ok : batch_07_18_values.all id = true := by decide

def batch_07_19_values : List Bool := [accepted_392]
theorem batch_07_19_ok : batch_07_19_values.all id = true := by decide

def batch_07_20_values : List Bool := [accepted_393]
theorem batch_07_20_ok : batch_07_20_values.all id = true := by decide

def batch_07_21_values : List Bool := [accepted_395]
theorem batch_07_21_ok : batch_07_21_values.all id = true := by decide

def batch_07_22_values : List Bool := [accepted_396]
theorem batch_07_22_ok : batch_07_22_values.all id = true := by decide

def batch_07_23_values : List Bool := [accepted_399]
theorem batch_07_23_ok : batch_07_23_values.all id = true := by decide

theorem leaf_350_ok : checkAt 527 1000 box_350 cert_350 = true := by
  have h := List.all_eq_true.mp batch_07_00_ok accepted_350 (by simp [batch_07_00_values])
  exact h
theorem leaf_350_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_350.profileLo box_350.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_350_ok
theorem branch_box_350_nonnegative : ∀ j, 0 ≤ branch_box_350.lower j ∧ 0 ≤ branch_box_350.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_350, Box.profileLo, Box.profileHi, box_350]
theorem leaf_350_BranchSafe : CertificateConsequences.BranchSafe branch_box_350 := by
  left; refine ⟨branch_box_350_nonnegative, ?_⟩
  intro z hz; exact leaf_350_sound hz

theorem leaf_356_ok : checkAt 527 1000 box_356 cert_356 = true := by
  have h := List.all_eq_true.mp batch_07_01_ok accepted_356 (by simp [batch_07_01_values])
  exact h
theorem leaf_356_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_356.profileLo box_356.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_356_ok
theorem branch_box_356_nonnegative : ∀ j, 0 ≤ branch_box_356.lower j ∧ 0 ≤ branch_box_356.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_356, Box.profileLo, Box.profileHi, box_356]
theorem leaf_356_BranchSafe : CertificateConsequences.BranchSafe branch_box_356 := by
  left; refine ⟨branch_box_356_nonnegative, ?_⟩
  intro z hz; exact leaf_356_sound hz

theorem leaf_357_ok : checkAt 527 1000 box_357 cert_357 = true := by
  have h := List.all_eq_true.mp batch_07_02_ok accepted_357 (by simp [batch_07_02_values])
  exact h
theorem leaf_357_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_357.profileLo box_357.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_357_ok
theorem branch_box_357_nonnegative : ∀ j, 0 ≤ branch_box_357.lower j ∧ 0 ≤ branch_box_357.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_357, Box.profileLo, Box.profileHi, box_357]
theorem leaf_357_BranchSafe : CertificateConsequences.BranchSafe branch_box_357 := by
  left; refine ⟨branch_box_357_nonnegative, ?_⟩
  intro z hz; exact leaf_357_sound hz

theorem leaf_358_ok : checkAt 527 1000 box_358 cert_358 = true := by
  have h := List.all_eq_true.mp batch_07_03_ok accepted_358 (by simp [batch_07_03_values])
  exact h
theorem leaf_358_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_358.profileLo box_358.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_358_ok
theorem branch_box_358_nonnegative : ∀ j, 0 ≤ branch_box_358.lower j ∧ 0 ≤ branch_box_358.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_358, Box.profileLo, Box.profileHi, box_358]
theorem leaf_358_BranchSafe : CertificateConsequences.BranchSafe branch_box_358 := by
  left; refine ⟨branch_box_358_nonnegative, ?_⟩
  intro z hz; exact leaf_358_sound hz

theorem leaf_362_ok : checkAt 527 1000 box_362 cert_362 = true := by
  have h := List.all_eq_true.mp batch_07_04_ok accepted_362 (by simp [batch_07_04_values])
  exact h
theorem leaf_362_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_362.profileLo box_362.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_362_ok
theorem branch_box_362_nonnegative : ∀ j, 0 ≤ branch_box_362.lower j ∧ 0 ≤ branch_box_362.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_362, Box.profileLo, Box.profileHi, box_362]
theorem leaf_362_BranchSafe : CertificateConsequences.BranchSafe branch_box_362 := by
  left; refine ⟨branch_box_362_nonnegative, ?_⟩
  intro z hz; exact leaf_362_sound hz

theorem leaf_364_ok : checkAt 527 1000 box_364 cert_364 = true := by
  have h := List.all_eq_true.mp batch_07_05_ok accepted_364 (by simp [batch_07_05_values])
  exact h
theorem leaf_364_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_364.profileLo box_364.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_364_ok
theorem branch_box_364_nonnegative : ∀ j, 0 ≤ branch_box_364.lower j ∧ 0 ≤ branch_box_364.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_364, Box.profileLo, Box.profileHi, box_364]
theorem leaf_364_BranchSafe : CertificateConsequences.BranchSafe branch_box_364 := by
  left; refine ⟨branch_box_364_nonnegative, ?_⟩
  intro z hz; exact leaf_364_sound hz

theorem leaf_365_ok : checkAt 527 1000 box_365 cert_365 = true := by
  have h := List.all_eq_true.mp batch_07_06_ok accepted_365 (by simp [batch_07_06_values])
  exact h
theorem leaf_365_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_365.profileLo box_365.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_365_ok
theorem branch_box_365_nonnegative : ∀ j, 0 ≤ branch_box_365.lower j ∧ 0 ≤ branch_box_365.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_365, Box.profileLo, Box.profileHi, box_365]
theorem leaf_365_BranchSafe : CertificateConsequences.BranchSafe branch_box_365 := by
  left; refine ⟨branch_box_365_nonnegative, ?_⟩
  intro z hz; exact leaf_365_sound hz

theorem leaf_367_ok : checkAt 527 1000 box_367 cert_367 = true := by
  have h := List.all_eq_true.mp batch_07_07_ok accepted_367 (by simp [batch_07_07_values])
  exact h
theorem leaf_367_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_367.profileLo box_367.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_367_ok
theorem branch_box_367_nonnegative : ∀ j, 0 ≤ branch_box_367.lower j ∧ 0 ≤ branch_box_367.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_367, Box.profileLo, Box.profileHi, box_367]
theorem leaf_367_BranchSafe : CertificateConsequences.BranchSafe branch_box_367 := by
  left; refine ⟨branch_box_367_nonnegative, ?_⟩
  intro z hz; exact leaf_367_sound hz

theorem leaf_368_ok : checkAt 527 1000 box_368 cert_368 = true := by
  have h := List.all_eq_true.mp batch_07_08_ok accepted_368 (by simp [batch_07_08_values])
  exact h
theorem leaf_368_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_368.profileLo box_368.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_368_ok
theorem branch_box_368_nonnegative : ∀ j, 0 ≤ branch_box_368.lower j ∧ 0 ≤ branch_box_368.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_368, Box.profileLo, Box.profileHi, box_368]
theorem leaf_368_BranchSafe : CertificateConsequences.BranchSafe branch_box_368 := by
  left; refine ⟨branch_box_368_nonnegative, ?_⟩
  intro z hz; exact leaf_368_sound hz

theorem leaf_370_ok : checkAt 527 1000 box_370 cert_370 = true := by
  have h := List.all_eq_true.mp batch_07_09_ok accepted_370 (by simp [batch_07_09_values])
  exact h
theorem leaf_370_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_370.profileLo box_370.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_370_ok
theorem branch_box_370_nonnegative : ∀ j, 0 ≤ branch_box_370.lower j ∧ 0 ≤ branch_box_370.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_370, Box.profileLo, Box.profileHi, box_370]
theorem leaf_370_BranchSafe : CertificateConsequences.BranchSafe branch_box_370 := by
  left; refine ⟨branch_box_370_nonnegative, ?_⟩
  intro z hz; exact leaf_370_sound hz

theorem leaf_371_ok : checkAt 527 1000 box_371 cert_371 = true := by
  have h := List.all_eq_true.mp batch_07_10_ok accepted_371 (by simp [batch_07_10_values])
  exact h
theorem leaf_371_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_371.profileLo box_371.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_371_ok
theorem branch_box_371_nonnegative : ∀ j, 0 ≤ branch_box_371.lower j ∧ 0 ≤ branch_box_371.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_371, Box.profileLo, Box.profileHi, box_371]
theorem leaf_371_BranchSafe : CertificateConsequences.BranchSafe branch_box_371 := by
  left; refine ⟨branch_box_371_nonnegative, ?_⟩
  intro z hz; exact leaf_371_sound hz

theorem leaf_372_ok : checkAt 527 1000 box_372 cert_372 = true := by
  have h := List.all_eq_true.mp batch_07_11_ok accepted_372 (by simp [batch_07_11_values])
  exact h
theorem leaf_372_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_372.profileLo box_372.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_372_ok
theorem branch_box_372_nonnegative : ∀ j, 0 ≤ branch_box_372.lower j ∧ 0 ≤ branch_box_372.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_372, Box.profileLo, Box.profileHi, box_372]
theorem leaf_372_BranchSafe : CertificateConsequences.BranchSafe branch_box_372 := by
  left; refine ⟨branch_box_372_nonnegative, ?_⟩
  intro z hz; exact leaf_372_sound hz

theorem leaf_377_ok : checkAt 527 1000 box_377 cert_377 = true := by
  have h := List.all_eq_true.mp batch_07_12_ok accepted_377 (by simp [batch_07_12_values])
  exact h
theorem leaf_377_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_377.profileLo box_377.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_377_ok
theorem branch_box_377_nonnegative : ∀ j, 0 ≤ branch_box_377.lower j ∧ 0 ≤ branch_box_377.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_377, Box.profileLo, Box.profileHi, box_377]
theorem leaf_377_BranchSafe : CertificateConsequences.BranchSafe branch_box_377 := by
  left; refine ⟨branch_box_377_nonnegative, ?_⟩
  intro z hz; exact leaf_377_sound hz

theorem leaf_378_ok : checkAt 527 1000 box_378 cert_378 = true := by
  have h := List.all_eq_true.mp batch_07_13_ok accepted_378 (by simp [batch_07_13_values])
  exact h
theorem leaf_378_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_378.profileLo box_378.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_378_ok
theorem branch_box_378_nonnegative : ∀ j, 0 ≤ branch_box_378.lower j ∧ 0 ≤ branch_box_378.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_378, Box.profileLo, Box.profileHi, box_378]
theorem leaf_378_BranchSafe : CertificateConsequences.BranchSafe branch_box_378 := by
  left; refine ⟨branch_box_378_nonnegative, ?_⟩
  intro z hz; exact leaf_378_sound hz

theorem leaf_386_ok : checkAt 527 1000 box_386 cert_386 = true := by
  have h := List.all_eq_true.mp batch_07_14_ok accepted_386 (by simp [batch_07_14_values])
  exact h
theorem leaf_386_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_386.profileLo box_386.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_386_ok
theorem branch_box_386_nonnegative : ∀ j, 0 ≤ branch_box_386.lower j ∧ 0 ≤ branch_box_386.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_386, Box.profileLo, Box.profileHi, box_386]
theorem leaf_386_BranchSafe : CertificateConsequences.BranchSafe branch_box_386 := by
  left; refine ⟨branch_box_386_nonnegative, ?_⟩
  intro z hz; exact leaf_386_sound hz

theorem leaf_387_ok : checkAt 527 1000 box_387 cert_387 = true := by
  have h := List.all_eq_true.mp batch_07_15_ok accepted_387 (by simp [batch_07_15_values])
  exact h
theorem leaf_387_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_387.profileLo box_387.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_387_ok
theorem branch_box_387_nonnegative : ∀ j, 0 ≤ branch_box_387.lower j ∧ 0 ≤ branch_box_387.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_387, Box.profileLo, Box.profileHi, box_387]
theorem leaf_387_BranchSafe : CertificateConsequences.BranchSafe branch_box_387 := by
  left; refine ⟨branch_box_387_nonnegative, ?_⟩
  intro z hz; exact leaf_387_sound hz

theorem leaf_388_ok : checkAt 527 1000 box_388 cert_388 = true := by
  have h := List.all_eq_true.mp batch_07_16_ok accepted_388 (by simp [batch_07_16_values])
  exact h
theorem leaf_388_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_388.profileLo box_388.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_388_ok
theorem branch_box_388_nonnegative : ∀ j, 0 ≤ branch_box_388.lower j ∧ 0 ≤ branch_box_388.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_388, Box.profileLo, Box.profileHi, box_388]
theorem leaf_388_BranchSafe : CertificateConsequences.BranchSafe branch_box_388 := by
  left; refine ⟨branch_box_388_nonnegative, ?_⟩
  intro z hz; exact leaf_388_sound hz

theorem leaf_389_ok : checkAt 527 1000 box_389 cert_389 = true := by
  have h := List.all_eq_true.mp batch_07_17_ok accepted_389 (by simp [batch_07_17_values])
  exact h
theorem leaf_389_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_389.profileLo box_389.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_389_ok
theorem branch_box_389_nonnegative : ∀ j, 0 ≤ branch_box_389.lower j ∧ 0 ≤ branch_box_389.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_389, Box.profileLo, Box.profileHi, box_389]
theorem leaf_389_BranchSafe : CertificateConsequences.BranchSafe branch_box_389 := by
  left; refine ⟨branch_box_389_nonnegative, ?_⟩
  intro z hz; exact leaf_389_sound hz

theorem leaf_391_ok : checkAt 527 1000 box_391 cert_391 = true := by
  have h := List.all_eq_true.mp batch_07_18_ok accepted_391 (by simp [batch_07_18_values])
  exact h
theorem leaf_391_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_391.profileLo box_391.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_391_ok
theorem branch_box_391_nonnegative : ∀ j, 0 ≤ branch_box_391.lower j ∧ 0 ≤ branch_box_391.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_391, Box.profileLo, Box.profileHi, box_391]
theorem leaf_391_BranchSafe : CertificateConsequences.BranchSafe branch_box_391 := by
  left; refine ⟨branch_box_391_nonnegative, ?_⟩
  intro z hz; exact leaf_391_sound hz

theorem leaf_392_ok : checkAt 527 1000 box_392 cert_392 = true := by
  have h := List.all_eq_true.mp batch_07_19_ok accepted_392 (by simp [batch_07_19_values])
  exact h
theorem leaf_392_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_392.profileLo box_392.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_392_ok
theorem branch_box_392_nonnegative : ∀ j, 0 ≤ branch_box_392.lower j ∧ 0 ≤ branch_box_392.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_392, Box.profileLo, Box.profileHi, box_392]
theorem leaf_392_BranchSafe : CertificateConsequences.BranchSafe branch_box_392 := by
  left; refine ⟨branch_box_392_nonnegative, ?_⟩
  intro z hz; exact leaf_392_sound hz

theorem leaf_393_ok : checkAt 527 1000 box_393 cert_393 = true := by
  have h := List.all_eq_true.mp batch_07_20_ok accepted_393 (by simp [batch_07_20_values])
  exact h
theorem leaf_393_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_393.profileLo box_393.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_393_ok
theorem branch_box_393_nonnegative : ∀ j, 0 ≤ branch_box_393.lower j ∧ 0 ≤ branch_box_393.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_393, Box.profileLo, Box.profileHi, box_393]
theorem leaf_393_BranchSafe : CertificateConsequences.BranchSafe branch_box_393 := by
  left; refine ⟨branch_box_393_nonnegative, ?_⟩
  intro z hz; exact leaf_393_sound hz

theorem leaf_395_ok : checkAt 527 1000 box_395 cert_395 = true := by
  have h := List.all_eq_true.mp batch_07_21_ok accepted_395 (by simp [batch_07_21_values])
  exact h
theorem leaf_395_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_395.profileLo box_395.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_395_ok
theorem branch_box_395_nonnegative : ∀ j, 0 ≤ branch_box_395.lower j ∧ 0 ≤ branch_box_395.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_395, Box.profileLo, Box.profileHi, box_395]
theorem leaf_395_BranchSafe : CertificateConsequences.BranchSafe branch_box_395 := by
  left; refine ⟨branch_box_395_nonnegative, ?_⟩
  intro z hz; exact leaf_395_sound hz

theorem leaf_396_ok : checkAt 527 1000 box_396 cert_396 = true := by
  have h := List.all_eq_true.mp batch_07_22_ok accepted_396 (by simp [batch_07_22_values])
  exact h
theorem leaf_396_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_396.profileLo box_396.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_396_ok
theorem branch_box_396_nonnegative : ∀ j, 0 ≤ branch_box_396.lower j ∧ 0 ≤ branch_box_396.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_396, Box.profileLo, Box.profileHi, box_396]
theorem leaf_396_BranchSafe : CertificateConsequences.BranchSafe branch_box_396 := by
  left; refine ⟨branch_box_396_nonnegative, ?_⟩
  intro z hz; exact leaf_396_sound hz

theorem leaf_399_ok : checkAt 527 1000 box_399 cert_399 = true := by
  have h := List.all_eq_true.mp batch_07_23_ok accepted_399 (by simp [batch_07_23_values])
  exact h
theorem leaf_399_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_399.profileLo box_399.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_399_ok
theorem branch_box_399_nonnegative : ∀ j, 0 ≤ branch_box_399.lower j ∧ 0 ≤ branch_box_399.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_399, Box.profileLo, Box.profileHi, box_399]
theorem leaf_399_BranchSafe : CertificateConsequences.BranchSafe branch_box_399 := by
  left; refine ⟨branch_box_399_nonnegative, ?_⟩
  intro z hz; exact leaf_399_sound hz

#print axioms batch_07_00_ok
#print axioms leaf_350_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
