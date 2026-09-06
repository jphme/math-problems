import PeaceableQueens.UpperBound.Generated.Even.CoreScaled07Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_07_00_values : List Bool := [accepted_352]
theorem batch_07_00_ok : batch_07_00_values.all id = true := by decide

def batch_07_01_values : List Bool := [accepted_353]
theorem batch_07_01_ok : batch_07_01_values.all id = true := by decide

def batch_07_02_values : List Bool := [accepted_355]
theorem batch_07_02_ok : batch_07_02_values.all id = true := by decide

def batch_07_03_values : List Bool := [accepted_357]
theorem batch_07_03_ok : batch_07_03_values.all id = true := by decide

def batch_07_04_values : List Bool := [accepted_360]
theorem batch_07_04_ok : batch_07_04_values.all id = true := by decide

def batch_07_05_values : List Bool := [accepted_361]
theorem batch_07_05_ok : batch_07_05_values.all id = true := by decide

def batch_07_06_values : List Bool := [accepted_363]
theorem batch_07_06_ok : batch_07_06_values.all id = true := by decide

def batch_07_07_values : List Bool := [accepted_365]
theorem batch_07_07_ok : batch_07_07_values.all id = true := by decide

def batch_07_08_values : List Bool := [accepted_376]
theorem batch_07_08_ok : batch_07_08_values.all id = true := by decide

def batch_07_09_values : List Bool := [accepted_378]
theorem batch_07_09_ok : batch_07_09_values.all id = true := by decide

def batch_07_10_values : List Bool := [accepted_380]
theorem batch_07_10_ok : batch_07_10_values.all id = true := by decide

def batch_07_11_values : List Bool := [accepted_382]
theorem batch_07_11_ok : batch_07_11_values.all id = true := by decide

def batch_07_12_values : List Bool := [accepted_388]
theorem batch_07_12_ok : batch_07_12_values.all id = true := by decide

def batch_07_13_values : List Bool := [accepted_390]
theorem batch_07_13_ok : batch_07_13_values.all id = true := by decide

def batch_07_14_values : List Bool := [accepted_392]
theorem batch_07_14_ok : batch_07_14_values.all id = true := by decide

def batch_07_15_values : List Bool := [accepted_398]
theorem batch_07_15_ok : batch_07_15_values.all id = true := by decide

def batch_07_16_values : List Bool := [accepted_399]
theorem batch_07_16_ok : batch_07_16_values.all id = true := by decide

theorem leaf_352_ok : checkAt 527 1000 box_352 cert_352 = true := by
  have h := List.all_eq_true.mp batch_07_00_ok accepted_352 (by simp [batch_07_00_values])
  exact h
theorem leaf_352_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_352.profileLo box_352.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_352_ok
theorem branch_box_352_nonnegative : ∀ j, 0 ≤ branch_box_352.lower j ∧ 0 ≤ branch_box_352.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_352, Box.profileLo, Box.profileHi, box_352]
theorem leaf_352_BranchSafe : CertificateConsequences.BranchSafe branch_box_352 := by
  left; refine ⟨branch_box_352_nonnegative, ?_⟩
  intro z hz; exact leaf_352_sound hz

theorem leaf_353_ok : checkAt 527 1000 box_353 cert_353 = true := by
  have h := List.all_eq_true.mp batch_07_01_ok accepted_353 (by simp [batch_07_01_values])
  exact h
theorem leaf_353_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_353.profileLo box_353.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_353_ok
theorem branch_box_353_nonnegative : ∀ j, 0 ≤ branch_box_353.lower j ∧ 0 ≤ branch_box_353.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_353, Box.profileLo, Box.profileHi, box_353]
theorem leaf_353_BranchSafe : CertificateConsequences.BranchSafe branch_box_353 := by
  left; refine ⟨branch_box_353_nonnegative, ?_⟩
  intro z hz; exact leaf_353_sound hz

theorem leaf_355_ok : checkAt 527 1000 box_355 cert_355 = true := by
  have h := List.all_eq_true.mp batch_07_02_ok accepted_355 (by simp [batch_07_02_values])
  exact h
theorem leaf_355_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_355.profileLo box_355.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_355_ok
theorem branch_box_355_nonnegative : ∀ j, 0 ≤ branch_box_355.lower j ∧ 0 ≤ branch_box_355.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_355, Box.profileLo, Box.profileHi, box_355]
theorem leaf_355_BranchSafe : CertificateConsequences.BranchSafe branch_box_355 := by
  left; refine ⟨branch_box_355_nonnegative, ?_⟩
  intro z hz; exact leaf_355_sound hz

theorem leaf_357_ok : checkAt 527 1000 box_357 cert_357 = true := by
  have h := List.all_eq_true.mp batch_07_03_ok accepted_357 (by simp [batch_07_03_values])
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

theorem leaf_360_ok : checkAt 527 1000 box_360 cert_360 = true := by
  have h := List.all_eq_true.mp batch_07_04_ok accepted_360 (by simp [batch_07_04_values])
  exact h
theorem leaf_360_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_360.profileLo box_360.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_360_ok
theorem branch_box_360_nonnegative : ∀ j, 0 ≤ branch_box_360.lower j ∧ 0 ≤ branch_box_360.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_360, Box.profileLo, Box.profileHi, box_360]
theorem leaf_360_BranchSafe : CertificateConsequences.BranchSafe branch_box_360 := by
  left; refine ⟨branch_box_360_nonnegative, ?_⟩
  intro z hz; exact leaf_360_sound hz

theorem leaf_361_ok : checkAt 527 1000 box_361 cert_361 = true := by
  have h := List.all_eq_true.mp batch_07_05_ok accepted_361 (by simp [batch_07_05_values])
  exact h
theorem leaf_361_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_361.profileLo box_361.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_361_ok
theorem branch_box_361_nonnegative : ∀ j, 0 ≤ branch_box_361.lower j ∧ 0 ≤ branch_box_361.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_361, Box.profileLo, Box.profileHi, box_361]
theorem leaf_361_BranchSafe : CertificateConsequences.BranchSafe branch_box_361 := by
  left; refine ⟨branch_box_361_nonnegative, ?_⟩
  intro z hz; exact leaf_361_sound hz

theorem leaf_363_ok : checkAt 527 1000 box_363 cert_363 = true := by
  have h := List.all_eq_true.mp batch_07_06_ok accepted_363 (by simp [batch_07_06_values])
  exact h
theorem leaf_363_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_363.profileLo box_363.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_363_ok
theorem branch_box_363_nonnegative : ∀ j, 0 ≤ branch_box_363.lower j ∧ 0 ≤ branch_box_363.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_363, Box.profileLo, Box.profileHi, box_363]
theorem leaf_363_BranchSafe : CertificateConsequences.BranchSafe branch_box_363 := by
  left; refine ⟨branch_box_363_nonnegative, ?_⟩
  intro z hz; exact leaf_363_sound hz

theorem leaf_365_ok : checkAt 527 1000 box_365 cert_365 = true := by
  have h := List.all_eq_true.mp batch_07_07_ok accepted_365 (by simp [batch_07_07_values])
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

theorem leaf_376_ok : checkAt 527 1000 box_376 cert_376 = true := by
  have h := List.all_eq_true.mp batch_07_08_ok accepted_376 (by simp [batch_07_08_values])
  exact h
theorem leaf_376_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_376.profileLo box_376.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_376_ok
theorem branch_box_376_nonnegative : ∀ j, 0 ≤ branch_box_376.lower j ∧ 0 ≤ branch_box_376.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_376, Box.profileLo, Box.profileHi, box_376]
theorem leaf_376_BranchSafe : CertificateConsequences.BranchSafe branch_box_376 := by
  left; refine ⟨branch_box_376_nonnegative, ?_⟩
  intro z hz; exact leaf_376_sound hz

theorem leaf_378_ok : checkAt 527 1000 box_378 cert_378 = true := by
  have h := List.all_eq_true.mp batch_07_09_ok accepted_378 (by simp [batch_07_09_values])
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

theorem leaf_380_ok : checkAt 527 1000 box_380 cert_380 = true := by
  have h := List.all_eq_true.mp batch_07_10_ok accepted_380 (by simp [batch_07_10_values])
  exact h
theorem leaf_380_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_380.profileLo box_380.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_380_ok
theorem branch_box_380_nonnegative : ∀ j, 0 ≤ branch_box_380.lower j ∧ 0 ≤ branch_box_380.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_380, Box.profileLo, Box.profileHi, box_380]
theorem leaf_380_BranchSafe : CertificateConsequences.BranchSafe branch_box_380 := by
  left; refine ⟨branch_box_380_nonnegative, ?_⟩
  intro z hz; exact leaf_380_sound hz

theorem leaf_382_ok : checkAt 527 1000 box_382 cert_382 = true := by
  have h := List.all_eq_true.mp batch_07_11_ok accepted_382 (by simp [batch_07_11_values])
  exact h
theorem leaf_382_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_382.profileLo box_382.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_382_ok
theorem branch_box_382_nonnegative : ∀ j, 0 ≤ branch_box_382.lower j ∧ 0 ≤ branch_box_382.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_382, Box.profileLo, Box.profileHi, box_382]
theorem leaf_382_BranchSafe : CertificateConsequences.BranchSafe branch_box_382 := by
  left; refine ⟨branch_box_382_nonnegative, ?_⟩
  intro z hz; exact leaf_382_sound hz

theorem leaf_388_ok : checkAt 527 1000 box_388 cert_388 = true := by
  have h := List.all_eq_true.mp batch_07_12_ok accepted_388 (by simp [batch_07_12_values])
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

theorem leaf_390_ok : checkAt 527 1000 box_390 cert_390 = true := by
  have h := List.all_eq_true.mp batch_07_13_ok accepted_390 (by simp [batch_07_13_values])
  exact h
theorem leaf_390_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_390.profileLo box_390.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_390_ok
theorem branch_box_390_nonnegative : ∀ j, 0 ≤ branch_box_390.lower j ∧ 0 ≤ branch_box_390.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_390, Box.profileLo, Box.profileHi, box_390]
theorem leaf_390_BranchSafe : CertificateConsequences.BranchSafe branch_box_390 := by
  left; refine ⟨branch_box_390_nonnegative, ?_⟩
  intro z hz; exact leaf_390_sound hz

theorem leaf_392_ok : checkAt 527 1000 box_392 cert_392 = true := by
  have h := List.all_eq_true.mp batch_07_14_ok accepted_392 (by simp [batch_07_14_values])
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

theorem leaf_398_ok : checkAt 527 1000 box_398 cert_398 = true := by
  have h := List.all_eq_true.mp batch_07_15_ok accepted_398 (by simp [batch_07_15_values])
  exact h
theorem leaf_398_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_398.profileLo box_398.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_398_ok
theorem branch_box_398_nonnegative : ∀ j, 0 ≤ branch_box_398.lower j ∧ 0 ≤ branch_box_398.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_398, Box.profileLo, Box.profileHi, box_398]
theorem leaf_398_BranchSafe : CertificateConsequences.BranchSafe branch_box_398 := by
  left; refine ⟨branch_box_398_nonnegative, ?_⟩
  intro z hz; exact leaf_398_sound hz

theorem leaf_399_ok : checkAt 527 1000 box_399 cert_399 = true := by
  have h := List.all_eq_true.mp batch_07_16_ok accepted_399 (by simp [batch_07_16_values])
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
#print axioms leaf_352_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
