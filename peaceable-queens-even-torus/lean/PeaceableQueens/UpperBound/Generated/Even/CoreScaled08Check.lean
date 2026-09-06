import PeaceableQueens.UpperBound.Generated.Even.CoreScaled08Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_08_00_values : List Bool := [accepted_401]
theorem batch_08_00_ok : batch_08_00_values.all id = true := by decide

def batch_08_01_values : List Bool := [accepted_403]
theorem batch_08_01_ok : batch_08_01_values.all id = true := by decide

def batch_08_02_values : List Bool := [accepted_405]
theorem batch_08_02_ok : batch_08_02_values.all id = true := by decide

def batch_08_03_values : List Bool := [accepted_408]
theorem batch_08_03_ok : batch_08_03_values.all id = true := by decide

def batch_08_04_values : List Bool := [accepted_409]
theorem batch_08_04_ok : batch_08_04_values.all id = true := by decide

def batch_08_05_values : List Bool := [accepted_411]
theorem batch_08_05_ok : batch_08_05_values.all id = true := by decide

def batch_08_06_values : List Bool := [accepted_420]
theorem batch_08_06_ok : batch_08_06_values.all id = true := by decide

def batch_08_07_values : List Bool := [accepted_424]
theorem batch_08_07_ok : batch_08_07_values.all id = true := by decide

def batch_08_08_values : List Bool := [accepted_428]
theorem batch_08_08_ok : batch_08_08_values.all id = true := by decide

def batch_08_09_values : List Bool := [accepted_431]
theorem batch_08_09_ok : batch_08_09_values.all id = true := by decide

def batch_08_10_values : List Bool := [accepted_436]
theorem batch_08_10_ok : batch_08_10_values.all id = true := by decide

def batch_08_11_values : List Bool := [accepted_437]
theorem batch_08_11_ok : batch_08_11_values.all id = true := by decide

def batch_08_12_values : List Bool := [accepted_440]
theorem batch_08_12_ok : batch_08_12_values.all id = true := by decide

def batch_08_13_values : List Bool := [accepted_441]
theorem batch_08_13_ok : batch_08_13_values.all id = true := by decide

theorem leaf_401_ok : checkAt 527 1000 box_401 cert_401 = true := by
  have h := List.all_eq_true.mp batch_08_00_ok accepted_401 (by simp [batch_08_00_values])
  exact h
theorem leaf_401_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_401.profileLo box_401.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_401_ok
theorem branch_box_401_nonnegative : ∀ j, 0 ≤ branch_box_401.lower j ∧ 0 ≤ branch_box_401.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_401, Box.profileLo, Box.profileHi, box_401]
theorem leaf_401_BranchSafe : CertificateConsequences.BranchSafe branch_box_401 := by
  left; refine ⟨branch_box_401_nonnegative, ?_⟩
  intro z hz; exact leaf_401_sound hz

theorem leaf_403_ok : checkAt 527 1000 box_403 cert_403 = true := by
  have h := List.all_eq_true.mp batch_08_01_ok accepted_403 (by simp [batch_08_01_values])
  exact h
theorem leaf_403_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_403.profileLo box_403.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_403_ok
theorem branch_box_403_nonnegative : ∀ j, 0 ≤ branch_box_403.lower j ∧ 0 ≤ branch_box_403.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_403, Box.profileLo, Box.profileHi, box_403]
theorem leaf_403_BranchSafe : CertificateConsequences.BranchSafe branch_box_403 := by
  left; refine ⟨branch_box_403_nonnegative, ?_⟩
  intro z hz; exact leaf_403_sound hz

theorem leaf_405_ok : checkAt 527 1000 box_405 cert_405 = true := by
  have h := List.all_eq_true.mp batch_08_02_ok accepted_405 (by simp [batch_08_02_values])
  exact h
theorem leaf_405_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_405.profileLo box_405.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_405_ok
theorem branch_box_405_nonnegative : ∀ j, 0 ≤ branch_box_405.lower j ∧ 0 ≤ branch_box_405.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_405, Box.profileLo, Box.profileHi, box_405]
theorem leaf_405_BranchSafe : CertificateConsequences.BranchSafe branch_box_405 := by
  left; refine ⟨branch_box_405_nonnegative, ?_⟩
  intro z hz; exact leaf_405_sound hz

theorem leaf_408_ok : checkAt 527 1000 box_408 cert_408 = true := by
  have h := List.all_eq_true.mp batch_08_03_ok accepted_408 (by simp [batch_08_03_values])
  exact h
theorem leaf_408_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_408.profileLo box_408.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_408_ok
theorem branch_box_408_nonnegative : ∀ j, 0 ≤ branch_box_408.lower j ∧ 0 ≤ branch_box_408.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_408, Box.profileLo, Box.profileHi, box_408]
theorem leaf_408_BranchSafe : CertificateConsequences.BranchSafe branch_box_408 := by
  left; refine ⟨branch_box_408_nonnegative, ?_⟩
  intro z hz; exact leaf_408_sound hz

theorem leaf_409_ok : checkAt 527 1000 box_409 cert_409 = true := by
  have h := List.all_eq_true.mp batch_08_04_ok accepted_409 (by simp [batch_08_04_values])
  exact h
theorem leaf_409_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_409.profileLo box_409.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_409_ok
theorem branch_box_409_nonnegative : ∀ j, 0 ≤ branch_box_409.lower j ∧ 0 ≤ branch_box_409.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_409, Box.profileLo, Box.profileHi, box_409]
theorem leaf_409_BranchSafe : CertificateConsequences.BranchSafe branch_box_409 := by
  left; refine ⟨branch_box_409_nonnegative, ?_⟩
  intro z hz; exact leaf_409_sound hz

theorem leaf_411_ok : checkAt 527 1000 box_411 cert_411 = true := by
  have h := List.all_eq_true.mp batch_08_05_ok accepted_411 (by simp [batch_08_05_values])
  exact h
theorem leaf_411_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_411.profileLo box_411.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_411_ok
theorem branch_box_411_nonnegative : ∀ j, 0 ≤ branch_box_411.lower j ∧ 0 ≤ branch_box_411.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_411, Box.profileLo, Box.profileHi, box_411]
theorem leaf_411_BranchSafe : CertificateConsequences.BranchSafe branch_box_411 := by
  left; refine ⟨branch_box_411_nonnegative, ?_⟩
  intro z hz; exact leaf_411_sound hz

theorem leaf_420_ok : checkAt 527 1000 box_420 cert_420 = true := by
  have h := List.all_eq_true.mp batch_08_06_ok accepted_420 (by simp [batch_08_06_values])
  exact h
theorem leaf_420_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_420.profileLo box_420.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_420_ok
theorem branch_box_420_nonnegative : ∀ j, 0 ≤ branch_box_420.lower j ∧ 0 ≤ branch_box_420.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_420, Box.profileLo, Box.profileHi, box_420]
theorem leaf_420_BranchSafe : CertificateConsequences.BranchSafe branch_box_420 := by
  left; refine ⟨branch_box_420_nonnegative, ?_⟩
  intro z hz; exact leaf_420_sound hz

theorem leaf_424_ok : checkAt 527 1000 box_424 cert_424 = true := by
  have h := List.all_eq_true.mp batch_08_07_ok accepted_424 (by simp [batch_08_07_values])
  exact h
theorem leaf_424_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_424.profileLo box_424.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_424_ok
theorem branch_box_424_nonnegative : ∀ j, 0 ≤ branch_box_424.lower j ∧ 0 ≤ branch_box_424.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_424, Box.profileLo, Box.profileHi, box_424]
theorem leaf_424_BranchSafe : CertificateConsequences.BranchSafe branch_box_424 := by
  left; refine ⟨branch_box_424_nonnegative, ?_⟩
  intro z hz; exact leaf_424_sound hz

theorem leaf_428_ok : checkAt 527 1000 box_428 cert_428 = true := by
  have h := List.all_eq_true.mp batch_08_08_ok accepted_428 (by simp [batch_08_08_values])
  exact h
theorem leaf_428_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_428.profileLo box_428.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_428_ok
theorem branch_box_428_nonnegative : ∀ j, 0 ≤ branch_box_428.lower j ∧ 0 ≤ branch_box_428.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_428, Box.profileLo, Box.profileHi, box_428]
theorem leaf_428_BranchSafe : CertificateConsequences.BranchSafe branch_box_428 := by
  left; refine ⟨branch_box_428_nonnegative, ?_⟩
  intro z hz; exact leaf_428_sound hz

theorem leaf_431_ok : checkAt 527 1000 box_431 cert_431 = true := by
  have h := List.all_eq_true.mp batch_08_09_ok accepted_431 (by simp [batch_08_09_values])
  exact h
theorem leaf_431_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_431.profileLo box_431.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_431_ok
theorem branch_box_431_nonnegative : ∀ j, 0 ≤ branch_box_431.lower j ∧ 0 ≤ branch_box_431.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_431, Box.profileLo, Box.profileHi, box_431]
theorem leaf_431_BranchSafe : CertificateConsequences.BranchSafe branch_box_431 := by
  left; refine ⟨branch_box_431_nonnegative, ?_⟩
  intro z hz; exact leaf_431_sound hz

theorem leaf_436_ok : checkAt 527 1000 box_436 cert_436 = true := by
  have h := List.all_eq_true.mp batch_08_10_ok accepted_436 (by simp [batch_08_10_values])
  exact h
theorem leaf_436_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_436.profileLo box_436.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_436_ok
theorem branch_box_436_nonnegative : ∀ j, 0 ≤ branch_box_436.lower j ∧ 0 ≤ branch_box_436.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_436, Box.profileLo, Box.profileHi, box_436]
theorem leaf_436_BranchSafe : CertificateConsequences.BranchSafe branch_box_436 := by
  left; refine ⟨branch_box_436_nonnegative, ?_⟩
  intro z hz; exact leaf_436_sound hz

theorem leaf_437_ok : checkAt 527 1000 box_437 cert_437 = true := by
  have h := List.all_eq_true.mp batch_08_11_ok accepted_437 (by simp [batch_08_11_values])
  exact h
theorem leaf_437_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_437.profileLo box_437.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_437_ok
theorem branch_box_437_nonnegative : ∀ j, 0 ≤ branch_box_437.lower j ∧ 0 ≤ branch_box_437.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_437, Box.profileLo, Box.profileHi, box_437]
theorem leaf_437_BranchSafe : CertificateConsequences.BranchSafe branch_box_437 := by
  left; refine ⟨branch_box_437_nonnegative, ?_⟩
  intro z hz; exact leaf_437_sound hz

theorem leaf_440_ok : checkAt 527 1000 box_440 cert_440 = true := by
  have h := List.all_eq_true.mp batch_08_12_ok accepted_440 (by simp [batch_08_12_values])
  exact h
theorem leaf_440_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_440.profileLo box_440.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_440_ok
theorem branch_box_440_nonnegative : ∀ j, 0 ≤ branch_box_440.lower j ∧ 0 ≤ branch_box_440.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_440, Box.profileLo, Box.profileHi, box_440]
theorem leaf_440_BranchSafe : CertificateConsequences.BranchSafe branch_box_440 := by
  left; refine ⟨branch_box_440_nonnegative, ?_⟩
  intro z hz; exact leaf_440_sound hz

theorem leaf_441_ok : checkAt 527 1000 box_441 cert_441 = true := by
  have h := List.all_eq_true.mp batch_08_13_ok accepted_441 (by simp [batch_08_13_values])
  exact h
theorem leaf_441_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_441.profileLo box_441.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_441_ok
theorem branch_box_441_nonnegative : ∀ j, 0 ≤ branch_box_441.lower j ∧ 0 ≤ branch_box_441.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_441, Box.profileLo, Box.profileHi, box_441]
theorem leaf_441_BranchSafe : CertificateConsequences.BranchSafe branch_box_441 := by
  left; refine ⟨branch_box_441_nonnegative, ?_⟩
  intro z hz; exact leaf_441_sound hz

#print axioms batch_08_00_ok
#print axioms leaf_401_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
