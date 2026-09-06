import PeaceableQueens.UpperBound.Generated.Even.CoreScaled67Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_67_00_values : List Bool := [accepted_3350]
theorem batch_67_00_ok : batch_67_00_values.all id = true := by decide

def batch_67_01_values : List Bool := [accepted_3352]
theorem batch_67_01_ok : batch_67_01_values.all id = true := by decide

def batch_67_02_values : List Bool := [accepted_3354]
theorem batch_67_02_ok : batch_67_02_values.all id = true := by decide

def batch_67_03_values : List Bool := [accepted_3355]
theorem batch_67_03_ok : batch_67_03_values.all id = true := by decide

def batch_67_04_values : List Bool := [accepted_3362]
theorem batch_67_04_ok : batch_67_04_values.all id = true := by decide

def batch_67_05_values : List Bool := [accepted_3364]
theorem batch_67_05_ok : batch_67_05_values.all id = true := by decide

def batch_67_06_values : List Bool := [accepted_3366]
theorem batch_67_06_ok : batch_67_06_values.all id = true := by decide

def batch_67_07_values : List Bool := [accepted_3368]
theorem batch_67_07_ok : batch_67_07_values.all id = true := by decide

def batch_67_08_values : List Bool := [accepted_3370]
theorem batch_67_08_ok : batch_67_08_values.all id = true := by decide

def batch_67_09_values : List Bool := [accepted_3372]
theorem batch_67_09_ok : batch_67_09_values.all id = true := by decide

def batch_67_10_values : List Bool := [accepted_3374]
theorem batch_67_10_ok : batch_67_10_values.all id = true := by decide

def batch_67_11_values : List Bool := [accepted_3376]
theorem batch_67_11_ok : batch_67_11_values.all id = true := by decide

def batch_67_12_values : List Bool := [accepted_3386]
theorem batch_67_12_ok : batch_67_12_values.all id = true := by decide

def batch_67_13_values : List Bool := [accepted_3388]
theorem batch_67_13_ok : batch_67_13_values.all id = true := by decide

def batch_67_14_values : List Bool := [accepted_3389]
theorem batch_67_14_ok : batch_67_14_values.all id = true := by decide

def batch_67_15_values : List Bool := [accepted_3391]
theorem batch_67_15_ok : batch_67_15_values.all id = true := by decide

def batch_67_16_values : List Bool := [accepted_3395]
theorem batch_67_16_ok : batch_67_16_values.all id = true := by decide

theorem leaf_3350_ok : checkAt 527 1000 box_3350 cert_3350 = true := by
  have h := List.all_eq_true.mp batch_67_00_ok accepted_3350 (by simp [batch_67_00_values])
  exact h
theorem leaf_3350_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3350.profileLo box_3350.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3350_ok
theorem branch_box_3350_nonnegative : ∀ j, 0 ≤ branch_box_3350.lower j ∧ 0 ≤ branch_box_3350.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3350, Box.profileLo, Box.profileHi, box_3350]
theorem leaf_3350_BranchSafe : CertificateConsequences.BranchSafe branch_box_3350 := by
  left; refine ⟨branch_box_3350_nonnegative, ?_⟩
  intro z hz; exact leaf_3350_sound hz

theorem leaf_3352_ok : checkAt 527 1000 box_3352 cert_3352 = true := by
  have h := List.all_eq_true.mp batch_67_01_ok accepted_3352 (by simp [batch_67_01_values])
  exact h
theorem leaf_3352_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3352.profileLo box_3352.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3352_ok
theorem branch_box_3352_nonnegative : ∀ j, 0 ≤ branch_box_3352.lower j ∧ 0 ≤ branch_box_3352.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3352, Box.profileLo, Box.profileHi, box_3352]
theorem leaf_3352_BranchSafe : CertificateConsequences.BranchSafe branch_box_3352 := by
  left; refine ⟨branch_box_3352_nonnegative, ?_⟩
  intro z hz; exact leaf_3352_sound hz

theorem leaf_3354_ok : checkAt 527 1000 box_3354 cert_3354 = true := by
  have h := List.all_eq_true.mp batch_67_02_ok accepted_3354 (by simp [batch_67_02_values])
  exact h
theorem leaf_3354_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3354.profileLo box_3354.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3354_ok
theorem branch_box_3354_nonnegative : ∀ j, 0 ≤ branch_box_3354.lower j ∧ 0 ≤ branch_box_3354.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3354, Box.profileLo, Box.profileHi, box_3354]
theorem leaf_3354_BranchSafe : CertificateConsequences.BranchSafe branch_box_3354 := by
  left; refine ⟨branch_box_3354_nonnegative, ?_⟩
  intro z hz; exact leaf_3354_sound hz

theorem leaf_3355_ok : checkAt 527 1000 box_3355 cert_3355 = true := by
  have h := List.all_eq_true.mp batch_67_03_ok accepted_3355 (by simp [batch_67_03_values])
  exact h
theorem leaf_3355_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3355.profileLo box_3355.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3355_ok
theorem branch_box_3355_nonnegative : ∀ j, 0 ≤ branch_box_3355.lower j ∧ 0 ≤ branch_box_3355.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3355, Box.profileLo, Box.profileHi, box_3355]
theorem leaf_3355_BranchSafe : CertificateConsequences.BranchSafe branch_box_3355 := by
  left; refine ⟨branch_box_3355_nonnegative, ?_⟩
  intro z hz; exact leaf_3355_sound hz

theorem leaf_3362_ok : checkAt 527 1000 box_3362 cert_3362 = true := by
  have h := List.all_eq_true.mp batch_67_04_ok accepted_3362 (by simp [batch_67_04_values])
  exact h
theorem leaf_3362_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3362.profileLo box_3362.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3362_ok
theorem branch_box_3362_nonnegative : ∀ j, 0 ≤ branch_box_3362.lower j ∧ 0 ≤ branch_box_3362.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3362, Box.profileLo, Box.profileHi, box_3362]
theorem leaf_3362_BranchSafe : CertificateConsequences.BranchSafe branch_box_3362 := by
  left; refine ⟨branch_box_3362_nonnegative, ?_⟩
  intro z hz; exact leaf_3362_sound hz

theorem leaf_3364_ok : checkAt 527 1000 box_3364 cert_3364 = true := by
  have h := List.all_eq_true.mp batch_67_05_ok accepted_3364 (by simp [batch_67_05_values])
  exact h
theorem leaf_3364_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3364.profileLo box_3364.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3364_ok
theorem branch_box_3364_nonnegative : ∀ j, 0 ≤ branch_box_3364.lower j ∧ 0 ≤ branch_box_3364.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3364, Box.profileLo, Box.profileHi, box_3364]
theorem leaf_3364_BranchSafe : CertificateConsequences.BranchSafe branch_box_3364 := by
  left; refine ⟨branch_box_3364_nonnegative, ?_⟩
  intro z hz; exact leaf_3364_sound hz

theorem leaf_3366_ok : checkAt 527 1000 box_3366 cert_3366 = true := by
  have h := List.all_eq_true.mp batch_67_06_ok accepted_3366 (by simp [batch_67_06_values])
  exact h
theorem leaf_3366_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3366.profileLo box_3366.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3366_ok
theorem branch_box_3366_nonnegative : ∀ j, 0 ≤ branch_box_3366.lower j ∧ 0 ≤ branch_box_3366.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3366, Box.profileLo, Box.profileHi, box_3366]
theorem leaf_3366_BranchSafe : CertificateConsequences.BranchSafe branch_box_3366 := by
  left; refine ⟨branch_box_3366_nonnegative, ?_⟩
  intro z hz; exact leaf_3366_sound hz

theorem leaf_3368_ok : checkAt 527 1000 box_3368 cert_3368 = true := by
  have h := List.all_eq_true.mp batch_67_07_ok accepted_3368 (by simp [batch_67_07_values])
  exact h
theorem leaf_3368_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3368.profileLo box_3368.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3368_ok
theorem branch_box_3368_nonnegative : ∀ j, 0 ≤ branch_box_3368.lower j ∧ 0 ≤ branch_box_3368.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3368, Box.profileLo, Box.profileHi, box_3368]
theorem leaf_3368_BranchSafe : CertificateConsequences.BranchSafe branch_box_3368 := by
  left; refine ⟨branch_box_3368_nonnegative, ?_⟩
  intro z hz; exact leaf_3368_sound hz

theorem leaf_3370_ok : checkAt 527 1000 box_3370 cert_3370 = true := by
  have h := List.all_eq_true.mp batch_67_08_ok accepted_3370 (by simp [batch_67_08_values])
  exact h
theorem leaf_3370_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3370.profileLo box_3370.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3370_ok
theorem branch_box_3370_nonnegative : ∀ j, 0 ≤ branch_box_3370.lower j ∧ 0 ≤ branch_box_3370.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3370, Box.profileLo, Box.profileHi, box_3370]
theorem leaf_3370_BranchSafe : CertificateConsequences.BranchSafe branch_box_3370 := by
  left; refine ⟨branch_box_3370_nonnegative, ?_⟩
  intro z hz; exact leaf_3370_sound hz

theorem leaf_3372_ok : checkAt 527 1000 box_3372 cert_3372 = true := by
  have h := List.all_eq_true.mp batch_67_09_ok accepted_3372 (by simp [batch_67_09_values])
  exact h
theorem leaf_3372_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3372.profileLo box_3372.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3372_ok
theorem branch_box_3372_nonnegative : ∀ j, 0 ≤ branch_box_3372.lower j ∧ 0 ≤ branch_box_3372.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3372, Box.profileLo, Box.profileHi, box_3372]
theorem leaf_3372_BranchSafe : CertificateConsequences.BranchSafe branch_box_3372 := by
  left; refine ⟨branch_box_3372_nonnegative, ?_⟩
  intro z hz; exact leaf_3372_sound hz

theorem leaf_3374_ok : checkAt 527 1000 box_3374 cert_3374 = true := by
  have h := List.all_eq_true.mp batch_67_10_ok accepted_3374 (by simp [batch_67_10_values])
  exact h
theorem leaf_3374_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3374.profileLo box_3374.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3374_ok
theorem branch_box_3374_nonnegative : ∀ j, 0 ≤ branch_box_3374.lower j ∧ 0 ≤ branch_box_3374.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3374, Box.profileLo, Box.profileHi, box_3374]
theorem leaf_3374_BranchSafe : CertificateConsequences.BranchSafe branch_box_3374 := by
  left; refine ⟨branch_box_3374_nonnegative, ?_⟩
  intro z hz; exact leaf_3374_sound hz

theorem leaf_3376_ok : checkAt 527 1000 box_3376 cert_3376 = true := by
  have h := List.all_eq_true.mp batch_67_11_ok accepted_3376 (by simp [batch_67_11_values])
  exact h
theorem leaf_3376_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3376.profileLo box_3376.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3376_ok
theorem branch_box_3376_nonnegative : ∀ j, 0 ≤ branch_box_3376.lower j ∧ 0 ≤ branch_box_3376.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3376, Box.profileLo, Box.profileHi, box_3376]
theorem leaf_3376_BranchSafe : CertificateConsequences.BranchSafe branch_box_3376 := by
  left; refine ⟨branch_box_3376_nonnegative, ?_⟩
  intro z hz; exact leaf_3376_sound hz

theorem leaf_3386_ok : checkAt 527 1000 box_3386 cert_3386 = true := by
  have h := List.all_eq_true.mp batch_67_12_ok accepted_3386 (by simp [batch_67_12_values])
  exact h
theorem leaf_3386_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3386.profileLo box_3386.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3386_ok
theorem branch_box_3386_nonnegative : ∀ j, 0 ≤ branch_box_3386.lower j ∧ 0 ≤ branch_box_3386.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3386, Box.profileLo, Box.profileHi, box_3386]
theorem leaf_3386_BranchSafe : CertificateConsequences.BranchSafe branch_box_3386 := by
  left; refine ⟨branch_box_3386_nonnegative, ?_⟩
  intro z hz; exact leaf_3386_sound hz

theorem leaf_3388_ok : checkAt 527 1000 box_3388 cert_3388 = true := by
  have h := List.all_eq_true.mp batch_67_13_ok accepted_3388 (by simp [batch_67_13_values])
  exact h
theorem leaf_3388_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3388.profileLo box_3388.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3388_ok
theorem branch_box_3388_nonnegative : ∀ j, 0 ≤ branch_box_3388.lower j ∧ 0 ≤ branch_box_3388.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3388, Box.profileLo, Box.profileHi, box_3388]
theorem leaf_3388_BranchSafe : CertificateConsequences.BranchSafe branch_box_3388 := by
  left; refine ⟨branch_box_3388_nonnegative, ?_⟩
  intro z hz; exact leaf_3388_sound hz

theorem leaf_3389_ok : checkAt 527 1000 box_3389 cert_3389 = true := by
  have h := List.all_eq_true.mp batch_67_14_ok accepted_3389 (by simp [batch_67_14_values])
  exact h
theorem leaf_3389_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3389.profileLo box_3389.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3389_ok
theorem branch_box_3389_nonnegative : ∀ j, 0 ≤ branch_box_3389.lower j ∧ 0 ≤ branch_box_3389.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3389, Box.profileLo, Box.profileHi, box_3389]
theorem leaf_3389_BranchSafe : CertificateConsequences.BranchSafe branch_box_3389 := by
  left; refine ⟨branch_box_3389_nonnegative, ?_⟩
  intro z hz; exact leaf_3389_sound hz

theorem leaf_3391_ok : checkAt 527 1000 box_3391 cert_3391 = true := by
  have h := List.all_eq_true.mp batch_67_15_ok accepted_3391 (by simp [batch_67_15_values])
  exact h
theorem leaf_3391_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3391.profileLo box_3391.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3391_ok
theorem branch_box_3391_nonnegative : ∀ j, 0 ≤ branch_box_3391.lower j ∧ 0 ≤ branch_box_3391.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3391, Box.profileLo, Box.profileHi, box_3391]
theorem leaf_3391_BranchSafe : CertificateConsequences.BranchSafe branch_box_3391 := by
  left; refine ⟨branch_box_3391_nonnegative, ?_⟩
  intro z hz; exact leaf_3391_sound hz

theorem leaf_3395_ok : checkAt 527 1000 box_3395 cert_3395 = true := by
  have h := List.all_eq_true.mp batch_67_16_ok accepted_3395 (by simp [batch_67_16_values])
  exact h
theorem leaf_3395_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3395.profileLo box_3395.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3395_ok
theorem branch_box_3395_nonnegative : ∀ j, 0 ≤ branch_box_3395.lower j ∧ 0 ≤ branch_box_3395.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3395, Box.profileLo, Box.profileHi, box_3395]
theorem leaf_3395_BranchSafe : CertificateConsequences.BranchSafe branch_box_3395 := by
  left; refine ⟨branch_box_3395_nonnegative, ?_⟩
  intro z hz; exact leaf_3395_sound hz

#print axioms batch_67_00_ok
#print axioms leaf_3350_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
