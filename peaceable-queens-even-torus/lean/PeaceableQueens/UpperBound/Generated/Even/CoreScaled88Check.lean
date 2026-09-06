import PeaceableQueens.UpperBound.Generated.Even.CoreScaled88Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_88_00_values : List Bool := [accepted_4400]
theorem batch_88_00_ok : batch_88_00_values.all id = true := by decide

def batch_88_01_values : List Bool := [accepted_4402]
theorem batch_88_01_ok : batch_88_01_values.all id = true := by decide

def batch_88_02_values : List Bool := [accepted_4404]
theorem batch_88_02_ok : batch_88_02_values.all id = true := by decide

def batch_88_03_values : List Bool := [accepted_4406]
theorem batch_88_03_ok : batch_88_03_values.all id = true := by decide

def batch_88_04_values : List Bool := [accepted_4407]
theorem batch_88_04_ok : batch_88_04_values.all id = true := by decide

def batch_88_05_values : List Bool := [accepted_4410]
theorem batch_88_05_ok : batch_88_05_values.all id = true := by decide

def batch_88_06_values : List Bool := [accepted_4418]
theorem batch_88_06_ok : batch_88_06_values.all id = true := by decide

def batch_88_07_values : List Bool := [accepted_4420]
theorem batch_88_07_ok : batch_88_07_values.all id = true := by decide

def batch_88_08_values : List Bool := [accepted_4422]
theorem batch_88_08_ok : batch_88_08_values.all id = true := by decide

theorem leaf_4400_ok : checkAt 527 1000 box_4400 cert_4400 = true := by
  have h := List.all_eq_true.mp batch_88_00_ok accepted_4400 (by simp [batch_88_00_values])
  exact h
theorem leaf_4400_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4400.profileLo box_4400.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4400_ok
theorem branch_box_4400_nonnegative : ∀ j, 0 ≤ branch_box_4400.lower j ∧ 0 ≤ branch_box_4400.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4400, Box.profileLo, Box.profileHi, box_4400]
theorem leaf_4400_BranchSafe : CertificateConsequences.BranchSafe branch_box_4400 := by
  left; refine ⟨branch_box_4400_nonnegative, ?_⟩
  intro z hz; exact leaf_4400_sound hz

theorem leaf_4402_ok : checkAt 527 1000 box_4402 cert_4402 = true := by
  have h := List.all_eq_true.mp batch_88_01_ok accepted_4402 (by simp [batch_88_01_values])
  exact h
theorem leaf_4402_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4402.profileLo box_4402.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4402_ok
theorem branch_box_4402_nonnegative : ∀ j, 0 ≤ branch_box_4402.lower j ∧ 0 ≤ branch_box_4402.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4402, Box.profileLo, Box.profileHi, box_4402]
theorem leaf_4402_BranchSafe : CertificateConsequences.BranchSafe branch_box_4402 := by
  left; refine ⟨branch_box_4402_nonnegative, ?_⟩
  intro z hz; exact leaf_4402_sound hz

theorem leaf_4404_ok : checkAt 527 1000 box_4404 cert_4404 = true := by
  have h := List.all_eq_true.mp batch_88_02_ok accepted_4404 (by simp [batch_88_02_values])
  exact h
theorem leaf_4404_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4404.profileLo box_4404.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4404_ok
theorem branch_box_4404_nonnegative : ∀ j, 0 ≤ branch_box_4404.lower j ∧ 0 ≤ branch_box_4404.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4404, Box.profileLo, Box.profileHi, box_4404]
theorem leaf_4404_BranchSafe : CertificateConsequences.BranchSafe branch_box_4404 := by
  left; refine ⟨branch_box_4404_nonnegative, ?_⟩
  intro z hz; exact leaf_4404_sound hz

theorem leaf_4406_ok : checkAt 527 1000 box_4406 cert_4406 = true := by
  have h := List.all_eq_true.mp batch_88_03_ok accepted_4406 (by simp [batch_88_03_values])
  exact h
theorem leaf_4406_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4406.profileLo box_4406.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4406_ok
theorem branch_box_4406_nonnegative : ∀ j, 0 ≤ branch_box_4406.lower j ∧ 0 ≤ branch_box_4406.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4406, Box.profileLo, Box.profileHi, box_4406]
theorem leaf_4406_BranchSafe : CertificateConsequences.BranchSafe branch_box_4406 := by
  left; refine ⟨branch_box_4406_nonnegative, ?_⟩
  intro z hz; exact leaf_4406_sound hz

theorem leaf_4407_ok : checkAt 527 1000 box_4407 cert_4407 = true := by
  have h := List.all_eq_true.mp batch_88_04_ok accepted_4407 (by simp [batch_88_04_values])
  exact h
theorem leaf_4407_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4407.profileLo box_4407.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4407_ok
theorem branch_box_4407_nonnegative : ∀ j, 0 ≤ branch_box_4407.lower j ∧ 0 ≤ branch_box_4407.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4407, Box.profileLo, Box.profileHi, box_4407]
theorem leaf_4407_BranchSafe : CertificateConsequences.BranchSafe branch_box_4407 := by
  left; refine ⟨branch_box_4407_nonnegative, ?_⟩
  intro z hz; exact leaf_4407_sound hz

theorem leaf_4410_ok : checkAt 527 1000 box_4410 cert_4410 = true := by
  have h := List.all_eq_true.mp batch_88_05_ok accepted_4410 (by simp [batch_88_05_values])
  exact h
theorem leaf_4410_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4410.profileLo box_4410.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4410_ok
theorem branch_box_4410_nonnegative : ∀ j, 0 ≤ branch_box_4410.lower j ∧ 0 ≤ branch_box_4410.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4410, Box.profileLo, Box.profileHi, box_4410]
theorem leaf_4410_BranchSafe : CertificateConsequences.BranchSafe branch_box_4410 := by
  left; refine ⟨branch_box_4410_nonnegative, ?_⟩
  intro z hz; exact leaf_4410_sound hz

theorem leaf_4418_ok : checkAt 527 1000 box_4418 cert_4418 = true := by
  have h := List.all_eq_true.mp batch_88_06_ok accepted_4418 (by simp [batch_88_06_values])
  exact h
theorem leaf_4418_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4418.profileLo box_4418.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4418_ok
theorem branch_box_4418_nonnegative : ∀ j, 0 ≤ branch_box_4418.lower j ∧ 0 ≤ branch_box_4418.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4418, Box.profileLo, Box.profileHi, box_4418]
theorem leaf_4418_BranchSafe : CertificateConsequences.BranchSafe branch_box_4418 := by
  left; refine ⟨branch_box_4418_nonnegative, ?_⟩
  intro z hz; exact leaf_4418_sound hz

theorem leaf_4420_ok : checkAt 527 1000 box_4420 cert_4420 = true := by
  have h := List.all_eq_true.mp batch_88_07_ok accepted_4420 (by simp [batch_88_07_values])
  exact h
theorem leaf_4420_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4420.profileLo box_4420.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4420_ok
theorem branch_box_4420_nonnegative : ∀ j, 0 ≤ branch_box_4420.lower j ∧ 0 ≤ branch_box_4420.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4420, Box.profileLo, Box.profileHi, box_4420]
theorem leaf_4420_BranchSafe : CertificateConsequences.BranchSafe branch_box_4420 := by
  left; refine ⟨branch_box_4420_nonnegative, ?_⟩
  intro z hz; exact leaf_4420_sound hz

theorem leaf_4422_ok : checkAt 527 1000 box_4422 cert_4422 = true := by
  have h := List.all_eq_true.mp batch_88_08_ok accepted_4422 (by simp [batch_88_08_values])
  exact h
theorem leaf_4422_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4422.profileLo box_4422.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4422_ok
theorem branch_box_4422_nonnegative : ∀ j, 0 ≤ branch_box_4422.lower j ∧ 0 ≤ branch_box_4422.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4422, Box.profileLo, Box.profileHi, box_4422]
theorem leaf_4422_BranchSafe : CertificateConsequences.BranchSafe branch_box_4422 := by
  left; refine ⟨branch_box_4422_nonnegative, ?_⟩
  intro z hz; exact leaf_4422_sound hz

#print axioms batch_88_00_ok
#print axioms leaf_4400_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
