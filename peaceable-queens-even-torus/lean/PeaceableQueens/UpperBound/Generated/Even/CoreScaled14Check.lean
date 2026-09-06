import PeaceableQueens.UpperBound.Generated.Even.CoreScaled14Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_14_00_values : List Bool := [accepted_700]
theorem batch_14_00_ok : batch_14_00_values.all id = true := by decide

def batch_14_01_values : List Bool := [accepted_701]
theorem batch_14_01_ok : batch_14_01_values.all id = true := by decide

def batch_14_02_values : List Bool := [accepted_703]
theorem batch_14_02_ok : batch_14_02_values.all id = true := by decide

def batch_14_03_values : List Bool := [accepted_705]
theorem batch_14_03_ok : batch_14_03_values.all id = true := by decide

def batch_14_04_values : List Bool := [accepted_712]
theorem batch_14_04_ok : batch_14_04_values.all id = true := by decide

def batch_14_05_values : List Bool := [accepted_714]
theorem batch_14_05_ok : batch_14_05_values.all id = true := by decide

def batch_14_06_values : List Bool := [accepted_716]
theorem batch_14_06_ok : batch_14_06_values.all id = true := by decide

def batch_14_07_values : List Bool := [accepted_722]
theorem batch_14_07_ok : batch_14_07_values.all id = true := by decide

def batch_14_08_values : List Bool := [accepted_724]
theorem batch_14_08_ok : batch_14_08_values.all id = true := by decide

def batch_14_09_values : List Bool := [accepted_726]
theorem batch_14_09_ok : batch_14_09_values.all id = true := by decide

def batch_14_10_values : List Bool := [accepted_730]
theorem batch_14_10_ok : batch_14_10_values.all id = true := by decide

def batch_14_11_values : List Bool := [accepted_732]
theorem batch_14_11_ok : batch_14_11_values.all id = true := by decide

def batch_14_12_values : List Bool := [accepted_734]
theorem batch_14_12_ok : batch_14_12_values.all id = true := by decide

def batch_14_13_values : List Bool := [accepted_735]
theorem batch_14_13_ok : batch_14_13_values.all id = true := by decide

def batch_14_14_values : List Bool := [accepted_737]
theorem batch_14_14_ok : batch_14_14_values.all id = true := by decide

def batch_14_15_values : List Bool := [accepted_739]
theorem batch_14_15_ok : batch_14_15_values.all id = true := by decide

theorem leaf_700_ok : checkAt 527 1000 box_700 cert_700 = true := by
  have h := List.all_eq_true.mp batch_14_00_ok accepted_700 (by simp [batch_14_00_values])
  exact h
theorem leaf_700_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_700.profileLo box_700.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_700_ok
theorem branch_box_700_nonnegative : ∀ j, 0 ≤ branch_box_700.lower j ∧ 0 ≤ branch_box_700.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_700, Box.profileLo, Box.profileHi, box_700]
theorem leaf_700_BranchSafe : CertificateConsequences.BranchSafe branch_box_700 := by
  left; refine ⟨branch_box_700_nonnegative, ?_⟩
  intro z hz; exact leaf_700_sound hz

theorem leaf_701_ok : checkAt 527 1000 box_701 cert_701 = true := by
  have h := List.all_eq_true.mp batch_14_01_ok accepted_701 (by simp [batch_14_01_values])
  exact h
theorem leaf_701_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_701.profileLo box_701.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_701_ok
theorem branch_box_701_nonnegative : ∀ j, 0 ≤ branch_box_701.lower j ∧ 0 ≤ branch_box_701.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_701, Box.profileLo, Box.profileHi, box_701]
theorem leaf_701_BranchSafe : CertificateConsequences.BranchSafe branch_box_701 := by
  left; refine ⟨branch_box_701_nonnegative, ?_⟩
  intro z hz; exact leaf_701_sound hz

theorem leaf_703_ok : checkAt 527 1000 box_703 cert_703 = true := by
  have h := List.all_eq_true.mp batch_14_02_ok accepted_703 (by simp [batch_14_02_values])
  exact h
theorem leaf_703_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_703.profileLo box_703.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_703_ok
theorem branch_box_703_nonnegative : ∀ j, 0 ≤ branch_box_703.lower j ∧ 0 ≤ branch_box_703.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_703, Box.profileLo, Box.profileHi, box_703]
theorem leaf_703_BranchSafe : CertificateConsequences.BranchSafe branch_box_703 := by
  left; refine ⟨branch_box_703_nonnegative, ?_⟩
  intro z hz; exact leaf_703_sound hz

theorem leaf_705_ok : checkAt 527 1000 box_705 cert_705 = true := by
  have h := List.all_eq_true.mp batch_14_03_ok accepted_705 (by simp [batch_14_03_values])
  exact h
theorem leaf_705_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_705.profileLo box_705.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_705_ok
theorem branch_box_705_nonnegative : ∀ j, 0 ≤ branch_box_705.lower j ∧ 0 ≤ branch_box_705.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_705, Box.profileLo, Box.profileHi, box_705]
theorem leaf_705_BranchSafe : CertificateConsequences.BranchSafe branch_box_705 := by
  left; refine ⟨branch_box_705_nonnegative, ?_⟩
  intro z hz; exact leaf_705_sound hz

theorem leaf_712_ok : checkAt 527 1000 box_712 cert_712 = true := by
  have h := List.all_eq_true.mp batch_14_04_ok accepted_712 (by simp [batch_14_04_values])
  exact h
theorem leaf_712_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_712.profileLo box_712.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_712_ok
theorem branch_box_712_nonnegative : ∀ j, 0 ≤ branch_box_712.lower j ∧ 0 ≤ branch_box_712.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_712, Box.profileLo, Box.profileHi, box_712]
theorem leaf_712_BranchSafe : CertificateConsequences.BranchSafe branch_box_712 := by
  left; refine ⟨branch_box_712_nonnegative, ?_⟩
  intro z hz; exact leaf_712_sound hz

theorem leaf_714_ok : checkAt 527 1000 box_714 cert_714 = true := by
  have h := List.all_eq_true.mp batch_14_05_ok accepted_714 (by simp [batch_14_05_values])
  exact h
theorem leaf_714_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_714.profileLo box_714.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_714_ok
theorem branch_box_714_nonnegative : ∀ j, 0 ≤ branch_box_714.lower j ∧ 0 ≤ branch_box_714.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_714, Box.profileLo, Box.profileHi, box_714]
theorem leaf_714_BranchSafe : CertificateConsequences.BranchSafe branch_box_714 := by
  left; refine ⟨branch_box_714_nonnegative, ?_⟩
  intro z hz; exact leaf_714_sound hz

theorem leaf_716_ok : checkAt 527 1000 box_716 cert_716 = true := by
  have h := List.all_eq_true.mp batch_14_06_ok accepted_716 (by simp [batch_14_06_values])
  exact h
theorem leaf_716_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_716.profileLo box_716.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_716_ok
theorem branch_box_716_nonnegative : ∀ j, 0 ≤ branch_box_716.lower j ∧ 0 ≤ branch_box_716.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_716, Box.profileLo, Box.profileHi, box_716]
theorem leaf_716_BranchSafe : CertificateConsequences.BranchSafe branch_box_716 := by
  left; refine ⟨branch_box_716_nonnegative, ?_⟩
  intro z hz; exact leaf_716_sound hz

theorem leaf_722_ok : checkAt 527 1000 box_722 cert_722 = true := by
  have h := List.all_eq_true.mp batch_14_07_ok accepted_722 (by simp [batch_14_07_values])
  exact h
theorem leaf_722_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_722.profileLo box_722.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_722_ok
theorem branch_box_722_nonnegative : ∀ j, 0 ≤ branch_box_722.lower j ∧ 0 ≤ branch_box_722.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_722, Box.profileLo, Box.profileHi, box_722]
theorem leaf_722_BranchSafe : CertificateConsequences.BranchSafe branch_box_722 := by
  left; refine ⟨branch_box_722_nonnegative, ?_⟩
  intro z hz; exact leaf_722_sound hz

theorem leaf_724_ok : checkAt 527 1000 box_724 cert_724 = true := by
  have h := List.all_eq_true.mp batch_14_08_ok accepted_724 (by simp [batch_14_08_values])
  exact h
theorem leaf_724_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_724.profileLo box_724.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_724_ok
theorem branch_box_724_nonnegative : ∀ j, 0 ≤ branch_box_724.lower j ∧ 0 ≤ branch_box_724.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_724, Box.profileLo, Box.profileHi, box_724]
theorem leaf_724_BranchSafe : CertificateConsequences.BranchSafe branch_box_724 := by
  left; refine ⟨branch_box_724_nonnegative, ?_⟩
  intro z hz; exact leaf_724_sound hz

theorem leaf_726_ok : checkAt 527 1000 box_726 cert_726 = true := by
  have h := List.all_eq_true.mp batch_14_09_ok accepted_726 (by simp [batch_14_09_values])
  exact h
theorem leaf_726_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_726.profileLo box_726.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_726_ok
theorem branch_box_726_nonnegative : ∀ j, 0 ≤ branch_box_726.lower j ∧ 0 ≤ branch_box_726.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_726, Box.profileLo, Box.profileHi, box_726]
theorem leaf_726_BranchSafe : CertificateConsequences.BranchSafe branch_box_726 := by
  left; refine ⟨branch_box_726_nonnegative, ?_⟩
  intro z hz; exact leaf_726_sound hz

theorem leaf_730_ok : checkAt 527 1000 box_730 cert_730 = true := by
  have h := List.all_eq_true.mp batch_14_10_ok accepted_730 (by simp [batch_14_10_values])
  exact h
theorem leaf_730_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_730.profileLo box_730.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_730_ok
theorem branch_box_730_nonnegative : ∀ j, 0 ≤ branch_box_730.lower j ∧ 0 ≤ branch_box_730.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_730, Box.profileLo, Box.profileHi, box_730]
theorem leaf_730_BranchSafe : CertificateConsequences.BranchSafe branch_box_730 := by
  left; refine ⟨branch_box_730_nonnegative, ?_⟩
  intro z hz; exact leaf_730_sound hz

theorem leaf_732_ok : checkAt 527 1000 box_732 cert_732 = true := by
  have h := List.all_eq_true.mp batch_14_11_ok accepted_732 (by simp [batch_14_11_values])
  exact h
theorem leaf_732_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_732.profileLo box_732.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_732_ok
theorem branch_box_732_nonnegative : ∀ j, 0 ≤ branch_box_732.lower j ∧ 0 ≤ branch_box_732.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_732, Box.profileLo, Box.profileHi, box_732]
theorem leaf_732_BranchSafe : CertificateConsequences.BranchSafe branch_box_732 := by
  left; refine ⟨branch_box_732_nonnegative, ?_⟩
  intro z hz; exact leaf_732_sound hz

theorem leaf_734_ok : checkAt 527 1000 box_734 cert_734 = true := by
  have h := List.all_eq_true.mp batch_14_12_ok accepted_734 (by simp [batch_14_12_values])
  exact h
theorem leaf_734_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_734.profileLo box_734.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_734_ok
theorem branch_box_734_nonnegative : ∀ j, 0 ≤ branch_box_734.lower j ∧ 0 ≤ branch_box_734.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_734, Box.profileLo, Box.profileHi, box_734]
theorem leaf_734_BranchSafe : CertificateConsequences.BranchSafe branch_box_734 := by
  left; refine ⟨branch_box_734_nonnegative, ?_⟩
  intro z hz; exact leaf_734_sound hz

theorem leaf_735_ok : checkAt 527 1000 box_735 cert_735 = true := by
  have h := List.all_eq_true.mp batch_14_13_ok accepted_735 (by simp [batch_14_13_values])
  exact h
theorem leaf_735_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_735.profileLo box_735.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_735_ok
theorem branch_box_735_nonnegative : ∀ j, 0 ≤ branch_box_735.lower j ∧ 0 ≤ branch_box_735.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_735, Box.profileLo, Box.profileHi, box_735]
theorem leaf_735_BranchSafe : CertificateConsequences.BranchSafe branch_box_735 := by
  left; refine ⟨branch_box_735_nonnegative, ?_⟩
  intro z hz; exact leaf_735_sound hz

theorem leaf_737_ok : checkAt 527 1000 box_737 cert_737 = true := by
  have h := List.all_eq_true.mp batch_14_14_ok accepted_737 (by simp [batch_14_14_values])
  exact h
theorem leaf_737_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_737.profileLo box_737.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_737_ok
theorem branch_box_737_nonnegative : ∀ j, 0 ≤ branch_box_737.lower j ∧ 0 ≤ branch_box_737.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_737, Box.profileLo, Box.profileHi, box_737]
theorem leaf_737_BranchSafe : CertificateConsequences.BranchSafe branch_box_737 := by
  left; refine ⟨branch_box_737_nonnegative, ?_⟩
  intro z hz; exact leaf_737_sound hz

theorem leaf_739_ok : checkAt 527 1000 box_739 cert_739 = true := by
  have h := List.all_eq_true.mp batch_14_15_ok accepted_739 (by simp [batch_14_15_values])
  exact h
theorem leaf_739_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_739.profileLo box_739.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_739_ok
theorem branch_box_739_nonnegative : ∀ j, 0 ≤ branch_box_739.lower j ∧ 0 ≤ branch_box_739.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_739, Box.profileLo, Box.profileHi, box_739]
theorem leaf_739_BranchSafe : CertificateConsequences.BranchSafe branch_box_739 := by
  left; refine ⟨branch_box_739_nonnegative, ?_⟩
  intro z hz; exact leaf_739_sound hz

#print axioms batch_14_00_ok
#print axioms leaf_700_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
