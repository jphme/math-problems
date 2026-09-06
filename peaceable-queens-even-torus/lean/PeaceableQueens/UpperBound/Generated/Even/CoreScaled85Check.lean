import PeaceableQueens.UpperBound.Generated.Even.CoreScaled85Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_85_00_values : List Bool := [accepted_4252]
theorem batch_85_00_ok : batch_85_00_values.all id = true := by decide

def batch_85_01_values : List Bool := [accepted_4254]
theorem batch_85_01_ok : batch_85_01_values.all id = true := by decide

def batch_85_02_values : List Bool := [accepted_4256]
theorem batch_85_02_ok : batch_85_02_values.all id = true := by decide

def batch_85_03_values : List Bool := [accepted_4258]
theorem batch_85_03_ok : batch_85_03_values.all id = true := by decide

def batch_85_04_values : List Bool := [accepted_4260]
theorem batch_85_04_ok : batch_85_04_values.all id = true := by decide

def batch_85_05_values : List Bool := [accepted_4266]
theorem batch_85_05_ok : batch_85_05_values.all id = true := by decide

def batch_85_06_values : List Bool := [accepted_4268]
theorem batch_85_06_ok : batch_85_06_values.all id = true := by decide

def batch_85_07_values : List Bool := [accepted_4269]
theorem batch_85_07_ok : batch_85_07_values.all id = true := by decide

def batch_85_08_values : List Bool := [accepted_4271]
theorem batch_85_08_ok : batch_85_08_values.all id = true := by decide

def batch_85_09_values : List Bool := [accepted_4280]
theorem batch_85_09_ok : batch_85_09_values.all id = true := by decide

def batch_85_10_values : List Bool := [accepted_4283]
theorem batch_85_10_ok : batch_85_10_values.all id = true := by decide

def batch_85_11_values : List Bool := [accepted_4288]
theorem batch_85_11_ok : batch_85_11_values.all id = true := by decide

def batch_85_12_values : List Bool := [accepted_4289]
theorem batch_85_12_ok : batch_85_12_values.all id = true := by decide

def batch_85_13_values : List Bool := [accepted_4292]
theorem batch_85_13_ok : batch_85_13_values.all id = true := by decide

def batch_85_14_values : List Bool := [accepted_4293]
theorem batch_85_14_ok : batch_85_14_values.all id = true := by decide

theorem leaf_4252_ok : checkAt 527 1000 box_4252 cert_4252 = true := by
  have h := List.all_eq_true.mp batch_85_00_ok accepted_4252 (by simp [batch_85_00_values])
  exact h
theorem leaf_4252_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4252.profileLo box_4252.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4252_ok
theorem branch_box_4252_nonnegative : ∀ j, 0 ≤ branch_box_4252.lower j ∧ 0 ≤ branch_box_4252.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4252, Box.profileLo, Box.profileHi, box_4252]
theorem leaf_4252_BranchSafe : CertificateConsequences.BranchSafe branch_box_4252 := by
  left; refine ⟨branch_box_4252_nonnegative, ?_⟩
  intro z hz; exact leaf_4252_sound hz

theorem leaf_4254_ok : checkAt 527 1000 box_4254 cert_4254 = true := by
  have h := List.all_eq_true.mp batch_85_01_ok accepted_4254 (by simp [batch_85_01_values])
  exact h
theorem leaf_4254_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4254.profileLo box_4254.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4254_ok
theorem branch_box_4254_nonnegative : ∀ j, 0 ≤ branch_box_4254.lower j ∧ 0 ≤ branch_box_4254.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4254, Box.profileLo, Box.profileHi, box_4254]
theorem leaf_4254_BranchSafe : CertificateConsequences.BranchSafe branch_box_4254 := by
  left; refine ⟨branch_box_4254_nonnegative, ?_⟩
  intro z hz; exact leaf_4254_sound hz

theorem leaf_4256_ok : checkAt 527 1000 box_4256 cert_4256 = true := by
  have h := List.all_eq_true.mp batch_85_02_ok accepted_4256 (by simp [batch_85_02_values])
  exact h
theorem leaf_4256_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4256.profileLo box_4256.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4256_ok
theorem branch_box_4256_nonnegative : ∀ j, 0 ≤ branch_box_4256.lower j ∧ 0 ≤ branch_box_4256.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4256, Box.profileLo, Box.profileHi, box_4256]
theorem leaf_4256_BranchSafe : CertificateConsequences.BranchSafe branch_box_4256 := by
  left; refine ⟨branch_box_4256_nonnegative, ?_⟩
  intro z hz; exact leaf_4256_sound hz

theorem leaf_4258_ok : checkAt 527 1000 box_4258 cert_4258 = true := by
  have h := List.all_eq_true.mp batch_85_03_ok accepted_4258 (by simp [batch_85_03_values])
  exact h
theorem leaf_4258_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4258.profileLo box_4258.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4258_ok
theorem branch_box_4258_nonnegative : ∀ j, 0 ≤ branch_box_4258.lower j ∧ 0 ≤ branch_box_4258.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4258, Box.profileLo, Box.profileHi, box_4258]
theorem leaf_4258_BranchSafe : CertificateConsequences.BranchSafe branch_box_4258 := by
  left; refine ⟨branch_box_4258_nonnegative, ?_⟩
  intro z hz; exact leaf_4258_sound hz

theorem leaf_4260_ok : checkAt 527 1000 box_4260 cert_4260 = true := by
  have h := List.all_eq_true.mp batch_85_04_ok accepted_4260 (by simp [batch_85_04_values])
  exact h
theorem leaf_4260_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4260.profileLo box_4260.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4260_ok
theorem branch_box_4260_nonnegative : ∀ j, 0 ≤ branch_box_4260.lower j ∧ 0 ≤ branch_box_4260.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4260, Box.profileLo, Box.profileHi, box_4260]
theorem leaf_4260_BranchSafe : CertificateConsequences.BranchSafe branch_box_4260 := by
  left; refine ⟨branch_box_4260_nonnegative, ?_⟩
  intro z hz; exact leaf_4260_sound hz

theorem leaf_4266_ok : checkAt 527 1000 box_4266 cert_4266 = true := by
  have h := List.all_eq_true.mp batch_85_05_ok accepted_4266 (by simp [batch_85_05_values])
  exact h
theorem leaf_4266_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4266.profileLo box_4266.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4266_ok
theorem branch_box_4266_nonnegative : ∀ j, 0 ≤ branch_box_4266.lower j ∧ 0 ≤ branch_box_4266.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4266, Box.profileLo, Box.profileHi, box_4266]
theorem leaf_4266_BranchSafe : CertificateConsequences.BranchSafe branch_box_4266 := by
  left; refine ⟨branch_box_4266_nonnegative, ?_⟩
  intro z hz; exact leaf_4266_sound hz

theorem leaf_4268_ok : checkAt 527 1000 box_4268 cert_4268 = true := by
  have h := List.all_eq_true.mp batch_85_06_ok accepted_4268 (by simp [batch_85_06_values])
  exact h
theorem leaf_4268_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4268.profileLo box_4268.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4268_ok
theorem branch_box_4268_nonnegative : ∀ j, 0 ≤ branch_box_4268.lower j ∧ 0 ≤ branch_box_4268.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4268, Box.profileLo, Box.profileHi, box_4268]
theorem leaf_4268_BranchSafe : CertificateConsequences.BranchSafe branch_box_4268 := by
  left; refine ⟨branch_box_4268_nonnegative, ?_⟩
  intro z hz; exact leaf_4268_sound hz

theorem leaf_4269_ok : checkAt 527 1000 box_4269 cert_4269 = true := by
  have h := List.all_eq_true.mp batch_85_07_ok accepted_4269 (by simp [batch_85_07_values])
  exact h
theorem leaf_4269_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4269.profileLo box_4269.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4269_ok
theorem branch_box_4269_nonnegative : ∀ j, 0 ≤ branch_box_4269.lower j ∧ 0 ≤ branch_box_4269.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4269, Box.profileLo, Box.profileHi, box_4269]
theorem leaf_4269_BranchSafe : CertificateConsequences.BranchSafe branch_box_4269 := by
  left; refine ⟨branch_box_4269_nonnegative, ?_⟩
  intro z hz; exact leaf_4269_sound hz

theorem leaf_4271_ok : checkAt 527 1000 box_4271 cert_4271 = true := by
  have h := List.all_eq_true.mp batch_85_08_ok accepted_4271 (by simp [batch_85_08_values])
  exact h
theorem leaf_4271_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4271.profileLo box_4271.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4271_ok
theorem branch_box_4271_nonnegative : ∀ j, 0 ≤ branch_box_4271.lower j ∧ 0 ≤ branch_box_4271.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4271, Box.profileLo, Box.profileHi, box_4271]
theorem leaf_4271_BranchSafe : CertificateConsequences.BranchSafe branch_box_4271 := by
  left; refine ⟨branch_box_4271_nonnegative, ?_⟩
  intro z hz; exact leaf_4271_sound hz

theorem leaf_4280_ok : checkAt 527 1000 box_4280 cert_4280 = true := by
  have h := List.all_eq_true.mp batch_85_09_ok accepted_4280 (by simp [batch_85_09_values])
  exact h
theorem leaf_4280_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4280.profileLo box_4280.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4280_ok
theorem branch_box_4280_nonnegative : ∀ j, 0 ≤ branch_box_4280.lower j ∧ 0 ≤ branch_box_4280.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4280, Box.profileLo, Box.profileHi, box_4280]
theorem leaf_4280_BranchSafe : CertificateConsequences.BranchSafe branch_box_4280 := by
  left; refine ⟨branch_box_4280_nonnegative, ?_⟩
  intro z hz; exact leaf_4280_sound hz

theorem leaf_4283_ok : checkAt 527 1000 box_4283 cert_4283 = true := by
  have h := List.all_eq_true.mp batch_85_10_ok accepted_4283 (by simp [batch_85_10_values])
  exact h
theorem leaf_4283_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4283.profileLo box_4283.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4283_ok
theorem branch_box_4283_nonnegative : ∀ j, 0 ≤ branch_box_4283.lower j ∧ 0 ≤ branch_box_4283.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4283, Box.profileLo, Box.profileHi, box_4283]
theorem leaf_4283_BranchSafe : CertificateConsequences.BranchSafe branch_box_4283 := by
  left; refine ⟨branch_box_4283_nonnegative, ?_⟩
  intro z hz; exact leaf_4283_sound hz

theorem leaf_4288_ok : checkAt 527 1000 box_4288 cert_4288 = true := by
  have h := List.all_eq_true.mp batch_85_11_ok accepted_4288 (by simp [batch_85_11_values])
  exact h
theorem leaf_4288_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4288.profileLo box_4288.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4288_ok
theorem branch_box_4288_nonnegative : ∀ j, 0 ≤ branch_box_4288.lower j ∧ 0 ≤ branch_box_4288.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4288, Box.profileLo, Box.profileHi, box_4288]
theorem leaf_4288_BranchSafe : CertificateConsequences.BranchSafe branch_box_4288 := by
  left; refine ⟨branch_box_4288_nonnegative, ?_⟩
  intro z hz; exact leaf_4288_sound hz

theorem leaf_4289_ok : checkAt 527 1000 box_4289 cert_4289 = true := by
  have h := List.all_eq_true.mp batch_85_12_ok accepted_4289 (by simp [batch_85_12_values])
  exact h
theorem leaf_4289_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4289.profileLo box_4289.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4289_ok
theorem branch_box_4289_nonnegative : ∀ j, 0 ≤ branch_box_4289.lower j ∧ 0 ≤ branch_box_4289.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4289, Box.profileLo, Box.profileHi, box_4289]
theorem leaf_4289_BranchSafe : CertificateConsequences.BranchSafe branch_box_4289 := by
  left; refine ⟨branch_box_4289_nonnegative, ?_⟩
  intro z hz; exact leaf_4289_sound hz

theorem leaf_4292_ok : checkAt 527 1000 box_4292 cert_4292 = true := by
  have h := List.all_eq_true.mp batch_85_13_ok accepted_4292 (by simp [batch_85_13_values])
  exact h
theorem leaf_4292_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4292.profileLo box_4292.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4292_ok
theorem branch_box_4292_nonnegative : ∀ j, 0 ≤ branch_box_4292.lower j ∧ 0 ≤ branch_box_4292.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4292, Box.profileLo, Box.profileHi, box_4292]
theorem leaf_4292_BranchSafe : CertificateConsequences.BranchSafe branch_box_4292 := by
  left; refine ⟨branch_box_4292_nonnegative, ?_⟩
  intro z hz; exact leaf_4292_sound hz

theorem leaf_4293_ok : checkAt 527 1000 box_4293 cert_4293 = true := by
  have h := List.all_eq_true.mp batch_85_14_ok accepted_4293 (by simp [batch_85_14_values])
  exact h
theorem leaf_4293_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4293.profileLo box_4293.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4293_ok
theorem branch_box_4293_nonnegative : ∀ j, 0 ≤ branch_box_4293.lower j ∧ 0 ≤ branch_box_4293.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4293, Box.profileLo, Box.profileHi, box_4293]
theorem leaf_4293_BranchSafe : CertificateConsequences.BranchSafe branch_box_4293 := by
  left; refine ⟨branch_box_4293_nonnegative, ?_⟩
  intro z hz; exact leaf_4293_sound hz

#print axioms batch_85_00_ok
#print axioms leaf_4252_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
