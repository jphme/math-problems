import PeaceableQueens.UpperBound.Generated.Even.C527Scaled125Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_125_00_values : List Bool := [accepted_6252]
theorem batch_125_00_ok : batch_125_00_values.all id = true := by decide

def batch_125_01_values : List Bool := [accepted_6253]
theorem batch_125_01_ok : batch_125_01_values.all id = true := by decide

def batch_125_02_values : List Bool := [accepted_6254]
theorem batch_125_02_ok : batch_125_02_values.all id = true := by decide

def batch_125_03_values : List Bool := [accepted_6260]
theorem batch_125_03_ok : batch_125_03_values.all id = true := by decide

def batch_125_04_values : List Bool := [accepted_6261]
theorem batch_125_04_ok : batch_125_04_values.all id = true := by decide

def batch_125_05_values : List Bool := [accepted_6262]
theorem batch_125_05_ok : batch_125_05_values.all id = true := by decide

def batch_125_06_values : List Bool := [accepted_6263]
theorem batch_125_06_ok : batch_125_06_values.all id = true := by decide

def batch_125_07_values : List Bool := [accepted_6271]
theorem batch_125_07_ok : batch_125_07_values.all id = true := by decide

def batch_125_08_values : List Bool := [accepted_6272]
theorem batch_125_08_ok : batch_125_08_values.all id = true := by decide

def batch_125_09_values : List Bool := [accepted_6275]
theorem batch_125_09_ok : batch_125_09_values.all id = true := by decide

def batch_125_10_values : List Bool := [accepted_6279]
theorem batch_125_10_ok : batch_125_10_values.all id = true := by decide

def batch_125_11_values : List Bool := [accepted_6281]
theorem batch_125_11_ok : batch_125_11_values.all id = true := by decide

def batch_125_12_values : List Bool := [accepted_6282]
theorem batch_125_12_ok : batch_125_12_values.all id = true := by decide

def batch_125_13_values : List Bool := [accepted_6291]
theorem batch_125_13_ok : batch_125_13_values.all id = true := by decide

def batch_125_14_values : List Bool := [accepted_6293]
theorem batch_125_14_ok : batch_125_14_values.all id = true := by decide

def batch_125_15_values : List Bool := [accepted_6294]
theorem batch_125_15_ok : batch_125_15_values.all id = true := by decide

def batch_125_16_values : List Bool := [accepted_6295]
theorem batch_125_16_ok : batch_125_16_values.all id = true := by decide

def batch_125_17_values : List Bool := [accepted_6296]
theorem batch_125_17_ok : batch_125_17_values.all id = true := by decide

def batch_125_18_values : List Bool := [accepted_6298]
theorem batch_125_18_ok : batch_125_18_values.all id = true := by decide

def batch_125_19_values : List Bool := [accepted_6299]
theorem batch_125_19_ok : batch_125_19_values.all id = true := by decide

theorem leaf_6252_ok : checkAt 527 1000 box_6252 cert_6252 = true := by
  have h := List.all_eq_true.mp batch_125_00_ok accepted_6252 (by simp [batch_125_00_values])
  exact h
theorem leaf_6252_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6252.profileLo box_6252.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6252_ok
theorem branch_box_6252_nonnegative : ∀ j, 0 ≤ branch_box_6252.lower j ∧ 0 ≤ branch_box_6252.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6252, Box.profileLo, Box.profileHi, box_6252]
theorem leaf_6252_BranchSafe : CertificateConsequences.BranchSafe branch_box_6252 := by
  left; refine ⟨branch_box_6252_nonnegative, ?_⟩
  intro z hz; exact leaf_6252_sound hz

theorem leaf_6253_ok : checkAt 527 1000 box_6253 cert_6253 = true := by
  have h := List.all_eq_true.mp batch_125_01_ok accepted_6253 (by simp [batch_125_01_values])
  exact h
theorem leaf_6253_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6253.profileLo box_6253.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6253_ok
theorem branch_box_6253_nonnegative : ∀ j, 0 ≤ branch_box_6253.lower j ∧ 0 ≤ branch_box_6253.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6253, Box.profileLo, Box.profileHi, box_6253]
theorem leaf_6253_BranchSafe : CertificateConsequences.BranchSafe branch_box_6253 := by
  left; refine ⟨branch_box_6253_nonnegative, ?_⟩
  intro z hz; exact leaf_6253_sound hz

theorem leaf_6254_ok : checkAt 527 1000 box_6254 cert_6254 = true := by
  have h := List.all_eq_true.mp batch_125_02_ok accepted_6254 (by simp [batch_125_02_values])
  exact h
theorem leaf_6254_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6254.profileLo box_6254.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6254_ok
theorem branch_box_6254_nonnegative : ∀ j, 0 ≤ branch_box_6254.lower j ∧ 0 ≤ branch_box_6254.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6254, Box.profileLo, Box.profileHi, box_6254]
theorem leaf_6254_BranchSafe : CertificateConsequences.BranchSafe branch_box_6254 := by
  left; refine ⟨branch_box_6254_nonnegative, ?_⟩
  intro z hz; exact leaf_6254_sound hz

theorem leaf_6260_ok : checkAt 527 1000 box_6260 cert_6260 = true := by
  have h := List.all_eq_true.mp batch_125_03_ok accepted_6260 (by simp [batch_125_03_values])
  exact h
theorem leaf_6260_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6260.profileLo box_6260.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6260_ok
theorem branch_box_6260_nonnegative : ∀ j, 0 ≤ branch_box_6260.lower j ∧ 0 ≤ branch_box_6260.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6260, Box.profileLo, Box.profileHi, box_6260]
theorem leaf_6260_BranchSafe : CertificateConsequences.BranchSafe branch_box_6260 := by
  left; refine ⟨branch_box_6260_nonnegative, ?_⟩
  intro z hz; exact leaf_6260_sound hz

theorem leaf_6261_ok : checkAt 527 1000 box_6261 cert_6261 = true := by
  have h := List.all_eq_true.mp batch_125_04_ok accepted_6261 (by simp [batch_125_04_values])
  exact h
theorem leaf_6261_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6261.profileLo box_6261.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6261_ok
theorem branch_box_6261_nonnegative : ∀ j, 0 ≤ branch_box_6261.lower j ∧ 0 ≤ branch_box_6261.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6261, Box.profileLo, Box.profileHi, box_6261]
theorem leaf_6261_BranchSafe : CertificateConsequences.BranchSafe branch_box_6261 := by
  left; refine ⟨branch_box_6261_nonnegative, ?_⟩
  intro z hz; exact leaf_6261_sound hz

theorem leaf_6262_ok : checkAt 527 1000 box_6262 cert_6262 = true := by
  have h := List.all_eq_true.mp batch_125_05_ok accepted_6262 (by simp [batch_125_05_values])
  exact h
theorem leaf_6262_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6262.profileLo box_6262.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6262_ok
theorem branch_box_6262_nonnegative : ∀ j, 0 ≤ branch_box_6262.lower j ∧ 0 ≤ branch_box_6262.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6262, Box.profileLo, Box.profileHi, box_6262]
theorem leaf_6262_BranchSafe : CertificateConsequences.BranchSafe branch_box_6262 := by
  left; refine ⟨branch_box_6262_nonnegative, ?_⟩
  intro z hz; exact leaf_6262_sound hz

theorem leaf_6263_ok : checkAt 527 1000 box_6263 cert_6263 = true := by
  have h := List.all_eq_true.mp batch_125_06_ok accepted_6263 (by simp [batch_125_06_values])
  exact h
theorem leaf_6263_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6263.profileLo box_6263.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6263_ok
theorem branch_box_6263_nonnegative : ∀ j, 0 ≤ branch_box_6263.lower j ∧ 0 ≤ branch_box_6263.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6263, Box.profileLo, Box.profileHi, box_6263]
theorem leaf_6263_BranchSafe : CertificateConsequences.BranchSafe branch_box_6263 := by
  left; refine ⟨branch_box_6263_nonnegative, ?_⟩
  intro z hz; exact leaf_6263_sound hz

theorem leaf_6271_ok : checkAt 527 1000 box_6271 cert_6271 = true := by
  have h := List.all_eq_true.mp batch_125_07_ok accepted_6271 (by simp [batch_125_07_values])
  exact h
theorem leaf_6271_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6271.profileLo box_6271.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6271_ok
theorem branch_box_6271_nonnegative : ∀ j, 0 ≤ branch_box_6271.lower j ∧ 0 ≤ branch_box_6271.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6271, Box.profileLo, Box.profileHi, box_6271]
theorem leaf_6271_BranchSafe : CertificateConsequences.BranchSafe branch_box_6271 := by
  left; refine ⟨branch_box_6271_nonnegative, ?_⟩
  intro z hz; exact leaf_6271_sound hz

theorem leaf_6272_ok : checkAt 527 1000 box_6272 cert_6272 = true := by
  have h := List.all_eq_true.mp batch_125_08_ok accepted_6272 (by simp [batch_125_08_values])
  exact h
theorem leaf_6272_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6272.profileLo box_6272.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6272_ok
theorem branch_box_6272_nonnegative : ∀ j, 0 ≤ branch_box_6272.lower j ∧ 0 ≤ branch_box_6272.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6272, Box.profileLo, Box.profileHi, box_6272]
theorem leaf_6272_BranchSafe : CertificateConsequences.BranchSafe branch_box_6272 := by
  left; refine ⟨branch_box_6272_nonnegative, ?_⟩
  intro z hz; exact leaf_6272_sound hz

theorem leaf_6275_ok : checkAt 527 1000 box_6275 cert_6275 = true := by
  have h := List.all_eq_true.mp batch_125_09_ok accepted_6275 (by simp [batch_125_09_values])
  exact h
theorem leaf_6275_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6275.profileLo box_6275.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6275_ok
theorem branch_box_6275_nonnegative : ∀ j, 0 ≤ branch_box_6275.lower j ∧ 0 ≤ branch_box_6275.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6275, Box.profileLo, Box.profileHi, box_6275]
theorem leaf_6275_BranchSafe : CertificateConsequences.BranchSafe branch_box_6275 := by
  left; refine ⟨branch_box_6275_nonnegative, ?_⟩
  intro z hz; exact leaf_6275_sound hz

theorem leaf_6279_ok : checkAt 527 1000 box_6279 cert_6279 = true := by
  have h := List.all_eq_true.mp batch_125_10_ok accepted_6279 (by simp [batch_125_10_values])
  exact h
theorem leaf_6279_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6279.profileLo box_6279.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6279_ok
theorem branch_box_6279_nonnegative : ∀ j, 0 ≤ branch_box_6279.lower j ∧ 0 ≤ branch_box_6279.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6279, Box.profileLo, Box.profileHi, box_6279]
theorem leaf_6279_BranchSafe : CertificateConsequences.BranchSafe branch_box_6279 := by
  left; refine ⟨branch_box_6279_nonnegative, ?_⟩
  intro z hz; exact leaf_6279_sound hz

theorem leaf_6281_ok : checkAt 527 1000 box_6281 cert_6281 = true := by
  have h := List.all_eq_true.mp batch_125_11_ok accepted_6281 (by simp [batch_125_11_values])
  exact h
theorem leaf_6281_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6281.profileLo box_6281.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6281_ok
theorem branch_box_6281_nonnegative : ∀ j, 0 ≤ branch_box_6281.lower j ∧ 0 ≤ branch_box_6281.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6281, Box.profileLo, Box.profileHi, box_6281]
theorem leaf_6281_BranchSafe : CertificateConsequences.BranchSafe branch_box_6281 := by
  left; refine ⟨branch_box_6281_nonnegative, ?_⟩
  intro z hz; exact leaf_6281_sound hz

theorem leaf_6282_ok : checkAt 527 1000 box_6282 cert_6282 = true := by
  have h := List.all_eq_true.mp batch_125_12_ok accepted_6282 (by simp [batch_125_12_values])
  exact h
theorem leaf_6282_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6282.profileLo box_6282.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6282_ok
theorem branch_box_6282_nonnegative : ∀ j, 0 ≤ branch_box_6282.lower j ∧ 0 ≤ branch_box_6282.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6282, Box.profileLo, Box.profileHi, box_6282]
theorem leaf_6282_BranchSafe : CertificateConsequences.BranchSafe branch_box_6282 := by
  left; refine ⟨branch_box_6282_nonnegative, ?_⟩
  intro z hz; exact leaf_6282_sound hz

theorem leaf_6291_ok : checkAt 527 1000 box_6291 cert_6291 = true := by
  have h := List.all_eq_true.mp batch_125_13_ok accepted_6291 (by simp [batch_125_13_values])
  exact h
theorem leaf_6291_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6291.profileLo box_6291.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6291_ok
theorem branch_box_6291_nonnegative : ∀ j, 0 ≤ branch_box_6291.lower j ∧ 0 ≤ branch_box_6291.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6291, Box.profileLo, Box.profileHi, box_6291]
theorem leaf_6291_BranchSafe : CertificateConsequences.BranchSafe branch_box_6291 := by
  left; refine ⟨branch_box_6291_nonnegative, ?_⟩
  intro z hz; exact leaf_6291_sound hz

theorem leaf_6293_ok : checkAt 527 1000 box_6293 cert_6293 = true := by
  have h := List.all_eq_true.mp batch_125_14_ok accepted_6293 (by simp [batch_125_14_values])
  exact h
theorem leaf_6293_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6293.profileLo box_6293.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6293_ok
theorem branch_box_6293_nonnegative : ∀ j, 0 ≤ branch_box_6293.lower j ∧ 0 ≤ branch_box_6293.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6293, Box.profileLo, Box.profileHi, box_6293]
theorem leaf_6293_BranchSafe : CertificateConsequences.BranchSafe branch_box_6293 := by
  left; refine ⟨branch_box_6293_nonnegative, ?_⟩
  intro z hz; exact leaf_6293_sound hz

theorem leaf_6294_ok : checkAt 527 1000 box_6294 cert_6294 = true := by
  have h := List.all_eq_true.mp batch_125_15_ok accepted_6294 (by simp [batch_125_15_values])
  exact h
theorem leaf_6294_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6294.profileLo box_6294.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6294_ok
theorem branch_box_6294_nonnegative : ∀ j, 0 ≤ branch_box_6294.lower j ∧ 0 ≤ branch_box_6294.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6294, Box.profileLo, Box.profileHi, box_6294]
theorem leaf_6294_BranchSafe : CertificateConsequences.BranchSafe branch_box_6294 := by
  left; refine ⟨branch_box_6294_nonnegative, ?_⟩
  intro z hz; exact leaf_6294_sound hz

theorem leaf_6295_ok : checkAt 527 1000 box_6295 cert_6295 = true := by
  have h := List.all_eq_true.mp batch_125_16_ok accepted_6295 (by simp [batch_125_16_values])
  exact h
theorem leaf_6295_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6295.profileLo box_6295.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6295_ok
theorem branch_box_6295_nonnegative : ∀ j, 0 ≤ branch_box_6295.lower j ∧ 0 ≤ branch_box_6295.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6295, Box.profileLo, Box.profileHi, box_6295]
theorem leaf_6295_BranchSafe : CertificateConsequences.BranchSafe branch_box_6295 := by
  left; refine ⟨branch_box_6295_nonnegative, ?_⟩
  intro z hz; exact leaf_6295_sound hz

theorem leaf_6296_ok : checkAt 527 1000 box_6296 cert_6296 = true := by
  have h := List.all_eq_true.mp batch_125_17_ok accepted_6296 (by simp [batch_125_17_values])
  exact h
theorem leaf_6296_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6296.profileLo box_6296.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6296_ok
theorem branch_box_6296_nonnegative : ∀ j, 0 ≤ branch_box_6296.lower j ∧ 0 ≤ branch_box_6296.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6296, Box.profileLo, Box.profileHi, box_6296]
theorem leaf_6296_BranchSafe : CertificateConsequences.BranchSafe branch_box_6296 := by
  left; refine ⟨branch_box_6296_nonnegative, ?_⟩
  intro z hz; exact leaf_6296_sound hz

theorem leaf_6298_ok : checkAt 527 1000 box_6298 cert_6298 = true := by
  have h := List.all_eq_true.mp batch_125_18_ok accepted_6298 (by simp [batch_125_18_values])
  exact h
theorem leaf_6298_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6298.profileLo box_6298.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6298_ok
theorem branch_box_6298_nonnegative : ∀ j, 0 ≤ branch_box_6298.lower j ∧ 0 ≤ branch_box_6298.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6298, Box.profileLo, Box.profileHi, box_6298]
theorem leaf_6298_BranchSafe : CertificateConsequences.BranchSafe branch_box_6298 := by
  left; refine ⟨branch_box_6298_nonnegative, ?_⟩
  intro z hz; exact leaf_6298_sound hz

theorem leaf_6299_ok : checkAt 527 1000 box_6299 cert_6299 = true := by
  have h := List.all_eq_true.mp batch_125_19_ok accepted_6299 (by simp [batch_125_19_values])
  exact h
theorem leaf_6299_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6299.profileLo box_6299.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6299_ok
theorem branch_box_6299_nonnegative : ∀ j, 0 ≤ branch_box_6299.lower j ∧ 0 ≤ branch_box_6299.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6299, Box.profileLo, Box.profileHi, box_6299]
theorem leaf_6299_BranchSafe : CertificateConsequences.BranchSafe branch_box_6299 := by
  left; refine ⟨branch_box_6299_nonnegative, ?_⟩
  intro z hz; exact leaf_6299_sound hz

#print axioms batch_125_00_ok
#print axioms leaf_6252_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
