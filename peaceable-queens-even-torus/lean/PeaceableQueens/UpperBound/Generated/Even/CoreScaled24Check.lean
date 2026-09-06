import PeaceableQueens.UpperBound.Generated.Even.CoreScaled24Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_24_00_values : List Bool := [accepted_1200]
theorem batch_24_00_ok : batch_24_00_values.all id = true := by decide

def batch_24_01_values : List Bool := [accepted_1202]
theorem batch_24_01_ok : batch_24_01_values.all id = true := by decide

def batch_24_02_values : List Bool := [accepted_1204]
theorem batch_24_02_ok : batch_24_02_values.all id = true := by decide

def batch_24_03_values : List Bool := [accepted_1205]
theorem batch_24_03_ok : batch_24_03_values.all id = true := by decide

def batch_24_04_values : List Bool := [accepted_1214]
theorem batch_24_04_ok : batch_24_04_values.all id = true := by decide

def batch_24_05_values : List Bool := [accepted_1216]
theorem batch_24_05_ok : batch_24_05_values.all id = true := by decide

def batch_24_06_values : List Bool := [accepted_1220]
theorem batch_24_06_ok : batch_24_06_values.all id = true := by decide

def batch_24_07_values : List Bool := [accepted_1222]
theorem batch_24_07_ok : batch_24_07_values.all id = true := by decide

def batch_24_08_values : List Bool := [accepted_1224]
theorem batch_24_08_ok : batch_24_08_values.all id = true := by decide

def batch_24_09_values : List Bool := [accepted_1226]
theorem batch_24_09_ok : batch_24_09_values.all id = true := by decide

def batch_24_10_values : List Bool := [accepted_1227]
theorem batch_24_10_ok : batch_24_10_values.all id = true := by decide

def batch_24_11_values : List Bool := [accepted_1229]
theorem batch_24_11_ok : batch_24_11_values.all id = true := by decide

def batch_24_12_values : List Bool := [accepted_1231]
theorem batch_24_12_ok : batch_24_12_values.all id = true := by decide

def batch_24_13_values : List Bool := [accepted_1234]
theorem batch_24_13_ok : batch_24_13_values.all id = true := by decide

def batch_24_14_values : List Bool := [accepted_1236]
theorem batch_24_14_ok : batch_24_14_values.all id = true := by decide

def batch_24_15_values : List Bool := [accepted_1237]
theorem batch_24_15_ok : batch_24_15_values.all id = true := by decide

def batch_24_16_values : List Bool := [accepted_1242]
theorem batch_24_16_ok : batch_24_16_values.all id = true := by decide

def batch_24_17_values : List Bool := [accepted_1244]
theorem batch_24_17_ok : batch_24_17_values.all id = true := by decide

def batch_24_18_values : List Bool := [accepted_1246]
theorem batch_24_18_ok : batch_24_18_values.all id = true := by decide

def batch_24_19_values : List Bool := [accepted_1248]
theorem batch_24_19_ok : batch_24_19_values.all id = true := by decide

theorem leaf_1200_ok : checkAt 527 1000 box_1200 cert_1200 = true := by
  have h := List.all_eq_true.mp batch_24_00_ok accepted_1200 (by simp [batch_24_00_values])
  exact h
theorem leaf_1200_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1200.profileLo box_1200.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1200_ok
theorem branch_box_1200_nonnegative : ∀ j, 0 ≤ branch_box_1200.lower j ∧ 0 ≤ branch_box_1200.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1200, Box.profileLo, Box.profileHi, box_1200]
theorem leaf_1200_BranchSafe : CertificateConsequences.BranchSafe branch_box_1200 := by
  left; refine ⟨branch_box_1200_nonnegative, ?_⟩
  intro z hz; exact leaf_1200_sound hz

theorem leaf_1202_ok : checkAt 527 1000 box_1202 cert_1202 = true := by
  have h := List.all_eq_true.mp batch_24_01_ok accepted_1202 (by simp [batch_24_01_values])
  exact h
theorem leaf_1202_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1202.profileLo box_1202.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1202_ok
theorem branch_box_1202_nonnegative : ∀ j, 0 ≤ branch_box_1202.lower j ∧ 0 ≤ branch_box_1202.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1202, Box.profileLo, Box.profileHi, box_1202]
theorem leaf_1202_BranchSafe : CertificateConsequences.BranchSafe branch_box_1202 := by
  left; refine ⟨branch_box_1202_nonnegative, ?_⟩
  intro z hz; exact leaf_1202_sound hz

theorem leaf_1204_ok : checkAt 527 1000 box_1204 cert_1204 = true := by
  have h := List.all_eq_true.mp batch_24_02_ok accepted_1204 (by simp [batch_24_02_values])
  exact h
theorem leaf_1204_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1204.profileLo box_1204.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1204_ok
theorem branch_box_1204_nonnegative : ∀ j, 0 ≤ branch_box_1204.lower j ∧ 0 ≤ branch_box_1204.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1204, Box.profileLo, Box.profileHi, box_1204]
theorem leaf_1204_BranchSafe : CertificateConsequences.BranchSafe branch_box_1204 := by
  left; refine ⟨branch_box_1204_nonnegative, ?_⟩
  intro z hz; exact leaf_1204_sound hz

theorem leaf_1205_ok : checkAt 527 1000 box_1205 cert_1205 = true := by
  have h := List.all_eq_true.mp batch_24_03_ok accepted_1205 (by simp [batch_24_03_values])
  exact h
theorem leaf_1205_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1205.profileLo box_1205.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1205_ok
theorem branch_box_1205_nonnegative : ∀ j, 0 ≤ branch_box_1205.lower j ∧ 0 ≤ branch_box_1205.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1205, Box.profileLo, Box.profileHi, box_1205]
theorem leaf_1205_BranchSafe : CertificateConsequences.BranchSafe branch_box_1205 := by
  left; refine ⟨branch_box_1205_nonnegative, ?_⟩
  intro z hz; exact leaf_1205_sound hz

theorem leaf_1214_ok : checkAt 527 1000 box_1214 cert_1214 = true := by
  have h := List.all_eq_true.mp batch_24_04_ok accepted_1214 (by simp [batch_24_04_values])
  exact h
theorem leaf_1214_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1214.profileLo box_1214.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1214_ok
theorem branch_box_1214_nonnegative : ∀ j, 0 ≤ branch_box_1214.lower j ∧ 0 ≤ branch_box_1214.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1214, Box.profileLo, Box.profileHi, box_1214]
theorem leaf_1214_BranchSafe : CertificateConsequences.BranchSafe branch_box_1214 := by
  left; refine ⟨branch_box_1214_nonnegative, ?_⟩
  intro z hz; exact leaf_1214_sound hz

theorem leaf_1216_ok : checkAt 527 1000 box_1216 cert_1216 = true := by
  have h := List.all_eq_true.mp batch_24_05_ok accepted_1216 (by simp [batch_24_05_values])
  exact h
theorem leaf_1216_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1216.profileLo box_1216.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1216_ok
theorem branch_box_1216_nonnegative : ∀ j, 0 ≤ branch_box_1216.lower j ∧ 0 ≤ branch_box_1216.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1216, Box.profileLo, Box.profileHi, box_1216]
theorem leaf_1216_BranchSafe : CertificateConsequences.BranchSafe branch_box_1216 := by
  left; refine ⟨branch_box_1216_nonnegative, ?_⟩
  intro z hz; exact leaf_1216_sound hz

theorem leaf_1220_ok : checkAt 527 1000 box_1220 cert_1220 = true := by
  have h := List.all_eq_true.mp batch_24_06_ok accepted_1220 (by simp [batch_24_06_values])
  exact h
theorem leaf_1220_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1220.profileLo box_1220.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1220_ok
theorem branch_box_1220_nonnegative : ∀ j, 0 ≤ branch_box_1220.lower j ∧ 0 ≤ branch_box_1220.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1220, Box.profileLo, Box.profileHi, box_1220]
theorem leaf_1220_BranchSafe : CertificateConsequences.BranchSafe branch_box_1220 := by
  left; refine ⟨branch_box_1220_nonnegative, ?_⟩
  intro z hz; exact leaf_1220_sound hz

theorem leaf_1222_ok : checkAt 527 1000 box_1222 cert_1222 = true := by
  have h := List.all_eq_true.mp batch_24_07_ok accepted_1222 (by simp [batch_24_07_values])
  exact h
theorem leaf_1222_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1222.profileLo box_1222.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1222_ok
theorem branch_box_1222_nonnegative : ∀ j, 0 ≤ branch_box_1222.lower j ∧ 0 ≤ branch_box_1222.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1222, Box.profileLo, Box.profileHi, box_1222]
theorem leaf_1222_BranchSafe : CertificateConsequences.BranchSafe branch_box_1222 := by
  left; refine ⟨branch_box_1222_nonnegative, ?_⟩
  intro z hz; exact leaf_1222_sound hz

theorem leaf_1224_ok : checkAt 527 1000 box_1224 cert_1224 = true := by
  have h := List.all_eq_true.mp batch_24_08_ok accepted_1224 (by simp [batch_24_08_values])
  exact h
theorem leaf_1224_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1224.profileLo box_1224.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1224_ok
theorem branch_box_1224_nonnegative : ∀ j, 0 ≤ branch_box_1224.lower j ∧ 0 ≤ branch_box_1224.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1224, Box.profileLo, Box.profileHi, box_1224]
theorem leaf_1224_BranchSafe : CertificateConsequences.BranchSafe branch_box_1224 := by
  left; refine ⟨branch_box_1224_nonnegative, ?_⟩
  intro z hz; exact leaf_1224_sound hz

theorem leaf_1226_ok : checkAt 527 1000 box_1226 cert_1226 = true := by
  have h := List.all_eq_true.mp batch_24_09_ok accepted_1226 (by simp [batch_24_09_values])
  exact h
theorem leaf_1226_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1226.profileLo box_1226.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1226_ok
theorem branch_box_1226_nonnegative : ∀ j, 0 ≤ branch_box_1226.lower j ∧ 0 ≤ branch_box_1226.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1226, Box.profileLo, Box.profileHi, box_1226]
theorem leaf_1226_BranchSafe : CertificateConsequences.BranchSafe branch_box_1226 := by
  left; refine ⟨branch_box_1226_nonnegative, ?_⟩
  intro z hz; exact leaf_1226_sound hz

theorem leaf_1227_ok : checkAt 527 1000 box_1227 cert_1227 = true := by
  have h := List.all_eq_true.mp batch_24_10_ok accepted_1227 (by simp [batch_24_10_values])
  exact h
theorem leaf_1227_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1227.profileLo box_1227.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1227_ok
theorem branch_box_1227_nonnegative : ∀ j, 0 ≤ branch_box_1227.lower j ∧ 0 ≤ branch_box_1227.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1227, Box.profileLo, Box.profileHi, box_1227]
theorem leaf_1227_BranchSafe : CertificateConsequences.BranchSafe branch_box_1227 := by
  left; refine ⟨branch_box_1227_nonnegative, ?_⟩
  intro z hz; exact leaf_1227_sound hz

theorem leaf_1229_ok : checkAt 527 1000 box_1229 cert_1229 = true := by
  have h := List.all_eq_true.mp batch_24_11_ok accepted_1229 (by simp [batch_24_11_values])
  exact h
theorem leaf_1229_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1229.profileLo box_1229.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1229_ok
theorem branch_box_1229_nonnegative : ∀ j, 0 ≤ branch_box_1229.lower j ∧ 0 ≤ branch_box_1229.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1229, Box.profileLo, Box.profileHi, box_1229]
theorem leaf_1229_BranchSafe : CertificateConsequences.BranchSafe branch_box_1229 := by
  left; refine ⟨branch_box_1229_nonnegative, ?_⟩
  intro z hz; exact leaf_1229_sound hz

theorem leaf_1231_ok : checkAt 527 1000 box_1231 cert_1231 = true := by
  have h := List.all_eq_true.mp batch_24_12_ok accepted_1231 (by simp [batch_24_12_values])
  exact h
theorem leaf_1231_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1231.profileLo box_1231.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1231_ok
theorem branch_box_1231_nonnegative : ∀ j, 0 ≤ branch_box_1231.lower j ∧ 0 ≤ branch_box_1231.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1231, Box.profileLo, Box.profileHi, box_1231]
theorem leaf_1231_BranchSafe : CertificateConsequences.BranchSafe branch_box_1231 := by
  left; refine ⟨branch_box_1231_nonnegative, ?_⟩
  intro z hz; exact leaf_1231_sound hz

theorem leaf_1234_ok : checkAt 527 1000 box_1234 cert_1234 = true := by
  have h := List.all_eq_true.mp batch_24_13_ok accepted_1234 (by simp [batch_24_13_values])
  exact h
theorem leaf_1234_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1234.profileLo box_1234.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1234_ok
theorem branch_box_1234_nonnegative : ∀ j, 0 ≤ branch_box_1234.lower j ∧ 0 ≤ branch_box_1234.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1234, Box.profileLo, Box.profileHi, box_1234]
theorem leaf_1234_BranchSafe : CertificateConsequences.BranchSafe branch_box_1234 := by
  left; refine ⟨branch_box_1234_nonnegative, ?_⟩
  intro z hz; exact leaf_1234_sound hz

theorem leaf_1236_ok : checkAt 527 1000 box_1236 cert_1236 = true := by
  have h := List.all_eq_true.mp batch_24_14_ok accepted_1236 (by simp [batch_24_14_values])
  exact h
theorem leaf_1236_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1236.profileLo box_1236.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1236_ok
theorem branch_box_1236_nonnegative : ∀ j, 0 ≤ branch_box_1236.lower j ∧ 0 ≤ branch_box_1236.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1236, Box.profileLo, Box.profileHi, box_1236]
theorem leaf_1236_BranchSafe : CertificateConsequences.BranchSafe branch_box_1236 := by
  left; refine ⟨branch_box_1236_nonnegative, ?_⟩
  intro z hz; exact leaf_1236_sound hz

theorem leaf_1237_ok : checkAt 527 1000 box_1237 cert_1237 = true := by
  have h := List.all_eq_true.mp batch_24_15_ok accepted_1237 (by simp [batch_24_15_values])
  exact h
theorem leaf_1237_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1237.profileLo box_1237.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1237_ok
theorem branch_box_1237_nonnegative : ∀ j, 0 ≤ branch_box_1237.lower j ∧ 0 ≤ branch_box_1237.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1237, Box.profileLo, Box.profileHi, box_1237]
theorem leaf_1237_BranchSafe : CertificateConsequences.BranchSafe branch_box_1237 := by
  left; refine ⟨branch_box_1237_nonnegative, ?_⟩
  intro z hz; exact leaf_1237_sound hz

theorem leaf_1242_ok : checkAt 527 1000 box_1242 cert_1242 = true := by
  have h := List.all_eq_true.mp batch_24_16_ok accepted_1242 (by simp [batch_24_16_values])
  exact h
theorem leaf_1242_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1242.profileLo box_1242.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1242_ok
theorem branch_box_1242_nonnegative : ∀ j, 0 ≤ branch_box_1242.lower j ∧ 0 ≤ branch_box_1242.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1242, Box.profileLo, Box.profileHi, box_1242]
theorem leaf_1242_BranchSafe : CertificateConsequences.BranchSafe branch_box_1242 := by
  left; refine ⟨branch_box_1242_nonnegative, ?_⟩
  intro z hz; exact leaf_1242_sound hz

theorem leaf_1244_ok : checkAt 527 1000 box_1244 cert_1244 = true := by
  have h := List.all_eq_true.mp batch_24_17_ok accepted_1244 (by simp [batch_24_17_values])
  exact h
theorem leaf_1244_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1244.profileLo box_1244.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1244_ok
theorem branch_box_1244_nonnegative : ∀ j, 0 ≤ branch_box_1244.lower j ∧ 0 ≤ branch_box_1244.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1244, Box.profileLo, Box.profileHi, box_1244]
theorem leaf_1244_BranchSafe : CertificateConsequences.BranchSafe branch_box_1244 := by
  left; refine ⟨branch_box_1244_nonnegative, ?_⟩
  intro z hz; exact leaf_1244_sound hz

theorem leaf_1246_ok : checkAt 527 1000 box_1246 cert_1246 = true := by
  have h := List.all_eq_true.mp batch_24_18_ok accepted_1246 (by simp [batch_24_18_values])
  exact h
theorem leaf_1246_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1246.profileLo box_1246.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1246_ok
theorem branch_box_1246_nonnegative : ∀ j, 0 ≤ branch_box_1246.lower j ∧ 0 ≤ branch_box_1246.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1246, Box.profileLo, Box.profileHi, box_1246]
theorem leaf_1246_BranchSafe : CertificateConsequences.BranchSafe branch_box_1246 := by
  left; refine ⟨branch_box_1246_nonnegative, ?_⟩
  intro z hz; exact leaf_1246_sound hz

theorem leaf_1248_ok : checkAt 527 1000 box_1248 cert_1248 = true := by
  have h := List.all_eq_true.mp batch_24_19_ok accepted_1248 (by simp [batch_24_19_values])
  exact h
theorem leaf_1248_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1248.profileLo box_1248.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1248_ok
theorem branch_box_1248_nonnegative : ∀ j, 0 ≤ branch_box_1248.lower j ∧ 0 ≤ branch_box_1248.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1248, Box.profileLo, Box.profileHi, box_1248]
theorem leaf_1248_BranchSafe : CertificateConsequences.BranchSafe branch_box_1248 := by
  left; refine ⟨branch_box_1248_nonnegative, ?_⟩
  intro z hz; exact leaf_1248_sound hz

#print axioms batch_24_00_ok
#print axioms leaf_1200_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
