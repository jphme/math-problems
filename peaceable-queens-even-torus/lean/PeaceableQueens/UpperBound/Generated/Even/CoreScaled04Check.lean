import PeaceableQueens.UpperBound.Generated.Even.CoreScaled04Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_04_00_values : List Bool := [accepted_202]
theorem batch_04_00_ok : batch_04_00_values.all id = true := by decide

def batch_04_01_values : List Bool := [accepted_204]
theorem batch_04_01_ok : batch_04_01_values.all id = true := by decide

def batch_04_02_values : List Bool := [accepted_206]
theorem batch_04_02_ok : batch_04_02_values.all id = true := by decide

def batch_04_03_values : List Bool := [accepted_208]
theorem batch_04_03_ok : batch_04_03_values.all id = true := by decide

def batch_04_04_values : List Bool := [accepted_212]
theorem batch_04_04_ok : batch_04_04_values.all id = true := by decide

def batch_04_05_values : List Bool := [accepted_214]
theorem batch_04_05_ok : batch_04_05_values.all id = true := by decide

def batch_04_06_values : List Bool := [accepted_215]
theorem batch_04_06_ok : batch_04_06_values.all id = true := by decide

def batch_04_07_values : List Bool := [accepted_217]
theorem batch_04_07_ok : batch_04_07_values.all id = true := by decide

def batch_04_08_values : List Bool := [accepted_219]
theorem batch_04_08_ok : batch_04_08_values.all id = true := by decide

def batch_04_09_values : List Bool := [accepted_224]
theorem batch_04_09_ok : batch_04_09_values.all id = true := by decide

def batch_04_10_values : List Bool := [accepted_229]
theorem batch_04_10_ok : batch_04_10_values.all id = true := by decide

def batch_04_11_values : List Bool := [accepted_236]
theorem batch_04_11_ok : batch_04_11_values.all id = true := by decide

def batch_04_12_values : List Bool := [accepted_238]
theorem batch_04_12_ok : batch_04_12_values.all id = true := by decide

def batch_04_13_values : List Bool := [accepted_239]
theorem batch_04_13_ok : batch_04_13_values.all id = true := by decide

def batch_04_14_values : List Bool := [accepted_242]
theorem batch_04_14_ok : batch_04_14_values.all id = true := by decide

def batch_04_15_values : List Bool := [accepted_244]
theorem batch_04_15_ok : batch_04_15_values.all id = true := by decide

def batch_04_16_values : List Bool := [accepted_246]
theorem batch_04_16_ok : batch_04_16_values.all id = true := by decide

def batch_04_17_values : List Bool := [accepted_248]
theorem batch_04_17_ok : batch_04_17_values.all id = true := by decide

theorem leaf_202_ok : checkAt 527 1000 box_202 cert_202 = true := by
  have h := List.all_eq_true.mp batch_04_00_ok accepted_202 (by simp [batch_04_00_values])
  exact h
theorem leaf_202_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_202.profileLo box_202.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_202_ok
theorem branch_box_202_nonnegative : ∀ j, 0 ≤ branch_box_202.lower j ∧ 0 ≤ branch_box_202.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_202, Box.profileLo, Box.profileHi, box_202]
theorem leaf_202_BranchSafe : CertificateConsequences.BranchSafe branch_box_202 := by
  left; refine ⟨branch_box_202_nonnegative, ?_⟩
  intro z hz; exact leaf_202_sound hz

theorem leaf_204_ok : checkAt 527 1000 box_204 cert_204 = true := by
  have h := List.all_eq_true.mp batch_04_01_ok accepted_204 (by simp [batch_04_01_values])
  exact h
theorem leaf_204_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_204.profileLo box_204.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_204_ok
theorem branch_box_204_nonnegative : ∀ j, 0 ≤ branch_box_204.lower j ∧ 0 ≤ branch_box_204.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_204, Box.profileLo, Box.profileHi, box_204]
theorem leaf_204_BranchSafe : CertificateConsequences.BranchSafe branch_box_204 := by
  left; refine ⟨branch_box_204_nonnegative, ?_⟩
  intro z hz; exact leaf_204_sound hz

theorem leaf_206_ok : checkAt 527 1000 box_206 cert_206 = true := by
  have h := List.all_eq_true.mp batch_04_02_ok accepted_206 (by simp [batch_04_02_values])
  exact h
theorem leaf_206_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_206.profileLo box_206.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_206_ok
theorem branch_box_206_nonnegative : ∀ j, 0 ≤ branch_box_206.lower j ∧ 0 ≤ branch_box_206.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_206, Box.profileLo, Box.profileHi, box_206]
theorem leaf_206_BranchSafe : CertificateConsequences.BranchSafe branch_box_206 := by
  left; refine ⟨branch_box_206_nonnegative, ?_⟩
  intro z hz; exact leaf_206_sound hz

theorem leaf_208_ok : checkAt 527 1000 box_208 cert_208 = true := by
  have h := List.all_eq_true.mp batch_04_03_ok accepted_208 (by simp [batch_04_03_values])
  exact h
theorem leaf_208_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_208.profileLo box_208.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_208_ok
theorem branch_box_208_nonnegative : ∀ j, 0 ≤ branch_box_208.lower j ∧ 0 ≤ branch_box_208.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_208, Box.profileLo, Box.profileHi, box_208]
theorem leaf_208_BranchSafe : CertificateConsequences.BranchSafe branch_box_208 := by
  left; refine ⟨branch_box_208_nonnegative, ?_⟩
  intro z hz; exact leaf_208_sound hz

theorem leaf_212_ok : checkAt 527 1000 box_212 cert_212 = true := by
  have h := List.all_eq_true.mp batch_04_04_ok accepted_212 (by simp [batch_04_04_values])
  exact h
theorem leaf_212_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_212.profileLo box_212.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_212_ok
theorem branch_box_212_nonnegative : ∀ j, 0 ≤ branch_box_212.lower j ∧ 0 ≤ branch_box_212.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_212, Box.profileLo, Box.profileHi, box_212]
theorem leaf_212_BranchSafe : CertificateConsequences.BranchSafe branch_box_212 := by
  left; refine ⟨branch_box_212_nonnegative, ?_⟩
  intro z hz; exact leaf_212_sound hz

theorem leaf_214_ok : checkAt 527 1000 box_214 cert_214 = true := by
  have h := List.all_eq_true.mp batch_04_05_ok accepted_214 (by simp [batch_04_05_values])
  exact h
theorem leaf_214_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_214.profileLo box_214.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_214_ok
theorem branch_box_214_nonnegative : ∀ j, 0 ≤ branch_box_214.lower j ∧ 0 ≤ branch_box_214.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_214, Box.profileLo, Box.profileHi, box_214]
theorem leaf_214_BranchSafe : CertificateConsequences.BranchSafe branch_box_214 := by
  left; refine ⟨branch_box_214_nonnegative, ?_⟩
  intro z hz; exact leaf_214_sound hz

theorem leaf_215_ok : checkAt 527 1000 box_215 cert_215 = true := by
  have h := List.all_eq_true.mp batch_04_06_ok accepted_215 (by simp [batch_04_06_values])
  exact h
theorem leaf_215_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_215.profileLo box_215.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_215_ok
theorem branch_box_215_nonnegative : ∀ j, 0 ≤ branch_box_215.lower j ∧ 0 ≤ branch_box_215.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_215, Box.profileLo, Box.profileHi, box_215]
theorem leaf_215_BranchSafe : CertificateConsequences.BranchSafe branch_box_215 := by
  left; refine ⟨branch_box_215_nonnegative, ?_⟩
  intro z hz; exact leaf_215_sound hz

theorem leaf_217_ok : checkAt 527 1000 box_217 cert_217 = true := by
  have h := List.all_eq_true.mp batch_04_07_ok accepted_217 (by simp [batch_04_07_values])
  exact h
theorem leaf_217_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_217.profileLo box_217.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_217_ok
theorem branch_box_217_nonnegative : ∀ j, 0 ≤ branch_box_217.lower j ∧ 0 ≤ branch_box_217.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_217, Box.profileLo, Box.profileHi, box_217]
theorem leaf_217_BranchSafe : CertificateConsequences.BranchSafe branch_box_217 := by
  left; refine ⟨branch_box_217_nonnegative, ?_⟩
  intro z hz; exact leaf_217_sound hz

theorem leaf_219_ok : checkAt 527 1000 box_219 cert_219 = true := by
  have h := List.all_eq_true.mp batch_04_08_ok accepted_219 (by simp [batch_04_08_values])
  exact h
theorem leaf_219_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_219.profileLo box_219.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_219_ok
theorem branch_box_219_nonnegative : ∀ j, 0 ≤ branch_box_219.lower j ∧ 0 ≤ branch_box_219.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_219, Box.profileLo, Box.profileHi, box_219]
theorem leaf_219_BranchSafe : CertificateConsequences.BranchSafe branch_box_219 := by
  left; refine ⟨branch_box_219_nonnegative, ?_⟩
  intro z hz; exact leaf_219_sound hz

theorem leaf_224_ok : checkAt 527 1000 box_224 cert_224 = true := by
  have h := List.all_eq_true.mp batch_04_09_ok accepted_224 (by simp [batch_04_09_values])
  exact h
theorem leaf_224_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_224.profileLo box_224.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_224_ok
theorem branch_box_224_nonnegative : ∀ j, 0 ≤ branch_box_224.lower j ∧ 0 ≤ branch_box_224.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_224, Box.profileLo, Box.profileHi, box_224]
theorem leaf_224_BranchSafe : CertificateConsequences.BranchSafe branch_box_224 := by
  left; refine ⟨branch_box_224_nonnegative, ?_⟩
  intro z hz; exact leaf_224_sound hz

theorem leaf_229_ok : checkAt 527 1000 box_229 cert_229 = true := by
  have h := List.all_eq_true.mp batch_04_10_ok accepted_229 (by simp [batch_04_10_values])
  exact h
theorem leaf_229_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_229.profileLo box_229.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_229_ok
theorem branch_box_229_nonnegative : ∀ j, 0 ≤ branch_box_229.lower j ∧ 0 ≤ branch_box_229.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_229, Box.profileLo, Box.profileHi, box_229]
theorem leaf_229_BranchSafe : CertificateConsequences.BranchSafe branch_box_229 := by
  left; refine ⟨branch_box_229_nonnegative, ?_⟩
  intro z hz; exact leaf_229_sound hz

theorem leaf_236_ok : checkAt 527 1000 box_236 cert_236 = true := by
  have h := List.all_eq_true.mp batch_04_11_ok accepted_236 (by simp [batch_04_11_values])
  exact h
theorem leaf_236_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_236.profileLo box_236.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_236_ok
theorem branch_box_236_nonnegative : ∀ j, 0 ≤ branch_box_236.lower j ∧ 0 ≤ branch_box_236.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_236, Box.profileLo, Box.profileHi, box_236]
theorem leaf_236_BranchSafe : CertificateConsequences.BranchSafe branch_box_236 := by
  left; refine ⟨branch_box_236_nonnegative, ?_⟩
  intro z hz; exact leaf_236_sound hz

theorem leaf_238_ok : checkAt 527 1000 box_238 cert_238 = true := by
  have h := List.all_eq_true.mp batch_04_12_ok accepted_238 (by simp [batch_04_12_values])
  exact h
theorem leaf_238_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_238.profileLo box_238.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_238_ok
theorem branch_box_238_nonnegative : ∀ j, 0 ≤ branch_box_238.lower j ∧ 0 ≤ branch_box_238.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_238, Box.profileLo, Box.profileHi, box_238]
theorem leaf_238_BranchSafe : CertificateConsequences.BranchSafe branch_box_238 := by
  left; refine ⟨branch_box_238_nonnegative, ?_⟩
  intro z hz; exact leaf_238_sound hz

theorem leaf_239_ok : checkAt 527 1000 box_239 cert_239 = true := by
  have h := List.all_eq_true.mp batch_04_13_ok accepted_239 (by simp [batch_04_13_values])
  exact h
theorem leaf_239_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_239.profileLo box_239.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_239_ok
theorem branch_box_239_nonnegative : ∀ j, 0 ≤ branch_box_239.lower j ∧ 0 ≤ branch_box_239.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_239, Box.profileLo, Box.profileHi, box_239]
theorem leaf_239_BranchSafe : CertificateConsequences.BranchSafe branch_box_239 := by
  left; refine ⟨branch_box_239_nonnegative, ?_⟩
  intro z hz; exact leaf_239_sound hz

theorem leaf_242_ok : checkAt 527 1000 box_242 cert_242 = true := by
  have h := List.all_eq_true.mp batch_04_14_ok accepted_242 (by simp [batch_04_14_values])
  exact h
theorem leaf_242_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_242.profileLo box_242.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_242_ok
theorem branch_box_242_nonnegative : ∀ j, 0 ≤ branch_box_242.lower j ∧ 0 ≤ branch_box_242.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_242, Box.profileLo, Box.profileHi, box_242]
theorem leaf_242_BranchSafe : CertificateConsequences.BranchSafe branch_box_242 := by
  left; refine ⟨branch_box_242_nonnegative, ?_⟩
  intro z hz; exact leaf_242_sound hz

theorem leaf_244_ok : checkAt 527 1000 box_244 cert_244 = true := by
  have h := List.all_eq_true.mp batch_04_15_ok accepted_244 (by simp [batch_04_15_values])
  exact h
theorem leaf_244_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_244.profileLo box_244.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_244_ok
theorem branch_box_244_nonnegative : ∀ j, 0 ≤ branch_box_244.lower j ∧ 0 ≤ branch_box_244.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_244, Box.profileLo, Box.profileHi, box_244]
theorem leaf_244_BranchSafe : CertificateConsequences.BranchSafe branch_box_244 := by
  left; refine ⟨branch_box_244_nonnegative, ?_⟩
  intro z hz; exact leaf_244_sound hz

theorem leaf_246_ok : checkAt 527 1000 box_246 cert_246 = true := by
  have h := List.all_eq_true.mp batch_04_16_ok accepted_246 (by simp [batch_04_16_values])
  exact h
theorem leaf_246_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_246.profileLo box_246.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_246_ok
theorem branch_box_246_nonnegative : ∀ j, 0 ≤ branch_box_246.lower j ∧ 0 ≤ branch_box_246.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_246, Box.profileLo, Box.profileHi, box_246]
theorem leaf_246_BranchSafe : CertificateConsequences.BranchSafe branch_box_246 := by
  left; refine ⟨branch_box_246_nonnegative, ?_⟩
  intro z hz; exact leaf_246_sound hz

theorem leaf_248_ok : checkAt 527 1000 box_248 cert_248 = true := by
  have h := List.all_eq_true.mp batch_04_17_ok accepted_248 (by simp [batch_04_17_values])
  exact h
theorem leaf_248_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_248.profileLo box_248.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_248_ok
theorem branch_box_248_nonnegative : ∀ j, 0 ≤ branch_box_248.lower j ∧ 0 ≤ branch_box_248.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_248, Box.profileLo, Box.profileHi, box_248]
theorem leaf_248_BranchSafe : CertificateConsequences.BranchSafe branch_box_248 := by
  left; refine ⟨branch_box_248_nonnegative, ?_⟩
  intro z hz; exact leaf_248_sound hz

#print axioms batch_04_00_ok
#print axioms leaf_202_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
