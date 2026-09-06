import PeaceableQueens.UpperBound.Generated.Even.CoreScaled05Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_05_00_values : List Bool := [accepted_250]
theorem batch_05_00_ok : batch_05_00_values.all id = true := by decide

def batch_05_01_values : List Bool := [accepted_251]
theorem batch_05_01_ok : batch_05_01_values.all id = true := by decide

def batch_05_02_values : List Bool := [accepted_254]
theorem batch_05_02_ok : batch_05_02_values.all id = true := by decide

def batch_05_03_values : List Bool := [accepted_256]
theorem batch_05_03_ok : batch_05_03_values.all id = true := by decide

def batch_05_04_values : List Bool := [accepted_258]
theorem batch_05_04_ok : batch_05_04_values.all id = true := by decide

def batch_05_05_values : List Bool := [accepted_260]
theorem batch_05_05_ok : batch_05_05_values.all id = true := by decide

def batch_05_06_values : List Bool := [accepted_264]
theorem batch_05_06_ok : batch_05_06_values.all id = true := by decide

def batch_05_07_values : List Bool := [accepted_267]
theorem batch_05_07_ok : batch_05_07_values.all id = true := by decide

def batch_05_08_values : List Bool := [accepted_269]
theorem batch_05_08_ok : batch_05_08_values.all id = true := by decide

def batch_05_09_values : List Bool := [accepted_273]
theorem batch_05_09_ok : batch_05_09_values.all id = true := by decide

def batch_05_10_values : List Bool := [accepted_277]
theorem batch_05_10_ok : batch_05_10_values.all id = true := by decide

def batch_05_11_values : List Bool := [accepted_279]
theorem batch_05_11_ok : batch_05_11_values.all id = true := by decide

def batch_05_12_values : List Bool := [accepted_281]
theorem batch_05_12_ok : batch_05_12_values.all id = true := by decide

def batch_05_13_values : List Bool := [accepted_285]
theorem batch_05_13_ok : batch_05_13_values.all id = true := by decide

def batch_05_14_values : List Bool := [accepted_287]
theorem batch_05_14_ok : batch_05_14_values.all id = true := by decide

def batch_05_15_values : List Bool := [accepted_289]
theorem batch_05_15_ok : batch_05_15_values.all id = true := by decide

def batch_05_16_values : List Bool := [accepted_291]
theorem batch_05_16_ok : batch_05_16_values.all id = true := by decide

def batch_05_17_values : List Bool := [accepted_293]
theorem batch_05_17_ok : batch_05_17_values.all id = true := by decide

def batch_05_18_values : List Bool := [accepted_295]
theorem batch_05_18_ok : batch_05_18_values.all id = true := by decide

def batch_05_19_values : List Bool := [accepted_298]
theorem batch_05_19_ok : batch_05_19_values.all id = true := by decide

def batch_05_20_values : List Bool := [accepted_299]
theorem batch_05_20_ok : batch_05_20_values.all id = true := by decide

theorem leaf_250_ok : checkAt 527 1000 box_250 cert_250 = true := by
  have h := List.all_eq_true.mp batch_05_00_ok accepted_250 (by simp [batch_05_00_values])
  exact h
theorem leaf_250_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_250.profileLo box_250.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_250_ok
theorem branch_box_250_nonnegative : ∀ j, 0 ≤ branch_box_250.lower j ∧ 0 ≤ branch_box_250.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_250, Box.profileLo, Box.profileHi, box_250]
theorem leaf_250_BranchSafe : CertificateConsequences.BranchSafe branch_box_250 := by
  left; refine ⟨branch_box_250_nonnegative, ?_⟩
  intro z hz; exact leaf_250_sound hz

theorem leaf_251_ok : checkAt 527 1000 box_251 cert_251 = true := by
  have h := List.all_eq_true.mp batch_05_01_ok accepted_251 (by simp [batch_05_01_values])
  exact h
theorem leaf_251_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_251.profileLo box_251.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_251_ok
theorem branch_box_251_nonnegative : ∀ j, 0 ≤ branch_box_251.lower j ∧ 0 ≤ branch_box_251.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_251, Box.profileLo, Box.profileHi, box_251]
theorem leaf_251_BranchSafe : CertificateConsequences.BranchSafe branch_box_251 := by
  left; refine ⟨branch_box_251_nonnegative, ?_⟩
  intro z hz; exact leaf_251_sound hz

theorem leaf_254_ok : checkAt 527 1000 box_254 cert_254 = true := by
  have h := List.all_eq_true.mp batch_05_02_ok accepted_254 (by simp [batch_05_02_values])
  exact h
theorem leaf_254_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_254.profileLo box_254.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_254_ok
theorem branch_box_254_nonnegative : ∀ j, 0 ≤ branch_box_254.lower j ∧ 0 ≤ branch_box_254.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_254, Box.profileLo, Box.profileHi, box_254]
theorem leaf_254_BranchSafe : CertificateConsequences.BranchSafe branch_box_254 := by
  left; refine ⟨branch_box_254_nonnegative, ?_⟩
  intro z hz; exact leaf_254_sound hz

theorem leaf_256_ok : checkAt 527 1000 box_256 cert_256 = true := by
  have h := List.all_eq_true.mp batch_05_03_ok accepted_256 (by simp [batch_05_03_values])
  exact h
theorem leaf_256_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_256.profileLo box_256.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_256_ok
theorem branch_box_256_nonnegative : ∀ j, 0 ≤ branch_box_256.lower j ∧ 0 ≤ branch_box_256.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_256, Box.profileLo, Box.profileHi, box_256]
theorem leaf_256_BranchSafe : CertificateConsequences.BranchSafe branch_box_256 := by
  left; refine ⟨branch_box_256_nonnegative, ?_⟩
  intro z hz; exact leaf_256_sound hz

theorem leaf_258_ok : checkAt 527 1000 box_258 cert_258 = true := by
  have h := List.all_eq_true.mp batch_05_04_ok accepted_258 (by simp [batch_05_04_values])
  exact h
theorem leaf_258_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_258.profileLo box_258.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_258_ok
theorem branch_box_258_nonnegative : ∀ j, 0 ≤ branch_box_258.lower j ∧ 0 ≤ branch_box_258.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_258, Box.profileLo, Box.profileHi, box_258]
theorem leaf_258_BranchSafe : CertificateConsequences.BranchSafe branch_box_258 := by
  left; refine ⟨branch_box_258_nonnegative, ?_⟩
  intro z hz; exact leaf_258_sound hz

theorem leaf_260_ok : checkAt 527 1000 box_260 cert_260 = true := by
  have h := List.all_eq_true.mp batch_05_05_ok accepted_260 (by simp [batch_05_05_values])
  exact h
theorem leaf_260_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_260.profileLo box_260.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_260_ok
theorem branch_box_260_nonnegative : ∀ j, 0 ≤ branch_box_260.lower j ∧ 0 ≤ branch_box_260.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_260, Box.profileLo, Box.profileHi, box_260]
theorem leaf_260_BranchSafe : CertificateConsequences.BranchSafe branch_box_260 := by
  left; refine ⟨branch_box_260_nonnegative, ?_⟩
  intro z hz; exact leaf_260_sound hz

theorem leaf_264_ok : checkAt 527 1000 box_264 cert_264 = true := by
  have h := List.all_eq_true.mp batch_05_06_ok accepted_264 (by simp [batch_05_06_values])
  exact h
theorem leaf_264_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_264.profileLo box_264.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_264_ok
theorem branch_box_264_nonnegative : ∀ j, 0 ≤ branch_box_264.lower j ∧ 0 ≤ branch_box_264.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_264, Box.profileLo, Box.profileHi, box_264]
theorem leaf_264_BranchSafe : CertificateConsequences.BranchSafe branch_box_264 := by
  left; refine ⟨branch_box_264_nonnegative, ?_⟩
  intro z hz; exact leaf_264_sound hz

theorem leaf_267_ok : checkAt 527 1000 box_267 cert_267 = true := by
  have h := List.all_eq_true.mp batch_05_07_ok accepted_267 (by simp [batch_05_07_values])
  exact h
theorem leaf_267_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_267.profileLo box_267.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_267_ok
theorem branch_box_267_nonnegative : ∀ j, 0 ≤ branch_box_267.lower j ∧ 0 ≤ branch_box_267.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_267, Box.profileLo, Box.profileHi, box_267]
theorem leaf_267_BranchSafe : CertificateConsequences.BranchSafe branch_box_267 := by
  left; refine ⟨branch_box_267_nonnegative, ?_⟩
  intro z hz; exact leaf_267_sound hz

theorem leaf_269_ok : checkAt 527 1000 box_269 cert_269 = true := by
  have h := List.all_eq_true.mp batch_05_08_ok accepted_269 (by simp [batch_05_08_values])
  exact h
theorem leaf_269_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_269.profileLo box_269.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_269_ok
theorem branch_box_269_nonnegative : ∀ j, 0 ≤ branch_box_269.lower j ∧ 0 ≤ branch_box_269.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_269, Box.profileLo, Box.profileHi, box_269]
theorem leaf_269_BranchSafe : CertificateConsequences.BranchSafe branch_box_269 := by
  left; refine ⟨branch_box_269_nonnegative, ?_⟩
  intro z hz; exact leaf_269_sound hz

theorem leaf_273_ok : checkAt 527 1000 box_273 cert_273 = true := by
  have h := List.all_eq_true.mp batch_05_09_ok accepted_273 (by simp [batch_05_09_values])
  exact h
theorem leaf_273_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_273.profileLo box_273.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_273_ok
theorem branch_box_273_nonnegative : ∀ j, 0 ≤ branch_box_273.lower j ∧ 0 ≤ branch_box_273.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_273, Box.profileLo, Box.profileHi, box_273]
theorem leaf_273_BranchSafe : CertificateConsequences.BranchSafe branch_box_273 := by
  left; refine ⟨branch_box_273_nonnegative, ?_⟩
  intro z hz; exact leaf_273_sound hz

theorem leaf_277_ok : checkAt 527 1000 box_277 cert_277 = true := by
  have h := List.all_eq_true.mp batch_05_10_ok accepted_277 (by simp [batch_05_10_values])
  exact h
theorem leaf_277_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_277.profileLo box_277.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_277_ok
theorem branch_box_277_nonnegative : ∀ j, 0 ≤ branch_box_277.lower j ∧ 0 ≤ branch_box_277.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_277, Box.profileLo, Box.profileHi, box_277]
theorem leaf_277_BranchSafe : CertificateConsequences.BranchSafe branch_box_277 := by
  left; refine ⟨branch_box_277_nonnegative, ?_⟩
  intro z hz; exact leaf_277_sound hz

theorem leaf_279_ok : checkAt 527 1000 box_279 cert_279 = true := by
  have h := List.all_eq_true.mp batch_05_11_ok accepted_279 (by simp [batch_05_11_values])
  exact h
theorem leaf_279_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_279.profileLo box_279.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_279_ok
theorem branch_box_279_nonnegative : ∀ j, 0 ≤ branch_box_279.lower j ∧ 0 ≤ branch_box_279.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_279, Box.profileLo, Box.profileHi, box_279]
theorem leaf_279_BranchSafe : CertificateConsequences.BranchSafe branch_box_279 := by
  left; refine ⟨branch_box_279_nonnegative, ?_⟩
  intro z hz; exact leaf_279_sound hz

theorem leaf_281_ok : checkAt 527 1000 box_281 cert_281 = true := by
  have h := List.all_eq_true.mp batch_05_12_ok accepted_281 (by simp [batch_05_12_values])
  exact h
theorem leaf_281_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_281.profileLo box_281.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_281_ok
theorem branch_box_281_nonnegative : ∀ j, 0 ≤ branch_box_281.lower j ∧ 0 ≤ branch_box_281.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_281, Box.profileLo, Box.profileHi, box_281]
theorem leaf_281_BranchSafe : CertificateConsequences.BranchSafe branch_box_281 := by
  left; refine ⟨branch_box_281_nonnegative, ?_⟩
  intro z hz; exact leaf_281_sound hz

theorem leaf_285_ok : checkAt 527 1000 box_285 cert_285 = true := by
  have h := List.all_eq_true.mp batch_05_13_ok accepted_285 (by simp [batch_05_13_values])
  exact h
theorem leaf_285_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_285.profileLo box_285.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_285_ok
theorem branch_box_285_nonnegative : ∀ j, 0 ≤ branch_box_285.lower j ∧ 0 ≤ branch_box_285.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_285, Box.profileLo, Box.profileHi, box_285]
theorem leaf_285_BranchSafe : CertificateConsequences.BranchSafe branch_box_285 := by
  left; refine ⟨branch_box_285_nonnegative, ?_⟩
  intro z hz; exact leaf_285_sound hz

theorem leaf_287_ok : checkAt 527 1000 box_287 cert_287 = true := by
  have h := List.all_eq_true.mp batch_05_14_ok accepted_287 (by simp [batch_05_14_values])
  exact h
theorem leaf_287_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_287.profileLo box_287.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_287_ok
theorem branch_box_287_nonnegative : ∀ j, 0 ≤ branch_box_287.lower j ∧ 0 ≤ branch_box_287.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_287, Box.profileLo, Box.profileHi, box_287]
theorem leaf_287_BranchSafe : CertificateConsequences.BranchSafe branch_box_287 := by
  left; refine ⟨branch_box_287_nonnegative, ?_⟩
  intro z hz; exact leaf_287_sound hz

theorem leaf_289_ok : checkAt 527 1000 box_289 cert_289 = true := by
  have h := List.all_eq_true.mp batch_05_15_ok accepted_289 (by simp [batch_05_15_values])
  exact h
theorem leaf_289_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_289.profileLo box_289.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_289_ok
theorem branch_box_289_nonnegative : ∀ j, 0 ≤ branch_box_289.lower j ∧ 0 ≤ branch_box_289.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_289, Box.profileLo, Box.profileHi, box_289]
theorem leaf_289_BranchSafe : CertificateConsequences.BranchSafe branch_box_289 := by
  left; refine ⟨branch_box_289_nonnegative, ?_⟩
  intro z hz; exact leaf_289_sound hz

theorem leaf_291_ok : checkAt 527 1000 box_291 cert_291 = true := by
  have h := List.all_eq_true.mp batch_05_16_ok accepted_291 (by simp [batch_05_16_values])
  exact h
theorem leaf_291_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_291.profileLo box_291.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_291_ok
theorem branch_box_291_nonnegative : ∀ j, 0 ≤ branch_box_291.lower j ∧ 0 ≤ branch_box_291.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_291, Box.profileLo, Box.profileHi, box_291]
theorem leaf_291_BranchSafe : CertificateConsequences.BranchSafe branch_box_291 := by
  left; refine ⟨branch_box_291_nonnegative, ?_⟩
  intro z hz; exact leaf_291_sound hz

theorem leaf_293_ok : checkAt 527 1000 box_293 cert_293 = true := by
  have h := List.all_eq_true.mp batch_05_17_ok accepted_293 (by simp [batch_05_17_values])
  exact h
theorem leaf_293_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_293.profileLo box_293.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_293_ok
theorem branch_box_293_nonnegative : ∀ j, 0 ≤ branch_box_293.lower j ∧ 0 ≤ branch_box_293.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_293, Box.profileLo, Box.profileHi, box_293]
theorem leaf_293_BranchSafe : CertificateConsequences.BranchSafe branch_box_293 := by
  left; refine ⟨branch_box_293_nonnegative, ?_⟩
  intro z hz; exact leaf_293_sound hz

theorem leaf_295_ok : checkAt 527 1000 box_295 cert_295 = true := by
  have h := List.all_eq_true.mp batch_05_18_ok accepted_295 (by simp [batch_05_18_values])
  exact h
theorem leaf_295_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_295.profileLo box_295.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_295_ok
theorem branch_box_295_nonnegative : ∀ j, 0 ≤ branch_box_295.lower j ∧ 0 ≤ branch_box_295.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_295, Box.profileLo, Box.profileHi, box_295]
theorem leaf_295_BranchSafe : CertificateConsequences.BranchSafe branch_box_295 := by
  left; refine ⟨branch_box_295_nonnegative, ?_⟩
  intro z hz; exact leaf_295_sound hz

theorem leaf_298_ok : checkAt 527 1000 box_298 cert_298 = true := by
  have h := List.all_eq_true.mp batch_05_19_ok accepted_298 (by simp [batch_05_19_values])
  exact h
theorem leaf_298_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_298.profileLo box_298.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_298_ok
theorem branch_box_298_nonnegative : ∀ j, 0 ≤ branch_box_298.lower j ∧ 0 ≤ branch_box_298.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_298, Box.profileLo, Box.profileHi, box_298]
theorem leaf_298_BranchSafe : CertificateConsequences.BranchSafe branch_box_298 := by
  left; refine ⟨branch_box_298_nonnegative, ?_⟩
  intro z hz; exact leaf_298_sound hz

theorem leaf_299_ok : checkAt 527 1000 box_299 cert_299 = true := by
  have h := List.all_eq_true.mp batch_05_20_ok accepted_299 (by simp [batch_05_20_values])
  exact h
theorem leaf_299_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_299.profileLo box_299.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_299_ok
theorem branch_box_299_nonnegative : ∀ j, 0 ≤ branch_box_299.lower j ∧ 0 ≤ branch_box_299.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_299, Box.profileLo, Box.profileHi, box_299]
theorem leaf_299_BranchSafe : CertificateConsequences.BranchSafe branch_box_299 := by
  left; refine ⟨branch_box_299_nonnegative, ?_⟩
  intro z hz; exact leaf_299_sound hz

#print axioms batch_05_00_ok
#print axioms leaf_250_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
