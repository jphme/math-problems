import PeaceableQueens.UpperBound.Generated.Even.C527Scaled05Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_05_00_values : List Bool := [accepted_252]
theorem batch_05_00_ok : batch_05_00_values.all id = true := by decide

def batch_05_01_values : List Bool := [accepted_253]
theorem batch_05_01_ok : batch_05_01_values.all id = true := by decide

def batch_05_02_values : List Bool := [accepted_254]
theorem batch_05_02_ok : batch_05_02_values.all id = true := by decide

def batch_05_03_values : List Bool := [accepted_257]
theorem batch_05_03_ok : batch_05_03_values.all id = true := by decide

def batch_05_04_values : List Bool := [accepted_258]
theorem batch_05_04_ok : batch_05_04_values.all id = true := by decide

def batch_05_05_values : List Bool := [accepted_259]
theorem batch_05_05_ok : batch_05_05_values.all id = true := by decide

def batch_05_06_values : List Bool := [accepted_262]
theorem batch_05_06_ok : batch_05_06_values.all id = true := by decide

def batch_05_07_values : List Bool := [accepted_263]
theorem batch_05_07_ok : batch_05_07_values.all id = true := by decide

def batch_05_08_values : List Bool := [accepted_264]
theorem batch_05_08_ok : batch_05_08_values.all id = true := by decide

def batch_05_09_values : List Bool := [accepted_267]
theorem batch_05_09_ok : batch_05_09_values.all id = true := by decide

def batch_05_10_values : List Bool := [accepted_269]
theorem batch_05_10_ok : batch_05_10_values.all id = true := by decide

def batch_05_11_values : List Bool := [accepted_270]
theorem batch_05_11_ok : batch_05_11_values.all id = true := by decide

def batch_05_12_values : List Bool := [accepted_273]
theorem batch_05_12_ok : batch_05_12_values.all id = true := by decide

def batch_05_13_values : List Bool := [accepted_274]
theorem batch_05_13_ok : batch_05_13_values.all id = true := by decide

def batch_05_14_values : List Bool := [accepted_277]
theorem batch_05_14_ok : batch_05_14_values.all id = true := by decide

def batch_05_15_values : List Bool := [accepted_278]
theorem batch_05_15_ok : batch_05_15_values.all id = true := by decide

def batch_05_16_values : List Bool := [accepted_279]
theorem batch_05_16_ok : batch_05_16_values.all id = true := by decide

def batch_05_17_values : List Bool := [accepted_281]
theorem batch_05_17_ok : batch_05_17_values.all id = true := by decide

def batch_05_18_values : List Bool := [accepted_282]
theorem batch_05_18_ok : batch_05_18_values.all id = true := by decide

def batch_05_19_values : List Bool := [accepted_287]
theorem batch_05_19_ok : batch_05_19_values.all id = true := by decide

def batch_05_20_values : List Bool := [accepted_289]
theorem batch_05_20_ok : batch_05_20_values.all id = true := by decide

def batch_05_21_values : List Bool := [accepted_291]
theorem batch_05_21_ok : batch_05_21_values.all id = true := by decide

def batch_05_22_values : List Bool := [accepted_292]
theorem batch_05_22_ok : batch_05_22_values.all id = true := by decide

def batch_05_23_values : List Bool := [accepted_293]
theorem batch_05_23_ok : batch_05_23_values.all id = true := by decide

def batch_05_24_values : List Bool := [accepted_297]
theorem batch_05_24_ok : batch_05_24_values.all id = true := by decide

def batch_05_25_values : List Bool := [accepted_298]
theorem batch_05_25_ok : batch_05_25_values.all id = true := by decide

theorem leaf_252_ok : checkAt 527 1000 box_252 cert_252 = true := by
  have h := List.all_eq_true.mp batch_05_00_ok accepted_252 (by simp [batch_05_00_values])
  exact h
theorem leaf_252_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_252.profileLo box_252.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_252_ok
theorem branch_box_252_nonnegative : ∀ j, 0 ≤ branch_box_252.lower j ∧ 0 ≤ branch_box_252.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_252, Box.profileLo, Box.profileHi, box_252]
theorem leaf_252_BranchSafe : CertificateConsequences.BranchSafe branch_box_252 := by
  left; refine ⟨branch_box_252_nonnegative, ?_⟩
  intro z hz; exact leaf_252_sound hz

theorem leaf_253_ok : checkAt 527 1000 box_253 cert_253 = true := by
  have h := List.all_eq_true.mp batch_05_01_ok accepted_253 (by simp [batch_05_01_values])
  exact h
theorem leaf_253_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_253.profileLo box_253.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_253_ok
theorem branch_box_253_nonnegative : ∀ j, 0 ≤ branch_box_253.lower j ∧ 0 ≤ branch_box_253.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_253, Box.profileLo, Box.profileHi, box_253]
theorem leaf_253_BranchSafe : CertificateConsequences.BranchSafe branch_box_253 := by
  left; refine ⟨branch_box_253_nonnegative, ?_⟩
  intro z hz; exact leaf_253_sound hz

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

theorem leaf_257_ok : checkAt 527 1000 box_257 cert_257 = true := by
  have h := List.all_eq_true.mp batch_05_03_ok accepted_257 (by simp [batch_05_03_values])
  exact h
theorem leaf_257_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_257.profileLo box_257.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_257_ok
theorem branch_box_257_nonnegative : ∀ j, 0 ≤ branch_box_257.lower j ∧ 0 ≤ branch_box_257.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_257, Box.profileLo, Box.profileHi, box_257]
theorem leaf_257_BranchSafe : CertificateConsequences.BranchSafe branch_box_257 := by
  left; refine ⟨branch_box_257_nonnegative, ?_⟩
  intro z hz; exact leaf_257_sound hz

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

theorem leaf_259_ok : checkAt 527 1000 box_259 cert_259 = true := by
  have h := List.all_eq_true.mp batch_05_05_ok accepted_259 (by simp [batch_05_05_values])
  exact h
theorem leaf_259_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_259.profileLo box_259.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_259_ok
theorem branch_box_259_nonnegative : ∀ j, 0 ≤ branch_box_259.lower j ∧ 0 ≤ branch_box_259.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_259, Box.profileLo, Box.profileHi, box_259]
theorem leaf_259_BranchSafe : CertificateConsequences.BranchSafe branch_box_259 := by
  left; refine ⟨branch_box_259_nonnegative, ?_⟩
  intro z hz; exact leaf_259_sound hz

theorem leaf_262_ok : checkAt 527 1000 box_262 cert_262 = true := by
  have h := List.all_eq_true.mp batch_05_06_ok accepted_262 (by simp [batch_05_06_values])
  exact h
theorem leaf_262_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_262.profileLo box_262.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_262_ok
theorem branch_box_262_nonnegative : ∀ j, 0 ≤ branch_box_262.lower j ∧ 0 ≤ branch_box_262.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_262, Box.profileLo, Box.profileHi, box_262]
theorem leaf_262_BranchSafe : CertificateConsequences.BranchSafe branch_box_262 := by
  left; refine ⟨branch_box_262_nonnegative, ?_⟩
  intro z hz; exact leaf_262_sound hz

theorem leaf_263_ok : checkAt 527 1000 box_263 cert_263 = true := by
  have h := List.all_eq_true.mp batch_05_07_ok accepted_263 (by simp [batch_05_07_values])
  exact h
theorem leaf_263_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_263.profileLo box_263.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_263_ok
theorem branch_box_263_nonnegative : ∀ j, 0 ≤ branch_box_263.lower j ∧ 0 ≤ branch_box_263.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_263, Box.profileLo, Box.profileHi, box_263]
theorem leaf_263_BranchSafe : CertificateConsequences.BranchSafe branch_box_263 := by
  left; refine ⟨branch_box_263_nonnegative, ?_⟩
  intro z hz; exact leaf_263_sound hz

theorem leaf_264_ok : checkAt 527 1000 box_264 cert_264 = true := by
  have h := List.all_eq_true.mp batch_05_08_ok accepted_264 (by simp [batch_05_08_values])
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
  have h := List.all_eq_true.mp batch_05_09_ok accepted_267 (by simp [batch_05_09_values])
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
  have h := List.all_eq_true.mp batch_05_10_ok accepted_269 (by simp [batch_05_10_values])
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

theorem leaf_270_ok : checkAt 527 1000 box_270 cert_270 = true := by
  have h := List.all_eq_true.mp batch_05_11_ok accepted_270 (by simp [batch_05_11_values])
  exact h
theorem leaf_270_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_270.profileLo box_270.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_270_ok
theorem branch_box_270_nonnegative : ∀ j, 0 ≤ branch_box_270.lower j ∧ 0 ≤ branch_box_270.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_270, Box.profileLo, Box.profileHi, box_270]
theorem leaf_270_BranchSafe : CertificateConsequences.BranchSafe branch_box_270 := by
  left; refine ⟨branch_box_270_nonnegative, ?_⟩
  intro z hz; exact leaf_270_sound hz

theorem leaf_273_ok : checkAt 527 1000 box_273 cert_273 = true := by
  have h := List.all_eq_true.mp batch_05_12_ok accepted_273 (by simp [batch_05_12_values])
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

theorem leaf_274_ok : checkAt 527 1000 box_274 cert_274 = true := by
  have h := List.all_eq_true.mp batch_05_13_ok accepted_274 (by simp [batch_05_13_values])
  exact h
theorem leaf_274_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_274.profileLo box_274.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_274_ok
theorem branch_box_274_nonnegative : ∀ j, 0 ≤ branch_box_274.lower j ∧ 0 ≤ branch_box_274.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_274, Box.profileLo, Box.profileHi, box_274]
theorem leaf_274_BranchSafe : CertificateConsequences.BranchSafe branch_box_274 := by
  left; refine ⟨branch_box_274_nonnegative, ?_⟩
  intro z hz; exact leaf_274_sound hz

theorem leaf_277_ok : checkAt 527 1000 box_277 cert_277 = true := by
  have h := List.all_eq_true.mp batch_05_14_ok accepted_277 (by simp [batch_05_14_values])
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

theorem leaf_278_ok : checkAt 527 1000 box_278 cert_278 = true := by
  have h := List.all_eq_true.mp batch_05_15_ok accepted_278 (by simp [batch_05_15_values])
  exact h
theorem leaf_278_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_278.profileLo box_278.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_278_ok
theorem branch_box_278_nonnegative : ∀ j, 0 ≤ branch_box_278.lower j ∧ 0 ≤ branch_box_278.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_278, Box.profileLo, Box.profileHi, box_278]
theorem leaf_278_BranchSafe : CertificateConsequences.BranchSafe branch_box_278 := by
  left; refine ⟨branch_box_278_nonnegative, ?_⟩
  intro z hz; exact leaf_278_sound hz

theorem leaf_279_ok : checkAt 527 1000 box_279 cert_279 = true := by
  have h := List.all_eq_true.mp batch_05_16_ok accepted_279 (by simp [batch_05_16_values])
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
  have h := List.all_eq_true.mp batch_05_17_ok accepted_281 (by simp [batch_05_17_values])
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

theorem leaf_282_ok : checkAt 527 1000 box_282 cert_282 = true := by
  have h := List.all_eq_true.mp batch_05_18_ok accepted_282 (by simp [batch_05_18_values])
  exact h
theorem leaf_282_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_282.profileLo box_282.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_282_ok
theorem branch_box_282_nonnegative : ∀ j, 0 ≤ branch_box_282.lower j ∧ 0 ≤ branch_box_282.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_282, Box.profileLo, Box.profileHi, box_282]
theorem leaf_282_BranchSafe : CertificateConsequences.BranchSafe branch_box_282 := by
  left; refine ⟨branch_box_282_nonnegative, ?_⟩
  intro z hz; exact leaf_282_sound hz

theorem leaf_287_ok : checkAt 527 1000 box_287 cert_287 = true := by
  have h := List.all_eq_true.mp batch_05_19_ok accepted_287 (by simp [batch_05_19_values])
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
  have h := List.all_eq_true.mp batch_05_20_ok accepted_289 (by simp [batch_05_20_values])
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
  have h := List.all_eq_true.mp batch_05_21_ok accepted_291 (by simp [batch_05_21_values])
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

theorem leaf_292_ok : checkAt 527 1000 box_292 cert_292 = true := by
  have h := List.all_eq_true.mp batch_05_22_ok accepted_292 (by simp [batch_05_22_values])
  exact h
theorem leaf_292_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_292.profileLo box_292.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_292_ok
theorem branch_box_292_nonnegative : ∀ j, 0 ≤ branch_box_292.lower j ∧ 0 ≤ branch_box_292.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_292, Box.profileLo, Box.profileHi, box_292]
theorem leaf_292_BranchSafe : CertificateConsequences.BranchSafe branch_box_292 := by
  left; refine ⟨branch_box_292_nonnegative, ?_⟩
  intro z hz; exact leaf_292_sound hz

theorem leaf_293_ok : checkAt 527 1000 box_293 cert_293 = true := by
  have h := List.all_eq_true.mp batch_05_23_ok accepted_293 (by simp [batch_05_23_values])
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

theorem leaf_297_ok : checkAt 527 1000 box_297 cert_297 = true := by
  have h := List.all_eq_true.mp batch_05_24_ok accepted_297 (by simp [batch_05_24_values])
  exact h
theorem leaf_297_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_297.profileLo box_297.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_297_ok
theorem branch_box_297_nonnegative : ∀ j, 0 ≤ branch_box_297.lower j ∧ 0 ≤ branch_box_297.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_297, Box.profileLo, Box.profileHi, box_297]
theorem leaf_297_BranchSafe : CertificateConsequences.BranchSafe branch_box_297 := by
  left; refine ⟨branch_box_297_nonnegative, ?_⟩
  intro z hz; exact leaf_297_sound hz

theorem leaf_298_ok : checkAt 527 1000 box_298 cert_298 = true := by
  have h := List.all_eq_true.mp batch_05_25_ok accepted_298 (by simp [batch_05_25_values])
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

#print axioms batch_05_00_ok
#print axioms leaf_252_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
