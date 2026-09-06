import PeaceableQueens.UpperBound.Generated.Even.C527Scaled04Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_04_00_values : List Bool := [accepted_200]
theorem batch_04_00_ok : batch_04_00_values.all id = true := by decide

def batch_04_01_values : List Bool := [accepted_201]
theorem batch_04_01_ok : batch_04_01_values.all id = true := by decide

def batch_04_02_values : List Bool := [accepted_202]
theorem batch_04_02_ok : batch_04_02_values.all id = true := by decide

def batch_04_03_values : List Bool := [accepted_207]
theorem batch_04_03_ok : batch_04_03_values.all id = true := by decide

def batch_04_04_values : List Bool := [accepted_209]
theorem batch_04_04_ok : batch_04_04_values.all id = true := by decide

def batch_04_05_values : List Bool := [accepted_210]
theorem batch_04_05_ok : batch_04_05_values.all id = true := by decide

def batch_04_06_values : List Bool := [accepted_215]
theorem batch_04_06_ok : batch_04_06_values.all id = true := by decide

def batch_04_07_values : List Bool := [accepted_217]
theorem batch_04_07_ok : batch_04_07_values.all id = true := by decide

def batch_04_08_values : List Bool := [accepted_218]
theorem batch_04_08_ok : batch_04_08_values.all id = true := by decide

def batch_04_09_values : List Bool := [accepted_219]
theorem batch_04_09_ok : batch_04_09_values.all id = true := by decide

def batch_04_10_values : List Bool := [accepted_220]
theorem batch_04_10_ok : batch_04_10_values.all id = true := by decide

def batch_04_11_values : List Bool := [accepted_223]
theorem batch_04_11_ok : batch_04_11_values.all id = true := by decide

def batch_04_12_values : List Bool := [accepted_224]
theorem batch_04_12_ok : batch_04_12_values.all id = true := by decide

def batch_04_13_values : List Bool := [accepted_226]
theorem batch_04_13_ok : batch_04_13_values.all id = true := by decide

def batch_04_14_values : List Bool := [accepted_227]
theorem batch_04_14_ok : batch_04_14_values.all id = true := by decide

def batch_04_15_values : List Bool := [accepted_228]
theorem batch_04_15_ok : batch_04_15_values.all id = true := by decide

def batch_04_16_values : List Bool := [accepted_233]
theorem batch_04_16_ok : batch_04_16_values.all id = true := by decide

def batch_04_17_values : List Bool := [accepted_234]
theorem batch_04_17_ok : batch_04_17_values.all id = true := by decide

def batch_04_18_values : List Bool := [accepted_237]
theorem batch_04_18_ok : batch_04_18_values.all id = true := by decide

def batch_04_19_values : List Bool := [accepted_238]
theorem batch_04_19_ok : batch_04_19_values.all id = true := by decide

def batch_04_20_values : List Bool := [accepted_240]
theorem batch_04_20_ok : batch_04_20_values.all id = true := by decide

def batch_04_21_values : List Bool := [accepted_241]
theorem batch_04_21_ok : batch_04_21_values.all id = true := by decide

def batch_04_22_values : List Bool := [accepted_242]
theorem batch_04_22_ok : batch_04_22_values.all id = true := by decide

def batch_04_23_values : List Bool := [accepted_247]
theorem batch_04_23_ok : batch_04_23_values.all id = true := by decide

def batch_04_24_values : List Bool := [accepted_248]
theorem batch_04_24_ok : batch_04_24_values.all id = true := by decide

def batch_04_25_values : List Bool := [accepted_249]
theorem batch_04_25_ok : batch_04_25_values.all id = true := by decide

theorem leaf_200_ok : checkAt 527 1000 box_200 cert_200 = true := by
  have h := List.all_eq_true.mp batch_04_00_ok accepted_200 (by simp [batch_04_00_values])
  exact h
theorem leaf_200_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_200.profileLo box_200.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_200_ok
theorem branch_box_200_nonnegative : ∀ j, 0 ≤ branch_box_200.lower j ∧ 0 ≤ branch_box_200.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_200, Box.profileLo, Box.profileHi, box_200]
theorem leaf_200_BranchSafe : CertificateConsequences.BranchSafe branch_box_200 := by
  left; refine ⟨branch_box_200_nonnegative, ?_⟩
  intro z hz; exact leaf_200_sound hz

theorem leaf_201_ok : checkAt 527 1000 box_201 cert_201 = true := by
  have h := List.all_eq_true.mp batch_04_01_ok accepted_201 (by simp [batch_04_01_values])
  exact h
theorem leaf_201_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_201.profileLo box_201.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_201_ok
theorem branch_box_201_nonnegative : ∀ j, 0 ≤ branch_box_201.lower j ∧ 0 ≤ branch_box_201.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_201, Box.profileLo, Box.profileHi, box_201]
theorem leaf_201_BranchSafe : CertificateConsequences.BranchSafe branch_box_201 := by
  left; refine ⟨branch_box_201_nonnegative, ?_⟩
  intro z hz; exact leaf_201_sound hz

theorem leaf_202_ok : checkAt 527 1000 box_202 cert_202 = true := by
  have h := List.all_eq_true.mp batch_04_02_ok accepted_202 (by simp [batch_04_02_values])
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

theorem leaf_207_ok : checkAt 527 1000 box_207 cert_207 = true := by
  have h := List.all_eq_true.mp batch_04_03_ok accepted_207 (by simp [batch_04_03_values])
  exact h
theorem leaf_207_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_207.profileLo box_207.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_207_ok
theorem branch_box_207_nonnegative : ∀ j, 0 ≤ branch_box_207.lower j ∧ 0 ≤ branch_box_207.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_207, Box.profileLo, Box.profileHi, box_207]
theorem leaf_207_BranchSafe : CertificateConsequences.BranchSafe branch_box_207 := by
  left; refine ⟨branch_box_207_nonnegative, ?_⟩
  intro z hz; exact leaf_207_sound hz

theorem leaf_209_ok : checkAt 527 1000 box_209 cert_209 = true := by
  have h := List.all_eq_true.mp batch_04_04_ok accepted_209 (by simp [batch_04_04_values])
  exact h
theorem leaf_209_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_209.profileLo box_209.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_209_ok
theorem branch_box_209_nonnegative : ∀ j, 0 ≤ branch_box_209.lower j ∧ 0 ≤ branch_box_209.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_209, Box.profileLo, Box.profileHi, box_209]
theorem leaf_209_BranchSafe : CertificateConsequences.BranchSafe branch_box_209 := by
  left; refine ⟨branch_box_209_nonnegative, ?_⟩
  intro z hz; exact leaf_209_sound hz

theorem leaf_210_ok : checkAt 527 1000 box_210 cert_210 = true := by
  have h := List.all_eq_true.mp batch_04_05_ok accepted_210 (by simp [batch_04_05_values])
  exact h
theorem leaf_210_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_210.profileLo box_210.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_210_ok
theorem branch_box_210_nonnegative : ∀ j, 0 ≤ branch_box_210.lower j ∧ 0 ≤ branch_box_210.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_210, Box.profileLo, Box.profileHi, box_210]
theorem leaf_210_BranchSafe : CertificateConsequences.BranchSafe branch_box_210 := by
  left; refine ⟨branch_box_210_nonnegative, ?_⟩
  intro z hz; exact leaf_210_sound hz

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

theorem leaf_218_ok : checkAt 527 1000 box_218 cert_218 = true := by
  have h := List.all_eq_true.mp batch_04_08_ok accepted_218 (by simp [batch_04_08_values])
  exact h
theorem leaf_218_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_218.profileLo box_218.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_218_ok
theorem branch_box_218_nonnegative : ∀ j, 0 ≤ branch_box_218.lower j ∧ 0 ≤ branch_box_218.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_218, Box.profileLo, Box.profileHi, box_218]
theorem leaf_218_BranchSafe : CertificateConsequences.BranchSafe branch_box_218 := by
  left; refine ⟨branch_box_218_nonnegative, ?_⟩
  intro z hz; exact leaf_218_sound hz

theorem leaf_219_ok : checkAt 527 1000 box_219 cert_219 = true := by
  have h := List.all_eq_true.mp batch_04_09_ok accepted_219 (by simp [batch_04_09_values])
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

theorem leaf_220_ok : checkAt 527 1000 box_220 cert_220 = true := by
  have h := List.all_eq_true.mp batch_04_10_ok accepted_220 (by simp [batch_04_10_values])
  exact h
theorem leaf_220_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_220.profileLo box_220.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_220_ok
theorem branch_box_220_nonnegative : ∀ j, 0 ≤ branch_box_220.lower j ∧ 0 ≤ branch_box_220.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_220, Box.profileLo, Box.profileHi, box_220]
theorem leaf_220_BranchSafe : CertificateConsequences.BranchSafe branch_box_220 := by
  left; refine ⟨branch_box_220_nonnegative, ?_⟩
  intro z hz; exact leaf_220_sound hz

theorem leaf_223_ok : checkAt 527 1000 box_223 cert_223 = true := by
  have h := List.all_eq_true.mp batch_04_11_ok accepted_223 (by simp [batch_04_11_values])
  exact h
theorem leaf_223_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_223.profileLo box_223.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_223_ok
theorem branch_box_223_nonnegative : ∀ j, 0 ≤ branch_box_223.lower j ∧ 0 ≤ branch_box_223.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_223, Box.profileLo, Box.profileHi, box_223]
theorem leaf_223_BranchSafe : CertificateConsequences.BranchSafe branch_box_223 := by
  left; refine ⟨branch_box_223_nonnegative, ?_⟩
  intro z hz; exact leaf_223_sound hz

theorem leaf_224_ok : checkAt 527 1000 box_224 cert_224 = true := by
  have h := List.all_eq_true.mp batch_04_12_ok accepted_224 (by simp [batch_04_12_values])
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

theorem leaf_226_ok : checkAt 527 1000 box_226 cert_226 = true := by
  have h := List.all_eq_true.mp batch_04_13_ok accepted_226 (by simp [batch_04_13_values])
  exact h
theorem leaf_226_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_226.profileLo box_226.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_226_ok
theorem branch_box_226_nonnegative : ∀ j, 0 ≤ branch_box_226.lower j ∧ 0 ≤ branch_box_226.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_226, Box.profileLo, Box.profileHi, box_226]
theorem leaf_226_BranchSafe : CertificateConsequences.BranchSafe branch_box_226 := by
  left; refine ⟨branch_box_226_nonnegative, ?_⟩
  intro z hz; exact leaf_226_sound hz

theorem leaf_227_ok : checkAt 527 1000 box_227 cert_227 = true := by
  have h := List.all_eq_true.mp batch_04_14_ok accepted_227 (by simp [batch_04_14_values])
  exact h
theorem leaf_227_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_227.profileLo box_227.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_227_ok
theorem branch_box_227_nonnegative : ∀ j, 0 ≤ branch_box_227.lower j ∧ 0 ≤ branch_box_227.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_227, Box.profileLo, Box.profileHi, box_227]
theorem leaf_227_BranchSafe : CertificateConsequences.BranchSafe branch_box_227 := by
  left; refine ⟨branch_box_227_nonnegative, ?_⟩
  intro z hz; exact leaf_227_sound hz

theorem leaf_228_ok : checkAt 527 1000 box_228 cert_228 = true := by
  have h := List.all_eq_true.mp batch_04_15_ok accepted_228 (by simp [batch_04_15_values])
  exact h
theorem leaf_228_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_228.profileLo box_228.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_228_ok
theorem branch_box_228_nonnegative : ∀ j, 0 ≤ branch_box_228.lower j ∧ 0 ≤ branch_box_228.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_228, Box.profileLo, Box.profileHi, box_228]
theorem leaf_228_BranchSafe : CertificateConsequences.BranchSafe branch_box_228 := by
  left; refine ⟨branch_box_228_nonnegative, ?_⟩
  intro z hz; exact leaf_228_sound hz

theorem leaf_233_ok : checkAt 527 1000 box_233 cert_233 = true := by
  have h := List.all_eq_true.mp batch_04_16_ok accepted_233 (by simp [batch_04_16_values])
  exact h
theorem leaf_233_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_233.profileLo box_233.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_233_ok
theorem branch_box_233_nonnegative : ∀ j, 0 ≤ branch_box_233.lower j ∧ 0 ≤ branch_box_233.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_233, Box.profileLo, Box.profileHi, box_233]
theorem leaf_233_BranchSafe : CertificateConsequences.BranchSafe branch_box_233 := by
  left; refine ⟨branch_box_233_nonnegative, ?_⟩
  intro z hz; exact leaf_233_sound hz

theorem leaf_234_ok : checkAt 527 1000 box_234 cert_234 = true := by
  have h := List.all_eq_true.mp batch_04_17_ok accepted_234 (by simp [batch_04_17_values])
  exact h
theorem leaf_234_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_234.profileLo box_234.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_234_ok
theorem branch_box_234_nonnegative : ∀ j, 0 ≤ branch_box_234.lower j ∧ 0 ≤ branch_box_234.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_234, Box.profileLo, Box.profileHi, box_234]
theorem leaf_234_BranchSafe : CertificateConsequences.BranchSafe branch_box_234 := by
  left; refine ⟨branch_box_234_nonnegative, ?_⟩
  intro z hz; exact leaf_234_sound hz

theorem leaf_237_ok : checkAt 527 1000 box_237 cert_237 = true := by
  have h := List.all_eq_true.mp batch_04_18_ok accepted_237 (by simp [batch_04_18_values])
  exact h
theorem leaf_237_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_237.profileLo box_237.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_237_ok
theorem branch_box_237_nonnegative : ∀ j, 0 ≤ branch_box_237.lower j ∧ 0 ≤ branch_box_237.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_237, Box.profileLo, Box.profileHi, box_237]
theorem leaf_237_BranchSafe : CertificateConsequences.BranchSafe branch_box_237 := by
  left; refine ⟨branch_box_237_nonnegative, ?_⟩
  intro z hz; exact leaf_237_sound hz

theorem leaf_238_ok : checkAt 527 1000 box_238 cert_238 = true := by
  have h := List.all_eq_true.mp batch_04_19_ok accepted_238 (by simp [batch_04_19_values])
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

theorem leaf_240_ok : checkAt 527 1000 box_240 cert_240 = true := by
  have h := List.all_eq_true.mp batch_04_20_ok accepted_240 (by simp [batch_04_20_values])
  exact h
theorem leaf_240_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_240.profileLo box_240.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_240_ok
theorem branch_box_240_nonnegative : ∀ j, 0 ≤ branch_box_240.lower j ∧ 0 ≤ branch_box_240.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_240, Box.profileLo, Box.profileHi, box_240]
theorem leaf_240_BranchSafe : CertificateConsequences.BranchSafe branch_box_240 := by
  left; refine ⟨branch_box_240_nonnegative, ?_⟩
  intro z hz; exact leaf_240_sound hz

theorem leaf_241_ok : checkAt 527 1000 box_241 cert_241 = true := by
  have h := List.all_eq_true.mp batch_04_21_ok accepted_241 (by simp [batch_04_21_values])
  exact h
theorem leaf_241_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_241.profileLo box_241.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_241_ok
theorem branch_box_241_nonnegative : ∀ j, 0 ≤ branch_box_241.lower j ∧ 0 ≤ branch_box_241.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_241, Box.profileLo, Box.profileHi, box_241]
theorem leaf_241_BranchSafe : CertificateConsequences.BranchSafe branch_box_241 := by
  left; refine ⟨branch_box_241_nonnegative, ?_⟩
  intro z hz; exact leaf_241_sound hz

theorem leaf_242_ok : checkAt 527 1000 box_242 cert_242 = true := by
  have h := List.all_eq_true.mp batch_04_22_ok accepted_242 (by simp [batch_04_22_values])
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

theorem leaf_247_ok : checkAt 527 1000 box_247 cert_247 = true := by
  have h := List.all_eq_true.mp batch_04_23_ok accepted_247 (by simp [batch_04_23_values])
  exact h
theorem leaf_247_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_247.profileLo box_247.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_247_ok
theorem branch_box_247_nonnegative : ∀ j, 0 ≤ branch_box_247.lower j ∧ 0 ≤ branch_box_247.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_247, Box.profileLo, Box.profileHi, box_247]
theorem leaf_247_BranchSafe : CertificateConsequences.BranchSafe branch_box_247 := by
  left; refine ⟨branch_box_247_nonnegative, ?_⟩
  intro z hz; exact leaf_247_sound hz

theorem leaf_248_ok : checkAt 527 1000 box_248 cert_248 = true := by
  have h := List.all_eq_true.mp batch_04_24_ok accepted_248 (by simp [batch_04_24_values])
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

theorem leaf_249_ok : checkAt 527 1000 box_249 cert_249 = true := by
  have h := List.all_eq_true.mp batch_04_25_ok accepted_249 (by simp [batch_04_25_values])
  exact h
theorem leaf_249_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_249.profileLo box_249.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_249_ok
theorem branch_box_249_nonnegative : ∀ j, 0 ≤ branch_box_249.lower j ∧ 0 ≤ branch_box_249.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_249, Box.profileLo, Box.profileHi, box_249]
theorem leaf_249_BranchSafe : CertificateConsequences.BranchSafe branch_box_249 := by
  left; refine ⟨branch_box_249_nonnegative, ?_⟩
  intro z hz; exact leaf_249_sound hz

#print axioms batch_04_00_ok
#print axioms leaf_200_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
