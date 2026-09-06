import PeaceableQueens.UpperBound.Generated.Even.C527Scaled127Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_127_00_values : List Bool := [accepted_6353]
theorem batch_127_00_ok : batch_127_00_values.all id = true := by decide

def batch_127_01_values : List Bool := [accepted_6354]
theorem batch_127_01_ok : batch_127_01_values.all id = true := by decide

def batch_127_02_values : List Bool := [accepted_6359]
theorem batch_127_02_ok : batch_127_02_values.all id = true := by decide

def batch_127_03_values : List Bool := [accepted_6360]
theorem batch_127_03_ok : batch_127_03_values.all id = true := by decide

def batch_127_04_values : List Bool := [accepted_6362]
theorem batch_127_04_ok : batch_127_04_values.all id = true := by decide

def batch_127_05_values : List Bool := [accepted_6363]
theorem batch_127_05_ok : batch_127_05_values.all id = true := by decide

def batch_127_06_values : List Bool := [accepted_6364]
theorem batch_127_06_ok : batch_127_06_values.all id = true := by decide

def batch_127_07_values : List Bool := [accepted_6369]
theorem batch_127_07_ok : batch_127_07_values.all id = true := by decide

def batch_127_08_values : List Bool := [accepted_6370]
theorem batch_127_08_ok : batch_127_08_values.all id = true := by decide

def batch_127_09_values : List Bool := [accepted_6371]
theorem batch_127_09_ok : batch_127_09_values.all id = true := by decide

def batch_127_10_values : List Bool := [accepted_6372]
theorem batch_127_10_ok : batch_127_10_values.all id = true := by decide

def batch_127_11_values : List Bool := [accepted_6375]
theorem batch_127_11_ok : batch_127_11_values.all id = true := by decide

def batch_127_12_values : List Bool := [accepted_6379]
theorem batch_127_12_ok : batch_127_12_values.all id = true := by decide

def batch_127_13_values : List Bool := [accepted_6380]
theorem batch_127_13_ok : batch_127_13_values.all id = true := by decide

def batch_127_14_values : List Bool := [accepted_6381]
theorem batch_127_14_ok : batch_127_14_values.all id = true := by decide

def batch_127_15_values : List Bool := [accepted_6382]
theorem batch_127_15_ok : batch_127_15_values.all id = true := by decide

def batch_127_16_values : List Bool := [accepted_6387]
theorem batch_127_16_ok : batch_127_16_values.all id = true := by decide

def batch_127_17_values : List Bool := [accepted_6389]
theorem batch_127_17_ok : batch_127_17_values.all id = true := by decide

def batch_127_18_values : List Bool := [accepted_6390]
theorem batch_127_18_ok : batch_127_18_values.all id = true := by decide

def batch_127_19_values : List Bool := [accepted_6393]
theorem batch_127_19_ok : batch_127_19_values.all id = true := by decide

def batch_127_20_values : List Bool := [accepted_6395]
theorem batch_127_20_ok : batch_127_20_values.all id = true := by decide

def batch_127_21_values : List Bool := [accepted_6399]
theorem batch_127_21_ok : batch_127_21_values.all id = true := by decide

theorem leaf_6353_ok : checkAt 527 1000 box_6353 cert_6353 = true := by
  have h := List.all_eq_true.mp batch_127_00_ok accepted_6353 (by simp [batch_127_00_values])
  exact h
theorem leaf_6353_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6353.profileLo box_6353.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6353_ok
theorem branch_box_6353_nonnegative : ∀ j, 0 ≤ branch_box_6353.lower j ∧ 0 ≤ branch_box_6353.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6353, Box.profileLo, Box.profileHi, box_6353]
theorem leaf_6353_BranchSafe : CertificateConsequences.BranchSafe branch_box_6353 := by
  left; refine ⟨branch_box_6353_nonnegative, ?_⟩
  intro z hz; exact leaf_6353_sound hz

theorem leaf_6354_ok : checkAt 527 1000 box_6354 cert_6354 = true := by
  have h := List.all_eq_true.mp batch_127_01_ok accepted_6354 (by simp [batch_127_01_values])
  exact h
theorem leaf_6354_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6354.profileLo box_6354.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6354_ok
theorem branch_box_6354_nonnegative : ∀ j, 0 ≤ branch_box_6354.lower j ∧ 0 ≤ branch_box_6354.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6354, Box.profileLo, Box.profileHi, box_6354]
theorem leaf_6354_BranchSafe : CertificateConsequences.BranchSafe branch_box_6354 := by
  left; refine ⟨branch_box_6354_nonnegative, ?_⟩
  intro z hz; exact leaf_6354_sound hz

theorem leaf_6359_ok : checkAt 527 1000 box_6359 cert_6359 = true := by
  have h := List.all_eq_true.mp batch_127_02_ok accepted_6359 (by simp [batch_127_02_values])
  exact h
theorem leaf_6359_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6359.profileLo box_6359.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6359_ok
theorem branch_box_6359_nonnegative : ∀ j, 0 ≤ branch_box_6359.lower j ∧ 0 ≤ branch_box_6359.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6359, Box.profileLo, Box.profileHi, box_6359]
theorem leaf_6359_BranchSafe : CertificateConsequences.BranchSafe branch_box_6359 := by
  left; refine ⟨branch_box_6359_nonnegative, ?_⟩
  intro z hz; exact leaf_6359_sound hz

theorem leaf_6360_ok : checkAt 527 1000 box_6360 cert_6360 = true := by
  have h := List.all_eq_true.mp batch_127_03_ok accepted_6360 (by simp [batch_127_03_values])
  exact h
theorem leaf_6360_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6360.profileLo box_6360.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6360_ok
theorem branch_box_6360_nonnegative : ∀ j, 0 ≤ branch_box_6360.lower j ∧ 0 ≤ branch_box_6360.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6360, Box.profileLo, Box.profileHi, box_6360]
theorem leaf_6360_BranchSafe : CertificateConsequences.BranchSafe branch_box_6360 := by
  left; refine ⟨branch_box_6360_nonnegative, ?_⟩
  intro z hz; exact leaf_6360_sound hz

theorem leaf_6362_ok : checkAt 527 1000 box_6362 cert_6362 = true := by
  have h := List.all_eq_true.mp batch_127_04_ok accepted_6362 (by simp [batch_127_04_values])
  exact h
theorem leaf_6362_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6362.profileLo box_6362.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6362_ok
theorem branch_box_6362_nonnegative : ∀ j, 0 ≤ branch_box_6362.lower j ∧ 0 ≤ branch_box_6362.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6362, Box.profileLo, Box.profileHi, box_6362]
theorem leaf_6362_BranchSafe : CertificateConsequences.BranchSafe branch_box_6362 := by
  left; refine ⟨branch_box_6362_nonnegative, ?_⟩
  intro z hz; exact leaf_6362_sound hz

theorem leaf_6363_ok : checkAt 527 1000 box_6363 cert_6363 = true := by
  have h := List.all_eq_true.mp batch_127_05_ok accepted_6363 (by simp [batch_127_05_values])
  exact h
theorem leaf_6363_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6363.profileLo box_6363.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6363_ok
theorem branch_box_6363_nonnegative : ∀ j, 0 ≤ branch_box_6363.lower j ∧ 0 ≤ branch_box_6363.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6363, Box.profileLo, Box.profileHi, box_6363]
theorem leaf_6363_BranchSafe : CertificateConsequences.BranchSafe branch_box_6363 := by
  left; refine ⟨branch_box_6363_nonnegative, ?_⟩
  intro z hz; exact leaf_6363_sound hz

theorem leaf_6364_ok : checkAt 527 1000 box_6364 cert_6364 = true := by
  have h := List.all_eq_true.mp batch_127_06_ok accepted_6364 (by simp [batch_127_06_values])
  exact h
theorem leaf_6364_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6364.profileLo box_6364.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6364_ok
theorem branch_box_6364_nonnegative : ∀ j, 0 ≤ branch_box_6364.lower j ∧ 0 ≤ branch_box_6364.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6364, Box.profileLo, Box.profileHi, box_6364]
theorem leaf_6364_BranchSafe : CertificateConsequences.BranchSafe branch_box_6364 := by
  left; refine ⟨branch_box_6364_nonnegative, ?_⟩
  intro z hz; exact leaf_6364_sound hz

theorem leaf_6369_ok : checkAt 527 1000 box_6369 cert_6369 = true := by
  have h := List.all_eq_true.mp batch_127_07_ok accepted_6369 (by simp [batch_127_07_values])
  exact h
theorem leaf_6369_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6369.profileLo box_6369.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6369_ok
theorem branch_box_6369_nonnegative : ∀ j, 0 ≤ branch_box_6369.lower j ∧ 0 ≤ branch_box_6369.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6369, Box.profileLo, Box.profileHi, box_6369]
theorem leaf_6369_BranchSafe : CertificateConsequences.BranchSafe branch_box_6369 := by
  left; refine ⟨branch_box_6369_nonnegative, ?_⟩
  intro z hz; exact leaf_6369_sound hz

theorem leaf_6370_ok : checkAt 527 1000 box_6370 cert_6370 = true := by
  have h := List.all_eq_true.mp batch_127_08_ok accepted_6370 (by simp [batch_127_08_values])
  exact h
theorem leaf_6370_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6370.profileLo box_6370.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6370_ok
theorem branch_box_6370_nonnegative : ∀ j, 0 ≤ branch_box_6370.lower j ∧ 0 ≤ branch_box_6370.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6370, Box.profileLo, Box.profileHi, box_6370]
theorem leaf_6370_BranchSafe : CertificateConsequences.BranchSafe branch_box_6370 := by
  left; refine ⟨branch_box_6370_nonnegative, ?_⟩
  intro z hz; exact leaf_6370_sound hz

theorem leaf_6371_ok : checkAt 527 1000 box_6371 cert_6371 = true := by
  have h := List.all_eq_true.mp batch_127_09_ok accepted_6371 (by simp [batch_127_09_values])
  exact h
theorem leaf_6371_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6371.profileLo box_6371.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6371_ok
theorem branch_box_6371_nonnegative : ∀ j, 0 ≤ branch_box_6371.lower j ∧ 0 ≤ branch_box_6371.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6371, Box.profileLo, Box.profileHi, box_6371]
theorem leaf_6371_BranchSafe : CertificateConsequences.BranchSafe branch_box_6371 := by
  left; refine ⟨branch_box_6371_nonnegative, ?_⟩
  intro z hz; exact leaf_6371_sound hz

theorem leaf_6372_ok : checkAt 527 1000 box_6372 cert_6372 = true := by
  have h := List.all_eq_true.mp batch_127_10_ok accepted_6372 (by simp [batch_127_10_values])
  exact h
theorem leaf_6372_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6372.profileLo box_6372.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6372_ok
theorem branch_box_6372_nonnegative : ∀ j, 0 ≤ branch_box_6372.lower j ∧ 0 ≤ branch_box_6372.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6372, Box.profileLo, Box.profileHi, box_6372]
theorem leaf_6372_BranchSafe : CertificateConsequences.BranchSafe branch_box_6372 := by
  left; refine ⟨branch_box_6372_nonnegative, ?_⟩
  intro z hz; exact leaf_6372_sound hz

theorem leaf_6375_ok : checkAt 527 1000 box_6375 cert_6375 = true := by
  have h := List.all_eq_true.mp batch_127_11_ok accepted_6375 (by simp [batch_127_11_values])
  exact h
theorem leaf_6375_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6375.profileLo box_6375.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6375_ok
theorem branch_box_6375_nonnegative : ∀ j, 0 ≤ branch_box_6375.lower j ∧ 0 ≤ branch_box_6375.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6375, Box.profileLo, Box.profileHi, box_6375]
theorem leaf_6375_BranchSafe : CertificateConsequences.BranchSafe branch_box_6375 := by
  left; refine ⟨branch_box_6375_nonnegative, ?_⟩
  intro z hz; exact leaf_6375_sound hz

theorem leaf_6379_ok : checkAt 527 1000 box_6379 cert_6379 = true := by
  have h := List.all_eq_true.mp batch_127_12_ok accepted_6379 (by simp [batch_127_12_values])
  exact h
theorem leaf_6379_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6379.profileLo box_6379.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6379_ok
theorem branch_box_6379_nonnegative : ∀ j, 0 ≤ branch_box_6379.lower j ∧ 0 ≤ branch_box_6379.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6379, Box.profileLo, Box.profileHi, box_6379]
theorem leaf_6379_BranchSafe : CertificateConsequences.BranchSafe branch_box_6379 := by
  left; refine ⟨branch_box_6379_nonnegative, ?_⟩
  intro z hz; exact leaf_6379_sound hz

theorem leaf_6380_ok : checkAt 527 1000 box_6380 cert_6380 = true := by
  have h := List.all_eq_true.mp batch_127_13_ok accepted_6380 (by simp [batch_127_13_values])
  exact h
theorem leaf_6380_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6380.profileLo box_6380.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6380_ok
theorem branch_box_6380_nonnegative : ∀ j, 0 ≤ branch_box_6380.lower j ∧ 0 ≤ branch_box_6380.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6380, Box.profileLo, Box.profileHi, box_6380]
theorem leaf_6380_BranchSafe : CertificateConsequences.BranchSafe branch_box_6380 := by
  left; refine ⟨branch_box_6380_nonnegative, ?_⟩
  intro z hz; exact leaf_6380_sound hz

theorem leaf_6381_ok : checkAt 527 1000 box_6381 cert_6381 = true := by
  have h := List.all_eq_true.mp batch_127_14_ok accepted_6381 (by simp [batch_127_14_values])
  exact h
theorem leaf_6381_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6381.profileLo box_6381.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6381_ok
theorem branch_box_6381_nonnegative : ∀ j, 0 ≤ branch_box_6381.lower j ∧ 0 ≤ branch_box_6381.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6381, Box.profileLo, Box.profileHi, box_6381]
theorem leaf_6381_BranchSafe : CertificateConsequences.BranchSafe branch_box_6381 := by
  left; refine ⟨branch_box_6381_nonnegative, ?_⟩
  intro z hz; exact leaf_6381_sound hz

theorem leaf_6382_ok : checkAt 527 1000 box_6382 cert_6382 = true := by
  have h := List.all_eq_true.mp batch_127_15_ok accepted_6382 (by simp [batch_127_15_values])
  exact h
theorem leaf_6382_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6382.profileLo box_6382.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6382_ok
theorem branch_box_6382_nonnegative : ∀ j, 0 ≤ branch_box_6382.lower j ∧ 0 ≤ branch_box_6382.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6382, Box.profileLo, Box.profileHi, box_6382]
theorem leaf_6382_BranchSafe : CertificateConsequences.BranchSafe branch_box_6382 := by
  left; refine ⟨branch_box_6382_nonnegative, ?_⟩
  intro z hz; exact leaf_6382_sound hz

theorem leaf_6387_ok : checkAt 527 1000 box_6387 cert_6387 = true := by
  have h := List.all_eq_true.mp batch_127_16_ok accepted_6387 (by simp [batch_127_16_values])
  exact h
theorem leaf_6387_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6387.profileLo box_6387.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6387_ok
theorem branch_box_6387_nonnegative : ∀ j, 0 ≤ branch_box_6387.lower j ∧ 0 ≤ branch_box_6387.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6387, Box.profileLo, Box.profileHi, box_6387]
theorem leaf_6387_BranchSafe : CertificateConsequences.BranchSafe branch_box_6387 := by
  left; refine ⟨branch_box_6387_nonnegative, ?_⟩
  intro z hz; exact leaf_6387_sound hz

theorem leaf_6389_ok : checkAt 527 1000 box_6389 cert_6389 = true := by
  have h := List.all_eq_true.mp batch_127_17_ok accepted_6389 (by simp [batch_127_17_values])
  exact h
theorem leaf_6389_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6389.profileLo box_6389.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6389_ok
theorem branch_box_6389_nonnegative : ∀ j, 0 ≤ branch_box_6389.lower j ∧ 0 ≤ branch_box_6389.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6389, Box.profileLo, Box.profileHi, box_6389]
theorem leaf_6389_BranchSafe : CertificateConsequences.BranchSafe branch_box_6389 := by
  left; refine ⟨branch_box_6389_nonnegative, ?_⟩
  intro z hz; exact leaf_6389_sound hz

theorem leaf_6390_ok : checkAt 527 1000 box_6390 cert_6390 = true := by
  have h := List.all_eq_true.mp batch_127_18_ok accepted_6390 (by simp [batch_127_18_values])
  exact h
theorem leaf_6390_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6390.profileLo box_6390.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6390_ok
theorem branch_box_6390_nonnegative : ∀ j, 0 ≤ branch_box_6390.lower j ∧ 0 ≤ branch_box_6390.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6390, Box.profileLo, Box.profileHi, box_6390]
theorem leaf_6390_BranchSafe : CertificateConsequences.BranchSafe branch_box_6390 := by
  left; refine ⟨branch_box_6390_nonnegative, ?_⟩
  intro z hz; exact leaf_6390_sound hz

theorem leaf_6393_ok : checkAt 527 1000 box_6393 cert_6393 = true := by
  have h := List.all_eq_true.mp batch_127_19_ok accepted_6393 (by simp [batch_127_19_values])
  exact h
theorem leaf_6393_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6393.profileLo box_6393.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6393_ok
theorem branch_box_6393_nonnegative : ∀ j, 0 ≤ branch_box_6393.lower j ∧ 0 ≤ branch_box_6393.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6393, Box.profileLo, Box.profileHi, box_6393]
theorem leaf_6393_BranchSafe : CertificateConsequences.BranchSafe branch_box_6393 := by
  left; refine ⟨branch_box_6393_nonnegative, ?_⟩
  intro z hz; exact leaf_6393_sound hz

theorem leaf_6395_ok : checkAt 527 1000 box_6395 cert_6395 = true := by
  have h := List.all_eq_true.mp batch_127_20_ok accepted_6395 (by simp [batch_127_20_values])
  exact h
theorem leaf_6395_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6395.profileLo box_6395.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6395_ok
theorem branch_box_6395_nonnegative : ∀ j, 0 ≤ branch_box_6395.lower j ∧ 0 ≤ branch_box_6395.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6395, Box.profileLo, Box.profileHi, box_6395]
theorem leaf_6395_BranchSafe : CertificateConsequences.BranchSafe branch_box_6395 := by
  left; refine ⟨branch_box_6395_nonnegative, ?_⟩
  intro z hz; exact leaf_6395_sound hz

theorem leaf_6399_ok : checkAt 527 1000 box_6399 cert_6399 = true := by
  have h := List.all_eq_true.mp batch_127_21_ok accepted_6399 (by simp [batch_127_21_values])
  exact h
theorem leaf_6399_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6399.profileLo box_6399.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6399_ok
theorem branch_box_6399_nonnegative : ∀ j, 0 ≤ branch_box_6399.lower j ∧ 0 ≤ branch_box_6399.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6399, Box.profileLo, Box.profileHi, box_6399]
theorem leaf_6399_BranchSafe : CertificateConsequences.BranchSafe branch_box_6399 := by
  left; refine ⟨branch_box_6399_nonnegative, ?_⟩
  intro z hz; exact leaf_6399_sound hz

#print axioms batch_127_00_ok
#print axioms leaf_6353_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
