import PeaceableQueens.UpperBound.Generated.Even.C527Scaled88Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_88_00_values : List Bool := [accepted_4400]
theorem batch_88_00_ok : batch_88_00_values.all id = true := by decide

def batch_88_01_values : List Bool := [accepted_4401]
theorem batch_88_01_ok : batch_88_01_values.all id = true := by decide

def batch_88_02_values : List Bool := [accepted_4402]
theorem batch_88_02_ok : batch_88_02_values.all id = true := by decide

def batch_88_03_values : List Bool := [accepted_4407]
theorem batch_88_03_ok : batch_88_03_values.all id = true := by decide

def batch_88_04_values : List Bool := [accepted_4408]
theorem batch_88_04_ok : batch_88_04_values.all id = true := by decide

def batch_88_05_values : List Bool := [accepted_4409]
theorem batch_88_05_ok : batch_88_05_values.all id = true := by decide

def batch_88_06_values : List Bool := [accepted_4410]
theorem batch_88_06_ok : batch_88_06_values.all id = true := by decide

def batch_88_07_values : List Bool := [accepted_4414]
theorem batch_88_07_ok : batch_88_07_values.all id = true := by decide

def batch_88_08_values : List Bool := [accepted_4416]
theorem batch_88_08_ok : batch_88_08_values.all id = true := by decide

def batch_88_09_values : List Bool := [accepted_4417]
theorem batch_88_09_ok : batch_88_09_values.all id = true := by decide

def batch_88_10_values : List Bool := [accepted_4418]
theorem batch_88_10_ok : batch_88_10_values.all id = true := by decide

def batch_88_11_values : List Bool := [accepted_4421]
theorem batch_88_11_ok : batch_88_11_values.all id = true := by decide

def batch_88_12_values : List Bool := [accepted_4422]
theorem batch_88_12_ok : batch_88_12_values.all id = true := by decide

def batch_88_13_values : List Bool := [accepted_4423]
theorem batch_88_13_ok : batch_88_13_values.all id = true := by decide

def batch_88_14_values : List Bool := [accepted_4424]
theorem batch_88_14_ok : batch_88_14_values.all id = true := by decide

def batch_88_15_values : List Bool := [accepted_4427]
theorem batch_88_15_ok : batch_88_15_values.all id = true := by decide

def batch_88_16_values : List Bool := [accepted_4428]
theorem batch_88_16_ok : batch_88_16_values.all id = true := by decide

def batch_88_17_values : List Bool := [accepted_4430]
theorem batch_88_17_ok : batch_88_17_values.all id = true := by decide

def batch_88_18_values : List Bool := [accepted_4433]
theorem batch_88_18_ok : batch_88_18_values.all id = true := by decide

def batch_88_19_values : List Bool := [accepted_4434]
theorem batch_88_19_ok : batch_88_19_values.all id = true := by decide

def batch_88_20_values : List Bool := [accepted_4435]
theorem batch_88_20_ok : batch_88_20_values.all id = true := by decide

def batch_88_21_values : List Bool := [accepted_4436]
theorem batch_88_21_ok : batch_88_21_values.all id = true := by decide

def batch_88_22_values : List Bool := [accepted_4444]
theorem batch_88_22_ok : batch_88_22_values.all id = true := by decide

def batch_88_23_values : List Bool := [accepted_4445]
theorem batch_88_23_ok : batch_88_23_values.all id = true := by decide

def batch_88_24_values : List Bool := [accepted_4446]
theorem batch_88_24_ok : batch_88_24_values.all id = true := by decide

def batch_88_25_values : List Bool := [accepted_4448]
theorem batch_88_25_ok : batch_88_25_values.all id = true := by decide

def batch_88_26_values : List Bool := [accepted_4449]
theorem batch_88_26_ok : batch_88_26_values.all id = true := by decide

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

theorem leaf_4401_ok : checkAt 527 1000 box_4401 cert_4401 = true := by
  have h := List.all_eq_true.mp batch_88_01_ok accepted_4401 (by simp [batch_88_01_values])
  exact h
theorem leaf_4401_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4401.profileLo box_4401.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4401_ok
theorem branch_box_4401_nonnegative : ∀ j, 0 ≤ branch_box_4401.lower j ∧ 0 ≤ branch_box_4401.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4401, Box.profileLo, Box.profileHi, box_4401]
theorem leaf_4401_BranchSafe : CertificateConsequences.BranchSafe branch_box_4401 := by
  left; refine ⟨branch_box_4401_nonnegative, ?_⟩
  intro z hz; exact leaf_4401_sound hz

theorem leaf_4402_ok : checkAt 527 1000 box_4402 cert_4402 = true := by
  have h := List.all_eq_true.mp batch_88_02_ok accepted_4402 (by simp [batch_88_02_values])
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

theorem leaf_4407_ok : checkAt 527 1000 box_4407 cert_4407 = true := by
  have h := List.all_eq_true.mp batch_88_03_ok accepted_4407 (by simp [batch_88_03_values])
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

theorem leaf_4408_ok : checkAt 527 1000 box_4408 cert_4408 = true := by
  have h := List.all_eq_true.mp batch_88_04_ok accepted_4408 (by simp [batch_88_04_values])
  exact h
theorem leaf_4408_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4408.profileLo box_4408.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4408_ok
theorem branch_box_4408_nonnegative : ∀ j, 0 ≤ branch_box_4408.lower j ∧ 0 ≤ branch_box_4408.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4408, Box.profileLo, Box.profileHi, box_4408]
theorem leaf_4408_BranchSafe : CertificateConsequences.BranchSafe branch_box_4408 := by
  left; refine ⟨branch_box_4408_nonnegative, ?_⟩
  intro z hz; exact leaf_4408_sound hz

theorem leaf_4409_ok : checkAt 527 1000 box_4409 cert_4409 = true := by
  have h := List.all_eq_true.mp batch_88_05_ok accepted_4409 (by simp [batch_88_05_values])
  exact h
theorem leaf_4409_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4409.profileLo box_4409.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4409_ok
theorem branch_box_4409_nonnegative : ∀ j, 0 ≤ branch_box_4409.lower j ∧ 0 ≤ branch_box_4409.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4409, Box.profileLo, Box.profileHi, box_4409]
theorem leaf_4409_BranchSafe : CertificateConsequences.BranchSafe branch_box_4409 := by
  left; refine ⟨branch_box_4409_nonnegative, ?_⟩
  intro z hz; exact leaf_4409_sound hz

theorem leaf_4410_ok : checkAt 527 1000 box_4410 cert_4410 = true := by
  have h := List.all_eq_true.mp batch_88_06_ok accepted_4410 (by simp [batch_88_06_values])
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

theorem leaf_4414_ok : checkAt 527 1000 box_4414 cert_4414 = true := by
  have h := List.all_eq_true.mp batch_88_07_ok accepted_4414 (by simp [batch_88_07_values])
  exact h
theorem leaf_4414_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4414.profileLo box_4414.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4414_ok
theorem branch_box_4414_nonnegative : ∀ j, 0 ≤ branch_box_4414.lower j ∧ 0 ≤ branch_box_4414.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4414, Box.profileLo, Box.profileHi, box_4414]
theorem leaf_4414_BranchSafe : CertificateConsequences.BranchSafe branch_box_4414 := by
  left; refine ⟨branch_box_4414_nonnegative, ?_⟩
  intro z hz; exact leaf_4414_sound hz

theorem leaf_4416_ok : checkAt 527 1000 box_4416 cert_4416 = true := by
  have h := List.all_eq_true.mp batch_88_08_ok accepted_4416 (by simp [batch_88_08_values])
  exact h
theorem leaf_4416_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4416.profileLo box_4416.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4416_ok
theorem branch_box_4416_nonnegative : ∀ j, 0 ≤ branch_box_4416.lower j ∧ 0 ≤ branch_box_4416.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4416, Box.profileLo, Box.profileHi, box_4416]
theorem leaf_4416_BranchSafe : CertificateConsequences.BranchSafe branch_box_4416 := by
  left; refine ⟨branch_box_4416_nonnegative, ?_⟩
  intro z hz; exact leaf_4416_sound hz

theorem leaf_4417_ok : checkAt 527 1000 box_4417 cert_4417 = true := by
  have h := List.all_eq_true.mp batch_88_09_ok accepted_4417 (by simp [batch_88_09_values])
  exact h
theorem leaf_4417_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4417.profileLo box_4417.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4417_ok
theorem branch_box_4417_nonnegative : ∀ j, 0 ≤ branch_box_4417.lower j ∧ 0 ≤ branch_box_4417.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4417, Box.profileLo, Box.profileHi, box_4417]
theorem leaf_4417_BranchSafe : CertificateConsequences.BranchSafe branch_box_4417 := by
  left; refine ⟨branch_box_4417_nonnegative, ?_⟩
  intro z hz; exact leaf_4417_sound hz

theorem leaf_4418_ok : checkAt 527 1000 box_4418 cert_4418 = true := by
  have h := List.all_eq_true.mp batch_88_10_ok accepted_4418 (by simp [batch_88_10_values])
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

theorem leaf_4421_ok : checkAt 527 1000 box_4421 cert_4421 = true := by
  have h := List.all_eq_true.mp batch_88_11_ok accepted_4421 (by simp [batch_88_11_values])
  exact h
theorem leaf_4421_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4421.profileLo box_4421.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4421_ok
theorem branch_box_4421_nonnegative : ∀ j, 0 ≤ branch_box_4421.lower j ∧ 0 ≤ branch_box_4421.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4421, Box.profileLo, Box.profileHi, box_4421]
theorem leaf_4421_BranchSafe : CertificateConsequences.BranchSafe branch_box_4421 := by
  left; refine ⟨branch_box_4421_nonnegative, ?_⟩
  intro z hz; exact leaf_4421_sound hz

theorem leaf_4422_ok : checkAt 527 1000 box_4422 cert_4422 = true := by
  have h := List.all_eq_true.mp batch_88_12_ok accepted_4422 (by simp [batch_88_12_values])
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

theorem leaf_4423_ok : checkAt 527 1000 box_4423 cert_4423 = true := by
  have h := List.all_eq_true.mp batch_88_13_ok accepted_4423 (by simp [batch_88_13_values])
  exact h
theorem leaf_4423_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4423.profileLo box_4423.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4423_ok
theorem branch_box_4423_nonnegative : ∀ j, 0 ≤ branch_box_4423.lower j ∧ 0 ≤ branch_box_4423.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4423, Box.profileLo, Box.profileHi, box_4423]
theorem leaf_4423_BranchSafe : CertificateConsequences.BranchSafe branch_box_4423 := by
  left; refine ⟨branch_box_4423_nonnegative, ?_⟩
  intro z hz; exact leaf_4423_sound hz

theorem leaf_4424_ok : checkAt 527 1000 box_4424 cert_4424 = true := by
  have h := List.all_eq_true.mp batch_88_14_ok accepted_4424 (by simp [batch_88_14_values])
  exact h
theorem leaf_4424_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4424.profileLo box_4424.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4424_ok
theorem branch_box_4424_nonnegative : ∀ j, 0 ≤ branch_box_4424.lower j ∧ 0 ≤ branch_box_4424.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4424, Box.profileLo, Box.profileHi, box_4424]
theorem leaf_4424_BranchSafe : CertificateConsequences.BranchSafe branch_box_4424 := by
  left; refine ⟨branch_box_4424_nonnegative, ?_⟩
  intro z hz; exact leaf_4424_sound hz

theorem leaf_4427_ok : checkAt 527 1000 box_4427 cert_4427 = true := by
  have h := List.all_eq_true.mp batch_88_15_ok accepted_4427 (by simp [batch_88_15_values])
  exact h
theorem leaf_4427_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4427.profileLo box_4427.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4427_ok
theorem branch_box_4427_nonnegative : ∀ j, 0 ≤ branch_box_4427.lower j ∧ 0 ≤ branch_box_4427.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4427, Box.profileLo, Box.profileHi, box_4427]
theorem leaf_4427_BranchSafe : CertificateConsequences.BranchSafe branch_box_4427 := by
  left; refine ⟨branch_box_4427_nonnegative, ?_⟩
  intro z hz; exact leaf_4427_sound hz

theorem leaf_4428_ok : checkAt 527 1000 box_4428 cert_4428 = true := by
  have h := List.all_eq_true.mp batch_88_16_ok accepted_4428 (by simp [batch_88_16_values])
  exact h
theorem leaf_4428_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4428.profileLo box_4428.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4428_ok
theorem branch_box_4428_nonnegative : ∀ j, 0 ≤ branch_box_4428.lower j ∧ 0 ≤ branch_box_4428.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4428, Box.profileLo, Box.profileHi, box_4428]
theorem leaf_4428_BranchSafe : CertificateConsequences.BranchSafe branch_box_4428 := by
  left; refine ⟨branch_box_4428_nonnegative, ?_⟩
  intro z hz; exact leaf_4428_sound hz

theorem leaf_4430_ok : checkAt 527 1000 box_4430 cert_4430 = true := by
  have h := List.all_eq_true.mp batch_88_17_ok accepted_4430 (by simp [batch_88_17_values])
  exact h
theorem leaf_4430_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4430.profileLo box_4430.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4430_ok
theorem branch_box_4430_nonnegative : ∀ j, 0 ≤ branch_box_4430.lower j ∧ 0 ≤ branch_box_4430.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4430, Box.profileLo, Box.profileHi, box_4430]
theorem leaf_4430_BranchSafe : CertificateConsequences.BranchSafe branch_box_4430 := by
  left; refine ⟨branch_box_4430_nonnegative, ?_⟩
  intro z hz; exact leaf_4430_sound hz

theorem leaf_4433_ok : checkAt 527 1000 box_4433 cert_4433 = true := by
  have h := List.all_eq_true.mp batch_88_18_ok accepted_4433 (by simp [batch_88_18_values])
  exact h
theorem leaf_4433_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4433.profileLo box_4433.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4433_ok
theorem branch_box_4433_nonnegative : ∀ j, 0 ≤ branch_box_4433.lower j ∧ 0 ≤ branch_box_4433.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4433, Box.profileLo, Box.profileHi, box_4433]
theorem leaf_4433_BranchSafe : CertificateConsequences.BranchSafe branch_box_4433 := by
  left; refine ⟨branch_box_4433_nonnegative, ?_⟩
  intro z hz; exact leaf_4433_sound hz

theorem leaf_4434_ok : checkAt 527 1000 box_4434 cert_4434 = true := by
  have h := List.all_eq_true.mp batch_88_19_ok accepted_4434 (by simp [batch_88_19_values])
  exact h
theorem leaf_4434_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4434.profileLo box_4434.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4434_ok
theorem branch_box_4434_nonnegative : ∀ j, 0 ≤ branch_box_4434.lower j ∧ 0 ≤ branch_box_4434.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4434, Box.profileLo, Box.profileHi, box_4434]
theorem leaf_4434_BranchSafe : CertificateConsequences.BranchSafe branch_box_4434 := by
  left; refine ⟨branch_box_4434_nonnegative, ?_⟩
  intro z hz; exact leaf_4434_sound hz

theorem leaf_4435_ok : checkAt 527 1000 box_4435 cert_4435 = true := by
  have h := List.all_eq_true.mp batch_88_20_ok accepted_4435 (by simp [batch_88_20_values])
  exact h
theorem leaf_4435_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4435.profileLo box_4435.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4435_ok
theorem branch_box_4435_nonnegative : ∀ j, 0 ≤ branch_box_4435.lower j ∧ 0 ≤ branch_box_4435.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4435, Box.profileLo, Box.profileHi, box_4435]
theorem leaf_4435_BranchSafe : CertificateConsequences.BranchSafe branch_box_4435 := by
  left; refine ⟨branch_box_4435_nonnegative, ?_⟩
  intro z hz; exact leaf_4435_sound hz

theorem leaf_4436_ok : checkAt 527 1000 box_4436 cert_4436 = true := by
  have h := List.all_eq_true.mp batch_88_21_ok accepted_4436 (by simp [batch_88_21_values])
  exact h
theorem leaf_4436_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4436.profileLo box_4436.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4436_ok
theorem branch_box_4436_nonnegative : ∀ j, 0 ≤ branch_box_4436.lower j ∧ 0 ≤ branch_box_4436.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4436, Box.profileLo, Box.profileHi, box_4436]
theorem leaf_4436_BranchSafe : CertificateConsequences.BranchSafe branch_box_4436 := by
  left; refine ⟨branch_box_4436_nonnegative, ?_⟩
  intro z hz; exact leaf_4436_sound hz

theorem leaf_4444_ok : checkAt 527 1000 box_4444 cert_4444 = true := by
  have h := List.all_eq_true.mp batch_88_22_ok accepted_4444 (by simp [batch_88_22_values])
  exact h
theorem leaf_4444_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4444.profileLo box_4444.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4444_ok
theorem branch_box_4444_nonnegative : ∀ j, 0 ≤ branch_box_4444.lower j ∧ 0 ≤ branch_box_4444.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4444, Box.profileLo, Box.profileHi, box_4444]
theorem leaf_4444_BranchSafe : CertificateConsequences.BranchSafe branch_box_4444 := by
  left; refine ⟨branch_box_4444_nonnegative, ?_⟩
  intro z hz; exact leaf_4444_sound hz

theorem leaf_4445_ok : checkAt 527 1000 box_4445 cert_4445 = true := by
  have h := List.all_eq_true.mp batch_88_23_ok accepted_4445 (by simp [batch_88_23_values])
  exact h
theorem leaf_4445_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4445.profileLo box_4445.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4445_ok
theorem branch_box_4445_nonnegative : ∀ j, 0 ≤ branch_box_4445.lower j ∧ 0 ≤ branch_box_4445.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4445, Box.profileLo, Box.profileHi, box_4445]
theorem leaf_4445_BranchSafe : CertificateConsequences.BranchSafe branch_box_4445 := by
  left; refine ⟨branch_box_4445_nonnegative, ?_⟩
  intro z hz; exact leaf_4445_sound hz

theorem leaf_4446_ok : checkAt 527 1000 box_4446 cert_4446 = true := by
  have h := List.all_eq_true.mp batch_88_24_ok accepted_4446 (by simp [batch_88_24_values])
  exact h
theorem leaf_4446_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4446.profileLo box_4446.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4446_ok
theorem branch_box_4446_nonnegative : ∀ j, 0 ≤ branch_box_4446.lower j ∧ 0 ≤ branch_box_4446.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4446, Box.profileLo, Box.profileHi, box_4446]
theorem leaf_4446_BranchSafe : CertificateConsequences.BranchSafe branch_box_4446 := by
  left; refine ⟨branch_box_4446_nonnegative, ?_⟩
  intro z hz; exact leaf_4446_sound hz

theorem leaf_4448_ok : checkAt 527 1000 box_4448 cert_4448 = true := by
  have h := List.all_eq_true.mp batch_88_25_ok accepted_4448 (by simp [batch_88_25_values])
  exact h
theorem leaf_4448_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4448.profileLo box_4448.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4448_ok
theorem branch_box_4448_nonnegative : ∀ j, 0 ≤ branch_box_4448.lower j ∧ 0 ≤ branch_box_4448.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4448, Box.profileLo, Box.profileHi, box_4448]
theorem leaf_4448_BranchSafe : CertificateConsequences.BranchSafe branch_box_4448 := by
  left; refine ⟨branch_box_4448_nonnegative, ?_⟩
  intro z hz; exact leaf_4448_sound hz

theorem leaf_4449_ok : checkAt 527 1000 box_4449 cert_4449 = true := by
  have h := List.all_eq_true.mp batch_88_26_ok accepted_4449 (by simp [batch_88_26_values])
  exact h
theorem leaf_4449_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4449.profileLo box_4449.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4449_ok
theorem branch_box_4449_nonnegative : ∀ j, 0 ≤ branch_box_4449.lower j ∧ 0 ≤ branch_box_4449.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4449, Box.profileLo, Box.profileHi, box_4449]
theorem leaf_4449_BranchSafe : CertificateConsequences.BranchSafe branch_box_4449 := by
  left; refine ⟨branch_box_4449_nonnegative, ?_⟩
  intro z hz; exact leaf_4449_sound hz

#print axioms batch_88_00_ok
#print axioms leaf_4400_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
