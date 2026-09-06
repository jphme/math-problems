import PeaceableQueens.UpperBound.Generated.Even.C527Scaled128Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_128_00_values : List Bool := [accepted_6405]
theorem batch_128_00_ok : batch_128_00_values.all id = true := by decide

def batch_128_01_values : List Bool := [accepted_6406]
theorem batch_128_01_ok : batch_128_01_values.all id = true := by decide

def batch_128_02_values : List Bool := [accepted_6407]
theorem batch_128_02_ok : batch_128_02_values.all id = true := by decide

def batch_128_03_values : List Bool := [accepted_6408]
theorem batch_128_03_ok : batch_128_03_values.all id = true := by decide

def batch_128_04_values : List Bool := [accepted_6411]
theorem batch_128_04_ok : batch_128_04_values.all id = true := by decide

def batch_128_05_values : List Bool := [accepted_6412]
theorem batch_128_05_ok : batch_128_05_values.all id = true := by decide

def batch_128_06_values : List Bool := [accepted_6415]
theorem batch_128_06_ok : batch_128_06_values.all id = true := by decide

def batch_128_07_values : List Bool := [accepted_6418]
theorem batch_128_07_ok : batch_128_07_values.all id = true := by decide

def batch_128_08_values : List Bool := [accepted_6419]
theorem batch_128_08_ok : batch_128_08_values.all id = true := by decide

def batch_128_09_values : List Bool := [accepted_6421]
theorem batch_128_09_ok : batch_128_09_values.all id = true := by decide

def batch_128_10_values : List Bool := [accepted_6422]
theorem batch_128_10_ok : batch_128_10_values.all id = true := by decide

def batch_128_11_values : List Bool := [accepted_6425]
theorem batch_128_11_ok : batch_128_11_values.all id = true := by decide

def batch_128_12_values : List Bool := [accepted_6427]
theorem batch_128_12_ok : batch_128_12_values.all id = true := by decide

def batch_128_13_values : List Bool := [accepted_6430]
theorem batch_128_13_ok : batch_128_13_values.all id = true := by decide

def batch_128_14_values : List Bool := [accepted_6431]
theorem batch_128_14_ok : batch_128_14_values.all id = true := by decide

def batch_128_15_values : List Bool := [accepted_6432]
theorem batch_128_15_ok : batch_128_15_values.all id = true := by decide

def batch_128_16_values : List Bool := [accepted_6437]
theorem batch_128_16_ok : batch_128_16_values.all id = true := by decide

def batch_128_17_values : List Bool := [accepted_6438]
theorem batch_128_17_ok : batch_128_17_values.all id = true := by decide

def batch_128_18_values : List Bool := [accepted_6442]
theorem batch_128_18_ok : batch_128_18_values.all id = true := by decide

def batch_128_19_values : List Bool := [accepted_6443]
theorem batch_128_19_ok : batch_128_19_values.all id = true := by decide

def batch_128_20_values : List Bool := [accepted_6445]
theorem batch_128_20_ok : batch_128_20_values.all id = true := by decide

def batch_128_21_values : List Bool := [accepted_6446]
theorem batch_128_21_ok : batch_128_21_values.all id = true := by decide

theorem leaf_6405_ok : checkAt 527 1000 box_6405 cert_6405 = true := by
  have h := List.all_eq_true.mp batch_128_00_ok accepted_6405 (by simp [batch_128_00_values])
  exact h
theorem leaf_6405_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6405.profileLo box_6405.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6405_ok
theorem branch_box_6405_nonnegative : ∀ j, 0 ≤ branch_box_6405.lower j ∧ 0 ≤ branch_box_6405.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6405, Box.profileLo, Box.profileHi, box_6405]
theorem leaf_6405_BranchSafe : CertificateConsequences.BranchSafe branch_box_6405 := by
  left; refine ⟨branch_box_6405_nonnegative, ?_⟩
  intro z hz; exact leaf_6405_sound hz

theorem leaf_6406_ok : checkAt 527 1000 box_6406 cert_6406 = true := by
  have h := List.all_eq_true.mp batch_128_01_ok accepted_6406 (by simp [batch_128_01_values])
  exact h
theorem leaf_6406_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6406.profileLo box_6406.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6406_ok
theorem branch_box_6406_nonnegative : ∀ j, 0 ≤ branch_box_6406.lower j ∧ 0 ≤ branch_box_6406.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6406, Box.profileLo, Box.profileHi, box_6406]
theorem leaf_6406_BranchSafe : CertificateConsequences.BranchSafe branch_box_6406 := by
  left; refine ⟨branch_box_6406_nonnegative, ?_⟩
  intro z hz; exact leaf_6406_sound hz

theorem leaf_6407_ok : checkAt 527 1000 box_6407 cert_6407 = true := by
  have h := List.all_eq_true.mp batch_128_02_ok accepted_6407 (by simp [batch_128_02_values])
  exact h
theorem leaf_6407_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6407.profileLo box_6407.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6407_ok
theorem branch_box_6407_nonnegative : ∀ j, 0 ≤ branch_box_6407.lower j ∧ 0 ≤ branch_box_6407.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6407, Box.profileLo, Box.profileHi, box_6407]
theorem leaf_6407_BranchSafe : CertificateConsequences.BranchSafe branch_box_6407 := by
  left; refine ⟨branch_box_6407_nonnegative, ?_⟩
  intro z hz; exact leaf_6407_sound hz

theorem leaf_6408_ok : checkAt 527 1000 box_6408 cert_6408 = true := by
  have h := List.all_eq_true.mp batch_128_03_ok accepted_6408 (by simp [batch_128_03_values])
  exact h
theorem leaf_6408_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6408.profileLo box_6408.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6408_ok
theorem branch_box_6408_nonnegative : ∀ j, 0 ≤ branch_box_6408.lower j ∧ 0 ≤ branch_box_6408.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6408, Box.profileLo, Box.profileHi, box_6408]
theorem leaf_6408_BranchSafe : CertificateConsequences.BranchSafe branch_box_6408 := by
  left; refine ⟨branch_box_6408_nonnegative, ?_⟩
  intro z hz; exact leaf_6408_sound hz

theorem leaf_6411_ok : checkAt 527 1000 box_6411 cert_6411 = true := by
  have h := List.all_eq_true.mp batch_128_04_ok accepted_6411 (by simp [batch_128_04_values])
  exact h
theorem leaf_6411_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6411.profileLo box_6411.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6411_ok
theorem branch_box_6411_nonnegative : ∀ j, 0 ≤ branch_box_6411.lower j ∧ 0 ≤ branch_box_6411.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6411, Box.profileLo, Box.profileHi, box_6411]
theorem leaf_6411_BranchSafe : CertificateConsequences.BranchSafe branch_box_6411 := by
  left; refine ⟨branch_box_6411_nonnegative, ?_⟩
  intro z hz; exact leaf_6411_sound hz

theorem leaf_6412_ok : checkAt 527 1000 box_6412 cert_6412 = true := by
  have h := List.all_eq_true.mp batch_128_05_ok accepted_6412 (by simp [batch_128_05_values])
  exact h
theorem leaf_6412_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6412.profileLo box_6412.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6412_ok
theorem branch_box_6412_nonnegative : ∀ j, 0 ≤ branch_box_6412.lower j ∧ 0 ≤ branch_box_6412.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6412, Box.profileLo, Box.profileHi, box_6412]
theorem leaf_6412_BranchSafe : CertificateConsequences.BranchSafe branch_box_6412 := by
  left; refine ⟨branch_box_6412_nonnegative, ?_⟩
  intro z hz; exact leaf_6412_sound hz

theorem leaf_6415_ok : checkAt 527 1000 box_6415 cert_6415 = true := by
  have h := List.all_eq_true.mp batch_128_06_ok accepted_6415 (by simp [batch_128_06_values])
  exact h
theorem leaf_6415_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6415.profileLo box_6415.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6415_ok
theorem branch_box_6415_nonnegative : ∀ j, 0 ≤ branch_box_6415.lower j ∧ 0 ≤ branch_box_6415.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6415, Box.profileLo, Box.profileHi, box_6415]
theorem leaf_6415_BranchSafe : CertificateConsequences.BranchSafe branch_box_6415 := by
  left; refine ⟨branch_box_6415_nonnegative, ?_⟩
  intro z hz; exact leaf_6415_sound hz

theorem leaf_6418_ok : checkAt 527 1000 box_6418 cert_6418 = true := by
  have h := List.all_eq_true.mp batch_128_07_ok accepted_6418 (by simp [batch_128_07_values])
  exact h
theorem leaf_6418_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6418.profileLo box_6418.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6418_ok
theorem branch_box_6418_nonnegative : ∀ j, 0 ≤ branch_box_6418.lower j ∧ 0 ≤ branch_box_6418.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6418, Box.profileLo, Box.profileHi, box_6418]
theorem leaf_6418_BranchSafe : CertificateConsequences.BranchSafe branch_box_6418 := by
  left; refine ⟨branch_box_6418_nonnegative, ?_⟩
  intro z hz; exact leaf_6418_sound hz

theorem leaf_6419_ok : checkAt 527 1000 box_6419 cert_6419 = true := by
  have h := List.all_eq_true.mp batch_128_08_ok accepted_6419 (by simp [batch_128_08_values])
  exact h
theorem leaf_6419_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6419.profileLo box_6419.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6419_ok
theorem branch_box_6419_nonnegative : ∀ j, 0 ≤ branch_box_6419.lower j ∧ 0 ≤ branch_box_6419.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6419, Box.profileLo, Box.profileHi, box_6419]
theorem leaf_6419_BranchSafe : CertificateConsequences.BranchSafe branch_box_6419 := by
  left; refine ⟨branch_box_6419_nonnegative, ?_⟩
  intro z hz; exact leaf_6419_sound hz

theorem leaf_6421_ok : checkAt 527 1000 box_6421 cert_6421 = true := by
  have h := List.all_eq_true.mp batch_128_09_ok accepted_6421 (by simp [batch_128_09_values])
  exact h
theorem leaf_6421_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6421.profileLo box_6421.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6421_ok
theorem branch_box_6421_nonnegative : ∀ j, 0 ≤ branch_box_6421.lower j ∧ 0 ≤ branch_box_6421.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6421, Box.profileLo, Box.profileHi, box_6421]
theorem leaf_6421_BranchSafe : CertificateConsequences.BranchSafe branch_box_6421 := by
  left; refine ⟨branch_box_6421_nonnegative, ?_⟩
  intro z hz; exact leaf_6421_sound hz

theorem leaf_6422_ok : checkAt 527 1000 box_6422 cert_6422 = true := by
  have h := List.all_eq_true.mp batch_128_10_ok accepted_6422 (by simp [batch_128_10_values])
  exact h
theorem leaf_6422_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6422.profileLo box_6422.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6422_ok
theorem branch_box_6422_nonnegative : ∀ j, 0 ≤ branch_box_6422.lower j ∧ 0 ≤ branch_box_6422.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6422, Box.profileLo, Box.profileHi, box_6422]
theorem leaf_6422_BranchSafe : CertificateConsequences.BranchSafe branch_box_6422 := by
  left; refine ⟨branch_box_6422_nonnegative, ?_⟩
  intro z hz; exact leaf_6422_sound hz

theorem leaf_6425_ok : checkAt 527 1000 box_6425 cert_6425 = true := by
  have h := List.all_eq_true.mp batch_128_11_ok accepted_6425 (by simp [batch_128_11_values])
  exact h
theorem leaf_6425_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6425.profileLo box_6425.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6425_ok
theorem branch_box_6425_nonnegative : ∀ j, 0 ≤ branch_box_6425.lower j ∧ 0 ≤ branch_box_6425.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6425, Box.profileLo, Box.profileHi, box_6425]
theorem leaf_6425_BranchSafe : CertificateConsequences.BranchSafe branch_box_6425 := by
  left; refine ⟨branch_box_6425_nonnegative, ?_⟩
  intro z hz; exact leaf_6425_sound hz

theorem leaf_6427_ok : checkAt 527 1000 box_6427 cert_6427 = true := by
  have h := List.all_eq_true.mp batch_128_12_ok accepted_6427 (by simp [batch_128_12_values])
  exact h
theorem leaf_6427_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6427.profileLo box_6427.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6427_ok
theorem branch_box_6427_nonnegative : ∀ j, 0 ≤ branch_box_6427.lower j ∧ 0 ≤ branch_box_6427.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6427, Box.profileLo, Box.profileHi, box_6427]
theorem leaf_6427_BranchSafe : CertificateConsequences.BranchSafe branch_box_6427 := by
  left; refine ⟨branch_box_6427_nonnegative, ?_⟩
  intro z hz; exact leaf_6427_sound hz

theorem leaf_6430_ok : checkAt 527 1000 box_6430 cert_6430 = true := by
  have h := List.all_eq_true.mp batch_128_13_ok accepted_6430 (by simp [batch_128_13_values])
  exact h
theorem leaf_6430_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6430.profileLo box_6430.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6430_ok
theorem branch_box_6430_nonnegative : ∀ j, 0 ≤ branch_box_6430.lower j ∧ 0 ≤ branch_box_6430.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6430, Box.profileLo, Box.profileHi, box_6430]
theorem leaf_6430_BranchSafe : CertificateConsequences.BranchSafe branch_box_6430 := by
  left; refine ⟨branch_box_6430_nonnegative, ?_⟩
  intro z hz; exact leaf_6430_sound hz

theorem leaf_6431_ok : checkAt 527 1000 box_6431 cert_6431 = true := by
  have h := List.all_eq_true.mp batch_128_14_ok accepted_6431 (by simp [batch_128_14_values])
  exact h
theorem leaf_6431_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6431.profileLo box_6431.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6431_ok
theorem branch_box_6431_nonnegative : ∀ j, 0 ≤ branch_box_6431.lower j ∧ 0 ≤ branch_box_6431.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6431, Box.profileLo, Box.profileHi, box_6431]
theorem leaf_6431_BranchSafe : CertificateConsequences.BranchSafe branch_box_6431 := by
  left; refine ⟨branch_box_6431_nonnegative, ?_⟩
  intro z hz; exact leaf_6431_sound hz

theorem leaf_6432_ok : checkAt 527 1000 box_6432 cert_6432 = true := by
  have h := List.all_eq_true.mp batch_128_15_ok accepted_6432 (by simp [batch_128_15_values])
  exact h
theorem leaf_6432_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6432.profileLo box_6432.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6432_ok
theorem branch_box_6432_nonnegative : ∀ j, 0 ≤ branch_box_6432.lower j ∧ 0 ≤ branch_box_6432.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6432, Box.profileLo, Box.profileHi, box_6432]
theorem leaf_6432_BranchSafe : CertificateConsequences.BranchSafe branch_box_6432 := by
  left; refine ⟨branch_box_6432_nonnegative, ?_⟩
  intro z hz; exact leaf_6432_sound hz

theorem leaf_6437_ok : checkAt 527 1000 box_6437 cert_6437 = true := by
  have h := List.all_eq_true.mp batch_128_16_ok accepted_6437 (by simp [batch_128_16_values])
  exact h
theorem leaf_6437_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6437.profileLo box_6437.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6437_ok
theorem branch_box_6437_nonnegative : ∀ j, 0 ≤ branch_box_6437.lower j ∧ 0 ≤ branch_box_6437.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6437, Box.profileLo, Box.profileHi, box_6437]
theorem leaf_6437_BranchSafe : CertificateConsequences.BranchSafe branch_box_6437 := by
  left; refine ⟨branch_box_6437_nonnegative, ?_⟩
  intro z hz; exact leaf_6437_sound hz

theorem leaf_6438_ok : checkAt 527 1000 box_6438 cert_6438 = true := by
  have h := List.all_eq_true.mp batch_128_17_ok accepted_6438 (by simp [batch_128_17_values])
  exact h
theorem leaf_6438_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6438.profileLo box_6438.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6438_ok
theorem branch_box_6438_nonnegative : ∀ j, 0 ≤ branch_box_6438.lower j ∧ 0 ≤ branch_box_6438.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6438, Box.profileLo, Box.profileHi, box_6438]
theorem leaf_6438_BranchSafe : CertificateConsequences.BranchSafe branch_box_6438 := by
  left; refine ⟨branch_box_6438_nonnegative, ?_⟩
  intro z hz; exact leaf_6438_sound hz

theorem leaf_6442_ok : checkAt 527 1000 box_6442 cert_6442 = true := by
  have h := List.all_eq_true.mp batch_128_18_ok accepted_6442 (by simp [batch_128_18_values])
  exact h
theorem leaf_6442_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6442.profileLo box_6442.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6442_ok
theorem branch_box_6442_nonnegative : ∀ j, 0 ≤ branch_box_6442.lower j ∧ 0 ≤ branch_box_6442.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6442, Box.profileLo, Box.profileHi, box_6442]
theorem leaf_6442_BranchSafe : CertificateConsequences.BranchSafe branch_box_6442 := by
  left; refine ⟨branch_box_6442_nonnegative, ?_⟩
  intro z hz; exact leaf_6442_sound hz

theorem leaf_6443_ok : checkAt 527 1000 box_6443 cert_6443 = true := by
  have h := List.all_eq_true.mp batch_128_19_ok accepted_6443 (by simp [batch_128_19_values])
  exact h
theorem leaf_6443_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6443.profileLo box_6443.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6443_ok
theorem branch_box_6443_nonnegative : ∀ j, 0 ≤ branch_box_6443.lower j ∧ 0 ≤ branch_box_6443.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6443, Box.profileLo, Box.profileHi, box_6443]
theorem leaf_6443_BranchSafe : CertificateConsequences.BranchSafe branch_box_6443 := by
  left; refine ⟨branch_box_6443_nonnegative, ?_⟩
  intro z hz; exact leaf_6443_sound hz

theorem leaf_6445_ok : checkAt 527 1000 box_6445 cert_6445 = true := by
  have h := List.all_eq_true.mp batch_128_20_ok accepted_6445 (by simp [batch_128_20_values])
  exact h
theorem leaf_6445_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6445.profileLo box_6445.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6445_ok
theorem branch_box_6445_nonnegative : ∀ j, 0 ≤ branch_box_6445.lower j ∧ 0 ≤ branch_box_6445.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6445, Box.profileLo, Box.profileHi, box_6445]
theorem leaf_6445_BranchSafe : CertificateConsequences.BranchSafe branch_box_6445 := by
  left; refine ⟨branch_box_6445_nonnegative, ?_⟩
  intro z hz; exact leaf_6445_sound hz

theorem leaf_6446_ok : checkAt 527 1000 box_6446 cert_6446 = true := by
  have h := List.all_eq_true.mp batch_128_21_ok accepted_6446 (by simp [batch_128_21_values])
  exact h
theorem leaf_6446_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6446.profileLo box_6446.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6446_ok
theorem branch_box_6446_nonnegative : ∀ j, 0 ≤ branch_box_6446.lower j ∧ 0 ≤ branch_box_6446.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6446, Box.profileLo, Box.profileHi, box_6446]
theorem leaf_6446_BranchSafe : CertificateConsequences.BranchSafe branch_box_6446 := by
  left; refine ⟨branch_box_6446_nonnegative, ?_⟩
  intro z hz; exact leaf_6446_sound hz

#print axioms batch_128_00_ok
#print axioms leaf_6405_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
