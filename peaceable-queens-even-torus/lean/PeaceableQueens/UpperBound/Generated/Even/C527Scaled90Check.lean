import PeaceableQueens.UpperBound.Generated.Even.C527Scaled90Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_90_00_values : List Bool := [accepted_4501]
theorem batch_90_00_ok : batch_90_00_values.all id = true := by decide

def batch_90_01_values : List Bool := [accepted_4503]
theorem batch_90_01_ok : batch_90_01_values.all id = true := by decide

def batch_90_02_values : List Bool := [accepted_4504]
theorem batch_90_02_ok : batch_90_02_values.all id = true := by decide

def batch_90_03_values : List Bool := [accepted_4509]
theorem batch_90_03_ok : batch_90_03_values.all id = true := by decide

def batch_90_04_values : List Bool := [accepted_4511]
theorem batch_90_04_ok : batch_90_04_values.all id = true := by decide

def batch_90_05_values : List Bool := [accepted_4512]
theorem batch_90_05_ok : batch_90_05_values.all id = true := by decide

def batch_90_06_values : List Bool := [accepted_4513]
theorem batch_90_06_ok : batch_90_06_values.all id = true := by decide

def batch_90_07_values : List Bool := [accepted_4514]
theorem batch_90_07_ok : batch_90_07_values.all id = true := by decide

def batch_90_08_values : List Bool := [accepted_4519]
theorem batch_90_08_ok : batch_90_08_values.all id = true := by decide

def batch_90_09_values : List Bool := [accepted_4521]
theorem batch_90_09_ok : batch_90_09_values.all id = true := by decide

def batch_90_10_values : List Bool := [accepted_4522]
theorem batch_90_10_ok : batch_90_10_values.all id = true := by decide

def batch_90_11_values : List Bool := [accepted_4523]
theorem batch_90_11_ok : batch_90_11_values.all id = true := by decide

def batch_90_12_values : List Bool := [accepted_4524]
theorem batch_90_12_ok : batch_90_12_values.all id = true := by decide

def batch_90_13_values : List Bool := [accepted_4527]
theorem batch_90_13_ok : batch_90_13_values.all id = true := by decide

def batch_90_14_values : List Bool := [accepted_4528]
theorem batch_90_14_ok : batch_90_14_values.all id = true := by decide

def batch_90_15_values : List Bool := [accepted_4529]
theorem batch_90_15_ok : batch_90_15_values.all id = true := by decide

def batch_90_16_values : List Bool := [accepted_4530]
theorem batch_90_16_ok : batch_90_16_values.all id = true := by decide

def batch_90_17_values : List Bool := [accepted_4535]
theorem batch_90_17_ok : batch_90_17_values.all id = true := by decide

def batch_90_18_values : List Bool := [accepted_4536]
theorem batch_90_18_ok : batch_90_18_values.all id = true := by decide

def batch_90_19_values : List Bool := [accepted_4537]
theorem batch_90_19_ok : batch_90_19_values.all id = true := by decide

def batch_90_20_values : List Bool := [accepted_4538]
theorem batch_90_20_ok : batch_90_20_values.all id = true := by decide

def batch_90_21_values : List Bool := [accepted_4543]
theorem batch_90_21_ok : batch_90_21_values.all id = true := by decide

def batch_90_22_values : List Bool := [accepted_4544]
theorem batch_90_22_ok : batch_90_22_values.all id = true := by decide

def batch_90_23_values : List Bool := [accepted_4546]
theorem batch_90_23_ok : batch_90_23_values.all id = true := by decide

def batch_90_24_values : List Bool := [accepted_4547]
theorem batch_90_24_ok : batch_90_24_values.all id = true := by decide

def batch_90_25_values : List Bool := [accepted_4548]
theorem batch_90_25_ok : batch_90_25_values.all id = true := by decide

theorem leaf_4501_ok : checkAt 527 1000 box_4501 cert_4501 = true := by
  have h := List.all_eq_true.mp batch_90_00_ok accepted_4501 (by simp [batch_90_00_values])
  exact h
theorem leaf_4501_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4501.profileLo box_4501.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4501_ok
theorem branch_box_4501_nonnegative : ∀ j, 0 ≤ branch_box_4501.lower j ∧ 0 ≤ branch_box_4501.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4501, Box.profileLo, Box.profileHi, box_4501]
theorem leaf_4501_BranchSafe : CertificateConsequences.BranchSafe branch_box_4501 := by
  left; refine ⟨branch_box_4501_nonnegative, ?_⟩
  intro z hz; exact leaf_4501_sound hz

theorem leaf_4503_ok : checkAt 527 1000 box_4503 cert_4503 = true := by
  have h := List.all_eq_true.mp batch_90_01_ok accepted_4503 (by simp [batch_90_01_values])
  exact h
theorem leaf_4503_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4503.profileLo box_4503.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4503_ok
theorem branch_box_4503_nonnegative : ∀ j, 0 ≤ branch_box_4503.lower j ∧ 0 ≤ branch_box_4503.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4503, Box.profileLo, Box.profileHi, box_4503]
theorem leaf_4503_BranchSafe : CertificateConsequences.BranchSafe branch_box_4503 := by
  left; refine ⟨branch_box_4503_nonnegative, ?_⟩
  intro z hz; exact leaf_4503_sound hz

theorem leaf_4504_ok : checkAt 527 1000 box_4504 cert_4504 = true := by
  have h := List.all_eq_true.mp batch_90_02_ok accepted_4504 (by simp [batch_90_02_values])
  exact h
theorem leaf_4504_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4504.profileLo box_4504.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4504_ok
theorem branch_box_4504_nonnegative : ∀ j, 0 ≤ branch_box_4504.lower j ∧ 0 ≤ branch_box_4504.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4504, Box.profileLo, Box.profileHi, box_4504]
theorem leaf_4504_BranchSafe : CertificateConsequences.BranchSafe branch_box_4504 := by
  left; refine ⟨branch_box_4504_nonnegative, ?_⟩
  intro z hz; exact leaf_4504_sound hz

theorem leaf_4509_ok : checkAt 527 1000 box_4509 cert_4509 = true := by
  have h := List.all_eq_true.mp batch_90_03_ok accepted_4509 (by simp [batch_90_03_values])
  exact h
theorem leaf_4509_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4509.profileLo box_4509.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4509_ok
theorem branch_box_4509_nonnegative : ∀ j, 0 ≤ branch_box_4509.lower j ∧ 0 ≤ branch_box_4509.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4509, Box.profileLo, Box.profileHi, box_4509]
theorem leaf_4509_BranchSafe : CertificateConsequences.BranchSafe branch_box_4509 := by
  left; refine ⟨branch_box_4509_nonnegative, ?_⟩
  intro z hz; exact leaf_4509_sound hz

theorem leaf_4511_ok : checkAt 527 1000 box_4511 cert_4511 = true := by
  have h := List.all_eq_true.mp batch_90_04_ok accepted_4511 (by simp [batch_90_04_values])
  exact h
theorem leaf_4511_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4511.profileLo box_4511.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4511_ok
theorem branch_box_4511_nonnegative : ∀ j, 0 ≤ branch_box_4511.lower j ∧ 0 ≤ branch_box_4511.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4511, Box.profileLo, Box.profileHi, box_4511]
theorem leaf_4511_BranchSafe : CertificateConsequences.BranchSafe branch_box_4511 := by
  left; refine ⟨branch_box_4511_nonnegative, ?_⟩
  intro z hz; exact leaf_4511_sound hz

theorem leaf_4512_ok : checkAt 527 1000 box_4512 cert_4512 = true := by
  have h := List.all_eq_true.mp batch_90_05_ok accepted_4512 (by simp [batch_90_05_values])
  exact h
theorem leaf_4512_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4512.profileLo box_4512.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4512_ok
theorem branch_box_4512_nonnegative : ∀ j, 0 ≤ branch_box_4512.lower j ∧ 0 ≤ branch_box_4512.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4512, Box.profileLo, Box.profileHi, box_4512]
theorem leaf_4512_BranchSafe : CertificateConsequences.BranchSafe branch_box_4512 := by
  left; refine ⟨branch_box_4512_nonnegative, ?_⟩
  intro z hz; exact leaf_4512_sound hz

theorem leaf_4513_ok : checkAt 527 1000 box_4513 cert_4513 = true := by
  have h := List.all_eq_true.mp batch_90_06_ok accepted_4513 (by simp [batch_90_06_values])
  exact h
theorem leaf_4513_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4513.profileLo box_4513.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4513_ok
theorem branch_box_4513_nonnegative : ∀ j, 0 ≤ branch_box_4513.lower j ∧ 0 ≤ branch_box_4513.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4513, Box.profileLo, Box.profileHi, box_4513]
theorem leaf_4513_BranchSafe : CertificateConsequences.BranchSafe branch_box_4513 := by
  left; refine ⟨branch_box_4513_nonnegative, ?_⟩
  intro z hz; exact leaf_4513_sound hz

theorem leaf_4514_ok : checkAt 527 1000 box_4514 cert_4514 = true := by
  have h := List.all_eq_true.mp batch_90_07_ok accepted_4514 (by simp [batch_90_07_values])
  exact h
theorem leaf_4514_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4514.profileLo box_4514.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4514_ok
theorem branch_box_4514_nonnegative : ∀ j, 0 ≤ branch_box_4514.lower j ∧ 0 ≤ branch_box_4514.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4514, Box.profileLo, Box.profileHi, box_4514]
theorem leaf_4514_BranchSafe : CertificateConsequences.BranchSafe branch_box_4514 := by
  left; refine ⟨branch_box_4514_nonnegative, ?_⟩
  intro z hz; exact leaf_4514_sound hz

theorem leaf_4519_ok : checkAt 527 1000 box_4519 cert_4519 = true := by
  have h := List.all_eq_true.mp batch_90_08_ok accepted_4519 (by simp [batch_90_08_values])
  exact h
theorem leaf_4519_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4519.profileLo box_4519.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4519_ok
theorem branch_box_4519_nonnegative : ∀ j, 0 ≤ branch_box_4519.lower j ∧ 0 ≤ branch_box_4519.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4519, Box.profileLo, Box.profileHi, box_4519]
theorem leaf_4519_BranchSafe : CertificateConsequences.BranchSafe branch_box_4519 := by
  left; refine ⟨branch_box_4519_nonnegative, ?_⟩
  intro z hz; exact leaf_4519_sound hz

theorem leaf_4521_ok : checkAt 527 1000 box_4521 cert_4521 = true := by
  have h := List.all_eq_true.mp batch_90_09_ok accepted_4521 (by simp [batch_90_09_values])
  exact h
theorem leaf_4521_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4521.profileLo box_4521.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4521_ok
theorem branch_box_4521_nonnegative : ∀ j, 0 ≤ branch_box_4521.lower j ∧ 0 ≤ branch_box_4521.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4521, Box.profileLo, Box.profileHi, box_4521]
theorem leaf_4521_BranchSafe : CertificateConsequences.BranchSafe branch_box_4521 := by
  left; refine ⟨branch_box_4521_nonnegative, ?_⟩
  intro z hz; exact leaf_4521_sound hz

theorem leaf_4522_ok : checkAt 527 1000 box_4522 cert_4522 = true := by
  have h := List.all_eq_true.mp batch_90_10_ok accepted_4522 (by simp [batch_90_10_values])
  exact h
theorem leaf_4522_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4522.profileLo box_4522.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4522_ok
theorem branch_box_4522_nonnegative : ∀ j, 0 ≤ branch_box_4522.lower j ∧ 0 ≤ branch_box_4522.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4522, Box.profileLo, Box.profileHi, box_4522]
theorem leaf_4522_BranchSafe : CertificateConsequences.BranchSafe branch_box_4522 := by
  left; refine ⟨branch_box_4522_nonnegative, ?_⟩
  intro z hz; exact leaf_4522_sound hz

theorem leaf_4523_ok : checkAt 527 1000 box_4523 cert_4523 = true := by
  have h := List.all_eq_true.mp batch_90_11_ok accepted_4523 (by simp [batch_90_11_values])
  exact h
theorem leaf_4523_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4523.profileLo box_4523.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4523_ok
theorem branch_box_4523_nonnegative : ∀ j, 0 ≤ branch_box_4523.lower j ∧ 0 ≤ branch_box_4523.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4523, Box.profileLo, Box.profileHi, box_4523]
theorem leaf_4523_BranchSafe : CertificateConsequences.BranchSafe branch_box_4523 := by
  left; refine ⟨branch_box_4523_nonnegative, ?_⟩
  intro z hz; exact leaf_4523_sound hz

theorem leaf_4524_ok : checkAt 527 1000 box_4524 cert_4524 = true := by
  have h := List.all_eq_true.mp batch_90_12_ok accepted_4524 (by simp [batch_90_12_values])
  exact h
theorem leaf_4524_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4524.profileLo box_4524.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4524_ok
theorem branch_box_4524_nonnegative : ∀ j, 0 ≤ branch_box_4524.lower j ∧ 0 ≤ branch_box_4524.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4524, Box.profileLo, Box.profileHi, box_4524]
theorem leaf_4524_BranchSafe : CertificateConsequences.BranchSafe branch_box_4524 := by
  left; refine ⟨branch_box_4524_nonnegative, ?_⟩
  intro z hz; exact leaf_4524_sound hz

theorem leaf_4527_ok : checkAt 527 1000 box_4527 cert_4527 = true := by
  have h := List.all_eq_true.mp batch_90_13_ok accepted_4527 (by simp [batch_90_13_values])
  exact h
theorem leaf_4527_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4527.profileLo box_4527.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4527_ok
theorem branch_box_4527_nonnegative : ∀ j, 0 ≤ branch_box_4527.lower j ∧ 0 ≤ branch_box_4527.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4527, Box.profileLo, Box.profileHi, box_4527]
theorem leaf_4527_BranchSafe : CertificateConsequences.BranchSafe branch_box_4527 := by
  left; refine ⟨branch_box_4527_nonnegative, ?_⟩
  intro z hz; exact leaf_4527_sound hz

theorem leaf_4528_ok : checkAt 527 1000 box_4528 cert_4528 = true := by
  have h := List.all_eq_true.mp batch_90_14_ok accepted_4528 (by simp [batch_90_14_values])
  exact h
theorem leaf_4528_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4528.profileLo box_4528.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4528_ok
theorem branch_box_4528_nonnegative : ∀ j, 0 ≤ branch_box_4528.lower j ∧ 0 ≤ branch_box_4528.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4528, Box.profileLo, Box.profileHi, box_4528]
theorem leaf_4528_BranchSafe : CertificateConsequences.BranchSafe branch_box_4528 := by
  left; refine ⟨branch_box_4528_nonnegative, ?_⟩
  intro z hz; exact leaf_4528_sound hz

theorem leaf_4529_ok : checkAt 527 1000 box_4529 cert_4529 = true := by
  have h := List.all_eq_true.mp batch_90_15_ok accepted_4529 (by simp [batch_90_15_values])
  exact h
theorem leaf_4529_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4529.profileLo box_4529.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4529_ok
theorem branch_box_4529_nonnegative : ∀ j, 0 ≤ branch_box_4529.lower j ∧ 0 ≤ branch_box_4529.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4529, Box.profileLo, Box.profileHi, box_4529]
theorem leaf_4529_BranchSafe : CertificateConsequences.BranchSafe branch_box_4529 := by
  left; refine ⟨branch_box_4529_nonnegative, ?_⟩
  intro z hz; exact leaf_4529_sound hz

theorem leaf_4530_ok : checkAt 527 1000 box_4530 cert_4530 = true := by
  have h := List.all_eq_true.mp batch_90_16_ok accepted_4530 (by simp [batch_90_16_values])
  exact h
theorem leaf_4530_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4530.profileLo box_4530.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4530_ok
theorem branch_box_4530_nonnegative : ∀ j, 0 ≤ branch_box_4530.lower j ∧ 0 ≤ branch_box_4530.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4530, Box.profileLo, Box.profileHi, box_4530]
theorem leaf_4530_BranchSafe : CertificateConsequences.BranchSafe branch_box_4530 := by
  left; refine ⟨branch_box_4530_nonnegative, ?_⟩
  intro z hz; exact leaf_4530_sound hz

theorem leaf_4535_ok : checkAt 527 1000 box_4535 cert_4535 = true := by
  have h := List.all_eq_true.mp batch_90_17_ok accepted_4535 (by simp [batch_90_17_values])
  exact h
theorem leaf_4535_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4535.profileLo box_4535.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4535_ok
theorem branch_box_4535_nonnegative : ∀ j, 0 ≤ branch_box_4535.lower j ∧ 0 ≤ branch_box_4535.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4535, Box.profileLo, Box.profileHi, box_4535]
theorem leaf_4535_BranchSafe : CertificateConsequences.BranchSafe branch_box_4535 := by
  left; refine ⟨branch_box_4535_nonnegative, ?_⟩
  intro z hz; exact leaf_4535_sound hz

theorem leaf_4536_ok : checkAt 527 1000 box_4536 cert_4536 = true := by
  have h := List.all_eq_true.mp batch_90_18_ok accepted_4536 (by simp [batch_90_18_values])
  exact h
theorem leaf_4536_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4536.profileLo box_4536.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4536_ok
theorem branch_box_4536_nonnegative : ∀ j, 0 ≤ branch_box_4536.lower j ∧ 0 ≤ branch_box_4536.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4536, Box.profileLo, Box.profileHi, box_4536]
theorem leaf_4536_BranchSafe : CertificateConsequences.BranchSafe branch_box_4536 := by
  left; refine ⟨branch_box_4536_nonnegative, ?_⟩
  intro z hz; exact leaf_4536_sound hz

theorem leaf_4537_ok : checkAt 527 1000 box_4537 cert_4537 = true := by
  have h := List.all_eq_true.mp batch_90_19_ok accepted_4537 (by simp [batch_90_19_values])
  exact h
theorem leaf_4537_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4537.profileLo box_4537.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4537_ok
theorem branch_box_4537_nonnegative : ∀ j, 0 ≤ branch_box_4537.lower j ∧ 0 ≤ branch_box_4537.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4537, Box.profileLo, Box.profileHi, box_4537]
theorem leaf_4537_BranchSafe : CertificateConsequences.BranchSafe branch_box_4537 := by
  left; refine ⟨branch_box_4537_nonnegative, ?_⟩
  intro z hz; exact leaf_4537_sound hz

theorem leaf_4538_ok : checkAt 527 1000 box_4538 cert_4538 = true := by
  have h := List.all_eq_true.mp batch_90_20_ok accepted_4538 (by simp [batch_90_20_values])
  exact h
theorem leaf_4538_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4538.profileLo box_4538.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4538_ok
theorem branch_box_4538_nonnegative : ∀ j, 0 ≤ branch_box_4538.lower j ∧ 0 ≤ branch_box_4538.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4538, Box.profileLo, Box.profileHi, box_4538]
theorem leaf_4538_BranchSafe : CertificateConsequences.BranchSafe branch_box_4538 := by
  left; refine ⟨branch_box_4538_nonnegative, ?_⟩
  intro z hz; exact leaf_4538_sound hz

theorem leaf_4543_ok : checkAt 527 1000 box_4543 cert_4543 = true := by
  have h := List.all_eq_true.mp batch_90_21_ok accepted_4543 (by simp [batch_90_21_values])
  exact h
theorem leaf_4543_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4543.profileLo box_4543.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4543_ok
theorem branch_box_4543_nonnegative : ∀ j, 0 ≤ branch_box_4543.lower j ∧ 0 ≤ branch_box_4543.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4543, Box.profileLo, Box.profileHi, box_4543]
theorem leaf_4543_BranchSafe : CertificateConsequences.BranchSafe branch_box_4543 := by
  left; refine ⟨branch_box_4543_nonnegative, ?_⟩
  intro z hz; exact leaf_4543_sound hz

theorem leaf_4544_ok : checkAt 527 1000 box_4544 cert_4544 = true := by
  have h := List.all_eq_true.mp batch_90_22_ok accepted_4544 (by simp [batch_90_22_values])
  exact h
theorem leaf_4544_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4544.profileLo box_4544.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4544_ok
theorem branch_box_4544_nonnegative : ∀ j, 0 ≤ branch_box_4544.lower j ∧ 0 ≤ branch_box_4544.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4544, Box.profileLo, Box.profileHi, box_4544]
theorem leaf_4544_BranchSafe : CertificateConsequences.BranchSafe branch_box_4544 := by
  left; refine ⟨branch_box_4544_nonnegative, ?_⟩
  intro z hz; exact leaf_4544_sound hz

theorem leaf_4546_ok : checkAt 527 1000 box_4546 cert_4546 = true := by
  have h := List.all_eq_true.mp batch_90_23_ok accepted_4546 (by simp [batch_90_23_values])
  exact h
theorem leaf_4546_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4546.profileLo box_4546.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4546_ok
theorem branch_box_4546_nonnegative : ∀ j, 0 ≤ branch_box_4546.lower j ∧ 0 ≤ branch_box_4546.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4546, Box.profileLo, Box.profileHi, box_4546]
theorem leaf_4546_BranchSafe : CertificateConsequences.BranchSafe branch_box_4546 := by
  left; refine ⟨branch_box_4546_nonnegative, ?_⟩
  intro z hz; exact leaf_4546_sound hz

theorem leaf_4547_ok : checkAt 527 1000 box_4547 cert_4547 = true := by
  have h := List.all_eq_true.mp batch_90_24_ok accepted_4547 (by simp [batch_90_24_values])
  exact h
theorem leaf_4547_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4547.profileLo box_4547.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4547_ok
theorem branch_box_4547_nonnegative : ∀ j, 0 ≤ branch_box_4547.lower j ∧ 0 ≤ branch_box_4547.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4547, Box.profileLo, Box.profileHi, box_4547]
theorem leaf_4547_BranchSafe : CertificateConsequences.BranchSafe branch_box_4547 := by
  left; refine ⟨branch_box_4547_nonnegative, ?_⟩
  intro z hz; exact leaf_4547_sound hz

theorem leaf_4548_ok : checkAt 527 1000 box_4548 cert_4548 = true := by
  have h := List.all_eq_true.mp batch_90_25_ok accepted_4548 (by simp [batch_90_25_values])
  exact h
theorem leaf_4548_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4548.profileLo box_4548.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4548_ok
theorem branch_box_4548_nonnegative : ∀ j, 0 ≤ branch_box_4548.lower j ∧ 0 ≤ branch_box_4548.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4548, Box.profileLo, Box.profileHi, box_4548]
theorem leaf_4548_BranchSafe : CertificateConsequences.BranchSafe branch_box_4548 := by
  left; refine ⟨branch_box_4548_nonnegative, ?_⟩
  intro z hz; exact leaf_4548_sound hz

#print axioms batch_90_00_ok
#print axioms leaf_4501_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
