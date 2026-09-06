import PeaceableQueens.UpperBound.Generated.Even.C527Scaled110Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_110_00_values : List Bool := [accepted_5503]
theorem batch_110_00_ok : batch_110_00_values.all id = true := by decide

def batch_110_01_values : List Bool := [accepted_5504]
theorem batch_110_01_ok : batch_110_01_values.all id = true := by decide

def batch_110_02_values : List Bool := [accepted_5506]
theorem batch_110_02_ok : batch_110_02_values.all id = true := by decide

def batch_110_03_values : List Bool := [accepted_5507]
theorem batch_110_03_ok : batch_110_03_values.all id = true := by decide

def batch_110_04_values : List Bool := [accepted_5508]
theorem batch_110_04_ok : batch_110_04_values.all id = true := by decide

def batch_110_05_values : List Bool := [accepted_5511]
theorem batch_110_05_ok : batch_110_05_values.all id = true := by decide

def batch_110_06_values : List Bool := [accepted_5512]
theorem batch_110_06_ok : batch_110_06_values.all id = true := by decide

def batch_110_07_values : List Bool := [accepted_5515]
theorem batch_110_07_ok : batch_110_07_values.all id = true := by decide

def batch_110_08_values : List Bool := [accepted_5516]
theorem batch_110_08_ok : batch_110_08_values.all id = true := by decide

def batch_110_09_values : List Bool := [accepted_5518]
theorem batch_110_09_ok : batch_110_09_values.all id = true := by decide

def batch_110_10_values : List Bool := [accepted_5520]
theorem batch_110_10_ok : batch_110_10_values.all id = true := by decide

def batch_110_11_values : List Bool := [accepted_5521]
theorem batch_110_11_ok : batch_110_11_values.all id = true := by decide

def batch_110_12_values : List Bool := [accepted_5522]
theorem batch_110_12_ok : batch_110_12_values.all id = true := by decide

def batch_110_13_values : List Bool := [accepted_5525]
theorem batch_110_13_ok : batch_110_13_values.all id = true := by decide

def batch_110_14_values : List Bool := [accepted_5528]
theorem batch_110_14_ok : batch_110_14_values.all id = true := by decide

def batch_110_15_values : List Bool := [accepted_5530]
theorem batch_110_15_ok : batch_110_15_values.all id = true := by decide

def batch_110_16_values : List Bool := [accepted_5531]
theorem batch_110_16_ok : batch_110_16_values.all id = true := by decide

def batch_110_17_values : List Bool := [accepted_5532]
theorem batch_110_17_ok : batch_110_17_values.all id = true := by decide

def batch_110_18_values : List Bool := [accepted_5535]
theorem batch_110_18_ok : batch_110_18_values.all id = true := by decide

def batch_110_19_values : List Bool := [accepted_5536]
theorem batch_110_19_ok : batch_110_19_values.all id = true := by decide

def batch_110_20_values : List Bool := [accepted_5537]
theorem batch_110_20_ok : batch_110_20_values.all id = true := by decide

def batch_110_21_values : List Bool := [accepted_5539]
theorem batch_110_21_ok : batch_110_21_values.all id = true := by decide

def batch_110_22_values : List Bool := [accepted_5540]
theorem batch_110_22_ok : batch_110_22_values.all id = true := by decide

def batch_110_23_values : List Bool := [accepted_5547]
theorem batch_110_23_ok : batch_110_23_values.all id = true := by decide

theorem leaf_5503_ok : checkAt 527 1000 box_5503 cert_5503 = true := by
  have h := List.all_eq_true.mp batch_110_00_ok accepted_5503 (by simp [batch_110_00_values])
  exact h
theorem leaf_5503_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5503.profileLo box_5503.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5503_ok
theorem branch_box_5503_nonnegative : ∀ j, 0 ≤ branch_box_5503.lower j ∧ 0 ≤ branch_box_5503.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5503, Box.profileLo, Box.profileHi, box_5503]
theorem leaf_5503_BranchSafe : CertificateConsequences.BranchSafe branch_box_5503 := by
  left; refine ⟨branch_box_5503_nonnegative, ?_⟩
  intro z hz; exact leaf_5503_sound hz

theorem leaf_5504_ok : checkAt 527 1000 box_5504 cert_5504 = true := by
  have h := List.all_eq_true.mp batch_110_01_ok accepted_5504 (by simp [batch_110_01_values])
  exact h
theorem leaf_5504_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5504.profileLo box_5504.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5504_ok
theorem branch_box_5504_nonnegative : ∀ j, 0 ≤ branch_box_5504.lower j ∧ 0 ≤ branch_box_5504.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5504, Box.profileLo, Box.profileHi, box_5504]
theorem leaf_5504_BranchSafe : CertificateConsequences.BranchSafe branch_box_5504 := by
  left; refine ⟨branch_box_5504_nonnegative, ?_⟩
  intro z hz; exact leaf_5504_sound hz

theorem leaf_5506_ok : checkAt 527 1000 box_5506 cert_5506 = true := by
  have h := List.all_eq_true.mp batch_110_02_ok accepted_5506 (by simp [batch_110_02_values])
  exact h
theorem leaf_5506_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5506.profileLo box_5506.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5506_ok
theorem branch_box_5506_nonnegative : ∀ j, 0 ≤ branch_box_5506.lower j ∧ 0 ≤ branch_box_5506.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5506, Box.profileLo, Box.profileHi, box_5506]
theorem leaf_5506_BranchSafe : CertificateConsequences.BranchSafe branch_box_5506 := by
  left; refine ⟨branch_box_5506_nonnegative, ?_⟩
  intro z hz; exact leaf_5506_sound hz

theorem leaf_5507_ok : checkAt 527 1000 box_5507 cert_5507 = true := by
  have h := List.all_eq_true.mp batch_110_03_ok accepted_5507 (by simp [batch_110_03_values])
  exact h
theorem leaf_5507_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5507.profileLo box_5507.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5507_ok
theorem branch_box_5507_nonnegative : ∀ j, 0 ≤ branch_box_5507.lower j ∧ 0 ≤ branch_box_5507.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5507, Box.profileLo, Box.profileHi, box_5507]
theorem leaf_5507_BranchSafe : CertificateConsequences.BranchSafe branch_box_5507 := by
  left; refine ⟨branch_box_5507_nonnegative, ?_⟩
  intro z hz; exact leaf_5507_sound hz

theorem leaf_5508_ok : checkAt 527 1000 box_5508 cert_5508 = true := by
  have h := List.all_eq_true.mp batch_110_04_ok accepted_5508 (by simp [batch_110_04_values])
  exact h
theorem leaf_5508_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5508.profileLo box_5508.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5508_ok
theorem branch_box_5508_nonnegative : ∀ j, 0 ≤ branch_box_5508.lower j ∧ 0 ≤ branch_box_5508.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5508, Box.profileLo, Box.profileHi, box_5508]
theorem leaf_5508_BranchSafe : CertificateConsequences.BranchSafe branch_box_5508 := by
  left; refine ⟨branch_box_5508_nonnegative, ?_⟩
  intro z hz; exact leaf_5508_sound hz

theorem leaf_5511_ok : checkAt 527 1000 box_5511 cert_5511 = true := by
  have h := List.all_eq_true.mp batch_110_05_ok accepted_5511 (by simp [batch_110_05_values])
  exact h
theorem leaf_5511_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5511.profileLo box_5511.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5511_ok
theorem branch_box_5511_nonnegative : ∀ j, 0 ≤ branch_box_5511.lower j ∧ 0 ≤ branch_box_5511.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5511, Box.profileLo, Box.profileHi, box_5511]
theorem leaf_5511_BranchSafe : CertificateConsequences.BranchSafe branch_box_5511 := by
  left; refine ⟨branch_box_5511_nonnegative, ?_⟩
  intro z hz; exact leaf_5511_sound hz

theorem leaf_5512_ok : checkAt 527 1000 box_5512 cert_5512 = true := by
  have h := List.all_eq_true.mp batch_110_06_ok accepted_5512 (by simp [batch_110_06_values])
  exact h
theorem leaf_5512_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5512.profileLo box_5512.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5512_ok
theorem branch_box_5512_nonnegative : ∀ j, 0 ≤ branch_box_5512.lower j ∧ 0 ≤ branch_box_5512.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5512, Box.profileLo, Box.profileHi, box_5512]
theorem leaf_5512_BranchSafe : CertificateConsequences.BranchSafe branch_box_5512 := by
  left; refine ⟨branch_box_5512_nonnegative, ?_⟩
  intro z hz; exact leaf_5512_sound hz

theorem leaf_5515_ok : checkAt 527 1000 box_5515 cert_5515 = true := by
  have h := List.all_eq_true.mp batch_110_07_ok accepted_5515 (by simp [batch_110_07_values])
  exact h
theorem leaf_5515_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5515.profileLo box_5515.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5515_ok
theorem branch_box_5515_nonnegative : ∀ j, 0 ≤ branch_box_5515.lower j ∧ 0 ≤ branch_box_5515.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5515, Box.profileLo, Box.profileHi, box_5515]
theorem leaf_5515_BranchSafe : CertificateConsequences.BranchSafe branch_box_5515 := by
  left; refine ⟨branch_box_5515_nonnegative, ?_⟩
  intro z hz; exact leaf_5515_sound hz

theorem leaf_5516_ok : checkAt 527 1000 box_5516 cert_5516 = true := by
  have h := List.all_eq_true.mp batch_110_08_ok accepted_5516 (by simp [batch_110_08_values])
  exact h
theorem leaf_5516_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5516.profileLo box_5516.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5516_ok
theorem branch_box_5516_nonnegative : ∀ j, 0 ≤ branch_box_5516.lower j ∧ 0 ≤ branch_box_5516.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5516, Box.profileLo, Box.profileHi, box_5516]
theorem leaf_5516_BranchSafe : CertificateConsequences.BranchSafe branch_box_5516 := by
  left; refine ⟨branch_box_5516_nonnegative, ?_⟩
  intro z hz; exact leaf_5516_sound hz

theorem leaf_5518_ok : checkAt 527 1000 box_5518 cert_5518 = true := by
  have h := List.all_eq_true.mp batch_110_09_ok accepted_5518 (by simp [batch_110_09_values])
  exact h
theorem leaf_5518_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5518.profileLo box_5518.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5518_ok
theorem branch_box_5518_nonnegative : ∀ j, 0 ≤ branch_box_5518.lower j ∧ 0 ≤ branch_box_5518.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5518, Box.profileLo, Box.profileHi, box_5518]
theorem leaf_5518_BranchSafe : CertificateConsequences.BranchSafe branch_box_5518 := by
  left; refine ⟨branch_box_5518_nonnegative, ?_⟩
  intro z hz; exact leaf_5518_sound hz

theorem leaf_5520_ok : checkAt 527 1000 box_5520 cert_5520 = true := by
  have h := List.all_eq_true.mp batch_110_10_ok accepted_5520 (by simp [batch_110_10_values])
  exact h
theorem leaf_5520_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5520.profileLo box_5520.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5520_ok
theorem branch_box_5520_nonnegative : ∀ j, 0 ≤ branch_box_5520.lower j ∧ 0 ≤ branch_box_5520.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5520, Box.profileLo, Box.profileHi, box_5520]
theorem leaf_5520_BranchSafe : CertificateConsequences.BranchSafe branch_box_5520 := by
  left; refine ⟨branch_box_5520_nonnegative, ?_⟩
  intro z hz; exact leaf_5520_sound hz

theorem leaf_5521_ok : checkAt 527 1000 box_5521 cert_5521 = true := by
  have h := List.all_eq_true.mp batch_110_11_ok accepted_5521 (by simp [batch_110_11_values])
  exact h
theorem leaf_5521_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5521.profileLo box_5521.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5521_ok
theorem branch_box_5521_nonnegative : ∀ j, 0 ≤ branch_box_5521.lower j ∧ 0 ≤ branch_box_5521.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5521, Box.profileLo, Box.profileHi, box_5521]
theorem leaf_5521_BranchSafe : CertificateConsequences.BranchSafe branch_box_5521 := by
  left; refine ⟨branch_box_5521_nonnegative, ?_⟩
  intro z hz; exact leaf_5521_sound hz

theorem leaf_5522_ok : checkAt 527 1000 box_5522 cert_5522 = true := by
  have h := List.all_eq_true.mp batch_110_12_ok accepted_5522 (by simp [batch_110_12_values])
  exact h
theorem leaf_5522_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5522.profileLo box_5522.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5522_ok
theorem branch_box_5522_nonnegative : ∀ j, 0 ≤ branch_box_5522.lower j ∧ 0 ≤ branch_box_5522.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5522, Box.profileLo, Box.profileHi, box_5522]
theorem leaf_5522_BranchSafe : CertificateConsequences.BranchSafe branch_box_5522 := by
  left; refine ⟨branch_box_5522_nonnegative, ?_⟩
  intro z hz; exact leaf_5522_sound hz

theorem leaf_5525_ok : checkAt 527 1000 box_5525 cert_5525 = true := by
  have h := List.all_eq_true.mp batch_110_13_ok accepted_5525 (by simp [batch_110_13_values])
  exact h
theorem leaf_5525_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5525.profileLo box_5525.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5525_ok
theorem branch_box_5525_nonnegative : ∀ j, 0 ≤ branch_box_5525.lower j ∧ 0 ≤ branch_box_5525.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5525, Box.profileLo, Box.profileHi, box_5525]
theorem leaf_5525_BranchSafe : CertificateConsequences.BranchSafe branch_box_5525 := by
  left; refine ⟨branch_box_5525_nonnegative, ?_⟩
  intro z hz; exact leaf_5525_sound hz

theorem leaf_5528_ok : checkAt 527 1000 box_5528 cert_5528 = true := by
  have h := List.all_eq_true.mp batch_110_14_ok accepted_5528 (by simp [batch_110_14_values])
  exact h
theorem leaf_5528_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5528.profileLo box_5528.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5528_ok
theorem branch_box_5528_nonnegative : ∀ j, 0 ≤ branch_box_5528.lower j ∧ 0 ≤ branch_box_5528.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5528, Box.profileLo, Box.profileHi, box_5528]
theorem leaf_5528_BranchSafe : CertificateConsequences.BranchSafe branch_box_5528 := by
  left; refine ⟨branch_box_5528_nonnegative, ?_⟩
  intro z hz; exact leaf_5528_sound hz

theorem leaf_5530_ok : checkAt 527 1000 box_5530 cert_5530 = true := by
  have h := List.all_eq_true.mp batch_110_15_ok accepted_5530 (by simp [batch_110_15_values])
  exact h
theorem leaf_5530_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5530.profileLo box_5530.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5530_ok
theorem branch_box_5530_nonnegative : ∀ j, 0 ≤ branch_box_5530.lower j ∧ 0 ≤ branch_box_5530.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5530, Box.profileLo, Box.profileHi, box_5530]
theorem leaf_5530_BranchSafe : CertificateConsequences.BranchSafe branch_box_5530 := by
  left; refine ⟨branch_box_5530_nonnegative, ?_⟩
  intro z hz; exact leaf_5530_sound hz

theorem leaf_5531_ok : checkAt 527 1000 box_5531 cert_5531 = true := by
  have h := List.all_eq_true.mp batch_110_16_ok accepted_5531 (by simp [batch_110_16_values])
  exact h
theorem leaf_5531_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5531.profileLo box_5531.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5531_ok
theorem branch_box_5531_nonnegative : ∀ j, 0 ≤ branch_box_5531.lower j ∧ 0 ≤ branch_box_5531.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5531, Box.profileLo, Box.profileHi, box_5531]
theorem leaf_5531_BranchSafe : CertificateConsequences.BranchSafe branch_box_5531 := by
  left; refine ⟨branch_box_5531_nonnegative, ?_⟩
  intro z hz; exact leaf_5531_sound hz

theorem leaf_5532_ok : checkAt 527 1000 box_5532 cert_5532 = true := by
  have h := List.all_eq_true.mp batch_110_17_ok accepted_5532 (by simp [batch_110_17_values])
  exact h
theorem leaf_5532_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5532.profileLo box_5532.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5532_ok
theorem branch_box_5532_nonnegative : ∀ j, 0 ≤ branch_box_5532.lower j ∧ 0 ≤ branch_box_5532.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5532, Box.profileLo, Box.profileHi, box_5532]
theorem leaf_5532_BranchSafe : CertificateConsequences.BranchSafe branch_box_5532 := by
  left; refine ⟨branch_box_5532_nonnegative, ?_⟩
  intro z hz; exact leaf_5532_sound hz

theorem leaf_5535_ok : checkAt 527 1000 box_5535 cert_5535 = true := by
  have h := List.all_eq_true.mp batch_110_18_ok accepted_5535 (by simp [batch_110_18_values])
  exact h
theorem leaf_5535_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5535.profileLo box_5535.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5535_ok
theorem branch_box_5535_nonnegative : ∀ j, 0 ≤ branch_box_5535.lower j ∧ 0 ≤ branch_box_5535.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5535, Box.profileLo, Box.profileHi, box_5535]
theorem leaf_5535_BranchSafe : CertificateConsequences.BranchSafe branch_box_5535 := by
  left; refine ⟨branch_box_5535_nonnegative, ?_⟩
  intro z hz; exact leaf_5535_sound hz

theorem leaf_5536_ok : checkAt 527 1000 box_5536 cert_5536 = true := by
  have h := List.all_eq_true.mp batch_110_19_ok accepted_5536 (by simp [batch_110_19_values])
  exact h
theorem leaf_5536_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5536.profileLo box_5536.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5536_ok
theorem branch_box_5536_nonnegative : ∀ j, 0 ≤ branch_box_5536.lower j ∧ 0 ≤ branch_box_5536.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5536, Box.profileLo, Box.profileHi, box_5536]
theorem leaf_5536_BranchSafe : CertificateConsequences.BranchSafe branch_box_5536 := by
  left; refine ⟨branch_box_5536_nonnegative, ?_⟩
  intro z hz; exact leaf_5536_sound hz

theorem leaf_5537_ok : checkAt 527 1000 box_5537 cert_5537 = true := by
  have h := List.all_eq_true.mp batch_110_20_ok accepted_5537 (by simp [batch_110_20_values])
  exact h
theorem leaf_5537_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5537.profileLo box_5537.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5537_ok
theorem branch_box_5537_nonnegative : ∀ j, 0 ≤ branch_box_5537.lower j ∧ 0 ≤ branch_box_5537.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5537, Box.profileLo, Box.profileHi, box_5537]
theorem leaf_5537_BranchSafe : CertificateConsequences.BranchSafe branch_box_5537 := by
  left; refine ⟨branch_box_5537_nonnegative, ?_⟩
  intro z hz; exact leaf_5537_sound hz

theorem leaf_5539_ok : checkAt 527 1000 box_5539 cert_5539 = true := by
  have h := List.all_eq_true.mp batch_110_21_ok accepted_5539 (by simp [batch_110_21_values])
  exact h
theorem leaf_5539_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5539.profileLo box_5539.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5539_ok
theorem branch_box_5539_nonnegative : ∀ j, 0 ≤ branch_box_5539.lower j ∧ 0 ≤ branch_box_5539.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5539, Box.profileLo, Box.profileHi, box_5539]
theorem leaf_5539_BranchSafe : CertificateConsequences.BranchSafe branch_box_5539 := by
  left; refine ⟨branch_box_5539_nonnegative, ?_⟩
  intro z hz; exact leaf_5539_sound hz

theorem leaf_5540_ok : checkAt 527 1000 box_5540 cert_5540 = true := by
  have h := List.all_eq_true.mp batch_110_22_ok accepted_5540 (by simp [batch_110_22_values])
  exact h
theorem leaf_5540_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5540.profileLo box_5540.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5540_ok
theorem branch_box_5540_nonnegative : ∀ j, 0 ≤ branch_box_5540.lower j ∧ 0 ≤ branch_box_5540.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5540, Box.profileLo, Box.profileHi, box_5540]
theorem leaf_5540_BranchSafe : CertificateConsequences.BranchSafe branch_box_5540 := by
  left; refine ⟨branch_box_5540_nonnegative, ?_⟩
  intro z hz; exact leaf_5540_sound hz

theorem leaf_5547_ok : checkAt 527 1000 box_5547 cert_5547 = true := by
  have h := List.all_eq_true.mp batch_110_23_ok accepted_5547 (by simp [batch_110_23_values])
  exact h
theorem leaf_5547_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5547.profileLo box_5547.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5547_ok
theorem branch_box_5547_nonnegative : ∀ j, 0 ≤ branch_box_5547.lower j ∧ 0 ≤ branch_box_5547.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5547, Box.profileLo, Box.profileHi, box_5547]
theorem leaf_5547_BranchSafe : CertificateConsequences.BranchSafe branch_box_5547 := by
  left; refine ⟨branch_box_5547_nonnegative, ?_⟩
  intro z hz; exact leaf_5547_sound hz

#print axioms batch_110_00_ok
#print axioms leaf_5503_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
