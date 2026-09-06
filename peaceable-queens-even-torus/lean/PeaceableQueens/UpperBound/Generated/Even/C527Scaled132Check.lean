import PeaceableQueens.UpperBound.Generated.Even.C527Scaled132Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_132_00_values : List Bool := [accepted_6601]
theorem batch_132_00_ok : batch_132_00_values.all id = true := by decide

def batch_132_01_values : List Bool := [accepted_6602]
theorem batch_132_01_ok : batch_132_01_values.all id = true := by decide

def batch_132_02_values : List Bool := [accepted_6603]
theorem batch_132_02_ok : batch_132_02_values.all id = true := by decide

def batch_132_03_values : List Bool := [accepted_6604]
theorem batch_132_03_ok : batch_132_03_values.all id = true := by decide

def batch_132_04_values : List Bool := [accepted_6609]
theorem batch_132_04_ok : batch_132_04_values.all id = true := by decide

def batch_132_05_values : List Bool := [accepted_6611]
theorem batch_132_05_ok : batch_132_05_values.all id = true := by decide

def batch_132_06_values : List Bool := [accepted_6613]
theorem batch_132_06_ok : batch_132_06_values.all id = true := by decide

def batch_132_07_values : List Bool := [accepted_6614]
theorem batch_132_07_ok : batch_132_07_values.all id = true := by decide

def batch_132_08_values : List Bool := [accepted_6619]
theorem batch_132_08_ok : batch_132_08_values.all id = true := by decide

def batch_132_09_values : List Bool := [accepted_6620]
theorem batch_132_09_ok : batch_132_09_values.all id = true := by decide

def batch_132_10_values : List Bool := [accepted_6621]
theorem batch_132_10_ok : batch_132_10_values.all id = true := by decide

def batch_132_11_values : List Bool := [accepted_6622]
theorem batch_132_11_ok : batch_132_11_values.all id = true := by decide

def batch_132_12_values : List Bool := [accepted_6625]
theorem batch_132_12_ok : batch_132_12_values.all id = true := by decide

def batch_132_13_values : List Bool := [accepted_6626]
theorem batch_132_13_ok : batch_132_13_values.all id = true := by decide

def batch_132_14_values : List Bool := [accepted_6627]
theorem batch_132_14_ok : batch_132_14_values.all id = true := by decide

def batch_132_15_values : List Bool := [accepted_6628]
theorem batch_132_15_ok : batch_132_15_values.all id = true := by decide

def batch_132_16_values : List Bool := [accepted_6633]
theorem batch_132_16_ok : batch_132_16_values.all id = true := by decide

def batch_132_17_values : List Bool := [accepted_6635]
theorem batch_132_17_ok : batch_132_17_values.all id = true := by decide

def batch_132_18_values : List Bool := [accepted_6636]
theorem batch_132_18_ok : batch_132_18_values.all id = true := by decide

def batch_132_19_values : List Bool := [accepted_6639]
theorem batch_132_19_ok : batch_132_19_values.all id = true := by decide

def batch_132_20_values : List Bool := [accepted_6640]
theorem batch_132_20_ok : batch_132_20_values.all id = true := by decide

def batch_132_21_values : List Bool := [accepted_6643]
theorem batch_132_21_ok : batch_132_21_values.all id = true := by decide

def batch_132_22_values : List Bool := [accepted_6644]
theorem batch_132_22_ok : batch_132_22_values.all id = true := by decide

def batch_132_23_values : List Bool := [accepted_6649]
theorem batch_132_23_ok : batch_132_23_values.all id = true := by decide

theorem leaf_6601_ok : checkAt 527 1000 box_6601 cert_6601 = true := by
  have h := List.all_eq_true.mp batch_132_00_ok accepted_6601 (by simp [batch_132_00_values])
  exact h
theorem leaf_6601_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6601.profileLo box_6601.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6601_ok
theorem branch_box_6601_nonnegative : ∀ j, 0 ≤ branch_box_6601.lower j ∧ 0 ≤ branch_box_6601.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6601, Box.profileLo, Box.profileHi, box_6601]
theorem leaf_6601_BranchSafe : CertificateConsequences.BranchSafe branch_box_6601 := by
  left; refine ⟨branch_box_6601_nonnegative, ?_⟩
  intro z hz; exact leaf_6601_sound hz

theorem leaf_6602_ok : checkAt 527 1000 box_6602 cert_6602 = true := by
  have h := List.all_eq_true.mp batch_132_01_ok accepted_6602 (by simp [batch_132_01_values])
  exact h
theorem leaf_6602_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6602.profileLo box_6602.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6602_ok
theorem branch_box_6602_nonnegative : ∀ j, 0 ≤ branch_box_6602.lower j ∧ 0 ≤ branch_box_6602.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6602, Box.profileLo, Box.profileHi, box_6602]
theorem leaf_6602_BranchSafe : CertificateConsequences.BranchSafe branch_box_6602 := by
  left; refine ⟨branch_box_6602_nonnegative, ?_⟩
  intro z hz; exact leaf_6602_sound hz

theorem leaf_6603_ok : checkAt 527 1000 box_6603 cert_6603 = true := by
  have h := List.all_eq_true.mp batch_132_02_ok accepted_6603 (by simp [batch_132_02_values])
  exact h
theorem leaf_6603_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6603.profileLo box_6603.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6603_ok
theorem branch_box_6603_nonnegative : ∀ j, 0 ≤ branch_box_6603.lower j ∧ 0 ≤ branch_box_6603.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6603, Box.profileLo, Box.profileHi, box_6603]
theorem leaf_6603_BranchSafe : CertificateConsequences.BranchSafe branch_box_6603 := by
  left; refine ⟨branch_box_6603_nonnegative, ?_⟩
  intro z hz; exact leaf_6603_sound hz

theorem leaf_6604_ok : checkAt 527 1000 box_6604 cert_6604 = true := by
  have h := List.all_eq_true.mp batch_132_03_ok accepted_6604 (by simp [batch_132_03_values])
  exact h
theorem leaf_6604_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6604.profileLo box_6604.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6604_ok
theorem branch_box_6604_nonnegative : ∀ j, 0 ≤ branch_box_6604.lower j ∧ 0 ≤ branch_box_6604.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6604, Box.profileLo, Box.profileHi, box_6604]
theorem leaf_6604_BranchSafe : CertificateConsequences.BranchSafe branch_box_6604 := by
  left; refine ⟨branch_box_6604_nonnegative, ?_⟩
  intro z hz; exact leaf_6604_sound hz

theorem leaf_6609_ok : checkAt 527 1000 box_6609 cert_6609 = true := by
  have h := List.all_eq_true.mp batch_132_04_ok accepted_6609 (by simp [batch_132_04_values])
  exact h
theorem leaf_6609_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6609.profileLo box_6609.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6609_ok
theorem branch_box_6609_nonnegative : ∀ j, 0 ≤ branch_box_6609.lower j ∧ 0 ≤ branch_box_6609.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6609, Box.profileLo, Box.profileHi, box_6609]
theorem leaf_6609_BranchSafe : CertificateConsequences.BranchSafe branch_box_6609 := by
  left; refine ⟨branch_box_6609_nonnegative, ?_⟩
  intro z hz; exact leaf_6609_sound hz

theorem leaf_6611_ok : checkAt 527 1000 box_6611 cert_6611 = true := by
  have h := List.all_eq_true.mp batch_132_05_ok accepted_6611 (by simp [batch_132_05_values])
  exact h
theorem leaf_6611_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6611.profileLo box_6611.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6611_ok
theorem branch_box_6611_nonnegative : ∀ j, 0 ≤ branch_box_6611.lower j ∧ 0 ≤ branch_box_6611.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6611, Box.profileLo, Box.profileHi, box_6611]
theorem leaf_6611_BranchSafe : CertificateConsequences.BranchSafe branch_box_6611 := by
  left; refine ⟨branch_box_6611_nonnegative, ?_⟩
  intro z hz; exact leaf_6611_sound hz

theorem leaf_6613_ok : checkAt 527 1000 box_6613 cert_6613 = true := by
  have h := List.all_eq_true.mp batch_132_06_ok accepted_6613 (by simp [batch_132_06_values])
  exact h
theorem leaf_6613_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6613.profileLo box_6613.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6613_ok
theorem branch_box_6613_nonnegative : ∀ j, 0 ≤ branch_box_6613.lower j ∧ 0 ≤ branch_box_6613.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6613, Box.profileLo, Box.profileHi, box_6613]
theorem leaf_6613_BranchSafe : CertificateConsequences.BranchSafe branch_box_6613 := by
  left; refine ⟨branch_box_6613_nonnegative, ?_⟩
  intro z hz; exact leaf_6613_sound hz

theorem leaf_6614_ok : checkAt 527 1000 box_6614 cert_6614 = true := by
  have h := List.all_eq_true.mp batch_132_07_ok accepted_6614 (by simp [batch_132_07_values])
  exact h
theorem leaf_6614_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6614.profileLo box_6614.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6614_ok
theorem branch_box_6614_nonnegative : ∀ j, 0 ≤ branch_box_6614.lower j ∧ 0 ≤ branch_box_6614.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6614, Box.profileLo, Box.profileHi, box_6614]
theorem leaf_6614_BranchSafe : CertificateConsequences.BranchSafe branch_box_6614 := by
  left; refine ⟨branch_box_6614_nonnegative, ?_⟩
  intro z hz; exact leaf_6614_sound hz

theorem leaf_6619_ok : checkAt 527 1000 box_6619 cert_6619 = true := by
  have h := List.all_eq_true.mp batch_132_08_ok accepted_6619 (by simp [batch_132_08_values])
  exact h
theorem leaf_6619_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6619.profileLo box_6619.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6619_ok
theorem branch_box_6619_nonnegative : ∀ j, 0 ≤ branch_box_6619.lower j ∧ 0 ≤ branch_box_6619.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6619, Box.profileLo, Box.profileHi, box_6619]
theorem leaf_6619_BranchSafe : CertificateConsequences.BranchSafe branch_box_6619 := by
  left; refine ⟨branch_box_6619_nonnegative, ?_⟩
  intro z hz; exact leaf_6619_sound hz

theorem leaf_6620_ok : checkAt 527 1000 box_6620 cert_6620 = true := by
  have h := List.all_eq_true.mp batch_132_09_ok accepted_6620 (by simp [batch_132_09_values])
  exact h
theorem leaf_6620_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6620.profileLo box_6620.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6620_ok
theorem branch_box_6620_nonnegative : ∀ j, 0 ≤ branch_box_6620.lower j ∧ 0 ≤ branch_box_6620.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6620, Box.profileLo, Box.profileHi, box_6620]
theorem leaf_6620_BranchSafe : CertificateConsequences.BranchSafe branch_box_6620 := by
  left; refine ⟨branch_box_6620_nonnegative, ?_⟩
  intro z hz; exact leaf_6620_sound hz

theorem leaf_6621_ok : checkAt 527 1000 box_6621 cert_6621 = true := by
  have h := List.all_eq_true.mp batch_132_10_ok accepted_6621 (by simp [batch_132_10_values])
  exact h
theorem leaf_6621_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6621.profileLo box_6621.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6621_ok
theorem branch_box_6621_nonnegative : ∀ j, 0 ≤ branch_box_6621.lower j ∧ 0 ≤ branch_box_6621.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6621, Box.profileLo, Box.profileHi, box_6621]
theorem leaf_6621_BranchSafe : CertificateConsequences.BranchSafe branch_box_6621 := by
  left; refine ⟨branch_box_6621_nonnegative, ?_⟩
  intro z hz; exact leaf_6621_sound hz

theorem leaf_6622_ok : checkAt 527 1000 box_6622 cert_6622 = true := by
  have h := List.all_eq_true.mp batch_132_11_ok accepted_6622 (by simp [batch_132_11_values])
  exact h
theorem leaf_6622_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6622.profileLo box_6622.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6622_ok
theorem branch_box_6622_nonnegative : ∀ j, 0 ≤ branch_box_6622.lower j ∧ 0 ≤ branch_box_6622.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6622, Box.profileLo, Box.profileHi, box_6622]
theorem leaf_6622_BranchSafe : CertificateConsequences.BranchSafe branch_box_6622 := by
  left; refine ⟨branch_box_6622_nonnegative, ?_⟩
  intro z hz; exact leaf_6622_sound hz

theorem leaf_6625_ok : checkAt 527 1000 box_6625 cert_6625 = true := by
  have h := List.all_eq_true.mp batch_132_12_ok accepted_6625 (by simp [batch_132_12_values])
  exact h
theorem leaf_6625_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6625.profileLo box_6625.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6625_ok
theorem branch_box_6625_nonnegative : ∀ j, 0 ≤ branch_box_6625.lower j ∧ 0 ≤ branch_box_6625.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6625, Box.profileLo, Box.profileHi, box_6625]
theorem leaf_6625_BranchSafe : CertificateConsequences.BranchSafe branch_box_6625 := by
  left; refine ⟨branch_box_6625_nonnegative, ?_⟩
  intro z hz; exact leaf_6625_sound hz

theorem leaf_6626_ok : checkAt 527 1000 box_6626 cert_6626 = true := by
  have h := List.all_eq_true.mp batch_132_13_ok accepted_6626 (by simp [batch_132_13_values])
  exact h
theorem leaf_6626_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6626.profileLo box_6626.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6626_ok
theorem branch_box_6626_nonnegative : ∀ j, 0 ≤ branch_box_6626.lower j ∧ 0 ≤ branch_box_6626.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6626, Box.profileLo, Box.profileHi, box_6626]
theorem leaf_6626_BranchSafe : CertificateConsequences.BranchSafe branch_box_6626 := by
  left; refine ⟨branch_box_6626_nonnegative, ?_⟩
  intro z hz; exact leaf_6626_sound hz

theorem leaf_6627_ok : checkAt 527 1000 box_6627 cert_6627 = true := by
  have h := List.all_eq_true.mp batch_132_14_ok accepted_6627 (by simp [batch_132_14_values])
  exact h
theorem leaf_6627_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6627.profileLo box_6627.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6627_ok
theorem branch_box_6627_nonnegative : ∀ j, 0 ≤ branch_box_6627.lower j ∧ 0 ≤ branch_box_6627.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6627, Box.profileLo, Box.profileHi, box_6627]
theorem leaf_6627_BranchSafe : CertificateConsequences.BranchSafe branch_box_6627 := by
  left; refine ⟨branch_box_6627_nonnegative, ?_⟩
  intro z hz; exact leaf_6627_sound hz

theorem leaf_6628_ok : checkAt 527 1000 box_6628 cert_6628 = true := by
  have h := List.all_eq_true.mp batch_132_15_ok accepted_6628 (by simp [batch_132_15_values])
  exact h
theorem leaf_6628_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6628.profileLo box_6628.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6628_ok
theorem branch_box_6628_nonnegative : ∀ j, 0 ≤ branch_box_6628.lower j ∧ 0 ≤ branch_box_6628.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6628, Box.profileLo, Box.profileHi, box_6628]
theorem leaf_6628_BranchSafe : CertificateConsequences.BranchSafe branch_box_6628 := by
  left; refine ⟨branch_box_6628_nonnegative, ?_⟩
  intro z hz; exact leaf_6628_sound hz

theorem leaf_6633_ok : checkAt 527 1000 box_6633 cert_6633 = true := by
  have h := List.all_eq_true.mp batch_132_16_ok accepted_6633 (by simp [batch_132_16_values])
  exact h
theorem leaf_6633_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6633.profileLo box_6633.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6633_ok
theorem branch_box_6633_nonnegative : ∀ j, 0 ≤ branch_box_6633.lower j ∧ 0 ≤ branch_box_6633.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6633, Box.profileLo, Box.profileHi, box_6633]
theorem leaf_6633_BranchSafe : CertificateConsequences.BranchSafe branch_box_6633 := by
  left; refine ⟨branch_box_6633_nonnegative, ?_⟩
  intro z hz; exact leaf_6633_sound hz

theorem leaf_6635_ok : checkAt 527 1000 box_6635 cert_6635 = true := by
  have h := List.all_eq_true.mp batch_132_17_ok accepted_6635 (by simp [batch_132_17_values])
  exact h
theorem leaf_6635_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6635.profileLo box_6635.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6635_ok
theorem branch_box_6635_nonnegative : ∀ j, 0 ≤ branch_box_6635.lower j ∧ 0 ≤ branch_box_6635.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6635, Box.profileLo, Box.profileHi, box_6635]
theorem leaf_6635_BranchSafe : CertificateConsequences.BranchSafe branch_box_6635 := by
  left; refine ⟨branch_box_6635_nonnegative, ?_⟩
  intro z hz; exact leaf_6635_sound hz

theorem leaf_6636_ok : checkAt 527 1000 box_6636 cert_6636 = true := by
  have h := List.all_eq_true.mp batch_132_18_ok accepted_6636 (by simp [batch_132_18_values])
  exact h
theorem leaf_6636_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6636.profileLo box_6636.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6636_ok
theorem branch_box_6636_nonnegative : ∀ j, 0 ≤ branch_box_6636.lower j ∧ 0 ≤ branch_box_6636.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6636, Box.profileLo, Box.profileHi, box_6636]
theorem leaf_6636_BranchSafe : CertificateConsequences.BranchSafe branch_box_6636 := by
  left; refine ⟨branch_box_6636_nonnegative, ?_⟩
  intro z hz; exact leaf_6636_sound hz

theorem leaf_6639_ok : checkAt 527 1000 box_6639 cert_6639 = true := by
  have h := List.all_eq_true.mp batch_132_19_ok accepted_6639 (by simp [batch_132_19_values])
  exact h
theorem leaf_6639_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6639.profileLo box_6639.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6639_ok
theorem branch_box_6639_nonnegative : ∀ j, 0 ≤ branch_box_6639.lower j ∧ 0 ≤ branch_box_6639.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6639, Box.profileLo, Box.profileHi, box_6639]
theorem leaf_6639_BranchSafe : CertificateConsequences.BranchSafe branch_box_6639 := by
  left; refine ⟨branch_box_6639_nonnegative, ?_⟩
  intro z hz; exact leaf_6639_sound hz

theorem leaf_6640_ok : checkAt 527 1000 box_6640 cert_6640 = true := by
  have h := List.all_eq_true.mp batch_132_20_ok accepted_6640 (by simp [batch_132_20_values])
  exact h
theorem leaf_6640_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6640.profileLo box_6640.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6640_ok
theorem branch_box_6640_nonnegative : ∀ j, 0 ≤ branch_box_6640.lower j ∧ 0 ≤ branch_box_6640.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6640, Box.profileLo, Box.profileHi, box_6640]
theorem leaf_6640_BranchSafe : CertificateConsequences.BranchSafe branch_box_6640 := by
  left; refine ⟨branch_box_6640_nonnegative, ?_⟩
  intro z hz; exact leaf_6640_sound hz

theorem leaf_6643_ok : checkAt 527 1000 box_6643 cert_6643 = true := by
  have h := List.all_eq_true.mp batch_132_21_ok accepted_6643 (by simp [batch_132_21_values])
  exact h
theorem leaf_6643_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6643.profileLo box_6643.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6643_ok
theorem branch_box_6643_nonnegative : ∀ j, 0 ≤ branch_box_6643.lower j ∧ 0 ≤ branch_box_6643.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6643, Box.profileLo, Box.profileHi, box_6643]
theorem leaf_6643_BranchSafe : CertificateConsequences.BranchSafe branch_box_6643 := by
  left; refine ⟨branch_box_6643_nonnegative, ?_⟩
  intro z hz; exact leaf_6643_sound hz

theorem leaf_6644_ok : checkAt 527 1000 box_6644 cert_6644 = true := by
  have h := List.all_eq_true.mp batch_132_22_ok accepted_6644 (by simp [batch_132_22_values])
  exact h
theorem leaf_6644_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6644.profileLo box_6644.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6644_ok
theorem branch_box_6644_nonnegative : ∀ j, 0 ≤ branch_box_6644.lower j ∧ 0 ≤ branch_box_6644.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6644, Box.profileLo, Box.profileHi, box_6644]
theorem leaf_6644_BranchSafe : CertificateConsequences.BranchSafe branch_box_6644 := by
  left; refine ⟨branch_box_6644_nonnegative, ?_⟩
  intro z hz; exact leaf_6644_sound hz

theorem leaf_6649_ok : checkAt 527 1000 box_6649 cert_6649 = true := by
  have h := List.all_eq_true.mp batch_132_23_ok accepted_6649 (by simp [batch_132_23_values])
  exact h
theorem leaf_6649_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6649.profileLo box_6649.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6649_ok
theorem branch_box_6649_nonnegative : ∀ j, 0 ≤ branch_box_6649.lower j ∧ 0 ≤ branch_box_6649.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6649, Box.profileLo, Box.profileHi, box_6649]
theorem leaf_6649_BranchSafe : CertificateConsequences.BranchSafe branch_box_6649 := by
  left; refine ⟨branch_box_6649_nonnegative, ?_⟩
  intro z hz; exact leaf_6649_sound hz

#print axioms batch_132_00_ok
#print axioms leaf_6601_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
