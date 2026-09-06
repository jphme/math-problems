import PeaceableQueens.UpperBound.Generated.Even.C527Scaled112Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_112_00_values : List Bool := [accepted_5600]
theorem batch_112_00_ok : batch_112_00_values.all id = true := by decide

def batch_112_01_values : List Bool := [accepted_5602]
theorem batch_112_01_ok : batch_112_01_values.all id = true := by decide

def batch_112_02_values : List Bool := [accepted_5603]
theorem batch_112_02_ok : batch_112_02_values.all id = true := by decide

def batch_112_03_values : List Bool := [accepted_5604]
theorem batch_112_03_ok : batch_112_03_values.all id = true := by decide

def batch_112_04_values : List Bool := [accepted_5611]
theorem batch_112_04_ok : batch_112_04_values.all id = true := by decide

def batch_112_05_values : List Bool := [accepted_5612]
theorem batch_112_05_ok : batch_112_05_values.all id = true := by decide

def batch_112_06_values : List Bool := [accepted_5614]
theorem batch_112_06_ok : batch_112_06_values.all id = true := by decide

def batch_112_07_values : List Bool := [accepted_5615]
theorem batch_112_07_ok : batch_112_07_values.all id = true := by decide

def batch_112_08_values : List Bool := [accepted_5618]
theorem batch_112_08_ok : batch_112_08_values.all id = true := by decide

def batch_112_09_values : List Bool := [accepted_5620]
theorem batch_112_09_ok : batch_112_09_values.all id = true := by decide

def batch_112_10_values : List Bool := [accepted_5621]
theorem batch_112_10_ok : batch_112_10_values.all id = true := by decide

def batch_112_11_values : List Bool := [accepted_5622]
theorem batch_112_11_ok : batch_112_11_values.all id = true := by decide

def batch_112_12_values : List Bool := [accepted_5625]
theorem batch_112_12_ok : batch_112_12_values.all id = true := by decide

def batch_112_13_values : List Bool := [accepted_5627]
theorem batch_112_13_ok : batch_112_13_values.all id = true := by decide

def batch_112_14_values : List Bool := [accepted_5628]
theorem batch_112_14_ok : batch_112_14_values.all id = true := by decide

def batch_112_15_values : List Bool := [accepted_5629]
theorem batch_112_15_ok : batch_112_15_values.all id = true := by decide

def batch_112_16_values : List Bool := [accepted_5631]
theorem batch_112_16_ok : batch_112_16_values.all id = true := by decide

def batch_112_17_values : List Bool := [accepted_5633]
theorem batch_112_17_ok : batch_112_17_values.all id = true := by decide

def batch_112_18_values : List Bool := [accepted_5634]
theorem batch_112_18_ok : batch_112_18_values.all id = true := by decide

def batch_112_19_values : List Bool := [accepted_5639]
theorem batch_112_19_ok : batch_112_19_values.all id = true := by decide

def batch_112_20_values : List Bool := [accepted_5640]
theorem batch_112_20_ok : batch_112_20_values.all id = true := by decide

def batch_112_21_values : List Bool := [accepted_5643]
theorem batch_112_21_ok : batch_112_21_values.all id = true := by decide

def batch_112_22_values : List Bool := [accepted_5644]
theorem batch_112_22_ok : batch_112_22_values.all id = true := by decide

def batch_112_23_values : List Bool := [accepted_5647]
theorem batch_112_23_ok : batch_112_23_values.all id = true := by decide

def batch_112_24_values : List Bool := [accepted_5648]
theorem batch_112_24_ok : batch_112_24_values.all id = true := by decide

def batch_112_25_values : List Bool := [accepted_5649]
theorem batch_112_25_ok : batch_112_25_values.all id = true := by decide

theorem leaf_5600_ok : checkAt 527 1000 box_5600 cert_5600 = true := by
  have h := List.all_eq_true.mp batch_112_00_ok accepted_5600 (by simp [batch_112_00_values])
  exact h
theorem leaf_5600_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5600.profileLo box_5600.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5600_ok
theorem branch_box_5600_nonnegative : ∀ j, 0 ≤ branch_box_5600.lower j ∧ 0 ≤ branch_box_5600.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5600, Box.profileLo, Box.profileHi, box_5600]
theorem leaf_5600_BranchSafe : CertificateConsequences.BranchSafe branch_box_5600 := by
  left; refine ⟨branch_box_5600_nonnegative, ?_⟩
  intro z hz; exact leaf_5600_sound hz

theorem leaf_5602_ok : checkAt 527 1000 box_5602 cert_5602 = true := by
  have h := List.all_eq_true.mp batch_112_01_ok accepted_5602 (by simp [batch_112_01_values])
  exact h
theorem leaf_5602_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5602.profileLo box_5602.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5602_ok
theorem branch_box_5602_nonnegative : ∀ j, 0 ≤ branch_box_5602.lower j ∧ 0 ≤ branch_box_5602.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5602, Box.profileLo, Box.profileHi, box_5602]
theorem leaf_5602_BranchSafe : CertificateConsequences.BranchSafe branch_box_5602 := by
  left; refine ⟨branch_box_5602_nonnegative, ?_⟩
  intro z hz; exact leaf_5602_sound hz

theorem leaf_5603_ok : checkAt 527 1000 box_5603 cert_5603 = true := by
  have h := List.all_eq_true.mp batch_112_02_ok accepted_5603 (by simp [batch_112_02_values])
  exact h
theorem leaf_5603_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5603.profileLo box_5603.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5603_ok
theorem branch_box_5603_nonnegative : ∀ j, 0 ≤ branch_box_5603.lower j ∧ 0 ≤ branch_box_5603.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5603, Box.profileLo, Box.profileHi, box_5603]
theorem leaf_5603_BranchSafe : CertificateConsequences.BranchSafe branch_box_5603 := by
  left; refine ⟨branch_box_5603_nonnegative, ?_⟩
  intro z hz; exact leaf_5603_sound hz

theorem leaf_5604_ok : checkAt 527 1000 box_5604 cert_5604 = true := by
  have h := List.all_eq_true.mp batch_112_03_ok accepted_5604 (by simp [batch_112_03_values])
  exact h
theorem leaf_5604_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5604.profileLo box_5604.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5604_ok
theorem branch_box_5604_nonnegative : ∀ j, 0 ≤ branch_box_5604.lower j ∧ 0 ≤ branch_box_5604.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5604, Box.profileLo, Box.profileHi, box_5604]
theorem leaf_5604_BranchSafe : CertificateConsequences.BranchSafe branch_box_5604 := by
  left; refine ⟨branch_box_5604_nonnegative, ?_⟩
  intro z hz; exact leaf_5604_sound hz

theorem leaf_5611_ok : checkAt 527 1000 box_5611 cert_5611 = true := by
  have h := List.all_eq_true.mp batch_112_04_ok accepted_5611 (by simp [batch_112_04_values])
  exact h
theorem leaf_5611_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5611.profileLo box_5611.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5611_ok
theorem branch_box_5611_nonnegative : ∀ j, 0 ≤ branch_box_5611.lower j ∧ 0 ≤ branch_box_5611.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5611, Box.profileLo, Box.profileHi, box_5611]
theorem leaf_5611_BranchSafe : CertificateConsequences.BranchSafe branch_box_5611 := by
  left; refine ⟨branch_box_5611_nonnegative, ?_⟩
  intro z hz; exact leaf_5611_sound hz

theorem leaf_5612_ok : checkAt 527 1000 box_5612 cert_5612 = true := by
  have h := List.all_eq_true.mp batch_112_05_ok accepted_5612 (by simp [batch_112_05_values])
  exact h
theorem leaf_5612_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5612.profileLo box_5612.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5612_ok
theorem branch_box_5612_nonnegative : ∀ j, 0 ≤ branch_box_5612.lower j ∧ 0 ≤ branch_box_5612.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5612, Box.profileLo, Box.profileHi, box_5612]
theorem leaf_5612_BranchSafe : CertificateConsequences.BranchSafe branch_box_5612 := by
  left; refine ⟨branch_box_5612_nonnegative, ?_⟩
  intro z hz; exact leaf_5612_sound hz

theorem leaf_5614_ok : checkAt 527 1000 box_5614 cert_5614 = true := by
  have h := List.all_eq_true.mp batch_112_06_ok accepted_5614 (by simp [batch_112_06_values])
  exact h
theorem leaf_5614_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5614.profileLo box_5614.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5614_ok
theorem branch_box_5614_nonnegative : ∀ j, 0 ≤ branch_box_5614.lower j ∧ 0 ≤ branch_box_5614.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5614, Box.profileLo, Box.profileHi, box_5614]
theorem leaf_5614_BranchSafe : CertificateConsequences.BranchSafe branch_box_5614 := by
  left; refine ⟨branch_box_5614_nonnegative, ?_⟩
  intro z hz; exact leaf_5614_sound hz

theorem leaf_5615_ok : checkAt 527 1000 box_5615 cert_5615 = true := by
  have h := List.all_eq_true.mp batch_112_07_ok accepted_5615 (by simp [batch_112_07_values])
  exact h
theorem leaf_5615_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5615.profileLo box_5615.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5615_ok
theorem branch_box_5615_nonnegative : ∀ j, 0 ≤ branch_box_5615.lower j ∧ 0 ≤ branch_box_5615.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5615, Box.profileLo, Box.profileHi, box_5615]
theorem leaf_5615_BranchSafe : CertificateConsequences.BranchSafe branch_box_5615 := by
  left; refine ⟨branch_box_5615_nonnegative, ?_⟩
  intro z hz; exact leaf_5615_sound hz

theorem leaf_5618_ok : checkAt 527 1000 box_5618 cert_5618 = true := by
  have h := List.all_eq_true.mp batch_112_08_ok accepted_5618 (by simp [batch_112_08_values])
  exact h
theorem leaf_5618_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5618.profileLo box_5618.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5618_ok
theorem branch_box_5618_nonnegative : ∀ j, 0 ≤ branch_box_5618.lower j ∧ 0 ≤ branch_box_5618.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5618, Box.profileLo, Box.profileHi, box_5618]
theorem leaf_5618_BranchSafe : CertificateConsequences.BranchSafe branch_box_5618 := by
  left; refine ⟨branch_box_5618_nonnegative, ?_⟩
  intro z hz; exact leaf_5618_sound hz

theorem leaf_5620_ok : checkAt 527 1000 box_5620 cert_5620 = true := by
  have h := List.all_eq_true.mp batch_112_09_ok accepted_5620 (by simp [batch_112_09_values])
  exact h
theorem leaf_5620_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5620.profileLo box_5620.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5620_ok
theorem branch_box_5620_nonnegative : ∀ j, 0 ≤ branch_box_5620.lower j ∧ 0 ≤ branch_box_5620.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5620, Box.profileLo, Box.profileHi, box_5620]
theorem leaf_5620_BranchSafe : CertificateConsequences.BranchSafe branch_box_5620 := by
  left; refine ⟨branch_box_5620_nonnegative, ?_⟩
  intro z hz; exact leaf_5620_sound hz

theorem leaf_5621_ok : checkAt 527 1000 box_5621 cert_5621 = true := by
  have h := List.all_eq_true.mp batch_112_10_ok accepted_5621 (by simp [batch_112_10_values])
  exact h
theorem leaf_5621_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5621.profileLo box_5621.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5621_ok
theorem branch_box_5621_nonnegative : ∀ j, 0 ≤ branch_box_5621.lower j ∧ 0 ≤ branch_box_5621.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5621, Box.profileLo, Box.profileHi, box_5621]
theorem leaf_5621_BranchSafe : CertificateConsequences.BranchSafe branch_box_5621 := by
  left; refine ⟨branch_box_5621_nonnegative, ?_⟩
  intro z hz; exact leaf_5621_sound hz

theorem leaf_5622_ok : checkAt 527 1000 box_5622 cert_5622 = true := by
  have h := List.all_eq_true.mp batch_112_11_ok accepted_5622 (by simp [batch_112_11_values])
  exact h
theorem leaf_5622_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5622.profileLo box_5622.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5622_ok
theorem branch_box_5622_nonnegative : ∀ j, 0 ≤ branch_box_5622.lower j ∧ 0 ≤ branch_box_5622.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5622, Box.profileLo, Box.profileHi, box_5622]
theorem leaf_5622_BranchSafe : CertificateConsequences.BranchSafe branch_box_5622 := by
  left; refine ⟨branch_box_5622_nonnegative, ?_⟩
  intro z hz; exact leaf_5622_sound hz

theorem leaf_5625_ok : checkAt 527 1000 box_5625 cert_5625 = true := by
  have h := List.all_eq_true.mp batch_112_12_ok accepted_5625 (by simp [batch_112_12_values])
  exact h
theorem leaf_5625_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5625.profileLo box_5625.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5625_ok
theorem branch_box_5625_nonnegative : ∀ j, 0 ≤ branch_box_5625.lower j ∧ 0 ≤ branch_box_5625.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5625, Box.profileLo, Box.profileHi, box_5625]
theorem leaf_5625_BranchSafe : CertificateConsequences.BranchSafe branch_box_5625 := by
  left; refine ⟨branch_box_5625_nonnegative, ?_⟩
  intro z hz; exact leaf_5625_sound hz

theorem leaf_5627_ok : checkAt 527 1000 box_5627 cert_5627 = true := by
  have h := List.all_eq_true.mp batch_112_13_ok accepted_5627 (by simp [batch_112_13_values])
  exact h
theorem leaf_5627_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5627.profileLo box_5627.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5627_ok
theorem branch_box_5627_nonnegative : ∀ j, 0 ≤ branch_box_5627.lower j ∧ 0 ≤ branch_box_5627.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5627, Box.profileLo, Box.profileHi, box_5627]
theorem leaf_5627_BranchSafe : CertificateConsequences.BranchSafe branch_box_5627 := by
  left; refine ⟨branch_box_5627_nonnegative, ?_⟩
  intro z hz; exact leaf_5627_sound hz

theorem leaf_5628_ok : checkAt 527 1000 box_5628 cert_5628 = true := by
  have h := List.all_eq_true.mp batch_112_14_ok accepted_5628 (by simp [batch_112_14_values])
  exact h
theorem leaf_5628_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5628.profileLo box_5628.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5628_ok
theorem branch_box_5628_nonnegative : ∀ j, 0 ≤ branch_box_5628.lower j ∧ 0 ≤ branch_box_5628.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5628, Box.profileLo, Box.profileHi, box_5628]
theorem leaf_5628_BranchSafe : CertificateConsequences.BranchSafe branch_box_5628 := by
  left; refine ⟨branch_box_5628_nonnegative, ?_⟩
  intro z hz; exact leaf_5628_sound hz

theorem leaf_5629_ok : checkAt 527 1000 box_5629 cert_5629 = true := by
  have h := List.all_eq_true.mp batch_112_15_ok accepted_5629 (by simp [batch_112_15_values])
  exact h
theorem leaf_5629_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5629.profileLo box_5629.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5629_ok
theorem branch_box_5629_nonnegative : ∀ j, 0 ≤ branch_box_5629.lower j ∧ 0 ≤ branch_box_5629.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5629, Box.profileLo, Box.profileHi, box_5629]
theorem leaf_5629_BranchSafe : CertificateConsequences.BranchSafe branch_box_5629 := by
  left; refine ⟨branch_box_5629_nonnegative, ?_⟩
  intro z hz; exact leaf_5629_sound hz

theorem leaf_5631_ok : checkAt 527 1000 box_5631 cert_5631 = true := by
  have h := List.all_eq_true.mp batch_112_16_ok accepted_5631 (by simp [batch_112_16_values])
  exact h
theorem leaf_5631_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5631.profileLo box_5631.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5631_ok
theorem branch_box_5631_nonnegative : ∀ j, 0 ≤ branch_box_5631.lower j ∧ 0 ≤ branch_box_5631.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5631, Box.profileLo, Box.profileHi, box_5631]
theorem leaf_5631_BranchSafe : CertificateConsequences.BranchSafe branch_box_5631 := by
  left; refine ⟨branch_box_5631_nonnegative, ?_⟩
  intro z hz; exact leaf_5631_sound hz

theorem leaf_5633_ok : checkAt 527 1000 box_5633 cert_5633 = true := by
  have h := List.all_eq_true.mp batch_112_17_ok accepted_5633 (by simp [batch_112_17_values])
  exact h
theorem leaf_5633_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5633.profileLo box_5633.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5633_ok
theorem branch_box_5633_nonnegative : ∀ j, 0 ≤ branch_box_5633.lower j ∧ 0 ≤ branch_box_5633.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5633, Box.profileLo, Box.profileHi, box_5633]
theorem leaf_5633_BranchSafe : CertificateConsequences.BranchSafe branch_box_5633 := by
  left; refine ⟨branch_box_5633_nonnegative, ?_⟩
  intro z hz; exact leaf_5633_sound hz

theorem leaf_5634_ok : checkAt 527 1000 box_5634 cert_5634 = true := by
  have h := List.all_eq_true.mp batch_112_18_ok accepted_5634 (by simp [batch_112_18_values])
  exact h
theorem leaf_5634_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5634.profileLo box_5634.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5634_ok
theorem branch_box_5634_nonnegative : ∀ j, 0 ≤ branch_box_5634.lower j ∧ 0 ≤ branch_box_5634.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5634, Box.profileLo, Box.profileHi, box_5634]
theorem leaf_5634_BranchSafe : CertificateConsequences.BranchSafe branch_box_5634 := by
  left; refine ⟨branch_box_5634_nonnegative, ?_⟩
  intro z hz; exact leaf_5634_sound hz

theorem leaf_5639_ok : checkAt 527 1000 box_5639 cert_5639 = true := by
  have h := List.all_eq_true.mp batch_112_19_ok accepted_5639 (by simp [batch_112_19_values])
  exact h
theorem leaf_5639_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5639.profileLo box_5639.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5639_ok
theorem branch_box_5639_nonnegative : ∀ j, 0 ≤ branch_box_5639.lower j ∧ 0 ≤ branch_box_5639.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5639, Box.profileLo, Box.profileHi, box_5639]
theorem leaf_5639_BranchSafe : CertificateConsequences.BranchSafe branch_box_5639 := by
  left; refine ⟨branch_box_5639_nonnegative, ?_⟩
  intro z hz; exact leaf_5639_sound hz

theorem leaf_5640_ok : checkAt 527 1000 box_5640 cert_5640 = true := by
  have h := List.all_eq_true.mp batch_112_20_ok accepted_5640 (by simp [batch_112_20_values])
  exact h
theorem leaf_5640_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5640.profileLo box_5640.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5640_ok
theorem branch_box_5640_nonnegative : ∀ j, 0 ≤ branch_box_5640.lower j ∧ 0 ≤ branch_box_5640.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5640, Box.profileLo, Box.profileHi, box_5640]
theorem leaf_5640_BranchSafe : CertificateConsequences.BranchSafe branch_box_5640 := by
  left; refine ⟨branch_box_5640_nonnegative, ?_⟩
  intro z hz; exact leaf_5640_sound hz

theorem leaf_5643_ok : checkAt 527 1000 box_5643 cert_5643 = true := by
  have h := List.all_eq_true.mp batch_112_21_ok accepted_5643 (by simp [batch_112_21_values])
  exact h
theorem leaf_5643_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5643.profileLo box_5643.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5643_ok
theorem branch_box_5643_nonnegative : ∀ j, 0 ≤ branch_box_5643.lower j ∧ 0 ≤ branch_box_5643.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5643, Box.profileLo, Box.profileHi, box_5643]
theorem leaf_5643_BranchSafe : CertificateConsequences.BranchSafe branch_box_5643 := by
  left; refine ⟨branch_box_5643_nonnegative, ?_⟩
  intro z hz; exact leaf_5643_sound hz

theorem leaf_5644_ok : checkAt 527 1000 box_5644 cert_5644 = true := by
  have h := List.all_eq_true.mp batch_112_22_ok accepted_5644 (by simp [batch_112_22_values])
  exact h
theorem leaf_5644_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5644.profileLo box_5644.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5644_ok
theorem branch_box_5644_nonnegative : ∀ j, 0 ≤ branch_box_5644.lower j ∧ 0 ≤ branch_box_5644.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5644, Box.profileLo, Box.profileHi, box_5644]
theorem leaf_5644_BranchSafe : CertificateConsequences.BranchSafe branch_box_5644 := by
  left; refine ⟨branch_box_5644_nonnegative, ?_⟩
  intro z hz; exact leaf_5644_sound hz

theorem leaf_5647_ok : checkAt 527 1000 box_5647 cert_5647 = true := by
  have h := List.all_eq_true.mp batch_112_23_ok accepted_5647 (by simp [batch_112_23_values])
  exact h
theorem leaf_5647_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5647.profileLo box_5647.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5647_ok
theorem branch_box_5647_nonnegative : ∀ j, 0 ≤ branch_box_5647.lower j ∧ 0 ≤ branch_box_5647.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5647, Box.profileLo, Box.profileHi, box_5647]
theorem leaf_5647_BranchSafe : CertificateConsequences.BranchSafe branch_box_5647 := by
  left; refine ⟨branch_box_5647_nonnegative, ?_⟩
  intro z hz; exact leaf_5647_sound hz

theorem leaf_5648_ok : checkAt 527 1000 box_5648 cert_5648 = true := by
  have h := List.all_eq_true.mp batch_112_24_ok accepted_5648 (by simp [batch_112_24_values])
  exact h
theorem leaf_5648_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5648.profileLo box_5648.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5648_ok
theorem branch_box_5648_nonnegative : ∀ j, 0 ≤ branch_box_5648.lower j ∧ 0 ≤ branch_box_5648.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5648, Box.profileLo, Box.profileHi, box_5648]
theorem leaf_5648_BranchSafe : CertificateConsequences.BranchSafe branch_box_5648 := by
  left; refine ⟨branch_box_5648_nonnegative, ?_⟩
  intro z hz; exact leaf_5648_sound hz

theorem leaf_5649_ok : checkAt 527 1000 box_5649 cert_5649 = true := by
  have h := List.all_eq_true.mp batch_112_25_ok accepted_5649 (by simp [batch_112_25_values])
  exact h
theorem leaf_5649_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5649.profileLo box_5649.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5649_ok
theorem branch_box_5649_nonnegative : ∀ j, 0 ≤ branch_box_5649.lower j ∧ 0 ≤ branch_box_5649.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5649, Box.profileLo, Box.profileHi, box_5649]
theorem leaf_5649_BranchSafe : CertificateConsequences.BranchSafe branch_box_5649 := by
  left; refine ⟨branch_box_5649_nonnegative, ?_⟩
  intro z hz; exact leaf_5649_sound hz

#print axioms batch_112_00_ok
#print axioms leaf_5600_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
