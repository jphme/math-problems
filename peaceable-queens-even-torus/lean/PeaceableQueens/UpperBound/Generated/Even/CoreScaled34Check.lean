import PeaceableQueens.UpperBound.Generated.Even.CoreScaled34Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_34_00_values : List Bool := [accepted_1702]
theorem batch_34_00_ok : batch_34_00_values.all id = true := by decide

def batch_34_01_values : List Bool := [accepted_1704]
theorem batch_34_01_ok : batch_34_01_values.all id = true := by decide

def batch_34_02_values : List Bool := [accepted_1706]
theorem batch_34_02_ok : batch_34_02_values.all id = true := by decide

def batch_34_03_values : List Bool := [accepted_1708]
theorem batch_34_03_ok : batch_34_03_values.all id = true := by decide

def batch_34_04_values : List Bool := [accepted_1712]
theorem batch_34_04_ok : batch_34_04_values.all id = true := by decide

def batch_34_05_values : List Bool := [accepted_1715]
theorem batch_34_05_ok : batch_34_05_values.all id = true := by decide

def batch_34_06_values : List Bool := [accepted_1717]
theorem batch_34_06_ok : batch_34_06_values.all id = true := by decide

def batch_34_07_values : List Bool := [accepted_1721]
theorem batch_34_07_ok : batch_34_07_values.all id = true := by decide

def batch_34_08_values : List Bool := [accepted_1725]
theorem batch_34_08_ok : batch_34_08_values.all id = true := by decide

def batch_34_09_values : List Bool := [accepted_1727]
theorem batch_34_09_ok : batch_34_09_values.all id = true := by decide

def batch_34_10_values : List Bool := [accepted_1729]
theorem batch_34_10_ok : batch_34_10_values.all id = true := by decide

def batch_34_11_values : List Bool := [accepted_1733]
theorem batch_34_11_ok : batch_34_11_values.all id = true := by decide

def batch_34_12_values : List Bool := [accepted_1735]
theorem batch_34_12_ok : batch_34_12_values.all id = true := by decide

def batch_34_13_values : List Bool := [accepted_1737]
theorem batch_34_13_ok : batch_34_13_values.all id = true := by decide

def batch_34_14_values : List Bool := [accepted_1739]
theorem batch_34_14_ok : batch_34_14_values.all id = true := by decide

def batch_34_15_values : List Bool := [accepted_1741]
theorem batch_34_15_ok : batch_34_15_values.all id = true := by decide

def batch_34_16_values : List Bool := [accepted_1743]
theorem batch_34_16_ok : batch_34_16_values.all id = true := by decide

def batch_34_17_values : List Bool := [accepted_1746]
theorem batch_34_17_ok : batch_34_17_values.all id = true := by decide

theorem leaf_1702_ok : checkAt 527 1000 box_1702 cert_1702 = true := by
  have h := List.all_eq_true.mp batch_34_00_ok accepted_1702 (by simp [batch_34_00_values])
  exact h
theorem leaf_1702_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1702.profileLo box_1702.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1702_ok
theorem branch_box_1702_nonnegative : ∀ j, 0 ≤ branch_box_1702.lower j ∧ 0 ≤ branch_box_1702.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1702, Box.profileLo, Box.profileHi, box_1702]
theorem leaf_1702_BranchSafe : CertificateConsequences.BranchSafe branch_box_1702 := by
  left; refine ⟨branch_box_1702_nonnegative, ?_⟩
  intro z hz; exact leaf_1702_sound hz

theorem leaf_1704_ok : checkAt 527 1000 box_1704 cert_1704 = true := by
  have h := List.all_eq_true.mp batch_34_01_ok accepted_1704 (by simp [batch_34_01_values])
  exact h
theorem leaf_1704_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1704.profileLo box_1704.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1704_ok
theorem branch_box_1704_nonnegative : ∀ j, 0 ≤ branch_box_1704.lower j ∧ 0 ≤ branch_box_1704.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1704, Box.profileLo, Box.profileHi, box_1704]
theorem leaf_1704_BranchSafe : CertificateConsequences.BranchSafe branch_box_1704 := by
  left; refine ⟨branch_box_1704_nonnegative, ?_⟩
  intro z hz; exact leaf_1704_sound hz

theorem leaf_1706_ok : checkAt 527 1000 box_1706 cert_1706 = true := by
  have h := List.all_eq_true.mp batch_34_02_ok accepted_1706 (by simp [batch_34_02_values])
  exact h
theorem leaf_1706_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1706.profileLo box_1706.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1706_ok
theorem branch_box_1706_nonnegative : ∀ j, 0 ≤ branch_box_1706.lower j ∧ 0 ≤ branch_box_1706.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1706, Box.profileLo, Box.profileHi, box_1706]
theorem leaf_1706_BranchSafe : CertificateConsequences.BranchSafe branch_box_1706 := by
  left; refine ⟨branch_box_1706_nonnegative, ?_⟩
  intro z hz; exact leaf_1706_sound hz

theorem leaf_1708_ok : checkAt 527 1000 box_1708 cert_1708 = true := by
  have h := List.all_eq_true.mp batch_34_03_ok accepted_1708 (by simp [batch_34_03_values])
  exact h
theorem leaf_1708_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1708.profileLo box_1708.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1708_ok
theorem branch_box_1708_nonnegative : ∀ j, 0 ≤ branch_box_1708.lower j ∧ 0 ≤ branch_box_1708.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1708, Box.profileLo, Box.profileHi, box_1708]
theorem leaf_1708_BranchSafe : CertificateConsequences.BranchSafe branch_box_1708 := by
  left; refine ⟨branch_box_1708_nonnegative, ?_⟩
  intro z hz; exact leaf_1708_sound hz

theorem leaf_1712_ok : checkAt 527 1000 box_1712 cert_1712 = true := by
  have h := List.all_eq_true.mp batch_34_04_ok accepted_1712 (by simp [batch_34_04_values])
  exact h
theorem leaf_1712_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1712.profileLo box_1712.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1712_ok
theorem branch_box_1712_nonnegative : ∀ j, 0 ≤ branch_box_1712.lower j ∧ 0 ≤ branch_box_1712.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1712, Box.profileLo, Box.profileHi, box_1712]
theorem leaf_1712_BranchSafe : CertificateConsequences.BranchSafe branch_box_1712 := by
  left; refine ⟨branch_box_1712_nonnegative, ?_⟩
  intro z hz; exact leaf_1712_sound hz

theorem leaf_1715_ok : checkAt 527 1000 box_1715 cert_1715 = true := by
  have h := List.all_eq_true.mp batch_34_05_ok accepted_1715 (by simp [batch_34_05_values])
  exact h
theorem leaf_1715_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1715.profileLo box_1715.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1715_ok
theorem branch_box_1715_nonnegative : ∀ j, 0 ≤ branch_box_1715.lower j ∧ 0 ≤ branch_box_1715.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1715, Box.profileLo, Box.profileHi, box_1715]
theorem leaf_1715_BranchSafe : CertificateConsequences.BranchSafe branch_box_1715 := by
  left; refine ⟨branch_box_1715_nonnegative, ?_⟩
  intro z hz; exact leaf_1715_sound hz

theorem leaf_1717_ok : checkAt 527 1000 box_1717 cert_1717 = true := by
  have h := List.all_eq_true.mp batch_34_06_ok accepted_1717 (by simp [batch_34_06_values])
  exact h
theorem leaf_1717_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1717.profileLo box_1717.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1717_ok
theorem branch_box_1717_nonnegative : ∀ j, 0 ≤ branch_box_1717.lower j ∧ 0 ≤ branch_box_1717.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1717, Box.profileLo, Box.profileHi, box_1717]
theorem leaf_1717_BranchSafe : CertificateConsequences.BranchSafe branch_box_1717 := by
  left; refine ⟨branch_box_1717_nonnegative, ?_⟩
  intro z hz; exact leaf_1717_sound hz

theorem leaf_1721_ok : checkAt 527 1000 box_1721 cert_1721 = true := by
  have h := List.all_eq_true.mp batch_34_07_ok accepted_1721 (by simp [batch_34_07_values])
  exact h
theorem leaf_1721_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1721.profileLo box_1721.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1721_ok
theorem branch_box_1721_nonnegative : ∀ j, 0 ≤ branch_box_1721.lower j ∧ 0 ≤ branch_box_1721.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1721, Box.profileLo, Box.profileHi, box_1721]
theorem leaf_1721_BranchSafe : CertificateConsequences.BranchSafe branch_box_1721 := by
  left; refine ⟨branch_box_1721_nonnegative, ?_⟩
  intro z hz; exact leaf_1721_sound hz

theorem leaf_1725_ok : checkAt 527 1000 box_1725 cert_1725 = true := by
  have h := List.all_eq_true.mp batch_34_08_ok accepted_1725 (by simp [batch_34_08_values])
  exact h
theorem leaf_1725_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1725.profileLo box_1725.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1725_ok
theorem branch_box_1725_nonnegative : ∀ j, 0 ≤ branch_box_1725.lower j ∧ 0 ≤ branch_box_1725.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1725, Box.profileLo, Box.profileHi, box_1725]
theorem leaf_1725_BranchSafe : CertificateConsequences.BranchSafe branch_box_1725 := by
  left; refine ⟨branch_box_1725_nonnegative, ?_⟩
  intro z hz; exact leaf_1725_sound hz

theorem leaf_1727_ok : checkAt 527 1000 box_1727 cert_1727 = true := by
  have h := List.all_eq_true.mp batch_34_09_ok accepted_1727 (by simp [batch_34_09_values])
  exact h
theorem leaf_1727_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1727.profileLo box_1727.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1727_ok
theorem branch_box_1727_nonnegative : ∀ j, 0 ≤ branch_box_1727.lower j ∧ 0 ≤ branch_box_1727.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1727, Box.profileLo, Box.profileHi, box_1727]
theorem leaf_1727_BranchSafe : CertificateConsequences.BranchSafe branch_box_1727 := by
  left; refine ⟨branch_box_1727_nonnegative, ?_⟩
  intro z hz; exact leaf_1727_sound hz

theorem leaf_1729_ok : checkAt 527 1000 box_1729 cert_1729 = true := by
  have h := List.all_eq_true.mp batch_34_10_ok accepted_1729 (by simp [batch_34_10_values])
  exact h
theorem leaf_1729_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1729.profileLo box_1729.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1729_ok
theorem branch_box_1729_nonnegative : ∀ j, 0 ≤ branch_box_1729.lower j ∧ 0 ≤ branch_box_1729.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1729, Box.profileLo, Box.profileHi, box_1729]
theorem leaf_1729_BranchSafe : CertificateConsequences.BranchSafe branch_box_1729 := by
  left; refine ⟨branch_box_1729_nonnegative, ?_⟩
  intro z hz; exact leaf_1729_sound hz

theorem leaf_1733_ok : checkAt 527 1000 box_1733 cert_1733 = true := by
  have h := List.all_eq_true.mp batch_34_11_ok accepted_1733 (by simp [batch_34_11_values])
  exact h
theorem leaf_1733_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1733.profileLo box_1733.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1733_ok
theorem branch_box_1733_nonnegative : ∀ j, 0 ≤ branch_box_1733.lower j ∧ 0 ≤ branch_box_1733.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1733, Box.profileLo, Box.profileHi, box_1733]
theorem leaf_1733_BranchSafe : CertificateConsequences.BranchSafe branch_box_1733 := by
  left; refine ⟨branch_box_1733_nonnegative, ?_⟩
  intro z hz; exact leaf_1733_sound hz

theorem leaf_1735_ok : checkAt 527 1000 box_1735 cert_1735 = true := by
  have h := List.all_eq_true.mp batch_34_12_ok accepted_1735 (by simp [batch_34_12_values])
  exact h
theorem leaf_1735_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1735.profileLo box_1735.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1735_ok
theorem branch_box_1735_nonnegative : ∀ j, 0 ≤ branch_box_1735.lower j ∧ 0 ≤ branch_box_1735.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1735, Box.profileLo, Box.profileHi, box_1735]
theorem leaf_1735_BranchSafe : CertificateConsequences.BranchSafe branch_box_1735 := by
  left; refine ⟨branch_box_1735_nonnegative, ?_⟩
  intro z hz; exact leaf_1735_sound hz

theorem leaf_1737_ok : checkAt 527 1000 box_1737 cert_1737 = true := by
  have h := List.all_eq_true.mp batch_34_13_ok accepted_1737 (by simp [batch_34_13_values])
  exact h
theorem leaf_1737_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1737.profileLo box_1737.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1737_ok
theorem branch_box_1737_nonnegative : ∀ j, 0 ≤ branch_box_1737.lower j ∧ 0 ≤ branch_box_1737.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1737, Box.profileLo, Box.profileHi, box_1737]
theorem leaf_1737_BranchSafe : CertificateConsequences.BranchSafe branch_box_1737 := by
  left; refine ⟨branch_box_1737_nonnegative, ?_⟩
  intro z hz; exact leaf_1737_sound hz

theorem leaf_1739_ok : checkAt 527 1000 box_1739 cert_1739 = true := by
  have h := List.all_eq_true.mp batch_34_14_ok accepted_1739 (by simp [batch_34_14_values])
  exact h
theorem leaf_1739_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1739.profileLo box_1739.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1739_ok
theorem branch_box_1739_nonnegative : ∀ j, 0 ≤ branch_box_1739.lower j ∧ 0 ≤ branch_box_1739.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1739, Box.profileLo, Box.profileHi, box_1739]
theorem leaf_1739_BranchSafe : CertificateConsequences.BranchSafe branch_box_1739 := by
  left; refine ⟨branch_box_1739_nonnegative, ?_⟩
  intro z hz; exact leaf_1739_sound hz

theorem leaf_1741_ok : checkAt 527 1000 box_1741 cert_1741 = true := by
  have h := List.all_eq_true.mp batch_34_15_ok accepted_1741 (by simp [batch_34_15_values])
  exact h
theorem leaf_1741_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1741.profileLo box_1741.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1741_ok
theorem branch_box_1741_nonnegative : ∀ j, 0 ≤ branch_box_1741.lower j ∧ 0 ≤ branch_box_1741.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1741, Box.profileLo, Box.profileHi, box_1741]
theorem leaf_1741_BranchSafe : CertificateConsequences.BranchSafe branch_box_1741 := by
  left; refine ⟨branch_box_1741_nonnegative, ?_⟩
  intro z hz; exact leaf_1741_sound hz

theorem leaf_1743_ok : checkAt 527 1000 box_1743 cert_1743 = true := by
  have h := List.all_eq_true.mp batch_34_16_ok accepted_1743 (by simp [batch_34_16_values])
  exact h
theorem leaf_1743_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1743.profileLo box_1743.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1743_ok
theorem branch_box_1743_nonnegative : ∀ j, 0 ≤ branch_box_1743.lower j ∧ 0 ≤ branch_box_1743.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1743, Box.profileLo, Box.profileHi, box_1743]
theorem leaf_1743_BranchSafe : CertificateConsequences.BranchSafe branch_box_1743 := by
  left; refine ⟨branch_box_1743_nonnegative, ?_⟩
  intro z hz; exact leaf_1743_sound hz

theorem leaf_1746_ok : checkAt 527 1000 box_1746 cert_1746 = true := by
  have h := List.all_eq_true.mp batch_34_17_ok accepted_1746 (by simp [batch_34_17_values])
  exact h
theorem leaf_1746_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1746.profileLo box_1746.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1746_ok
theorem branch_box_1746_nonnegative : ∀ j, 0 ≤ branch_box_1746.lower j ∧ 0 ≤ branch_box_1746.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1746, Box.profileLo, Box.profileHi, box_1746]
theorem leaf_1746_BranchSafe : CertificateConsequences.BranchSafe branch_box_1746 := by
  left; refine ⟨branch_box_1746_nonnegative, ?_⟩
  intro z hz; exact leaf_1746_sound hz

#print axioms batch_34_00_ok
#print axioms leaf_1702_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
