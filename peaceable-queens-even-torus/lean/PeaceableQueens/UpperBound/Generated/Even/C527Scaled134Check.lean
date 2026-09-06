import PeaceableQueens.UpperBound.Generated.Even.C527Scaled134Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_134_00_values : List Bool := [accepted_6700]
theorem batch_134_00_ok : batch_134_00_values.all id = true := by decide

def batch_134_01_values : List Bool := [accepted_6702]
theorem batch_134_01_ok : batch_134_01_values.all id = true := by decide

def batch_134_02_values : List Bool := [accepted_6703]
theorem batch_134_02_ok : batch_134_02_values.all id = true := by decide

def batch_134_03_values : List Bool := [accepted_6704]
theorem batch_134_03_ok : batch_134_03_values.all id = true := by decide

def batch_134_04_values : List Bool := [accepted_6710]
theorem batch_134_04_ok : batch_134_04_values.all id = true := by decide

def batch_134_05_values : List Bool := [accepted_6711]
theorem batch_134_05_ok : batch_134_05_values.all id = true := by decide

def batch_134_06_values : List Bool := [accepted_6712]
theorem batch_134_06_ok : batch_134_06_values.all id = true := by decide

def batch_134_07_values : List Bool := [accepted_6714]
theorem batch_134_07_ok : batch_134_07_values.all id = true := by decide

def batch_134_08_values : List Bool := [accepted_6716]
theorem batch_134_08_ok : batch_134_08_values.all id = true := by decide

def batch_134_09_values : List Bool := [accepted_6717]
theorem batch_134_09_ok : batch_134_09_values.all id = true := by decide

def batch_134_10_values : List Bool := [accepted_6718]
theorem batch_134_10_ok : batch_134_10_values.all id = true := by decide

def batch_134_11_values : List Bool := [accepted_6719]
theorem batch_134_11_ok : batch_134_11_values.all id = true := by decide

def batch_134_12_values : List Bool := [accepted_6720]
theorem batch_134_12_ok : batch_134_12_values.all id = true := by decide

def batch_134_13_values : List Bool := [accepted_6723]
theorem batch_134_13_ok : batch_134_13_values.all id = true := by decide

def batch_134_14_values : List Bool := [accepted_6727]
theorem batch_134_14_ok : batch_134_14_values.all id = true := by decide

def batch_134_15_values : List Bool := [accepted_6728]
theorem batch_134_15_ok : batch_134_15_values.all id = true := by decide

def batch_134_16_values : List Bool := [accepted_6733]
theorem batch_134_16_ok : batch_134_16_values.all id = true := by decide

def batch_134_17_values : List Bool := [accepted_6734]
theorem batch_134_17_ok : batch_134_17_values.all id = true := by decide

def batch_134_18_values : List Bool := [accepted_6735]
theorem batch_134_18_ok : batch_134_18_values.all id = true := by decide

def batch_134_19_values : List Bool := [accepted_6736]
theorem batch_134_19_ok : batch_134_19_values.all id = true := by decide

def batch_134_20_values : List Bool := [accepted_6743]
theorem batch_134_20_ok : batch_134_20_values.all id = true := by decide

def batch_134_21_values : List Bool := [accepted_6744]
theorem batch_134_21_ok : batch_134_21_values.all id = true := by decide

def batch_134_22_values : List Bool := [accepted_6747]
theorem batch_134_22_ok : batch_134_22_values.all id = true := by decide

def batch_134_23_values : List Bool := [accepted_6749]
theorem batch_134_23_ok : batch_134_23_values.all id = true := by decide

theorem leaf_6700_ok : checkAt 527 1000 box_6700 cert_6700 = true := by
  have h := List.all_eq_true.mp batch_134_00_ok accepted_6700 (by simp [batch_134_00_values])
  exact h
theorem leaf_6700_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6700.profileLo box_6700.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6700_ok
theorem branch_box_6700_nonnegative : ∀ j, 0 ≤ branch_box_6700.lower j ∧ 0 ≤ branch_box_6700.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6700, Box.profileLo, Box.profileHi, box_6700]
theorem leaf_6700_BranchSafe : CertificateConsequences.BranchSafe branch_box_6700 := by
  left; refine ⟨branch_box_6700_nonnegative, ?_⟩
  intro z hz; exact leaf_6700_sound hz

theorem leaf_6702_ok : checkAt 527 1000 box_6702 cert_6702 = true := by
  have h := List.all_eq_true.mp batch_134_01_ok accepted_6702 (by simp [batch_134_01_values])
  exact h
theorem leaf_6702_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6702.profileLo box_6702.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6702_ok
theorem branch_box_6702_nonnegative : ∀ j, 0 ≤ branch_box_6702.lower j ∧ 0 ≤ branch_box_6702.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6702, Box.profileLo, Box.profileHi, box_6702]
theorem leaf_6702_BranchSafe : CertificateConsequences.BranchSafe branch_box_6702 := by
  left; refine ⟨branch_box_6702_nonnegative, ?_⟩
  intro z hz; exact leaf_6702_sound hz

theorem leaf_6703_ok : checkAt 527 1000 box_6703 cert_6703 = true := by
  have h := List.all_eq_true.mp batch_134_02_ok accepted_6703 (by simp [batch_134_02_values])
  exact h
theorem leaf_6703_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6703.profileLo box_6703.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6703_ok
theorem branch_box_6703_nonnegative : ∀ j, 0 ≤ branch_box_6703.lower j ∧ 0 ≤ branch_box_6703.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6703, Box.profileLo, Box.profileHi, box_6703]
theorem leaf_6703_BranchSafe : CertificateConsequences.BranchSafe branch_box_6703 := by
  left; refine ⟨branch_box_6703_nonnegative, ?_⟩
  intro z hz; exact leaf_6703_sound hz

theorem leaf_6704_ok : checkAt 527 1000 box_6704 cert_6704 = true := by
  have h := List.all_eq_true.mp batch_134_03_ok accepted_6704 (by simp [batch_134_03_values])
  exact h
theorem leaf_6704_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6704.profileLo box_6704.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6704_ok
theorem branch_box_6704_nonnegative : ∀ j, 0 ≤ branch_box_6704.lower j ∧ 0 ≤ branch_box_6704.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6704, Box.profileLo, Box.profileHi, box_6704]
theorem leaf_6704_BranchSafe : CertificateConsequences.BranchSafe branch_box_6704 := by
  left; refine ⟨branch_box_6704_nonnegative, ?_⟩
  intro z hz; exact leaf_6704_sound hz

theorem leaf_6710_ok : checkAt 527 1000 box_6710 cert_6710 = true := by
  have h := List.all_eq_true.mp batch_134_04_ok accepted_6710 (by simp [batch_134_04_values])
  exact h
theorem leaf_6710_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6710.profileLo box_6710.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6710_ok
theorem branch_box_6710_nonnegative : ∀ j, 0 ≤ branch_box_6710.lower j ∧ 0 ≤ branch_box_6710.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6710, Box.profileLo, Box.profileHi, box_6710]
theorem leaf_6710_BranchSafe : CertificateConsequences.BranchSafe branch_box_6710 := by
  left; refine ⟨branch_box_6710_nonnegative, ?_⟩
  intro z hz; exact leaf_6710_sound hz

theorem leaf_6711_ok : checkAt 527 1000 box_6711 cert_6711 = true := by
  have h := List.all_eq_true.mp batch_134_05_ok accepted_6711 (by simp [batch_134_05_values])
  exact h
theorem leaf_6711_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6711.profileLo box_6711.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6711_ok
theorem branch_box_6711_nonnegative : ∀ j, 0 ≤ branch_box_6711.lower j ∧ 0 ≤ branch_box_6711.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6711, Box.profileLo, Box.profileHi, box_6711]
theorem leaf_6711_BranchSafe : CertificateConsequences.BranchSafe branch_box_6711 := by
  left; refine ⟨branch_box_6711_nonnegative, ?_⟩
  intro z hz; exact leaf_6711_sound hz

theorem leaf_6712_ok : checkAt 527 1000 box_6712 cert_6712 = true := by
  have h := List.all_eq_true.mp batch_134_06_ok accepted_6712 (by simp [batch_134_06_values])
  exact h
theorem leaf_6712_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6712.profileLo box_6712.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6712_ok
theorem branch_box_6712_nonnegative : ∀ j, 0 ≤ branch_box_6712.lower j ∧ 0 ≤ branch_box_6712.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6712, Box.profileLo, Box.profileHi, box_6712]
theorem leaf_6712_BranchSafe : CertificateConsequences.BranchSafe branch_box_6712 := by
  left; refine ⟨branch_box_6712_nonnegative, ?_⟩
  intro z hz; exact leaf_6712_sound hz

theorem leaf_6714_ok : checkAt 527 1000 box_6714 cert_6714 = true := by
  have h := List.all_eq_true.mp batch_134_07_ok accepted_6714 (by simp [batch_134_07_values])
  exact h
theorem leaf_6714_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6714.profileLo box_6714.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6714_ok
theorem branch_box_6714_nonnegative : ∀ j, 0 ≤ branch_box_6714.lower j ∧ 0 ≤ branch_box_6714.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6714, Box.profileLo, Box.profileHi, box_6714]
theorem leaf_6714_BranchSafe : CertificateConsequences.BranchSafe branch_box_6714 := by
  left; refine ⟨branch_box_6714_nonnegative, ?_⟩
  intro z hz; exact leaf_6714_sound hz

theorem leaf_6716_ok : checkAt 527 1000 box_6716 cert_6716 = true := by
  have h := List.all_eq_true.mp batch_134_08_ok accepted_6716 (by simp [batch_134_08_values])
  exact h
theorem leaf_6716_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6716.profileLo box_6716.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6716_ok
theorem branch_box_6716_nonnegative : ∀ j, 0 ≤ branch_box_6716.lower j ∧ 0 ≤ branch_box_6716.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6716, Box.profileLo, Box.profileHi, box_6716]
theorem leaf_6716_BranchSafe : CertificateConsequences.BranchSafe branch_box_6716 := by
  left; refine ⟨branch_box_6716_nonnegative, ?_⟩
  intro z hz; exact leaf_6716_sound hz

theorem leaf_6717_ok : checkAt 527 1000 box_6717 cert_6717 = true := by
  have h := List.all_eq_true.mp batch_134_09_ok accepted_6717 (by simp [batch_134_09_values])
  exact h
theorem leaf_6717_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6717.profileLo box_6717.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6717_ok
theorem branch_box_6717_nonnegative : ∀ j, 0 ≤ branch_box_6717.lower j ∧ 0 ≤ branch_box_6717.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6717, Box.profileLo, Box.profileHi, box_6717]
theorem leaf_6717_BranchSafe : CertificateConsequences.BranchSafe branch_box_6717 := by
  left; refine ⟨branch_box_6717_nonnegative, ?_⟩
  intro z hz; exact leaf_6717_sound hz

theorem leaf_6718_ok : checkAt 527 1000 box_6718 cert_6718 = true := by
  have h := List.all_eq_true.mp batch_134_10_ok accepted_6718 (by simp [batch_134_10_values])
  exact h
theorem leaf_6718_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6718.profileLo box_6718.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6718_ok
theorem branch_box_6718_nonnegative : ∀ j, 0 ≤ branch_box_6718.lower j ∧ 0 ≤ branch_box_6718.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6718, Box.profileLo, Box.profileHi, box_6718]
theorem leaf_6718_BranchSafe : CertificateConsequences.BranchSafe branch_box_6718 := by
  left; refine ⟨branch_box_6718_nonnegative, ?_⟩
  intro z hz; exact leaf_6718_sound hz

theorem leaf_6719_ok : checkAt 527 1000 box_6719 cert_6719 = true := by
  have h := List.all_eq_true.mp batch_134_11_ok accepted_6719 (by simp [batch_134_11_values])
  exact h
theorem leaf_6719_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6719.profileLo box_6719.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6719_ok
theorem branch_box_6719_nonnegative : ∀ j, 0 ≤ branch_box_6719.lower j ∧ 0 ≤ branch_box_6719.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6719, Box.profileLo, Box.profileHi, box_6719]
theorem leaf_6719_BranchSafe : CertificateConsequences.BranchSafe branch_box_6719 := by
  left; refine ⟨branch_box_6719_nonnegative, ?_⟩
  intro z hz; exact leaf_6719_sound hz

theorem leaf_6720_ok : checkAt 527 1000 box_6720 cert_6720 = true := by
  have h := List.all_eq_true.mp batch_134_12_ok accepted_6720 (by simp [batch_134_12_values])
  exact h
theorem leaf_6720_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6720.profileLo box_6720.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6720_ok
theorem branch_box_6720_nonnegative : ∀ j, 0 ≤ branch_box_6720.lower j ∧ 0 ≤ branch_box_6720.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6720, Box.profileLo, Box.profileHi, box_6720]
theorem leaf_6720_BranchSafe : CertificateConsequences.BranchSafe branch_box_6720 := by
  left; refine ⟨branch_box_6720_nonnegative, ?_⟩
  intro z hz; exact leaf_6720_sound hz

theorem leaf_6723_ok : checkAt 527 1000 box_6723 cert_6723 = true := by
  have h := List.all_eq_true.mp batch_134_13_ok accepted_6723 (by simp [batch_134_13_values])
  exact h
theorem leaf_6723_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6723.profileLo box_6723.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6723_ok
theorem branch_box_6723_nonnegative : ∀ j, 0 ≤ branch_box_6723.lower j ∧ 0 ≤ branch_box_6723.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6723, Box.profileLo, Box.profileHi, box_6723]
theorem leaf_6723_BranchSafe : CertificateConsequences.BranchSafe branch_box_6723 := by
  left; refine ⟨branch_box_6723_nonnegative, ?_⟩
  intro z hz; exact leaf_6723_sound hz

theorem leaf_6727_ok : checkAt 527 1000 box_6727 cert_6727 = true := by
  have h := List.all_eq_true.mp batch_134_14_ok accepted_6727 (by simp [batch_134_14_values])
  exact h
theorem leaf_6727_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6727.profileLo box_6727.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6727_ok
theorem branch_box_6727_nonnegative : ∀ j, 0 ≤ branch_box_6727.lower j ∧ 0 ≤ branch_box_6727.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6727, Box.profileLo, Box.profileHi, box_6727]
theorem leaf_6727_BranchSafe : CertificateConsequences.BranchSafe branch_box_6727 := by
  left; refine ⟨branch_box_6727_nonnegative, ?_⟩
  intro z hz; exact leaf_6727_sound hz

theorem leaf_6728_ok : checkAt 527 1000 box_6728 cert_6728 = true := by
  have h := List.all_eq_true.mp batch_134_15_ok accepted_6728 (by simp [batch_134_15_values])
  exact h
theorem leaf_6728_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6728.profileLo box_6728.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6728_ok
theorem branch_box_6728_nonnegative : ∀ j, 0 ≤ branch_box_6728.lower j ∧ 0 ≤ branch_box_6728.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6728, Box.profileLo, Box.profileHi, box_6728]
theorem leaf_6728_BranchSafe : CertificateConsequences.BranchSafe branch_box_6728 := by
  left; refine ⟨branch_box_6728_nonnegative, ?_⟩
  intro z hz; exact leaf_6728_sound hz

theorem leaf_6733_ok : checkAt 527 1000 box_6733 cert_6733 = true := by
  have h := List.all_eq_true.mp batch_134_16_ok accepted_6733 (by simp [batch_134_16_values])
  exact h
theorem leaf_6733_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6733.profileLo box_6733.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6733_ok
theorem branch_box_6733_nonnegative : ∀ j, 0 ≤ branch_box_6733.lower j ∧ 0 ≤ branch_box_6733.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6733, Box.profileLo, Box.profileHi, box_6733]
theorem leaf_6733_BranchSafe : CertificateConsequences.BranchSafe branch_box_6733 := by
  left; refine ⟨branch_box_6733_nonnegative, ?_⟩
  intro z hz; exact leaf_6733_sound hz

theorem leaf_6734_ok : checkAt 527 1000 box_6734 cert_6734 = true := by
  have h := List.all_eq_true.mp batch_134_17_ok accepted_6734 (by simp [batch_134_17_values])
  exact h
theorem leaf_6734_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6734.profileLo box_6734.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6734_ok
theorem branch_box_6734_nonnegative : ∀ j, 0 ≤ branch_box_6734.lower j ∧ 0 ≤ branch_box_6734.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6734, Box.profileLo, Box.profileHi, box_6734]
theorem leaf_6734_BranchSafe : CertificateConsequences.BranchSafe branch_box_6734 := by
  left; refine ⟨branch_box_6734_nonnegative, ?_⟩
  intro z hz; exact leaf_6734_sound hz

theorem leaf_6735_ok : checkAt 527 1000 box_6735 cert_6735 = true := by
  have h := List.all_eq_true.mp batch_134_18_ok accepted_6735 (by simp [batch_134_18_values])
  exact h
theorem leaf_6735_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6735.profileLo box_6735.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6735_ok
theorem branch_box_6735_nonnegative : ∀ j, 0 ≤ branch_box_6735.lower j ∧ 0 ≤ branch_box_6735.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6735, Box.profileLo, Box.profileHi, box_6735]
theorem leaf_6735_BranchSafe : CertificateConsequences.BranchSafe branch_box_6735 := by
  left; refine ⟨branch_box_6735_nonnegative, ?_⟩
  intro z hz; exact leaf_6735_sound hz

theorem leaf_6736_ok : checkAt 527 1000 box_6736 cert_6736 = true := by
  have h := List.all_eq_true.mp batch_134_19_ok accepted_6736 (by simp [batch_134_19_values])
  exact h
theorem leaf_6736_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6736.profileLo box_6736.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6736_ok
theorem branch_box_6736_nonnegative : ∀ j, 0 ≤ branch_box_6736.lower j ∧ 0 ≤ branch_box_6736.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6736, Box.profileLo, Box.profileHi, box_6736]
theorem leaf_6736_BranchSafe : CertificateConsequences.BranchSafe branch_box_6736 := by
  left; refine ⟨branch_box_6736_nonnegative, ?_⟩
  intro z hz; exact leaf_6736_sound hz

theorem leaf_6743_ok : checkAt 527 1000 box_6743 cert_6743 = true := by
  have h := List.all_eq_true.mp batch_134_20_ok accepted_6743 (by simp [batch_134_20_values])
  exact h
theorem leaf_6743_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6743.profileLo box_6743.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6743_ok
theorem branch_box_6743_nonnegative : ∀ j, 0 ≤ branch_box_6743.lower j ∧ 0 ≤ branch_box_6743.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6743, Box.profileLo, Box.profileHi, box_6743]
theorem leaf_6743_BranchSafe : CertificateConsequences.BranchSafe branch_box_6743 := by
  left; refine ⟨branch_box_6743_nonnegative, ?_⟩
  intro z hz; exact leaf_6743_sound hz

theorem leaf_6744_ok : checkAt 527 1000 box_6744 cert_6744 = true := by
  have h := List.all_eq_true.mp batch_134_21_ok accepted_6744 (by simp [batch_134_21_values])
  exact h
theorem leaf_6744_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6744.profileLo box_6744.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6744_ok
theorem branch_box_6744_nonnegative : ∀ j, 0 ≤ branch_box_6744.lower j ∧ 0 ≤ branch_box_6744.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6744, Box.profileLo, Box.profileHi, box_6744]
theorem leaf_6744_BranchSafe : CertificateConsequences.BranchSafe branch_box_6744 := by
  left; refine ⟨branch_box_6744_nonnegative, ?_⟩
  intro z hz; exact leaf_6744_sound hz

theorem leaf_6747_ok : checkAt 527 1000 box_6747 cert_6747 = true := by
  have h := List.all_eq_true.mp batch_134_22_ok accepted_6747 (by simp [batch_134_22_values])
  exact h
theorem leaf_6747_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6747.profileLo box_6747.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6747_ok
theorem branch_box_6747_nonnegative : ∀ j, 0 ≤ branch_box_6747.lower j ∧ 0 ≤ branch_box_6747.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6747, Box.profileLo, Box.profileHi, box_6747]
theorem leaf_6747_BranchSafe : CertificateConsequences.BranchSafe branch_box_6747 := by
  left; refine ⟨branch_box_6747_nonnegative, ?_⟩
  intro z hz; exact leaf_6747_sound hz

theorem leaf_6749_ok : checkAt 527 1000 box_6749 cert_6749 = true := by
  have h := List.all_eq_true.mp batch_134_23_ok accepted_6749 (by simp [batch_134_23_values])
  exact h
theorem leaf_6749_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6749.profileLo box_6749.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6749_ok
theorem branch_box_6749_nonnegative : ∀ j, 0 ≤ branch_box_6749.lower j ∧ 0 ≤ branch_box_6749.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6749, Box.profileLo, Box.profileHi, box_6749]
theorem leaf_6749_BranchSafe : CertificateConsequences.BranchSafe branch_box_6749 := by
  left; refine ⟨branch_box_6749_nonnegative, ?_⟩
  intro z hz; exact leaf_6749_sound hz

#print axioms batch_134_00_ok
#print axioms leaf_6700_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
