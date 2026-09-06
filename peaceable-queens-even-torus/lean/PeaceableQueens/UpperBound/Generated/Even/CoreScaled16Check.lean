import PeaceableQueens.UpperBound.Generated.Even.CoreScaled16Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_16_00_values : List Bool := [accepted_800]
theorem batch_16_00_ok : batch_16_00_values.all id = true := by decide

def batch_16_01_values : List Bool := [accepted_802]
theorem batch_16_01_ok : batch_16_01_values.all id = true := by decide

def batch_16_02_values : List Bool := [accepted_804]
theorem batch_16_02_ok : batch_16_02_values.all id = true := by decide

def batch_16_03_values : List Bool := [accepted_806]
theorem batch_16_03_ok : batch_16_03_values.all id = true := by decide

def batch_16_04_values : List Bool := [accepted_807]
theorem batch_16_04_ok : batch_16_04_values.all id = true := by decide

def batch_16_05_values : List Bool := [accepted_809]
theorem batch_16_05_ok : batch_16_05_values.all id = true := by decide

def batch_16_06_values : List Bool := [accepted_812]
theorem batch_16_06_ok : batch_16_06_values.all id = true := by decide

def batch_16_07_values : List Bool := [accepted_813]
theorem batch_16_07_ok : batch_16_07_values.all id = true := by decide

def batch_16_08_values : List Bool := [accepted_816]
theorem batch_16_08_ok : batch_16_08_values.all id = true := by decide

def batch_16_09_values : List Bool := [accepted_818]
theorem batch_16_09_ok : batch_16_09_values.all id = true := by decide

def batch_16_10_values : List Bool := [accepted_819]
theorem batch_16_10_ok : batch_16_10_values.all id = true := by decide

def batch_16_11_values : List Bool := [accepted_821]
theorem batch_16_11_ok : batch_16_11_values.all id = true := by decide

def batch_16_12_values : List Bool := [accepted_824]
theorem batch_16_12_ok : batch_16_12_values.all id = true := by decide

def batch_16_13_values : List Bool := [accepted_825]
theorem batch_16_13_ok : batch_16_13_values.all id = true := by decide

def batch_16_14_values : List Bool := [accepted_828]
theorem batch_16_14_ok : batch_16_14_values.all id = true := by decide

def batch_16_15_values : List Bool := [accepted_830]
theorem batch_16_15_ok : batch_16_15_values.all id = true := by decide

def batch_16_16_values : List Bool := [accepted_832]
theorem batch_16_16_ok : batch_16_16_values.all id = true := by decide

def batch_16_17_values : List Bool := [accepted_833]
theorem batch_16_17_ok : batch_16_17_values.all id = true := by decide

def batch_16_18_values : List Bool := [accepted_835]
theorem batch_16_18_ok : batch_16_18_values.all id = true := by decide

def batch_16_19_values : List Bool := [accepted_837]
theorem batch_16_19_ok : batch_16_19_values.all id = true := by decide

def batch_16_20_values : List Bool := [accepted_840]
theorem batch_16_20_ok : batch_16_20_values.all id = true := by decide

def batch_16_21_values : List Bool := [accepted_848]
theorem batch_16_21_ok : batch_16_21_values.all id = true := by decide

theorem leaf_800_ok : checkAt 527 1000 box_800 cert_800 = true := by
  have h := List.all_eq_true.mp batch_16_00_ok accepted_800 (by simp [batch_16_00_values])
  exact h
theorem leaf_800_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_800.profileLo box_800.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_800_ok
theorem branch_box_800_nonnegative : ∀ j, 0 ≤ branch_box_800.lower j ∧ 0 ≤ branch_box_800.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_800, Box.profileLo, Box.profileHi, box_800]
theorem leaf_800_BranchSafe : CertificateConsequences.BranchSafe branch_box_800 := by
  left; refine ⟨branch_box_800_nonnegative, ?_⟩
  intro z hz; exact leaf_800_sound hz

theorem leaf_802_ok : checkAt 527 1000 box_802 cert_802 = true := by
  have h := List.all_eq_true.mp batch_16_01_ok accepted_802 (by simp [batch_16_01_values])
  exact h
theorem leaf_802_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_802.profileLo box_802.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_802_ok
theorem branch_box_802_nonnegative : ∀ j, 0 ≤ branch_box_802.lower j ∧ 0 ≤ branch_box_802.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_802, Box.profileLo, Box.profileHi, box_802]
theorem leaf_802_BranchSafe : CertificateConsequences.BranchSafe branch_box_802 := by
  left; refine ⟨branch_box_802_nonnegative, ?_⟩
  intro z hz; exact leaf_802_sound hz

theorem leaf_804_ok : checkAt 527 1000 box_804 cert_804 = true := by
  have h := List.all_eq_true.mp batch_16_02_ok accepted_804 (by simp [batch_16_02_values])
  exact h
theorem leaf_804_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_804.profileLo box_804.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_804_ok
theorem branch_box_804_nonnegative : ∀ j, 0 ≤ branch_box_804.lower j ∧ 0 ≤ branch_box_804.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_804, Box.profileLo, Box.profileHi, box_804]
theorem leaf_804_BranchSafe : CertificateConsequences.BranchSafe branch_box_804 := by
  left; refine ⟨branch_box_804_nonnegative, ?_⟩
  intro z hz; exact leaf_804_sound hz

theorem leaf_806_ok : checkAt 527 1000 box_806 cert_806 = true := by
  have h := List.all_eq_true.mp batch_16_03_ok accepted_806 (by simp [batch_16_03_values])
  exact h
theorem leaf_806_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_806.profileLo box_806.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_806_ok
theorem branch_box_806_nonnegative : ∀ j, 0 ≤ branch_box_806.lower j ∧ 0 ≤ branch_box_806.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_806, Box.profileLo, Box.profileHi, box_806]
theorem leaf_806_BranchSafe : CertificateConsequences.BranchSafe branch_box_806 := by
  left; refine ⟨branch_box_806_nonnegative, ?_⟩
  intro z hz; exact leaf_806_sound hz

theorem leaf_807_ok : checkAt 527 1000 box_807 cert_807 = true := by
  have h := List.all_eq_true.mp batch_16_04_ok accepted_807 (by simp [batch_16_04_values])
  exact h
theorem leaf_807_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_807.profileLo box_807.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_807_ok
theorem branch_box_807_nonnegative : ∀ j, 0 ≤ branch_box_807.lower j ∧ 0 ≤ branch_box_807.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_807, Box.profileLo, Box.profileHi, box_807]
theorem leaf_807_BranchSafe : CertificateConsequences.BranchSafe branch_box_807 := by
  left; refine ⟨branch_box_807_nonnegative, ?_⟩
  intro z hz; exact leaf_807_sound hz

theorem leaf_809_ok : checkAt 527 1000 box_809 cert_809 = true := by
  have h := List.all_eq_true.mp batch_16_05_ok accepted_809 (by simp [batch_16_05_values])
  exact h
theorem leaf_809_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_809.profileLo box_809.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_809_ok
theorem branch_box_809_nonnegative : ∀ j, 0 ≤ branch_box_809.lower j ∧ 0 ≤ branch_box_809.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_809, Box.profileLo, Box.profileHi, box_809]
theorem leaf_809_BranchSafe : CertificateConsequences.BranchSafe branch_box_809 := by
  left; refine ⟨branch_box_809_nonnegative, ?_⟩
  intro z hz; exact leaf_809_sound hz

theorem leaf_812_ok : checkAt 527 1000 box_812 cert_812 = true := by
  have h := List.all_eq_true.mp batch_16_06_ok accepted_812 (by simp [batch_16_06_values])
  exact h
theorem leaf_812_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_812.profileLo box_812.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_812_ok
theorem branch_box_812_nonnegative : ∀ j, 0 ≤ branch_box_812.lower j ∧ 0 ≤ branch_box_812.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_812, Box.profileLo, Box.profileHi, box_812]
theorem leaf_812_BranchSafe : CertificateConsequences.BranchSafe branch_box_812 := by
  left; refine ⟨branch_box_812_nonnegative, ?_⟩
  intro z hz; exact leaf_812_sound hz

theorem leaf_813_ok : checkAt 527 1000 box_813 cert_813 = true := by
  have h := List.all_eq_true.mp batch_16_07_ok accepted_813 (by simp [batch_16_07_values])
  exact h
theorem leaf_813_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_813.profileLo box_813.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_813_ok
theorem branch_box_813_nonnegative : ∀ j, 0 ≤ branch_box_813.lower j ∧ 0 ≤ branch_box_813.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_813, Box.profileLo, Box.profileHi, box_813]
theorem leaf_813_BranchSafe : CertificateConsequences.BranchSafe branch_box_813 := by
  left; refine ⟨branch_box_813_nonnegative, ?_⟩
  intro z hz; exact leaf_813_sound hz

theorem leaf_816_ok : checkAt 527 1000 box_816 cert_816 = true := by
  have h := List.all_eq_true.mp batch_16_08_ok accepted_816 (by simp [batch_16_08_values])
  exact h
theorem leaf_816_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_816.profileLo box_816.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_816_ok
theorem branch_box_816_nonnegative : ∀ j, 0 ≤ branch_box_816.lower j ∧ 0 ≤ branch_box_816.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_816, Box.profileLo, Box.profileHi, box_816]
theorem leaf_816_BranchSafe : CertificateConsequences.BranchSafe branch_box_816 := by
  left; refine ⟨branch_box_816_nonnegative, ?_⟩
  intro z hz; exact leaf_816_sound hz

theorem leaf_818_ok : checkAt 527 1000 box_818 cert_818 = true := by
  have h := List.all_eq_true.mp batch_16_09_ok accepted_818 (by simp [batch_16_09_values])
  exact h
theorem leaf_818_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_818.profileLo box_818.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_818_ok
theorem branch_box_818_nonnegative : ∀ j, 0 ≤ branch_box_818.lower j ∧ 0 ≤ branch_box_818.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_818, Box.profileLo, Box.profileHi, box_818]
theorem leaf_818_BranchSafe : CertificateConsequences.BranchSafe branch_box_818 := by
  left; refine ⟨branch_box_818_nonnegative, ?_⟩
  intro z hz; exact leaf_818_sound hz

theorem leaf_819_ok : checkAt 527 1000 box_819 cert_819 = true := by
  have h := List.all_eq_true.mp batch_16_10_ok accepted_819 (by simp [batch_16_10_values])
  exact h
theorem leaf_819_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_819.profileLo box_819.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_819_ok
theorem branch_box_819_nonnegative : ∀ j, 0 ≤ branch_box_819.lower j ∧ 0 ≤ branch_box_819.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_819, Box.profileLo, Box.profileHi, box_819]
theorem leaf_819_BranchSafe : CertificateConsequences.BranchSafe branch_box_819 := by
  left; refine ⟨branch_box_819_nonnegative, ?_⟩
  intro z hz; exact leaf_819_sound hz

theorem leaf_821_ok : checkAt 527 1000 box_821 cert_821 = true := by
  have h := List.all_eq_true.mp batch_16_11_ok accepted_821 (by simp [batch_16_11_values])
  exact h
theorem leaf_821_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_821.profileLo box_821.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_821_ok
theorem branch_box_821_nonnegative : ∀ j, 0 ≤ branch_box_821.lower j ∧ 0 ≤ branch_box_821.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_821, Box.profileLo, Box.profileHi, box_821]
theorem leaf_821_BranchSafe : CertificateConsequences.BranchSafe branch_box_821 := by
  left; refine ⟨branch_box_821_nonnegative, ?_⟩
  intro z hz; exact leaf_821_sound hz

theorem leaf_824_ok : checkAt 527 1000 box_824 cert_824 = true := by
  have h := List.all_eq_true.mp batch_16_12_ok accepted_824 (by simp [batch_16_12_values])
  exact h
theorem leaf_824_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_824.profileLo box_824.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_824_ok
theorem branch_box_824_nonnegative : ∀ j, 0 ≤ branch_box_824.lower j ∧ 0 ≤ branch_box_824.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_824, Box.profileLo, Box.profileHi, box_824]
theorem leaf_824_BranchSafe : CertificateConsequences.BranchSafe branch_box_824 := by
  left; refine ⟨branch_box_824_nonnegative, ?_⟩
  intro z hz; exact leaf_824_sound hz

theorem leaf_825_ok : checkAt 527 1000 box_825 cert_825 = true := by
  have h := List.all_eq_true.mp batch_16_13_ok accepted_825 (by simp [batch_16_13_values])
  exact h
theorem leaf_825_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_825.profileLo box_825.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_825_ok
theorem branch_box_825_nonnegative : ∀ j, 0 ≤ branch_box_825.lower j ∧ 0 ≤ branch_box_825.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_825, Box.profileLo, Box.profileHi, box_825]
theorem leaf_825_BranchSafe : CertificateConsequences.BranchSafe branch_box_825 := by
  left; refine ⟨branch_box_825_nonnegative, ?_⟩
  intro z hz; exact leaf_825_sound hz

theorem leaf_828_ok : checkAt 527 1000 box_828 cert_828 = true := by
  have h := List.all_eq_true.mp batch_16_14_ok accepted_828 (by simp [batch_16_14_values])
  exact h
theorem leaf_828_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_828.profileLo box_828.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_828_ok
theorem branch_box_828_nonnegative : ∀ j, 0 ≤ branch_box_828.lower j ∧ 0 ≤ branch_box_828.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_828, Box.profileLo, Box.profileHi, box_828]
theorem leaf_828_BranchSafe : CertificateConsequences.BranchSafe branch_box_828 := by
  left; refine ⟨branch_box_828_nonnegative, ?_⟩
  intro z hz; exact leaf_828_sound hz

theorem leaf_830_ok : checkAt 527 1000 box_830 cert_830 = true := by
  have h := List.all_eq_true.mp batch_16_15_ok accepted_830 (by simp [batch_16_15_values])
  exact h
theorem leaf_830_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_830.profileLo box_830.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_830_ok
theorem branch_box_830_nonnegative : ∀ j, 0 ≤ branch_box_830.lower j ∧ 0 ≤ branch_box_830.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_830, Box.profileLo, Box.profileHi, box_830]
theorem leaf_830_BranchSafe : CertificateConsequences.BranchSafe branch_box_830 := by
  left; refine ⟨branch_box_830_nonnegative, ?_⟩
  intro z hz; exact leaf_830_sound hz

theorem leaf_832_ok : checkAt 527 1000 box_832 cert_832 = true := by
  have h := List.all_eq_true.mp batch_16_16_ok accepted_832 (by simp [batch_16_16_values])
  exact h
theorem leaf_832_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_832.profileLo box_832.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_832_ok
theorem branch_box_832_nonnegative : ∀ j, 0 ≤ branch_box_832.lower j ∧ 0 ≤ branch_box_832.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_832, Box.profileLo, Box.profileHi, box_832]
theorem leaf_832_BranchSafe : CertificateConsequences.BranchSafe branch_box_832 := by
  left; refine ⟨branch_box_832_nonnegative, ?_⟩
  intro z hz; exact leaf_832_sound hz

theorem leaf_833_ok : checkAt 527 1000 box_833 cert_833 = true := by
  have h := List.all_eq_true.mp batch_16_17_ok accepted_833 (by simp [batch_16_17_values])
  exact h
theorem leaf_833_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_833.profileLo box_833.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_833_ok
theorem branch_box_833_nonnegative : ∀ j, 0 ≤ branch_box_833.lower j ∧ 0 ≤ branch_box_833.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_833, Box.profileLo, Box.profileHi, box_833]
theorem leaf_833_BranchSafe : CertificateConsequences.BranchSafe branch_box_833 := by
  left; refine ⟨branch_box_833_nonnegative, ?_⟩
  intro z hz; exact leaf_833_sound hz

theorem leaf_835_ok : checkAt 527 1000 box_835 cert_835 = true := by
  have h := List.all_eq_true.mp batch_16_18_ok accepted_835 (by simp [batch_16_18_values])
  exact h
theorem leaf_835_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_835.profileLo box_835.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_835_ok
theorem branch_box_835_nonnegative : ∀ j, 0 ≤ branch_box_835.lower j ∧ 0 ≤ branch_box_835.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_835, Box.profileLo, Box.profileHi, box_835]
theorem leaf_835_BranchSafe : CertificateConsequences.BranchSafe branch_box_835 := by
  left; refine ⟨branch_box_835_nonnegative, ?_⟩
  intro z hz; exact leaf_835_sound hz

theorem leaf_837_ok : checkAt 527 1000 box_837 cert_837 = true := by
  have h := List.all_eq_true.mp batch_16_19_ok accepted_837 (by simp [batch_16_19_values])
  exact h
theorem leaf_837_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_837.profileLo box_837.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_837_ok
theorem branch_box_837_nonnegative : ∀ j, 0 ≤ branch_box_837.lower j ∧ 0 ≤ branch_box_837.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_837, Box.profileLo, Box.profileHi, box_837]
theorem leaf_837_BranchSafe : CertificateConsequences.BranchSafe branch_box_837 := by
  left; refine ⟨branch_box_837_nonnegative, ?_⟩
  intro z hz; exact leaf_837_sound hz

theorem leaf_840_ok : checkAt 527 1000 box_840 cert_840 = true := by
  have h := List.all_eq_true.mp batch_16_20_ok accepted_840 (by simp [batch_16_20_values])
  exact h
theorem leaf_840_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_840.profileLo box_840.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_840_ok
theorem branch_box_840_nonnegative : ∀ j, 0 ≤ branch_box_840.lower j ∧ 0 ≤ branch_box_840.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_840, Box.profileLo, Box.profileHi, box_840]
theorem leaf_840_BranchSafe : CertificateConsequences.BranchSafe branch_box_840 := by
  left; refine ⟨branch_box_840_nonnegative, ?_⟩
  intro z hz; exact leaf_840_sound hz

theorem leaf_848_ok : checkAt 527 1000 box_848 cert_848 = true := by
  have h := List.all_eq_true.mp batch_16_21_ok accepted_848 (by simp [batch_16_21_values])
  exact h
theorem leaf_848_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_848.profileLo box_848.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_848_ok
theorem branch_box_848_nonnegative : ∀ j, 0 ≤ branch_box_848.lower j ∧ 0 ≤ branch_box_848.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_848, Box.profileLo, Box.profileHi, box_848]
theorem leaf_848_BranchSafe : CertificateConsequences.BranchSafe branch_box_848 := by
  left; refine ⟨branch_box_848_nonnegative, ?_⟩
  intro z hz; exact leaf_848_sound hz

#print axioms batch_16_00_ok
#print axioms leaf_800_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
