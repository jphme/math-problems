import PeaceableQueens.UpperBound.Generated.Even.C527Scaled16Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_16_00_values : List Bool := [accepted_801]
theorem batch_16_00_ok : batch_16_00_values.all id = true := by decide

def batch_16_01_values : List Bool := [accepted_802]
theorem batch_16_01_ok : batch_16_01_values.all id = true := by decide

def batch_16_02_values : List Bool := [accepted_809]
theorem batch_16_02_ok : batch_16_02_values.all id = true := by decide

def batch_16_03_values : List Bool := [accepted_810]
theorem batch_16_03_ok : batch_16_03_values.all id = true := by decide

def batch_16_04_values : List Bool := [accepted_811]
theorem batch_16_04_ok : batch_16_04_values.all id = true := by decide

def batch_16_05_values : List Bool := [accepted_813]
theorem batch_16_05_ok : batch_16_05_values.all id = true := by decide

def batch_16_06_values : List Bool := [accepted_815]
theorem batch_16_06_ok : batch_16_06_values.all id = true := by decide

def batch_16_07_values : List Bool := [accepted_816]
theorem batch_16_07_ok : batch_16_07_values.all id = true := by decide

def batch_16_08_values : List Bool := [accepted_817]
theorem batch_16_08_ok : batch_16_08_values.all id = true := by decide

def batch_16_09_values : List Bool := [accepted_819]
theorem batch_16_09_ok : batch_16_09_values.all id = true := by decide

def batch_16_10_values : List Bool := [accepted_820]
theorem batch_16_10_ok : batch_16_10_values.all id = true := by decide

def batch_16_11_values : List Bool := [accepted_825]
theorem batch_16_11_ok : batch_16_11_values.all id = true := by decide

def batch_16_12_values : List Bool := [accepted_827]
theorem batch_16_12_ok : batch_16_12_values.all id = true := by decide

def batch_16_13_values : List Bool := [accepted_828]
theorem batch_16_13_ok : batch_16_13_values.all id = true := by decide

def batch_16_14_values : List Bool := [accepted_829]
theorem batch_16_14_ok : batch_16_14_values.all id = true := by decide

def batch_16_15_values : List Bool := [accepted_831]
theorem batch_16_15_ok : batch_16_15_values.all id = true := by decide

def batch_16_16_values : List Bool := [accepted_832]
theorem batch_16_16_ok : batch_16_16_values.all id = true := by decide

def batch_16_17_values : List Bool := [accepted_833]
theorem batch_16_17_ok : batch_16_17_values.all id = true := by decide

def batch_16_18_values : List Bool := [accepted_837]
theorem batch_16_18_ok : batch_16_18_values.all id = true := by decide

def batch_16_19_values : List Bool := [accepted_838]
theorem batch_16_19_ok : batch_16_19_values.all id = true := by decide

def batch_16_20_values : List Bool := [accepted_839]
theorem batch_16_20_ok : batch_16_20_values.all id = true := by decide

def batch_16_21_values : List Bool := [accepted_840]
theorem batch_16_21_ok : batch_16_21_values.all id = true := by decide

def batch_16_22_values : List Bool := [accepted_845]
theorem batch_16_22_ok : batch_16_22_values.all id = true := by decide

def batch_16_23_values : List Bool := [accepted_847]
theorem batch_16_23_ok : batch_16_23_values.all id = true := by decide

def batch_16_24_values : List Bool := [accepted_848]
theorem batch_16_24_ok : batch_16_24_values.all id = true := by decide

theorem leaf_801_ok : checkAt 527 1000 box_801 cert_801 = true := by
  have h := List.all_eq_true.mp batch_16_00_ok accepted_801 (by simp [batch_16_00_values])
  exact h
theorem leaf_801_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_801.profileLo box_801.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_801_ok
theorem branch_box_801_nonnegative : ∀ j, 0 ≤ branch_box_801.lower j ∧ 0 ≤ branch_box_801.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_801, Box.profileLo, Box.profileHi, box_801]
theorem leaf_801_BranchSafe : CertificateConsequences.BranchSafe branch_box_801 := by
  left; refine ⟨branch_box_801_nonnegative, ?_⟩
  intro z hz; exact leaf_801_sound hz

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

theorem leaf_809_ok : checkAt 527 1000 box_809 cert_809 = true := by
  have h := List.all_eq_true.mp batch_16_02_ok accepted_809 (by simp [batch_16_02_values])
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

theorem leaf_810_ok : checkAt 527 1000 box_810 cert_810 = true := by
  have h := List.all_eq_true.mp batch_16_03_ok accepted_810 (by simp [batch_16_03_values])
  exact h
theorem leaf_810_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_810.profileLo box_810.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_810_ok
theorem branch_box_810_nonnegative : ∀ j, 0 ≤ branch_box_810.lower j ∧ 0 ≤ branch_box_810.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_810, Box.profileLo, Box.profileHi, box_810]
theorem leaf_810_BranchSafe : CertificateConsequences.BranchSafe branch_box_810 := by
  left; refine ⟨branch_box_810_nonnegative, ?_⟩
  intro z hz; exact leaf_810_sound hz

theorem leaf_811_ok : checkAt 527 1000 box_811 cert_811 = true := by
  have h := List.all_eq_true.mp batch_16_04_ok accepted_811 (by simp [batch_16_04_values])
  exact h
theorem leaf_811_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_811.profileLo box_811.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_811_ok
theorem branch_box_811_nonnegative : ∀ j, 0 ≤ branch_box_811.lower j ∧ 0 ≤ branch_box_811.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_811, Box.profileLo, Box.profileHi, box_811]
theorem leaf_811_BranchSafe : CertificateConsequences.BranchSafe branch_box_811 := by
  left; refine ⟨branch_box_811_nonnegative, ?_⟩
  intro z hz; exact leaf_811_sound hz

theorem leaf_813_ok : checkAt 527 1000 box_813 cert_813 = true := by
  have h := List.all_eq_true.mp batch_16_05_ok accepted_813 (by simp [batch_16_05_values])
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

theorem leaf_815_ok : checkAt 527 1000 box_815 cert_815 = true := by
  have h := List.all_eq_true.mp batch_16_06_ok accepted_815 (by simp [batch_16_06_values])
  exact h
theorem leaf_815_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_815.profileLo box_815.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_815_ok
theorem branch_box_815_nonnegative : ∀ j, 0 ≤ branch_box_815.lower j ∧ 0 ≤ branch_box_815.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_815, Box.profileLo, Box.profileHi, box_815]
theorem leaf_815_BranchSafe : CertificateConsequences.BranchSafe branch_box_815 := by
  left; refine ⟨branch_box_815_nonnegative, ?_⟩
  intro z hz; exact leaf_815_sound hz

theorem leaf_816_ok : checkAt 527 1000 box_816 cert_816 = true := by
  have h := List.all_eq_true.mp batch_16_07_ok accepted_816 (by simp [batch_16_07_values])
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

theorem leaf_817_ok : checkAt 527 1000 box_817 cert_817 = true := by
  have h := List.all_eq_true.mp batch_16_08_ok accepted_817 (by simp [batch_16_08_values])
  exact h
theorem leaf_817_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_817.profileLo box_817.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_817_ok
theorem branch_box_817_nonnegative : ∀ j, 0 ≤ branch_box_817.lower j ∧ 0 ≤ branch_box_817.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_817, Box.profileLo, Box.profileHi, box_817]
theorem leaf_817_BranchSafe : CertificateConsequences.BranchSafe branch_box_817 := by
  left; refine ⟨branch_box_817_nonnegative, ?_⟩
  intro z hz; exact leaf_817_sound hz

theorem leaf_819_ok : checkAt 527 1000 box_819 cert_819 = true := by
  have h := List.all_eq_true.mp batch_16_09_ok accepted_819 (by simp [batch_16_09_values])
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

theorem leaf_820_ok : checkAt 527 1000 box_820 cert_820 = true := by
  have h := List.all_eq_true.mp batch_16_10_ok accepted_820 (by simp [batch_16_10_values])
  exact h
theorem leaf_820_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_820.profileLo box_820.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_820_ok
theorem branch_box_820_nonnegative : ∀ j, 0 ≤ branch_box_820.lower j ∧ 0 ≤ branch_box_820.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_820, Box.profileLo, Box.profileHi, box_820]
theorem leaf_820_BranchSafe : CertificateConsequences.BranchSafe branch_box_820 := by
  left; refine ⟨branch_box_820_nonnegative, ?_⟩
  intro z hz; exact leaf_820_sound hz

theorem leaf_825_ok : checkAt 527 1000 box_825 cert_825 = true := by
  have h := List.all_eq_true.mp batch_16_11_ok accepted_825 (by simp [batch_16_11_values])
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

theorem leaf_827_ok : checkAt 527 1000 box_827 cert_827 = true := by
  have h := List.all_eq_true.mp batch_16_12_ok accepted_827 (by simp [batch_16_12_values])
  exact h
theorem leaf_827_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_827.profileLo box_827.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_827_ok
theorem branch_box_827_nonnegative : ∀ j, 0 ≤ branch_box_827.lower j ∧ 0 ≤ branch_box_827.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_827, Box.profileLo, Box.profileHi, box_827]
theorem leaf_827_BranchSafe : CertificateConsequences.BranchSafe branch_box_827 := by
  left; refine ⟨branch_box_827_nonnegative, ?_⟩
  intro z hz; exact leaf_827_sound hz

theorem leaf_828_ok : checkAt 527 1000 box_828 cert_828 = true := by
  have h := List.all_eq_true.mp batch_16_13_ok accepted_828 (by simp [batch_16_13_values])
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

theorem leaf_829_ok : checkAt 527 1000 box_829 cert_829 = true := by
  have h := List.all_eq_true.mp batch_16_14_ok accepted_829 (by simp [batch_16_14_values])
  exact h
theorem leaf_829_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_829.profileLo box_829.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_829_ok
theorem branch_box_829_nonnegative : ∀ j, 0 ≤ branch_box_829.lower j ∧ 0 ≤ branch_box_829.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_829, Box.profileLo, Box.profileHi, box_829]
theorem leaf_829_BranchSafe : CertificateConsequences.BranchSafe branch_box_829 := by
  left; refine ⟨branch_box_829_nonnegative, ?_⟩
  intro z hz; exact leaf_829_sound hz

theorem leaf_831_ok : checkAt 527 1000 box_831 cert_831 = true := by
  have h := List.all_eq_true.mp batch_16_15_ok accepted_831 (by simp [batch_16_15_values])
  exact h
theorem leaf_831_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_831.profileLo box_831.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_831_ok
theorem branch_box_831_nonnegative : ∀ j, 0 ≤ branch_box_831.lower j ∧ 0 ≤ branch_box_831.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_831, Box.profileLo, Box.profileHi, box_831]
theorem leaf_831_BranchSafe : CertificateConsequences.BranchSafe branch_box_831 := by
  left; refine ⟨branch_box_831_nonnegative, ?_⟩
  intro z hz; exact leaf_831_sound hz

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

theorem leaf_837_ok : checkAt 527 1000 box_837 cert_837 = true := by
  have h := List.all_eq_true.mp batch_16_18_ok accepted_837 (by simp [batch_16_18_values])
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

theorem leaf_838_ok : checkAt 527 1000 box_838 cert_838 = true := by
  have h := List.all_eq_true.mp batch_16_19_ok accepted_838 (by simp [batch_16_19_values])
  exact h
theorem leaf_838_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_838.profileLo box_838.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_838_ok
theorem branch_box_838_nonnegative : ∀ j, 0 ≤ branch_box_838.lower j ∧ 0 ≤ branch_box_838.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_838, Box.profileLo, Box.profileHi, box_838]
theorem leaf_838_BranchSafe : CertificateConsequences.BranchSafe branch_box_838 := by
  left; refine ⟨branch_box_838_nonnegative, ?_⟩
  intro z hz; exact leaf_838_sound hz

theorem leaf_839_ok : checkAt 527 1000 box_839 cert_839 = true := by
  have h := List.all_eq_true.mp batch_16_20_ok accepted_839 (by simp [batch_16_20_values])
  exact h
theorem leaf_839_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_839.profileLo box_839.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_839_ok
theorem branch_box_839_nonnegative : ∀ j, 0 ≤ branch_box_839.lower j ∧ 0 ≤ branch_box_839.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_839, Box.profileLo, Box.profileHi, box_839]
theorem leaf_839_BranchSafe : CertificateConsequences.BranchSafe branch_box_839 := by
  left; refine ⟨branch_box_839_nonnegative, ?_⟩
  intro z hz; exact leaf_839_sound hz

theorem leaf_840_ok : checkAt 527 1000 box_840 cert_840 = true := by
  have h := List.all_eq_true.mp batch_16_21_ok accepted_840 (by simp [batch_16_21_values])
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

theorem leaf_845_ok : checkAt 527 1000 box_845 cert_845 = true := by
  have h := List.all_eq_true.mp batch_16_22_ok accepted_845 (by simp [batch_16_22_values])
  exact h
theorem leaf_845_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_845.profileLo box_845.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_845_ok
theorem branch_box_845_nonnegative : ∀ j, 0 ≤ branch_box_845.lower j ∧ 0 ≤ branch_box_845.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_845, Box.profileLo, Box.profileHi, box_845]
theorem leaf_845_BranchSafe : CertificateConsequences.BranchSafe branch_box_845 := by
  left; refine ⟨branch_box_845_nonnegative, ?_⟩
  intro z hz; exact leaf_845_sound hz

theorem leaf_847_ok : checkAt 527 1000 box_847 cert_847 = true := by
  have h := List.all_eq_true.mp batch_16_23_ok accepted_847 (by simp [batch_16_23_values])
  exact h
theorem leaf_847_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_847.profileLo box_847.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_847_ok
theorem branch_box_847_nonnegative : ∀ j, 0 ≤ branch_box_847.lower j ∧ 0 ≤ branch_box_847.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_847, Box.profileLo, Box.profileHi, box_847]
theorem leaf_847_BranchSafe : CertificateConsequences.BranchSafe branch_box_847 := by
  left; refine ⟨branch_box_847_nonnegative, ?_⟩
  intro z hz; exact leaf_847_sound hz

theorem leaf_848_ok : checkAt 527 1000 box_848 cert_848 = true := by
  have h := List.all_eq_true.mp batch_16_24_ok accepted_848 (by simp [batch_16_24_values])
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
#print axioms leaf_801_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
