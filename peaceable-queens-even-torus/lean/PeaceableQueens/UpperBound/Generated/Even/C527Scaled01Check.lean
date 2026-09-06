import PeaceableQueens.UpperBound.Generated.Even.C527Scaled01Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_01_00_values : List Bool := [accepted_51]
theorem batch_01_00_ok : batch_01_00_values.all id = true := by decide

def batch_01_01_values : List Bool := [accepted_53]
theorem batch_01_01_ok : batch_01_01_values.all id = true := by decide

def batch_01_02_values : List Bool := [accepted_55]
theorem batch_01_02_ok : batch_01_02_values.all id = true := by decide

def batch_01_03_values : List Bool := [accepted_60]
theorem batch_01_03_ok : batch_01_03_values.all id = true := by decide

def batch_01_04_values : List Bool := [accepted_61]
theorem batch_01_04_ok : batch_01_04_values.all id = true := by decide

def batch_01_05_values : List Bool := [accepted_62]
theorem batch_01_05_ok : batch_01_05_values.all id = true := by decide

def batch_01_06_values : List Bool := [accepted_63]
theorem batch_01_06_ok : batch_01_06_values.all id = true := by decide

def batch_01_07_values : List Bool := [accepted_65]
theorem batch_01_07_ok : batch_01_07_values.all id = true := by decide

def batch_01_08_values : List Bool := [accepted_66]
theorem batch_01_08_ok : batch_01_08_values.all id = true := by decide

def batch_01_09_values : List Bool := [accepted_67]
theorem batch_01_09_ok : batch_01_09_values.all id = true := by decide

def batch_01_10_values : List Bool := [accepted_69]
theorem batch_01_10_ok : batch_01_10_values.all id = true := by decide

def batch_01_11_values : List Bool := [accepted_71]
theorem batch_01_11_ok : batch_01_11_values.all id = true := by decide

def batch_01_12_values : List Bool := [accepted_73]
theorem batch_01_12_ok : batch_01_12_values.all id = true := by decide

def batch_01_13_values : List Bool := [accepted_74]
theorem batch_01_13_ok : batch_01_13_values.all id = true := by decide

def batch_01_14_values : List Bool := [accepted_82]
theorem batch_01_14_ok : batch_01_14_values.all id = true := by decide

def batch_01_15_values : List Bool := [accepted_83]
theorem batch_01_15_ok : batch_01_15_values.all id = true := by decide

def batch_01_16_values : List Bool := [accepted_84]
theorem batch_01_16_ok : batch_01_16_values.all id = true := by decide

def batch_01_17_values : List Bool := [accepted_85]
theorem batch_01_17_ok : batch_01_17_values.all id = true := by decide

def batch_01_18_values : List Bool := [accepted_86]
theorem batch_01_18_ok : batch_01_18_values.all id = true := by decide

def batch_01_19_values : List Bool := [accepted_89]
theorem batch_01_19_ok : batch_01_19_values.all id = true := by decide

def batch_01_20_values : List Bool := [accepted_90]
theorem batch_01_20_ok : batch_01_20_values.all id = true := by decide

def batch_01_21_values : List Bool := [accepted_91]
theorem batch_01_21_ok : batch_01_21_values.all id = true := by decide

def batch_01_22_values : List Bool := [accepted_93]
theorem batch_01_22_ok : batch_01_22_values.all id = true := by decide

def batch_01_23_values : List Bool := [accepted_97]
theorem batch_01_23_ok : batch_01_23_values.all id = true := by decide

def batch_01_24_values : List Bool := [accepted_99]
theorem batch_01_24_ok : batch_01_24_values.all id = true := by decide

theorem leaf_51_ok : checkAt 527 1000 box_51 cert_51 = true := by
  have h := List.all_eq_true.mp batch_01_00_ok accepted_51 (by simp [batch_01_00_values])
  exact h
theorem leaf_51_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_51.profileLo box_51.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_51_ok
theorem branch_box_51_nonnegative : ∀ j, 0 ≤ branch_box_51.lower j ∧ 0 ≤ branch_box_51.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_51, Box.profileLo, Box.profileHi, box_51]
theorem leaf_51_BranchSafe : CertificateConsequences.BranchSafe branch_box_51 := by
  left; refine ⟨branch_box_51_nonnegative, ?_⟩
  intro z hz; exact leaf_51_sound hz

theorem leaf_53_ok : checkAt 527 1000 box_53 cert_53 = true := by
  have h := List.all_eq_true.mp batch_01_01_ok accepted_53 (by simp [batch_01_01_values])
  exact h
theorem leaf_53_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_53.profileLo box_53.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_53_ok
theorem branch_box_53_nonnegative : ∀ j, 0 ≤ branch_box_53.lower j ∧ 0 ≤ branch_box_53.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_53, Box.profileLo, Box.profileHi, box_53]
theorem leaf_53_BranchSafe : CertificateConsequences.BranchSafe branch_box_53 := by
  left; refine ⟨branch_box_53_nonnegative, ?_⟩
  intro z hz; exact leaf_53_sound hz

theorem leaf_55_ok : checkAt 527 1000 box_55 cert_55 = true := by
  have h := List.all_eq_true.mp batch_01_02_ok accepted_55 (by simp [batch_01_02_values])
  exact h
theorem leaf_55_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_55.profileLo box_55.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_55_ok
theorem branch_box_55_nonnegative : ∀ j, 0 ≤ branch_box_55.lower j ∧ 0 ≤ branch_box_55.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_55, Box.profileLo, Box.profileHi, box_55]
theorem leaf_55_BranchSafe : CertificateConsequences.BranchSafe branch_box_55 := by
  left; refine ⟨branch_box_55_nonnegative, ?_⟩
  intro z hz; exact leaf_55_sound hz

theorem leaf_60_ok : checkAt 527 1000 box_60 cert_60 = true := by
  have h := List.all_eq_true.mp batch_01_03_ok accepted_60 (by simp [batch_01_03_values])
  exact h
theorem leaf_60_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_60.profileLo box_60.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_60_ok
theorem branch_box_60_nonnegative : ∀ j, 0 ≤ branch_box_60.lower j ∧ 0 ≤ branch_box_60.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_60, Box.profileLo, Box.profileHi, box_60]
theorem leaf_60_BranchSafe : CertificateConsequences.BranchSafe branch_box_60 := by
  left; refine ⟨branch_box_60_nonnegative, ?_⟩
  intro z hz; exact leaf_60_sound hz

theorem leaf_61_ok : checkAt 527 1000 box_61 cert_61 = true := by
  have h := List.all_eq_true.mp batch_01_04_ok accepted_61 (by simp [batch_01_04_values])
  exact h
theorem leaf_61_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_61.profileLo box_61.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_61_ok
theorem branch_box_61_nonnegative : ∀ j, 0 ≤ branch_box_61.lower j ∧ 0 ≤ branch_box_61.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_61, Box.profileLo, Box.profileHi, box_61]
theorem leaf_61_BranchSafe : CertificateConsequences.BranchSafe branch_box_61 := by
  left; refine ⟨branch_box_61_nonnegative, ?_⟩
  intro z hz; exact leaf_61_sound hz

theorem leaf_62_ok : checkAt 527 1000 box_62 cert_62 = true := by
  have h := List.all_eq_true.mp batch_01_05_ok accepted_62 (by simp [batch_01_05_values])
  exact h
theorem leaf_62_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_62.profileLo box_62.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_62_ok
theorem branch_box_62_nonnegative : ∀ j, 0 ≤ branch_box_62.lower j ∧ 0 ≤ branch_box_62.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_62, Box.profileLo, Box.profileHi, box_62]
theorem leaf_62_BranchSafe : CertificateConsequences.BranchSafe branch_box_62 := by
  left; refine ⟨branch_box_62_nonnegative, ?_⟩
  intro z hz; exact leaf_62_sound hz

theorem leaf_63_ok : checkAt 527 1000 box_63 cert_63 = true := by
  have h := List.all_eq_true.mp batch_01_06_ok accepted_63 (by simp [batch_01_06_values])
  exact h
theorem leaf_63_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_63.profileLo box_63.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_63_ok
theorem branch_box_63_nonnegative : ∀ j, 0 ≤ branch_box_63.lower j ∧ 0 ≤ branch_box_63.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_63, Box.profileLo, Box.profileHi, box_63]
theorem leaf_63_BranchSafe : CertificateConsequences.BranchSafe branch_box_63 := by
  left; refine ⟨branch_box_63_nonnegative, ?_⟩
  intro z hz; exact leaf_63_sound hz

theorem leaf_65_ok : checkAt 527 1000 box_65 cert_65 = true := by
  have h := List.all_eq_true.mp batch_01_07_ok accepted_65 (by simp [batch_01_07_values])
  exact h
theorem leaf_65_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_65.profileLo box_65.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_65_ok
theorem branch_box_65_nonnegative : ∀ j, 0 ≤ branch_box_65.lower j ∧ 0 ≤ branch_box_65.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_65, Box.profileLo, Box.profileHi, box_65]
theorem leaf_65_BranchSafe : CertificateConsequences.BranchSafe branch_box_65 := by
  left; refine ⟨branch_box_65_nonnegative, ?_⟩
  intro z hz; exact leaf_65_sound hz

theorem leaf_66_ok : checkAt 527 1000 box_66 cert_66 = true := by
  have h := List.all_eq_true.mp batch_01_08_ok accepted_66 (by simp [batch_01_08_values])
  exact h
theorem leaf_66_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_66.profileLo box_66.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_66_ok
theorem branch_box_66_nonnegative : ∀ j, 0 ≤ branch_box_66.lower j ∧ 0 ≤ branch_box_66.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_66, Box.profileLo, Box.profileHi, box_66]
theorem leaf_66_BranchSafe : CertificateConsequences.BranchSafe branch_box_66 := by
  left; refine ⟨branch_box_66_nonnegative, ?_⟩
  intro z hz; exact leaf_66_sound hz

theorem leaf_67_ok : checkAt 527 1000 box_67 cert_67 = true := by
  have h := List.all_eq_true.mp batch_01_09_ok accepted_67 (by simp [batch_01_09_values])
  exact h
theorem leaf_67_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_67.profileLo box_67.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_67_ok
theorem branch_box_67_nonnegative : ∀ j, 0 ≤ branch_box_67.lower j ∧ 0 ≤ branch_box_67.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_67, Box.profileLo, Box.profileHi, box_67]
theorem leaf_67_BranchSafe : CertificateConsequences.BranchSafe branch_box_67 := by
  left; refine ⟨branch_box_67_nonnegative, ?_⟩
  intro z hz; exact leaf_67_sound hz

theorem leaf_69_ok : checkAt 527 1000 box_69 cert_69 = true := by
  have h := List.all_eq_true.mp batch_01_10_ok accepted_69 (by simp [batch_01_10_values])
  exact h
theorem leaf_69_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_69.profileLo box_69.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_69_ok
theorem branch_box_69_nonnegative : ∀ j, 0 ≤ branch_box_69.lower j ∧ 0 ≤ branch_box_69.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_69, Box.profileLo, Box.profileHi, box_69]
theorem leaf_69_BranchSafe : CertificateConsequences.BranchSafe branch_box_69 := by
  left; refine ⟨branch_box_69_nonnegative, ?_⟩
  intro z hz; exact leaf_69_sound hz

theorem leaf_71_ok : checkAt 527 1000 box_71 cert_71 = true := by
  have h := List.all_eq_true.mp batch_01_11_ok accepted_71 (by simp [batch_01_11_values])
  exact h
theorem leaf_71_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_71.profileLo box_71.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_71_ok
theorem branch_box_71_nonnegative : ∀ j, 0 ≤ branch_box_71.lower j ∧ 0 ≤ branch_box_71.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_71, Box.profileLo, Box.profileHi, box_71]
theorem leaf_71_BranchSafe : CertificateConsequences.BranchSafe branch_box_71 := by
  left; refine ⟨branch_box_71_nonnegative, ?_⟩
  intro z hz; exact leaf_71_sound hz

theorem leaf_73_ok : checkAt 527 1000 box_73 cert_73 = true := by
  have h := List.all_eq_true.mp batch_01_12_ok accepted_73 (by simp [batch_01_12_values])
  exact h
theorem leaf_73_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_73.profileLo box_73.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_73_ok
theorem branch_box_73_nonnegative : ∀ j, 0 ≤ branch_box_73.lower j ∧ 0 ≤ branch_box_73.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_73, Box.profileLo, Box.profileHi, box_73]
theorem leaf_73_BranchSafe : CertificateConsequences.BranchSafe branch_box_73 := by
  left; refine ⟨branch_box_73_nonnegative, ?_⟩
  intro z hz; exact leaf_73_sound hz

theorem leaf_74_ok : checkAt 527 1000 box_74 cert_74 = true := by
  have h := List.all_eq_true.mp batch_01_13_ok accepted_74 (by simp [batch_01_13_values])
  exact h
theorem leaf_74_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_74.profileLo box_74.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_74_ok
theorem branch_box_74_nonnegative : ∀ j, 0 ≤ branch_box_74.lower j ∧ 0 ≤ branch_box_74.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_74, Box.profileLo, Box.profileHi, box_74]
theorem leaf_74_BranchSafe : CertificateConsequences.BranchSafe branch_box_74 := by
  left; refine ⟨branch_box_74_nonnegative, ?_⟩
  intro z hz; exact leaf_74_sound hz

theorem leaf_82_ok : checkAt 527 1000 box_82 cert_82 = true := by
  have h := List.all_eq_true.mp batch_01_14_ok accepted_82 (by simp [batch_01_14_values])
  exact h
theorem leaf_82_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_82.profileLo box_82.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_82_ok
theorem branch_box_82_nonnegative : ∀ j, 0 ≤ branch_box_82.lower j ∧ 0 ≤ branch_box_82.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_82, Box.profileLo, Box.profileHi, box_82]
theorem leaf_82_BranchSafe : CertificateConsequences.BranchSafe branch_box_82 := by
  left; refine ⟨branch_box_82_nonnegative, ?_⟩
  intro z hz; exact leaf_82_sound hz

theorem leaf_83_ok : checkAt 527 1000 box_83 cert_83 = true := by
  have h := List.all_eq_true.mp batch_01_15_ok accepted_83 (by simp [batch_01_15_values])
  exact h
theorem leaf_83_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_83.profileLo box_83.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_83_ok
theorem branch_box_83_nonnegative : ∀ j, 0 ≤ branch_box_83.lower j ∧ 0 ≤ branch_box_83.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_83, Box.profileLo, Box.profileHi, box_83]
theorem leaf_83_BranchSafe : CertificateConsequences.BranchSafe branch_box_83 := by
  left; refine ⟨branch_box_83_nonnegative, ?_⟩
  intro z hz; exact leaf_83_sound hz

theorem leaf_84_ok : checkAt 527 1000 box_84 cert_84 = true := by
  have h := List.all_eq_true.mp batch_01_16_ok accepted_84 (by simp [batch_01_16_values])
  exact h
theorem leaf_84_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_84.profileLo box_84.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_84_ok
theorem branch_box_84_nonnegative : ∀ j, 0 ≤ branch_box_84.lower j ∧ 0 ≤ branch_box_84.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_84, Box.profileLo, Box.profileHi, box_84]
theorem leaf_84_BranchSafe : CertificateConsequences.BranchSafe branch_box_84 := by
  left; refine ⟨branch_box_84_nonnegative, ?_⟩
  intro z hz; exact leaf_84_sound hz

theorem leaf_85_ok : checkAt 527 1000 box_85 cert_85 = true := by
  have h := List.all_eq_true.mp batch_01_17_ok accepted_85 (by simp [batch_01_17_values])
  exact h
theorem leaf_85_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_85.profileLo box_85.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_85_ok
theorem branch_box_85_nonnegative : ∀ j, 0 ≤ branch_box_85.lower j ∧ 0 ≤ branch_box_85.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_85, Box.profileLo, Box.profileHi, box_85]
theorem leaf_85_BranchSafe : CertificateConsequences.BranchSafe branch_box_85 := by
  left; refine ⟨branch_box_85_nonnegative, ?_⟩
  intro z hz; exact leaf_85_sound hz

theorem leaf_86_ok : checkAt 527 1000 box_86 cert_86 = true := by
  have h := List.all_eq_true.mp batch_01_18_ok accepted_86 (by simp [batch_01_18_values])
  exact h
theorem leaf_86_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_86.profileLo box_86.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_86_ok
theorem branch_box_86_nonnegative : ∀ j, 0 ≤ branch_box_86.lower j ∧ 0 ≤ branch_box_86.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_86, Box.profileLo, Box.profileHi, box_86]
theorem leaf_86_BranchSafe : CertificateConsequences.BranchSafe branch_box_86 := by
  left; refine ⟨branch_box_86_nonnegative, ?_⟩
  intro z hz; exact leaf_86_sound hz

theorem leaf_89_ok : checkAt 527 1000 box_89 cert_89 = true := by
  have h := List.all_eq_true.mp batch_01_19_ok accepted_89 (by simp [batch_01_19_values])
  exact h
theorem leaf_89_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_89.profileLo box_89.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_89_ok
theorem branch_box_89_nonnegative : ∀ j, 0 ≤ branch_box_89.lower j ∧ 0 ≤ branch_box_89.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_89, Box.profileLo, Box.profileHi, box_89]
theorem leaf_89_BranchSafe : CertificateConsequences.BranchSafe branch_box_89 := by
  left; refine ⟨branch_box_89_nonnegative, ?_⟩
  intro z hz; exact leaf_89_sound hz

theorem leaf_90_ok : checkAt 527 1000 box_90 cert_90 = true := by
  have h := List.all_eq_true.mp batch_01_20_ok accepted_90 (by simp [batch_01_20_values])
  exact h
theorem leaf_90_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_90.profileLo box_90.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_90_ok
theorem branch_box_90_nonnegative : ∀ j, 0 ≤ branch_box_90.lower j ∧ 0 ≤ branch_box_90.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_90, Box.profileLo, Box.profileHi, box_90]
theorem leaf_90_BranchSafe : CertificateConsequences.BranchSafe branch_box_90 := by
  left; refine ⟨branch_box_90_nonnegative, ?_⟩
  intro z hz; exact leaf_90_sound hz

theorem leaf_91_ok : checkAt 527 1000 box_91 cert_91 = true := by
  have h := List.all_eq_true.mp batch_01_21_ok accepted_91 (by simp [batch_01_21_values])
  exact h
theorem leaf_91_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_91.profileLo box_91.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_91_ok
theorem branch_box_91_nonnegative : ∀ j, 0 ≤ branch_box_91.lower j ∧ 0 ≤ branch_box_91.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_91, Box.profileLo, Box.profileHi, box_91]
theorem leaf_91_BranchSafe : CertificateConsequences.BranchSafe branch_box_91 := by
  left; refine ⟨branch_box_91_nonnegative, ?_⟩
  intro z hz; exact leaf_91_sound hz

theorem leaf_93_ok : checkAt 527 1000 box_93 cert_93 = true := by
  have h := List.all_eq_true.mp batch_01_22_ok accepted_93 (by simp [batch_01_22_values])
  exact h
theorem leaf_93_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_93.profileLo box_93.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_93_ok
theorem branch_box_93_nonnegative : ∀ j, 0 ≤ branch_box_93.lower j ∧ 0 ≤ branch_box_93.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_93, Box.profileLo, Box.profileHi, box_93]
theorem leaf_93_BranchSafe : CertificateConsequences.BranchSafe branch_box_93 := by
  left; refine ⟨branch_box_93_nonnegative, ?_⟩
  intro z hz; exact leaf_93_sound hz

theorem leaf_97_ok : checkAt 527 1000 box_97 cert_97 = true := by
  have h := List.all_eq_true.mp batch_01_23_ok accepted_97 (by simp [batch_01_23_values])
  exact h
theorem leaf_97_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_97.profileLo box_97.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_97_ok
theorem branch_box_97_nonnegative : ∀ j, 0 ≤ branch_box_97.lower j ∧ 0 ≤ branch_box_97.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_97, Box.profileLo, Box.profileHi, box_97]
theorem leaf_97_BranchSafe : CertificateConsequences.BranchSafe branch_box_97 := by
  left; refine ⟨branch_box_97_nonnegative, ?_⟩
  intro z hz; exact leaf_97_sound hz

theorem leaf_99_ok : checkAt 527 1000 box_99 cert_99 = true := by
  have h := List.all_eq_true.mp batch_01_24_ok accepted_99 (by simp [batch_01_24_values])
  exact h
theorem leaf_99_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_99.profileLo box_99.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_99_ok
theorem branch_box_99_nonnegative : ∀ j, 0 ≤ branch_box_99.lower j ∧ 0 ≤ branch_box_99.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_99, Box.profileLo, Box.profileHi, box_99]
theorem leaf_99_BranchSafe : CertificateConsequences.BranchSafe branch_box_99 := by
  left; refine ⟨branch_box_99_nonnegative, ?_⟩
  intro z hz; exact leaf_99_sound hz

#print axioms batch_01_00_ok
#print axioms leaf_51_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
