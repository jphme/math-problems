import PeaceableQueens.UpperBound.Generated.Even.CoreScaled01Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
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

def batch_01_03_values : List Bool := [accepted_59]
theorem batch_01_03_ok : batch_01_03_values.all id = true := by decide

def batch_01_04_values : List Bool := [accepted_63]
theorem batch_01_04_ok : batch_01_04_values.all id = true := by decide

def batch_01_05_values : List Bool := [accepted_65]
theorem batch_01_05_ok : batch_01_05_values.all id = true := by decide

def batch_01_06_values : List Bool := [accepted_67]
theorem batch_01_06_ok : batch_01_06_values.all id = true := by decide

def batch_01_07_values : List Bool := [accepted_71]
theorem batch_01_07_ok : batch_01_07_values.all id = true := by decide

def batch_01_08_values : List Bool := [accepted_73]
theorem batch_01_08_ok : batch_01_08_values.all id = true := by decide

def batch_01_09_values : List Bool := [accepted_75]
theorem batch_01_09_ok : batch_01_09_values.all id = true := by decide

def batch_01_10_values : List Bool := [accepted_77]
theorem batch_01_10_ok : batch_01_10_values.all id = true := by decide

def batch_01_11_values : List Bool := [accepted_79]
theorem batch_01_11_ok : batch_01_11_values.all id = true := by decide

def batch_01_12_values : List Bool := [accepted_81]
theorem batch_01_12_ok : batch_01_12_values.all id = true := by decide

def batch_01_13_values : List Bool := [accepted_88]
theorem batch_01_13_ok : batch_01_13_values.all id = true := by decide

def batch_01_14_values : List Bool := [accepted_90]
theorem batch_01_14_ok : batch_01_14_values.all id = true := by decide

def batch_01_15_values : List Bool := [accepted_95]
theorem batch_01_15_ok : batch_01_15_values.all id = true := by decide

def batch_01_16_values : List Bool := [accepted_97]
theorem batch_01_16_ok : batch_01_16_values.all id = true := by decide

def batch_01_17_values : List Bool := [accepted_99]
theorem batch_01_17_ok : batch_01_17_values.all id = true := by decide

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

theorem leaf_59_ok : checkAt 527 1000 box_59 cert_59 = true := by
  have h := List.all_eq_true.mp batch_01_03_ok accepted_59 (by simp [batch_01_03_values])
  exact h
theorem leaf_59_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_59.profileLo box_59.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_59_ok
theorem branch_box_59_nonnegative : ∀ j, 0 ≤ branch_box_59.lower j ∧ 0 ≤ branch_box_59.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_59, Box.profileLo, Box.profileHi, box_59]
theorem leaf_59_BranchSafe : CertificateConsequences.BranchSafe branch_box_59 := by
  left; refine ⟨branch_box_59_nonnegative, ?_⟩
  intro z hz; exact leaf_59_sound hz

theorem leaf_63_ok : checkAt 527 1000 box_63 cert_63 = true := by
  have h := List.all_eq_true.mp batch_01_04_ok accepted_63 (by simp [batch_01_04_values])
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
  have h := List.all_eq_true.mp batch_01_05_ok accepted_65 (by simp [batch_01_05_values])
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

theorem leaf_67_ok : checkAt 527 1000 box_67 cert_67 = true := by
  have h := List.all_eq_true.mp batch_01_06_ok accepted_67 (by simp [batch_01_06_values])
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

theorem leaf_71_ok : checkAt 527 1000 box_71 cert_71 = true := by
  have h := List.all_eq_true.mp batch_01_07_ok accepted_71 (by simp [batch_01_07_values])
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
  have h := List.all_eq_true.mp batch_01_08_ok accepted_73 (by simp [batch_01_08_values])
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

theorem leaf_75_ok : checkAt 527 1000 box_75 cert_75 = true := by
  have h := List.all_eq_true.mp batch_01_09_ok accepted_75 (by simp [batch_01_09_values])
  exact h
theorem leaf_75_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_75.profileLo box_75.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_75_ok
theorem branch_box_75_nonnegative : ∀ j, 0 ≤ branch_box_75.lower j ∧ 0 ≤ branch_box_75.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_75, Box.profileLo, Box.profileHi, box_75]
theorem leaf_75_BranchSafe : CertificateConsequences.BranchSafe branch_box_75 := by
  left; refine ⟨branch_box_75_nonnegative, ?_⟩
  intro z hz; exact leaf_75_sound hz

theorem leaf_77_ok : checkAt 527 1000 box_77 cert_77 = true := by
  have h := List.all_eq_true.mp batch_01_10_ok accepted_77 (by simp [batch_01_10_values])
  exact h
theorem leaf_77_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_77.profileLo box_77.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_77_ok
theorem branch_box_77_nonnegative : ∀ j, 0 ≤ branch_box_77.lower j ∧ 0 ≤ branch_box_77.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_77, Box.profileLo, Box.profileHi, box_77]
theorem leaf_77_BranchSafe : CertificateConsequences.BranchSafe branch_box_77 := by
  left; refine ⟨branch_box_77_nonnegative, ?_⟩
  intro z hz; exact leaf_77_sound hz

theorem leaf_79_ok : checkAt 527 1000 box_79 cert_79 = true := by
  have h := List.all_eq_true.mp batch_01_11_ok accepted_79 (by simp [batch_01_11_values])
  exact h
theorem leaf_79_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_79.profileLo box_79.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_79_ok
theorem branch_box_79_nonnegative : ∀ j, 0 ≤ branch_box_79.lower j ∧ 0 ≤ branch_box_79.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_79, Box.profileLo, Box.profileHi, box_79]
theorem leaf_79_BranchSafe : CertificateConsequences.BranchSafe branch_box_79 := by
  left; refine ⟨branch_box_79_nonnegative, ?_⟩
  intro z hz; exact leaf_79_sound hz

theorem leaf_81_ok : checkAt 527 1000 box_81 cert_81 = true := by
  have h := List.all_eq_true.mp batch_01_12_ok accepted_81 (by simp [batch_01_12_values])
  exact h
theorem leaf_81_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_81.profileLo box_81.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_81_ok
theorem branch_box_81_nonnegative : ∀ j, 0 ≤ branch_box_81.lower j ∧ 0 ≤ branch_box_81.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_81, Box.profileLo, Box.profileHi, box_81]
theorem leaf_81_BranchSafe : CertificateConsequences.BranchSafe branch_box_81 := by
  left; refine ⟨branch_box_81_nonnegative, ?_⟩
  intro z hz; exact leaf_81_sound hz

theorem leaf_88_ok : checkAt 527 1000 box_88 cert_88 = true := by
  have h := List.all_eq_true.mp batch_01_13_ok accepted_88 (by simp [batch_01_13_values])
  exact h
theorem leaf_88_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_88.profileLo box_88.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_88_ok
theorem branch_box_88_nonnegative : ∀ j, 0 ≤ branch_box_88.lower j ∧ 0 ≤ branch_box_88.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_88, Box.profileLo, Box.profileHi, box_88]
theorem leaf_88_BranchSafe : CertificateConsequences.BranchSafe branch_box_88 := by
  left; refine ⟨branch_box_88_nonnegative, ?_⟩
  intro z hz; exact leaf_88_sound hz

theorem leaf_90_ok : checkAt 527 1000 box_90 cert_90 = true := by
  have h := List.all_eq_true.mp batch_01_14_ok accepted_90 (by simp [batch_01_14_values])
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

theorem leaf_95_ok : checkAt 527 1000 box_95 cert_95 = true := by
  have h := List.all_eq_true.mp batch_01_15_ok accepted_95 (by simp [batch_01_15_values])
  exact h
theorem leaf_95_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_95.profileLo box_95.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_95_ok
theorem branch_box_95_nonnegative : ∀ j, 0 ≤ branch_box_95.lower j ∧ 0 ≤ branch_box_95.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_95, Box.profileLo, Box.profileHi, box_95]
theorem leaf_95_BranchSafe : CertificateConsequences.BranchSafe branch_box_95 := by
  left; refine ⟨branch_box_95_nonnegative, ?_⟩
  intro z hz; exact leaf_95_sound hz

theorem leaf_97_ok : checkAt 527 1000 box_97 cert_97 = true := by
  have h := List.all_eq_true.mp batch_01_16_ok accepted_97 (by simp [batch_01_16_values])
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
  have h := List.all_eq_true.mp batch_01_17_ok accepted_99 (by simp [batch_01_17_values])
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
end PeaceableQueens.UpperBound.Generated.Even.Core
