import PeaceableQueens.UpperBound.Generated.Even.CoreScaled02Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_02_00_values : List Bool := [accepted_103]
theorem batch_02_00_ok : batch_02_00_values.all id = true := by decide

def batch_02_01_values : List Bool := [accepted_105]
theorem batch_02_01_ok : batch_02_01_values.all id = true := by decide

def batch_02_02_values : List Bool := [accepted_107]
theorem batch_02_02_ok : batch_02_02_values.all id = true := by decide

def batch_02_03_values : List Bool := [accepted_109]
theorem batch_02_03_ok : batch_02_03_values.all id = true := by decide

def batch_02_04_values : List Bool := [accepted_111]
theorem batch_02_04_ok : batch_02_04_values.all id = true := by decide

def batch_02_05_values : List Bool := [accepted_113]
theorem batch_02_05_ok : batch_02_05_values.all id = true := by decide

def batch_02_06_values : List Bool := [accepted_116]
theorem batch_02_06_ok : batch_02_06_values.all id = true := by decide

def batch_02_07_values : List Bool := [accepted_125]
theorem batch_02_07_ok : batch_02_07_values.all id = true := by decide

def batch_02_08_values : List Bool := [accepted_127]
theorem batch_02_08_ok : batch_02_08_values.all id = true := by decide

def batch_02_09_values : List Bool := [accepted_129]
theorem batch_02_09_ok : batch_02_09_values.all id = true := by decide

def batch_02_10_values : List Bool := [accepted_131]
theorem batch_02_10_ok : batch_02_10_values.all id = true := by decide

def batch_02_11_values : List Bool := [accepted_137]
theorem batch_02_11_ok : batch_02_11_values.all id = true := by decide

def batch_02_12_values : List Bool := [accepted_141]
theorem batch_02_12_ok : batch_02_12_values.all id = true := by decide

def batch_02_13_values : List Bool := [accepted_144]
theorem batch_02_13_ok : batch_02_13_values.all id = true := by decide

theorem leaf_103_ok : checkAt 527 1000 box_103 cert_103 = true := by
  have h := List.all_eq_true.mp batch_02_00_ok accepted_103 (by simp [batch_02_00_values])
  exact h
theorem leaf_103_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_103.profileLo box_103.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_103_ok
theorem branch_box_103_nonnegative : ∀ j, 0 ≤ branch_box_103.lower j ∧ 0 ≤ branch_box_103.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_103, Box.profileLo, Box.profileHi, box_103]
theorem leaf_103_BranchSafe : CertificateConsequences.BranchSafe branch_box_103 := by
  left; refine ⟨branch_box_103_nonnegative, ?_⟩
  intro z hz; exact leaf_103_sound hz

theorem leaf_105_ok : checkAt 527 1000 box_105 cert_105 = true := by
  have h := List.all_eq_true.mp batch_02_01_ok accepted_105 (by simp [batch_02_01_values])
  exact h
theorem leaf_105_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_105.profileLo box_105.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_105_ok
theorem branch_box_105_nonnegative : ∀ j, 0 ≤ branch_box_105.lower j ∧ 0 ≤ branch_box_105.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_105, Box.profileLo, Box.profileHi, box_105]
theorem leaf_105_BranchSafe : CertificateConsequences.BranchSafe branch_box_105 := by
  left; refine ⟨branch_box_105_nonnegative, ?_⟩
  intro z hz; exact leaf_105_sound hz

theorem leaf_107_ok : checkAt 527 1000 box_107 cert_107 = true := by
  have h := List.all_eq_true.mp batch_02_02_ok accepted_107 (by simp [batch_02_02_values])
  exact h
theorem leaf_107_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_107.profileLo box_107.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_107_ok
theorem branch_box_107_nonnegative : ∀ j, 0 ≤ branch_box_107.lower j ∧ 0 ≤ branch_box_107.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_107, Box.profileLo, Box.profileHi, box_107]
theorem leaf_107_BranchSafe : CertificateConsequences.BranchSafe branch_box_107 := by
  left; refine ⟨branch_box_107_nonnegative, ?_⟩
  intro z hz; exact leaf_107_sound hz

theorem leaf_109_ok : checkAt 527 1000 box_109 cert_109 = true := by
  have h := List.all_eq_true.mp batch_02_03_ok accepted_109 (by simp [batch_02_03_values])
  exact h
theorem leaf_109_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_109.profileLo box_109.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_109_ok
theorem branch_box_109_nonnegative : ∀ j, 0 ≤ branch_box_109.lower j ∧ 0 ≤ branch_box_109.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_109, Box.profileLo, Box.profileHi, box_109]
theorem leaf_109_BranchSafe : CertificateConsequences.BranchSafe branch_box_109 := by
  left; refine ⟨branch_box_109_nonnegative, ?_⟩
  intro z hz; exact leaf_109_sound hz

theorem leaf_111_ok : checkAt 527 1000 box_111 cert_111 = true := by
  have h := List.all_eq_true.mp batch_02_04_ok accepted_111 (by simp [batch_02_04_values])
  exact h
theorem leaf_111_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_111.profileLo box_111.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_111_ok
theorem branch_box_111_nonnegative : ∀ j, 0 ≤ branch_box_111.lower j ∧ 0 ≤ branch_box_111.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_111, Box.profileLo, Box.profileHi, box_111]
theorem leaf_111_BranchSafe : CertificateConsequences.BranchSafe branch_box_111 := by
  left; refine ⟨branch_box_111_nonnegative, ?_⟩
  intro z hz; exact leaf_111_sound hz

theorem leaf_113_ok : checkAt 527 1000 box_113 cert_113 = true := by
  have h := List.all_eq_true.mp batch_02_05_ok accepted_113 (by simp [batch_02_05_values])
  exact h
theorem leaf_113_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_113.profileLo box_113.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_113_ok
theorem branch_box_113_nonnegative : ∀ j, 0 ≤ branch_box_113.lower j ∧ 0 ≤ branch_box_113.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_113, Box.profileLo, Box.profileHi, box_113]
theorem leaf_113_BranchSafe : CertificateConsequences.BranchSafe branch_box_113 := by
  left; refine ⟨branch_box_113_nonnegative, ?_⟩
  intro z hz; exact leaf_113_sound hz

theorem leaf_116_ok : checkAt 527 1000 box_116 cert_116 = true := by
  have h := List.all_eq_true.mp batch_02_06_ok accepted_116 (by simp [batch_02_06_values])
  exact h
theorem leaf_116_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_116.profileLo box_116.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_116_ok
theorem branch_box_116_nonnegative : ∀ j, 0 ≤ branch_box_116.lower j ∧ 0 ≤ branch_box_116.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_116, Box.profileLo, Box.profileHi, box_116]
theorem leaf_116_BranchSafe : CertificateConsequences.BranchSafe branch_box_116 := by
  left; refine ⟨branch_box_116_nonnegative, ?_⟩
  intro z hz; exact leaf_116_sound hz

theorem leaf_125_ok : checkAt 527 1000 box_125 cert_125 = true := by
  have h := List.all_eq_true.mp batch_02_07_ok accepted_125 (by simp [batch_02_07_values])
  exact h
theorem leaf_125_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_125.profileLo box_125.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_125_ok
theorem branch_box_125_nonnegative : ∀ j, 0 ≤ branch_box_125.lower j ∧ 0 ≤ branch_box_125.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_125, Box.profileLo, Box.profileHi, box_125]
theorem leaf_125_BranchSafe : CertificateConsequences.BranchSafe branch_box_125 := by
  left; refine ⟨branch_box_125_nonnegative, ?_⟩
  intro z hz; exact leaf_125_sound hz

theorem leaf_127_ok : checkAt 527 1000 box_127 cert_127 = true := by
  have h := List.all_eq_true.mp batch_02_08_ok accepted_127 (by simp [batch_02_08_values])
  exact h
theorem leaf_127_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_127.profileLo box_127.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_127_ok
theorem branch_box_127_nonnegative : ∀ j, 0 ≤ branch_box_127.lower j ∧ 0 ≤ branch_box_127.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_127, Box.profileLo, Box.profileHi, box_127]
theorem leaf_127_BranchSafe : CertificateConsequences.BranchSafe branch_box_127 := by
  left; refine ⟨branch_box_127_nonnegative, ?_⟩
  intro z hz; exact leaf_127_sound hz

theorem leaf_129_ok : checkAt 527 1000 box_129 cert_129 = true := by
  have h := List.all_eq_true.mp batch_02_09_ok accepted_129 (by simp [batch_02_09_values])
  exact h
theorem leaf_129_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_129.profileLo box_129.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_129_ok
theorem branch_box_129_nonnegative : ∀ j, 0 ≤ branch_box_129.lower j ∧ 0 ≤ branch_box_129.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_129, Box.profileLo, Box.profileHi, box_129]
theorem leaf_129_BranchSafe : CertificateConsequences.BranchSafe branch_box_129 := by
  left; refine ⟨branch_box_129_nonnegative, ?_⟩
  intro z hz; exact leaf_129_sound hz

theorem leaf_131_ok : checkAt 527 1000 box_131 cert_131 = true := by
  have h := List.all_eq_true.mp batch_02_10_ok accepted_131 (by simp [batch_02_10_values])
  exact h
theorem leaf_131_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_131.profileLo box_131.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_131_ok
theorem branch_box_131_nonnegative : ∀ j, 0 ≤ branch_box_131.lower j ∧ 0 ≤ branch_box_131.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_131, Box.profileLo, Box.profileHi, box_131]
theorem leaf_131_BranchSafe : CertificateConsequences.BranchSafe branch_box_131 := by
  left; refine ⟨branch_box_131_nonnegative, ?_⟩
  intro z hz; exact leaf_131_sound hz

theorem leaf_137_ok : checkAt 527 1000 box_137 cert_137 = true := by
  have h := List.all_eq_true.mp batch_02_11_ok accepted_137 (by simp [batch_02_11_values])
  exact h
theorem leaf_137_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_137.profileLo box_137.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_137_ok
theorem branch_box_137_nonnegative : ∀ j, 0 ≤ branch_box_137.lower j ∧ 0 ≤ branch_box_137.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_137, Box.profileLo, Box.profileHi, box_137]
theorem leaf_137_BranchSafe : CertificateConsequences.BranchSafe branch_box_137 := by
  left; refine ⟨branch_box_137_nonnegative, ?_⟩
  intro z hz; exact leaf_137_sound hz

theorem leaf_141_ok : checkAt 527 1000 box_141 cert_141 = true := by
  have h := List.all_eq_true.mp batch_02_12_ok accepted_141 (by simp [batch_02_12_values])
  exact h
theorem leaf_141_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_141.profileLo box_141.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_141_ok
theorem branch_box_141_nonnegative : ∀ j, 0 ≤ branch_box_141.lower j ∧ 0 ≤ branch_box_141.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_141, Box.profileLo, Box.profileHi, box_141]
theorem leaf_141_BranchSafe : CertificateConsequences.BranchSafe branch_box_141 := by
  left; refine ⟨branch_box_141_nonnegative, ?_⟩
  intro z hz; exact leaf_141_sound hz

theorem leaf_144_ok : checkAt 527 1000 box_144 cert_144 = true := by
  have h := List.all_eq_true.mp batch_02_13_ok accepted_144 (by simp [batch_02_13_values])
  exact h
theorem leaf_144_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_144.profileLo box_144.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_144_ok
theorem branch_box_144_nonnegative : ∀ j, 0 ≤ branch_box_144.lower j ∧ 0 ≤ branch_box_144.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_144, Box.profileLo, Box.profileHi, box_144]
theorem leaf_144_BranchSafe : CertificateConsequences.BranchSafe branch_box_144 := by
  left; refine ⟨branch_box_144_nonnegative, ?_⟩
  intro z hz; exact leaf_144_sound hz

#print axioms batch_02_00_ok
#print axioms leaf_103_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
