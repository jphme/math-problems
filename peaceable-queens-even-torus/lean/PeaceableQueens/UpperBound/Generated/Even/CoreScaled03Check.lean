import PeaceableQueens.UpperBound.Generated.Even.CoreScaled03Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_03_00_values : List Bool := [accepted_150]
theorem batch_03_00_ok : batch_03_00_values.all id = true := by decide

def batch_03_01_values : List Bool := [accepted_152]
theorem batch_03_01_ok : batch_03_01_values.all id = true := by decide

def batch_03_02_values : List Bool := [accepted_153]
theorem batch_03_02_ok : batch_03_02_values.all id = true := by decide

def batch_03_03_values : List Bool := [accepted_155]
theorem batch_03_03_ok : batch_03_03_values.all id = true := by decide

def batch_03_04_values : List Bool := [accepted_159]
theorem batch_03_04_ok : batch_03_04_values.all id = true := by decide

def batch_03_05_values : List Bool := [accepted_165]
theorem batch_03_05_ok : batch_03_05_values.all id = true := by decide

def batch_03_06_values : List Bool := [accepted_167]
theorem batch_03_06_ok : batch_03_06_values.all id = true := by decide

def batch_03_07_values : List Bool := [accepted_169]
theorem batch_03_07_ok : batch_03_07_values.all id = true := by decide

def batch_03_08_values : List Bool := [accepted_176]
theorem batch_03_08_ok : batch_03_08_values.all id = true := by decide

def batch_03_09_values : List Bool := [accepted_178]
theorem batch_03_09_ok : batch_03_09_values.all id = true := by decide

def batch_03_10_values : List Bool := [accepted_179]
theorem batch_03_10_ok : batch_03_10_values.all id = true := by decide

def batch_03_11_values : List Bool := [accepted_181]
theorem batch_03_11_ok : batch_03_11_values.all id = true := by decide

def batch_03_12_values : List Bool := [accepted_183]
theorem batch_03_12_ok : batch_03_12_values.all id = true := by decide

def batch_03_13_values : List Bool := [accepted_186]
theorem batch_03_13_ok : batch_03_13_values.all id = true := by decide

def batch_03_14_values : List Bool := [accepted_188]
theorem batch_03_14_ok : batch_03_14_values.all id = true := by decide

def batch_03_15_values : List Bool := [accepted_190]
theorem batch_03_15_ok : batch_03_15_values.all id = true := by decide

def batch_03_16_values : List Bool := [accepted_192]
theorem batch_03_16_ok : batch_03_16_values.all id = true := by decide

def batch_03_17_values : List Bool := [accepted_194]
theorem batch_03_17_ok : batch_03_17_values.all id = true := by decide

def batch_03_18_values : List Bool := [accepted_195]
theorem batch_03_18_ok : batch_03_18_values.all id = true := by decide

def batch_03_19_values : List Bool := [accepted_197]
theorem batch_03_19_ok : batch_03_19_values.all id = true := by decide

def batch_03_20_values : List Bool := [accepted_199]
theorem batch_03_20_ok : batch_03_20_values.all id = true := by decide

theorem leaf_150_ok : checkAt 527 1000 box_150 cert_150 = true := by
  have h := List.all_eq_true.mp batch_03_00_ok accepted_150 (by simp [batch_03_00_values])
  exact h
theorem leaf_150_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_150.profileLo box_150.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_150_ok
theorem branch_box_150_nonnegative : ∀ j, 0 ≤ branch_box_150.lower j ∧ 0 ≤ branch_box_150.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_150, Box.profileLo, Box.profileHi, box_150]
theorem leaf_150_BranchSafe : CertificateConsequences.BranchSafe branch_box_150 := by
  left; refine ⟨branch_box_150_nonnegative, ?_⟩
  intro z hz; exact leaf_150_sound hz

theorem leaf_152_ok : checkAt 527 1000 box_152 cert_152 = true := by
  have h := List.all_eq_true.mp batch_03_01_ok accepted_152 (by simp [batch_03_01_values])
  exact h
theorem leaf_152_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_152.profileLo box_152.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_152_ok
theorem branch_box_152_nonnegative : ∀ j, 0 ≤ branch_box_152.lower j ∧ 0 ≤ branch_box_152.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_152, Box.profileLo, Box.profileHi, box_152]
theorem leaf_152_BranchSafe : CertificateConsequences.BranchSafe branch_box_152 := by
  left; refine ⟨branch_box_152_nonnegative, ?_⟩
  intro z hz; exact leaf_152_sound hz

theorem leaf_153_ok : checkAt 527 1000 box_153 cert_153 = true := by
  have h := List.all_eq_true.mp batch_03_02_ok accepted_153 (by simp [batch_03_02_values])
  exact h
theorem leaf_153_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_153.profileLo box_153.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_153_ok
theorem branch_box_153_nonnegative : ∀ j, 0 ≤ branch_box_153.lower j ∧ 0 ≤ branch_box_153.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_153, Box.profileLo, Box.profileHi, box_153]
theorem leaf_153_BranchSafe : CertificateConsequences.BranchSafe branch_box_153 := by
  left; refine ⟨branch_box_153_nonnegative, ?_⟩
  intro z hz; exact leaf_153_sound hz

theorem leaf_155_ok : checkAt 527 1000 box_155 cert_155 = true := by
  have h := List.all_eq_true.mp batch_03_03_ok accepted_155 (by simp [batch_03_03_values])
  exact h
theorem leaf_155_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_155.profileLo box_155.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_155_ok
theorem branch_box_155_nonnegative : ∀ j, 0 ≤ branch_box_155.lower j ∧ 0 ≤ branch_box_155.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_155, Box.profileLo, Box.profileHi, box_155]
theorem leaf_155_BranchSafe : CertificateConsequences.BranchSafe branch_box_155 := by
  left; refine ⟨branch_box_155_nonnegative, ?_⟩
  intro z hz; exact leaf_155_sound hz

theorem leaf_159_ok : checkAt 527 1000 box_159 cert_159 = true := by
  have h := List.all_eq_true.mp batch_03_04_ok accepted_159 (by simp [batch_03_04_values])
  exact h
theorem leaf_159_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_159.profileLo box_159.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_159_ok
theorem branch_box_159_nonnegative : ∀ j, 0 ≤ branch_box_159.lower j ∧ 0 ≤ branch_box_159.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_159, Box.profileLo, Box.profileHi, box_159]
theorem leaf_159_BranchSafe : CertificateConsequences.BranchSafe branch_box_159 := by
  left; refine ⟨branch_box_159_nonnegative, ?_⟩
  intro z hz; exact leaf_159_sound hz

theorem leaf_165_ok : checkAt 527 1000 box_165 cert_165 = true := by
  have h := List.all_eq_true.mp batch_03_05_ok accepted_165 (by simp [batch_03_05_values])
  exact h
theorem leaf_165_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_165.profileLo box_165.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_165_ok
theorem branch_box_165_nonnegative : ∀ j, 0 ≤ branch_box_165.lower j ∧ 0 ≤ branch_box_165.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_165, Box.profileLo, Box.profileHi, box_165]
theorem leaf_165_BranchSafe : CertificateConsequences.BranchSafe branch_box_165 := by
  left; refine ⟨branch_box_165_nonnegative, ?_⟩
  intro z hz; exact leaf_165_sound hz

theorem leaf_167_ok : checkAt 527 1000 box_167 cert_167 = true := by
  have h := List.all_eq_true.mp batch_03_06_ok accepted_167 (by simp [batch_03_06_values])
  exact h
theorem leaf_167_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_167.profileLo box_167.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_167_ok
theorem branch_box_167_nonnegative : ∀ j, 0 ≤ branch_box_167.lower j ∧ 0 ≤ branch_box_167.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_167, Box.profileLo, Box.profileHi, box_167]
theorem leaf_167_BranchSafe : CertificateConsequences.BranchSafe branch_box_167 := by
  left; refine ⟨branch_box_167_nonnegative, ?_⟩
  intro z hz; exact leaf_167_sound hz

theorem leaf_169_ok : checkAt 527 1000 box_169 cert_169 = true := by
  have h := List.all_eq_true.mp batch_03_07_ok accepted_169 (by simp [batch_03_07_values])
  exact h
theorem leaf_169_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_169.profileLo box_169.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_169_ok
theorem branch_box_169_nonnegative : ∀ j, 0 ≤ branch_box_169.lower j ∧ 0 ≤ branch_box_169.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_169, Box.profileLo, Box.profileHi, box_169]
theorem leaf_169_BranchSafe : CertificateConsequences.BranchSafe branch_box_169 := by
  left; refine ⟨branch_box_169_nonnegative, ?_⟩
  intro z hz; exact leaf_169_sound hz

theorem leaf_176_ok : checkAt 527 1000 box_176 cert_176 = true := by
  have h := List.all_eq_true.mp batch_03_08_ok accepted_176 (by simp [batch_03_08_values])
  exact h
theorem leaf_176_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_176.profileLo box_176.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_176_ok
theorem branch_box_176_nonnegative : ∀ j, 0 ≤ branch_box_176.lower j ∧ 0 ≤ branch_box_176.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_176, Box.profileLo, Box.profileHi, box_176]
theorem leaf_176_BranchSafe : CertificateConsequences.BranchSafe branch_box_176 := by
  left; refine ⟨branch_box_176_nonnegative, ?_⟩
  intro z hz; exact leaf_176_sound hz

theorem leaf_178_ok : checkAt 527 1000 box_178 cert_178 = true := by
  have h := List.all_eq_true.mp batch_03_09_ok accepted_178 (by simp [batch_03_09_values])
  exact h
theorem leaf_178_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_178.profileLo box_178.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_178_ok
theorem branch_box_178_nonnegative : ∀ j, 0 ≤ branch_box_178.lower j ∧ 0 ≤ branch_box_178.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_178, Box.profileLo, Box.profileHi, box_178]
theorem leaf_178_BranchSafe : CertificateConsequences.BranchSafe branch_box_178 := by
  left; refine ⟨branch_box_178_nonnegative, ?_⟩
  intro z hz; exact leaf_178_sound hz

theorem leaf_179_ok : checkAt 527 1000 box_179 cert_179 = true := by
  have h := List.all_eq_true.mp batch_03_10_ok accepted_179 (by simp [batch_03_10_values])
  exact h
theorem leaf_179_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_179.profileLo box_179.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_179_ok
theorem branch_box_179_nonnegative : ∀ j, 0 ≤ branch_box_179.lower j ∧ 0 ≤ branch_box_179.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_179, Box.profileLo, Box.profileHi, box_179]
theorem leaf_179_BranchSafe : CertificateConsequences.BranchSafe branch_box_179 := by
  left; refine ⟨branch_box_179_nonnegative, ?_⟩
  intro z hz; exact leaf_179_sound hz

theorem leaf_181_ok : checkAt 527 1000 box_181 cert_181 = true := by
  have h := List.all_eq_true.mp batch_03_11_ok accepted_181 (by simp [batch_03_11_values])
  exact h
theorem leaf_181_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_181.profileLo box_181.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_181_ok
theorem branch_box_181_nonnegative : ∀ j, 0 ≤ branch_box_181.lower j ∧ 0 ≤ branch_box_181.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_181, Box.profileLo, Box.profileHi, box_181]
theorem leaf_181_BranchSafe : CertificateConsequences.BranchSafe branch_box_181 := by
  left; refine ⟨branch_box_181_nonnegative, ?_⟩
  intro z hz; exact leaf_181_sound hz

theorem leaf_183_ok : checkAt 527 1000 box_183 cert_183 = true := by
  have h := List.all_eq_true.mp batch_03_12_ok accepted_183 (by simp [batch_03_12_values])
  exact h
theorem leaf_183_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_183.profileLo box_183.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_183_ok
theorem branch_box_183_nonnegative : ∀ j, 0 ≤ branch_box_183.lower j ∧ 0 ≤ branch_box_183.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_183, Box.profileLo, Box.profileHi, box_183]
theorem leaf_183_BranchSafe : CertificateConsequences.BranchSafe branch_box_183 := by
  left; refine ⟨branch_box_183_nonnegative, ?_⟩
  intro z hz; exact leaf_183_sound hz

theorem leaf_186_ok : checkAt 527 1000 box_186 cert_186 = true := by
  have h := List.all_eq_true.mp batch_03_13_ok accepted_186 (by simp [batch_03_13_values])
  exact h
theorem leaf_186_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_186.profileLo box_186.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_186_ok
theorem branch_box_186_nonnegative : ∀ j, 0 ≤ branch_box_186.lower j ∧ 0 ≤ branch_box_186.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_186, Box.profileLo, Box.profileHi, box_186]
theorem leaf_186_BranchSafe : CertificateConsequences.BranchSafe branch_box_186 := by
  left; refine ⟨branch_box_186_nonnegative, ?_⟩
  intro z hz; exact leaf_186_sound hz

theorem leaf_188_ok : checkAt 527 1000 box_188 cert_188 = true := by
  have h := List.all_eq_true.mp batch_03_14_ok accepted_188 (by simp [batch_03_14_values])
  exact h
theorem leaf_188_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_188.profileLo box_188.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_188_ok
theorem branch_box_188_nonnegative : ∀ j, 0 ≤ branch_box_188.lower j ∧ 0 ≤ branch_box_188.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_188, Box.profileLo, Box.profileHi, box_188]
theorem leaf_188_BranchSafe : CertificateConsequences.BranchSafe branch_box_188 := by
  left; refine ⟨branch_box_188_nonnegative, ?_⟩
  intro z hz; exact leaf_188_sound hz

theorem leaf_190_ok : checkAt 527 1000 box_190 cert_190 = true := by
  have h := List.all_eq_true.mp batch_03_15_ok accepted_190 (by simp [batch_03_15_values])
  exact h
theorem leaf_190_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_190.profileLo box_190.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_190_ok
theorem branch_box_190_nonnegative : ∀ j, 0 ≤ branch_box_190.lower j ∧ 0 ≤ branch_box_190.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_190, Box.profileLo, Box.profileHi, box_190]
theorem leaf_190_BranchSafe : CertificateConsequences.BranchSafe branch_box_190 := by
  left; refine ⟨branch_box_190_nonnegative, ?_⟩
  intro z hz; exact leaf_190_sound hz

theorem leaf_192_ok : checkAt 527 1000 box_192 cert_192 = true := by
  have h := List.all_eq_true.mp batch_03_16_ok accepted_192 (by simp [batch_03_16_values])
  exact h
theorem leaf_192_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_192.profileLo box_192.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_192_ok
theorem branch_box_192_nonnegative : ∀ j, 0 ≤ branch_box_192.lower j ∧ 0 ≤ branch_box_192.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_192, Box.profileLo, Box.profileHi, box_192]
theorem leaf_192_BranchSafe : CertificateConsequences.BranchSafe branch_box_192 := by
  left; refine ⟨branch_box_192_nonnegative, ?_⟩
  intro z hz; exact leaf_192_sound hz

theorem leaf_194_ok : checkAt 527 1000 box_194 cert_194 = true := by
  have h := List.all_eq_true.mp batch_03_17_ok accepted_194 (by simp [batch_03_17_values])
  exact h
theorem leaf_194_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_194.profileLo box_194.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_194_ok
theorem branch_box_194_nonnegative : ∀ j, 0 ≤ branch_box_194.lower j ∧ 0 ≤ branch_box_194.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_194, Box.profileLo, Box.profileHi, box_194]
theorem leaf_194_BranchSafe : CertificateConsequences.BranchSafe branch_box_194 := by
  left; refine ⟨branch_box_194_nonnegative, ?_⟩
  intro z hz; exact leaf_194_sound hz

theorem leaf_195_ok : checkAt 527 1000 box_195 cert_195 = true := by
  have h := List.all_eq_true.mp batch_03_18_ok accepted_195 (by simp [batch_03_18_values])
  exact h
theorem leaf_195_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_195.profileLo box_195.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_195_ok
theorem branch_box_195_nonnegative : ∀ j, 0 ≤ branch_box_195.lower j ∧ 0 ≤ branch_box_195.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_195, Box.profileLo, Box.profileHi, box_195]
theorem leaf_195_BranchSafe : CertificateConsequences.BranchSafe branch_box_195 := by
  left; refine ⟨branch_box_195_nonnegative, ?_⟩
  intro z hz; exact leaf_195_sound hz

theorem leaf_197_ok : checkAt 527 1000 box_197 cert_197 = true := by
  have h := List.all_eq_true.mp batch_03_19_ok accepted_197 (by simp [batch_03_19_values])
  exact h
theorem leaf_197_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_197.profileLo box_197.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_197_ok
theorem branch_box_197_nonnegative : ∀ j, 0 ≤ branch_box_197.lower j ∧ 0 ≤ branch_box_197.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_197, Box.profileLo, Box.profileHi, box_197]
theorem leaf_197_BranchSafe : CertificateConsequences.BranchSafe branch_box_197 := by
  left; refine ⟨branch_box_197_nonnegative, ?_⟩
  intro z hz; exact leaf_197_sound hz

theorem leaf_199_ok : checkAt 527 1000 box_199 cert_199 = true := by
  have h := List.all_eq_true.mp batch_03_20_ok accepted_199 (by simp [batch_03_20_values])
  exact h
theorem leaf_199_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_199.profileLo box_199.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_199_ok
theorem branch_box_199_nonnegative : ∀ j, 0 ≤ branch_box_199.lower j ∧ 0 ≤ branch_box_199.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_199, Box.profileLo, Box.profileHi, box_199]
theorem leaf_199_BranchSafe : CertificateConsequences.BranchSafe branch_box_199 := by
  left; refine ⟨branch_box_199_nonnegative, ?_⟩
  intro z hz; exact leaf_199_sound hz

#print axioms batch_03_00_ok
#print axioms leaf_150_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
