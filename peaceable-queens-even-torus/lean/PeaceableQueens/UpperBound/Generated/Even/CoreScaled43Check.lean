import PeaceableQueens.UpperBound.Generated.Even.CoreScaled43Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_43_00_values : List Bool := [accepted_2151]
theorem batch_43_00_ok : batch_43_00_values.all id = true := by decide

def batch_43_01_values : List Bool := [accepted_2156]
theorem batch_43_01_ok : batch_43_01_values.all id = true := by decide

def batch_43_02_values : List Bool := [accepted_2164]
theorem batch_43_02_ok : batch_43_02_values.all id = true := by decide

def batch_43_03_values : List Bool := [accepted_2166]
theorem batch_43_03_ok : batch_43_03_values.all id = true := by decide

def batch_43_04_values : List Bool := [accepted_2170]
theorem batch_43_04_ok : batch_43_04_values.all id = true := by decide

def batch_43_05_values : List Bool := [accepted_2178]
theorem batch_43_05_ok : batch_43_05_values.all id = true := by decide

def batch_43_06_values : List Bool := [accepted_2180]
theorem batch_43_06_ok : batch_43_06_values.all id = true := by decide

def batch_43_07_values : List Bool := [accepted_2184]
theorem batch_43_07_ok : batch_43_07_values.all id = true := by decide

def batch_43_08_values : List Bool := [accepted_2189]
theorem batch_43_08_ok : batch_43_08_values.all id = true := by decide

def batch_43_09_values : List Bool := [accepted_2196]
theorem batch_43_09_ok : batch_43_09_values.all id = true := by decide

def batch_43_10_values : List Bool := [accepted_2198]
theorem batch_43_10_ok : batch_43_10_values.all id = true := by decide

theorem leaf_2151_ok : checkAt 527 1000 box_2151 cert_2151 = true := by
  have h := List.all_eq_true.mp batch_43_00_ok accepted_2151 (by simp [batch_43_00_values])
  exact h
theorem leaf_2151_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2151.profileLo box_2151.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2151_ok
theorem branch_box_2151_nonnegative : ∀ j, 0 ≤ branch_box_2151.lower j ∧ 0 ≤ branch_box_2151.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2151, Box.profileLo, Box.profileHi, box_2151]
theorem leaf_2151_BranchSafe : CertificateConsequences.BranchSafe branch_box_2151 := by
  left; refine ⟨branch_box_2151_nonnegative, ?_⟩
  intro z hz; exact leaf_2151_sound hz

theorem leaf_2156_ok : checkAt 527 1000 box_2156 cert_2156 = true := by
  have h := List.all_eq_true.mp batch_43_01_ok accepted_2156 (by simp [batch_43_01_values])
  exact h
theorem leaf_2156_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2156.profileLo box_2156.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2156_ok
theorem branch_box_2156_nonnegative : ∀ j, 0 ≤ branch_box_2156.lower j ∧ 0 ≤ branch_box_2156.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2156, Box.profileLo, Box.profileHi, box_2156]
theorem leaf_2156_BranchSafe : CertificateConsequences.BranchSafe branch_box_2156 := by
  left; refine ⟨branch_box_2156_nonnegative, ?_⟩
  intro z hz; exact leaf_2156_sound hz

theorem leaf_2164_ok : checkAt 527 1000 box_2164 cert_2164 = true := by
  have h := List.all_eq_true.mp batch_43_02_ok accepted_2164 (by simp [batch_43_02_values])
  exact h
theorem leaf_2164_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2164.profileLo box_2164.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2164_ok
theorem branch_box_2164_nonnegative : ∀ j, 0 ≤ branch_box_2164.lower j ∧ 0 ≤ branch_box_2164.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2164, Box.profileLo, Box.profileHi, box_2164]
theorem leaf_2164_BranchSafe : CertificateConsequences.BranchSafe branch_box_2164 := by
  left; refine ⟨branch_box_2164_nonnegative, ?_⟩
  intro z hz; exact leaf_2164_sound hz

theorem leaf_2166_ok : checkAt 527 1000 box_2166 cert_2166 = true := by
  have h := List.all_eq_true.mp batch_43_03_ok accepted_2166 (by simp [batch_43_03_values])
  exact h
theorem leaf_2166_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2166.profileLo box_2166.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2166_ok
theorem branch_box_2166_nonnegative : ∀ j, 0 ≤ branch_box_2166.lower j ∧ 0 ≤ branch_box_2166.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2166, Box.profileLo, Box.profileHi, box_2166]
theorem leaf_2166_BranchSafe : CertificateConsequences.BranchSafe branch_box_2166 := by
  left; refine ⟨branch_box_2166_nonnegative, ?_⟩
  intro z hz; exact leaf_2166_sound hz

theorem leaf_2170_ok : checkAt 527 1000 box_2170 cert_2170 = true := by
  have h := List.all_eq_true.mp batch_43_04_ok accepted_2170 (by simp [batch_43_04_values])
  exact h
theorem leaf_2170_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2170.profileLo box_2170.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2170_ok
theorem branch_box_2170_nonnegative : ∀ j, 0 ≤ branch_box_2170.lower j ∧ 0 ≤ branch_box_2170.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2170, Box.profileLo, Box.profileHi, box_2170]
theorem leaf_2170_BranchSafe : CertificateConsequences.BranchSafe branch_box_2170 := by
  left; refine ⟨branch_box_2170_nonnegative, ?_⟩
  intro z hz; exact leaf_2170_sound hz

theorem leaf_2178_ok : checkAt 527 1000 box_2178 cert_2178 = true := by
  have h := List.all_eq_true.mp batch_43_05_ok accepted_2178 (by simp [batch_43_05_values])
  exact h
theorem leaf_2178_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2178.profileLo box_2178.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2178_ok
theorem branch_box_2178_nonnegative : ∀ j, 0 ≤ branch_box_2178.lower j ∧ 0 ≤ branch_box_2178.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2178, Box.profileLo, Box.profileHi, box_2178]
theorem leaf_2178_BranchSafe : CertificateConsequences.BranchSafe branch_box_2178 := by
  left; refine ⟨branch_box_2178_nonnegative, ?_⟩
  intro z hz; exact leaf_2178_sound hz

theorem leaf_2180_ok : checkAt 527 1000 box_2180 cert_2180 = true := by
  have h := List.all_eq_true.mp batch_43_06_ok accepted_2180 (by simp [batch_43_06_values])
  exact h
theorem leaf_2180_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2180.profileLo box_2180.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2180_ok
theorem branch_box_2180_nonnegative : ∀ j, 0 ≤ branch_box_2180.lower j ∧ 0 ≤ branch_box_2180.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2180, Box.profileLo, Box.profileHi, box_2180]
theorem leaf_2180_BranchSafe : CertificateConsequences.BranchSafe branch_box_2180 := by
  left; refine ⟨branch_box_2180_nonnegative, ?_⟩
  intro z hz; exact leaf_2180_sound hz

theorem leaf_2184_ok : checkAt 527 1000 box_2184 cert_2184 = true := by
  have h := List.all_eq_true.mp batch_43_07_ok accepted_2184 (by simp [batch_43_07_values])
  exact h
theorem leaf_2184_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2184.profileLo box_2184.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2184_ok
theorem branch_box_2184_nonnegative : ∀ j, 0 ≤ branch_box_2184.lower j ∧ 0 ≤ branch_box_2184.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2184, Box.profileLo, Box.profileHi, box_2184]
theorem leaf_2184_BranchSafe : CertificateConsequences.BranchSafe branch_box_2184 := by
  left; refine ⟨branch_box_2184_nonnegative, ?_⟩
  intro z hz; exact leaf_2184_sound hz

theorem leaf_2189_ok : checkAt 527 1000 box_2189 cert_2189 = true := by
  have h := List.all_eq_true.mp batch_43_08_ok accepted_2189 (by simp [batch_43_08_values])
  exact h
theorem leaf_2189_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2189.profileLo box_2189.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2189_ok
theorem branch_box_2189_nonnegative : ∀ j, 0 ≤ branch_box_2189.lower j ∧ 0 ≤ branch_box_2189.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2189, Box.profileLo, Box.profileHi, box_2189]
theorem leaf_2189_BranchSafe : CertificateConsequences.BranchSafe branch_box_2189 := by
  left; refine ⟨branch_box_2189_nonnegative, ?_⟩
  intro z hz; exact leaf_2189_sound hz

theorem leaf_2196_ok : checkAt 527 1000 box_2196 cert_2196 = true := by
  have h := List.all_eq_true.mp batch_43_09_ok accepted_2196 (by simp [batch_43_09_values])
  exact h
theorem leaf_2196_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2196.profileLo box_2196.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2196_ok
theorem branch_box_2196_nonnegative : ∀ j, 0 ≤ branch_box_2196.lower j ∧ 0 ≤ branch_box_2196.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2196, Box.profileLo, Box.profileHi, box_2196]
theorem leaf_2196_BranchSafe : CertificateConsequences.BranchSafe branch_box_2196 := by
  left; refine ⟨branch_box_2196_nonnegative, ?_⟩
  intro z hz; exact leaf_2196_sound hz

theorem leaf_2198_ok : checkAt 527 1000 box_2198 cert_2198 = true := by
  have h := List.all_eq_true.mp batch_43_10_ok accepted_2198 (by simp [batch_43_10_values])
  exact h
theorem leaf_2198_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2198.profileLo box_2198.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2198_ok
theorem branch_box_2198_nonnegative : ∀ j, 0 ≤ branch_box_2198.lower j ∧ 0 ≤ branch_box_2198.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2198, Box.profileLo, Box.profileHi, box_2198]
theorem leaf_2198_BranchSafe : CertificateConsequences.BranchSafe branch_box_2198 := by
  left; refine ⟨branch_box_2198_nonnegative, ?_⟩
  intro z hz; exact leaf_2198_sound hz

#print axioms batch_43_00_ok
#print axioms leaf_2151_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
