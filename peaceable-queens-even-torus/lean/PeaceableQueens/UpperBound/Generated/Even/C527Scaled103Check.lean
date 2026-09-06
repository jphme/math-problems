import PeaceableQueens.UpperBound.Generated.Even.C527Scaled103Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_103_00_values : List Bool := [accepted_5150]
theorem batch_103_00_ok : batch_103_00_values.all id = true := by decide

def batch_103_01_values : List Bool := [accepted_5153]
theorem batch_103_01_ok : batch_103_01_values.all id = true := by decide

def batch_103_02_values : List Bool := [accepted_5155]
theorem batch_103_02_ok : batch_103_02_values.all id = true := by decide

def batch_103_03_values : List Bool := [accepted_5156]
theorem batch_103_03_ok : batch_103_03_values.all id = true := by decide

def batch_103_04_values : List Bool := [accepted_5159]
theorem batch_103_04_ok : batch_103_04_values.all id = true := by decide

def batch_103_05_values : List Bool := [accepted_5160]
theorem batch_103_05_ok : batch_103_05_values.all id = true := by decide

def batch_103_06_values : List Bool := [accepted_5161]
theorem batch_103_06_ok : batch_103_06_values.all id = true := by decide

def batch_103_07_values : List Bool := [accepted_5162]
theorem batch_103_07_ok : batch_103_07_values.all id = true := by decide

def batch_103_08_values : List Bool := [accepted_5169]
theorem batch_103_08_ok : batch_103_08_values.all id = true := by decide

def batch_103_09_values : List Bool := [accepted_5171]
theorem batch_103_09_ok : batch_103_09_values.all id = true := by decide

def batch_103_10_values : List Bool := [accepted_5172]
theorem batch_103_10_ok : batch_103_10_values.all id = true := by decide

def batch_103_11_values : List Bool := [accepted_5175]
theorem batch_103_11_ok : batch_103_11_values.all id = true := by decide

def batch_103_12_values : List Bool := [accepted_5177]
theorem batch_103_12_ok : batch_103_12_values.all id = true := by decide

def batch_103_13_values : List Bool := [accepted_5178]
theorem batch_103_13_ok : batch_103_13_values.all id = true := by decide

def batch_103_14_values : List Bool := [accepted_5181]
theorem batch_103_14_ok : batch_103_14_values.all id = true := by decide

def batch_103_15_values : List Bool := [accepted_5183]
theorem batch_103_15_ok : batch_103_15_values.all id = true := by decide

def batch_103_16_values : List Bool := [accepted_5184]
theorem batch_103_16_ok : batch_103_16_values.all id = true := by decide

def batch_103_17_values : List Bool := [accepted_5185]
theorem batch_103_17_ok : batch_103_17_values.all id = true := by decide

def batch_103_18_values : List Bool := [accepted_5187]
theorem batch_103_18_ok : batch_103_18_values.all id = true := by decide

def batch_103_19_values : List Bool := [accepted_5188]
theorem batch_103_19_ok : batch_103_19_values.all id = true := by decide

def batch_103_20_values : List Bool := [accepted_5191]
theorem batch_103_20_ok : batch_103_20_values.all id = true := by decide

def batch_103_21_values : List Bool := [accepted_5192]
theorem batch_103_21_ok : batch_103_21_values.all id = true := by decide

def batch_103_22_values : List Bool := [accepted_5199]
theorem batch_103_22_ok : batch_103_22_values.all id = true := by decide

theorem leaf_5150_ok : checkAt 527 1000 box_5150 cert_5150 = true := by
  have h := List.all_eq_true.mp batch_103_00_ok accepted_5150 (by simp [batch_103_00_values])
  exact h
theorem leaf_5150_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5150.profileLo box_5150.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5150_ok
theorem branch_box_5150_nonnegative : ∀ j, 0 ≤ branch_box_5150.lower j ∧ 0 ≤ branch_box_5150.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5150, Box.profileLo, Box.profileHi, box_5150]
theorem leaf_5150_BranchSafe : CertificateConsequences.BranchSafe branch_box_5150 := by
  left; refine ⟨branch_box_5150_nonnegative, ?_⟩
  intro z hz; exact leaf_5150_sound hz

theorem leaf_5153_ok : checkAt 527 1000 box_5153 cert_5153 = true := by
  have h := List.all_eq_true.mp batch_103_01_ok accepted_5153 (by simp [batch_103_01_values])
  exact h
theorem leaf_5153_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5153.profileLo box_5153.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5153_ok
theorem branch_box_5153_nonnegative : ∀ j, 0 ≤ branch_box_5153.lower j ∧ 0 ≤ branch_box_5153.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5153, Box.profileLo, Box.profileHi, box_5153]
theorem leaf_5153_BranchSafe : CertificateConsequences.BranchSafe branch_box_5153 := by
  left; refine ⟨branch_box_5153_nonnegative, ?_⟩
  intro z hz; exact leaf_5153_sound hz

theorem leaf_5155_ok : checkAt 527 1000 box_5155 cert_5155 = true := by
  have h := List.all_eq_true.mp batch_103_02_ok accepted_5155 (by simp [batch_103_02_values])
  exact h
theorem leaf_5155_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5155.profileLo box_5155.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5155_ok
theorem branch_box_5155_nonnegative : ∀ j, 0 ≤ branch_box_5155.lower j ∧ 0 ≤ branch_box_5155.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5155, Box.profileLo, Box.profileHi, box_5155]
theorem leaf_5155_BranchSafe : CertificateConsequences.BranchSafe branch_box_5155 := by
  left; refine ⟨branch_box_5155_nonnegative, ?_⟩
  intro z hz; exact leaf_5155_sound hz

theorem leaf_5156_ok : checkAt 527 1000 box_5156 cert_5156 = true := by
  have h := List.all_eq_true.mp batch_103_03_ok accepted_5156 (by simp [batch_103_03_values])
  exact h
theorem leaf_5156_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5156.profileLo box_5156.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5156_ok
theorem branch_box_5156_nonnegative : ∀ j, 0 ≤ branch_box_5156.lower j ∧ 0 ≤ branch_box_5156.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5156, Box.profileLo, Box.profileHi, box_5156]
theorem leaf_5156_BranchSafe : CertificateConsequences.BranchSafe branch_box_5156 := by
  left; refine ⟨branch_box_5156_nonnegative, ?_⟩
  intro z hz; exact leaf_5156_sound hz

theorem leaf_5159_ok : checkAt 527 1000 box_5159 cert_5159 = true := by
  have h := List.all_eq_true.mp batch_103_04_ok accepted_5159 (by simp [batch_103_04_values])
  exact h
theorem leaf_5159_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5159.profileLo box_5159.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5159_ok
theorem branch_box_5159_nonnegative : ∀ j, 0 ≤ branch_box_5159.lower j ∧ 0 ≤ branch_box_5159.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5159, Box.profileLo, Box.profileHi, box_5159]
theorem leaf_5159_BranchSafe : CertificateConsequences.BranchSafe branch_box_5159 := by
  left; refine ⟨branch_box_5159_nonnegative, ?_⟩
  intro z hz; exact leaf_5159_sound hz

theorem leaf_5160_ok : checkAt 527 1000 box_5160 cert_5160 = true := by
  have h := List.all_eq_true.mp batch_103_05_ok accepted_5160 (by simp [batch_103_05_values])
  exact h
theorem leaf_5160_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5160.profileLo box_5160.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5160_ok
theorem branch_box_5160_nonnegative : ∀ j, 0 ≤ branch_box_5160.lower j ∧ 0 ≤ branch_box_5160.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5160, Box.profileLo, Box.profileHi, box_5160]
theorem leaf_5160_BranchSafe : CertificateConsequences.BranchSafe branch_box_5160 := by
  left; refine ⟨branch_box_5160_nonnegative, ?_⟩
  intro z hz; exact leaf_5160_sound hz

theorem leaf_5161_ok : checkAt 527 1000 box_5161 cert_5161 = true := by
  have h := List.all_eq_true.mp batch_103_06_ok accepted_5161 (by simp [batch_103_06_values])
  exact h
theorem leaf_5161_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5161.profileLo box_5161.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5161_ok
theorem branch_box_5161_nonnegative : ∀ j, 0 ≤ branch_box_5161.lower j ∧ 0 ≤ branch_box_5161.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5161, Box.profileLo, Box.profileHi, box_5161]
theorem leaf_5161_BranchSafe : CertificateConsequences.BranchSafe branch_box_5161 := by
  left; refine ⟨branch_box_5161_nonnegative, ?_⟩
  intro z hz; exact leaf_5161_sound hz

theorem leaf_5162_ok : checkAt 527 1000 box_5162 cert_5162 = true := by
  have h := List.all_eq_true.mp batch_103_07_ok accepted_5162 (by simp [batch_103_07_values])
  exact h
theorem leaf_5162_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5162.profileLo box_5162.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5162_ok
theorem branch_box_5162_nonnegative : ∀ j, 0 ≤ branch_box_5162.lower j ∧ 0 ≤ branch_box_5162.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5162, Box.profileLo, Box.profileHi, box_5162]
theorem leaf_5162_BranchSafe : CertificateConsequences.BranchSafe branch_box_5162 := by
  left; refine ⟨branch_box_5162_nonnegative, ?_⟩
  intro z hz; exact leaf_5162_sound hz

theorem leaf_5169_ok : checkAt 527 1000 box_5169 cert_5169 = true := by
  have h := List.all_eq_true.mp batch_103_08_ok accepted_5169 (by simp [batch_103_08_values])
  exact h
theorem leaf_5169_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5169.profileLo box_5169.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5169_ok
theorem branch_box_5169_nonnegative : ∀ j, 0 ≤ branch_box_5169.lower j ∧ 0 ≤ branch_box_5169.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5169, Box.profileLo, Box.profileHi, box_5169]
theorem leaf_5169_BranchSafe : CertificateConsequences.BranchSafe branch_box_5169 := by
  left; refine ⟨branch_box_5169_nonnegative, ?_⟩
  intro z hz; exact leaf_5169_sound hz

theorem leaf_5171_ok : checkAt 527 1000 box_5171 cert_5171 = true := by
  have h := List.all_eq_true.mp batch_103_09_ok accepted_5171 (by simp [batch_103_09_values])
  exact h
theorem leaf_5171_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5171.profileLo box_5171.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5171_ok
theorem branch_box_5171_nonnegative : ∀ j, 0 ≤ branch_box_5171.lower j ∧ 0 ≤ branch_box_5171.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5171, Box.profileLo, Box.profileHi, box_5171]
theorem leaf_5171_BranchSafe : CertificateConsequences.BranchSafe branch_box_5171 := by
  left; refine ⟨branch_box_5171_nonnegative, ?_⟩
  intro z hz; exact leaf_5171_sound hz

theorem leaf_5172_ok : checkAt 527 1000 box_5172 cert_5172 = true := by
  have h := List.all_eq_true.mp batch_103_10_ok accepted_5172 (by simp [batch_103_10_values])
  exact h
theorem leaf_5172_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5172.profileLo box_5172.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5172_ok
theorem branch_box_5172_nonnegative : ∀ j, 0 ≤ branch_box_5172.lower j ∧ 0 ≤ branch_box_5172.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5172, Box.profileLo, Box.profileHi, box_5172]
theorem leaf_5172_BranchSafe : CertificateConsequences.BranchSafe branch_box_5172 := by
  left; refine ⟨branch_box_5172_nonnegative, ?_⟩
  intro z hz; exact leaf_5172_sound hz

theorem leaf_5175_ok : checkAt 527 1000 box_5175 cert_5175 = true := by
  have h := List.all_eq_true.mp batch_103_11_ok accepted_5175 (by simp [batch_103_11_values])
  exact h
theorem leaf_5175_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5175.profileLo box_5175.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5175_ok
theorem branch_box_5175_nonnegative : ∀ j, 0 ≤ branch_box_5175.lower j ∧ 0 ≤ branch_box_5175.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5175, Box.profileLo, Box.profileHi, box_5175]
theorem leaf_5175_BranchSafe : CertificateConsequences.BranchSafe branch_box_5175 := by
  left; refine ⟨branch_box_5175_nonnegative, ?_⟩
  intro z hz; exact leaf_5175_sound hz

theorem leaf_5177_ok : checkAt 527 1000 box_5177 cert_5177 = true := by
  have h := List.all_eq_true.mp batch_103_12_ok accepted_5177 (by simp [batch_103_12_values])
  exact h
theorem leaf_5177_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5177.profileLo box_5177.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5177_ok
theorem branch_box_5177_nonnegative : ∀ j, 0 ≤ branch_box_5177.lower j ∧ 0 ≤ branch_box_5177.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5177, Box.profileLo, Box.profileHi, box_5177]
theorem leaf_5177_BranchSafe : CertificateConsequences.BranchSafe branch_box_5177 := by
  left; refine ⟨branch_box_5177_nonnegative, ?_⟩
  intro z hz; exact leaf_5177_sound hz

theorem leaf_5178_ok : checkAt 527 1000 box_5178 cert_5178 = true := by
  have h := List.all_eq_true.mp batch_103_13_ok accepted_5178 (by simp [batch_103_13_values])
  exact h
theorem leaf_5178_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5178.profileLo box_5178.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5178_ok
theorem branch_box_5178_nonnegative : ∀ j, 0 ≤ branch_box_5178.lower j ∧ 0 ≤ branch_box_5178.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5178, Box.profileLo, Box.profileHi, box_5178]
theorem leaf_5178_BranchSafe : CertificateConsequences.BranchSafe branch_box_5178 := by
  left; refine ⟨branch_box_5178_nonnegative, ?_⟩
  intro z hz; exact leaf_5178_sound hz

theorem leaf_5181_ok : checkAt 527 1000 box_5181 cert_5181 = true := by
  have h := List.all_eq_true.mp batch_103_14_ok accepted_5181 (by simp [batch_103_14_values])
  exact h
theorem leaf_5181_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5181.profileLo box_5181.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5181_ok
theorem branch_box_5181_nonnegative : ∀ j, 0 ≤ branch_box_5181.lower j ∧ 0 ≤ branch_box_5181.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5181, Box.profileLo, Box.profileHi, box_5181]
theorem leaf_5181_BranchSafe : CertificateConsequences.BranchSafe branch_box_5181 := by
  left; refine ⟨branch_box_5181_nonnegative, ?_⟩
  intro z hz; exact leaf_5181_sound hz

theorem leaf_5183_ok : checkAt 527 1000 box_5183 cert_5183 = true := by
  have h := List.all_eq_true.mp batch_103_15_ok accepted_5183 (by simp [batch_103_15_values])
  exact h
theorem leaf_5183_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5183.profileLo box_5183.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5183_ok
theorem branch_box_5183_nonnegative : ∀ j, 0 ≤ branch_box_5183.lower j ∧ 0 ≤ branch_box_5183.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5183, Box.profileLo, Box.profileHi, box_5183]
theorem leaf_5183_BranchSafe : CertificateConsequences.BranchSafe branch_box_5183 := by
  left; refine ⟨branch_box_5183_nonnegative, ?_⟩
  intro z hz; exact leaf_5183_sound hz

theorem leaf_5184_ok : checkAt 527 1000 box_5184 cert_5184 = true := by
  have h := List.all_eq_true.mp batch_103_16_ok accepted_5184 (by simp [batch_103_16_values])
  exact h
theorem leaf_5184_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5184.profileLo box_5184.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5184_ok
theorem branch_box_5184_nonnegative : ∀ j, 0 ≤ branch_box_5184.lower j ∧ 0 ≤ branch_box_5184.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5184, Box.profileLo, Box.profileHi, box_5184]
theorem leaf_5184_BranchSafe : CertificateConsequences.BranchSafe branch_box_5184 := by
  left; refine ⟨branch_box_5184_nonnegative, ?_⟩
  intro z hz; exact leaf_5184_sound hz

theorem leaf_5185_ok : checkAt 527 1000 box_5185 cert_5185 = true := by
  have h := List.all_eq_true.mp batch_103_17_ok accepted_5185 (by simp [batch_103_17_values])
  exact h
theorem leaf_5185_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5185.profileLo box_5185.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5185_ok
theorem branch_box_5185_nonnegative : ∀ j, 0 ≤ branch_box_5185.lower j ∧ 0 ≤ branch_box_5185.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5185, Box.profileLo, Box.profileHi, box_5185]
theorem leaf_5185_BranchSafe : CertificateConsequences.BranchSafe branch_box_5185 := by
  left; refine ⟨branch_box_5185_nonnegative, ?_⟩
  intro z hz; exact leaf_5185_sound hz

theorem leaf_5187_ok : checkAt 527 1000 box_5187 cert_5187 = true := by
  have h := List.all_eq_true.mp batch_103_18_ok accepted_5187 (by simp [batch_103_18_values])
  exact h
theorem leaf_5187_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5187.profileLo box_5187.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5187_ok
theorem branch_box_5187_nonnegative : ∀ j, 0 ≤ branch_box_5187.lower j ∧ 0 ≤ branch_box_5187.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5187, Box.profileLo, Box.profileHi, box_5187]
theorem leaf_5187_BranchSafe : CertificateConsequences.BranchSafe branch_box_5187 := by
  left; refine ⟨branch_box_5187_nonnegative, ?_⟩
  intro z hz; exact leaf_5187_sound hz

theorem leaf_5188_ok : checkAt 527 1000 box_5188 cert_5188 = true := by
  have h := List.all_eq_true.mp batch_103_19_ok accepted_5188 (by simp [batch_103_19_values])
  exact h
theorem leaf_5188_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5188.profileLo box_5188.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5188_ok
theorem branch_box_5188_nonnegative : ∀ j, 0 ≤ branch_box_5188.lower j ∧ 0 ≤ branch_box_5188.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5188, Box.profileLo, Box.profileHi, box_5188]
theorem leaf_5188_BranchSafe : CertificateConsequences.BranchSafe branch_box_5188 := by
  left; refine ⟨branch_box_5188_nonnegative, ?_⟩
  intro z hz; exact leaf_5188_sound hz

theorem leaf_5191_ok : checkAt 527 1000 box_5191 cert_5191 = true := by
  have h := List.all_eq_true.mp batch_103_20_ok accepted_5191 (by simp [batch_103_20_values])
  exact h
theorem leaf_5191_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5191.profileLo box_5191.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5191_ok
theorem branch_box_5191_nonnegative : ∀ j, 0 ≤ branch_box_5191.lower j ∧ 0 ≤ branch_box_5191.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5191, Box.profileLo, Box.profileHi, box_5191]
theorem leaf_5191_BranchSafe : CertificateConsequences.BranchSafe branch_box_5191 := by
  left; refine ⟨branch_box_5191_nonnegative, ?_⟩
  intro z hz; exact leaf_5191_sound hz

theorem leaf_5192_ok : checkAt 527 1000 box_5192 cert_5192 = true := by
  have h := List.all_eq_true.mp batch_103_21_ok accepted_5192 (by simp [batch_103_21_values])
  exact h
theorem leaf_5192_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5192.profileLo box_5192.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5192_ok
theorem branch_box_5192_nonnegative : ∀ j, 0 ≤ branch_box_5192.lower j ∧ 0 ≤ branch_box_5192.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5192, Box.profileLo, Box.profileHi, box_5192]
theorem leaf_5192_BranchSafe : CertificateConsequences.BranchSafe branch_box_5192 := by
  left; refine ⟨branch_box_5192_nonnegative, ?_⟩
  intro z hz; exact leaf_5192_sound hz

theorem leaf_5199_ok : checkAt 527 1000 box_5199 cert_5199 = true := by
  have h := List.all_eq_true.mp batch_103_22_ok accepted_5199 (by simp [batch_103_22_values])
  exact h
theorem leaf_5199_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5199.profileLo box_5199.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5199_ok
theorem branch_box_5199_nonnegative : ∀ j, 0 ≤ branch_box_5199.lower j ∧ 0 ≤ branch_box_5199.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5199, Box.profileLo, Box.profileHi, box_5199]
theorem leaf_5199_BranchSafe : CertificateConsequences.BranchSafe branch_box_5199 := by
  left; refine ⟨branch_box_5199_nonnegative, ?_⟩
  intro z hz; exact leaf_5199_sound hz

#print axioms batch_103_00_ok
#print axioms leaf_5150_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
