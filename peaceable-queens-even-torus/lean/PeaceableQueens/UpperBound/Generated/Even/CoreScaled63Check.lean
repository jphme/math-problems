import PeaceableQueens.UpperBound.Generated.Even.CoreScaled63Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_63_00_values : List Bool := [accepted_3154]
theorem batch_63_00_ok : batch_63_00_values.all id = true := by decide

def batch_63_01_values : List Bool := [accepted_3155]
theorem batch_63_01_ok : batch_63_01_values.all id = true := by decide

def batch_63_02_values : List Bool := [accepted_3157]
theorem batch_63_02_ok : batch_63_02_values.all id = true := by decide

def batch_63_03_values : List Bool := [accepted_3159]
theorem batch_63_03_ok : batch_63_03_values.all id = true := by decide

def batch_63_04_values : List Bool := [accepted_3162]
theorem batch_63_04_ok : batch_63_04_values.all id = true := by decide

def batch_63_05_values : List Bool := [accepted_3164]
theorem batch_63_05_ok : batch_63_05_values.all id = true := by decide

def batch_63_06_values : List Bool := [accepted_3165]
theorem batch_63_06_ok : batch_63_06_values.all id = true := by decide

def batch_63_07_values : List Bool := [accepted_3167]
theorem batch_63_07_ok : batch_63_07_values.all id = true := by decide

def batch_63_08_values : List Bool := [accepted_3169]
theorem batch_63_08_ok : batch_63_08_values.all id = true := by decide

def batch_63_09_values : List Bool := [accepted_3176]
theorem batch_63_09_ok : batch_63_09_values.all id = true := by decide

def batch_63_10_values : List Bool := [accepted_3177]
theorem batch_63_10_ok : batch_63_10_values.all id = true := by decide

def batch_63_11_values : List Bool := [accepted_3179]
theorem batch_63_11_ok : batch_63_11_values.all id = true := by decide

def batch_63_12_values : List Bool := [accepted_3181]
theorem batch_63_12_ok : batch_63_12_values.all id = true := by decide

def batch_63_13_values : List Bool := [accepted_3184]
theorem batch_63_13_ok : batch_63_13_values.all id = true := by decide

def batch_63_14_values : List Bool := [accepted_3186]
theorem batch_63_14_ok : batch_63_14_values.all id = true := by decide

def batch_63_15_values : List Bool := [accepted_3187]
theorem batch_63_15_ok : batch_63_15_values.all id = true := by decide

def batch_63_16_values : List Bool := [accepted_3189]
theorem batch_63_16_ok : batch_63_16_values.all id = true := by decide

def batch_63_17_values : List Bool := [accepted_3191]
theorem batch_63_17_ok : batch_63_17_values.all id = true := by decide

def batch_63_18_values : List Bool := [accepted_3196]
theorem batch_63_18_ok : batch_63_18_values.all id = true := by decide

def batch_63_19_values : List Bool := [accepted_3197]
theorem batch_63_19_ok : batch_63_19_values.all id = true := by decide

theorem leaf_3154_ok : checkAt 527 1000 box_3154 cert_3154 = true := by
  have h := List.all_eq_true.mp batch_63_00_ok accepted_3154 (by simp [batch_63_00_values])
  exact h
theorem leaf_3154_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3154.profileLo box_3154.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3154_ok
theorem branch_box_3154_nonnegative : ∀ j, 0 ≤ branch_box_3154.lower j ∧ 0 ≤ branch_box_3154.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3154, Box.profileLo, Box.profileHi, box_3154]
theorem leaf_3154_BranchSafe : CertificateConsequences.BranchSafe branch_box_3154 := by
  left; refine ⟨branch_box_3154_nonnegative, ?_⟩
  intro z hz; exact leaf_3154_sound hz

theorem leaf_3155_ok : checkAt 527 1000 box_3155 cert_3155 = true := by
  have h := List.all_eq_true.mp batch_63_01_ok accepted_3155 (by simp [batch_63_01_values])
  exact h
theorem leaf_3155_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3155.profileLo box_3155.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3155_ok
theorem branch_box_3155_nonnegative : ∀ j, 0 ≤ branch_box_3155.lower j ∧ 0 ≤ branch_box_3155.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3155, Box.profileLo, Box.profileHi, box_3155]
theorem leaf_3155_BranchSafe : CertificateConsequences.BranchSafe branch_box_3155 := by
  left; refine ⟨branch_box_3155_nonnegative, ?_⟩
  intro z hz; exact leaf_3155_sound hz

theorem leaf_3157_ok : checkAt 527 1000 box_3157 cert_3157 = true := by
  have h := List.all_eq_true.mp batch_63_02_ok accepted_3157 (by simp [batch_63_02_values])
  exact h
theorem leaf_3157_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3157.profileLo box_3157.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3157_ok
theorem branch_box_3157_nonnegative : ∀ j, 0 ≤ branch_box_3157.lower j ∧ 0 ≤ branch_box_3157.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3157, Box.profileLo, Box.profileHi, box_3157]
theorem leaf_3157_BranchSafe : CertificateConsequences.BranchSafe branch_box_3157 := by
  left; refine ⟨branch_box_3157_nonnegative, ?_⟩
  intro z hz; exact leaf_3157_sound hz

theorem leaf_3159_ok : checkAt 527 1000 box_3159 cert_3159 = true := by
  have h := List.all_eq_true.mp batch_63_03_ok accepted_3159 (by simp [batch_63_03_values])
  exact h
theorem leaf_3159_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3159.profileLo box_3159.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3159_ok
theorem branch_box_3159_nonnegative : ∀ j, 0 ≤ branch_box_3159.lower j ∧ 0 ≤ branch_box_3159.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3159, Box.profileLo, Box.profileHi, box_3159]
theorem leaf_3159_BranchSafe : CertificateConsequences.BranchSafe branch_box_3159 := by
  left; refine ⟨branch_box_3159_nonnegative, ?_⟩
  intro z hz; exact leaf_3159_sound hz

theorem leaf_3162_ok : checkAt 527 1000 box_3162 cert_3162 = true := by
  have h := List.all_eq_true.mp batch_63_04_ok accepted_3162 (by simp [batch_63_04_values])
  exact h
theorem leaf_3162_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3162.profileLo box_3162.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3162_ok
theorem branch_box_3162_nonnegative : ∀ j, 0 ≤ branch_box_3162.lower j ∧ 0 ≤ branch_box_3162.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3162, Box.profileLo, Box.profileHi, box_3162]
theorem leaf_3162_BranchSafe : CertificateConsequences.BranchSafe branch_box_3162 := by
  left; refine ⟨branch_box_3162_nonnegative, ?_⟩
  intro z hz; exact leaf_3162_sound hz

theorem leaf_3164_ok : checkAt 527 1000 box_3164 cert_3164 = true := by
  have h := List.all_eq_true.mp batch_63_05_ok accepted_3164 (by simp [batch_63_05_values])
  exact h
theorem leaf_3164_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3164.profileLo box_3164.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3164_ok
theorem branch_box_3164_nonnegative : ∀ j, 0 ≤ branch_box_3164.lower j ∧ 0 ≤ branch_box_3164.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3164, Box.profileLo, Box.profileHi, box_3164]
theorem leaf_3164_BranchSafe : CertificateConsequences.BranchSafe branch_box_3164 := by
  left; refine ⟨branch_box_3164_nonnegative, ?_⟩
  intro z hz; exact leaf_3164_sound hz

theorem leaf_3165_ok : checkAt 527 1000 box_3165 cert_3165 = true := by
  have h := List.all_eq_true.mp batch_63_06_ok accepted_3165 (by simp [batch_63_06_values])
  exact h
theorem leaf_3165_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3165.profileLo box_3165.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3165_ok
theorem branch_box_3165_nonnegative : ∀ j, 0 ≤ branch_box_3165.lower j ∧ 0 ≤ branch_box_3165.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3165, Box.profileLo, Box.profileHi, box_3165]
theorem leaf_3165_BranchSafe : CertificateConsequences.BranchSafe branch_box_3165 := by
  left; refine ⟨branch_box_3165_nonnegative, ?_⟩
  intro z hz; exact leaf_3165_sound hz

theorem leaf_3167_ok : checkAt 527 1000 box_3167 cert_3167 = true := by
  have h := List.all_eq_true.mp batch_63_07_ok accepted_3167 (by simp [batch_63_07_values])
  exact h
theorem leaf_3167_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3167.profileLo box_3167.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3167_ok
theorem branch_box_3167_nonnegative : ∀ j, 0 ≤ branch_box_3167.lower j ∧ 0 ≤ branch_box_3167.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3167, Box.profileLo, Box.profileHi, box_3167]
theorem leaf_3167_BranchSafe : CertificateConsequences.BranchSafe branch_box_3167 := by
  left; refine ⟨branch_box_3167_nonnegative, ?_⟩
  intro z hz; exact leaf_3167_sound hz

theorem leaf_3169_ok : checkAt 527 1000 box_3169 cert_3169 = true := by
  have h := List.all_eq_true.mp batch_63_08_ok accepted_3169 (by simp [batch_63_08_values])
  exact h
theorem leaf_3169_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3169.profileLo box_3169.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3169_ok
theorem branch_box_3169_nonnegative : ∀ j, 0 ≤ branch_box_3169.lower j ∧ 0 ≤ branch_box_3169.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3169, Box.profileLo, Box.profileHi, box_3169]
theorem leaf_3169_BranchSafe : CertificateConsequences.BranchSafe branch_box_3169 := by
  left; refine ⟨branch_box_3169_nonnegative, ?_⟩
  intro z hz; exact leaf_3169_sound hz

theorem leaf_3176_ok : checkAt 527 1000 box_3176 cert_3176 = true := by
  have h := List.all_eq_true.mp batch_63_09_ok accepted_3176 (by simp [batch_63_09_values])
  exact h
theorem leaf_3176_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3176.profileLo box_3176.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3176_ok
theorem branch_box_3176_nonnegative : ∀ j, 0 ≤ branch_box_3176.lower j ∧ 0 ≤ branch_box_3176.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3176, Box.profileLo, Box.profileHi, box_3176]
theorem leaf_3176_BranchSafe : CertificateConsequences.BranchSafe branch_box_3176 := by
  left; refine ⟨branch_box_3176_nonnegative, ?_⟩
  intro z hz; exact leaf_3176_sound hz

theorem leaf_3177_ok : checkAt 527 1000 box_3177 cert_3177 = true := by
  have h := List.all_eq_true.mp batch_63_10_ok accepted_3177 (by simp [batch_63_10_values])
  exact h
theorem leaf_3177_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3177.profileLo box_3177.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3177_ok
theorem branch_box_3177_nonnegative : ∀ j, 0 ≤ branch_box_3177.lower j ∧ 0 ≤ branch_box_3177.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3177, Box.profileLo, Box.profileHi, box_3177]
theorem leaf_3177_BranchSafe : CertificateConsequences.BranchSafe branch_box_3177 := by
  left; refine ⟨branch_box_3177_nonnegative, ?_⟩
  intro z hz; exact leaf_3177_sound hz

theorem leaf_3179_ok : checkAt 527 1000 box_3179 cert_3179 = true := by
  have h := List.all_eq_true.mp batch_63_11_ok accepted_3179 (by simp [batch_63_11_values])
  exact h
theorem leaf_3179_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3179.profileLo box_3179.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3179_ok
theorem branch_box_3179_nonnegative : ∀ j, 0 ≤ branch_box_3179.lower j ∧ 0 ≤ branch_box_3179.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3179, Box.profileLo, Box.profileHi, box_3179]
theorem leaf_3179_BranchSafe : CertificateConsequences.BranchSafe branch_box_3179 := by
  left; refine ⟨branch_box_3179_nonnegative, ?_⟩
  intro z hz; exact leaf_3179_sound hz

theorem leaf_3181_ok : checkAt 527 1000 box_3181 cert_3181 = true := by
  have h := List.all_eq_true.mp batch_63_12_ok accepted_3181 (by simp [batch_63_12_values])
  exact h
theorem leaf_3181_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3181.profileLo box_3181.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3181_ok
theorem branch_box_3181_nonnegative : ∀ j, 0 ≤ branch_box_3181.lower j ∧ 0 ≤ branch_box_3181.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3181, Box.profileLo, Box.profileHi, box_3181]
theorem leaf_3181_BranchSafe : CertificateConsequences.BranchSafe branch_box_3181 := by
  left; refine ⟨branch_box_3181_nonnegative, ?_⟩
  intro z hz; exact leaf_3181_sound hz

theorem leaf_3184_ok : checkAt 527 1000 box_3184 cert_3184 = true := by
  have h := List.all_eq_true.mp batch_63_13_ok accepted_3184 (by simp [batch_63_13_values])
  exact h
theorem leaf_3184_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3184.profileLo box_3184.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3184_ok
theorem branch_box_3184_nonnegative : ∀ j, 0 ≤ branch_box_3184.lower j ∧ 0 ≤ branch_box_3184.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3184, Box.profileLo, Box.profileHi, box_3184]
theorem leaf_3184_BranchSafe : CertificateConsequences.BranchSafe branch_box_3184 := by
  left; refine ⟨branch_box_3184_nonnegative, ?_⟩
  intro z hz; exact leaf_3184_sound hz

theorem leaf_3186_ok : checkAt 527 1000 box_3186 cert_3186 = true := by
  have h := List.all_eq_true.mp batch_63_14_ok accepted_3186 (by simp [batch_63_14_values])
  exact h
theorem leaf_3186_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3186.profileLo box_3186.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3186_ok
theorem branch_box_3186_nonnegative : ∀ j, 0 ≤ branch_box_3186.lower j ∧ 0 ≤ branch_box_3186.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3186, Box.profileLo, Box.profileHi, box_3186]
theorem leaf_3186_BranchSafe : CertificateConsequences.BranchSafe branch_box_3186 := by
  left; refine ⟨branch_box_3186_nonnegative, ?_⟩
  intro z hz; exact leaf_3186_sound hz

theorem leaf_3187_ok : checkAt 527 1000 box_3187 cert_3187 = true := by
  have h := List.all_eq_true.mp batch_63_15_ok accepted_3187 (by simp [batch_63_15_values])
  exact h
theorem leaf_3187_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3187.profileLo box_3187.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3187_ok
theorem branch_box_3187_nonnegative : ∀ j, 0 ≤ branch_box_3187.lower j ∧ 0 ≤ branch_box_3187.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3187, Box.profileLo, Box.profileHi, box_3187]
theorem leaf_3187_BranchSafe : CertificateConsequences.BranchSafe branch_box_3187 := by
  left; refine ⟨branch_box_3187_nonnegative, ?_⟩
  intro z hz; exact leaf_3187_sound hz

theorem leaf_3189_ok : checkAt 527 1000 box_3189 cert_3189 = true := by
  have h := List.all_eq_true.mp batch_63_16_ok accepted_3189 (by simp [batch_63_16_values])
  exact h
theorem leaf_3189_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3189.profileLo box_3189.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3189_ok
theorem branch_box_3189_nonnegative : ∀ j, 0 ≤ branch_box_3189.lower j ∧ 0 ≤ branch_box_3189.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3189, Box.profileLo, Box.profileHi, box_3189]
theorem leaf_3189_BranchSafe : CertificateConsequences.BranchSafe branch_box_3189 := by
  left; refine ⟨branch_box_3189_nonnegative, ?_⟩
  intro z hz; exact leaf_3189_sound hz

theorem leaf_3191_ok : checkAt 527 1000 box_3191 cert_3191 = true := by
  have h := List.all_eq_true.mp batch_63_17_ok accepted_3191 (by simp [batch_63_17_values])
  exact h
theorem leaf_3191_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3191.profileLo box_3191.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3191_ok
theorem branch_box_3191_nonnegative : ∀ j, 0 ≤ branch_box_3191.lower j ∧ 0 ≤ branch_box_3191.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3191, Box.profileLo, Box.profileHi, box_3191]
theorem leaf_3191_BranchSafe : CertificateConsequences.BranchSafe branch_box_3191 := by
  left; refine ⟨branch_box_3191_nonnegative, ?_⟩
  intro z hz; exact leaf_3191_sound hz

theorem leaf_3196_ok : checkAt 527 1000 box_3196 cert_3196 = true := by
  have h := List.all_eq_true.mp batch_63_18_ok accepted_3196 (by simp [batch_63_18_values])
  exact h
theorem leaf_3196_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3196.profileLo box_3196.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3196_ok
theorem branch_box_3196_nonnegative : ∀ j, 0 ≤ branch_box_3196.lower j ∧ 0 ≤ branch_box_3196.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3196, Box.profileLo, Box.profileHi, box_3196]
theorem leaf_3196_BranchSafe : CertificateConsequences.BranchSafe branch_box_3196 := by
  left; refine ⟨branch_box_3196_nonnegative, ?_⟩
  intro z hz; exact leaf_3196_sound hz

theorem leaf_3197_ok : checkAt 527 1000 box_3197 cert_3197 = true := by
  have h := List.all_eq_true.mp batch_63_19_ok accepted_3197 (by simp [batch_63_19_values])
  exact h
theorem leaf_3197_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_3197.profileLo box_3197.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_3197_ok
theorem branch_box_3197_nonnegative : ∀ j, 0 ≤ branch_box_3197.lower j ∧ 0 ≤ branch_box_3197.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_3197, Box.profileLo, Box.profileHi, box_3197]
theorem leaf_3197_BranchSafe : CertificateConsequences.BranchSafe branch_box_3197 := by
  left; refine ⟨branch_box_3197_nonnegative, ?_⟩
  intro z hz; exact leaf_3197_sound hz

#print axioms batch_63_00_ok
#print axioms leaf_3154_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
