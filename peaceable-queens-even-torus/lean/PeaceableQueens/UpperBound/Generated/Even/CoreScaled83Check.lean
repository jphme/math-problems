import PeaceableQueens.UpperBound.Generated.Even.CoreScaled83Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_83_00_values : List Bool := [accepted_4151]
theorem batch_83_00_ok : batch_83_00_values.all id = true := by decide

def batch_83_01_values : List Bool := [accepted_4156]
theorem batch_83_01_ok : batch_83_01_values.all id = true := by decide

def batch_83_02_values : List Bool := [accepted_4157]
theorem batch_83_02_ok : batch_83_02_values.all id = true := by decide

def batch_83_03_values : List Bool := [accepted_4159]
theorem batch_83_03_ok : batch_83_03_values.all id = true := by decide

def batch_83_04_values : List Bool := [accepted_4161]
theorem batch_83_04_ok : batch_83_04_values.all id = true := by decide

def batch_83_05_values : List Bool := [accepted_4168]
theorem batch_83_05_ok : batch_83_05_values.all id = true := by decide

def batch_83_06_values : List Bool := [accepted_4170]
theorem batch_83_06_ok : batch_83_06_values.all id = true := by decide

def batch_83_07_values : List Bool := [accepted_4172]
theorem batch_83_07_ok : batch_83_07_values.all id = true := by decide

def batch_83_08_values : List Bool := [accepted_4174]
theorem batch_83_08_ok : batch_83_08_values.all id = true := by decide

def batch_83_09_values : List Bool := [accepted_4176]
theorem batch_83_09_ok : batch_83_09_values.all id = true := by decide

def batch_83_10_values : List Bool := [accepted_4177]
theorem batch_83_10_ok : batch_83_10_values.all id = true := by decide

def batch_83_11_values : List Bool := [accepted_4182]
theorem batch_83_11_ok : batch_83_11_values.all id = true := by decide

def batch_83_12_values : List Bool := [accepted_4183]
theorem batch_83_12_ok : batch_83_12_values.all id = true := by decide

def batch_83_13_values : List Bool := [accepted_4188]
theorem batch_83_13_ok : batch_83_13_values.all id = true := by decide

def batch_83_14_values : List Bool := [accepted_4189]
theorem batch_83_14_ok : batch_83_14_values.all id = true := by decide

def batch_83_15_values : List Bool := [accepted_4192]
theorem batch_83_15_ok : batch_83_15_values.all id = true := by decide

def batch_83_16_values : List Bool := [accepted_4196]
theorem batch_83_16_ok : batch_83_16_values.all id = true := by decide

def batch_83_17_values : List Bool := [accepted_4198]
theorem batch_83_17_ok : batch_83_17_values.all id = true := by decide

theorem leaf_4151_ok : checkAt 527 1000 box_4151 cert_4151 = true := by
  have h := List.all_eq_true.mp batch_83_00_ok accepted_4151 (by simp [batch_83_00_values])
  exact h
theorem leaf_4151_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4151.profileLo box_4151.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4151_ok
theorem branch_box_4151_nonnegative : ∀ j, 0 ≤ branch_box_4151.lower j ∧ 0 ≤ branch_box_4151.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4151, Box.profileLo, Box.profileHi, box_4151]
theorem leaf_4151_BranchSafe : CertificateConsequences.BranchSafe branch_box_4151 := by
  left; refine ⟨branch_box_4151_nonnegative, ?_⟩
  intro z hz; exact leaf_4151_sound hz

theorem leaf_4156_ok : checkAt 527 1000 box_4156 cert_4156 = true := by
  have h := List.all_eq_true.mp batch_83_01_ok accepted_4156 (by simp [batch_83_01_values])
  exact h
theorem leaf_4156_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4156.profileLo box_4156.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4156_ok
theorem branch_box_4156_nonnegative : ∀ j, 0 ≤ branch_box_4156.lower j ∧ 0 ≤ branch_box_4156.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4156, Box.profileLo, Box.profileHi, box_4156]
theorem leaf_4156_BranchSafe : CertificateConsequences.BranchSafe branch_box_4156 := by
  left; refine ⟨branch_box_4156_nonnegative, ?_⟩
  intro z hz; exact leaf_4156_sound hz

theorem leaf_4157_ok : checkAt 527 1000 box_4157 cert_4157 = true := by
  have h := List.all_eq_true.mp batch_83_02_ok accepted_4157 (by simp [batch_83_02_values])
  exact h
theorem leaf_4157_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4157.profileLo box_4157.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4157_ok
theorem branch_box_4157_nonnegative : ∀ j, 0 ≤ branch_box_4157.lower j ∧ 0 ≤ branch_box_4157.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4157, Box.profileLo, Box.profileHi, box_4157]
theorem leaf_4157_BranchSafe : CertificateConsequences.BranchSafe branch_box_4157 := by
  left; refine ⟨branch_box_4157_nonnegative, ?_⟩
  intro z hz; exact leaf_4157_sound hz

theorem leaf_4159_ok : checkAt 527 1000 box_4159 cert_4159 = true := by
  have h := List.all_eq_true.mp batch_83_03_ok accepted_4159 (by simp [batch_83_03_values])
  exact h
theorem leaf_4159_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4159.profileLo box_4159.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4159_ok
theorem branch_box_4159_nonnegative : ∀ j, 0 ≤ branch_box_4159.lower j ∧ 0 ≤ branch_box_4159.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4159, Box.profileLo, Box.profileHi, box_4159]
theorem leaf_4159_BranchSafe : CertificateConsequences.BranchSafe branch_box_4159 := by
  left; refine ⟨branch_box_4159_nonnegative, ?_⟩
  intro z hz; exact leaf_4159_sound hz

theorem leaf_4161_ok : checkAt 527 1000 box_4161 cert_4161 = true := by
  have h := List.all_eq_true.mp batch_83_04_ok accepted_4161 (by simp [batch_83_04_values])
  exact h
theorem leaf_4161_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4161.profileLo box_4161.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4161_ok
theorem branch_box_4161_nonnegative : ∀ j, 0 ≤ branch_box_4161.lower j ∧ 0 ≤ branch_box_4161.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4161, Box.profileLo, Box.profileHi, box_4161]
theorem leaf_4161_BranchSafe : CertificateConsequences.BranchSafe branch_box_4161 := by
  left; refine ⟨branch_box_4161_nonnegative, ?_⟩
  intro z hz; exact leaf_4161_sound hz

theorem leaf_4168_ok : checkAt 527 1000 box_4168 cert_4168 = true := by
  have h := List.all_eq_true.mp batch_83_05_ok accepted_4168 (by simp [batch_83_05_values])
  exact h
theorem leaf_4168_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4168.profileLo box_4168.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4168_ok
theorem branch_box_4168_nonnegative : ∀ j, 0 ≤ branch_box_4168.lower j ∧ 0 ≤ branch_box_4168.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4168, Box.profileLo, Box.profileHi, box_4168]
theorem leaf_4168_BranchSafe : CertificateConsequences.BranchSafe branch_box_4168 := by
  left; refine ⟨branch_box_4168_nonnegative, ?_⟩
  intro z hz; exact leaf_4168_sound hz

theorem leaf_4170_ok : checkAt 527 1000 box_4170 cert_4170 = true := by
  have h := List.all_eq_true.mp batch_83_06_ok accepted_4170 (by simp [batch_83_06_values])
  exact h
theorem leaf_4170_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4170.profileLo box_4170.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4170_ok
theorem branch_box_4170_nonnegative : ∀ j, 0 ≤ branch_box_4170.lower j ∧ 0 ≤ branch_box_4170.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4170, Box.profileLo, Box.profileHi, box_4170]
theorem leaf_4170_BranchSafe : CertificateConsequences.BranchSafe branch_box_4170 := by
  left; refine ⟨branch_box_4170_nonnegative, ?_⟩
  intro z hz; exact leaf_4170_sound hz

theorem leaf_4172_ok : checkAt 527 1000 box_4172 cert_4172 = true := by
  have h := List.all_eq_true.mp batch_83_07_ok accepted_4172 (by simp [batch_83_07_values])
  exact h
theorem leaf_4172_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4172.profileLo box_4172.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4172_ok
theorem branch_box_4172_nonnegative : ∀ j, 0 ≤ branch_box_4172.lower j ∧ 0 ≤ branch_box_4172.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4172, Box.profileLo, Box.profileHi, box_4172]
theorem leaf_4172_BranchSafe : CertificateConsequences.BranchSafe branch_box_4172 := by
  left; refine ⟨branch_box_4172_nonnegative, ?_⟩
  intro z hz; exact leaf_4172_sound hz

theorem leaf_4174_ok : checkAt 527 1000 box_4174 cert_4174 = true := by
  have h := List.all_eq_true.mp batch_83_08_ok accepted_4174 (by simp [batch_83_08_values])
  exact h
theorem leaf_4174_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4174.profileLo box_4174.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4174_ok
theorem branch_box_4174_nonnegative : ∀ j, 0 ≤ branch_box_4174.lower j ∧ 0 ≤ branch_box_4174.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4174, Box.profileLo, Box.profileHi, box_4174]
theorem leaf_4174_BranchSafe : CertificateConsequences.BranchSafe branch_box_4174 := by
  left; refine ⟨branch_box_4174_nonnegative, ?_⟩
  intro z hz; exact leaf_4174_sound hz

theorem leaf_4176_ok : checkAt 527 1000 box_4176 cert_4176 = true := by
  have h := List.all_eq_true.mp batch_83_09_ok accepted_4176 (by simp [batch_83_09_values])
  exact h
theorem leaf_4176_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4176.profileLo box_4176.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4176_ok
theorem branch_box_4176_nonnegative : ∀ j, 0 ≤ branch_box_4176.lower j ∧ 0 ≤ branch_box_4176.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4176, Box.profileLo, Box.profileHi, box_4176]
theorem leaf_4176_BranchSafe : CertificateConsequences.BranchSafe branch_box_4176 := by
  left; refine ⟨branch_box_4176_nonnegative, ?_⟩
  intro z hz; exact leaf_4176_sound hz

theorem leaf_4177_ok : checkAt 527 1000 box_4177 cert_4177 = true := by
  have h := List.all_eq_true.mp batch_83_10_ok accepted_4177 (by simp [batch_83_10_values])
  exact h
theorem leaf_4177_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4177.profileLo box_4177.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4177_ok
theorem branch_box_4177_nonnegative : ∀ j, 0 ≤ branch_box_4177.lower j ∧ 0 ≤ branch_box_4177.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4177, Box.profileLo, Box.profileHi, box_4177]
theorem leaf_4177_BranchSafe : CertificateConsequences.BranchSafe branch_box_4177 := by
  left; refine ⟨branch_box_4177_nonnegative, ?_⟩
  intro z hz; exact leaf_4177_sound hz

theorem leaf_4182_ok : checkAt 527 1000 box_4182 cert_4182 = true := by
  have h := List.all_eq_true.mp batch_83_11_ok accepted_4182 (by simp [batch_83_11_values])
  exact h
theorem leaf_4182_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4182.profileLo box_4182.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4182_ok
theorem branch_box_4182_nonnegative : ∀ j, 0 ≤ branch_box_4182.lower j ∧ 0 ≤ branch_box_4182.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4182, Box.profileLo, Box.profileHi, box_4182]
theorem leaf_4182_BranchSafe : CertificateConsequences.BranchSafe branch_box_4182 := by
  left; refine ⟨branch_box_4182_nonnegative, ?_⟩
  intro z hz; exact leaf_4182_sound hz

theorem leaf_4183_ok : checkAt 527 1000 box_4183 cert_4183 = true := by
  have h := List.all_eq_true.mp batch_83_12_ok accepted_4183 (by simp [batch_83_12_values])
  exact h
theorem leaf_4183_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4183.profileLo box_4183.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4183_ok
theorem branch_box_4183_nonnegative : ∀ j, 0 ≤ branch_box_4183.lower j ∧ 0 ≤ branch_box_4183.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4183, Box.profileLo, Box.profileHi, box_4183]
theorem leaf_4183_BranchSafe : CertificateConsequences.BranchSafe branch_box_4183 := by
  left; refine ⟨branch_box_4183_nonnegative, ?_⟩
  intro z hz; exact leaf_4183_sound hz

theorem leaf_4188_ok : checkAt 527 1000 box_4188 cert_4188 = true := by
  have h := List.all_eq_true.mp batch_83_13_ok accepted_4188 (by simp [batch_83_13_values])
  exact h
theorem leaf_4188_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4188.profileLo box_4188.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4188_ok
theorem branch_box_4188_nonnegative : ∀ j, 0 ≤ branch_box_4188.lower j ∧ 0 ≤ branch_box_4188.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4188, Box.profileLo, Box.profileHi, box_4188]
theorem leaf_4188_BranchSafe : CertificateConsequences.BranchSafe branch_box_4188 := by
  left; refine ⟨branch_box_4188_nonnegative, ?_⟩
  intro z hz; exact leaf_4188_sound hz

theorem leaf_4189_ok : checkAt 527 1000 box_4189 cert_4189 = true := by
  have h := List.all_eq_true.mp batch_83_14_ok accepted_4189 (by simp [batch_83_14_values])
  exact h
theorem leaf_4189_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4189.profileLo box_4189.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4189_ok
theorem branch_box_4189_nonnegative : ∀ j, 0 ≤ branch_box_4189.lower j ∧ 0 ≤ branch_box_4189.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4189, Box.profileLo, Box.profileHi, box_4189]
theorem leaf_4189_BranchSafe : CertificateConsequences.BranchSafe branch_box_4189 := by
  left; refine ⟨branch_box_4189_nonnegative, ?_⟩
  intro z hz; exact leaf_4189_sound hz

theorem leaf_4192_ok : checkAt 527 1000 box_4192 cert_4192 = true := by
  have h := List.all_eq_true.mp batch_83_15_ok accepted_4192 (by simp [batch_83_15_values])
  exact h
theorem leaf_4192_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4192.profileLo box_4192.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4192_ok
theorem branch_box_4192_nonnegative : ∀ j, 0 ≤ branch_box_4192.lower j ∧ 0 ≤ branch_box_4192.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4192, Box.profileLo, Box.profileHi, box_4192]
theorem leaf_4192_BranchSafe : CertificateConsequences.BranchSafe branch_box_4192 := by
  left; refine ⟨branch_box_4192_nonnegative, ?_⟩
  intro z hz; exact leaf_4192_sound hz

theorem leaf_4196_ok : checkAt 527 1000 box_4196 cert_4196 = true := by
  have h := List.all_eq_true.mp batch_83_16_ok accepted_4196 (by simp [batch_83_16_values])
  exact h
theorem leaf_4196_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4196.profileLo box_4196.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4196_ok
theorem branch_box_4196_nonnegative : ∀ j, 0 ≤ branch_box_4196.lower j ∧ 0 ≤ branch_box_4196.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4196, Box.profileLo, Box.profileHi, box_4196]
theorem leaf_4196_BranchSafe : CertificateConsequences.BranchSafe branch_box_4196 := by
  left; refine ⟨branch_box_4196_nonnegative, ?_⟩
  intro z hz; exact leaf_4196_sound hz

theorem leaf_4198_ok : checkAt 527 1000 box_4198 cert_4198 = true := by
  have h := List.all_eq_true.mp batch_83_17_ok accepted_4198 (by simp [batch_83_17_values])
  exact h
theorem leaf_4198_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4198.profileLo box_4198.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4198_ok
theorem branch_box_4198_nonnegative : ∀ j, 0 ≤ branch_box_4198.lower j ∧ 0 ≤ branch_box_4198.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4198, Box.profileLo, Box.profileHi, box_4198]
theorem leaf_4198_BranchSafe : CertificateConsequences.BranchSafe branch_box_4198 := by
  left; refine ⟨branch_box_4198_nonnegative, ?_⟩
  intro z hz; exact leaf_4198_sound hz

#print axioms batch_83_00_ok
#print axioms leaf_4151_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
