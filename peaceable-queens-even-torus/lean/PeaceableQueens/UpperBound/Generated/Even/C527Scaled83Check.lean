import PeaceableQueens.UpperBound.Generated.Even.C527Scaled83Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_83_00_values : List Bool := [accepted_4150]
theorem batch_83_00_ok : batch_83_00_values.all id = true := by decide

def batch_83_01_values : List Bool := [accepted_4151]
theorem batch_83_01_ok : batch_83_01_values.all id = true := by decide

def batch_83_02_values : List Bool := [accepted_4152]
theorem batch_83_02_ok : batch_83_02_values.all id = true := by decide

def batch_83_03_values : List Bool := [accepted_4162]
theorem batch_83_03_ok : batch_83_03_values.all id = true := by decide

def batch_83_04_values : List Bool := [accepted_4163]
theorem batch_83_04_ok : batch_83_04_values.all id = true := by decide

def batch_83_05_values : List Bool := [accepted_4164]
theorem batch_83_05_ok : batch_83_05_values.all id = true := by decide

def batch_83_06_values : List Bool := [accepted_4167]
theorem batch_83_06_ok : batch_83_06_values.all id = true := by decide

def batch_83_07_values : List Bool := [accepted_4168]
theorem batch_83_07_ok : batch_83_07_values.all id = true := by decide

def batch_83_08_values : List Bool := [accepted_4169]
theorem batch_83_08_ok : batch_83_08_values.all id = true := by decide

def batch_83_09_values : List Bool := [accepted_4171]
theorem batch_83_09_ok : batch_83_09_values.all id = true := by decide

def batch_83_10_values : List Bool := [accepted_4172]
theorem batch_83_10_ok : batch_83_10_values.all id = true := by decide

def batch_83_11_values : List Bool := [accepted_4176]
theorem batch_83_11_ok : batch_83_11_values.all id = true := by decide

def batch_83_12_values : List Bool := [accepted_4177]
theorem batch_83_12_ok : batch_83_12_values.all id = true := by decide

def batch_83_13_values : List Bool := [accepted_4178]
theorem batch_83_13_ok : batch_83_13_values.all id = true := by decide

def batch_83_14_values : List Bool := [accepted_4181]
theorem batch_83_14_ok : batch_83_14_values.all id = true := by decide

def batch_83_15_values : List Bool := [accepted_4182]
theorem batch_83_15_ok : batch_83_15_values.all id = true := by decide

def batch_83_16_values : List Bool := [accepted_4186]
theorem batch_83_16_ok : batch_83_16_values.all id = true := by decide

def batch_83_17_values : List Bool := [accepted_4187]
theorem batch_83_17_ok : batch_83_17_values.all id = true := by decide

def batch_83_18_values : List Bool := [accepted_4189]
theorem batch_83_18_ok : batch_83_18_values.all id = true := by decide

def batch_83_19_values : List Bool := [accepted_4191]
theorem batch_83_19_ok : batch_83_19_values.all id = true := by decide

def batch_83_20_values : List Bool := [accepted_4192]
theorem batch_83_20_ok : batch_83_20_values.all id = true := by decide

def batch_83_21_values : List Bool := [accepted_4193]
theorem batch_83_21_ok : batch_83_21_values.all id = true := by decide

def batch_83_22_values : List Bool := [accepted_4195]
theorem batch_83_22_ok : batch_83_22_values.all id = true := by decide

def batch_83_23_values : List Bool := [accepted_4196]
theorem batch_83_23_ok : batch_83_23_values.all id = true := by decide

def batch_83_24_values : List Bool := [accepted_4199]
theorem batch_83_24_ok : batch_83_24_values.all id = true := by decide

theorem leaf_4150_ok : checkAt 527 1000 box_4150 cert_4150 = true := by
  have h := List.all_eq_true.mp batch_83_00_ok accepted_4150 (by simp [batch_83_00_values])
  exact h
theorem leaf_4150_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4150.profileLo box_4150.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4150_ok
theorem branch_box_4150_nonnegative : ∀ j, 0 ≤ branch_box_4150.lower j ∧ 0 ≤ branch_box_4150.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4150, Box.profileLo, Box.profileHi, box_4150]
theorem leaf_4150_BranchSafe : CertificateConsequences.BranchSafe branch_box_4150 := by
  left; refine ⟨branch_box_4150_nonnegative, ?_⟩
  intro z hz; exact leaf_4150_sound hz

theorem leaf_4151_ok : checkAt 527 1000 box_4151 cert_4151 = true := by
  have h := List.all_eq_true.mp batch_83_01_ok accepted_4151 (by simp [batch_83_01_values])
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

theorem leaf_4152_ok : checkAt 527 1000 box_4152 cert_4152 = true := by
  have h := List.all_eq_true.mp batch_83_02_ok accepted_4152 (by simp [batch_83_02_values])
  exact h
theorem leaf_4152_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4152.profileLo box_4152.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4152_ok
theorem branch_box_4152_nonnegative : ∀ j, 0 ≤ branch_box_4152.lower j ∧ 0 ≤ branch_box_4152.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4152, Box.profileLo, Box.profileHi, box_4152]
theorem leaf_4152_BranchSafe : CertificateConsequences.BranchSafe branch_box_4152 := by
  left; refine ⟨branch_box_4152_nonnegative, ?_⟩
  intro z hz; exact leaf_4152_sound hz

theorem leaf_4162_ok : checkAt 527 1000 box_4162 cert_4162 = true := by
  have h := List.all_eq_true.mp batch_83_03_ok accepted_4162 (by simp [batch_83_03_values])
  exact h
theorem leaf_4162_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4162.profileLo box_4162.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4162_ok
theorem branch_box_4162_nonnegative : ∀ j, 0 ≤ branch_box_4162.lower j ∧ 0 ≤ branch_box_4162.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4162, Box.profileLo, Box.profileHi, box_4162]
theorem leaf_4162_BranchSafe : CertificateConsequences.BranchSafe branch_box_4162 := by
  left; refine ⟨branch_box_4162_nonnegative, ?_⟩
  intro z hz; exact leaf_4162_sound hz

theorem leaf_4163_ok : checkAt 527 1000 box_4163 cert_4163 = true := by
  have h := List.all_eq_true.mp batch_83_04_ok accepted_4163 (by simp [batch_83_04_values])
  exact h
theorem leaf_4163_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4163.profileLo box_4163.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4163_ok
theorem branch_box_4163_nonnegative : ∀ j, 0 ≤ branch_box_4163.lower j ∧ 0 ≤ branch_box_4163.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4163, Box.profileLo, Box.profileHi, box_4163]
theorem leaf_4163_BranchSafe : CertificateConsequences.BranchSafe branch_box_4163 := by
  left; refine ⟨branch_box_4163_nonnegative, ?_⟩
  intro z hz; exact leaf_4163_sound hz

theorem leaf_4164_ok : checkAt 527 1000 box_4164 cert_4164 = true := by
  have h := List.all_eq_true.mp batch_83_05_ok accepted_4164 (by simp [batch_83_05_values])
  exact h
theorem leaf_4164_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4164.profileLo box_4164.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4164_ok
theorem branch_box_4164_nonnegative : ∀ j, 0 ≤ branch_box_4164.lower j ∧ 0 ≤ branch_box_4164.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4164, Box.profileLo, Box.profileHi, box_4164]
theorem leaf_4164_BranchSafe : CertificateConsequences.BranchSafe branch_box_4164 := by
  left; refine ⟨branch_box_4164_nonnegative, ?_⟩
  intro z hz; exact leaf_4164_sound hz

theorem leaf_4167_ok : checkAt 527 1000 box_4167 cert_4167 = true := by
  have h := List.all_eq_true.mp batch_83_06_ok accepted_4167 (by simp [batch_83_06_values])
  exact h
theorem leaf_4167_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4167.profileLo box_4167.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4167_ok
theorem branch_box_4167_nonnegative : ∀ j, 0 ≤ branch_box_4167.lower j ∧ 0 ≤ branch_box_4167.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4167, Box.profileLo, Box.profileHi, box_4167]
theorem leaf_4167_BranchSafe : CertificateConsequences.BranchSafe branch_box_4167 := by
  left; refine ⟨branch_box_4167_nonnegative, ?_⟩
  intro z hz; exact leaf_4167_sound hz

theorem leaf_4168_ok : checkAt 527 1000 box_4168 cert_4168 = true := by
  have h := List.all_eq_true.mp batch_83_07_ok accepted_4168 (by simp [batch_83_07_values])
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

theorem leaf_4169_ok : checkAt 527 1000 box_4169 cert_4169 = true := by
  have h := List.all_eq_true.mp batch_83_08_ok accepted_4169 (by simp [batch_83_08_values])
  exact h
theorem leaf_4169_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4169.profileLo box_4169.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4169_ok
theorem branch_box_4169_nonnegative : ∀ j, 0 ≤ branch_box_4169.lower j ∧ 0 ≤ branch_box_4169.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4169, Box.profileLo, Box.profileHi, box_4169]
theorem leaf_4169_BranchSafe : CertificateConsequences.BranchSafe branch_box_4169 := by
  left; refine ⟨branch_box_4169_nonnegative, ?_⟩
  intro z hz; exact leaf_4169_sound hz

theorem leaf_4171_ok : checkAt 527 1000 box_4171 cert_4171 = true := by
  have h := List.all_eq_true.mp batch_83_09_ok accepted_4171 (by simp [batch_83_09_values])
  exact h
theorem leaf_4171_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4171.profileLo box_4171.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4171_ok
theorem branch_box_4171_nonnegative : ∀ j, 0 ≤ branch_box_4171.lower j ∧ 0 ≤ branch_box_4171.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4171, Box.profileLo, Box.profileHi, box_4171]
theorem leaf_4171_BranchSafe : CertificateConsequences.BranchSafe branch_box_4171 := by
  left; refine ⟨branch_box_4171_nonnegative, ?_⟩
  intro z hz; exact leaf_4171_sound hz

theorem leaf_4172_ok : checkAt 527 1000 box_4172 cert_4172 = true := by
  have h := List.all_eq_true.mp batch_83_10_ok accepted_4172 (by simp [batch_83_10_values])
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

theorem leaf_4176_ok : checkAt 527 1000 box_4176 cert_4176 = true := by
  have h := List.all_eq_true.mp batch_83_11_ok accepted_4176 (by simp [batch_83_11_values])
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
  have h := List.all_eq_true.mp batch_83_12_ok accepted_4177 (by simp [batch_83_12_values])
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

theorem leaf_4178_ok : checkAt 527 1000 box_4178 cert_4178 = true := by
  have h := List.all_eq_true.mp batch_83_13_ok accepted_4178 (by simp [batch_83_13_values])
  exact h
theorem leaf_4178_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4178.profileLo box_4178.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4178_ok
theorem branch_box_4178_nonnegative : ∀ j, 0 ≤ branch_box_4178.lower j ∧ 0 ≤ branch_box_4178.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4178, Box.profileLo, Box.profileHi, box_4178]
theorem leaf_4178_BranchSafe : CertificateConsequences.BranchSafe branch_box_4178 := by
  left; refine ⟨branch_box_4178_nonnegative, ?_⟩
  intro z hz; exact leaf_4178_sound hz

theorem leaf_4181_ok : checkAt 527 1000 box_4181 cert_4181 = true := by
  have h := List.all_eq_true.mp batch_83_14_ok accepted_4181 (by simp [batch_83_14_values])
  exact h
theorem leaf_4181_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4181.profileLo box_4181.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4181_ok
theorem branch_box_4181_nonnegative : ∀ j, 0 ≤ branch_box_4181.lower j ∧ 0 ≤ branch_box_4181.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4181, Box.profileLo, Box.profileHi, box_4181]
theorem leaf_4181_BranchSafe : CertificateConsequences.BranchSafe branch_box_4181 := by
  left; refine ⟨branch_box_4181_nonnegative, ?_⟩
  intro z hz; exact leaf_4181_sound hz

theorem leaf_4182_ok : checkAt 527 1000 box_4182 cert_4182 = true := by
  have h := List.all_eq_true.mp batch_83_15_ok accepted_4182 (by simp [batch_83_15_values])
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

theorem leaf_4186_ok : checkAt 527 1000 box_4186 cert_4186 = true := by
  have h := List.all_eq_true.mp batch_83_16_ok accepted_4186 (by simp [batch_83_16_values])
  exact h
theorem leaf_4186_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4186.profileLo box_4186.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4186_ok
theorem branch_box_4186_nonnegative : ∀ j, 0 ≤ branch_box_4186.lower j ∧ 0 ≤ branch_box_4186.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4186, Box.profileLo, Box.profileHi, box_4186]
theorem leaf_4186_BranchSafe : CertificateConsequences.BranchSafe branch_box_4186 := by
  left; refine ⟨branch_box_4186_nonnegative, ?_⟩
  intro z hz; exact leaf_4186_sound hz

theorem leaf_4187_ok : checkAt 527 1000 box_4187 cert_4187 = true := by
  have h := List.all_eq_true.mp batch_83_17_ok accepted_4187 (by simp [batch_83_17_values])
  exact h
theorem leaf_4187_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4187.profileLo box_4187.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4187_ok
theorem branch_box_4187_nonnegative : ∀ j, 0 ≤ branch_box_4187.lower j ∧ 0 ≤ branch_box_4187.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4187, Box.profileLo, Box.profileHi, box_4187]
theorem leaf_4187_BranchSafe : CertificateConsequences.BranchSafe branch_box_4187 := by
  left; refine ⟨branch_box_4187_nonnegative, ?_⟩
  intro z hz; exact leaf_4187_sound hz

theorem leaf_4189_ok : checkAt 527 1000 box_4189 cert_4189 = true := by
  have h := List.all_eq_true.mp batch_83_18_ok accepted_4189 (by simp [batch_83_18_values])
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

theorem leaf_4191_ok : checkAt 527 1000 box_4191 cert_4191 = true := by
  have h := List.all_eq_true.mp batch_83_19_ok accepted_4191 (by simp [batch_83_19_values])
  exact h
theorem leaf_4191_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4191.profileLo box_4191.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4191_ok
theorem branch_box_4191_nonnegative : ∀ j, 0 ≤ branch_box_4191.lower j ∧ 0 ≤ branch_box_4191.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4191, Box.profileLo, Box.profileHi, box_4191]
theorem leaf_4191_BranchSafe : CertificateConsequences.BranchSafe branch_box_4191 := by
  left; refine ⟨branch_box_4191_nonnegative, ?_⟩
  intro z hz; exact leaf_4191_sound hz

theorem leaf_4192_ok : checkAt 527 1000 box_4192 cert_4192 = true := by
  have h := List.all_eq_true.mp batch_83_20_ok accepted_4192 (by simp [batch_83_20_values])
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

theorem leaf_4193_ok : checkAt 527 1000 box_4193 cert_4193 = true := by
  have h := List.all_eq_true.mp batch_83_21_ok accepted_4193 (by simp [batch_83_21_values])
  exact h
theorem leaf_4193_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4193.profileLo box_4193.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4193_ok
theorem branch_box_4193_nonnegative : ∀ j, 0 ≤ branch_box_4193.lower j ∧ 0 ≤ branch_box_4193.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4193, Box.profileLo, Box.profileHi, box_4193]
theorem leaf_4193_BranchSafe : CertificateConsequences.BranchSafe branch_box_4193 := by
  left; refine ⟨branch_box_4193_nonnegative, ?_⟩
  intro z hz; exact leaf_4193_sound hz

theorem leaf_4195_ok : checkAt 527 1000 box_4195 cert_4195 = true := by
  have h := List.all_eq_true.mp batch_83_22_ok accepted_4195 (by simp [batch_83_22_values])
  exact h
theorem leaf_4195_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4195.profileLo box_4195.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4195_ok
theorem branch_box_4195_nonnegative : ∀ j, 0 ≤ branch_box_4195.lower j ∧ 0 ≤ branch_box_4195.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4195, Box.profileLo, Box.profileHi, box_4195]
theorem leaf_4195_BranchSafe : CertificateConsequences.BranchSafe branch_box_4195 := by
  left; refine ⟨branch_box_4195_nonnegative, ?_⟩
  intro z hz; exact leaf_4195_sound hz

theorem leaf_4196_ok : checkAt 527 1000 box_4196 cert_4196 = true := by
  have h := List.all_eq_true.mp batch_83_23_ok accepted_4196 (by simp [batch_83_23_values])
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

theorem leaf_4199_ok : checkAt 527 1000 box_4199 cert_4199 = true := by
  have h := List.all_eq_true.mp batch_83_24_ok accepted_4199 (by simp [batch_83_24_values])
  exact h
theorem leaf_4199_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_4199.profileLo box_4199.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_4199_ok
theorem branch_box_4199_nonnegative : ∀ j, 0 ≤ branch_box_4199.lower j ∧ 0 ≤ branch_box_4199.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_4199, Box.profileLo, Box.profileHi, box_4199]
theorem leaf_4199_BranchSafe : CertificateConsequences.BranchSafe branch_box_4199 := by
  left; refine ⟨branch_box_4199_nonnegative, ?_⟩
  intro z hz; exact leaf_4199_sound hz

#print axioms batch_83_00_ok
#print axioms leaf_4150_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
