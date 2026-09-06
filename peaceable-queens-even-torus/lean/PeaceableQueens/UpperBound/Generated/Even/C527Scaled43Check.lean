import PeaceableQueens.UpperBound.Generated.Even.C527Scaled43Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_43_00_values : List Bool := [accepted_2150]
theorem batch_43_00_ok : batch_43_00_values.all id = true := by decide

def batch_43_01_values : List Bool := [accepted_2151]
theorem batch_43_01_ok : batch_43_01_values.all id = true := by decide

def batch_43_02_values : List Bool := [accepted_2156]
theorem batch_43_02_ok : batch_43_02_values.all id = true := by decide

def batch_43_03_values : List Bool := [accepted_2157]
theorem batch_43_03_ok : batch_43_03_values.all id = true := by decide

def batch_43_04_values : List Bool := [accepted_2158]
theorem batch_43_04_ok : batch_43_04_values.all id = true := by decide

def batch_43_05_values : List Bool := [accepted_2159]
theorem batch_43_05_ok : batch_43_05_values.all id = true := by decide

def batch_43_06_values : List Bool := [accepted_2160]
theorem batch_43_06_ok : batch_43_06_values.all id = true := by decide

def batch_43_07_values : List Bool := [accepted_2165]
theorem batch_43_07_ok : batch_43_07_values.all id = true := by decide

def batch_43_08_values : List Bool := [accepted_2167]
theorem batch_43_08_ok : batch_43_08_values.all id = true := by decide

def batch_43_09_values : List Bool := [accepted_2169]
theorem batch_43_09_ok : batch_43_09_values.all id = true := by decide

def batch_43_10_values : List Bool := [accepted_2170]
theorem batch_43_10_ok : batch_43_10_values.all id = true := by decide

def batch_43_11_values : List Bool := [accepted_2171]
theorem batch_43_11_ok : batch_43_11_values.all id = true := by decide

def batch_43_12_values : List Bool := [accepted_2172]
theorem batch_43_12_ok : batch_43_12_values.all id = true := by decide

def batch_43_13_values : List Bool := [accepted_2174]
theorem batch_43_13_ok : batch_43_13_values.all id = true := by decide

def batch_43_14_values : List Bool := [accepted_2175]
theorem batch_43_14_ok : batch_43_14_values.all id = true := by decide

def batch_43_15_values : List Bool := [accepted_2176]
theorem batch_43_15_ok : batch_43_15_values.all id = true := by decide

def batch_43_16_values : List Bool := [accepted_2182]
theorem batch_43_16_ok : batch_43_16_values.all id = true := by decide

def batch_43_17_values : List Bool := [accepted_2184]
theorem batch_43_17_ok : batch_43_17_values.all id = true := by decide

def batch_43_18_values : List Bool := [accepted_2185]
theorem batch_43_18_ok : batch_43_18_values.all id = true := by decide

def batch_43_19_values : List Bool := [accepted_2186]
theorem batch_43_19_ok : batch_43_19_values.all id = true := by decide

def batch_43_20_values : List Bool := [accepted_2188]
theorem batch_43_20_ok : batch_43_20_values.all id = true := by decide

def batch_43_21_values : List Bool := [accepted_2189]
theorem batch_43_21_ok : batch_43_21_values.all id = true := by decide

def batch_43_22_values : List Bool := [accepted_2190]
theorem batch_43_22_ok : batch_43_22_values.all id = true := by decide

def batch_43_23_values : List Bool := [accepted_2191]
theorem batch_43_23_ok : batch_43_23_values.all id = true := by decide

def batch_43_24_values : List Bool := [accepted_2193]
theorem batch_43_24_ok : batch_43_24_values.all id = true := by decide

def batch_43_25_values : List Bool := [accepted_2194]
theorem batch_43_25_ok : batch_43_25_values.all id = true := by decide

theorem leaf_2150_ok : checkAt 527 1000 box_2150 cert_2150 = true := by
  have h := List.all_eq_true.mp batch_43_00_ok accepted_2150 (by simp [batch_43_00_values])
  exact h
theorem leaf_2150_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2150.profileLo box_2150.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2150_ok
theorem branch_box_2150_nonnegative : ∀ j, 0 ≤ branch_box_2150.lower j ∧ 0 ≤ branch_box_2150.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2150, Box.profileLo, Box.profileHi, box_2150]
theorem leaf_2150_BranchSafe : CertificateConsequences.BranchSafe branch_box_2150 := by
  left; refine ⟨branch_box_2150_nonnegative, ?_⟩
  intro z hz; exact leaf_2150_sound hz

theorem leaf_2151_ok : checkAt 527 1000 box_2151 cert_2151 = true := by
  have h := List.all_eq_true.mp batch_43_01_ok accepted_2151 (by simp [batch_43_01_values])
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
  have h := List.all_eq_true.mp batch_43_02_ok accepted_2156 (by simp [batch_43_02_values])
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

theorem leaf_2157_ok : checkAt 527 1000 box_2157 cert_2157 = true := by
  have h := List.all_eq_true.mp batch_43_03_ok accepted_2157 (by simp [batch_43_03_values])
  exact h
theorem leaf_2157_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2157.profileLo box_2157.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2157_ok
theorem branch_box_2157_nonnegative : ∀ j, 0 ≤ branch_box_2157.lower j ∧ 0 ≤ branch_box_2157.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2157, Box.profileLo, Box.profileHi, box_2157]
theorem leaf_2157_BranchSafe : CertificateConsequences.BranchSafe branch_box_2157 := by
  left; refine ⟨branch_box_2157_nonnegative, ?_⟩
  intro z hz; exact leaf_2157_sound hz

theorem leaf_2158_ok : checkAt 527 1000 box_2158 cert_2158 = true := by
  have h := List.all_eq_true.mp batch_43_04_ok accepted_2158 (by simp [batch_43_04_values])
  exact h
theorem leaf_2158_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2158.profileLo box_2158.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2158_ok
theorem branch_box_2158_nonnegative : ∀ j, 0 ≤ branch_box_2158.lower j ∧ 0 ≤ branch_box_2158.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2158, Box.profileLo, Box.profileHi, box_2158]
theorem leaf_2158_BranchSafe : CertificateConsequences.BranchSafe branch_box_2158 := by
  left; refine ⟨branch_box_2158_nonnegative, ?_⟩
  intro z hz; exact leaf_2158_sound hz

theorem leaf_2159_ok : checkAt 527 1000 box_2159 cert_2159 = true := by
  have h := List.all_eq_true.mp batch_43_05_ok accepted_2159 (by simp [batch_43_05_values])
  exact h
theorem leaf_2159_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2159.profileLo box_2159.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2159_ok
theorem branch_box_2159_nonnegative : ∀ j, 0 ≤ branch_box_2159.lower j ∧ 0 ≤ branch_box_2159.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2159, Box.profileLo, Box.profileHi, box_2159]
theorem leaf_2159_BranchSafe : CertificateConsequences.BranchSafe branch_box_2159 := by
  left; refine ⟨branch_box_2159_nonnegative, ?_⟩
  intro z hz; exact leaf_2159_sound hz

theorem leaf_2160_ok : checkAt 527 1000 box_2160 cert_2160 = true := by
  have h := List.all_eq_true.mp batch_43_06_ok accepted_2160 (by simp [batch_43_06_values])
  exact h
theorem leaf_2160_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2160.profileLo box_2160.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2160_ok
theorem branch_box_2160_nonnegative : ∀ j, 0 ≤ branch_box_2160.lower j ∧ 0 ≤ branch_box_2160.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2160, Box.profileLo, Box.profileHi, box_2160]
theorem leaf_2160_BranchSafe : CertificateConsequences.BranchSafe branch_box_2160 := by
  left; refine ⟨branch_box_2160_nonnegative, ?_⟩
  intro z hz; exact leaf_2160_sound hz

theorem leaf_2165_ok : checkAt 527 1000 box_2165 cert_2165 = true := by
  have h := List.all_eq_true.mp batch_43_07_ok accepted_2165 (by simp [batch_43_07_values])
  exact h
theorem leaf_2165_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2165.profileLo box_2165.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2165_ok
theorem branch_box_2165_nonnegative : ∀ j, 0 ≤ branch_box_2165.lower j ∧ 0 ≤ branch_box_2165.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2165, Box.profileLo, Box.profileHi, box_2165]
theorem leaf_2165_BranchSafe : CertificateConsequences.BranchSafe branch_box_2165 := by
  left; refine ⟨branch_box_2165_nonnegative, ?_⟩
  intro z hz; exact leaf_2165_sound hz

theorem leaf_2167_ok : checkAt 527 1000 box_2167 cert_2167 = true := by
  have h := List.all_eq_true.mp batch_43_08_ok accepted_2167 (by simp [batch_43_08_values])
  exact h
theorem leaf_2167_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2167.profileLo box_2167.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2167_ok
theorem branch_box_2167_nonnegative : ∀ j, 0 ≤ branch_box_2167.lower j ∧ 0 ≤ branch_box_2167.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2167, Box.profileLo, Box.profileHi, box_2167]
theorem leaf_2167_BranchSafe : CertificateConsequences.BranchSafe branch_box_2167 := by
  left; refine ⟨branch_box_2167_nonnegative, ?_⟩
  intro z hz; exact leaf_2167_sound hz

theorem leaf_2169_ok : checkAt 527 1000 box_2169 cert_2169 = true := by
  have h := List.all_eq_true.mp batch_43_09_ok accepted_2169 (by simp [batch_43_09_values])
  exact h
theorem leaf_2169_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2169.profileLo box_2169.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2169_ok
theorem branch_box_2169_nonnegative : ∀ j, 0 ≤ branch_box_2169.lower j ∧ 0 ≤ branch_box_2169.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2169, Box.profileLo, Box.profileHi, box_2169]
theorem leaf_2169_BranchSafe : CertificateConsequences.BranchSafe branch_box_2169 := by
  left; refine ⟨branch_box_2169_nonnegative, ?_⟩
  intro z hz; exact leaf_2169_sound hz

theorem leaf_2170_ok : checkAt 527 1000 box_2170 cert_2170 = true := by
  have h := List.all_eq_true.mp batch_43_10_ok accepted_2170 (by simp [batch_43_10_values])
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

theorem leaf_2171_ok : checkAt 527 1000 box_2171 cert_2171 = true := by
  have h := List.all_eq_true.mp batch_43_11_ok accepted_2171 (by simp [batch_43_11_values])
  exact h
theorem leaf_2171_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2171.profileLo box_2171.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2171_ok
theorem branch_box_2171_nonnegative : ∀ j, 0 ≤ branch_box_2171.lower j ∧ 0 ≤ branch_box_2171.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2171, Box.profileLo, Box.profileHi, box_2171]
theorem leaf_2171_BranchSafe : CertificateConsequences.BranchSafe branch_box_2171 := by
  left; refine ⟨branch_box_2171_nonnegative, ?_⟩
  intro z hz; exact leaf_2171_sound hz

theorem leaf_2172_ok : checkAt 527 1000 box_2172 cert_2172 = true := by
  have h := List.all_eq_true.mp batch_43_12_ok accepted_2172 (by simp [batch_43_12_values])
  exact h
theorem leaf_2172_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2172.profileLo box_2172.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2172_ok
theorem branch_box_2172_nonnegative : ∀ j, 0 ≤ branch_box_2172.lower j ∧ 0 ≤ branch_box_2172.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2172, Box.profileLo, Box.profileHi, box_2172]
theorem leaf_2172_BranchSafe : CertificateConsequences.BranchSafe branch_box_2172 := by
  left; refine ⟨branch_box_2172_nonnegative, ?_⟩
  intro z hz; exact leaf_2172_sound hz

theorem leaf_2174_ok : checkAt 527 1000 box_2174 cert_2174 = true := by
  have h := List.all_eq_true.mp batch_43_13_ok accepted_2174 (by simp [batch_43_13_values])
  exact h
theorem leaf_2174_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2174.profileLo box_2174.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2174_ok
theorem branch_box_2174_nonnegative : ∀ j, 0 ≤ branch_box_2174.lower j ∧ 0 ≤ branch_box_2174.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2174, Box.profileLo, Box.profileHi, box_2174]
theorem leaf_2174_BranchSafe : CertificateConsequences.BranchSafe branch_box_2174 := by
  left; refine ⟨branch_box_2174_nonnegative, ?_⟩
  intro z hz; exact leaf_2174_sound hz

theorem leaf_2175_ok : checkAt 527 1000 box_2175 cert_2175 = true := by
  have h := List.all_eq_true.mp batch_43_14_ok accepted_2175 (by simp [batch_43_14_values])
  exact h
theorem leaf_2175_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2175.profileLo box_2175.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2175_ok
theorem branch_box_2175_nonnegative : ∀ j, 0 ≤ branch_box_2175.lower j ∧ 0 ≤ branch_box_2175.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2175, Box.profileLo, Box.profileHi, box_2175]
theorem leaf_2175_BranchSafe : CertificateConsequences.BranchSafe branch_box_2175 := by
  left; refine ⟨branch_box_2175_nonnegative, ?_⟩
  intro z hz; exact leaf_2175_sound hz

theorem leaf_2176_ok : checkAt 527 1000 box_2176 cert_2176 = true := by
  have h := List.all_eq_true.mp batch_43_15_ok accepted_2176 (by simp [batch_43_15_values])
  exact h
theorem leaf_2176_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2176.profileLo box_2176.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2176_ok
theorem branch_box_2176_nonnegative : ∀ j, 0 ≤ branch_box_2176.lower j ∧ 0 ≤ branch_box_2176.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2176, Box.profileLo, Box.profileHi, box_2176]
theorem leaf_2176_BranchSafe : CertificateConsequences.BranchSafe branch_box_2176 := by
  left; refine ⟨branch_box_2176_nonnegative, ?_⟩
  intro z hz; exact leaf_2176_sound hz

theorem leaf_2182_ok : checkAt 527 1000 box_2182 cert_2182 = true := by
  have h := List.all_eq_true.mp batch_43_16_ok accepted_2182 (by simp [batch_43_16_values])
  exact h
theorem leaf_2182_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2182.profileLo box_2182.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2182_ok
theorem branch_box_2182_nonnegative : ∀ j, 0 ≤ branch_box_2182.lower j ∧ 0 ≤ branch_box_2182.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2182, Box.profileLo, Box.profileHi, box_2182]
theorem leaf_2182_BranchSafe : CertificateConsequences.BranchSafe branch_box_2182 := by
  left; refine ⟨branch_box_2182_nonnegative, ?_⟩
  intro z hz; exact leaf_2182_sound hz

theorem leaf_2184_ok : checkAt 527 1000 box_2184 cert_2184 = true := by
  have h := List.all_eq_true.mp batch_43_17_ok accepted_2184 (by simp [batch_43_17_values])
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

theorem leaf_2185_ok : checkAt 527 1000 box_2185 cert_2185 = true := by
  have h := List.all_eq_true.mp batch_43_18_ok accepted_2185 (by simp [batch_43_18_values])
  exact h
theorem leaf_2185_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2185.profileLo box_2185.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2185_ok
theorem branch_box_2185_nonnegative : ∀ j, 0 ≤ branch_box_2185.lower j ∧ 0 ≤ branch_box_2185.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2185, Box.profileLo, Box.profileHi, box_2185]
theorem leaf_2185_BranchSafe : CertificateConsequences.BranchSafe branch_box_2185 := by
  left; refine ⟨branch_box_2185_nonnegative, ?_⟩
  intro z hz; exact leaf_2185_sound hz

theorem leaf_2186_ok : checkAt 527 1000 box_2186 cert_2186 = true := by
  have h := List.all_eq_true.mp batch_43_19_ok accepted_2186 (by simp [batch_43_19_values])
  exact h
theorem leaf_2186_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2186.profileLo box_2186.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2186_ok
theorem branch_box_2186_nonnegative : ∀ j, 0 ≤ branch_box_2186.lower j ∧ 0 ≤ branch_box_2186.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2186, Box.profileLo, Box.profileHi, box_2186]
theorem leaf_2186_BranchSafe : CertificateConsequences.BranchSafe branch_box_2186 := by
  left; refine ⟨branch_box_2186_nonnegative, ?_⟩
  intro z hz; exact leaf_2186_sound hz

theorem leaf_2188_ok : checkAt 527 1000 box_2188 cert_2188 = true := by
  have h := List.all_eq_true.mp batch_43_20_ok accepted_2188 (by simp [batch_43_20_values])
  exact h
theorem leaf_2188_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2188.profileLo box_2188.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2188_ok
theorem branch_box_2188_nonnegative : ∀ j, 0 ≤ branch_box_2188.lower j ∧ 0 ≤ branch_box_2188.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2188, Box.profileLo, Box.profileHi, box_2188]
theorem leaf_2188_BranchSafe : CertificateConsequences.BranchSafe branch_box_2188 := by
  left; refine ⟨branch_box_2188_nonnegative, ?_⟩
  intro z hz; exact leaf_2188_sound hz

theorem leaf_2189_ok : checkAt 527 1000 box_2189 cert_2189 = true := by
  have h := List.all_eq_true.mp batch_43_21_ok accepted_2189 (by simp [batch_43_21_values])
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

theorem leaf_2190_ok : checkAt 527 1000 box_2190 cert_2190 = true := by
  have h := List.all_eq_true.mp batch_43_22_ok accepted_2190 (by simp [batch_43_22_values])
  exact h
theorem leaf_2190_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2190.profileLo box_2190.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2190_ok
theorem branch_box_2190_nonnegative : ∀ j, 0 ≤ branch_box_2190.lower j ∧ 0 ≤ branch_box_2190.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2190, Box.profileLo, Box.profileHi, box_2190]
theorem leaf_2190_BranchSafe : CertificateConsequences.BranchSafe branch_box_2190 := by
  left; refine ⟨branch_box_2190_nonnegative, ?_⟩
  intro z hz; exact leaf_2190_sound hz

theorem leaf_2191_ok : checkAt 527 1000 box_2191 cert_2191 = true := by
  have h := List.all_eq_true.mp batch_43_23_ok accepted_2191 (by simp [batch_43_23_values])
  exact h
theorem leaf_2191_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2191.profileLo box_2191.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2191_ok
theorem branch_box_2191_nonnegative : ∀ j, 0 ≤ branch_box_2191.lower j ∧ 0 ≤ branch_box_2191.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2191, Box.profileLo, Box.profileHi, box_2191]
theorem leaf_2191_BranchSafe : CertificateConsequences.BranchSafe branch_box_2191 := by
  left; refine ⟨branch_box_2191_nonnegative, ?_⟩
  intro z hz; exact leaf_2191_sound hz

theorem leaf_2193_ok : checkAt 527 1000 box_2193 cert_2193 = true := by
  have h := List.all_eq_true.mp batch_43_24_ok accepted_2193 (by simp [batch_43_24_values])
  exact h
theorem leaf_2193_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2193.profileLo box_2193.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2193_ok
theorem branch_box_2193_nonnegative : ∀ j, 0 ≤ branch_box_2193.lower j ∧ 0 ≤ branch_box_2193.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2193, Box.profileLo, Box.profileHi, box_2193]
theorem leaf_2193_BranchSafe : CertificateConsequences.BranchSafe branch_box_2193 := by
  left; refine ⟨branch_box_2193_nonnegative, ?_⟩
  intro z hz; exact leaf_2193_sound hz

theorem leaf_2194_ok : checkAt 527 1000 box_2194 cert_2194 = true := by
  have h := List.all_eq_true.mp batch_43_25_ok accepted_2194 (by simp [batch_43_25_values])
  exact h
theorem leaf_2194_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2194.profileLo box_2194.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2194_ok
theorem branch_box_2194_nonnegative : ∀ j, 0 ≤ branch_box_2194.lower j ∧ 0 ≤ branch_box_2194.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2194, Box.profileLo, Box.profileHi, box_2194]
theorem leaf_2194_BranchSafe : CertificateConsequences.BranchSafe branch_box_2194 := by
  left; refine ⟨branch_box_2194_nonnegative, ?_⟩
  intro z hz; exact leaf_2194_sound hz

#print axioms batch_43_00_ok
#print axioms leaf_2150_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
