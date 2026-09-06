import PeaceableQueens.UpperBound.Generated.Even.C527Scaled42Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_42_00_values : List Bool := [accepted_2100]
theorem batch_42_00_ok : batch_42_00_values.all id = true := by decide

def batch_42_01_values : List Bool := [accepted_2101]
theorem batch_42_01_ok : batch_42_01_values.all id = true := by decide

def batch_42_02_values : List Bool := [accepted_2102]
theorem batch_42_02_ok : batch_42_02_values.all id = true := by decide

def batch_42_03_values : List Bool := [accepted_2112]
theorem batch_42_03_ok : batch_42_03_values.all id = true := by decide

def batch_42_04_values : List Bool := [accepted_2113]
theorem batch_42_04_ok : batch_42_04_values.all id = true := by decide

def batch_42_05_values : List Bool := [accepted_2114]
theorem batch_42_05_ok : batch_42_05_values.all id = true := by decide

def batch_42_06_values : List Bool := [accepted_2116]
theorem batch_42_06_ok : batch_42_06_values.all id = true := by decide

def batch_42_07_values : List Bool := [accepted_2117]
theorem batch_42_07_ok : batch_42_07_values.all id = true := by decide

def batch_42_08_values : List Bool := [accepted_2118]
theorem batch_42_08_ok : batch_42_08_values.all id = true := by decide

def batch_42_09_values : List Bool := [accepted_2121]
theorem batch_42_09_ok : batch_42_09_values.all id = true := by decide

def batch_42_10_values : List Bool := [accepted_2122]
theorem batch_42_10_ok : batch_42_10_values.all id = true := by decide

def batch_42_11_values : List Bool := [accepted_2123]
theorem batch_42_11_ok : batch_42_11_values.all id = true := by decide

def batch_42_12_values : List Bool := [accepted_2124]
theorem batch_42_12_ok : batch_42_12_values.all id = true := by decide

def batch_42_13_values : List Bool := [accepted_2135]
theorem batch_42_13_ok : batch_42_13_values.all id = true := by decide

def batch_42_14_values : List Bool := [accepted_2136]
theorem batch_42_14_ok : batch_42_14_values.all id = true := by decide

def batch_42_15_values : List Bool := [accepted_2141]
theorem batch_42_15_ok : batch_42_15_values.all id = true := by decide

def batch_42_16_values : List Bool := [accepted_2142]
theorem batch_42_16_ok : batch_42_16_values.all id = true := by decide

def batch_42_17_values : List Bool := [accepted_2143]
theorem batch_42_17_ok : batch_42_17_values.all id = true := by decide

def batch_42_18_values : List Bool := [accepted_2144]
theorem batch_42_18_ok : batch_42_18_values.all id = true := by decide

def batch_42_19_values : List Bool := [accepted_2145]
theorem batch_42_19_ok : batch_42_19_values.all id = true := by decide

def batch_42_20_values : List Bool := [accepted_2146]
theorem batch_42_20_ok : batch_42_20_values.all id = true := by decide

def batch_42_21_values : List Bool := [accepted_2147]
theorem batch_42_21_ok : batch_42_21_values.all id = true := by decide

def batch_42_22_values : List Bool := [accepted_2149]
theorem batch_42_22_ok : batch_42_22_values.all id = true := by decide

theorem leaf_2100_ok : checkAt 527 1000 box_2100 cert_2100 = true := by
  have h := List.all_eq_true.mp batch_42_00_ok accepted_2100 (by simp [batch_42_00_values])
  exact h
theorem leaf_2100_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2100.profileLo box_2100.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2100_ok
theorem branch_box_2100_nonnegative : ∀ j, 0 ≤ branch_box_2100.lower j ∧ 0 ≤ branch_box_2100.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2100, Box.profileLo, Box.profileHi, box_2100]
theorem leaf_2100_BranchSafe : CertificateConsequences.BranchSafe branch_box_2100 := by
  left; refine ⟨branch_box_2100_nonnegative, ?_⟩
  intro z hz; exact leaf_2100_sound hz

theorem leaf_2101_ok : checkAt 527 1000 box_2101 cert_2101 = true := by
  have h := List.all_eq_true.mp batch_42_01_ok accepted_2101 (by simp [batch_42_01_values])
  exact h
theorem leaf_2101_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2101.profileLo box_2101.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2101_ok
theorem branch_box_2101_nonnegative : ∀ j, 0 ≤ branch_box_2101.lower j ∧ 0 ≤ branch_box_2101.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2101, Box.profileLo, Box.profileHi, box_2101]
theorem leaf_2101_BranchSafe : CertificateConsequences.BranchSafe branch_box_2101 := by
  left; refine ⟨branch_box_2101_nonnegative, ?_⟩
  intro z hz; exact leaf_2101_sound hz

theorem leaf_2102_ok : checkAt 527 1000 box_2102 cert_2102 = true := by
  have h := List.all_eq_true.mp batch_42_02_ok accepted_2102 (by simp [batch_42_02_values])
  exact h
theorem leaf_2102_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2102.profileLo box_2102.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2102_ok
theorem branch_box_2102_nonnegative : ∀ j, 0 ≤ branch_box_2102.lower j ∧ 0 ≤ branch_box_2102.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2102, Box.profileLo, Box.profileHi, box_2102]
theorem leaf_2102_BranchSafe : CertificateConsequences.BranchSafe branch_box_2102 := by
  left; refine ⟨branch_box_2102_nonnegative, ?_⟩
  intro z hz; exact leaf_2102_sound hz

theorem leaf_2112_ok : checkAt 527 1000 box_2112 cert_2112 = true := by
  have h := List.all_eq_true.mp batch_42_03_ok accepted_2112 (by simp [batch_42_03_values])
  exact h
theorem leaf_2112_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2112.profileLo box_2112.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2112_ok
theorem branch_box_2112_nonnegative : ∀ j, 0 ≤ branch_box_2112.lower j ∧ 0 ≤ branch_box_2112.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2112, Box.profileLo, Box.profileHi, box_2112]
theorem leaf_2112_BranchSafe : CertificateConsequences.BranchSafe branch_box_2112 := by
  left; refine ⟨branch_box_2112_nonnegative, ?_⟩
  intro z hz; exact leaf_2112_sound hz

theorem leaf_2113_ok : checkAt 527 1000 box_2113 cert_2113 = true := by
  have h := List.all_eq_true.mp batch_42_04_ok accepted_2113 (by simp [batch_42_04_values])
  exact h
theorem leaf_2113_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2113.profileLo box_2113.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2113_ok
theorem branch_box_2113_nonnegative : ∀ j, 0 ≤ branch_box_2113.lower j ∧ 0 ≤ branch_box_2113.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2113, Box.profileLo, Box.profileHi, box_2113]
theorem leaf_2113_BranchSafe : CertificateConsequences.BranchSafe branch_box_2113 := by
  left; refine ⟨branch_box_2113_nonnegative, ?_⟩
  intro z hz; exact leaf_2113_sound hz

theorem leaf_2114_ok : checkAt 527 1000 box_2114 cert_2114 = true := by
  have h := List.all_eq_true.mp batch_42_05_ok accepted_2114 (by simp [batch_42_05_values])
  exact h
theorem leaf_2114_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2114.profileLo box_2114.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2114_ok
theorem branch_box_2114_nonnegative : ∀ j, 0 ≤ branch_box_2114.lower j ∧ 0 ≤ branch_box_2114.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2114, Box.profileLo, Box.profileHi, box_2114]
theorem leaf_2114_BranchSafe : CertificateConsequences.BranchSafe branch_box_2114 := by
  left; refine ⟨branch_box_2114_nonnegative, ?_⟩
  intro z hz; exact leaf_2114_sound hz

theorem leaf_2116_ok : checkAt 527 1000 box_2116 cert_2116 = true := by
  have h := List.all_eq_true.mp batch_42_06_ok accepted_2116 (by simp [batch_42_06_values])
  exact h
theorem leaf_2116_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2116.profileLo box_2116.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2116_ok
theorem branch_box_2116_nonnegative : ∀ j, 0 ≤ branch_box_2116.lower j ∧ 0 ≤ branch_box_2116.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2116, Box.profileLo, Box.profileHi, box_2116]
theorem leaf_2116_BranchSafe : CertificateConsequences.BranchSafe branch_box_2116 := by
  left; refine ⟨branch_box_2116_nonnegative, ?_⟩
  intro z hz; exact leaf_2116_sound hz

theorem leaf_2117_ok : checkAt 527 1000 box_2117 cert_2117 = true := by
  have h := List.all_eq_true.mp batch_42_07_ok accepted_2117 (by simp [batch_42_07_values])
  exact h
theorem leaf_2117_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2117.profileLo box_2117.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2117_ok
theorem branch_box_2117_nonnegative : ∀ j, 0 ≤ branch_box_2117.lower j ∧ 0 ≤ branch_box_2117.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2117, Box.profileLo, Box.profileHi, box_2117]
theorem leaf_2117_BranchSafe : CertificateConsequences.BranchSafe branch_box_2117 := by
  left; refine ⟨branch_box_2117_nonnegative, ?_⟩
  intro z hz; exact leaf_2117_sound hz

theorem leaf_2118_ok : checkAt 527 1000 box_2118 cert_2118 = true := by
  have h := List.all_eq_true.mp batch_42_08_ok accepted_2118 (by simp [batch_42_08_values])
  exact h
theorem leaf_2118_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2118.profileLo box_2118.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2118_ok
theorem branch_box_2118_nonnegative : ∀ j, 0 ≤ branch_box_2118.lower j ∧ 0 ≤ branch_box_2118.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2118, Box.profileLo, Box.profileHi, box_2118]
theorem leaf_2118_BranchSafe : CertificateConsequences.BranchSafe branch_box_2118 := by
  left; refine ⟨branch_box_2118_nonnegative, ?_⟩
  intro z hz; exact leaf_2118_sound hz

theorem leaf_2121_ok : checkAt 527 1000 box_2121 cert_2121 = true := by
  have h := List.all_eq_true.mp batch_42_09_ok accepted_2121 (by simp [batch_42_09_values])
  exact h
theorem leaf_2121_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2121.profileLo box_2121.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2121_ok
theorem branch_box_2121_nonnegative : ∀ j, 0 ≤ branch_box_2121.lower j ∧ 0 ≤ branch_box_2121.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2121, Box.profileLo, Box.profileHi, box_2121]
theorem leaf_2121_BranchSafe : CertificateConsequences.BranchSafe branch_box_2121 := by
  left; refine ⟨branch_box_2121_nonnegative, ?_⟩
  intro z hz; exact leaf_2121_sound hz

theorem leaf_2122_ok : checkAt 527 1000 box_2122 cert_2122 = true := by
  have h := List.all_eq_true.mp batch_42_10_ok accepted_2122 (by simp [batch_42_10_values])
  exact h
theorem leaf_2122_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2122.profileLo box_2122.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2122_ok
theorem branch_box_2122_nonnegative : ∀ j, 0 ≤ branch_box_2122.lower j ∧ 0 ≤ branch_box_2122.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2122, Box.profileLo, Box.profileHi, box_2122]
theorem leaf_2122_BranchSafe : CertificateConsequences.BranchSafe branch_box_2122 := by
  left; refine ⟨branch_box_2122_nonnegative, ?_⟩
  intro z hz; exact leaf_2122_sound hz

theorem leaf_2123_ok : checkAt 527 1000 box_2123 cert_2123 = true := by
  have h := List.all_eq_true.mp batch_42_11_ok accepted_2123 (by simp [batch_42_11_values])
  exact h
theorem leaf_2123_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2123.profileLo box_2123.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2123_ok
theorem branch_box_2123_nonnegative : ∀ j, 0 ≤ branch_box_2123.lower j ∧ 0 ≤ branch_box_2123.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2123, Box.profileLo, Box.profileHi, box_2123]
theorem leaf_2123_BranchSafe : CertificateConsequences.BranchSafe branch_box_2123 := by
  left; refine ⟨branch_box_2123_nonnegative, ?_⟩
  intro z hz; exact leaf_2123_sound hz

theorem leaf_2124_ok : checkAt 527 1000 box_2124 cert_2124 = true := by
  have h := List.all_eq_true.mp batch_42_12_ok accepted_2124 (by simp [batch_42_12_values])
  exact h
theorem leaf_2124_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2124.profileLo box_2124.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2124_ok
theorem branch_box_2124_nonnegative : ∀ j, 0 ≤ branch_box_2124.lower j ∧ 0 ≤ branch_box_2124.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2124, Box.profileLo, Box.profileHi, box_2124]
theorem leaf_2124_BranchSafe : CertificateConsequences.BranchSafe branch_box_2124 := by
  left; refine ⟨branch_box_2124_nonnegative, ?_⟩
  intro z hz; exact leaf_2124_sound hz

theorem leaf_2135_ok : checkAt 527 1000 box_2135 cert_2135 = true := by
  have h := List.all_eq_true.mp batch_42_13_ok accepted_2135 (by simp [batch_42_13_values])
  exact h
theorem leaf_2135_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2135.profileLo box_2135.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2135_ok
theorem branch_box_2135_nonnegative : ∀ j, 0 ≤ branch_box_2135.lower j ∧ 0 ≤ branch_box_2135.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2135, Box.profileLo, Box.profileHi, box_2135]
theorem leaf_2135_BranchSafe : CertificateConsequences.BranchSafe branch_box_2135 := by
  left; refine ⟨branch_box_2135_nonnegative, ?_⟩
  intro z hz; exact leaf_2135_sound hz

theorem leaf_2136_ok : checkAt 527 1000 box_2136 cert_2136 = true := by
  have h := List.all_eq_true.mp batch_42_14_ok accepted_2136 (by simp [batch_42_14_values])
  exact h
theorem leaf_2136_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2136.profileLo box_2136.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2136_ok
theorem branch_box_2136_nonnegative : ∀ j, 0 ≤ branch_box_2136.lower j ∧ 0 ≤ branch_box_2136.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2136, Box.profileLo, Box.profileHi, box_2136]
theorem leaf_2136_BranchSafe : CertificateConsequences.BranchSafe branch_box_2136 := by
  left; refine ⟨branch_box_2136_nonnegative, ?_⟩
  intro z hz; exact leaf_2136_sound hz

theorem leaf_2141_ok : checkAt 527 1000 box_2141 cert_2141 = true := by
  have h := List.all_eq_true.mp batch_42_15_ok accepted_2141 (by simp [batch_42_15_values])
  exact h
theorem leaf_2141_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2141.profileLo box_2141.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2141_ok
theorem branch_box_2141_nonnegative : ∀ j, 0 ≤ branch_box_2141.lower j ∧ 0 ≤ branch_box_2141.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2141, Box.profileLo, Box.profileHi, box_2141]
theorem leaf_2141_BranchSafe : CertificateConsequences.BranchSafe branch_box_2141 := by
  left; refine ⟨branch_box_2141_nonnegative, ?_⟩
  intro z hz; exact leaf_2141_sound hz

theorem leaf_2142_ok : checkAt 527 1000 box_2142 cert_2142 = true := by
  have h := List.all_eq_true.mp batch_42_16_ok accepted_2142 (by simp [batch_42_16_values])
  exact h
theorem leaf_2142_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2142.profileLo box_2142.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2142_ok
theorem branch_box_2142_nonnegative : ∀ j, 0 ≤ branch_box_2142.lower j ∧ 0 ≤ branch_box_2142.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2142, Box.profileLo, Box.profileHi, box_2142]
theorem leaf_2142_BranchSafe : CertificateConsequences.BranchSafe branch_box_2142 := by
  left; refine ⟨branch_box_2142_nonnegative, ?_⟩
  intro z hz; exact leaf_2142_sound hz

theorem leaf_2143_ok : checkAt 527 1000 box_2143 cert_2143 = true := by
  have h := List.all_eq_true.mp batch_42_17_ok accepted_2143 (by simp [batch_42_17_values])
  exact h
theorem leaf_2143_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2143.profileLo box_2143.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2143_ok
theorem branch_box_2143_nonnegative : ∀ j, 0 ≤ branch_box_2143.lower j ∧ 0 ≤ branch_box_2143.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2143, Box.profileLo, Box.profileHi, box_2143]
theorem leaf_2143_BranchSafe : CertificateConsequences.BranchSafe branch_box_2143 := by
  left; refine ⟨branch_box_2143_nonnegative, ?_⟩
  intro z hz; exact leaf_2143_sound hz

theorem leaf_2144_ok : checkAt 527 1000 box_2144 cert_2144 = true := by
  have h := List.all_eq_true.mp batch_42_18_ok accepted_2144 (by simp [batch_42_18_values])
  exact h
theorem leaf_2144_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2144.profileLo box_2144.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2144_ok
theorem branch_box_2144_nonnegative : ∀ j, 0 ≤ branch_box_2144.lower j ∧ 0 ≤ branch_box_2144.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2144, Box.profileLo, Box.profileHi, box_2144]
theorem leaf_2144_BranchSafe : CertificateConsequences.BranchSafe branch_box_2144 := by
  left; refine ⟨branch_box_2144_nonnegative, ?_⟩
  intro z hz; exact leaf_2144_sound hz

theorem leaf_2145_ok : checkAt 527 1000 box_2145 cert_2145 = true := by
  have h := List.all_eq_true.mp batch_42_19_ok accepted_2145 (by simp [batch_42_19_values])
  exact h
theorem leaf_2145_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2145.profileLo box_2145.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2145_ok
theorem branch_box_2145_nonnegative : ∀ j, 0 ≤ branch_box_2145.lower j ∧ 0 ≤ branch_box_2145.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2145, Box.profileLo, Box.profileHi, box_2145]
theorem leaf_2145_BranchSafe : CertificateConsequences.BranchSafe branch_box_2145 := by
  left; refine ⟨branch_box_2145_nonnegative, ?_⟩
  intro z hz; exact leaf_2145_sound hz

theorem leaf_2146_ok : checkAt 527 1000 box_2146 cert_2146 = true := by
  have h := List.all_eq_true.mp batch_42_20_ok accepted_2146 (by simp [batch_42_20_values])
  exact h
theorem leaf_2146_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2146.profileLo box_2146.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2146_ok
theorem branch_box_2146_nonnegative : ∀ j, 0 ≤ branch_box_2146.lower j ∧ 0 ≤ branch_box_2146.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2146, Box.profileLo, Box.profileHi, box_2146]
theorem leaf_2146_BranchSafe : CertificateConsequences.BranchSafe branch_box_2146 := by
  left; refine ⟨branch_box_2146_nonnegative, ?_⟩
  intro z hz; exact leaf_2146_sound hz

theorem leaf_2147_ok : checkAt 527 1000 box_2147 cert_2147 = true := by
  have h := List.all_eq_true.mp batch_42_21_ok accepted_2147 (by simp [batch_42_21_values])
  exact h
theorem leaf_2147_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2147.profileLo box_2147.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2147_ok
theorem branch_box_2147_nonnegative : ∀ j, 0 ≤ branch_box_2147.lower j ∧ 0 ≤ branch_box_2147.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2147, Box.profileLo, Box.profileHi, box_2147]
theorem leaf_2147_BranchSafe : CertificateConsequences.BranchSafe branch_box_2147 := by
  left; refine ⟨branch_box_2147_nonnegative, ?_⟩
  intro z hz; exact leaf_2147_sound hz

theorem leaf_2149_ok : checkAt 527 1000 box_2149 cert_2149 = true := by
  have h := List.all_eq_true.mp batch_42_22_ok accepted_2149 (by simp [batch_42_22_values])
  exact h
theorem leaf_2149_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2149.profileLo box_2149.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2149_ok
theorem branch_box_2149_nonnegative : ∀ j, 0 ≤ branch_box_2149.lower j ∧ 0 ≤ branch_box_2149.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2149, Box.profileLo, Box.profileHi, box_2149]
theorem leaf_2149_BranchSafe : CertificateConsequences.BranchSafe branch_box_2149 := by
  left; refine ⟨branch_box_2149_nonnegative, ?_⟩
  intro z hz; exact leaf_2149_sound hz

#print axioms batch_42_00_ok
#print axioms leaf_2100_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
