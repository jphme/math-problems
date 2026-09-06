import PeaceableQueens.UpperBound.Generated.Even.CoreScaled42Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_42_00_values : List Bool := [accepted_2101]
theorem batch_42_00_ok : batch_42_00_values.all id = true := by decide

def batch_42_01_values : List Bool := [accepted_2106]
theorem batch_42_01_ok : batch_42_01_values.all id = true := by decide

def batch_42_02_values : List Bool := [accepted_2108]
theorem batch_42_02_ok : batch_42_02_values.all id = true := by decide

def batch_42_03_values : List Bool := [accepted_2110]
theorem batch_42_03_ok : batch_42_03_values.all id = true := by decide

def batch_42_04_values : List Bool := [accepted_2112]
theorem batch_42_04_ok : batch_42_04_values.all id = true := by decide

def batch_42_05_values : List Bool := [accepted_2114]
theorem batch_42_05_ok : batch_42_05_values.all id = true := by decide

def batch_42_06_values : List Bool := [accepted_2115]
theorem batch_42_06_ok : batch_42_06_values.all id = true := by decide

def batch_42_07_values : List Bool := [accepted_2118]
theorem batch_42_07_ok : batch_42_07_values.all id = true := by decide

def batch_42_08_values : List Bool := [accepted_2120]
theorem batch_42_08_ok : batch_42_08_values.all id = true := by decide

def batch_42_09_values : List Bool := [accepted_2122]
theorem batch_42_09_ok : batch_42_09_values.all id = true := by decide

def batch_42_10_values : List Bool := [accepted_2124]
theorem batch_42_10_ok : batch_42_10_values.all id = true := by decide

def batch_42_11_values : List Bool := [accepted_2135]
theorem batch_42_11_ok : batch_42_11_values.all id = true := by decide

def batch_42_12_values : List Bool := [accepted_2137]
theorem batch_42_12_ok : batch_42_12_values.all id = true := by decide

def batch_42_13_values : List Bool := [accepted_2139]
theorem batch_42_13_ok : batch_42_13_values.all id = true := by decide

def batch_42_14_values : List Bool := [accepted_2141]
theorem batch_42_14_ok : batch_42_14_values.all id = true := by decide

def batch_42_15_values : List Bool := [accepted_2146]
theorem batch_42_15_ok : batch_42_15_values.all id = true := by decide

def batch_42_16_values : List Bool := [accepted_2148]
theorem batch_42_16_ok : batch_42_16_values.all id = true := by decide

def batch_42_17_values : List Bool := [accepted_2149]
theorem batch_42_17_ok : batch_42_17_values.all id = true := by decide

theorem leaf_2101_ok : checkAt 527 1000 box_2101 cert_2101 = true := by
  have h := List.all_eq_true.mp batch_42_00_ok accepted_2101 (by simp [batch_42_00_values])
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

theorem leaf_2106_ok : checkAt 527 1000 box_2106 cert_2106 = true := by
  have h := List.all_eq_true.mp batch_42_01_ok accepted_2106 (by simp [batch_42_01_values])
  exact h
theorem leaf_2106_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2106.profileLo box_2106.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2106_ok
theorem branch_box_2106_nonnegative : ∀ j, 0 ≤ branch_box_2106.lower j ∧ 0 ≤ branch_box_2106.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2106, Box.profileLo, Box.profileHi, box_2106]
theorem leaf_2106_BranchSafe : CertificateConsequences.BranchSafe branch_box_2106 := by
  left; refine ⟨branch_box_2106_nonnegative, ?_⟩
  intro z hz; exact leaf_2106_sound hz

theorem leaf_2108_ok : checkAt 527 1000 box_2108 cert_2108 = true := by
  have h := List.all_eq_true.mp batch_42_02_ok accepted_2108 (by simp [batch_42_02_values])
  exact h
theorem leaf_2108_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2108.profileLo box_2108.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2108_ok
theorem branch_box_2108_nonnegative : ∀ j, 0 ≤ branch_box_2108.lower j ∧ 0 ≤ branch_box_2108.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2108, Box.profileLo, Box.profileHi, box_2108]
theorem leaf_2108_BranchSafe : CertificateConsequences.BranchSafe branch_box_2108 := by
  left; refine ⟨branch_box_2108_nonnegative, ?_⟩
  intro z hz; exact leaf_2108_sound hz

theorem leaf_2110_ok : checkAt 527 1000 box_2110 cert_2110 = true := by
  have h := List.all_eq_true.mp batch_42_03_ok accepted_2110 (by simp [batch_42_03_values])
  exact h
theorem leaf_2110_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2110.profileLo box_2110.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2110_ok
theorem branch_box_2110_nonnegative : ∀ j, 0 ≤ branch_box_2110.lower j ∧ 0 ≤ branch_box_2110.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2110, Box.profileLo, Box.profileHi, box_2110]
theorem leaf_2110_BranchSafe : CertificateConsequences.BranchSafe branch_box_2110 := by
  left; refine ⟨branch_box_2110_nonnegative, ?_⟩
  intro z hz; exact leaf_2110_sound hz

theorem leaf_2112_ok : checkAt 527 1000 box_2112 cert_2112 = true := by
  have h := List.all_eq_true.mp batch_42_04_ok accepted_2112 (by simp [batch_42_04_values])
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

theorem leaf_2115_ok : checkAt 527 1000 box_2115 cert_2115 = true := by
  have h := List.all_eq_true.mp batch_42_06_ok accepted_2115 (by simp [batch_42_06_values])
  exact h
theorem leaf_2115_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2115.profileLo box_2115.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2115_ok
theorem branch_box_2115_nonnegative : ∀ j, 0 ≤ branch_box_2115.lower j ∧ 0 ≤ branch_box_2115.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2115, Box.profileLo, Box.profileHi, box_2115]
theorem leaf_2115_BranchSafe : CertificateConsequences.BranchSafe branch_box_2115 := by
  left; refine ⟨branch_box_2115_nonnegative, ?_⟩
  intro z hz; exact leaf_2115_sound hz

theorem leaf_2118_ok : checkAt 527 1000 box_2118 cert_2118 = true := by
  have h := List.all_eq_true.mp batch_42_07_ok accepted_2118 (by simp [batch_42_07_values])
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

theorem leaf_2120_ok : checkAt 527 1000 box_2120 cert_2120 = true := by
  have h := List.all_eq_true.mp batch_42_08_ok accepted_2120 (by simp [batch_42_08_values])
  exact h
theorem leaf_2120_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2120.profileLo box_2120.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2120_ok
theorem branch_box_2120_nonnegative : ∀ j, 0 ≤ branch_box_2120.lower j ∧ 0 ≤ branch_box_2120.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2120, Box.profileLo, Box.profileHi, box_2120]
theorem leaf_2120_BranchSafe : CertificateConsequences.BranchSafe branch_box_2120 := by
  left; refine ⟨branch_box_2120_nonnegative, ?_⟩
  intro z hz; exact leaf_2120_sound hz

theorem leaf_2122_ok : checkAt 527 1000 box_2122 cert_2122 = true := by
  have h := List.all_eq_true.mp batch_42_09_ok accepted_2122 (by simp [batch_42_09_values])
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

theorem leaf_2124_ok : checkAt 527 1000 box_2124 cert_2124 = true := by
  have h := List.all_eq_true.mp batch_42_10_ok accepted_2124 (by simp [batch_42_10_values])
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
  have h := List.all_eq_true.mp batch_42_11_ok accepted_2135 (by simp [batch_42_11_values])
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

theorem leaf_2137_ok : checkAt 527 1000 box_2137 cert_2137 = true := by
  have h := List.all_eq_true.mp batch_42_12_ok accepted_2137 (by simp [batch_42_12_values])
  exact h
theorem leaf_2137_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2137.profileLo box_2137.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2137_ok
theorem branch_box_2137_nonnegative : ∀ j, 0 ≤ branch_box_2137.lower j ∧ 0 ≤ branch_box_2137.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2137, Box.profileLo, Box.profileHi, box_2137]
theorem leaf_2137_BranchSafe : CertificateConsequences.BranchSafe branch_box_2137 := by
  left; refine ⟨branch_box_2137_nonnegative, ?_⟩
  intro z hz; exact leaf_2137_sound hz

theorem leaf_2139_ok : checkAt 527 1000 box_2139 cert_2139 = true := by
  have h := List.all_eq_true.mp batch_42_13_ok accepted_2139 (by simp [batch_42_13_values])
  exact h
theorem leaf_2139_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2139.profileLo box_2139.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2139_ok
theorem branch_box_2139_nonnegative : ∀ j, 0 ≤ branch_box_2139.lower j ∧ 0 ≤ branch_box_2139.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2139, Box.profileLo, Box.profileHi, box_2139]
theorem leaf_2139_BranchSafe : CertificateConsequences.BranchSafe branch_box_2139 := by
  left; refine ⟨branch_box_2139_nonnegative, ?_⟩
  intro z hz; exact leaf_2139_sound hz

theorem leaf_2141_ok : checkAt 527 1000 box_2141 cert_2141 = true := by
  have h := List.all_eq_true.mp batch_42_14_ok accepted_2141 (by simp [batch_42_14_values])
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

theorem leaf_2146_ok : checkAt 527 1000 box_2146 cert_2146 = true := by
  have h := List.all_eq_true.mp batch_42_15_ok accepted_2146 (by simp [batch_42_15_values])
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

theorem leaf_2148_ok : checkAt 527 1000 box_2148 cert_2148 = true := by
  have h := List.all_eq_true.mp batch_42_16_ok accepted_2148 (by simp [batch_42_16_values])
  exact h
theorem leaf_2148_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2148.profileLo box_2148.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2148_ok
theorem branch_box_2148_nonnegative : ∀ j, 0 ≤ branch_box_2148.lower j ∧ 0 ≤ branch_box_2148.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2148, Box.profileLo, Box.profileHi, box_2148]
theorem leaf_2148_BranchSafe : CertificateConsequences.BranchSafe branch_box_2148 := by
  left; refine ⟨branch_box_2148_nonnegative, ?_⟩
  intro z hz; exact leaf_2148_sound hz

theorem leaf_2149_ok : checkAt 527 1000 box_2149 cert_2149 = true := by
  have h := List.all_eq_true.mp batch_42_17_ok accepted_2149 (by simp [batch_42_17_values])
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
#print axioms leaf_2101_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
