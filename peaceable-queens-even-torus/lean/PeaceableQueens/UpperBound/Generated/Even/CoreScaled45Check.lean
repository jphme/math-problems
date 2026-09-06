import PeaceableQueens.UpperBound.Generated.Even.CoreScaled45Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_45_00_values : List Bool := [accepted_2252]
theorem batch_45_00_ok : batch_45_00_values.all id = true := by decide

def batch_45_01_values : List Bool := [accepted_2254]
theorem batch_45_01_ok : batch_45_01_values.all id = true := by decide

def batch_45_02_values : List Bool := [accepted_2256]
theorem batch_45_02_ok : batch_45_02_values.all id = true := by decide

def batch_45_03_values : List Bool := [accepted_2260]
theorem batch_45_03_ok : batch_45_03_values.all id = true := by decide

def batch_45_04_values : List Bool := [accepted_2262]
theorem batch_45_04_ok : batch_45_04_values.all id = true := by decide

def batch_45_05_values : List Bool := [accepted_2263]
theorem batch_45_05_ok : batch_45_05_values.all id = true := by decide

def batch_45_06_values : List Bool := [accepted_2265]
theorem batch_45_06_ok : batch_45_06_values.all id = true := by decide

def batch_45_07_values : List Bool := [accepted_2275]
theorem batch_45_07_ok : batch_45_07_values.all id = true := by decide

def batch_45_08_values : List Bool := [accepted_2277]
theorem batch_45_08_ok : batch_45_08_values.all id = true := by decide

def batch_45_09_values : List Bool := [accepted_2278]
theorem batch_45_09_ok : batch_45_09_values.all id = true := by decide

def batch_45_10_values : List Bool := [accepted_2280]
theorem batch_45_10_ok : batch_45_10_values.all id = true := by decide

def batch_45_11_values : List Bool := [accepted_2283]
theorem batch_45_11_ok : batch_45_11_values.all id = true := by decide

def batch_45_12_values : List Bool := [accepted_2290]
theorem batch_45_12_ok : batch_45_12_values.all id = true := by decide

def batch_45_13_values : List Bool := [accepted_2292]
theorem batch_45_13_ok : batch_45_13_values.all id = true := by decide

def batch_45_14_values : List Bool := [accepted_2294]
theorem batch_45_14_ok : batch_45_14_values.all id = true := by decide

theorem leaf_2252_ok : checkAt 527 1000 box_2252 cert_2252 = true := by
  have h := List.all_eq_true.mp batch_45_00_ok accepted_2252 (by simp [batch_45_00_values])
  exact h
theorem leaf_2252_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2252.profileLo box_2252.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2252_ok
theorem branch_box_2252_nonnegative : ∀ j, 0 ≤ branch_box_2252.lower j ∧ 0 ≤ branch_box_2252.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2252, Box.profileLo, Box.profileHi, box_2252]
theorem leaf_2252_BranchSafe : CertificateConsequences.BranchSafe branch_box_2252 := by
  left; refine ⟨branch_box_2252_nonnegative, ?_⟩
  intro z hz; exact leaf_2252_sound hz

theorem leaf_2254_ok : checkAt 527 1000 box_2254 cert_2254 = true := by
  have h := List.all_eq_true.mp batch_45_01_ok accepted_2254 (by simp [batch_45_01_values])
  exact h
theorem leaf_2254_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2254.profileLo box_2254.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2254_ok
theorem branch_box_2254_nonnegative : ∀ j, 0 ≤ branch_box_2254.lower j ∧ 0 ≤ branch_box_2254.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2254, Box.profileLo, Box.profileHi, box_2254]
theorem leaf_2254_BranchSafe : CertificateConsequences.BranchSafe branch_box_2254 := by
  left; refine ⟨branch_box_2254_nonnegative, ?_⟩
  intro z hz; exact leaf_2254_sound hz

theorem leaf_2256_ok : checkAt 527 1000 box_2256 cert_2256 = true := by
  have h := List.all_eq_true.mp batch_45_02_ok accepted_2256 (by simp [batch_45_02_values])
  exact h
theorem leaf_2256_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2256.profileLo box_2256.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2256_ok
theorem branch_box_2256_nonnegative : ∀ j, 0 ≤ branch_box_2256.lower j ∧ 0 ≤ branch_box_2256.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2256, Box.profileLo, Box.profileHi, box_2256]
theorem leaf_2256_BranchSafe : CertificateConsequences.BranchSafe branch_box_2256 := by
  left; refine ⟨branch_box_2256_nonnegative, ?_⟩
  intro z hz; exact leaf_2256_sound hz

theorem leaf_2260_ok : checkAt 527 1000 box_2260 cert_2260 = true := by
  have h := List.all_eq_true.mp batch_45_03_ok accepted_2260 (by simp [batch_45_03_values])
  exact h
theorem leaf_2260_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2260.profileLo box_2260.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2260_ok
theorem branch_box_2260_nonnegative : ∀ j, 0 ≤ branch_box_2260.lower j ∧ 0 ≤ branch_box_2260.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2260, Box.profileLo, Box.profileHi, box_2260]
theorem leaf_2260_BranchSafe : CertificateConsequences.BranchSafe branch_box_2260 := by
  left; refine ⟨branch_box_2260_nonnegative, ?_⟩
  intro z hz; exact leaf_2260_sound hz

theorem leaf_2262_ok : checkAt 527 1000 box_2262 cert_2262 = true := by
  have h := List.all_eq_true.mp batch_45_04_ok accepted_2262 (by simp [batch_45_04_values])
  exact h
theorem leaf_2262_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2262.profileLo box_2262.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2262_ok
theorem branch_box_2262_nonnegative : ∀ j, 0 ≤ branch_box_2262.lower j ∧ 0 ≤ branch_box_2262.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2262, Box.profileLo, Box.profileHi, box_2262]
theorem leaf_2262_BranchSafe : CertificateConsequences.BranchSafe branch_box_2262 := by
  left; refine ⟨branch_box_2262_nonnegative, ?_⟩
  intro z hz; exact leaf_2262_sound hz

theorem leaf_2263_ok : checkAt 527 1000 box_2263 cert_2263 = true := by
  have h := List.all_eq_true.mp batch_45_05_ok accepted_2263 (by simp [batch_45_05_values])
  exact h
theorem leaf_2263_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2263.profileLo box_2263.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2263_ok
theorem branch_box_2263_nonnegative : ∀ j, 0 ≤ branch_box_2263.lower j ∧ 0 ≤ branch_box_2263.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2263, Box.profileLo, Box.profileHi, box_2263]
theorem leaf_2263_BranchSafe : CertificateConsequences.BranchSafe branch_box_2263 := by
  left; refine ⟨branch_box_2263_nonnegative, ?_⟩
  intro z hz; exact leaf_2263_sound hz

theorem leaf_2265_ok : checkAt 527 1000 box_2265 cert_2265 = true := by
  have h := List.all_eq_true.mp batch_45_06_ok accepted_2265 (by simp [batch_45_06_values])
  exact h
theorem leaf_2265_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2265.profileLo box_2265.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2265_ok
theorem branch_box_2265_nonnegative : ∀ j, 0 ≤ branch_box_2265.lower j ∧ 0 ≤ branch_box_2265.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2265, Box.profileLo, Box.profileHi, box_2265]
theorem leaf_2265_BranchSafe : CertificateConsequences.BranchSafe branch_box_2265 := by
  left; refine ⟨branch_box_2265_nonnegative, ?_⟩
  intro z hz; exact leaf_2265_sound hz

theorem leaf_2275_ok : checkAt 527 1000 box_2275 cert_2275 = true := by
  have h := List.all_eq_true.mp batch_45_07_ok accepted_2275 (by simp [batch_45_07_values])
  exact h
theorem leaf_2275_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2275.profileLo box_2275.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2275_ok
theorem branch_box_2275_nonnegative : ∀ j, 0 ≤ branch_box_2275.lower j ∧ 0 ≤ branch_box_2275.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2275, Box.profileLo, Box.profileHi, box_2275]
theorem leaf_2275_BranchSafe : CertificateConsequences.BranchSafe branch_box_2275 := by
  left; refine ⟨branch_box_2275_nonnegative, ?_⟩
  intro z hz; exact leaf_2275_sound hz

theorem leaf_2277_ok : checkAt 527 1000 box_2277 cert_2277 = true := by
  have h := List.all_eq_true.mp batch_45_08_ok accepted_2277 (by simp [batch_45_08_values])
  exact h
theorem leaf_2277_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2277.profileLo box_2277.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2277_ok
theorem branch_box_2277_nonnegative : ∀ j, 0 ≤ branch_box_2277.lower j ∧ 0 ≤ branch_box_2277.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2277, Box.profileLo, Box.profileHi, box_2277]
theorem leaf_2277_BranchSafe : CertificateConsequences.BranchSafe branch_box_2277 := by
  left; refine ⟨branch_box_2277_nonnegative, ?_⟩
  intro z hz; exact leaf_2277_sound hz

theorem leaf_2278_ok : checkAt 527 1000 box_2278 cert_2278 = true := by
  have h := List.all_eq_true.mp batch_45_09_ok accepted_2278 (by simp [batch_45_09_values])
  exact h
theorem leaf_2278_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2278.profileLo box_2278.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2278_ok
theorem branch_box_2278_nonnegative : ∀ j, 0 ≤ branch_box_2278.lower j ∧ 0 ≤ branch_box_2278.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2278, Box.profileLo, Box.profileHi, box_2278]
theorem leaf_2278_BranchSafe : CertificateConsequences.BranchSafe branch_box_2278 := by
  left; refine ⟨branch_box_2278_nonnegative, ?_⟩
  intro z hz; exact leaf_2278_sound hz

theorem leaf_2280_ok : checkAt 527 1000 box_2280 cert_2280 = true := by
  have h := List.all_eq_true.mp batch_45_10_ok accepted_2280 (by simp [batch_45_10_values])
  exact h
theorem leaf_2280_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2280.profileLo box_2280.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2280_ok
theorem branch_box_2280_nonnegative : ∀ j, 0 ≤ branch_box_2280.lower j ∧ 0 ≤ branch_box_2280.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2280, Box.profileLo, Box.profileHi, box_2280]
theorem leaf_2280_BranchSafe : CertificateConsequences.BranchSafe branch_box_2280 := by
  left; refine ⟨branch_box_2280_nonnegative, ?_⟩
  intro z hz; exact leaf_2280_sound hz

theorem leaf_2283_ok : checkAt 527 1000 box_2283 cert_2283 = true := by
  have h := List.all_eq_true.mp batch_45_11_ok accepted_2283 (by simp [batch_45_11_values])
  exact h
theorem leaf_2283_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2283.profileLo box_2283.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2283_ok
theorem branch_box_2283_nonnegative : ∀ j, 0 ≤ branch_box_2283.lower j ∧ 0 ≤ branch_box_2283.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2283, Box.profileLo, Box.profileHi, box_2283]
theorem leaf_2283_BranchSafe : CertificateConsequences.BranchSafe branch_box_2283 := by
  left; refine ⟨branch_box_2283_nonnegative, ?_⟩
  intro z hz; exact leaf_2283_sound hz

theorem leaf_2290_ok : checkAt 527 1000 box_2290 cert_2290 = true := by
  have h := List.all_eq_true.mp batch_45_12_ok accepted_2290 (by simp [batch_45_12_values])
  exact h
theorem leaf_2290_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2290.profileLo box_2290.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2290_ok
theorem branch_box_2290_nonnegative : ∀ j, 0 ≤ branch_box_2290.lower j ∧ 0 ≤ branch_box_2290.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2290, Box.profileLo, Box.profileHi, box_2290]
theorem leaf_2290_BranchSafe : CertificateConsequences.BranchSafe branch_box_2290 := by
  left; refine ⟨branch_box_2290_nonnegative, ?_⟩
  intro z hz; exact leaf_2290_sound hz

theorem leaf_2292_ok : checkAt 527 1000 box_2292 cert_2292 = true := by
  have h := List.all_eq_true.mp batch_45_13_ok accepted_2292 (by simp [batch_45_13_values])
  exact h
theorem leaf_2292_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2292.profileLo box_2292.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2292_ok
theorem branch_box_2292_nonnegative : ∀ j, 0 ≤ branch_box_2292.lower j ∧ 0 ≤ branch_box_2292.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2292, Box.profileLo, Box.profileHi, box_2292]
theorem leaf_2292_BranchSafe : CertificateConsequences.BranchSafe branch_box_2292 := by
  left; refine ⟨branch_box_2292_nonnegative, ?_⟩
  intro z hz; exact leaf_2292_sound hz

theorem leaf_2294_ok : checkAt 527 1000 box_2294 cert_2294 = true := by
  have h := List.all_eq_true.mp batch_45_14_ok accepted_2294 (by simp [batch_45_14_values])
  exact h
theorem leaf_2294_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2294.profileLo box_2294.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2294_ok
theorem branch_box_2294_nonnegative : ∀ j, 0 ≤ branch_box_2294.lower j ∧ 0 ≤ branch_box_2294.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2294, Box.profileLo, Box.profileHi, box_2294]
theorem leaf_2294_BranchSafe : CertificateConsequences.BranchSafe branch_box_2294 := by
  left; refine ⟨branch_box_2294_nonnegative, ?_⟩
  intro z hz; exact leaf_2294_sound hz

#print axioms batch_45_00_ok
#print axioms leaf_2252_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
