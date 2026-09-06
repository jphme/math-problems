import PeaceableQueens.UpperBound.Generated.Even.C527Scaled46Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_46_00_values : List Bool := [accepted_2307]
theorem batch_46_00_ok : batch_46_00_values.all id = true := by decide

def batch_46_01_values : List Bool := [accepted_2309]
theorem batch_46_01_ok : batch_46_01_values.all id = true := by decide

def batch_46_02_values : List Bool := [accepted_2310]
theorem batch_46_02_ok : batch_46_02_values.all id = true := by decide

def batch_46_03_values : List Bool := [accepted_2311]
theorem batch_46_03_ok : batch_46_03_values.all id = true := by decide

def batch_46_04_values : List Bool := [accepted_2313]
theorem batch_46_04_ok : batch_46_04_values.all id = true := by decide

def batch_46_05_values : List Bool := [accepted_2314]
theorem batch_46_05_ok : batch_46_05_values.all id = true := by decide

def batch_46_06_values : List Bool := [accepted_2315]
theorem batch_46_06_ok : batch_46_06_values.all id = true := by decide

def batch_46_07_values : List Bool := [accepted_2316]
theorem batch_46_07_ok : batch_46_07_values.all id = true := by decide

def batch_46_08_values : List Bool := [accepted_2325]
theorem batch_46_08_ok : batch_46_08_values.all id = true := by decide

def batch_46_09_values : List Bool := [accepted_2326]
theorem batch_46_09_ok : batch_46_09_values.all id = true := by decide

def batch_46_10_values : List Bool := [accepted_2327]
theorem batch_46_10_ok : batch_46_10_values.all id = true := by decide

def batch_46_11_values : List Bool := [accepted_2328]
theorem batch_46_11_ok : batch_46_11_values.all id = true := by decide

def batch_46_12_values : List Bool := [accepted_2329]
theorem batch_46_12_ok : batch_46_12_values.all id = true := by decide

def batch_46_13_values : List Bool := [accepted_2331]
theorem batch_46_13_ok : batch_46_13_values.all id = true := by decide

def batch_46_14_values : List Bool := [accepted_2332]
theorem batch_46_14_ok : batch_46_14_values.all id = true := by decide

def batch_46_15_values : List Bool := [accepted_2337]
theorem batch_46_15_ok : batch_46_15_values.all id = true := by decide

def batch_46_16_values : List Bool := [accepted_2338]
theorem batch_46_16_ok : batch_46_16_values.all id = true := by decide

def batch_46_17_values : List Bool := [accepted_2339]
theorem batch_46_17_ok : batch_46_17_values.all id = true := by decide

def batch_46_18_values : List Bool := [accepted_2341]
theorem batch_46_18_ok : batch_46_18_values.all id = true := by decide

def batch_46_19_values : List Bool := [accepted_2342]
theorem batch_46_19_ok : batch_46_19_values.all id = true := by decide

def batch_46_20_values : List Bool := [accepted_2343]
theorem batch_46_20_ok : batch_46_20_values.all id = true := by decide

def batch_46_21_values : List Bool := [accepted_2345]
theorem batch_46_21_ok : batch_46_21_values.all id = true := by decide

def batch_46_22_values : List Bool := [accepted_2346]
theorem batch_46_22_ok : batch_46_22_values.all id = true := by decide

def batch_46_23_values : List Bool := [accepted_2349]
theorem batch_46_23_ok : batch_46_23_values.all id = true := by decide

theorem leaf_2307_ok : checkAt 527 1000 box_2307 cert_2307 = true := by
  have h := List.all_eq_true.mp batch_46_00_ok accepted_2307 (by simp [batch_46_00_values])
  exact h
theorem leaf_2307_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2307.profileLo box_2307.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2307_ok
theorem branch_box_2307_nonnegative : ∀ j, 0 ≤ branch_box_2307.lower j ∧ 0 ≤ branch_box_2307.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2307, Box.profileLo, Box.profileHi, box_2307]
theorem leaf_2307_BranchSafe : CertificateConsequences.BranchSafe branch_box_2307 := by
  left; refine ⟨branch_box_2307_nonnegative, ?_⟩
  intro z hz; exact leaf_2307_sound hz

theorem leaf_2309_ok : checkAt 527 1000 box_2309 cert_2309 = true := by
  have h := List.all_eq_true.mp batch_46_01_ok accepted_2309 (by simp [batch_46_01_values])
  exact h
theorem leaf_2309_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2309.profileLo box_2309.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2309_ok
theorem branch_box_2309_nonnegative : ∀ j, 0 ≤ branch_box_2309.lower j ∧ 0 ≤ branch_box_2309.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2309, Box.profileLo, Box.profileHi, box_2309]
theorem leaf_2309_BranchSafe : CertificateConsequences.BranchSafe branch_box_2309 := by
  left; refine ⟨branch_box_2309_nonnegative, ?_⟩
  intro z hz; exact leaf_2309_sound hz

theorem leaf_2310_ok : checkAt 527 1000 box_2310 cert_2310 = true := by
  have h := List.all_eq_true.mp batch_46_02_ok accepted_2310 (by simp [batch_46_02_values])
  exact h
theorem leaf_2310_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2310.profileLo box_2310.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2310_ok
theorem branch_box_2310_nonnegative : ∀ j, 0 ≤ branch_box_2310.lower j ∧ 0 ≤ branch_box_2310.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2310, Box.profileLo, Box.profileHi, box_2310]
theorem leaf_2310_BranchSafe : CertificateConsequences.BranchSafe branch_box_2310 := by
  left; refine ⟨branch_box_2310_nonnegative, ?_⟩
  intro z hz; exact leaf_2310_sound hz

theorem leaf_2311_ok : checkAt 527 1000 box_2311 cert_2311 = true := by
  have h := List.all_eq_true.mp batch_46_03_ok accepted_2311 (by simp [batch_46_03_values])
  exact h
theorem leaf_2311_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2311.profileLo box_2311.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2311_ok
theorem branch_box_2311_nonnegative : ∀ j, 0 ≤ branch_box_2311.lower j ∧ 0 ≤ branch_box_2311.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2311, Box.profileLo, Box.profileHi, box_2311]
theorem leaf_2311_BranchSafe : CertificateConsequences.BranchSafe branch_box_2311 := by
  left; refine ⟨branch_box_2311_nonnegative, ?_⟩
  intro z hz; exact leaf_2311_sound hz

theorem leaf_2313_ok : checkAt 527 1000 box_2313 cert_2313 = true := by
  have h := List.all_eq_true.mp batch_46_04_ok accepted_2313 (by simp [batch_46_04_values])
  exact h
theorem leaf_2313_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2313.profileLo box_2313.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2313_ok
theorem branch_box_2313_nonnegative : ∀ j, 0 ≤ branch_box_2313.lower j ∧ 0 ≤ branch_box_2313.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2313, Box.profileLo, Box.profileHi, box_2313]
theorem leaf_2313_BranchSafe : CertificateConsequences.BranchSafe branch_box_2313 := by
  left; refine ⟨branch_box_2313_nonnegative, ?_⟩
  intro z hz; exact leaf_2313_sound hz

theorem leaf_2314_ok : checkAt 527 1000 box_2314 cert_2314 = true := by
  have h := List.all_eq_true.mp batch_46_05_ok accepted_2314 (by simp [batch_46_05_values])
  exact h
theorem leaf_2314_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2314.profileLo box_2314.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2314_ok
theorem branch_box_2314_nonnegative : ∀ j, 0 ≤ branch_box_2314.lower j ∧ 0 ≤ branch_box_2314.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2314, Box.profileLo, Box.profileHi, box_2314]
theorem leaf_2314_BranchSafe : CertificateConsequences.BranchSafe branch_box_2314 := by
  left; refine ⟨branch_box_2314_nonnegative, ?_⟩
  intro z hz; exact leaf_2314_sound hz

theorem leaf_2315_ok : checkAt 527 1000 box_2315 cert_2315 = true := by
  have h := List.all_eq_true.mp batch_46_06_ok accepted_2315 (by simp [batch_46_06_values])
  exact h
theorem leaf_2315_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2315.profileLo box_2315.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2315_ok
theorem branch_box_2315_nonnegative : ∀ j, 0 ≤ branch_box_2315.lower j ∧ 0 ≤ branch_box_2315.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2315, Box.profileLo, Box.profileHi, box_2315]
theorem leaf_2315_BranchSafe : CertificateConsequences.BranchSafe branch_box_2315 := by
  left; refine ⟨branch_box_2315_nonnegative, ?_⟩
  intro z hz; exact leaf_2315_sound hz

theorem leaf_2316_ok : checkAt 527 1000 box_2316 cert_2316 = true := by
  have h := List.all_eq_true.mp batch_46_07_ok accepted_2316 (by simp [batch_46_07_values])
  exact h
theorem leaf_2316_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2316.profileLo box_2316.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2316_ok
theorem branch_box_2316_nonnegative : ∀ j, 0 ≤ branch_box_2316.lower j ∧ 0 ≤ branch_box_2316.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2316, Box.profileLo, Box.profileHi, box_2316]
theorem leaf_2316_BranchSafe : CertificateConsequences.BranchSafe branch_box_2316 := by
  left; refine ⟨branch_box_2316_nonnegative, ?_⟩
  intro z hz; exact leaf_2316_sound hz

theorem leaf_2325_ok : checkAt 527 1000 box_2325 cert_2325 = true := by
  have h := List.all_eq_true.mp batch_46_08_ok accepted_2325 (by simp [batch_46_08_values])
  exact h
theorem leaf_2325_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2325.profileLo box_2325.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2325_ok
theorem branch_box_2325_nonnegative : ∀ j, 0 ≤ branch_box_2325.lower j ∧ 0 ≤ branch_box_2325.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2325, Box.profileLo, Box.profileHi, box_2325]
theorem leaf_2325_BranchSafe : CertificateConsequences.BranchSafe branch_box_2325 := by
  left; refine ⟨branch_box_2325_nonnegative, ?_⟩
  intro z hz; exact leaf_2325_sound hz

theorem leaf_2326_ok : checkAt 527 1000 box_2326 cert_2326 = true := by
  have h := List.all_eq_true.mp batch_46_09_ok accepted_2326 (by simp [batch_46_09_values])
  exact h
theorem leaf_2326_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2326.profileLo box_2326.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2326_ok
theorem branch_box_2326_nonnegative : ∀ j, 0 ≤ branch_box_2326.lower j ∧ 0 ≤ branch_box_2326.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2326, Box.profileLo, Box.profileHi, box_2326]
theorem leaf_2326_BranchSafe : CertificateConsequences.BranchSafe branch_box_2326 := by
  left; refine ⟨branch_box_2326_nonnegative, ?_⟩
  intro z hz; exact leaf_2326_sound hz

theorem leaf_2327_ok : checkAt 527 1000 box_2327 cert_2327 = true := by
  have h := List.all_eq_true.mp batch_46_10_ok accepted_2327 (by simp [batch_46_10_values])
  exact h
theorem leaf_2327_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2327.profileLo box_2327.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2327_ok
theorem branch_box_2327_nonnegative : ∀ j, 0 ≤ branch_box_2327.lower j ∧ 0 ≤ branch_box_2327.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2327, Box.profileLo, Box.profileHi, box_2327]
theorem leaf_2327_BranchSafe : CertificateConsequences.BranchSafe branch_box_2327 := by
  left; refine ⟨branch_box_2327_nonnegative, ?_⟩
  intro z hz; exact leaf_2327_sound hz

theorem leaf_2328_ok : checkAt 527 1000 box_2328 cert_2328 = true := by
  have h := List.all_eq_true.mp batch_46_11_ok accepted_2328 (by simp [batch_46_11_values])
  exact h
theorem leaf_2328_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2328.profileLo box_2328.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2328_ok
theorem branch_box_2328_nonnegative : ∀ j, 0 ≤ branch_box_2328.lower j ∧ 0 ≤ branch_box_2328.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2328, Box.profileLo, Box.profileHi, box_2328]
theorem leaf_2328_BranchSafe : CertificateConsequences.BranchSafe branch_box_2328 := by
  left; refine ⟨branch_box_2328_nonnegative, ?_⟩
  intro z hz; exact leaf_2328_sound hz

theorem leaf_2329_ok : checkAt 527 1000 box_2329 cert_2329 = true := by
  have h := List.all_eq_true.mp batch_46_12_ok accepted_2329 (by simp [batch_46_12_values])
  exact h
theorem leaf_2329_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2329.profileLo box_2329.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2329_ok
theorem branch_box_2329_nonnegative : ∀ j, 0 ≤ branch_box_2329.lower j ∧ 0 ≤ branch_box_2329.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2329, Box.profileLo, Box.profileHi, box_2329]
theorem leaf_2329_BranchSafe : CertificateConsequences.BranchSafe branch_box_2329 := by
  left; refine ⟨branch_box_2329_nonnegative, ?_⟩
  intro z hz; exact leaf_2329_sound hz

theorem leaf_2331_ok : checkAt 527 1000 box_2331 cert_2331 = true := by
  have h := List.all_eq_true.mp batch_46_13_ok accepted_2331 (by simp [batch_46_13_values])
  exact h
theorem leaf_2331_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2331.profileLo box_2331.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2331_ok
theorem branch_box_2331_nonnegative : ∀ j, 0 ≤ branch_box_2331.lower j ∧ 0 ≤ branch_box_2331.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2331, Box.profileLo, Box.profileHi, box_2331]
theorem leaf_2331_BranchSafe : CertificateConsequences.BranchSafe branch_box_2331 := by
  left; refine ⟨branch_box_2331_nonnegative, ?_⟩
  intro z hz; exact leaf_2331_sound hz

theorem leaf_2332_ok : checkAt 527 1000 box_2332 cert_2332 = true := by
  have h := List.all_eq_true.mp batch_46_14_ok accepted_2332 (by simp [batch_46_14_values])
  exact h
theorem leaf_2332_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2332.profileLo box_2332.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2332_ok
theorem branch_box_2332_nonnegative : ∀ j, 0 ≤ branch_box_2332.lower j ∧ 0 ≤ branch_box_2332.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2332, Box.profileLo, Box.profileHi, box_2332]
theorem leaf_2332_BranchSafe : CertificateConsequences.BranchSafe branch_box_2332 := by
  left; refine ⟨branch_box_2332_nonnegative, ?_⟩
  intro z hz; exact leaf_2332_sound hz

theorem leaf_2337_ok : checkAt 527 1000 box_2337 cert_2337 = true := by
  have h := List.all_eq_true.mp batch_46_15_ok accepted_2337 (by simp [batch_46_15_values])
  exact h
theorem leaf_2337_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2337.profileLo box_2337.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2337_ok
theorem branch_box_2337_nonnegative : ∀ j, 0 ≤ branch_box_2337.lower j ∧ 0 ≤ branch_box_2337.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2337, Box.profileLo, Box.profileHi, box_2337]
theorem leaf_2337_BranchSafe : CertificateConsequences.BranchSafe branch_box_2337 := by
  left; refine ⟨branch_box_2337_nonnegative, ?_⟩
  intro z hz; exact leaf_2337_sound hz

theorem leaf_2338_ok : checkAt 527 1000 box_2338 cert_2338 = true := by
  have h := List.all_eq_true.mp batch_46_16_ok accepted_2338 (by simp [batch_46_16_values])
  exact h
theorem leaf_2338_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2338.profileLo box_2338.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2338_ok
theorem branch_box_2338_nonnegative : ∀ j, 0 ≤ branch_box_2338.lower j ∧ 0 ≤ branch_box_2338.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2338, Box.profileLo, Box.profileHi, box_2338]
theorem leaf_2338_BranchSafe : CertificateConsequences.BranchSafe branch_box_2338 := by
  left; refine ⟨branch_box_2338_nonnegative, ?_⟩
  intro z hz; exact leaf_2338_sound hz

theorem leaf_2339_ok : checkAt 527 1000 box_2339 cert_2339 = true := by
  have h := List.all_eq_true.mp batch_46_17_ok accepted_2339 (by simp [batch_46_17_values])
  exact h
theorem leaf_2339_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2339.profileLo box_2339.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2339_ok
theorem branch_box_2339_nonnegative : ∀ j, 0 ≤ branch_box_2339.lower j ∧ 0 ≤ branch_box_2339.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2339, Box.profileLo, Box.profileHi, box_2339]
theorem leaf_2339_BranchSafe : CertificateConsequences.BranchSafe branch_box_2339 := by
  left; refine ⟨branch_box_2339_nonnegative, ?_⟩
  intro z hz; exact leaf_2339_sound hz

theorem leaf_2341_ok : checkAt 527 1000 box_2341 cert_2341 = true := by
  have h := List.all_eq_true.mp batch_46_18_ok accepted_2341 (by simp [batch_46_18_values])
  exact h
theorem leaf_2341_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2341.profileLo box_2341.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2341_ok
theorem branch_box_2341_nonnegative : ∀ j, 0 ≤ branch_box_2341.lower j ∧ 0 ≤ branch_box_2341.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2341, Box.profileLo, Box.profileHi, box_2341]
theorem leaf_2341_BranchSafe : CertificateConsequences.BranchSafe branch_box_2341 := by
  left; refine ⟨branch_box_2341_nonnegative, ?_⟩
  intro z hz; exact leaf_2341_sound hz

theorem leaf_2342_ok : checkAt 527 1000 box_2342 cert_2342 = true := by
  have h := List.all_eq_true.mp batch_46_19_ok accepted_2342 (by simp [batch_46_19_values])
  exact h
theorem leaf_2342_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2342.profileLo box_2342.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2342_ok
theorem branch_box_2342_nonnegative : ∀ j, 0 ≤ branch_box_2342.lower j ∧ 0 ≤ branch_box_2342.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2342, Box.profileLo, Box.profileHi, box_2342]
theorem leaf_2342_BranchSafe : CertificateConsequences.BranchSafe branch_box_2342 := by
  left; refine ⟨branch_box_2342_nonnegative, ?_⟩
  intro z hz; exact leaf_2342_sound hz

theorem leaf_2343_ok : checkAt 527 1000 box_2343 cert_2343 = true := by
  have h := List.all_eq_true.mp batch_46_20_ok accepted_2343 (by simp [batch_46_20_values])
  exact h
theorem leaf_2343_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2343.profileLo box_2343.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2343_ok
theorem branch_box_2343_nonnegative : ∀ j, 0 ≤ branch_box_2343.lower j ∧ 0 ≤ branch_box_2343.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2343, Box.profileLo, Box.profileHi, box_2343]
theorem leaf_2343_BranchSafe : CertificateConsequences.BranchSafe branch_box_2343 := by
  left; refine ⟨branch_box_2343_nonnegative, ?_⟩
  intro z hz; exact leaf_2343_sound hz

theorem leaf_2345_ok : checkAt 527 1000 box_2345 cert_2345 = true := by
  have h := List.all_eq_true.mp batch_46_21_ok accepted_2345 (by simp [batch_46_21_values])
  exact h
theorem leaf_2345_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2345.profileLo box_2345.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2345_ok
theorem branch_box_2345_nonnegative : ∀ j, 0 ≤ branch_box_2345.lower j ∧ 0 ≤ branch_box_2345.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2345, Box.profileLo, Box.profileHi, box_2345]
theorem leaf_2345_BranchSafe : CertificateConsequences.BranchSafe branch_box_2345 := by
  left; refine ⟨branch_box_2345_nonnegative, ?_⟩
  intro z hz; exact leaf_2345_sound hz

theorem leaf_2346_ok : checkAt 527 1000 box_2346 cert_2346 = true := by
  have h := List.all_eq_true.mp batch_46_22_ok accepted_2346 (by simp [batch_46_22_values])
  exact h
theorem leaf_2346_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2346.profileLo box_2346.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2346_ok
theorem branch_box_2346_nonnegative : ∀ j, 0 ≤ branch_box_2346.lower j ∧ 0 ≤ branch_box_2346.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2346, Box.profileLo, Box.profileHi, box_2346]
theorem leaf_2346_BranchSafe : CertificateConsequences.BranchSafe branch_box_2346 := by
  left; refine ⟨branch_box_2346_nonnegative, ?_⟩
  intro z hz; exact leaf_2346_sound hz

theorem leaf_2349_ok : checkAt 527 1000 box_2349 cert_2349 = true := by
  have h := List.all_eq_true.mp batch_46_23_ok accepted_2349 (by simp [batch_46_23_values])
  exact h
theorem leaf_2349_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2349.profileLo box_2349.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2349_ok
theorem branch_box_2349_nonnegative : ∀ j, 0 ≤ branch_box_2349.lower j ∧ 0 ≤ branch_box_2349.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2349, Box.profileLo, Box.profileHi, box_2349]
theorem leaf_2349_BranchSafe : CertificateConsequences.BranchSafe branch_box_2349 := by
  left; refine ⟨branch_box_2349_nonnegative, ?_⟩
  intro z hz; exact leaf_2349_sound hz

#print axioms batch_46_00_ok
#print axioms leaf_2307_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
