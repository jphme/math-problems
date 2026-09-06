import PeaceableQueens.UpperBound.Generated.Even.CoreScaled46Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_46_00_values : List Bool := [accepted_2300]
theorem batch_46_00_ok : batch_46_00_values.all id = true := by decide

def batch_46_01_values : List Bool := [accepted_2302]
theorem batch_46_01_ok : batch_46_01_values.all id = true := by decide

def batch_46_02_values : List Bool := [accepted_2304]
theorem batch_46_02_ok : batch_46_02_values.all id = true := by decide

def batch_46_03_values : List Bool := [accepted_2306]
theorem batch_46_03_ok : batch_46_03_values.all id = true := by decide

def batch_46_04_values : List Bool := [accepted_2308]
theorem batch_46_04_ok : batch_46_04_values.all id = true := by decide

def batch_46_05_values : List Bool := [accepted_2311]
theorem batch_46_05_ok : batch_46_05_values.all id = true := by decide

def batch_46_06_values : List Bool := [accepted_2318]
theorem batch_46_06_ok : batch_46_06_values.all id = true := by decide

def batch_46_07_values : List Bool := [accepted_2320]
theorem batch_46_07_ok : batch_46_07_values.all id = true := by decide

def batch_46_08_values : List Bool := [accepted_2322]
theorem batch_46_08_ok : batch_46_08_values.all id = true := by decide

def batch_46_09_values : List Bool := [accepted_2328]
theorem batch_46_09_ok : batch_46_09_values.all id = true := by decide

def batch_46_10_values : List Bool := [accepted_2330]
theorem batch_46_10_ok : batch_46_10_values.all id = true := by decide

def batch_46_11_values : List Bool := [accepted_2332]
theorem batch_46_11_ok : batch_46_11_values.all id = true := by decide

def batch_46_12_values : List Bool := [accepted_2334]
theorem batch_46_12_ok : batch_46_12_values.all id = true := by decide

def batch_46_13_values : List Bool := [accepted_2336]
theorem batch_46_13_ok : batch_46_13_values.all id = true := by decide

def batch_46_14_values : List Bool := [accepted_2337]
theorem batch_46_14_ok : batch_46_14_values.all id = true := by decide

def batch_46_15_values : List Bool := [accepted_2339]
theorem batch_46_15_ok : batch_46_15_values.all id = true := by decide

def batch_46_16_values : List Bool := [accepted_2348]
theorem batch_46_16_ok : batch_46_16_values.all id = true := by decide

def batch_46_17_values : List Bool := [accepted_2349]
theorem batch_46_17_ok : batch_46_17_values.all id = true := by decide

theorem leaf_2300_ok : checkAt 527 1000 box_2300 cert_2300 = true := by
  have h := List.all_eq_true.mp batch_46_00_ok accepted_2300 (by simp [batch_46_00_values])
  exact h
theorem leaf_2300_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2300.profileLo box_2300.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2300_ok
theorem branch_box_2300_nonnegative : ∀ j, 0 ≤ branch_box_2300.lower j ∧ 0 ≤ branch_box_2300.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2300, Box.profileLo, Box.profileHi, box_2300]
theorem leaf_2300_BranchSafe : CertificateConsequences.BranchSafe branch_box_2300 := by
  left; refine ⟨branch_box_2300_nonnegative, ?_⟩
  intro z hz; exact leaf_2300_sound hz

theorem leaf_2302_ok : checkAt 527 1000 box_2302 cert_2302 = true := by
  have h := List.all_eq_true.mp batch_46_01_ok accepted_2302 (by simp [batch_46_01_values])
  exact h
theorem leaf_2302_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2302.profileLo box_2302.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2302_ok
theorem branch_box_2302_nonnegative : ∀ j, 0 ≤ branch_box_2302.lower j ∧ 0 ≤ branch_box_2302.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2302, Box.profileLo, Box.profileHi, box_2302]
theorem leaf_2302_BranchSafe : CertificateConsequences.BranchSafe branch_box_2302 := by
  left; refine ⟨branch_box_2302_nonnegative, ?_⟩
  intro z hz; exact leaf_2302_sound hz

theorem leaf_2304_ok : checkAt 527 1000 box_2304 cert_2304 = true := by
  have h := List.all_eq_true.mp batch_46_02_ok accepted_2304 (by simp [batch_46_02_values])
  exact h
theorem leaf_2304_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2304.profileLo box_2304.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2304_ok
theorem branch_box_2304_nonnegative : ∀ j, 0 ≤ branch_box_2304.lower j ∧ 0 ≤ branch_box_2304.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2304, Box.profileLo, Box.profileHi, box_2304]
theorem leaf_2304_BranchSafe : CertificateConsequences.BranchSafe branch_box_2304 := by
  left; refine ⟨branch_box_2304_nonnegative, ?_⟩
  intro z hz; exact leaf_2304_sound hz

theorem leaf_2306_ok : checkAt 527 1000 box_2306 cert_2306 = true := by
  have h := List.all_eq_true.mp batch_46_03_ok accepted_2306 (by simp [batch_46_03_values])
  exact h
theorem leaf_2306_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2306.profileLo box_2306.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2306_ok
theorem branch_box_2306_nonnegative : ∀ j, 0 ≤ branch_box_2306.lower j ∧ 0 ≤ branch_box_2306.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2306, Box.profileLo, Box.profileHi, box_2306]
theorem leaf_2306_BranchSafe : CertificateConsequences.BranchSafe branch_box_2306 := by
  left; refine ⟨branch_box_2306_nonnegative, ?_⟩
  intro z hz; exact leaf_2306_sound hz

theorem leaf_2308_ok : checkAt 527 1000 box_2308 cert_2308 = true := by
  have h := List.all_eq_true.mp batch_46_04_ok accepted_2308 (by simp [batch_46_04_values])
  exact h
theorem leaf_2308_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2308.profileLo box_2308.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2308_ok
theorem branch_box_2308_nonnegative : ∀ j, 0 ≤ branch_box_2308.lower j ∧ 0 ≤ branch_box_2308.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2308, Box.profileLo, Box.profileHi, box_2308]
theorem leaf_2308_BranchSafe : CertificateConsequences.BranchSafe branch_box_2308 := by
  left; refine ⟨branch_box_2308_nonnegative, ?_⟩
  intro z hz; exact leaf_2308_sound hz

theorem leaf_2311_ok : checkAt 527 1000 box_2311 cert_2311 = true := by
  have h := List.all_eq_true.mp batch_46_05_ok accepted_2311 (by simp [batch_46_05_values])
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

theorem leaf_2318_ok : checkAt 527 1000 box_2318 cert_2318 = true := by
  have h := List.all_eq_true.mp batch_46_06_ok accepted_2318 (by simp [batch_46_06_values])
  exact h
theorem leaf_2318_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2318.profileLo box_2318.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2318_ok
theorem branch_box_2318_nonnegative : ∀ j, 0 ≤ branch_box_2318.lower j ∧ 0 ≤ branch_box_2318.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2318, Box.profileLo, Box.profileHi, box_2318]
theorem leaf_2318_BranchSafe : CertificateConsequences.BranchSafe branch_box_2318 := by
  left; refine ⟨branch_box_2318_nonnegative, ?_⟩
  intro z hz; exact leaf_2318_sound hz

theorem leaf_2320_ok : checkAt 527 1000 box_2320 cert_2320 = true := by
  have h := List.all_eq_true.mp batch_46_07_ok accepted_2320 (by simp [batch_46_07_values])
  exact h
theorem leaf_2320_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2320.profileLo box_2320.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2320_ok
theorem branch_box_2320_nonnegative : ∀ j, 0 ≤ branch_box_2320.lower j ∧ 0 ≤ branch_box_2320.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2320, Box.profileLo, Box.profileHi, box_2320]
theorem leaf_2320_BranchSafe : CertificateConsequences.BranchSafe branch_box_2320 := by
  left; refine ⟨branch_box_2320_nonnegative, ?_⟩
  intro z hz; exact leaf_2320_sound hz

theorem leaf_2322_ok : checkAt 527 1000 box_2322 cert_2322 = true := by
  have h := List.all_eq_true.mp batch_46_08_ok accepted_2322 (by simp [batch_46_08_values])
  exact h
theorem leaf_2322_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2322.profileLo box_2322.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2322_ok
theorem branch_box_2322_nonnegative : ∀ j, 0 ≤ branch_box_2322.lower j ∧ 0 ≤ branch_box_2322.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2322, Box.profileLo, Box.profileHi, box_2322]
theorem leaf_2322_BranchSafe : CertificateConsequences.BranchSafe branch_box_2322 := by
  left; refine ⟨branch_box_2322_nonnegative, ?_⟩
  intro z hz; exact leaf_2322_sound hz

theorem leaf_2328_ok : checkAt 527 1000 box_2328 cert_2328 = true := by
  have h := List.all_eq_true.mp batch_46_09_ok accepted_2328 (by simp [batch_46_09_values])
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

theorem leaf_2330_ok : checkAt 527 1000 box_2330 cert_2330 = true := by
  have h := List.all_eq_true.mp batch_46_10_ok accepted_2330 (by simp [batch_46_10_values])
  exact h
theorem leaf_2330_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2330.profileLo box_2330.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2330_ok
theorem branch_box_2330_nonnegative : ∀ j, 0 ≤ branch_box_2330.lower j ∧ 0 ≤ branch_box_2330.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2330, Box.profileLo, Box.profileHi, box_2330]
theorem leaf_2330_BranchSafe : CertificateConsequences.BranchSafe branch_box_2330 := by
  left; refine ⟨branch_box_2330_nonnegative, ?_⟩
  intro z hz; exact leaf_2330_sound hz

theorem leaf_2332_ok : checkAt 527 1000 box_2332 cert_2332 = true := by
  have h := List.all_eq_true.mp batch_46_11_ok accepted_2332 (by simp [batch_46_11_values])
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

theorem leaf_2334_ok : checkAt 527 1000 box_2334 cert_2334 = true := by
  have h := List.all_eq_true.mp batch_46_12_ok accepted_2334 (by simp [batch_46_12_values])
  exact h
theorem leaf_2334_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2334.profileLo box_2334.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2334_ok
theorem branch_box_2334_nonnegative : ∀ j, 0 ≤ branch_box_2334.lower j ∧ 0 ≤ branch_box_2334.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2334, Box.profileLo, Box.profileHi, box_2334]
theorem leaf_2334_BranchSafe : CertificateConsequences.BranchSafe branch_box_2334 := by
  left; refine ⟨branch_box_2334_nonnegative, ?_⟩
  intro z hz; exact leaf_2334_sound hz

theorem leaf_2336_ok : checkAt 527 1000 box_2336 cert_2336 = true := by
  have h := List.all_eq_true.mp batch_46_13_ok accepted_2336 (by simp [batch_46_13_values])
  exact h
theorem leaf_2336_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2336.profileLo box_2336.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2336_ok
theorem branch_box_2336_nonnegative : ∀ j, 0 ≤ branch_box_2336.lower j ∧ 0 ≤ branch_box_2336.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2336, Box.profileLo, Box.profileHi, box_2336]
theorem leaf_2336_BranchSafe : CertificateConsequences.BranchSafe branch_box_2336 := by
  left; refine ⟨branch_box_2336_nonnegative, ?_⟩
  intro z hz; exact leaf_2336_sound hz

theorem leaf_2337_ok : checkAt 527 1000 box_2337 cert_2337 = true := by
  have h := List.all_eq_true.mp batch_46_14_ok accepted_2337 (by simp [batch_46_14_values])
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

theorem leaf_2339_ok : checkAt 527 1000 box_2339 cert_2339 = true := by
  have h := List.all_eq_true.mp batch_46_15_ok accepted_2339 (by simp [batch_46_15_values])
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

theorem leaf_2348_ok : checkAt 527 1000 box_2348 cert_2348 = true := by
  have h := List.all_eq_true.mp batch_46_16_ok accepted_2348 (by simp [batch_46_16_values])
  exact h
theorem leaf_2348_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_2348.profileLo box_2348.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_2348_ok
theorem branch_box_2348_nonnegative : ∀ j, 0 ≤ branch_box_2348.lower j ∧ 0 ≤ branch_box_2348.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_2348, Box.profileLo, Box.profileHi, box_2348]
theorem leaf_2348_BranchSafe : CertificateConsequences.BranchSafe branch_box_2348 := by
  left; refine ⟨branch_box_2348_nonnegative, ?_⟩
  intro z hz; exact leaf_2348_sound hz

theorem leaf_2349_ok : checkAt 527 1000 box_2349 cert_2349 = true := by
  have h := List.all_eq_true.mp batch_46_17_ok accepted_2349 (by simp [batch_46_17_values])
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
#print axioms leaf_2300_sound
end PeaceableQueens.UpperBound.Generated.Even.Core
