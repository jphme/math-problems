import PeaceableQueens.UpperBound.Generated.Even.C527Scaled126Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_126_00_values : List Bool := [accepted_6301]
theorem batch_126_00_ok : batch_126_00_values.all id = true := by decide

def batch_126_01_values : List Bool := [accepted_6303]
theorem batch_126_01_ok : batch_126_01_values.all id = true := by decide

def batch_126_02_values : List Bool := [accepted_6304]
theorem batch_126_02_ok : batch_126_02_values.all id = true := by decide

def batch_126_03_values : List Bool := [accepted_6311]
theorem batch_126_03_ok : batch_126_03_values.all id = true := by decide

def batch_126_04_values : List Bool := [accepted_6312]
theorem batch_126_04_ok : batch_126_04_values.all id = true := by decide

def batch_126_05_values : List Bool := [accepted_6313]
theorem batch_126_05_ok : batch_126_05_values.all id = true := by decide

def batch_126_06_values : List Bool := [accepted_6314]
theorem batch_126_06_ok : batch_126_06_values.all id = true := by decide

def batch_126_07_values : List Bool := [accepted_6317]
theorem batch_126_07_ok : batch_126_07_values.all id = true := by decide

def batch_126_08_values : List Bool := [accepted_6318]
theorem batch_126_08_ok : batch_126_08_values.all id = true := by decide

def batch_126_09_values : List Bool := [accepted_6323]
theorem batch_126_09_ok : batch_126_09_values.all id = true := by decide

def batch_126_10_values : List Bool := [accepted_6328]
theorem batch_126_10_ok : batch_126_10_values.all id = true := by decide

def batch_126_11_values : List Bool := [accepted_6329]
theorem batch_126_11_ok : batch_126_11_values.all id = true := by decide

def batch_126_12_values : List Bool := [accepted_6331]
theorem batch_126_12_ok : batch_126_12_values.all id = true := by decide

def batch_126_13_values : List Bool := [accepted_6333]
theorem batch_126_13_ok : batch_126_13_values.all id = true := by decide

def batch_126_14_values : List Bool := [accepted_6334]
theorem batch_126_14_ok : batch_126_14_values.all id = true := by decide

def batch_126_15_values : List Bool := [accepted_6337]
theorem batch_126_15_ok : batch_126_15_values.all id = true := by decide

def batch_126_16_values : List Bool := [accepted_6338]
theorem batch_126_16_ok : batch_126_16_values.all id = true := by decide

def batch_126_17_values : List Bool := [accepted_6340]
theorem batch_126_17_ok : batch_126_17_values.all id = true := by decide

def batch_126_18_values : List Bool := [accepted_6342]
theorem batch_126_18_ok : batch_126_18_values.all id = true := by decide

def batch_126_19_values : List Bool := [accepted_6345]
theorem batch_126_19_ok : batch_126_19_values.all id = true := by decide

theorem leaf_6301_ok : checkAt 527 1000 box_6301 cert_6301 = true := by
  have h := List.all_eq_true.mp batch_126_00_ok accepted_6301 (by simp [batch_126_00_values])
  exact h
theorem leaf_6301_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6301.profileLo box_6301.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6301_ok
theorem branch_box_6301_nonnegative : ∀ j, 0 ≤ branch_box_6301.lower j ∧ 0 ≤ branch_box_6301.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6301, Box.profileLo, Box.profileHi, box_6301]
theorem leaf_6301_BranchSafe : CertificateConsequences.BranchSafe branch_box_6301 := by
  left; refine ⟨branch_box_6301_nonnegative, ?_⟩
  intro z hz; exact leaf_6301_sound hz

theorem leaf_6303_ok : checkAt 527 1000 box_6303 cert_6303 = true := by
  have h := List.all_eq_true.mp batch_126_01_ok accepted_6303 (by simp [batch_126_01_values])
  exact h
theorem leaf_6303_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6303.profileLo box_6303.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6303_ok
theorem branch_box_6303_nonnegative : ∀ j, 0 ≤ branch_box_6303.lower j ∧ 0 ≤ branch_box_6303.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6303, Box.profileLo, Box.profileHi, box_6303]
theorem leaf_6303_BranchSafe : CertificateConsequences.BranchSafe branch_box_6303 := by
  left; refine ⟨branch_box_6303_nonnegative, ?_⟩
  intro z hz; exact leaf_6303_sound hz

theorem leaf_6304_ok : checkAt 527 1000 box_6304 cert_6304 = true := by
  have h := List.all_eq_true.mp batch_126_02_ok accepted_6304 (by simp [batch_126_02_values])
  exact h
theorem leaf_6304_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6304.profileLo box_6304.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6304_ok
theorem branch_box_6304_nonnegative : ∀ j, 0 ≤ branch_box_6304.lower j ∧ 0 ≤ branch_box_6304.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6304, Box.profileLo, Box.profileHi, box_6304]
theorem leaf_6304_BranchSafe : CertificateConsequences.BranchSafe branch_box_6304 := by
  left; refine ⟨branch_box_6304_nonnegative, ?_⟩
  intro z hz; exact leaf_6304_sound hz

theorem leaf_6311_ok : checkAt 527 1000 box_6311 cert_6311 = true := by
  have h := List.all_eq_true.mp batch_126_03_ok accepted_6311 (by simp [batch_126_03_values])
  exact h
theorem leaf_6311_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6311.profileLo box_6311.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6311_ok
theorem branch_box_6311_nonnegative : ∀ j, 0 ≤ branch_box_6311.lower j ∧ 0 ≤ branch_box_6311.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6311, Box.profileLo, Box.profileHi, box_6311]
theorem leaf_6311_BranchSafe : CertificateConsequences.BranchSafe branch_box_6311 := by
  left; refine ⟨branch_box_6311_nonnegative, ?_⟩
  intro z hz; exact leaf_6311_sound hz

theorem leaf_6312_ok : checkAt 527 1000 box_6312 cert_6312 = true := by
  have h := List.all_eq_true.mp batch_126_04_ok accepted_6312 (by simp [batch_126_04_values])
  exact h
theorem leaf_6312_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6312.profileLo box_6312.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6312_ok
theorem branch_box_6312_nonnegative : ∀ j, 0 ≤ branch_box_6312.lower j ∧ 0 ≤ branch_box_6312.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6312, Box.profileLo, Box.profileHi, box_6312]
theorem leaf_6312_BranchSafe : CertificateConsequences.BranchSafe branch_box_6312 := by
  left; refine ⟨branch_box_6312_nonnegative, ?_⟩
  intro z hz; exact leaf_6312_sound hz

theorem leaf_6313_ok : checkAt 527 1000 box_6313 cert_6313 = true := by
  have h := List.all_eq_true.mp batch_126_05_ok accepted_6313 (by simp [batch_126_05_values])
  exact h
theorem leaf_6313_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6313.profileLo box_6313.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6313_ok
theorem branch_box_6313_nonnegative : ∀ j, 0 ≤ branch_box_6313.lower j ∧ 0 ≤ branch_box_6313.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6313, Box.profileLo, Box.profileHi, box_6313]
theorem leaf_6313_BranchSafe : CertificateConsequences.BranchSafe branch_box_6313 := by
  left; refine ⟨branch_box_6313_nonnegative, ?_⟩
  intro z hz; exact leaf_6313_sound hz

theorem leaf_6314_ok : checkAt 527 1000 box_6314 cert_6314 = true := by
  have h := List.all_eq_true.mp batch_126_06_ok accepted_6314 (by simp [batch_126_06_values])
  exact h
theorem leaf_6314_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6314.profileLo box_6314.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6314_ok
theorem branch_box_6314_nonnegative : ∀ j, 0 ≤ branch_box_6314.lower j ∧ 0 ≤ branch_box_6314.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6314, Box.profileLo, Box.profileHi, box_6314]
theorem leaf_6314_BranchSafe : CertificateConsequences.BranchSafe branch_box_6314 := by
  left; refine ⟨branch_box_6314_nonnegative, ?_⟩
  intro z hz; exact leaf_6314_sound hz

theorem leaf_6317_ok : checkAt 527 1000 box_6317 cert_6317 = true := by
  have h := List.all_eq_true.mp batch_126_07_ok accepted_6317 (by simp [batch_126_07_values])
  exact h
theorem leaf_6317_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6317.profileLo box_6317.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6317_ok
theorem branch_box_6317_nonnegative : ∀ j, 0 ≤ branch_box_6317.lower j ∧ 0 ≤ branch_box_6317.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6317, Box.profileLo, Box.profileHi, box_6317]
theorem leaf_6317_BranchSafe : CertificateConsequences.BranchSafe branch_box_6317 := by
  left; refine ⟨branch_box_6317_nonnegative, ?_⟩
  intro z hz; exact leaf_6317_sound hz

theorem leaf_6318_ok : checkAt 527 1000 box_6318 cert_6318 = true := by
  have h := List.all_eq_true.mp batch_126_08_ok accepted_6318 (by simp [batch_126_08_values])
  exact h
theorem leaf_6318_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6318.profileLo box_6318.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6318_ok
theorem branch_box_6318_nonnegative : ∀ j, 0 ≤ branch_box_6318.lower j ∧ 0 ≤ branch_box_6318.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6318, Box.profileLo, Box.profileHi, box_6318]
theorem leaf_6318_BranchSafe : CertificateConsequences.BranchSafe branch_box_6318 := by
  left; refine ⟨branch_box_6318_nonnegative, ?_⟩
  intro z hz; exact leaf_6318_sound hz

theorem leaf_6323_ok : checkAt 527 1000 box_6323 cert_6323 = true := by
  have h := List.all_eq_true.mp batch_126_09_ok accepted_6323 (by simp [batch_126_09_values])
  exact h
theorem leaf_6323_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6323.profileLo box_6323.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6323_ok
theorem branch_box_6323_nonnegative : ∀ j, 0 ≤ branch_box_6323.lower j ∧ 0 ≤ branch_box_6323.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6323, Box.profileLo, Box.profileHi, box_6323]
theorem leaf_6323_BranchSafe : CertificateConsequences.BranchSafe branch_box_6323 := by
  left; refine ⟨branch_box_6323_nonnegative, ?_⟩
  intro z hz; exact leaf_6323_sound hz

theorem leaf_6328_ok : checkAt 527 1000 box_6328 cert_6328 = true := by
  have h := List.all_eq_true.mp batch_126_10_ok accepted_6328 (by simp [batch_126_10_values])
  exact h
theorem leaf_6328_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6328.profileLo box_6328.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6328_ok
theorem branch_box_6328_nonnegative : ∀ j, 0 ≤ branch_box_6328.lower j ∧ 0 ≤ branch_box_6328.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6328, Box.profileLo, Box.profileHi, box_6328]
theorem leaf_6328_BranchSafe : CertificateConsequences.BranchSafe branch_box_6328 := by
  left; refine ⟨branch_box_6328_nonnegative, ?_⟩
  intro z hz; exact leaf_6328_sound hz

theorem leaf_6329_ok : checkAt 527 1000 box_6329 cert_6329 = true := by
  have h := List.all_eq_true.mp batch_126_11_ok accepted_6329 (by simp [batch_126_11_values])
  exact h
theorem leaf_6329_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6329.profileLo box_6329.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6329_ok
theorem branch_box_6329_nonnegative : ∀ j, 0 ≤ branch_box_6329.lower j ∧ 0 ≤ branch_box_6329.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6329, Box.profileLo, Box.profileHi, box_6329]
theorem leaf_6329_BranchSafe : CertificateConsequences.BranchSafe branch_box_6329 := by
  left; refine ⟨branch_box_6329_nonnegative, ?_⟩
  intro z hz; exact leaf_6329_sound hz

theorem leaf_6331_ok : checkAt 527 1000 box_6331 cert_6331 = true := by
  have h := List.all_eq_true.mp batch_126_12_ok accepted_6331 (by simp [batch_126_12_values])
  exact h
theorem leaf_6331_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6331.profileLo box_6331.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6331_ok
theorem branch_box_6331_nonnegative : ∀ j, 0 ≤ branch_box_6331.lower j ∧ 0 ≤ branch_box_6331.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6331, Box.profileLo, Box.profileHi, box_6331]
theorem leaf_6331_BranchSafe : CertificateConsequences.BranchSafe branch_box_6331 := by
  left; refine ⟨branch_box_6331_nonnegative, ?_⟩
  intro z hz; exact leaf_6331_sound hz

theorem leaf_6333_ok : checkAt 527 1000 box_6333 cert_6333 = true := by
  have h := List.all_eq_true.mp batch_126_13_ok accepted_6333 (by simp [batch_126_13_values])
  exact h
theorem leaf_6333_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6333.profileLo box_6333.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6333_ok
theorem branch_box_6333_nonnegative : ∀ j, 0 ≤ branch_box_6333.lower j ∧ 0 ≤ branch_box_6333.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6333, Box.profileLo, Box.profileHi, box_6333]
theorem leaf_6333_BranchSafe : CertificateConsequences.BranchSafe branch_box_6333 := by
  left; refine ⟨branch_box_6333_nonnegative, ?_⟩
  intro z hz; exact leaf_6333_sound hz

theorem leaf_6334_ok : checkAt 527 1000 box_6334 cert_6334 = true := by
  have h := List.all_eq_true.mp batch_126_14_ok accepted_6334 (by simp [batch_126_14_values])
  exact h
theorem leaf_6334_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6334.profileLo box_6334.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6334_ok
theorem branch_box_6334_nonnegative : ∀ j, 0 ≤ branch_box_6334.lower j ∧ 0 ≤ branch_box_6334.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6334, Box.profileLo, Box.profileHi, box_6334]
theorem leaf_6334_BranchSafe : CertificateConsequences.BranchSafe branch_box_6334 := by
  left; refine ⟨branch_box_6334_nonnegative, ?_⟩
  intro z hz; exact leaf_6334_sound hz

theorem leaf_6337_ok : checkAt 527 1000 box_6337 cert_6337 = true := by
  have h := List.all_eq_true.mp batch_126_15_ok accepted_6337 (by simp [batch_126_15_values])
  exact h
theorem leaf_6337_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6337.profileLo box_6337.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6337_ok
theorem branch_box_6337_nonnegative : ∀ j, 0 ≤ branch_box_6337.lower j ∧ 0 ≤ branch_box_6337.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6337, Box.profileLo, Box.profileHi, box_6337]
theorem leaf_6337_BranchSafe : CertificateConsequences.BranchSafe branch_box_6337 := by
  left; refine ⟨branch_box_6337_nonnegative, ?_⟩
  intro z hz; exact leaf_6337_sound hz

theorem leaf_6338_ok : checkAt 527 1000 box_6338 cert_6338 = true := by
  have h := List.all_eq_true.mp batch_126_16_ok accepted_6338 (by simp [batch_126_16_values])
  exact h
theorem leaf_6338_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6338.profileLo box_6338.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6338_ok
theorem branch_box_6338_nonnegative : ∀ j, 0 ≤ branch_box_6338.lower j ∧ 0 ≤ branch_box_6338.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6338, Box.profileLo, Box.profileHi, box_6338]
theorem leaf_6338_BranchSafe : CertificateConsequences.BranchSafe branch_box_6338 := by
  left; refine ⟨branch_box_6338_nonnegative, ?_⟩
  intro z hz; exact leaf_6338_sound hz

theorem leaf_6340_ok : checkAt 527 1000 box_6340 cert_6340 = true := by
  have h := List.all_eq_true.mp batch_126_17_ok accepted_6340 (by simp [batch_126_17_values])
  exact h
theorem leaf_6340_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6340.profileLo box_6340.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6340_ok
theorem branch_box_6340_nonnegative : ∀ j, 0 ≤ branch_box_6340.lower j ∧ 0 ≤ branch_box_6340.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6340, Box.profileLo, Box.profileHi, box_6340]
theorem leaf_6340_BranchSafe : CertificateConsequences.BranchSafe branch_box_6340 := by
  left; refine ⟨branch_box_6340_nonnegative, ?_⟩
  intro z hz; exact leaf_6340_sound hz

theorem leaf_6342_ok : checkAt 527 1000 box_6342 cert_6342 = true := by
  have h := List.all_eq_true.mp batch_126_18_ok accepted_6342 (by simp [batch_126_18_values])
  exact h
theorem leaf_6342_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6342.profileLo box_6342.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6342_ok
theorem branch_box_6342_nonnegative : ∀ j, 0 ≤ branch_box_6342.lower j ∧ 0 ≤ branch_box_6342.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6342, Box.profileLo, Box.profileHi, box_6342]
theorem leaf_6342_BranchSafe : CertificateConsequences.BranchSafe branch_box_6342 := by
  left; refine ⟨branch_box_6342_nonnegative, ?_⟩
  intro z hz; exact leaf_6342_sound hz

theorem leaf_6345_ok : checkAt 527 1000 box_6345 cert_6345 = true := by
  have h := List.all_eq_true.mp batch_126_19_ok accepted_6345 (by simp [batch_126_19_values])
  exact h
theorem leaf_6345_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6345.profileLo box_6345.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6345_ok
theorem branch_box_6345_nonnegative : ∀ j, 0 ≤ branch_box_6345.lower j ∧ 0 ≤ branch_box_6345.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6345, Box.profileLo, Box.profileHi, box_6345]
theorem leaf_6345_BranchSafe : CertificateConsequences.BranchSafe branch_box_6345 := by
  left; refine ⟨branch_box_6345_nonnegative, ?_⟩
  intro z hz; exact leaf_6345_sound hz

#print axioms batch_126_00_ok
#print axioms leaf_6301_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
