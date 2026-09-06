import PeaceableQueens.UpperBound.Generated.Even.C527Scaled107Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_107_00_values : List Bool := [accepted_5350]
theorem batch_107_00_ok : batch_107_00_values.all id = true := by decide

def batch_107_01_values : List Bool := [accepted_5351]
theorem batch_107_01_ok : batch_107_01_values.all id = true := by decide

def batch_107_02_values : List Bool := [accepted_5352]
theorem batch_107_02_ok : batch_107_02_values.all id = true := by decide

def batch_107_03_values : List Bool := [accepted_5359]
theorem batch_107_03_ok : batch_107_03_values.all id = true := by decide

def batch_107_04_values : List Bool := [accepted_5365]
theorem batch_107_04_ok : batch_107_04_values.all id = true := by decide

def batch_107_05_values : List Bool := [accepted_5366]
theorem batch_107_05_ok : batch_107_05_values.all id = true := by decide

def batch_107_06_values : List Bool := [accepted_5368]
theorem batch_107_06_ok : batch_107_06_values.all id = true := by decide

def batch_107_07_values : List Bool := [accepted_5369]
theorem batch_107_07_ok : batch_107_07_values.all id = true := by decide

def batch_107_08_values : List Bool := [accepted_5370]
theorem batch_107_08_ok : batch_107_08_values.all id = true := by decide

def batch_107_09_values : List Bool := [accepted_5373]
theorem batch_107_09_ok : batch_107_09_values.all id = true := by decide

def batch_107_10_values : List Bool := [accepted_5374]
theorem batch_107_10_ok : batch_107_10_values.all id = true := by decide

def batch_107_11_values : List Bool := [accepted_5377]
theorem batch_107_11_ok : batch_107_11_values.all id = true := by decide

def batch_107_12_values : List Bool := [accepted_5378]
theorem batch_107_12_ok : batch_107_12_values.all id = true := by decide

def batch_107_13_values : List Bool := [accepted_5379]
theorem batch_107_13_ok : batch_107_13_values.all id = true := by decide

def batch_107_14_values : List Bool := [accepted_5380]
theorem batch_107_14_ok : batch_107_14_values.all id = true := by decide

def batch_107_15_values : List Bool := [accepted_5385]
theorem batch_107_15_ok : batch_107_15_values.all id = true := by decide

def batch_107_16_values : List Bool := [accepted_5387]
theorem batch_107_16_ok : batch_107_16_values.all id = true := by decide

def batch_107_17_values : List Bool := [accepted_5388]
theorem batch_107_17_ok : batch_107_17_values.all id = true := by decide

def batch_107_18_values : List Bool := [accepted_5389]
theorem batch_107_18_ok : batch_107_18_values.all id = true := by decide

def batch_107_19_values : List Bool := [accepted_5391]
theorem batch_107_19_ok : batch_107_19_values.all id = true := by decide

def batch_107_20_values : List Bool := [accepted_5392]
theorem batch_107_20_ok : batch_107_20_values.all id = true := by decide

def batch_107_21_values : List Bool := [accepted_5395]
theorem batch_107_21_ok : batch_107_21_values.all id = true := by decide

def batch_107_22_values : List Bool := [accepted_5397]
theorem batch_107_22_ok : batch_107_22_values.all id = true := by decide

def batch_107_23_values : List Bool := [accepted_5398]
theorem batch_107_23_ok : batch_107_23_values.all id = true := by decide

theorem leaf_5350_ok : checkAt 527 1000 box_5350 cert_5350 = true := by
  have h := List.all_eq_true.mp batch_107_00_ok accepted_5350 (by simp [batch_107_00_values])
  exact h
theorem leaf_5350_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5350.profileLo box_5350.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5350_ok
theorem branch_box_5350_nonnegative : ∀ j, 0 ≤ branch_box_5350.lower j ∧ 0 ≤ branch_box_5350.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5350, Box.profileLo, Box.profileHi, box_5350]
theorem leaf_5350_BranchSafe : CertificateConsequences.BranchSafe branch_box_5350 := by
  left; refine ⟨branch_box_5350_nonnegative, ?_⟩
  intro z hz; exact leaf_5350_sound hz

theorem leaf_5351_ok : checkAt 527 1000 box_5351 cert_5351 = true := by
  have h := List.all_eq_true.mp batch_107_01_ok accepted_5351 (by simp [batch_107_01_values])
  exact h
theorem leaf_5351_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5351.profileLo box_5351.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5351_ok
theorem branch_box_5351_nonnegative : ∀ j, 0 ≤ branch_box_5351.lower j ∧ 0 ≤ branch_box_5351.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5351, Box.profileLo, Box.profileHi, box_5351]
theorem leaf_5351_BranchSafe : CertificateConsequences.BranchSafe branch_box_5351 := by
  left; refine ⟨branch_box_5351_nonnegative, ?_⟩
  intro z hz; exact leaf_5351_sound hz

theorem leaf_5352_ok : checkAt 527 1000 box_5352 cert_5352 = true := by
  have h := List.all_eq_true.mp batch_107_02_ok accepted_5352 (by simp [batch_107_02_values])
  exact h
theorem leaf_5352_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5352.profileLo box_5352.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5352_ok
theorem branch_box_5352_nonnegative : ∀ j, 0 ≤ branch_box_5352.lower j ∧ 0 ≤ branch_box_5352.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5352, Box.profileLo, Box.profileHi, box_5352]
theorem leaf_5352_BranchSafe : CertificateConsequences.BranchSafe branch_box_5352 := by
  left; refine ⟨branch_box_5352_nonnegative, ?_⟩
  intro z hz; exact leaf_5352_sound hz

theorem leaf_5359_ok : checkAt 527 1000 box_5359 cert_5359 = true := by
  have h := List.all_eq_true.mp batch_107_03_ok accepted_5359 (by simp [batch_107_03_values])
  exact h
theorem leaf_5359_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5359.profileLo box_5359.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5359_ok
theorem branch_box_5359_nonnegative : ∀ j, 0 ≤ branch_box_5359.lower j ∧ 0 ≤ branch_box_5359.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5359, Box.profileLo, Box.profileHi, box_5359]
theorem leaf_5359_BranchSafe : CertificateConsequences.BranchSafe branch_box_5359 := by
  left; refine ⟨branch_box_5359_nonnegative, ?_⟩
  intro z hz; exact leaf_5359_sound hz

theorem leaf_5365_ok : checkAt 527 1000 box_5365 cert_5365 = true := by
  have h := List.all_eq_true.mp batch_107_04_ok accepted_5365 (by simp [batch_107_04_values])
  exact h
theorem leaf_5365_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5365.profileLo box_5365.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5365_ok
theorem branch_box_5365_nonnegative : ∀ j, 0 ≤ branch_box_5365.lower j ∧ 0 ≤ branch_box_5365.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5365, Box.profileLo, Box.profileHi, box_5365]
theorem leaf_5365_BranchSafe : CertificateConsequences.BranchSafe branch_box_5365 := by
  left; refine ⟨branch_box_5365_nonnegative, ?_⟩
  intro z hz; exact leaf_5365_sound hz

theorem leaf_5366_ok : checkAt 527 1000 box_5366 cert_5366 = true := by
  have h := List.all_eq_true.mp batch_107_05_ok accepted_5366 (by simp [batch_107_05_values])
  exact h
theorem leaf_5366_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5366.profileLo box_5366.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5366_ok
theorem branch_box_5366_nonnegative : ∀ j, 0 ≤ branch_box_5366.lower j ∧ 0 ≤ branch_box_5366.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5366, Box.profileLo, Box.profileHi, box_5366]
theorem leaf_5366_BranchSafe : CertificateConsequences.BranchSafe branch_box_5366 := by
  left; refine ⟨branch_box_5366_nonnegative, ?_⟩
  intro z hz; exact leaf_5366_sound hz

theorem leaf_5368_ok : checkAt 527 1000 box_5368 cert_5368 = true := by
  have h := List.all_eq_true.mp batch_107_06_ok accepted_5368 (by simp [batch_107_06_values])
  exact h
theorem leaf_5368_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5368.profileLo box_5368.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5368_ok
theorem branch_box_5368_nonnegative : ∀ j, 0 ≤ branch_box_5368.lower j ∧ 0 ≤ branch_box_5368.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5368, Box.profileLo, Box.profileHi, box_5368]
theorem leaf_5368_BranchSafe : CertificateConsequences.BranchSafe branch_box_5368 := by
  left; refine ⟨branch_box_5368_nonnegative, ?_⟩
  intro z hz; exact leaf_5368_sound hz

theorem leaf_5369_ok : checkAt 527 1000 box_5369 cert_5369 = true := by
  have h := List.all_eq_true.mp batch_107_07_ok accepted_5369 (by simp [batch_107_07_values])
  exact h
theorem leaf_5369_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5369.profileLo box_5369.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5369_ok
theorem branch_box_5369_nonnegative : ∀ j, 0 ≤ branch_box_5369.lower j ∧ 0 ≤ branch_box_5369.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5369, Box.profileLo, Box.profileHi, box_5369]
theorem leaf_5369_BranchSafe : CertificateConsequences.BranchSafe branch_box_5369 := by
  left; refine ⟨branch_box_5369_nonnegative, ?_⟩
  intro z hz; exact leaf_5369_sound hz

theorem leaf_5370_ok : checkAt 527 1000 box_5370 cert_5370 = true := by
  have h := List.all_eq_true.mp batch_107_08_ok accepted_5370 (by simp [batch_107_08_values])
  exact h
theorem leaf_5370_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5370.profileLo box_5370.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5370_ok
theorem branch_box_5370_nonnegative : ∀ j, 0 ≤ branch_box_5370.lower j ∧ 0 ≤ branch_box_5370.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5370, Box.profileLo, Box.profileHi, box_5370]
theorem leaf_5370_BranchSafe : CertificateConsequences.BranchSafe branch_box_5370 := by
  left; refine ⟨branch_box_5370_nonnegative, ?_⟩
  intro z hz; exact leaf_5370_sound hz

theorem leaf_5373_ok : checkAt 527 1000 box_5373 cert_5373 = true := by
  have h := List.all_eq_true.mp batch_107_09_ok accepted_5373 (by simp [batch_107_09_values])
  exact h
theorem leaf_5373_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5373.profileLo box_5373.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5373_ok
theorem branch_box_5373_nonnegative : ∀ j, 0 ≤ branch_box_5373.lower j ∧ 0 ≤ branch_box_5373.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5373, Box.profileLo, Box.profileHi, box_5373]
theorem leaf_5373_BranchSafe : CertificateConsequences.BranchSafe branch_box_5373 := by
  left; refine ⟨branch_box_5373_nonnegative, ?_⟩
  intro z hz; exact leaf_5373_sound hz

theorem leaf_5374_ok : checkAt 527 1000 box_5374 cert_5374 = true := by
  have h := List.all_eq_true.mp batch_107_10_ok accepted_5374 (by simp [batch_107_10_values])
  exact h
theorem leaf_5374_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5374.profileLo box_5374.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5374_ok
theorem branch_box_5374_nonnegative : ∀ j, 0 ≤ branch_box_5374.lower j ∧ 0 ≤ branch_box_5374.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5374, Box.profileLo, Box.profileHi, box_5374]
theorem leaf_5374_BranchSafe : CertificateConsequences.BranchSafe branch_box_5374 := by
  left; refine ⟨branch_box_5374_nonnegative, ?_⟩
  intro z hz; exact leaf_5374_sound hz

theorem leaf_5377_ok : checkAt 527 1000 box_5377 cert_5377 = true := by
  have h := List.all_eq_true.mp batch_107_11_ok accepted_5377 (by simp [batch_107_11_values])
  exact h
theorem leaf_5377_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5377.profileLo box_5377.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5377_ok
theorem branch_box_5377_nonnegative : ∀ j, 0 ≤ branch_box_5377.lower j ∧ 0 ≤ branch_box_5377.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5377, Box.profileLo, Box.profileHi, box_5377]
theorem leaf_5377_BranchSafe : CertificateConsequences.BranchSafe branch_box_5377 := by
  left; refine ⟨branch_box_5377_nonnegative, ?_⟩
  intro z hz; exact leaf_5377_sound hz

theorem leaf_5378_ok : checkAt 527 1000 box_5378 cert_5378 = true := by
  have h := List.all_eq_true.mp batch_107_12_ok accepted_5378 (by simp [batch_107_12_values])
  exact h
theorem leaf_5378_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5378.profileLo box_5378.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5378_ok
theorem branch_box_5378_nonnegative : ∀ j, 0 ≤ branch_box_5378.lower j ∧ 0 ≤ branch_box_5378.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5378, Box.profileLo, Box.profileHi, box_5378]
theorem leaf_5378_BranchSafe : CertificateConsequences.BranchSafe branch_box_5378 := by
  left; refine ⟨branch_box_5378_nonnegative, ?_⟩
  intro z hz; exact leaf_5378_sound hz

theorem leaf_5379_ok : checkAt 527 1000 box_5379 cert_5379 = true := by
  have h := List.all_eq_true.mp batch_107_13_ok accepted_5379 (by simp [batch_107_13_values])
  exact h
theorem leaf_5379_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5379.profileLo box_5379.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5379_ok
theorem branch_box_5379_nonnegative : ∀ j, 0 ≤ branch_box_5379.lower j ∧ 0 ≤ branch_box_5379.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5379, Box.profileLo, Box.profileHi, box_5379]
theorem leaf_5379_BranchSafe : CertificateConsequences.BranchSafe branch_box_5379 := by
  left; refine ⟨branch_box_5379_nonnegative, ?_⟩
  intro z hz; exact leaf_5379_sound hz

theorem leaf_5380_ok : checkAt 527 1000 box_5380 cert_5380 = true := by
  have h := List.all_eq_true.mp batch_107_14_ok accepted_5380 (by simp [batch_107_14_values])
  exact h
theorem leaf_5380_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5380.profileLo box_5380.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5380_ok
theorem branch_box_5380_nonnegative : ∀ j, 0 ≤ branch_box_5380.lower j ∧ 0 ≤ branch_box_5380.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5380, Box.profileLo, Box.profileHi, box_5380]
theorem leaf_5380_BranchSafe : CertificateConsequences.BranchSafe branch_box_5380 := by
  left; refine ⟨branch_box_5380_nonnegative, ?_⟩
  intro z hz; exact leaf_5380_sound hz

theorem leaf_5385_ok : checkAt 527 1000 box_5385 cert_5385 = true := by
  have h := List.all_eq_true.mp batch_107_15_ok accepted_5385 (by simp [batch_107_15_values])
  exact h
theorem leaf_5385_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5385.profileLo box_5385.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5385_ok
theorem branch_box_5385_nonnegative : ∀ j, 0 ≤ branch_box_5385.lower j ∧ 0 ≤ branch_box_5385.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5385, Box.profileLo, Box.profileHi, box_5385]
theorem leaf_5385_BranchSafe : CertificateConsequences.BranchSafe branch_box_5385 := by
  left; refine ⟨branch_box_5385_nonnegative, ?_⟩
  intro z hz; exact leaf_5385_sound hz

theorem leaf_5387_ok : checkAt 527 1000 box_5387 cert_5387 = true := by
  have h := List.all_eq_true.mp batch_107_16_ok accepted_5387 (by simp [batch_107_16_values])
  exact h
theorem leaf_5387_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5387.profileLo box_5387.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5387_ok
theorem branch_box_5387_nonnegative : ∀ j, 0 ≤ branch_box_5387.lower j ∧ 0 ≤ branch_box_5387.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5387, Box.profileLo, Box.profileHi, box_5387]
theorem leaf_5387_BranchSafe : CertificateConsequences.BranchSafe branch_box_5387 := by
  left; refine ⟨branch_box_5387_nonnegative, ?_⟩
  intro z hz; exact leaf_5387_sound hz

theorem leaf_5388_ok : checkAt 527 1000 box_5388 cert_5388 = true := by
  have h := List.all_eq_true.mp batch_107_17_ok accepted_5388 (by simp [batch_107_17_values])
  exact h
theorem leaf_5388_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5388.profileLo box_5388.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5388_ok
theorem branch_box_5388_nonnegative : ∀ j, 0 ≤ branch_box_5388.lower j ∧ 0 ≤ branch_box_5388.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5388, Box.profileLo, Box.profileHi, box_5388]
theorem leaf_5388_BranchSafe : CertificateConsequences.BranchSafe branch_box_5388 := by
  left; refine ⟨branch_box_5388_nonnegative, ?_⟩
  intro z hz; exact leaf_5388_sound hz

theorem leaf_5389_ok : checkAt 527 1000 box_5389 cert_5389 = true := by
  have h := List.all_eq_true.mp batch_107_18_ok accepted_5389 (by simp [batch_107_18_values])
  exact h
theorem leaf_5389_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5389.profileLo box_5389.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5389_ok
theorem branch_box_5389_nonnegative : ∀ j, 0 ≤ branch_box_5389.lower j ∧ 0 ≤ branch_box_5389.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5389, Box.profileLo, Box.profileHi, box_5389]
theorem leaf_5389_BranchSafe : CertificateConsequences.BranchSafe branch_box_5389 := by
  left; refine ⟨branch_box_5389_nonnegative, ?_⟩
  intro z hz; exact leaf_5389_sound hz

theorem leaf_5391_ok : checkAt 527 1000 box_5391 cert_5391 = true := by
  have h := List.all_eq_true.mp batch_107_19_ok accepted_5391 (by simp [batch_107_19_values])
  exact h
theorem leaf_5391_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5391.profileLo box_5391.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5391_ok
theorem branch_box_5391_nonnegative : ∀ j, 0 ≤ branch_box_5391.lower j ∧ 0 ≤ branch_box_5391.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5391, Box.profileLo, Box.profileHi, box_5391]
theorem leaf_5391_BranchSafe : CertificateConsequences.BranchSafe branch_box_5391 := by
  left; refine ⟨branch_box_5391_nonnegative, ?_⟩
  intro z hz; exact leaf_5391_sound hz

theorem leaf_5392_ok : checkAt 527 1000 box_5392 cert_5392 = true := by
  have h := List.all_eq_true.mp batch_107_20_ok accepted_5392 (by simp [batch_107_20_values])
  exact h
theorem leaf_5392_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5392.profileLo box_5392.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5392_ok
theorem branch_box_5392_nonnegative : ∀ j, 0 ≤ branch_box_5392.lower j ∧ 0 ≤ branch_box_5392.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5392, Box.profileLo, Box.profileHi, box_5392]
theorem leaf_5392_BranchSafe : CertificateConsequences.BranchSafe branch_box_5392 := by
  left; refine ⟨branch_box_5392_nonnegative, ?_⟩
  intro z hz; exact leaf_5392_sound hz

theorem leaf_5395_ok : checkAt 527 1000 box_5395 cert_5395 = true := by
  have h := List.all_eq_true.mp batch_107_21_ok accepted_5395 (by simp [batch_107_21_values])
  exact h
theorem leaf_5395_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5395.profileLo box_5395.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5395_ok
theorem branch_box_5395_nonnegative : ∀ j, 0 ≤ branch_box_5395.lower j ∧ 0 ≤ branch_box_5395.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5395, Box.profileLo, Box.profileHi, box_5395]
theorem leaf_5395_BranchSafe : CertificateConsequences.BranchSafe branch_box_5395 := by
  left; refine ⟨branch_box_5395_nonnegative, ?_⟩
  intro z hz; exact leaf_5395_sound hz

theorem leaf_5397_ok : checkAt 527 1000 box_5397 cert_5397 = true := by
  have h := List.all_eq_true.mp batch_107_22_ok accepted_5397 (by simp [batch_107_22_values])
  exact h
theorem leaf_5397_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5397.profileLo box_5397.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5397_ok
theorem branch_box_5397_nonnegative : ∀ j, 0 ≤ branch_box_5397.lower j ∧ 0 ≤ branch_box_5397.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5397, Box.profileLo, Box.profileHi, box_5397]
theorem leaf_5397_BranchSafe : CertificateConsequences.BranchSafe branch_box_5397 := by
  left; refine ⟨branch_box_5397_nonnegative, ?_⟩
  intro z hz; exact leaf_5397_sound hz

theorem leaf_5398_ok : checkAt 527 1000 box_5398 cert_5398 = true := by
  have h := List.all_eq_true.mp batch_107_23_ok accepted_5398 (by simp [batch_107_23_values])
  exact h
theorem leaf_5398_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5398.profileLo box_5398.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5398_ok
theorem branch_box_5398_nonnegative : ∀ j, 0 ≤ branch_box_5398.lower j ∧ 0 ≤ branch_box_5398.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5398, Box.profileLo, Box.profileHi, box_5398]
theorem leaf_5398_BranchSafe : CertificateConsequences.BranchSafe branch_box_5398 := by
  left; refine ⟨branch_box_5398_nonnegative, ?_⟩
  intro z hz; exact leaf_5398_sound hz

#print axioms batch_107_00_ok
#print axioms leaf_5350_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
