import PeaceableQueens.UpperBound.Generated.Even.C527Scaled102Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_102_00_values : List Bool := [accepted_5107]
theorem batch_102_00_ok : batch_102_00_values.all id = true := by decide

def batch_102_01_values : List Bool := [accepted_5108]
theorem batch_102_01_ok : batch_102_01_values.all id = true := by decide

def batch_102_02_values : List Bool := [accepted_5109]
theorem batch_102_02_ok : batch_102_02_values.all id = true := by decide

def batch_102_03_values : List Bool := [accepted_5110]
theorem batch_102_03_ok : batch_102_03_values.all id = true := by decide

def batch_102_04_values : List Bool := [accepted_5112]
theorem batch_102_04_ok : batch_102_04_values.all id = true := by decide

def batch_102_05_values : List Bool := [accepted_5113]
theorem batch_102_05_ok : batch_102_05_values.all id = true := by decide

def batch_102_06_values : List Bool := [accepted_5114]
theorem batch_102_06_ok : batch_102_06_values.all id = true := by decide

def batch_102_07_values : List Bool := [accepted_5120]
theorem batch_102_07_ok : batch_102_07_values.all id = true := by decide

def batch_102_08_values : List Bool := [accepted_5121]
theorem batch_102_08_ok : batch_102_08_values.all id = true := by decide

def batch_102_09_values : List Bool := [accepted_5122]
theorem batch_102_09_ok : batch_102_09_values.all id = true := by decide

def batch_102_10_values : List Bool := [accepted_5123]
theorem batch_102_10_ok : batch_102_10_values.all id = true := by decide

def batch_102_11_values : List Bool := [accepted_5125]
theorem batch_102_11_ok : batch_102_11_values.all id = true := by decide

def batch_102_12_values : List Bool := [accepted_5126]
theorem batch_102_12_ok : batch_102_12_values.all id = true := by decide

def batch_102_13_values : List Bool := [accepted_5127]
theorem batch_102_13_ok : batch_102_13_values.all id = true := by decide

def batch_102_14_values : List Bool := [accepted_5129]
theorem batch_102_14_ok : batch_102_14_values.all id = true := by decide

def batch_102_15_values : List Bool := [accepted_5130]
theorem batch_102_15_ok : batch_102_15_values.all id = true := by decide

def batch_102_16_values : List Bool := [accepted_5135]
theorem batch_102_16_ok : batch_102_16_values.all id = true := by decide

def batch_102_17_values : List Bool := [accepted_5136]
theorem batch_102_17_ok : batch_102_17_values.all id = true := by decide

def batch_102_18_values : List Bool := [accepted_5137]
theorem batch_102_18_ok : batch_102_18_values.all id = true := by decide

def batch_102_19_values : List Bool := [accepted_5139]
theorem batch_102_19_ok : batch_102_19_values.all id = true := by decide

def batch_102_20_values : List Bool := [accepted_5140]
theorem batch_102_20_ok : batch_102_20_values.all id = true := by decide

def batch_102_21_values : List Bool := [accepted_5141]
theorem batch_102_21_ok : batch_102_21_values.all id = true := by decide

def batch_102_22_values : List Bool := [accepted_5142]
theorem batch_102_22_ok : batch_102_22_values.all id = true := by decide

def batch_102_23_values : List Bool := [accepted_5149]
theorem batch_102_23_ok : batch_102_23_values.all id = true := by decide

theorem leaf_5107_ok : checkAt 527 1000 box_5107 cert_5107 = true := by
  have h := List.all_eq_true.mp batch_102_00_ok accepted_5107 (by simp [batch_102_00_values])
  exact h
theorem leaf_5107_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5107.profileLo box_5107.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5107_ok
theorem branch_box_5107_nonnegative : ∀ j, 0 ≤ branch_box_5107.lower j ∧ 0 ≤ branch_box_5107.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5107, Box.profileLo, Box.profileHi, box_5107]
theorem leaf_5107_BranchSafe : CertificateConsequences.BranchSafe branch_box_5107 := by
  left; refine ⟨branch_box_5107_nonnegative, ?_⟩
  intro z hz; exact leaf_5107_sound hz

theorem leaf_5108_ok : checkAt 527 1000 box_5108 cert_5108 = true := by
  have h := List.all_eq_true.mp batch_102_01_ok accepted_5108 (by simp [batch_102_01_values])
  exact h
theorem leaf_5108_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5108.profileLo box_5108.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5108_ok
theorem branch_box_5108_nonnegative : ∀ j, 0 ≤ branch_box_5108.lower j ∧ 0 ≤ branch_box_5108.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5108, Box.profileLo, Box.profileHi, box_5108]
theorem leaf_5108_BranchSafe : CertificateConsequences.BranchSafe branch_box_5108 := by
  left; refine ⟨branch_box_5108_nonnegative, ?_⟩
  intro z hz; exact leaf_5108_sound hz

theorem leaf_5109_ok : checkAt 527 1000 box_5109 cert_5109 = true := by
  have h := List.all_eq_true.mp batch_102_02_ok accepted_5109 (by simp [batch_102_02_values])
  exact h
theorem leaf_5109_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5109.profileLo box_5109.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5109_ok
theorem branch_box_5109_nonnegative : ∀ j, 0 ≤ branch_box_5109.lower j ∧ 0 ≤ branch_box_5109.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5109, Box.profileLo, Box.profileHi, box_5109]
theorem leaf_5109_BranchSafe : CertificateConsequences.BranchSafe branch_box_5109 := by
  left; refine ⟨branch_box_5109_nonnegative, ?_⟩
  intro z hz; exact leaf_5109_sound hz

theorem leaf_5110_ok : checkAt 527 1000 box_5110 cert_5110 = true := by
  have h := List.all_eq_true.mp batch_102_03_ok accepted_5110 (by simp [batch_102_03_values])
  exact h
theorem leaf_5110_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5110.profileLo box_5110.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5110_ok
theorem branch_box_5110_nonnegative : ∀ j, 0 ≤ branch_box_5110.lower j ∧ 0 ≤ branch_box_5110.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5110, Box.profileLo, Box.profileHi, box_5110]
theorem leaf_5110_BranchSafe : CertificateConsequences.BranchSafe branch_box_5110 := by
  left; refine ⟨branch_box_5110_nonnegative, ?_⟩
  intro z hz; exact leaf_5110_sound hz

theorem leaf_5112_ok : checkAt 527 1000 box_5112 cert_5112 = true := by
  have h := List.all_eq_true.mp batch_102_04_ok accepted_5112 (by simp [batch_102_04_values])
  exact h
theorem leaf_5112_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5112.profileLo box_5112.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5112_ok
theorem branch_box_5112_nonnegative : ∀ j, 0 ≤ branch_box_5112.lower j ∧ 0 ≤ branch_box_5112.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5112, Box.profileLo, Box.profileHi, box_5112]
theorem leaf_5112_BranchSafe : CertificateConsequences.BranchSafe branch_box_5112 := by
  left; refine ⟨branch_box_5112_nonnegative, ?_⟩
  intro z hz; exact leaf_5112_sound hz

theorem leaf_5113_ok : checkAt 527 1000 box_5113 cert_5113 = true := by
  have h := List.all_eq_true.mp batch_102_05_ok accepted_5113 (by simp [batch_102_05_values])
  exact h
theorem leaf_5113_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5113.profileLo box_5113.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5113_ok
theorem branch_box_5113_nonnegative : ∀ j, 0 ≤ branch_box_5113.lower j ∧ 0 ≤ branch_box_5113.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5113, Box.profileLo, Box.profileHi, box_5113]
theorem leaf_5113_BranchSafe : CertificateConsequences.BranchSafe branch_box_5113 := by
  left; refine ⟨branch_box_5113_nonnegative, ?_⟩
  intro z hz; exact leaf_5113_sound hz

theorem leaf_5114_ok : checkAt 527 1000 box_5114 cert_5114 = true := by
  have h := List.all_eq_true.mp batch_102_06_ok accepted_5114 (by simp [batch_102_06_values])
  exact h
theorem leaf_5114_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5114.profileLo box_5114.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5114_ok
theorem branch_box_5114_nonnegative : ∀ j, 0 ≤ branch_box_5114.lower j ∧ 0 ≤ branch_box_5114.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5114, Box.profileLo, Box.profileHi, box_5114]
theorem leaf_5114_BranchSafe : CertificateConsequences.BranchSafe branch_box_5114 := by
  left; refine ⟨branch_box_5114_nonnegative, ?_⟩
  intro z hz; exact leaf_5114_sound hz

theorem leaf_5120_ok : checkAt 527 1000 box_5120 cert_5120 = true := by
  have h := List.all_eq_true.mp batch_102_07_ok accepted_5120 (by simp [batch_102_07_values])
  exact h
theorem leaf_5120_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5120.profileLo box_5120.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5120_ok
theorem branch_box_5120_nonnegative : ∀ j, 0 ≤ branch_box_5120.lower j ∧ 0 ≤ branch_box_5120.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5120, Box.profileLo, Box.profileHi, box_5120]
theorem leaf_5120_BranchSafe : CertificateConsequences.BranchSafe branch_box_5120 := by
  left; refine ⟨branch_box_5120_nonnegative, ?_⟩
  intro z hz; exact leaf_5120_sound hz

theorem leaf_5121_ok : checkAt 527 1000 box_5121 cert_5121 = true := by
  have h := List.all_eq_true.mp batch_102_08_ok accepted_5121 (by simp [batch_102_08_values])
  exact h
theorem leaf_5121_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5121.profileLo box_5121.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5121_ok
theorem branch_box_5121_nonnegative : ∀ j, 0 ≤ branch_box_5121.lower j ∧ 0 ≤ branch_box_5121.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5121, Box.profileLo, Box.profileHi, box_5121]
theorem leaf_5121_BranchSafe : CertificateConsequences.BranchSafe branch_box_5121 := by
  left; refine ⟨branch_box_5121_nonnegative, ?_⟩
  intro z hz; exact leaf_5121_sound hz

theorem leaf_5122_ok : checkAt 527 1000 box_5122 cert_5122 = true := by
  have h := List.all_eq_true.mp batch_102_09_ok accepted_5122 (by simp [batch_102_09_values])
  exact h
theorem leaf_5122_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5122.profileLo box_5122.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5122_ok
theorem branch_box_5122_nonnegative : ∀ j, 0 ≤ branch_box_5122.lower j ∧ 0 ≤ branch_box_5122.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5122, Box.profileLo, Box.profileHi, box_5122]
theorem leaf_5122_BranchSafe : CertificateConsequences.BranchSafe branch_box_5122 := by
  left; refine ⟨branch_box_5122_nonnegative, ?_⟩
  intro z hz; exact leaf_5122_sound hz

theorem leaf_5123_ok : checkAt 527 1000 box_5123 cert_5123 = true := by
  have h := List.all_eq_true.mp batch_102_10_ok accepted_5123 (by simp [batch_102_10_values])
  exact h
theorem leaf_5123_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5123.profileLo box_5123.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5123_ok
theorem branch_box_5123_nonnegative : ∀ j, 0 ≤ branch_box_5123.lower j ∧ 0 ≤ branch_box_5123.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5123, Box.profileLo, Box.profileHi, box_5123]
theorem leaf_5123_BranchSafe : CertificateConsequences.BranchSafe branch_box_5123 := by
  left; refine ⟨branch_box_5123_nonnegative, ?_⟩
  intro z hz; exact leaf_5123_sound hz

theorem leaf_5125_ok : checkAt 527 1000 box_5125 cert_5125 = true := by
  have h := List.all_eq_true.mp batch_102_11_ok accepted_5125 (by simp [batch_102_11_values])
  exact h
theorem leaf_5125_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5125.profileLo box_5125.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5125_ok
theorem branch_box_5125_nonnegative : ∀ j, 0 ≤ branch_box_5125.lower j ∧ 0 ≤ branch_box_5125.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5125, Box.profileLo, Box.profileHi, box_5125]
theorem leaf_5125_BranchSafe : CertificateConsequences.BranchSafe branch_box_5125 := by
  left; refine ⟨branch_box_5125_nonnegative, ?_⟩
  intro z hz; exact leaf_5125_sound hz

theorem leaf_5126_ok : checkAt 527 1000 box_5126 cert_5126 = true := by
  have h := List.all_eq_true.mp batch_102_12_ok accepted_5126 (by simp [batch_102_12_values])
  exact h
theorem leaf_5126_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5126.profileLo box_5126.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5126_ok
theorem branch_box_5126_nonnegative : ∀ j, 0 ≤ branch_box_5126.lower j ∧ 0 ≤ branch_box_5126.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5126, Box.profileLo, Box.profileHi, box_5126]
theorem leaf_5126_BranchSafe : CertificateConsequences.BranchSafe branch_box_5126 := by
  left; refine ⟨branch_box_5126_nonnegative, ?_⟩
  intro z hz; exact leaf_5126_sound hz

theorem leaf_5127_ok : checkAt 527 1000 box_5127 cert_5127 = true := by
  have h := List.all_eq_true.mp batch_102_13_ok accepted_5127 (by simp [batch_102_13_values])
  exact h
theorem leaf_5127_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5127.profileLo box_5127.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5127_ok
theorem branch_box_5127_nonnegative : ∀ j, 0 ≤ branch_box_5127.lower j ∧ 0 ≤ branch_box_5127.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5127, Box.profileLo, Box.profileHi, box_5127]
theorem leaf_5127_BranchSafe : CertificateConsequences.BranchSafe branch_box_5127 := by
  left; refine ⟨branch_box_5127_nonnegative, ?_⟩
  intro z hz; exact leaf_5127_sound hz

theorem leaf_5129_ok : checkAt 527 1000 box_5129 cert_5129 = true := by
  have h := List.all_eq_true.mp batch_102_14_ok accepted_5129 (by simp [batch_102_14_values])
  exact h
theorem leaf_5129_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5129.profileLo box_5129.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5129_ok
theorem branch_box_5129_nonnegative : ∀ j, 0 ≤ branch_box_5129.lower j ∧ 0 ≤ branch_box_5129.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5129, Box.profileLo, Box.profileHi, box_5129]
theorem leaf_5129_BranchSafe : CertificateConsequences.BranchSafe branch_box_5129 := by
  left; refine ⟨branch_box_5129_nonnegative, ?_⟩
  intro z hz; exact leaf_5129_sound hz

theorem leaf_5130_ok : checkAt 527 1000 box_5130 cert_5130 = true := by
  have h := List.all_eq_true.mp batch_102_15_ok accepted_5130 (by simp [batch_102_15_values])
  exact h
theorem leaf_5130_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5130.profileLo box_5130.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5130_ok
theorem branch_box_5130_nonnegative : ∀ j, 0 ≤ branch_box_5130.lower j ∧ 0 ≤ branch_box_5130.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5130, Box.profileLo, Box.profileHi, box_5130]
theorem leaf_5130_BranchSafe : CertificateConsequences.BranchSafe branch_box_5130 := by
  left; refine ⟨branch_box_5130_nonnegative, ?_⟩
  intro z hz; exact leaf_5130_sound hz

theorem leaf_5135_ok : checkAt 527 1000 box_5135 cert_5135 = true := by
  have h := List.all_eq_true.mp batch_102_16_ok accepted_5135 (by simp [batch_102_16_values])
  exact h
theorem leaf_5135_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5135.profileLo box_5135.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5135_ok
theorem branch_box_5135_nonnegative : ∀ j, 0 ≤ branch_box_5135.lower j ∧ 0 ≤ branch_box_5135.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5135, Box.profileLo, Box.profileHi, box_5135]
theorem leaf_5135_BranchSafe : CertificateConsequences.BranchSafe branch_box_5135 := by
  left; refine ⟨branch_box_5135_nonnegative, ?_⟩
  intro z hz; exact leaf_5135_sound hz

theorem leaf_5136_ok : checkAt 527 1000 box_5136 cert_5136 = true := by
  have h := List.all_eq_true.mp batch_102_17_ok accepted_5136 (by simp [batch_102_17_values])
  exact h
theorem leaf_5136_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5136.profileLo box_5136.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5136_ok
theorem branch_box_5136_nonnegative : ∀ j, 0 ≤ branch_box_5136.lower j ∧ 0 ≤ branch_box_5136.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5136, Box.profileLo, Box.profileHi, box_5136]
theorem leaf_5136_BranchSafe : CertificateConsequences.BranchSafe branch_box_5136 := by
  left; refine ⟨branch_box_5136_nonnegative, ?_⟩
  intro z hz; exact leaf_5136_sound hz

theorem leaf_5137_ok : checkAt 527 1000 box_5137 cert_5137 = true := by
  have h := List.all_eq_true.mp batch_102_18_ok accepted_5137 (by simp [batch_102_18_values])
  exact h
theorem leaf_5137_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5137.profileLo box_5137.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5137_ok
theorem branch_box_5137_nonnegative : ∀ j, 0 ≤ branch_box_5137.lower j ∧ 0 ≤ branch_box_5137.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5137, Box.profileLo, Box.profileHi, box_5137]
theorem leaf_5137_BranchSafe : CertificateConsequences.BranchSafe branch_box_5137 := by
  left; refine ⟨branch_box_5137_nonnegative, ?_⟩
  intro z hz; exact leaf_5137_sound hz

theorem leaf_5139_ok : checkAt 527 1000 box_5139 cert_5139 = true := by
  have h := List.all_eq_true.mp batch_102_19_ok accepted_5139 (by simp [batch_102_19_values])
  exact h
theorem leaf_5139_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5139.profileLo box_5139.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5139_ok
theorem branch_box_5139_nonnegative : ∀ j, 0 ≤ branch_box_5139.lower j ∧ 0 ≤ branch_box_5139.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5139, Box.profileLo, Box.profileHi, box_5139]
theorem leaf_5139_BranchSafe : CertificateConsequences.BranchSafe branch_box_5139 := by
  left; refine ⟨branch_box_5139_nonnegative, ?_⟩
  intro z hz; exact leaf_5139_sound hz

theorem leaf_5140_ok : checkAt 527 1000 box_5140 cert_5140 = true := by
  have h := List.all_eq_true.mp batch_102_20_ok accepted_5140 (by simp [batch_102_20_values])
  exact h
theorem leaf_5140_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5140.profileLo box_5140.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5140_ok
theorem branch_box_5140_nonnegative : ∀ j, 0 ≤ branch_box_5140.lower j ∧ 0 ≤ branch_box_5140.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5140, Box.profileLo, Box.profileHi, box_5140]
theorem leaf_5140_BranchSafe : CertificateConsequences.BranchSafe branch_box_5140 := by
  left; refine ⟨branch_box_5140_nonnegative, ?_⟩
  intro z hz; exact leaf_5140_sound hz

theorem leaf_5141_ok : checkAt 527 1000 box_5141 cert_5141 = true := by
  have h := List.all_eq_true.mp batch_102_21_ok accepted_5141 (by simp [batch_102_21_values])
  exact h
theorem leaf_5141_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5141.profileLo box_5141.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5141_ok
theorem branch_box_5141_nonnegative : ∀ j, 0 ≤ branch_box_5141.lower j ∧ 0 ≤ branch_box_5141.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5141, Box.profileLo, Box.profileHi, box_5141]
theorem leaf_5141_BranchSafe : CertificateConsequences.BranchSafe branch_box_5141 := by
  left; refine ⟨branch_box_5141_nonnegative, ?_⟩
  intro z hz; exact leaf_5141_sound hz

theorem leaf_5142_ok : checkAt 527 1000 box_5142 cert_5142 = true := by
  have h := List.all_eq_true.mp batch_102_22_ok accepted_5142 (by simp [batch_102_22_values])
  exact h
theorem leaf_5142_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5142.profileLo box_5142.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5142_ok
theorem branch_box_5142_nonnegative : ∀ j, 0 ≤ branch_box_5142.lower j ∧ 0 ≤ branch_box_5142.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5142, Box.profileLo, Box.profileHi, box_5142]
theorem leaf_5142_BranchSafe : CertificateConsequences.BranchSafe branch_box_5142 := by
  left; refine ⟨branch_box_5142_nonnegative, ?_⟩
  intro z hz; exact leaf_5142_sound hz

theorem leaf_5149_ok : checkAt 527 1000 box_5149 cert_5149 = true := by
  have h := List.all_eq_true.mp batch_102_23_ok accepted_5149 (by simp [batch_102_23_values])
  exact h
theorem leaf_5149_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_5149.profileLo box_5149.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_5149_ok
theorem branch_box_5149_nonnegative : ∀ j, 0 ≤ branch_box_5149.lower j ∧ 0 ≤ branch_box_5149.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_5149, Box.profileLo, Box.profileHi, box_5149]
theorem leaf_5149_BranchSafe : CertificateConsequences.BranchSafe branch_box_5149 := by
  left; refine ⟨branch_box_5149_nonnegative, ?_⟩
  intro z hz; exact leaf_5149_sound hz

#print axioms batch_102_00_ok
#print axioms leaf_5107_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
