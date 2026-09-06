import PeaceableQueens.UpperBound.Generated.Even.C527Scaled02Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_02_00_values : List Bool := [accepted_101]
theorem batch_02_00_ok : batch_02_00_values.all id = true := by decide

def batch_02_01_values : List Bool := [accepted_103]
theorem batch_02_01_ok : batch_02_01_values.all id = true := by decide

def batch_02_02_values : List Bool := [accepted_105]
theorem batch_02_02_ok : batch_02_02_values.all id = true := by decide

def batch_02_03_values : List Bool := [accepted_106]
theorem batch_02_03_ok : batch_02_03_values.all id = true := by decide

def batch_02_04_values : List Bool := [accepted_107]
theorem batch_02_04_ok : batch_02_04_values.all id = true := by decide

def batch_02_05_values : List Bool := [accepted_109]
theorem batch_02_05_ok : batch_02_05_values.all id = true := by decide

def batch_02_06_values : List Bool := [accepted_110]
theorem batch_02_06_ok : batch_02_06_values.all id = true := by decide

def batch_02_07_values : List Bool := [accepted_117]
theorem batch_02_07_ok : batch_02_07_values.all id = true := by decide

def batch_02_08_values : List Bool := [accepted_121]
theorem batch_02_08_ok : batch_02_08_values.all id = true := by decide

def batch_02_09_values : List Bool := [accepted_123]
theorem batch_02_09_ok : batch_02_09_values.all id = true := by decide

def batch_02_10_values : List Bool := [accepted_125]
theorem batch_02_10_ok : batch_02_10_values.all id = true := by decide

def batch_02_11_values : List Bool := [accepted_126]
theorem batch_02_11_ok : batch_02_11_values.all id = true := by decide

def batch_02_12_values : List Bool := [accepted_127]
theorem batch_02_12_ok : batch_02_12_values.all id = true := by decide

def batch_02_13_values : List Bool := [accepted_128]
theorem batch_02_13_ok : batch_02_13_values.all id = true := by decide

def batch_02_14_values : List Bool := [accepted_131]
theorem batch_02_14_ok : batch_02_14_values.all id = true := by decide

def batch_02_15_values : List Bool := [accepted_133]
theorem batch_02_15_ok : batch_02_15_values.all id = true := by decide

def batch_02_16_values : List Bool := [accepted_135]
theorem batch_02_16_ok : batch_02_16_values.all id = true := by decide

def batch_02_17_values : List Bool := [accepted_136]
theorem batch_02_17_ok : batch_02_17_values.all id = true := by decide

def batch_02_18_values : List Bool := [accepted_138]
theorem batch_02_18_ok : batch_02_18_values.all id = true := by decide

def batch_02_19_values : List Bool := [accepted_139]
theorem batch_02_19_ok : batch_02_19_values.all id = true := by decide

def batch_02_20_values : List Bool := [accepted_140]
theorem batch_02_20_ok : batch_02_20_values.all id = true := by decide

def batch_02_21_values : List Bool := [accepted_143]
theorem batch_02_21_ok : batch_02_21_values.all id = true := by decide

def batch_02_22_values : List Bool := [accepted_145]
theorem batch_02_22_ok : batch_02_22_values.all id = true := by decide

def batch_02_23_values : List Bool := [accepted_146]
theorem batch_02_23_ok : batch_02_23_values.all id = true := by decide

def batch_02_24_values : List Bool := [accepted_148]
theorem batch_02_24_ok : batch_02_24_values.all id = true := by decide

def batch_02_25_values : List Bool := [accepted_149]
theorem batch_02_25_ok : batch_02_25_values.all id = true := by decide

theorem leaf_101_ok : checkAt 527 1000 box_101 cert_101 = true := by
  have h := List.all_eq_true.mp batch_02_00_ok accepted_101 (by simp [batch_02_00_values])
  exact h
theorem leaf_101_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_101.profileLo box_101.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_101_ok
theorem branch_box_101_nonnegative : ∀ j, 0 ≤ branch_box_101.lower j ∧ 0 ≤ branch_box_101.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_101, Box.profileLo, Box.profileHi, box_101]
theorem leaf_101_BranchSafe : CertificateConsequences.BranchSafe branch_box_101 := by
  left; refine ⟨branch_box_101_nonnegative, ?_⟩
  intro z hz; exact leaf_101_sound hz

theorem leaf_103_ok : checkAt 527 1000 box_103 cert_103 = true := by
  have h := List.all_eq_true.mp batch_02_01_ok accepted_103 (by simp [batch_02_01_values])
  exact h
theorem leaf_103_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_103.profileLo box_103.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_103_ok
theorem branch_box_103_nonnegative : ∀ j, 0 ≤ branch_box_103.lower j ∧ 0 ≤ branch_box_103.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_103, Box.profileLo, Box.profileHi, box_103]
theorem leaf_103_BranchSafe : CertificateConsequences.BranchSafe branch_box_103 := by
  left; refine ⟨branch_box_103_nonnegative, ?_⟩
  intro z hz; exact leaf_103_sound hz

theorem leaf_105_ok : checkAt 527 1000 box_105 cert_105 = true := by
  have h := List.all_eq_true.mp batch_02_02_ok accepted_105 (by simp [batch_02_02_values])
  exact h
theorem leaf_105_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_105.profileLo box_105.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_105_ok
theorem branch_box_105_nonnegative : ∀ j, 0 ≤ branch_box_105.lower j ∧ 0 ≤ branch_box_105.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_105, Box.profileLo, Box.profileHi, box_105]
theorem leaf_105_BranchSafe : CertificateConsequences.BranchSafe branch_box_105 := by
  left; refine ⟨branch_box_105_nonnegative, ?_⟩
  intro z hz; exact leaf_105_sound hz

theorem leaf_106_ok : checkAt 527 1000 box_106 cert_106 = true := by
  have h := List.all_eq_true.mp batch_02_03_ok accepted_106 (by simp [batch_02_03_values])
  exact h
theorem leaf_106_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_106.profileLo box_106.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_106_ok
theorem branch_box_106_nonnegative : ∀ j, 0 ≤ branch_box_106.lower j ∧ 0 ≤ branch_box_106.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_106, Box.profileLo, Box.profileHi, box_106]
theorem leaf_106_BranchSafe : CertificateConsequences.BranchSafe branch_box_106 := by
  left; refine ⟨branch_box_106_nonnegative, ?_⟩
  intro z hz; exact leaf_106_sound hz

theorem leaf_107_ok : checkAt 527 1000 box_107 cert_107 = true := by
  have h := List.all_eq_true.mp batch_02_04_ok accepted_107 (by simp [batch_02_04_values])
  exact h
theorem leaf_107_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_107.profileLo box_107.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_107_ok
theorem branch_box_107_nonnegative : ∀ j, 0 ≤ branch_box_107.lower j ∧ 0 ≤ branch_box_107.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_107, Box.profileLo, Box.profileHi, box_107]
theorem leaf_107_BranchSafe : CertificateConsequences.BranchSafe branch_box_107 := by
  left; refine ⟨branch_box_107_nonnegative, ?_⟩
  intro z hz; exact leaf_107_sound hz

theorem leaf_109_ok : checkAt 527 1000 box_109 cert_109 = true := by
  have h := List.all_eq_true.mp batch_02_05_ok accepted_109 (by simp [batch_02_05_values])
  exact h
theorem leaf_109_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_109.profileLo box_109.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_109_ok
theorem branch_box_109_nonnegative : ∀ j, 0 ≤ branch_box_109.lower j ∧ 0 ≤ branch_box_109.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_109, Box.profileLo, Box.profileHi, box_109]
theorem leaf_109_BranchSafe : CertificateConsequences.BranchSafe branch_box_109 := by
  left; refine ⟨branch_box_109_nonnegative, ?_⟩
  intro z hz; exact leaf_109_sound hz

theorem leaf_110_ok : checkAt 527 1000 box_110 cert_110 = true := by
  have h := List.all_eq_true.mp batch_02_06_ok accepted_110 (by simp [batch_02_06_values])
  exact h
theorem leaf_110_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_110.profileLo box_110.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_110_ok
theorem branch_box_110_nonnegative : ∀ j, 0 ≤ branch_box_110.lower j ∧ 0 ≤ branch_box_110.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_110, Box.profileLo, Box.profileHi, box_110]
theorem leaf_110_BranchSafe : CertificateConsequences.BranchSafe branch_box_110 := by
  left; refine ⟨branch_box_110_nonnegative, ?_⟩
  intro z hz; exact leaf_110_sound hz

theorem leaf_117_ok : checkAt 527 1000 box_117 cert_117 = true := by
  have h := List.all_eq_true.mp batch_02_07_ok accepted_117 (by simp [batch_02_07_values])
  exact h
theorem leaf_117_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_117.profileLo box_117.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_117_ok
theorem branch_box_117_nonnegative : ∀ j, 0 ≤ branch_box_117.lower j ∧ 0 ≤ branch_box_117.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_117, Box.profileLo, Box.profileHi, box_117]
theorem leaf_117_BranchSafe : CertificateConsequences.BranchSafe branch_box_117 := by
  left; refine ⟨branch_box_117_nonnegative, ?_⟩
  intro z hz; exact leaf_117_sound hz

theorem leaf_121_ok : checkAt 527 1000 box_121 cert_121 = true := by
  have h := List.all_eq_true.mp batch_02_08_ok accepted_121 (by simp [batch_02_08_values])
  exact h
theorem leaf_121_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_121.profileLo box_121.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_121_ok
theorem branch_box_121_nonnegative : ∀ j, 0 ≤ branch_box_121.lower j ∧ 0 ≤ branch_box_121.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_121, Box.profileLo, Box.profileHi, box_121]
theorem leaf_121_BranchSafe : CertificateConsequences.BranchSafe branch_box_121 := by
  left; refine ⟨branch_box_121_nonnegative, ?_⟩
  intro z hz; exact leaf_121_sound hz

theorem leaf_123_ok : checkAt 527 1000 box_123 cert_123 = true := by
  have h := List.all_eq_true.mp batch_02_09_ok accepted_123 (by simp [batch_02_09_values])
  exact h
theorem leaf_123_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_123.profileLo box_123.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_123_ok
theorem branch_box_123_nonnegative : ∀ j, 0 ≤ branch_box_123.lower j ∧ 0 ≤ branch_box_123.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_123, Box.profileLo, Box.profileHi, box_123]
theorem leaf_123_BranchSafe : CertificateConsequences.BranchSafe branch_box_123 := by
  left; refine ⟨branch_box_123_nonnegative, ?_⟩
  intro z hz; exact leaf_123_sound hz

theorem leaf_125_ok : checkAt 527 1000 box_125 cert_125 = true := by
  have h := List.all_eq_true.mp batch_02_10_ok accepted_125 (by simp [batch_02_10_values])
  exact h
theorem leaf_125_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_125.profileLo box_125.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_125_ok
theorem branch_box_125_nonnegative : ∀ j, 0 ≤ branch_box_125.lower j ∧ 0 ≤ branch_box_125.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_125, Box.profileLo, Box.profileHi, box_125]
theorem leaf_125_BranchSafe : CertificateConsequences.BranchSafe branch_box_125 := by
  left; refine ⟨branch_box_125_nonnegative, ?_⟩
  intro z hz; exact leaf_125_sound hz

theorem leaf_126_ok : checkAt 527 1000 box_126 cert_126 = true := by
  have h := List.all_eq_true.mp batch_02_11_ok accepted_126 (by simp [batch_02_11_values])
  exact h
theorem leaf_126_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_126.profileLo box_126.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_126_ok
theorem branch_box_126_nonnegative : ∀ j, 0 ≤ branch_box_126.lower j ∧ 0 ≤ branch_box_126.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_126, Box.profileLo, Box.profileHi, box_126]
theorem leaf_126_BranchSafe : CertificateConsequences.BranchSafe branch_box_126 := by
  left; refine ⟨branch_box_126_nonnegative, ?_⟩
  intro z hz; exact leaf_126_sound hz

theorem leaf_127_ok : checkAt 527 1000 box_127 cert_127 = true := by
  have h := List.all_eq_true.mp batch_02_12_ok accepted_127 (by simp [batch_02_12_values])
  exact h
theorem leaf_127_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_127.profileLo box_127.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_127_ok
theorem branch_box_127_nonnegative : ∀ j, 0 ≤ branch_box_127.lower j ∧ 0 ≤ branch_box_127.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_127, Box.profileLo, Box.profileHi, box_127]
theorem leaf_127_BranchSafe : CertificateConsequences.BranchSafe branch_box_127 := by
  left; refine ⟨branch_box_127_nonnegative, ?_⟩
  intro z hz; exact leaf_127_sound hz

theorem leaf_128_ok : checkAt 527 1000 box_128 cert_128 = true := by
  have h := List.all_eq_true.mp batch_02_13_ok accepted_128 (by simp [batch_02_13_values])
  exact h
theorem leaf_128_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_128.profileLo box_128.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_128_ok
theorem branch_box_128_nonnegative : ∀ j, 0 ≤ branch_box_128.lower j ∧ 0 ≤ branch_box_128.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_128, Box.profileLo, Box.profileHi, box_128]
theorem leaf_128_BranchSafe : CertificateConsequences.BranchSafe branch_box_128 := by
  left; refine ⟨branch_box_128_nonnegative, ?_⟩
  intro z hz; exact leaf_128_sound hz

theorem leaf_131_ok : checkAt 527 1000 box_131 cert_131 = true := by
  have h := List.all_eq_true.mp batch_02_14_ok accepted_131 (by simp [batch_02_14_values])
  exact h
theorem leaf_131_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_131.profileLo box_131.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_131_ok
theorem branch_box_131_nonnegative : ∀ j, 0 ≤ branch_box_131.lower j ∧ 0 ≤ branch_box_131.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_131, Box.profileLo, Box.profileHi, box_131]
theorem leaf_131_BranchSafe : CertificateConsequences.BranchSafe branch_box_131 := by
  left; refine ⟨branch_box_131_nonnegative, ?_⟩
  intro z hz; exact leaf_131_sound hz

theorem leaf_133_ok : checkAt 527 1000 box_133 cert_133 = true := by
  have h := List.all_eq_true.mp batch_02_15_ok accepted_133 (by simp [batch_02_15_values])
  exact h
theorem leaf_133_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_133.profileLo box_133.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_133_ok
theorem branch_box_133_nonnegative : ∀ j, 0 ≤ branch_box_133.lower j ∧ 0 ≤ branch_box_133.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_133, Box.profileLo, Box.profileHi, box_133]
theorem leaf_133_BranchSafe : CertificateConsequences.BranchSafe branch_box_133 := by
  left; refine ⟨branch_box_133_nonnegative, ?_⟩
  intro z hz; exact leaf_133_sound hz

theorem leaf_135_ok : checkAt 527 1000 box_135 cert_135 = true := by
  have h := List.all_eq_true.mp batch_02_16_ok accepted_135 (by simp [batch_02_16_values])
  exact h
theorem leaf_135_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_135.profileLo box_135.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_135_ok
theorem branch_box_135_nonnegative : ∀ j, 0 ≤ branch_box_135.lower j ∧ 0 ≤ branch_box_135.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_135, Box.profileLo, Box.profileHi, box_135]
theorem leaf_135_BranchSafe : CertificateConsequences.BranchSafe branch_box_135 := by
  left; refine ⟨branch_box_135_nonnegative, ?_⟩
  intro z hz; exact leaf_135_sound hz

theorem leaf_136_ok : checkAt 527 1000 box_136 cert_136 = true := by
  have h := List.all_eq_true.mp batch_02_17_ok accepted_136 (by simp [batch_02_17_values])
  exact h
theorem leaf_136_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_136.profileLo box_136.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_136_ok
theorem branch_box_136_nonnegative : ∀ j, 0 ≤ branch_box_136.lower j ∧ 0 ≤ branch_box_136.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_136, Box.profileLo, Box.profileHi, box_136]
theorem leaf_136_BranchSafe : CertificateConsequences.BranchSafe branch_box_136 := by
  left; refine ⟨branch_box_136_nonnegative, ?_⟩
  intro z hz; exact leaf_136_sound hz

theorem leaf_138_ok : checkAt 527 1000 box_138 cert_138 = true := by
  have h := List.all_eq_true.mp batch_02_18_ok accepted_138 (by simp [batch_02_18_values])
  exact h
theorem leaf_138_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_138.profileLo box_138.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_138_ok
theorem branch_box_138_nonnegative : ∀ j, 0 ≤ branch_box_138.lower j ∧ 0 ≤ branch_box_138.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_138, Box.profileLo, Box.profileHi, box_138]
theorem leaf_138_BranchSafe : CertificateConsequences.BranchSafe branch_box_138 := by
  left; refine ⟨branch_box_138_nonnegative, ?_⟩
  intro z hz; exact leaf_138_sound hz

theorem leaf_139_ok : checkAt 527 1000 box_139 cert_139 = true := by
  have h := List.all_eq_true.mp batch_02_19_ok accepted_139 (by simp [batch_02_19_values])
  exact h
theorem leaf_139_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_139.profileLo box_139.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_139_ok
theorem branch_box_139_nonnegative : ∀ j, 0 ≤ branch_box_139.lower j ∧ 0 ≤ branch_box_139.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_139, Box.profileLo, Box.profileHi, box_139]
theorem leaf_139_BranchSafe : CertificateConsequences.BranchSafe branch_box_139 := by
  left; refine ⟨branch_box_139_nonnegative, ?_⟩
  intro z hz; exact leaf_139_sound hz

theorem leaf_140_ok : checkAt 527 1000 box_140 cert_140 = true := by
  have h := List.all_eq_true.mp batch_02_20_ok accepted_140 (by simp [batch_02_20_values])
  exact h
theorem leaf_140_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_140.profileLo box_140.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_140_ok
theorem branch_box_140_nonnegative : ∀ j, 0 ≤ branch_box_140.lower j ∧ 0 ≤ branch_box_140.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_140, Box.profileLo, Box.profileHi, box_140]
theorem leaf_140_BranchSafe : CertificateConsequences.BranchSafe branch_box_140 := by
  left; refine ⟨branch_box_140_nonnegative, ?_⟩
  intro z hz; exact leaf_140_sound hz

theorem leaf_143_ok : checkAt 527 1000 box_143 cert_143 = true := by
  have h := List.all_eq_true.mp batch_02_21_ok accepted_143 (by simp [batch_02_21_values])
  exact h
theorem leaf_143_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_143.profileLo box_143.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_143_ok
theorem branch_box_143_nonnegative : ∀ j, 0 ≤ branch_box_143.lower j ∧ 0 ≤ branch_box_143.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_143, Box.profileLo, Box.profileHi, box_143]
theorem leaf_143_BranchSafe : CertificateConsequences.BranchSafe branch_box_143 := by
  left; refine ⟨branch_box_143_nonnegative, ?_⟩
  intro z hz; exact leaf_143_sound hz

theorem leaf_145_ok : checkAt 527 1000 box_145 cert_145 = true := by
  have h := List.all_eq_true.mp batch_02_22_ok accepted_145 (by simp [batch_02_22_values])
  exact h
theorem leaf_145_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_145.profileLo box_145.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_145_ok
theorem branch_box_145_nonnegative : ∀ j, 0 ≤ branch_box_145.lower j ∧ 0 ≤ branch_box_145.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_145, Box.profileLo, Box.profileHi, box_145]
theorem leaf_145_BranchSafe : CertificateConsequences.BranchSafe branch_box_145 := by
  left; refine ⟨branch_box_145_nonnegative, ?_⟩
  intro z hz; exact leaf_145_sound hz

theorem leaf_146_ok : checkAt 527 1000 box_146 cert_146 = true := by
  have h := List.all_eq_true.mp batch_02_23_ok accepted_146 (by simp [batch_02_23_values])
  exact h
theorem leaf_146_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_146.profileLo box_146.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_146_ok
theorem branch_box_146_nonnegative : ∀ j, 0 ≤ branch_box_146.lower j ∧ 0 ≤ branch_box_146.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_146, Box.profileLo, Box.profileHi, box_146]
theorem leaf_146_BranchSafe : CertificateConsequences.BranchSafe branch_box_146 := by
  left; refine ⟨branch_box_146_nonnegative, ?_⟩
  intro z hz; exact leaf_146_sound hz

theorem leaf_148_ok : checkAt 527 1000 box_148 cert_148 = true := by
  have h := List.all_eq_true.mp batch_02_24_ok accepted_148 (by simp [batch_02_24_values])
  exact h
theorem leaf_148_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_148.profileLo box_148.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_148_ok
theorem branch_box_148_nonnegative : ∀ j, 0 ≤ branch_box_148.lower j ∧ 0 ≤ branch_box_148.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_148, Box.profileLo, Box.profileHi, box_148]
theorem leaf_148_BranchSafe : CertificateConsequences.BranchSafe branch_box_148 := by
  left; refine ⟨branch_box_148_nonnegative, ?_⟩
  intro z hz; exact leaf_148_sound hz

theorem leaf_149_ok : checkAt 527 1000 box_149 cert_149 = true := by
  have h := List.all_eq_true.mp batch_02_25_ok accepted_149 (by simp [batch_02_25_values])
  exact h
theorem leaf_149_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_149.profileLo box_149.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_149_ok
theorem branch_box_149_nonnegative : ∀ j, 0 ≤ branch_box_149.lower j ∧ 0 ≤ branch_box_149.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_149, Box.profileLo, Box.profileHi, box_149]
theorem leaf_149_BranchSafe : CertificateConsequences.BranchSafe branch_box_149 := by
  left; refine ⟨branch_box_149_nonnegative, ?_⟩
  intro z hz; exact leaf_149_sound hz

#print axioms batch_02_00_ok
#print axioms leaf_101_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
