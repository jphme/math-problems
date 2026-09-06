import PeaceableQueens.UpperBound.Generated.Even.C527Scaled123Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_123_00_values : List Bool := [accepted_6151]
theorem batch_123_00_ok : batch_123_00_values.all id = true := by decide

def batch_123_01_values : List Bool := [accepted_6152]
theorem batch_123_01_ok : batch_123_01_values.all id = true := by decide

def batch_123_02_values : List Bool := [accepted_6153]
theorem batch_123_02_ok : batch_123_02_values.all id = true := by decide

def batch_123_03_values : List Bool := [accepted_6154]
theorem batch_123_03_ok : batch_123_03_values.all id = true := by decide

def batch_123_04_values : List Bool := [accepted_6159]
theorem batch_123_04_ok : batch_123_04_values.all id = true := by decide

def batch_123_05_values : List Bool := [accepted_6161]
theorem batch_123_05_ok : batch_123_05_values.all id = true := by decide

def batch_123_06_values : List Bool := [accepted_6162]
theorem batch_123_06_ok : batch_123_06_values.all id = true := by decide

def batch_123_07_values : List Bool := [accepted_6165]
theorem batch_123_07_ok : batch_123_07_values.all id = true := by decide

def batch_123_08_values : List Bool := [accepted_6166]
theorem batch_123_08_ok : batch_123_08_values.all id = true := by decide

def batch_123_09_values : List Bool := [accepted_6167]
theorem batch_123_09_ok : batch_123_09_values.all id = true := by decide

def batch_123_10_values : List Bool := [accepted_6168]
theorem batch_123_10_ok : batch_123_10_values.all id = true := by decide

def batch_123_11_values : List Bool := [accepted_6174]
theorem batch_123_11_ok : batch_123_11_values.all id = true := by decide

def batch_123_12_values : List Bool := [accepted_6175]
theorem batch_123_12_ok : batch_123_12_values.all id = true := by decide

def batch_123_13_values : List Bool := [accepted_6176]
theorem batch_123_13_ok : batch_123_13_values.all id = true := by decide

def batch_123_14_values : List Bool := [accepted_6177]
theorem batch_123_14_ok : batch_123_14_values.all id = true := by decide

def batch_123_15_values : List Bool := [accepted_6178]
theorem batch_123_15_ok : batch_123_15_values.all id = true := by decide

def batch_123_16_values : List Bool := [accepted_6181]
theorem batch_123_16_ok : batch_123_16_values.all id = true := by decide

def batch_123_17_values : List Bool := [accepted_6183]
theorem batch_123_17_ok : batch_123_17_values.all id = true := by decide

def batch_123_18_values : List Bool := [accepted_6184]
theorem batch_123_18_ok : batch_123_18_values.all id = true := by decide

def batch_123_19_values : List Bool := [accepted_6187]
theorem batch_123_19_ok : batch_123_19_values.all id = true := by decide

def batch_123_20_values : List Bool := [accepted_6189]
theorem batch_123_20_ok : batch_123_20_values.all id = true := by decide

def batch_123_21_values : List Bool := [accepted_6191]
theorem batch_123_21_ok : batch_123_21_values.all id = true := by decide

def batch_123_22_values : List Bool := [accepted_6192]
theorem batch_123_22_ok : batch_123_22_values.all id = true := by decide

def batch_123_23_values : List Bool := [accepted_6195]
theorem batch_123_23_ok : batch_123_23_values.all id = true := by decide

def batch_123_24_values : List Bool := [accepted_6197]
theorem batch_123_24_ok : batch_123_24_values.all id = true := by decide

def batch_123_25_values : List Bool := [accepted_6198]
theorem batch_123_25_ok : batch_123_25_values.all id = true := by decide

def batch_123_26_values : List Bool := [accepted_6199]
theorem batch_123_26_ok : batch_123_26_values.all id = true := by decide

theorem leaf_6151_ok : checkAt 527 1000 box_6151 cert_6151 = true := by
  have h := List.all_eq_true.mp batch_123_00_ok accepted_6151 (by simp [batch_123_00_values])
  exact h
theorem leaf_6151_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6151.profileLo box_6151.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6151_ok
theorem branch_box_6151_nonnegative : ∀ j, 0 ≤ branch_box_6151.lower j ∧ 0 ≤ branch_box_6151.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6151, Box.profileLo, Box.profileHi, box_6151]
theorem leaf_6151_BranchSafe : CertificateConsequences.BranchSafe branch_box_6151 := by
  left; refine ⟨branch_box_6151_nonnegative, ?_⟩
  intro z hz; exact leaf_6151_sound hz

theorem leaf_6152_ok : checkAt 527 1000 box_6152 cert_6152 = true := by
  have h := List.all_eq_true.mp batch_123_01_ok accepted_6152 (by simp [batch_123_01_values])
  exact h
theorem leaf_6152_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6152.profileLo box_6152.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6152_ok
theorem branch_box_6152_nonnegative : ∀ j, 0 ≤ branch_box_6152.lower j ∧ 0 ≤ branch_box_6152.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6152, Box.profileLo, Box.profileHi, box_6152]
theorem leaf_6152_BranchSafe : CertificateConsequences.BranchSafe branch_box_6152 := by
  left; refine ⟨branch_box_6152_nonnegative, ?_⟩
  intro z hz; exact leaf_6152_sound hz

theorem leaf_6153_ok : checkAt 527 1000 box_6153 cert_6153 = true := by
  have h := List.all_eq_true.mp batch_123_02_ok accepted_6153 (by simp [batch_123_02_values])
  exact h
theorem leaf_6153_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6153.profileLo box_6153.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6153_ok
theorem branch_box_6153_nonnegative : ∀ j, 0 ≤ branch_box_6153.lower j ∧ 0 ≤ branch_box_6153.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6153, Box.profileLo, Box.profileHi, box_6153]
theorem leaf_6153_BranchSafe : CertificateConsequences.BranchSafe branch_box_6153 := by
  left; refine ⟨branch_box_6153_nonnegative, ?_⟩
  intro z hz; exact leaf_6153_sound hz

theorem leaf_6154_ok : checkAt 527 1000 box_6154 cert_6154 = true := by
  have h := List.all_eq_true.mp batch_123_03_ok accepted_6154 (by simp [batch_123_03_values])
  exact h
theorem leaf_6154_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6154.profileLo box_6154.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6154_ok
theorem branch_box_6154_nonnegative : ∀ j, 0 ≤ branch_box_6154.lower j ∧ 0 ≤ branch_box_6154.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6154, Box.profileLo, Box.profileHi, box_6154]
theorem leaf_6154_BranchSafe : CertificateConsequences.BranchSafe branch_box_6154 := by
  left; refine ⟨branch_box_6154_nonnegative, ?_⟩
  intro z hz; exact leaf_6154_sound hz

theorem leaf_6159_ok : checkAt 527 1000 box_6159 cert_6159 = true := by
  have h := List.all_eq_true.mp batch_123_04_ok accepted_6159 (by simp [batch_123_04_values])
  exact h
theorem leaf_6159_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6159.profileLo box_6159.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6159_ok
theorem branch_box_6159_nonnegative : ∀ j, 0 ≤ branch_box_6159.lower j ∧ 0 ≤ branch_box_6159.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6159, Box.profileLo, Box.profileHi, box_6159]
theorem leaf_6159_BranchSafe : CertificateConsequences.BranchSafe branch_box_6159 := by
  left; refine ⟨branch_box_6159_nonnegative, ?_⟩
  intro z hz; exact leaf_6159_sound hz

theorem leaf_6161_ok : checkAt 527 1000 box_6161 cert_6161 = true := by
  have h := List.all_eq_true.mp batch_123_05_ok accepted_6161 (by simp [batch_123_05_values])
  exact h
theorem leaf_6161_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6161.profileLo box_6161.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6161_ok
theorem branch_box_6161_nonnegative : ∀ j, 0 ≤ branch_box_6161.lower j ∧ 0 ≤ branch_box_6161.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6161, Box.profileLo, Box.profileHi, box_6161]
theorem leaf_6161_BranchSafe : CertificateConsequences.BranchSafe branch_box_6161 := by
  left; refine ⟨branch_box_6161_nonnegative, ?_⟩
  intro z hz; exact leaf_6161_sound hz

theorem leaf_6162_ok : checkAt 527 1000 box_6162 cert_6162 = true := by
  have h := List.all_eq_true.mp batch_123_06_ok accepted_6162 (by simp [batch_123_06_values])
  exact h
theorem leaf_6162_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6162.profileLo box_6162.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6162_ok
theorem branch_box_6162_nonnegative : ∀ j, 0 ≤ branch_box_6162.lower j ∧ 0 ≤ branch_box_6162.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6162, Box.profileLo, Box.profileHi, box_6162]
theorem leaf_6162_BranchSafe : CertificateConsequences.BranchSafe branch_box_6162 := by
  left; refine ⟨branch_box_6162_nonnegative, ?_⟩
  intro z hz; exact leaf_6162_sound hz

theorem leaf_6165_ok : checkAt 527 1000 box_6165 cert_6165 = true := by
  have h := List.all_eq_true.mp batch_123_07_ok accepted_6165 (by simp [batch_123_07_values])
  exact h
theorem leaf_6165_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6165.profileLo box_6165.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6165_ok
theorem branch_box_6165_nonnegative : ∀ j, 0 ≤ branch_box_6165.lower j ∧ 0 ≤ branch_box_6165.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6165, Box.profileLo, Box.profileHi, box_6165]
theorem leaf_6165_BranchSafe : CertificateConsequences.BranchSafe branch_box_6165 := by
  left; refine ⟨branch_box_6165_nonnegative, ?_⟩
  intro z hz; exact leaf_6165_sound hz

theorem leaf_6166_ok : checkAt 527 1000 box_6166 cert_6166 = true := by
  have h := List.all_eq_true.mp batch_123_08_ok accepted_6166 (by simp [batch_123_08_values])
  exact h
theorem leaf_6166_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6166.profileLo box_6166.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6166_ok
theorem branch_box_6166_nonnegative : ∀ j, 0 ≤ branch_box_6166.lower j ∧ 0 ≤ branch_box_6166.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6166, Box.profileLo, Box.profileHi, box_6166]
theorem leaf_6166_BranchSafe : CertificateConsequences.BranchSafe branch_box_6166 := by
  left; refine ⟨branch_box_6166_nonnegative, ?_⟩
  intro z hz; exact leaf_6166_sound hz

theorem leaf_6167_ok : checkAt 527 1000 box_6167 cert_6167 = true := by
  have h := List.all_eq_true.mp batch_123_09_ok accepted_6167 (by simp [batch_123_09_values])
  exact h
theorem leaf_6167_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6167.profileLo box_6167.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6167_ok
theorem branch_box_6167_nonnegative : ∀ j, 0 ≤ branch_box_6167.lower j ∧ 0 ≤ branch_box_6167.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6167, Box.profileLo, Box.profileHi, box_6167]
theorem leaf_6167_BranchSafe : CertificateConsequences.BranchSafe branch_box_6167 := by
  left; refine ⟨branch_box_6167_nonnegative, ?_⟩
  intro z hz; exact leaf_6167_sound hz

theorem leaf_6168_ok : checkAt 527 1000 box_6168 cert_6168 = true := by
  have h := List.all_eq_true.mp batch_123_10_ok accepted_6168 (by simp [batch_123_10_values])
  exact h
theorem leaf_6168_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6168.profileLo box_6168.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6168_ok
theorem branch_box_6168_nonnegative : ∀ j, 0 ≤ branch_box_6168.lower j ∧ 0 ≤ branch_box_6168.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6168, Box.profileLo, Box.profileHi, box_6168]
theorem leaf_6168_BranchSafe : CertificateConsequences.BranchSafe branch_box_6168 := by
  left; refine ⟨branch_box_6168_nonnegative, ?_⟩
  intro z hz; exact leaf_6168_sound hz

theorem leaf_6174_ok : checkAt 527 1000 box_6174 cert_6174 = true := by
  have h := List.all_eq_true.mp batch_123_11_ok accepted_6174 (by simp [batch_123_11_values])
  exact h
theorem leaf_6174_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6174.profileLo box_6174.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6174_ok
theorem branch_box_6174_nonnegative : ∀ j, 0 ≤ branch_box_6174.lower j ∧ 0 ≤ branch_box_6174.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6174, Box.profileLo, Box.profileHi, box_6174]
theorem leaf_6174_BranchSafe : CertificateConsequences.BranchSafe branch_box_6174 := by
  left; refine ⟨branch_box_6174_nonnegative, ?_⟩
  intro z hz; exact leaf_6174_sound hz

theorem leaf_6175_ok : checkAt 527 1000 box_6175 cert_6175 = true := by
  have h := List.all_eq_true.mp batch_123_12_ok accepted_6175 (by simp [batch_123_12_values])
  exact h
theorem leaf_6175_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6175.profileLo box_6175.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6175_ok
theorem branch_box_6175_nonnegative : ∀ j, 0 ≤ branch_box_6175.lower j ∧ 0 ≤ branch_box_6175.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6175, Box.profileLo, Box.profileHi, box_6175]
theorem leaf_6175_BranchSafe : CertificateConsequences.BranchSafe branch_box_6175 := by
  left; refine ⟨branch_box_6175_nonnegative, ?_⟩
  intro z hz; exact leaf_6175_sound hz

theorem leaf_6176_ok : checkAt 527 1000 box_6176 cert_6176 = true := by
  have h := List.all_eq_true.mp batch_123_13_ok accepted_6176 (by simp [batch_123_13_values])
  exact h
theorem leaf_6176_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6176.profileLo box_6176.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6176_ok
theorem branch_box_6176_nonnegative : ∀ j, 0 ≤ branch_box_6176.lower j ∧ 0 ≤ branch_box_6176.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6176, Box.profileLo, Box.profileHi, box_6176]
theorem leaf_6176_BranchSafe : CertificateConsequences.BranchSafe branch_box_6176 := by
  left; refine ⟨branch_box_6176_nonnegative, ?_⟩
  intro z hz; exact leaf_6176_sound hz

theorem leaf_6177_ok : checkAt 527 1000 box_6177 cert_6177 = true := by
  have h := List.all_eq_true.mp batch_123_14_ok accepted_6177 (by simp [batch_123_14_values])
  exact h
theorem leaf_6177_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6177.profileLo box_6177.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6177_ok
theorem branch_box_6177_nonnegative : ∀ j, 0 ≤ branch_box_6177.lower j ∧ 0 ≤ branch_box_6177.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6177, Box.profileLo, Box.profileHi, box_6177]
theorem leaf_6177_BranchSafe : CertificateConsequences.BranchSafe branch_box_6177 := by
  left; refine ⟨branch_box_6177_nonnegative, ?_⟩
  intro z hz; exact leaf_6177_sound hz

theorem leaf_6178_ok : checkAt 527 1000 box_6178 cert_6178 = true := by
  have h := List.all_eq_true.mp batch_123_15_ok accepted_6178 (by simp [batch_123_15_values])
  exact h
theorem leaf_6178_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6178.profileLo box_6178.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6178_ok
theorem branch_box_6178_nonnegative : ∀ j, 0 ≤ branch_box_6178.lower j ∧ 0 ≤ branch_box_6178.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6178, Box.profileLo, Box.profileHi, box_6178]
theorem leaf_6178_BranchSafe : CertificateConsequences.BranchSafe branch_box_6178 := by
  left; refine ⟨branch_box_6178_nonnegative, ?_⟩
  intro z hz; exact leaf_6178_sound hz

theorem leaf_6181_ok : checkAt 527 1000 box_6181 cert_6181 = true := by
  have h := List.all_eq_true.mp batch_123_16_ok accepted_6181 (by simp [batch_123_16_values])
  exact h
theorem leaf_6181_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6181.profileLo box_6181.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6181_ok
theorem branch_box_6181_nonnegative : ∀ j, 0 ≤ branch_box_6181.lower j ∧ 0 ≤ branch_box_6181.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6181, Box.profileLo, Box.profileHi, box_6181]
theorem leaf_6181_BranchSafe : CertificateConsequences.BranchSafe branch_box_6181 := by
  left; refine ⟨branch_box_6181_nonnegative, ?_⟩
  intro z hz; exact leaf_6181_sound hz

theorem leaf_6183_ok : checkAt 527 1000 box_6183 cert_6183 = true := by
  have h := List.all_eq_true.mp batch_123_17_ok accepted_6183 (by simp [batch_123_17_values])
  exact h
theorem leaf_6183_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6183.profileLo box_6183.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6183_ok
theorem branch_box_6183_nonnegative : ∀ j, 0 ≤ branch_box_6183.lower j ∧ 0 ≤ branch_box_6183.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6183, Box.profileLo, Box.profileHi, box_6183]
theorem leaf_6183_BranchSafe : CertificateConsequences.BranchSafe branch_box_6183 := by
  left; refine ⟨branch_box_6183_nonnegative, ?_⟩
  intro z hz; exact leaf_6183_sound hz

theorem leaf_6184_ok : checkAt 527 1000 box_6184 cert_6184 = true := by
  have h := List.all_eq_true.mp batch_123_18_ok accepted_6184 (by simp [batch_123_18_values])
  exact h
theorem leaf_6184_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6184.profileLo box_6184.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6184_ok
theorem branch_box_6184_nonnegative : ∀ j, 0 ≤ branch_box_6184.lower j ∧ 0 ≤ branch_box_6184.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6184, Box.profileLo, Box.profileHi, box_6184]
theorem leaf_6184_BranchSafe : CertificateConsequences.BranchSafe branch_box_6184 := by
  left; refine ⟨branch_box_6184_nonnegative, ?_⟩
  intro z hz; exact leaf_6184_sound hz

theorem leaf_6187_ok : checkAt 527 1000 box_6187 cert_6187 = true := by
  have h := List.all_eq_true.mp batch_123_19_ok accepted_6187 (by simp [batch_123_19_values])
  exact h
theorem leaf_6187_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6187.profileLo box_6187.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6187_ok
theorem branch_box_6187_nonnegative : ∀ j, 0 ≤ branch_box_6187.lower j ∧ 0 ≤ branch_box_6187.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6187, Box.profileLo, Box.profileHi, box_6187]
theorem leaf_6187_BranchSafe : CertificateConsequences.BranchSafe branch_box_6187 := by
  left; refine ⟨branch_box_6187_nonnegative, ?_⟩
  intro z hz; exact leaf_6187_sound hz

theorem leaf_6189_ok : checkAt 527 1000 box_6189 cert_6189 = true := by
  have h := List.all_eq_true.mp batch_123_20_ok accepted_6189 (by simp [batch_123_20_values])
  exact h
theorem leaf_6189_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6189.profileLo box_6189.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6189_ok
theorem branch_box_6189_nonnegative : ∀ j, 0 ≤ branch_box_6189.lower j ∧ 0 ≤ branch_box_6189.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6189, Box.profileLo, Box.profileHi, box_6189]
theorem leaf_6189_BranchSafe : CertificateConsequences.BranchSafe branch_box_6189 := by
  left; refine ⟨branch_box_6189_nonnegative, ?_⟩
  intro z hz; exact leaf_6189_sound hz

theorem leaf_6191_ok : checkAt 527 1000 box_6191 cert_6191 = true := by
  have h := List.all_eq_true.mp batch_123_21_ok accepted_6191 (by simp [batch_123_21_values])
  exact h
theorem leaf_6191_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6191.profileLo box_6191.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6191_ok
theorem branch_box_6191_nonnegative : ∀ j, 0 ≤ branch_box_6191.lower j ∧ 0 ≤ branch_box_6191.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6191, Box.profileLo, Box.profileHi, box_6191]
theorem leaf_6191_BranchSafe : CertificateConsequences.BranchSafe branch_box_6191 := by
  left; refine ⟨branch_box_6191_nonnegative, ?_⟩
  intro z hz; exact leaf_6191_sound hz

theorem leaf_6192_ok : checkAt 527 1000 box_6192 cert_6192 = true := by
  have h := List.all_eq_true.mp batch_123_22_ok accepted_6192 (by simp [batch_123_22_values])
  exact h
theorem leaf_6192_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6192.profileLo box_6192.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6192_ok
theorem branch_box_6192_nonnegative : ∀ j, 0 ≤ branch_box_6192.lower j ∧ 0 ≤ branch_box_6192.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6192, Box.profileLo, Box.profileHi, box_6192]
theorem leaf_6192_BranchSafe : CertificateConsequences.BranchSafe branch_box_6192 := by
  left; refine ⟨branch_box_6192_nonnegative, ?_⟩
  intro z hz; exact leaf_6192_sound hz

theorem leaf_6195_ok : checkAt 527 1000 box_6195 cert_6195 = true := by
  have h := List.all_eq_true.mp batch_123_23_ok accepted_6195 (by simp [batch_123_23_values])
  exact h
theorem leaf_6195_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6195.profileLo box_6195.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6195_ok
theorem branch_box_6195_nonnegative : ∀ j, 0 ≤ branch_box_6195.lower j ∧ 0 ≤ branch_box_6195.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6195, Box.profileLo, Box.profileHi, box_6195]
theorem leaf_6195_BranchSafe : CertificateConsequences.BranchSafe branch_box_6195 := by
  left; refine ⟨branch_box_6195_nonnegative, ?_⟩
  intro z hz; exact leaf_6195_sound hz

theorem leaf_6197_ok : checkAt 527 1000 box_6197 cert_6197 = true := by
  have h := List.all_eq_true.mp batch_123_24_ok accepted_6197 (by simp [batch_123_24_values])
  exact h
theorem leaf_6197_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6197.profileLo box_6197.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6197_ok
theorem branch_box_6197_nonnegative : ∀ j, 0 ≤ branch_box_6197.lower j ∧ 0 ≤ branch_box_6197.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6197, Box.profileLo, Box.profileHi, box_6197]
theorem leaf_6197_BranchSafe : CertificateConsequences.BranchSafe branch_box_6197 := by
  left; refine ⟨branch_box_6197_nonnegative, ?_⟩
  intro z hz; exact leaf_6197_sound hz

theorem leaf_6198_ok : checkAt 527 1000 box_6198 cert_6198 = true := by
  have h := List.all_eq_true.mp batch_123_25_ok accepted_6198 (by simp [batch_123_25_values])
  exact h
theorem leaf_6198_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6198.profileLo box_6198.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6198_ok
theorem branch_box_6198_nonnegative : ∀ j, 0 ≤ branch_box_6198.lower j ∧ 0 ≤ branch_box_6198.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6198, Box.profileLo, Box.profileHi, box_6198]
theorem leaf_6198_BranchSafe : CertificateConsequences.BranchSafe branch_box_6198 := by
  left; refine ⟨branch_box_6198_nonnegative, ?_⟩
  intro z hz; exact leaf_6198_sound hz

theorem leaf_6199_ok : checkAt 527 1000 box_6199 cert_6199 = true := by
  have h := List.all_eq_true.mp batch_123_26_ok accepted_6199 (by simp [batch_123_26_values])
  exact h
theorem leaf_6199_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_6199.profileLo box_6199.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_6199_ok
theorem branch_box_6199_nonnegative : ∀ j, 0 ≤ branch_box_6199.lower j ∧ 0 ≤ branch_box_6199.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_6199, Box.profileLo, Box.profileHi, box_6199]
theorem leaf_6199_BranchSafe : CertificateConsequences.BranchSafe branch_box_6199 := by
  left; refine ⟨branch_box_6199_nonnegative, ?_⟩
  intro z hz; exact leaf_6199_sound hz

#print axioms batch_123_00_ok
#print axioms leaf_6151_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
