import PeaceableQueens.UpperBound.Generated.Even.C527Scaled24Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_24_00_values : List Bool := [accepted_1200]
theorem batch_24_00_ok : batch_24_00_values.all id = true := by decide

def batch_24_01_values : List Bool := [accepted_1201]
theorem batch_24_01_ok : batch_24_01_values.all id = true := by decide

def batch_24_02_values : List Bool := [accepted_1202]
theorem batch_24_02_ok : batch_24_02_values.all id = true := by decide

def batch_24_03_values : List Bool := [accepted_1208]
theorem batch_24_03_ok : batch_24_03_values.all id = true := by decide

def batch_24_04_values : List Bool := [accepted_1210]
theorem batch_24_04_ok : batch_24_04_values.all id = true := by decide

def batch_24_05_values : List Bool := [accepted_1212]
theorem batch_24_05_ok : batch_24_05_values.all id = true := by decide

def batch_24_06_values : List Bool := [accepted_1213]
theorem batch_24_06_ok : batch_24_06_values.all id = true := by decide

def batch_24_07_values : List Bool := [accepted_1214]
theorem batch_24_07_ok : batch_24_07_values.all id = true := by decide

def batch_24_08_values : List Bool := [accepted_1215]
theorem batch_24_08_ok : batch_24_08_values.all id = true := by decide

def batch_24_09_values : List Bool := [accepted_1219]
theorem batch_24_09_ok : batch_24_09_values.all id = true := by decide

def batch_24_10_values : List Bool := [accepted_1220]
theorem batch_24_10_ok : batch_24_10_values.all id = true := by decide

def batch_24_11_values : List Bool := [accepted_1221]
theorem batch_24_11_ok : batch_24_11_values.all id = true := by decide

def batch_24_12_values : List Bool := [accepted_1222]
theorem batch_24_12_ok : batch_24_12_values.all id = true := by decide

def batch_24_13_values : List Bool := [accepted_1225]
theorem batch_24_13_ok : batch_24_13_values.all id = true := by decide

def batch_24_14_values : List Bool := [accepted_1226]
theorem batch_24_14_ok : batch_24_14_values.all id = true := by decide

def batch_24_15_values : List Bool := [accepted_1227]
theorem batch_24_15_ok : batch_24_15_values.all id = true := by decide

def batch_24_16_values : List Bool := [accepted_1229]
theorem batch_24_16_ok : batch_24_16_values.all id = true := by decide

def batch_24_17_values : List Bool := [accepted_1230]
theorem batch_24_17_ok : batch_24_17_values.all id = true := by decide

def batch_24_18_values : List Bool := [accepted_1241]
theorem batch_24_18_ok : batch_24_18_values.all id = true := by decide

def batch_24_19_values : List Bool := [accepted_1242]
theorem batch_24_19_ok : batch_24_19_values.all id = true := by decide

def batch_24_20_values : List Bool := [accepted_1243]
theorem batch_24_20_ok : batch_24_20_values.all id = true := by decide

def batch_24_21_values : List Bool := [accepted_1244]
theorem batch_24_21_ok : batch_24_21_values.all id = true := by decide

def batch_24_22_values : List Bool := [accepted_1246]
theorem batch_24_22_ok : batch_24_22_values.all id = true := by decide

def batch_24_23_values : List Bool := [accepted_1247]
theorem batch_24_23_ok : batch_24_23_values.all id = true := by decide

def batch_24_24_values : List Bool := [accepted_1248]
theorem batch_24_24_ok : batch_24_24_values.all id = true := by decide

theorem leaf_1200_ok : checkAt 527 1000 box_1200 cert_1200 = true := by
  have h := List.all_eq_true.mp batch_24_00_ok accepted_1200 (by simp [batch_24_00_values])
  exact h
theorem leaf_1200_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1200.profileLo box_1200.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1200_ok
theorem branch_box_1200_nonnegative : ∀ j, 0 ≤ branch_box_1200.lower j ∧ 0 ≤ branch_box_1200.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1200, Box.profileLo, Box.profileHi, box_1200]
theorem leaf_1200_BranchSafe : CertificateConsequences.BranchSafe branch_box_1200 := by
  left; refine ⟨branch_box_1200_nonnegative, ?_⟩
  intro z hz; exact leaf_1200_sound hz

theorem leaf_1201_ok : checkAt 527 1000 box_1201 cert_1201 = true := by
  have h := List.all_eq_true.mp batch_24_01_ok accepted_1201 (by simp [batch_24_01_values])
  exact h
theorem leaf_1201_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1201.profileLo box_1201.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1201_ok
theorem branch_box_1201_nonnegative : ∀ j, 0 ≤ branch_box_1201.lower j ∧ 0 ≤ branch_box_1201.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1201, Box.profileLo, Box.profileHi, box_1201]
theorem leaf_1201_BranchSafe : CertificateConsequences.BranchSafe branch_box_1201 := by
  left; refine ⟨branch_box_1201_nonnegative, ?_⟩
  intro z hz; exact leaf_1201_sound hz

theorem leaf_1202_ok : checkAt 527 1000 box_1202 cert_1202 = true := by
  have h := List.all_eq_true.mp batch_24_02_ok accepted_1202 (by simp [batch_24_02_values])
  exact h
theorem leaf_1202_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1202.profileLo box_1202.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1202_ok
theorem branch_box_1202_nonnegative : ∀ j, 0 ≤ branch_box_1202.lower j ∧ 0 ≤ branch_box_1202.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1202, Box.profileLo, Box.profileHi, box_1202]
theorem leaf_1202_BranchSafe : CertificateConsequences.BranchSafe branch_box_1202 := by
  left; refine ⟨branch_box_1202_nonnegative, ?_⟩
  intro z hz; exact leaf_1202_sound hz

theorem leaf_1208_ok : checkAt 527 1000 box_1208 cert_1208 = true := by
  have h := List.all_eq_true.mp batch_24_03_ok accepted_1208 (by simp [batch_24_03_values])
  exact h
theorem leaf_1208_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1208.profileLo box_1208.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1208_ok
theorem branch_box_1208_nonnegative : ∀ j, 0 ≤ branch_box_1208.lower j ∧ 0 ≤ branch_box_1208.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1208, Box.profileLo, Box.profileHi, box_1208]
theorem leaf_1208_BranchSafe : CertificateConsequences.BranchSafe branch_box_1208 := by
  left; refine ⟨branch_box_1208_nonnegative, ?_⟩
  intro z hz; exact leaf_1208_sound hz

theorem leaf_1210_ok : checkAt 527 1000 box_1210 cert_1210 = true := by
  have h := List.all_eq_true.mp batch_24_04_ok accepted_1210 (by simp [batch_24_04_values])
  exact h
theorem leaf_1210_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1210.profileLo box_1210.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1210_ok
theorem branch_box_1210_nonnegative : ∀ j, 0 ≤ branch_box_1210.lower j ∧ 0 ≤ branch_box_1210.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1210, Box.profileLo, Box.profileHi, box_1210]
theorem leaf_1210_BranchSafe : CertificateConsequences.BranchSafe branch_box_1210 := by
  left; refine ⟨branch_box_1210_nonnegative, ?_⟩
  intro z hz; exact leaf_1210_sound hz

theorem leaf_1212_ok : checkAt 527 1000 box_1212 cert_1212 = true := by
  have h := List.all_eq_true.mp batch_24_05_ok accepted_1212 (by simp [batch_24_05_values])
  exact h
theorem leaf_1212_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1212.profileLo box_1212.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1212_ok
theorem branch_box_1212_nonnegative : ∀ j, 0 ≤ branch_box_1212.lower j ∧ 0 ≤ branch_box_1212.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1212, Box.profileLo, Box.profileHi, box_1212]
theorem leaf_1212_BranchSafe : CertificateConsequences.BranchSafe branch_box_1212 := by
  left; refine ⟨branch_box_1212_nonnegative, ?_⟩
  intro z hz; exact leaf_1212_sound hz

theorem leaf_1213_ok : checkAt 527 1000 box_1213 cert_1213 = true := by
  have h := List.all_eq_true.mp batch_24_06_ok accepted_1213 (by simp [batch_24_06_values])
  exact h
theorem leaf_1213_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1213.profileLo box_1213.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1213_ok
theorem branch_box_1213_nonnegative : ∀ j, 0 ≤ branch_box_1213.lower j ∧ 0 ≤ branch_box_1213.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1213, Box.profileLo, Box.profileHi, box_1213]
theorem leaf_1213_BranchSafe : CertificateConsequences.BranchSafe branch_box_1213 := by
  left; refine ⟨branch_box_1213_nonnegative, ?_⟩
  intro z hz; exact leaf_1213_sound hz

theorem leaf_1214_ok : checkAt 527 1000 box_1214 cert_1214 = true := by
  have h := List.all_eq_true.mp batch_24_07_ok accepted_1214 (by simp [batch_24_07_values])
  exact h
theorem leaf_1214_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1214.profileLo box_1214.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1214_ok
theorem branch_box_1214_nonnegative : ∀ j, 0 ≤ branch_box_1214.lower j ∧ 0 ≤ branch_box_1214.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1214, Box.profileLo, Box.profileHi, box_1214]
theorem leaf_1214_BranchSafe : CertificateConsequences.BranchSafe branch_box_1214 := by
  left; refine ⟨branch_box_1214_nonnegative, ?_⟩
  intro z hz; exact leaf_1214_sound hz

theorem leaf_1215_ok : checkAt 527 1000 box_1215 cert_1215 = true := by
  have h := List.all_eq_true.mp batch_24_08_ok accepted_1215 (by simp [batch_24_08_values])
  exact h
theorem leaf_1215_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1215.profileLo box_1215.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1215_ok
theorem branch_box_1215_nonnegative : ∀ j, 0 ≤ branch_box_1215.lower j ∧ 0 ≤ branch_box_1215.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1215, Box.profileLo, Box.profileHi, box_1215]
theorem leaf_1215_BranchSafe : CertificateConsequences.BranchSafe branch_box_1215 := by
  left; refine ⟨branch_box_1215_nonnegative, ?_⟩
  intro z hz; exact leaf_1215_sound hz

theorem leaf_1219_ok : checkAt 527 1000 box_1219 cert_1219 = true := by
  have h := List.all_eq_true.mp batch_24_09_ok accepted_1219 (by simp [batch_24_09_values])
  exact h
theorem leaf_1219_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1219.profileLo box_1219.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1219_ok
theorem branch_box_1219_nonnegative : ∀ j, 0 ≤ branch_box_1219.lower j ∧ 0 ≤ branch_box_1219.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1219, Box.profileLo, Box.profileHi, box_1219]
theorem leaf_1219_BranchSafe : CertificateConsequences.BranchSafe branch_box_1219 := by
  left; refine ⟨branch_box_1219_nonnegative, ?_⟩
  intro z hz; exact leaf_1219_sound hz

theorem leaf_1220_ok : checkAt 527 1000 box_1220 cert_1220 = true := by
  have h := List.all_eq_true.mp batch_24_10_ok accepted_1220 (by simp [batch_24_10_values])
  exact h
theorem leaf_1220_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1220.profileLo box_1220.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1220_ok
theorem branch_box_1220_nonnegative : ∀ j, 0 ≤ branch_box_1220.lower j ∧ 0 ≤ branch_box_1220.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1220, Box.profileLo, Box.profileHi, box_1220]
theorem leaf_1220_BranchSafe : CertificateConsequences.BranchSafe branch_box_1220 := by
  left; refine ⟨branch_box_1220_nonnegative, ?_⟩
  intro z hz; exact leaf_1220_sound hz

theorem leaf_1221_ok : checkAt 527 1000 box_1221 cert_1221 = true := by
  have h := List.all_eq_true.mp batch_24_11_ok accepted_1221 (by simp [batch_24_11_values])
  exact h
theorem leaf_1221_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1221.profileLo box_1221.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1221_ok
theorem branch_box_1221_nonnegative : ∀ j, 0 ≤ branch_box_1221.lower j ∧ 0 ≤ branch_box_1221.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1221, Box.profileLo, Box.profileHi, box_1221]
theorem leaf_1221_BranchSafe : CertificateConsequences.BranchSafe branch_box_1221 := by
  left; refine ⟨branch_box_1221_nonnegative, ?_⟩
  intro z hz; exact leaf_1221_sound hz

theorem leaf_1222_ok : checkAt 527 1000 box_1222 cert_1222 = true := by
  have h := List.all_eq_true.mp batch_24_12_ok accepted_1222 (by simp [batch_24_12_values])
  exact h
theorem leaf_1222_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1222.profileLo box_1222.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1222_ok
theorem branch_box_1222_nonnegative : ∀ j, 0 ≤ branch_box_1222.lower j ∧ 0 ≤ branch_box_1222.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1222, Box.profileLo, Box.profileHi, box_1222]
theorem leaf_1222_BranchSafe : CertificateConsequences.BranchSafe branch_box_1222 := by
  left; refine ⟨branch_box_1222_nonnegative, ?_⟩
  intro z hz; exact leaf_1222_sound hz

theorem leaf_1225_ok : checkAt 527 1000 box_1225 cert_1225 = true := by
  have h := List.all_eq_true.mp batch_24_13_ok accepted_1225 (by simp [batch_24_13_values])
  exact h
theorem leaf_1225_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1225.profileLo box_1225.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1225_ok
theorem branch_box_1225_nonnegative : ∀ j, 0 ≤ branch_box_1225.lower j ∧ 0 ≤ branch_box_1225.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1225, Box.profileLo, Box.profileHi, box_1225]
theorem leaf_1225_BranchSafe : CertificateConsequences.BranchSafe branch_box_1225 := by
  left; refine ⟨branch_box_1225_nonnegative, ?_⟩
  intro z hz; exact leaf_1225_sound hz

theorem leaf_1226_ok : checkAt 527 1000 box_1226 cert_1226 = true := by
  have h := List.all_eq_true.mp batch_24_14_ok accepted_1226 (by simp [batch_24_14_values])
  exact h
theorem leaf_1226_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1226.profileLo box_1226.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1226_ok
theorem branch_box_1226_nonnegative : ∀ j, 0 ≤ branch_box_1226.lower j ∧ 0 ≤ branch_box_1226.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1226, Box.profileLo, Box.profileHi, box_1226]
theorem leaf_1226_BranchSafe : CertificateConsequences.BranchSafe branch_box_1226 := by
  left; refine ⟨branch_box_1226_nonnegative, ?_⟩
  intro z hz; exact leaf_1226_sound hz

theorem leaf_1227_ok : checkAt 527 1000 box_1227 cert_1227 = true := by
  have h := List.all_eq_true.mp batch_24_15_ok accepted_1227 (by simp [batch_24_15_values])
  exact h
theorem leaf_1227_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1227.profileLo box_1227.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1227_ok
theorem branch_box_1227_nonnegative : ∀ j, 0 ≤ branch_box_1227.lower j ∧ 0 ≤ branch_box_1227.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1227, Box.profileLo, Box.profileHi, box_1227]
theorem leaf_1227_BranchSafe : CertificateConsequences.BranchSafe branch_box_1227 := by
  left; refine ⟨branch_box_1227_nonnegative, ?_⟩
  intro z hz; exact leaf_1227_sound hz

theorem leaf_1229_ok : checkAt 527 1000 box_1229 cert_1229 = true := by
  have h := List.all_eq_true.mp batch_24_16_ok accepted_1229 (by simp [batch_24_16_values])
  exact h
theorem leaf_1229_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1229.profileLo box_1229.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1229_ok
theorem branch_box_1229_nonnegative : ∀ j, 0 ≤ branch_box_1229.lower j ∧ 0 ≤ branch_box_1229.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1229, Box.profileLo, Box.profileHi, box_1229]
theorem leaf_1229_BranchSafe : CertificateConsequences.BranchSafe branch_box_1229 := by
  left; refine ⟨branch_box_1229_nonnegative, ?_⟩
  intro z hz; exact leaf_1229_sound hz

theorem leaf_1230_ok : checkAt 527 1000 box_1230 cert_1230 = true := by
  have h := List.all_eq_true.mp batch_24_17_ok accepted_1230 (by simp [batch_24_17_values])
  exact h
theorem leaf_1230_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1230.profileLo box_1230.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1230_ok
theorem branch_box_1230_nonnegative : ∀ j, 0 ≤ branch_box_1230.lower j ∧ 0 ≤ branch_box_1230.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1230, Box.profileLo, Box.profileHi, box_1230]
theorem leaf_1230_BranchSafe : CertificateConsequences.BranchSafe branch_box_1230 := by
  left; refine ⟨branch_box_1230_nonnegative, ?_⟩
  intro z hz; exact leaf_1230_sound hz

theorem leaf_1241_ok : checkAt 527 1000 box_1241 cert_1241 = true := by
  have h := List.all_eq_true.mp batch_24_18_ok accepted_1241 (by simp [batch_24_18_values])
  exact h
theorem leaf_1241_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1241.profileLo box_1241.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1241_ok
theorem branch_box_1241_nonnegative : ∀ j, 0 ≤ branch_box_1241.lower j ∧ 0 ≤ branch_box_1241.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1241, Box.profileLo, Box.profileHi, box_1241]
theorem leaf_1241_BranchSafe : CertificateConsequences.BranchSafe branch_box_1241 := by
  left; refine ⟨branch_box_1241_nonnegative, ?_⟩
  intro z hz; exact leaf_1241_sound hz

theorem leaf_1242_ok : checkAt 527 1000 box_1242 cert_1242 = true := by
  have h := List.all_eq_true.mp batch_24_19_ok accepted_1242 (by simp [batch_24_19_values])
  exact h
theorem leaf_1242_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1242.profileLo box_1242.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1242_ok
theorem branch_box_1242_nonnegative : ∀ j, 0 ≤ branch_box_1242.lower j ∧ 0 ≤ branch_box_1242.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1242, Box.profileLo, Box.profileHi, box_1242]
theorem leaf_1242_BranchSafe : CertificateConsequences.BranchSafe branch_box_1242 := by
  left; refine ⟨branch_box_1242_nonnegative, ?_⟩
  intro z hz; exact leaf_1242_sound hz

theorem leaf_1243_ok : checkAt 527 1000 box_1243 cert_1243 = true := by
  have h := List.all_eq_true.mp batch_24_20_ok accepted_1243 (by simp [batch_24_20_values])
  exact h
theorem leaf_1243_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1243.profileLo box_1243.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1243_ok
theorem branch_box_1243_nonnegative : ∀ j, 0 ≤ branch_box_1243.lower j ∧ 0 ≤ branch_box_1243.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1243, Box.profileLo, Box.profileHi, box_1243]
theorem leaf_1243_BranchSafe : CertificateConsequences.BranchSafe branch_box_1243 := by
  left; refine ⟨branch_box_1243_nonnegative, ?_⟩
  intro z hz; exact leaf_1243_sound hz

theorem leaf_1244_ok : checkAt 527 1000 box_1244 cert_1244 = true := by
  have h := List.all_eq_true.mp batch_24_21_ok accepted_1244 (by simp [batch_24_21_values])
  exact h
theorem leaf_1244_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1244.profileLo box_1244.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1244_ok
theorem branch_box_1244_nonnegative : ∀ j, 0 ≤ branch_box_1244.lower j ∧ 0 ≤ branch_box_1244.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1244, Box.profileLo, Box.profileHi, box_1244]
theorem leaf_1244_BranchSafe : CertificateConsequences.BranchSafe branch_box_1244 := by
  left; refine ⟨branch_box_1244_nonnegative, ?_⟩
  intro z hz; exact leaf_1244_sound hz

theorem leaf_1246_ok : checkAt 527 1000 box_1246 cert_1246 = true := by
  have h := List.all_eq_true.mp batch_24_22_ok accepted_1246 (by simp [batch_24_22_values])
  exact h
theorem leaf_1246_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1246.profileLo box_1246.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1246_ok
theorem branch_box_1246_nonnegative : ∀ j, 0 ≤ branch_box_1246.lower j ∧ 0 ≤ branch_box_1246.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1246, Box.profileLo, Box.profileHi, box_1246]
theorem leaf_1246_BranchSafe : CertificateConsequences.BranchSafe branch_box_1246 := by
  left; refine ⟨branch_box_1246_nonnegative, ?_⟩
  intro z hz; exact leaf_1246_sound hz

theorem leaf_1247_ok : checkAt 527 1000 box_1247 cert_1247 = true := by
  have h := List.all_eq_true.mp batch_24_23_ok accepted_1247 (by simp [batch_24_23_values])
  exact h
theorem leaf_1247_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1247.profileLo box_1247.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1247_ok
theorem branch_box_1247_nonnegative : ∀ j, 0 ≤ branch_box_1247.lower j ∧ 0 ≤ branch_box_1247.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1247, Box.profileLo, Box.profileHi, box_1247]
theorem leaf_1247_BranchSafe : CertificateConsequences.BranchSafe branch_box_1247 := by
  left; refine ⟨branch_box_1247_nonnegative, ?_⟩
  intro z hz; exact leaf_1247_sound hz

theorem leaf_1248_ok : checkAt 527 1000 box_1248 cert_1248 = true := by
  have h := List.all_eq_true.mp batch_24_24_ok accepted_1248 (by simp [batch_24_24_values])
  exact h
theorem leaf_1248_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1248.profileLo box_1248.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1248_ok
theorem branch_box_1248_nonnegative : ∀ j, 0 ≤ branch_box_1248.lower j ∧ 0 ≤ branch_box_1248.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1248, Box.profileLo, Box.profileHi, box_1248]
theorem leaf_1248_BranchSafe : CertificateConsequences.BranchSafe branch_box_1248 := by
  left; refine ⟨branch_box_1248_nonnegative, ?_⟩
  intro z hz; exact leaf_1248_sound hz

#print axioms batch_24_00_ok
#print axioms leaf_1200_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
