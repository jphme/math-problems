import PeaceableQueens.UpperBound.Generated.Even.C527Scaled25Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_25_00_values : List Bool := [accepted_1254]
theorem batch_25_00_ok : batch_25_00_values.all id = true := by decide

def batch_25_01_values : List Bool := [accepted_1255]
theorem batch_25_01_ok : batch_25_01_values.all id = true := by decide

def batch_25_02_values : List Bool := [accepted_1256]
theorem batch_25_02_ok : batch_25_02_values.all id = true := by decide

def batch_25_03_values : List Bool := [accepted_1257]
theorem batch_25_03_ok : batch_25_03_values.all id = true := by decide

def batch_25_04_values : List Bool := [accepted_1258]
theorem batch_25_04_ok : batch_25_04_values.all id = true := by decide

def batch_25_05_values : List Bool := [accepted_1262]
theorem batch_25_05_ok : batch_25_05_values.all id = true := by decide

def batch_25_06_values : List Bool := [accepted_1263]
theorem batch_25_06_ok : batch_25_06_values.all id = true := by decide

def batch_25_07_values : List Bool := [accepted_1264]
theorem batch_25_07_ok : batch_25_07_values.all id = true := by decide

def batch_25_08_values : List Bool := [accepted_1265]
theorem batch_25_08_ok : batch_25_08_values.all id = true := by decide

def batch_25_09_values : List Bool := [accepted_1268]
theorem batch_25_09_ok : batch_25_09_values.all id = true := by decide

def batch_25_10_values : List Bool := [accepted_1269]
theorem batch_25_10_ok : batch_25_10_values.all id = true := by decide

def batch_25_11_values : List Bool := [accepted_1270]
theorem batch_25_11_ok : batch_25_11_values.all id = true := by decide

def batch_25_12_values : List Bool := [accepted_1274]
theorem batch_25_12_ok : batch_25_12_values.all id = true := by decide

def batch_25_13_values : List Bool := [accepted_1275]
theorem batch_25_13_ok : batch_25_13_values.all id = true := by decide

def batch_25_14_values : List Bool := [accepted_1276]
theorem batch_25_14_ok : batch_25_14_values.all id = true := by decide

def batch_25_15_values : List Bool := [accepted_1277]
theorem batch_25_15_ok : batch_25_15_values.all id = true := by decide

def batch_25_16_values : List Bool := [accepted_1278]
theorem batch_25_16_ok : batch_25_16_values.all id = true := by decide

def batch_25_17_values : List Bool := [accepted_1288]
theorem batch_25_17_ok : batch_25_17_values.all id = true := by decide

def batch_25_18_values : List Bool := [accepted_1290]
theorem batch_25_18_ok : batch_25_18_values.all id = true := by decide

def batch_25_19_values : List Bool := [accepted_1292]
theorem batch_25_19_ok : batch_25_19_values.all id = true := by decide

def batch_25_20_values : List Bool := [accepted_1293]
theorem batch_25_20_ok : batch_25_20_values.all id = true := by decide

def batch_25_21_values : List Bool := [accepted_1294]
theorem batch_25_21_ok : batch_25_21_values.all id = true := by decide

def batch_25_22_values : List Bool := [accepted_1298]
theorem batch_25_22_ok : batch_25_22_values.all id = true := by decide

theorem leaf_1254_ok : checkAt 527 1000 box_1254 cert_1254 = true := by
  have h := List.all_eq_true.mp batch_25_00_ok accepted_1254 (by simp [batch_25_00_values])
  exact h
theorem leaf_1254_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1254.profileLo box_1254.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1254_ok
theorem branch_box_1254_nonnegative : ∀ j, 0 ≤ branch_box_1254.lower j ∧ 0 ≤ branch_box_1254.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1254, Box.profileLo, Box.profileHi, box_1254]
theorem leaf_1254_BranchSafe : CertificateConsequences.BranchSafe branch_box_1254 := by
  left; refine ⟨branch_box_1254_nonnegative, ?_⟩
  intro z hz; exact leaf_1254_sound hz

theorem leaf_1255_ok : checkAt 527 1000 box_1255 cert_1255 = true := by
  have h := List.all_eq_true.mp batch_25_01_ok accepted_1255 (by simp [batch_25_01_values])
  exact h
theorem leaf_1255_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1255.profileLo box_1255.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1255_ok
theorem branch_box_1255_nonnegative : ∀ j, 0 ≤ branch_box_1255.lower j ∧ 0 ≤ branch_box_1255.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1255, Box.profileLo, Box.profileHi, box_1255]
theorem leaf_1255_BranchSafe : CertificateConsequences.BranchSafe branch_box_1255 := by
  left; refine ⟨branch_box_1255_nonnegative, ?_⟩
  intro z hz; exact leaf_1255_sound hz

theorem leaf_1256_ok : checkAt 527 1000 box_1256 cert_1256 = true := by
  have h := List.all_eq_true.mp batch_25_02_ok accepted_1256 (by simp [batch_25_02_values])
  exact h
theorem leaf_1256_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1256.profileLo box_1256.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1256_ok
theorem branch_box_1256_nonnegative : ∀ j, 0 ≤ branch_box_1256.lower j ∧ 0 ≤ branch_box_1256.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1256, Box.profileLo, Box.profileHi, box_1256]
theorem leaf_1256_BranchSafe : CertificateConsequences.BranchSafe branch_box_1256 := by
  left; refine ⟨branch_box_1256_nonnegative, ?_⟩
  intro z hz; exact leaf_1256_sound hz

theorem leaf_1257_ok : checkAt 527 1000 box_1257 cert_1257 = true := by
  have h := List.all_eq_true.mp batch_25_03_ok accepted_1257 (by simp [batch_25_03_values])
  exact h
theorem leaf_1257_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1257.profileLo box_1257.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1257_ok
theorem branch_box_1257_nonnegative : ∀ j, 0 ≤ branch_box_1257.lower j ∧ 0 ≤ branch_box_1257.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1257, Box.profileLo, Box.profileHi, box_1257]
theorem leaf_1257_BranchSafe : CertificateConsequences.BranchSafe branch_box_1257 := by
  left; refine ⟨branch_box_1257_nonnegative, ?_⟩
  intro z hz; exact leaf_1257_sound hz

theorem leaf_1258_ok : checkAt 527 1000 box_1258 cert_1258 = true := by
  have h := List.all_eq_true.mp batch_25_04_ok accepted_1258 (by simp [batch_25_04_values])
  exact h
theorem leaf_1258_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1258.profileLo box_1258.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1258_ok
theorem branch_box_1258_nonnegative : ∀ j, 0 ≤ branch_box_1258.lower j ∧ 0 ≤ branch_box_1258.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1258, Box.profileLo, Box.profileHi, box_1258]
theorem leaf_1258_BranchSafe : CertificateConsequences.BranchSafe branch_box_1258 := by
  left; refine ⟨branch_box_1258_nonnegative, ?_⟩
  intro z hz; exact leaf_1258_sound hz

theorem leaf_1262_ok : checkAt 527 1000 box_1262 cert_1262 = true := by
  have h := List.all_eq_true.mp batch_25_05_ok accepted_1262 (by simp [batch_25_05_values])
  exact h
theorem leaf_1262_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1262.profileLo box_1262.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1262_ok
theorem branch_box_1262_nonnegative : ∀ j, 0 ≤ branch_box_1262.lower j ∧ 0 ≤ branch_box_1262.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1262, Box.profileLo, Box.profileHi, box_1262]
theorem leaf_1262_BranchSafe : CertificateConsequences.BranchSafe branch_box_1262 := by
  left; refine ⟨branch_box_1262_nonnegative, ?_⟩
  intro z hz; exact leaf_1262_sound hz

theorem leaf_1263_ok : checkAt 527 1000 box_1263 cert_1263 = true := by
  have h := List.all_eq_true.mp batch_25_06_ok accepted_1263 (by simp [batch_25_06_values])
  exact h
theorem leaf_1263_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1263.profileLo box_1263.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1263_ok
theorem branch_box_1263_nonnegative : ∀ j, 0 ≤ branch_box_1263.lower j ∧ 0 ≤ branch_box_1263.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1263, Box.profileLo, Box.profileHi, box_1263]
theorem leaf_1263_BranchSafe : CertificateConsequences.BranchSafe branch_box_1263 := by
  left; refine ⟨branch_box_1263_nonnegative, ?_⟩
  intro z hz; exact leaf_1263_sound hz

theorem leaf_1264_ok : checkAt 527 1000 box_1264 cert_1264 = true := by
  have h := List.all_eq_true.mp batch_25_07_ok accepted_1264 (by simp [batch_25_07_values])
  exact h
theorem leaf_1264_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1264.profileLo box_1264.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1264_ok
theorem branch_box_1264_nonnegative : ∀ j, 0 ≤ branch_box_1264.lower j ∧ 0 ≤ branch_box_1264.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1264, Box.profileLo, Box.profileHi, box_1264]
theorem leaf_1264_BranchSafe : CertificateConsequences.BranchSafe branch_box_1264 := by
  left; refine ⟨branch_box_1264_nonnegative, ?_⟩
  intro z hz; exact leaf_1264_sound hz

theorem leaf_1265_ok : checkAt 527 1000 box_1265 cert_1265 = true := by
  have h := List.all_eq_true.mp batch_25_08_ok accepted_1265 (by simp [batch_25_08_values])
  exact h
theorem leaf_1265_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1265.profileLo box_1265.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1265_ok
theorem branch_box_1265_nonnegative : ∀ j, 0 ≤ branch_box_1265.lower j ∧ 0 ≤ branch_box_1265.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1265, Box.profileLo, Box.profileHi, box_1265]
theorem leaf_1265_BranchSafe : CertificateConsequences.BranchSafe branch_box_1265 := by
  left; refine ⟨branch_box_1265_nonnegative, ?_⟩
  intro z hz; exact leaf_1265_sound hz

theorem leaf_1268_ok : checkAt 527 1000 box_1268 cert_1268 = true := by
  have h := List.all_eq_true.mp batch_25_09_ok accepted_1268 (by simp [batch_25_09_values])
  exact h
theorem leaf_1268_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1268.profileLo box_1268.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1268_ok
theorem branch_box_1268_nonnegative : ∀ j, 0 ≤ branch_box_1268.lower j ∧ 0 ≤ branch_box_1268.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1268, Box.profileLo, Box.profileHi, box_1268]
theorem leaf_1268_BranchSafe : CertificateConsequences.BranchSafe branch_box_1268 := by
  left; refine ⟨branch_box_1268_nonnegative, ?_⟩
  intro z hz; exact leaf_1268_sound hz

theorem leaf_1269_ok : checkAt 527 1000 box_1269 cert_1269 = true := by
  have h := List.all_eq_true.mp batch_25_10_ok accepted_1269 (by simp [batch_25_10_values])
  exact h
theorem leaf_1269_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1269.profileLo box_1269.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1269_ok
theorem branch_box_1269_nonnegative : ∀ j, 0 ≤ branch_box_1269.lower j ∧ 0 ≤ branch_box_1269.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1269, Box.profileLo, Box.profileHi, box_1269]
theorem leaf_1269_BranchSafe : CertificateConsequences.BranchSafe branch_box_1269 := by
  left; refine ⟨branch_box_1269_nonnegative, ?_⟩
  intro z hz; exact leaf_1269_sound hz

theorem leaf_1270_ok : checkAt 527 1000 box_1270 cert_1270 = true := by
  have h := List.all_eq_true.mp batch_25_11_ok accepted_1270 (by simp [batch_25_11_values])
  exact h
theorem leaf_1270_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1270.profileLo box_1270.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1270_ok
theorem branch_box_1270_nonnegative : ∀ j, 0 ≤ branch_box_1270.lower j ∧ 0 ≤ branch_box_1270.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1270, Box.profileLo, Box.profileHi, box_1270]
theorem leaf_1270_BranchSafe : CertificateConsequences.BranchSafe branch_box_1270 := by
  left; refine ⟨branch_box_1270_nonnegative, ?_⟩
  intro z hz; exact leaf_1270_sound hz

theorem leaf_1274_ok : checkAt 527 1000 box_1274 cert_1274 = true := by
  have h := List.all_eq_true.mp batch_25_12_ok accepted_1274 (by simp [batch_25_12_values])
  exact h
theorem leaf_1274_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1274.profileLo box_1274.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1274_ok
theorem branch_box_1274_nonnegative : ∀ j, 0 ≤ branch_box_1274.lower j ∧ 0 ≤ branch_box_1274.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1274, Box.profileLo, Box.profileHi, box_1274]
theorem leaf_1274_BranchSafe : CertificateConsequences.BranchSafe branch_box_1274 := by
  left; refine ⟨branch_box_1274_nonnegative, ?_⟩
  intro z hz; exact leaf_1274_sound hz

theorem leaf_1275_ok : checkAt 527 1000 box_1275 cert_1275 = true := by
  have h := List.all_eq_true.mp batch_25_13_ok accepted_1275 (by simp [batch_25_13_values])
  exact h
theorem leaf_1275_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1275.profileLo box_1275.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1275_ok
theorem branch_box_1275_nonnegative : ∀ j, 0 ≤ branch_box_1275.lower j ∧ 0 ≤ branch_box_1275.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1275, Box.profileLo, Box.profileHi, box_1275]
theorem leaf_1275_BranchSafe : CertificateConsequences.BranchSafe branch_box_1275 := by
  left; refine ⟨branch_box_1275_nonnegative, ?_⟩
  intro z hz; exact leaf_1275_sound hz

theorem leaf_1276_ok : checkAt 527 1000 box_1276 cert_1276 = true := by
  have h := List.all_eq_true.mp batch_25_14_ok accepted_1276 (by simp [batch_25_14_values])
  exact h
theorem leaf_1276_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1276.profileLo box_1276.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1276_ok
theorem branch_box_1276_nonnegative : ∀ j, 0 ≤ branch_box_1276.lower j ∧ 0 ≤ branch_box_1276.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1276, Box.profileLo, Box.profileHi, box_1276]
theorem leaf_1276_BranchSafe : CertificateConsequences.BranchSafe branch_box_1276 := by
  left; refine ⟨branch_box_1276_nonnegative, ?_⟩
  intro z hz; exact leaf_1276_sound hz

theorem leaf_1277_ok : checkAt 527 1000 box_1277 cert_1277 = true := by
  have h := List.all_eq_true.mp batch_25_15_ok accepted_1277 (by simp [batch_25_15_values])
  exact h
theorem leaf_1277_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1277.profileLo box_1277.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1277_ok
theorem branch_box_1277_nonnegative : ∀ j, 0 ≤ branch_box_1277.lower j ∧ 0 ≤ branch_box_1277.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1277, Box.profileLo, Box.profileHi, box_1277]
theorem leaf_1277_BranchSafe : CertificateConsequences.BranchSafe branch_box_1277 := by
  left; refine ⟨branch_box_1277_nonnegative, ?_⟩
  intro z hz; exact leaf_1277_sound hz

theorem leaf_1278_ok : checkAt 527 1000 box_1278 cert_1278 = true := by
  have h := List.all_eq_true.mp batch_25_16_ok accepted_1278 (by simp [batch_25_16_values])
  exact h
theorem leaf_1278_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1278.profileLo box_1278.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1278_ok
theorem branch_box_1278_nonnegative : ∀ j, 0 ≤ branch_box_1278.lower j ∧ 0 ≤ branch_box_1278.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1278, Box.profileLo, Box.profileHi, box_1278]
theorem leaf_1278_BranchSafe : CertificateConsequences.BranchSafe branch_box_1278 := by
  left; refine ⟨branch_box_1278_nonnegative, ?_⟩
  intro z hz; exact leaf_1278_sound hz

theorem leaf_1288_ok : checkAt 527 1000 box_1288 cert_1288 = true := by
  have h := List.all_eq_true.mp batch_25_17_ok accepted_1288 (by simp [batch_25_17_values])
  exact h
theorem leaf_1288_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1288.profileLo box_1288.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1288_ok
theorem branch_box_1288_nonnegative : ∀ j, 0 ≤ branch_box_1288.lower j ∧ 0 ≤ branch_box_1288.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1288, Box.profileLo, Box.profileHi, box_1288]
theorem leaf_1288_BranchSafe : CertificateConsequences.BranchSafe branch_box_1288 := by
  left; refine ⟨branch_box_1288_nonnegative, ?_⟩
  intro z hz; exact leaf_1288_sound hz

theorem leaf_1290_ok : checkAt 527 1000 box_1290 cert_1290 = true := by
  have h := List.all_eq_true.mp batch_25_18_ok accepted_1290 (by simp [batch_25_18_values])
  exact h
theorem leaf_1290_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1290.profileLo box_1290.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1290_ok
theorem branch_box_1290_nonnegative : ∀ j, 0 ≤ branch_box_1290.lower j ∧ 0 ≤ branch_box_1290.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1290, Box.profileLo, Box.profileHi, box_1290]
theorem leaf_1290_BranchSafe : CertificateConsequences.BranchSafe branch_box_1290 := by
  left; refine ⟨branch_box_1290_nonnegative, ?_⟩
  intro z hz; exact leaf_1290_sound hz

theorem leaf_1292_ok : checkAt 527 1000 box_1292 cert_1292 = true := by
  have h := List.all_eq_true.mp batch_25_19_ok accepted_1292 (by simp [batch_25_19_values])
  exact h
theorem leaf_1292_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1292.profileLo box_1292.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1292_ok
theorem branch_box_1292_nonnegative : ∀ j, 0 ≤ branch_box_1292.lower j ∧ 0 ≤ branch_box_1292.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1292, Box.profileLo, Box.profileHi, box_1292]
theorem leaf_1292_BranchSafe : CertificateConsequences.BranchSafe branch_box_1292 := by
  left; refine ⟨branch_box_1292_nonnegative, ?_⟩
  intro z hz; exact leaf_1292_sound hz

theorem leaf_1293_ok : checkAt 527 1000 box_1293 cert_1293 = true := by
  have h := List.all_eq_true.mp batch_25_20_ok accepted_1293 (by simp [batch_25_20_values])
  exact h
theorem leaf_1293_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1293.profileLo box_1293.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1293_ok
theorem branch_box_1293_nonnegative : ∀ j, 0 ≤ branch_box_1293.lower j ∧ 0 ≤ branch_box_1293.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1293, Box.profileLo, Box.profileHi, box_1293]
theorem leaf_1293_BranchSafe : CertificateConsequences.BranchSafe branch_box_1293 := by
  left; refine ⟨branch_box_1293_nonnegative, ?_⟩
  intro z hz; exact leaf_1293_sound hz

theorem leaf_1294_ok : checkAt 527 1000 box_1294 cert_1294 = true := by
  have h := List.all_eq_true.mp batch_25_21_ok accepted_1294 (by simp [batch_25_21_values])
  exact h
theorem leaf_1294_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1294.profileLo box_1294.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1294_ok
theorem branch_box_1294_nonnegative : ∀ j, 0 ≤ branch_box_1294.lower j ∧ 0 ≤ branch_box_1294.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1294, Box.profileLo, Box.profileHi, box_1294]
theorem leaf_1294_BranchSafe : CertificateConsequences.BranchSafe branch_box_1294 := by
  left; refine ⟨branch_box_1294_nonnegative, ?_⟩
  intro z hz; exact leaf_1294_sound hz

theorem leaf_1298_ok : checkAt 527 1000 box_1298 cert_1298 = true := by
  have h := List.all_eq_true.mp batch_25_22_ok accepted_1298 (by simp [batch_25_22_values])
  exact h
theorem leaf_1298_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1298.profileLo box_1298.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1298_ok
theorem branch_box_1298_nonnegative : ∀ j, 0 ≤ branch_box_1298.lower j ∧ 0 ≤ branch_box_1298.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1298, Box.profileLo, Box.profileHi, box_1298]
theorem leaf_1298_BranchSafe : CertificateConsequences.BranchSafe branch_box_1298 := by
  left; refine ⟨branch_box_1298_nonnegative, ?_⟩
  intro z hz; exact leaf_1298_sound hz

#print axioms batch_25_00_ok
#print axioms leaf_1254_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
