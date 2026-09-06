import PeaceableQueens.UpperBound.Generated.Even.C527Scaled30Data
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.ScaledIntDualLeaf

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def batch_30_00_values : List Bool := [accepted_1501]
theorem batch_30_00_ok : batch_30_00_values.all id = true := by decide

def batch_30_01_values : List Bool := [accepted_1502]
theorem batch_30_01_ok : batch_30_01_values.all id = true := by decide

def batch_30_02_values : List Bool := [accepted_1503]
theorem batch_30_02_ok : batch_30_02_values.all id = true := by decide

def batch_30_03_values : List Bool := [accepted_1504]
theorem batch_30_03_ok : batch_30_03_values.all id = true := by decide

def batch_30_04_values : List Bool := [accepted_1506]
theorem batch_30_04_ok : batch_30_04_values.all id = true := by decide

def batch_30_05_values : List Bool := [accepted_1507]
theorem batch_30_05_ok : batch_30_05_values.all id = true := by decide

def batch_30_06_values : List Bool := [accepted_1509]
theorem batch_30_06_ok : batch_30_06_values.all id = true := by decide

def batch_30_07_values : List Bool := [accepted_1510]
theorem batch_30_07_ok : batch_30_07_values.all id = true := by decide

def batch_30_08_values : List Bool := [accepted_1511]
theorem batch_30_08_ok : batch_30_08_values.all id = true := by decide

def batch_30_09_values : List Bool := [accepted_1513]
theorem batch_30_09_ok : batch_30_09_values.all id = true := by decide

def batch_30_10_values : List Bool := [accepted_1514]
theorem batch_30_10_ok : batch_30_10_values.all id = true := by decide

def batch_30_11_values : List Bool := [accepted_1520]
theorem batch_30_11_ok : batch_30_11_values.all id = true := by decide

def batch_30_12_values : List Bool := [accepted_1521]
theorem batch_30_12_ok : batch_30_12_values.all id = true := by decide

def batch_30_13_values : List Bool := [accepted_1522]
theorem batch_30_13_ok : batch_30_13_values.all id = true := by decide

def batch_30_14_values : List Bool := [accepted_1526]
theorem batch_30_14_ok : batch_30_14_values.all id = true := by decide

def batch_30_15_values : List Bool := [accepted_1527]
theorem batch_30_15_ok : batch_30_15_values.all id = true := by decide

def batch_30_16_values : List Bool := [accepted_1529]
theorem batch_30_16_ok : batch_30_16_values.all id = true := by decide

def batch_30_17_values : List Bool := [accepted_1530]
theorem batch_30_17_ok : batch_30_17_values.all id = true := by decide

def batch_30_18_values : List Bool := [accepted_1531]
theorem batch_30_18_ok : batch_30_18_values.all id = true := by decide

def batch_30_19_values : List Bool := [accepted_1532]
theorem batch_30_19_ok : batch_30_19_values.all id = true := by decide

def batch_30_20_values : List Bool := [accepted_1535]
theorem batch_30_20_ok : batch_30_20_values.all id = true := by decide

def batch_30_21_values : List Bool := [accepted_1538]
theorem batch_30_21_ok : batch_30_21_values.all id = true := by decide

def batch_30_22_values : List Bool := [accepted_1541]
theorem batch_30_22_ok : batch_30_22_values.all id = true := by decide

def batch_30_23_values : List Bool := [accepted_1542]
theorem batch_30_23_ok : batch_30_23_values.all id = true := by decide

def batch_30_24_values : List Bool := [accepted_1543]
theorem batch_30_24_ok : batch_30_24_values.all id = true := by decide

def batch_30_25_values : List Bool := [accepted_1544]
theorem batch_30_25_ok : batch_30_25_values.all id = true := by decide

def batch_30_26_values : List Bool := [accepted_1548]
theorem batch_30_26_ok : batch_30_26_values.all id = true := by decide

theorem leaf_1501_ok : checkAt 527 1000 box_1501 cert_1501 = true := by
  have h := List.all_eq_true.mp batch_30_00_ok accepted_1501 (by simp [batch_30_00_values])
  exact h
theorem leaf_1501_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1501.profileLo box_1501.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1501_ok
theorem branch_box_1501_nonnegative : ∀ j, 0 ≤ branch_box_1501.lower j ∧ 0 ≤ branch_box_1501.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1501, Box.profileLo, Box.profileHi, box_1501]
theorem leaf_1501_BranchSafe : CertificateConsequences.BranchSafe branch_box_1501 := by
  left; refine ⟨branch_box_1501_nonnegative, ?_⟩
  intro z hz; exact leaf_1501_sound hz

theorem leaf_1502_ok : checkAt 527 1000 box_1502 cert_1502 = true := by
  have h := List.all_eq_true.mp batch_30_01_ok accepted_1502 (by simp [batch_30_01_values])
  exact h
theorem leaf_1502_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1502.profileLo box_1502.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1502_ok
theorem branch_box_1502_nonnegative : ∀ j, 0 ≤ branch_box_1502.lower j ∧ 0 ≤ branch_box_1502.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1502, Box.profileLo, Box.profileHi, box_1502]
theorem leaf_1502_BranchSafe : CertificateConsequences.BranchSafe branch_box_1502 := by
  left; refine ⟨branch_box_1502_nonnegative, ?_⟩
  intro z hz; exact leaf_1502_sound hz

theorem leaf_1503_ok : checkAt 527 1000 box_1503 cert_1503 = true := by
  have h := List.all_eq_true.mp batch_30_02_ok accepted_1503 (by simp [batch_30_02_values])
  exact h
theorem leaf_1503_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1503.profileLo box_1503.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1503_ok
theorem branch_box_1503_nonnegative : ∀ j, 0 ≤ branch_box_1503.lower j ∧ 0 ≤ branch_box_1503.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1503, Box.profileLo, Box.profileHi, box_1503]
theorem leaf_1503_BranchSafe : CertificateConsequences.BranchSafe branch_box_1503 := by
  left; refine ⟨branch_box_1503_nonnegative, ?_⟩
  intro z hz; exact leaf_1503_sound hz

theorem leaf_1504_ok : checkAt 527 1000 box_1504 cert_1504 = true := by
  have h := List.all_eq_true.mp batch_30_03_ok accepted_1504 (by simp [batch_30_03_values])
  exact h
theorem leaf_1504_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1504.profileLo box_1504.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1504_ok
theorem branch_box_1504_nonnegative : ∀ j, 0 ≤ branch_box_1504.lower j ∧ 0 ≤ branch_box_1504.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1504, Box.profileLo, Box.profileHi, box_1504]
theorem leaf_1504_BranchSafe : CertificateConsequences.BranchSafe branch_box_1504 := by
  left; refine ⟨branch_box_1504_nonnegative, ?_⟩
  intro z hz; exact leaf_1504_sound hz

theorem leaf_1506_ok : checkAt 527 1000 box_1506 cert_1506 = true := by
  have h := List.all_eq_true.mp batch_30_04_ok accepted_1506 (by simp [batch_30_04_values])
  exact h
theorem leaf_1506_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1506.profileLo box_1506.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1506_ok
theorem branch_box_1506_nonnegative : ∀ j, 0 ≤ branch_box_1506.lower j ∧ 0 ≤ branch_box_1506.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1506, Box.profileLo, Box.profileHi, box_1506]
theorem leaf_1506_BranchSafe : CertificateConsequences.BranchSafe branch_box_1506 := by
  left; refine ⟨branch_box_1506_nonnegative, ?_⟩
  intro z hz; exact leaf_1506_sound hz

theorem leaf_1507_ok : checkAt 527 1000 box_1507 cert_1507 = true := by
  have h := List.all_eq_true.mp batch_30_05_ok accepted_1507 (by simp [batch_30_05_values])
  exact h
theorem leaf_1507_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1507.profileLo box_1507.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1507_ok
theorem branch_box_1507_nonnegative : ∀ j, 0 ≤ branch_box_1507.lower j ∧ 0 ≤ branch_box_1507.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1507, Box.profileLo, Box.profileHi, box_1507]
theorem leaf_1507_BranchSafe : CertificateConsequences.BranchSafe branch_box_1507 := by
  left; refine ⟨branch_box_1507_nonnegative, ?_⟩
  intro z hz; exact leaf_1507_sound hz

theorem leaf_1509_ok : checkAt 527 1000 box_1509 cert_1509 = true := by
  have h := List.all_eq_true.mp batch_30_06_ok accepted_1509 (by simp [batch_30_06_values])
  exact h
theorem leaf_1509_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1509.profileLo box_1509.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1509_ok
theorem branch_box_1509_nonnegative : ∀ j, 0 ≤ branch_box_1509.lower j ∧ 0 ≤ branch_box_1509.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1509, Box.profileLo, Box.profileHi, box_1509]
theorem leaf_1509_BranchSafe : CertificateConsequences.BranchSafe branch_box_1509 := by
  left; refine ⟨branch_box_1509_nonnegative, ?_⟩
  intro z hz; exact leaf_1509_sound hz

theorem leaf_1510_ok : checkAt 527 1000 box_1510 cert_1510 = true := by
  have h := List.all_eq_true.mp batch_30_07_ok accepted_1510 (by simp [batch_30_07_values])
  exact h
theorem leaf_1510_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1510.profileLo box_1510.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1510_ok
theorem branch_box_1510_nonnegative : ∀ j, 0 ≤ branch_box_1510.lower j ∧ 0 ≤ branch_box_1510.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1510, Box.profileLo, Box.profileHi, box_1510]
theorem leaf_1510_BranchSafe : CertificateConsequences.BranchSafe branch_box_1510 := by
  left; refine ⟨branch_box_1510_nonnegative, ?_⟩
  intro z hz; exact leaf_1510_sound hz

theorem leaf_1511_ok : checkAt 527 1000 box_1511 cert_1511 = true := by
  have h := List.all_eq_true.mp batch_30_08_ok accepted_1511 (by simp [batch_30_08_values])
  exact h
theorem leaf_1511_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1511.profileLo box_1511.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1511_ok
theorem branch_box_1511_nonnegative : ∀ j, 0 ≤ branch_box_1511.lower j ∧ 0 ≤ branch_box_1511.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1511, Box.profileLo, Box.profileHi, box_1511]
theorem leaf_1511_BranchSafe : CertificateConsequences.BranchSafe branch_box_1511 := by
  left; refine ⟨branch_box_1511_nonnegative, ?_⟩
  intro z hz; exact leaf_1511_sound hz

theorem leaf_1513_ok : checkAt 527 1000 box_1513 cert_1513 = true := by
  have h := List.all_eq_true.mp batch_30_09_ok accepted_1513 (by simp [batch_30_09_values])
  exact h
theorem leaf_1513_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1513.profileLo box_1513.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1513_ok
theorem branch_box_1513_nonnegative : ∀ j, 0 ≤ branch_box_1513.lower j ∧ 0 ≤ branch_box_1513.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1513, Box.profileLo, Box.profileHi, box_1513]
theorem leaf_1513_BranchSafe : CertificateConsequences.BranchSafe branch_box_1513 := by
  left; refine ⟨branch_box_1513_nonnegative, ?_⟩
  intro z hz; exact leaf_1513_sound hz

theorem leaf_1514_ok : checkAt 527 1000 box_1514 cert_1514 = true := by
  have h := List.all_eq_true.mp batch_30_10_ok accepted_1514 (by simp [batch_30_10_values])
  exact h
theorem leaf_1514_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1514.profileLo box_1514.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1514_ok
theorem branch_box_1514_nonnegative : ∀ j, 0 ≤ branch_box_1514.lower j ∧ 0 ≤ branch_box_1514.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1514, Box.profileLo, Box.profileHi, box_1514]
theorem leaf_1514_BranchSafe : CertificateConsequences.BranchSafe branch_box_1514 := by
  left; refine ⟨branch_box_1514_nonnegative, ?_⟩
  intro z hz; exact leaf_1514_sound hz

theorem leaf_1520_ok : checkAt 527 1000 box_1520 cert_1520 = true := by
  have h := List.all_eq_true.mp batch_30_11_ok accepted_1520 (by simp [batch_30_11_values])
  exact h
theorem leaf_1520_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1520.profileLo box_1520.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1520_ok
theorem branch_box_1520_nonnegative : ∀ j, 0 ≤ branch_box_1520.lower j ∧ 0 ≤ branch_box_1520.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1520, Box.profileLo, Box.profileHi, box_1520]
theorem leaf_1520_BranchSafe : CertificateConsequences.BranchSafe branch_box_1520 := by
  left; refine ⟨branch_box_1520_nonnegative, ?_⟩
  intro z hz; exact leaf_1520_sound hz

theorem leaf_1521_ok : checkAt 527 1000 box_1521 cert_1521 = true := by
  have h := List.all_eq_true.mp batch_30_12_ok accepted_1521 (by simp [batch_30_12_values])
  exact h
theorem leaf_1521_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1521.profileLo box_1521.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1521_ok
theorem branch_box_1521_nonnegative : ∀ j, 0 ≤ branch_box_1521.lower j ∧ 0 ≤ branch_box_1521.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1521, Box.profileLo, Box.profileHi, box_1521]
theorem leaf_1521_BranchSafe : CertificateConsequences.BranchSafe branch_box_1521 := by
  left; refine ⟨branch_box_1521_nonnegative, ?_⟩
  intro z hz; exact leaf_1521_sound hz

theorem leaf_1522_ok : checkAt 527 1000 box_1522 cert_1522 = true := by
  have h := List.all_eq_true.mp batch_30_13_ok accepted_1522 (by simp [batch_30_13_values])
  exact h
theorem leaf_1522_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1522.profileLo box_1522.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1522_ok
theorem branch_box_1522_nonnegative : ∀ j, 0 ≤ branch_box_1522.lower j ∧ 0 ≤ branch_box_1522.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1522, Box.profileLo, Box.profileHi, box_1522]
theorem leaf_1522_BranchSafe : CertificateConsequences.BranchSafe branch_box_1522 := by
  left; refine ⟨branch_box_1522_nonnegative, ?_⟩
  intro z hz; exact leaf_1522_sound hz

theorem leaf_1526_ok : checkAt 527 1000 box_1526 cert_1526 = true := by
  have h := List.all_eq_true.mp batch_30_14_ok accepted_1526 (by simp [batch_30_14_values])
  exact h
theorem leaf_1526_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1526.profileLo box_1526.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1526_ok
theorem branch_box_1526_nonnegative : ∀ j, 0 ≤ branch_box_1526.lower j ∧ 0 ≤ branch_box_1526.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1526, Box.profileLo, Box.profileHi, box_1526]
theorem leaf_1526_BranchSafe : CertificateConsequences.BranchSafe branch_box_1526 := by
  left; refine ⟨branch_box_1526_nonnegative, ?_⟩
  intro z hz; exact leaf_1526_sound hz

theorem leaf_1527_ok : checkAt 527 1000 box_1527 cert_1527 = true := by
  have h := List.all_eq_true.mp batch_30_15_ok accepted_1527 (by simp [batch_30_15_values])
  exact h
theorem leaf_1527_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1527.profileLo box_1527.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1527_ok
theorem branch_box_1527_nonnegative : ∀ j, 0 ≤ branch_box_1527.lower j ∧ 0 ≤ branch_box_1527.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1527, Box.profileLo, Box.profileHi, box_1527]
theorem leaf_1527_BranchSafe : CertificateConsequences.BranchSafe branch_box_1527 := by
  left; refine ⟨branch_box_1527_nonnegative, ?_⟩
  intro z hz; exact leaf_1527_sound hz

theorem leaf_1529_ok : checkAt 527 1000 box_1529 cert_1529 = true := by
  have h := List.all_eq_true.mp batch_30_16_ok accepted_1529 (by simp [batch_30_16_values])
  exact h
theorem leaf_1529_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1529.profileLo box_1529.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1529_ok
theorem branch_box_1529_nonnegative : ∀ j, 0 ≤ branch_box_1529.lower j ∧ 0 ≤ branch_box_1529.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1529, Box.profileLo, Box.profileHi, box_1529]
theorem leaf_1529_BranchSafe : CertificateConsequences.BranchSafe branch_box_1529 := by
  left; refine ⟨branch_box_1529_nonnegative, ?_⟩
  intro z hz; exact leaf_1529_sound hz

theorem leaf_1530_ok : checkAt 527 1000 box_1530 cert_1530 = true := by
  have h := List.all_eq_true.mp batch_30_17_ok accepted_1530 (by simp [batch_30_17_values])
  exact h
theorem leaf_1530_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1530.profileLo box_1530.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1530_ok
theorem branch_box_1530_nonnegative : ∀ j, 0 ≤ branch_box_1530.lower j ∧ 0 ≤ branch_box_1530.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1530, Box.profileLo, Box.profileHi, box_1530]
theorem leaf_1530_BranchSafe : CertificateConsequences.BranchSafe branch_box_1530 := by
  left; refine ⟨branch_box_1530_nonnegative, ?_⟩
  intro z hz; exact leaf_1530_sound hz

theorem leaf_1531_ok : checkAt 527 1000 box_1531 cert_1531 = true := by
  have h := List.all_eq_true.mp batch_30_18_ok accepted_1531 (by simp [batch_30_18_values])
  exact h
theorem leaf_1531_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1531.profileLo box_1531.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1531_ok
theorem branch_box_1531_nonnegative : ∀ j, 0 ≤ branch_box_1531.lower j ∧ 0 ≤ branch_box_1531.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1531, Box.profileLo, Box.profileHi, box_1531]
theorem leaf_1531_BranchSafe : CertificateConsequences.BranchSafe branch_box_1531 := by
  left; refine ⟨branch_box_1531_nonnegative, ?_⟩
  intro z hz; exact leaf_1531_sound hz

theorem leaf_1532_ok : checkAt 527 1000 box_1532 cert_1532 = true := by
  have h := List.all_eq_true.mp batch_30_19_ok accepted_1532 (by simp [batch_30_19_values])
  exact h
theorem leaf_1532_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1532.profileLo box_1532.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1532_ok
theorem branch_box_1532_nonnegative : ∀ j, 0 ≤ branch_box_1532.lower j ∧ 0 ≤ branch_box_1532.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1532, Box.profileLo, Box.profileHi, box_1532]
theorem leaf_1532_BranchSafe : CertificateConsequences.BranchSafe branch_box_1532 := by
  left; refine ⟨branch_box_1532_nonnegative, ?_⟩
  intro z hz; exact leaf_1532_sound hz

theorem leaf_1535_ok : checkAt 527 1000 box_1535 cert_1535 = true := by
  have h := List.all_eq_true.mp batch_30_20_ok accepted_1535 (by simp [batch_30_20_values])
  exact h
theorem leaf_1535_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1535.profileLo box_1535.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1535_ok
theorem branch_box_1535_nonnegative : ∀ j, 0 ≤ branch_box_1535.lower j ∧ 0 ≤ branch_box_1535.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1535, Box.profileLo, Box.profileHi, box_1535]
theorem leaf_1535_BranchSafe : CertificateConsequences.BranchSafe branch_box_1535 := by
  left; refine ⟨branch_box_1535_nonnegative, ?_⟩
  intro z hz; exact leaf_1535_sound hz

theorem leaf_1538_ok : checkAt 527 1000 box_1538 cert_1538 = true := by
  have h := List.all_eq_true.mp batch_30_21_ok accepted_1538 (by simp [batch_30_21_values])
  exact h
theorem leaf_1538_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1538.profileLo box_1538.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1538_ok
theorem branch_box_1538_nonnegative : ∀ j, 0 ≤ branch_box_1538.lower j ∧ 0 ≤ branch_box_1538.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1538, Box.profileLo, Box.profileHi, box_1538]
theorem leaf_1538_BranchSafe : CertificateConsequences.BranchSafe branch_box_1538 := by
  left; refine ⟨branch_box_1538_nonnegative, ?_⟩
  intro z hz; exact leaf_1538_sound hz

theorem leaf_1541_ok : checkAt 527 1000 box_1541 cert_1541 = true := by
  have h := List.all_eq_true.mp batch_30_22_ok accepted_1541 (by simp [batch_30_22_values])
  exact h
theorem leaf_1541_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1541.profileLo box_1541.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1541_ok
theorem branch_box_1541_nonnegative : ∀ j, 0 ≤ branch_box_1541.lower j ∧ 0 ≤ branch_box_1541.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1541, Box.profileLo, Box.profileHi, box_1541]
theorem leaf_1541_BranchSafe : CertificateConsequences.BranchSafe branch_box_1541 := by
  left; refine ⟨branch_box_1541_nonnegative, ?_⟩
  intro z hz; exact leaf_1541_sound hz

theorem leaf_1542_ok : checkAt 527 1000 box_1542 cert_1542 = true := by
  have h := List.all_eq_true.mp batch_30_23_ok accepted_1542 (by simp [batch_30_23_values])
  exact h
theorem leaf_1542_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1542.profileLo box_1542.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1542_ok
theorem branch_box_1542_nonnegative : ∀ j, 0 ≤ branch_box_1542.lower j ∧ 0 ≤ branch_box_1542.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1542, Box.profileLo, Box.profileHi, box_1542]
theorem leaf_1542_BranchSafe : CertificateConsequences.BranchSafe branch_box_1542 := by
  left; refine ⟨branch_box_1542_nonnegative, ?_⟩
  intro z hz; exact leaf_1542_sound hz

theorem leaf_1543_ok : checkAt 527 1000 box_1543 cert_1543 = true := by
  have h := List.all_eq_true.mp batch_30_24_ok accepted_1543 (by simp [batch_30_24_values])
  exact h
theorem leaf_1543_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1543.profileLo box_1543.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1543_ok
theorem branch_box_1543_nonnegative : ∀ j, 0 ≤ branch_box_1543.lower j ∧ 0 ≤ branch_box_1543.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1543, Box.profileLo, Box.profileHi, box_1543]
theorem leaf_1543_BranchSafe : CertificateConsequences.BranchSafe branch_box_1543 := by
  left; refine ⟨branch_box_1543_nonnegative, ?_⟩
  intro z hz; exact leaf_1543_sound hz

theorem leaf_1544_ok : checkAt 527 1000 box_1544 cert_1544 = true := by
  have h := List.all_eq_true.mp batch_30_25_ok accepted_1544 (by simp [batch_30_25_values])
  exact h
theorem leaf_1544_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1544.profileLo box_1544.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1544_ok
theorem branch_box_1544_nonnegative : ∀ j, 0 ≤ branch_box_1544.lower j ∧ 0 ≤ branch_box_1544.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1544, Box.profileLo, Box.profileHi, box_1544]
theorem leaf_1544_BranchSafe : CertificateConsequences.BranchSafe branch_box_1544 := by
  left; refine ⟨branch_box_1544_nonnegative, ?_⟩
  intro z hz; exact leaf_1544_sound hz

theorem leaf_1548_ok : checkAt 527 1000 box_1548 cert_1548 = true := by
  have h := List.all_eq_true.mp batch_30_26_ok accepted_1548 (by simp [batch_30_26_values])
  exact h
theorem leaf_1548_sound {z : LPModel.LPVector}
    (hz : DualLeaf.LeafFeasible box_1548.profileLo box_1548.profileHi z) :
    z LPModel.tVar ≤ (527 : ℚ) / 1000 :=
  scaled_checkAt_sound hz leaf_1548_ok
theorem branch_box_1548_nonnegative : ∀ j, 0 ≤ branch_box_1548.lower j ∧ 0 ≤ branch_box_1548.upper j := by
  intro j; fin_cases j <;> norm_num [branch_box_1548, Box.profileLo, Box.profileHi, box_1548]
theorem leaf_1548_BranchSafe : CertificateConsequences.BranchSafe branch_box_1548 := by
  left; refine ⟨branch_box_1548_nonnegative, ?_⟩
  intro z hz; exact leaf_1548_sound hz

#print axioms batch_30_00_ok
#print axioms leaf_1501_sound
end PeaceableQueens.UpperBound.Generated.Even.C527
