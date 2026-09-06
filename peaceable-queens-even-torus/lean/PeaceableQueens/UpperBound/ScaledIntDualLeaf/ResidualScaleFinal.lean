import PeaceableQueens.UpperBound.ScaledIntDualLeaf.RawCoefficients

namespace PeaceableQueens.UpperBound.ScaledIntDualLeaf
open LPModel DualLeaf
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma raw_mu_sum_div_y (b : Box) (hS : b.S ≠ 0)
    (l : List (IneqCoord × Int)) (k : ProductCoord) :
    (((l.map (fun e => e.2 * rawCoeff b e.1 (yVar k))).sum : Int) : ℚ) / b.S =
      (l.map (fun e => ((e.2 : ℚ) / b.S) *
        ineqCoeff b.profileLo b.profileHi e.1 (yVar k))).sum := by
  induction l with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul]
    rw [add_div, ih, rawCoeff_y]
    field_simp

lemma raw_mu_sum_div_p (b : Box) (hS : b.S ≠ 0)
    (l : List (IneqCoord × Int)) (a : AtomCoord) :
    (((l.map (fun e => e.2 * rawCoeff b e.1 (pVar a))).sum : Int) : ℚ) / b.S =
      (l.map (fun e => ((e.2 : ℚ) / b.S) *
        ineqCoeff b.profileLo b.profileHi e.1 (pVar a))).sum := by
  induction l with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul]
    rw [add_div, ih, rawCoeff_p]
    field_simp

lemma raw_mu_sum_div_t (b : Box) (hS : b.S ≠ 0)
    (l : List (IneqCoord × Int)) :
    (((l.map (fun e => e.2 * rawCoeff b e.1 tVar)).sum : Int) : ℚ) / b.S =
      (l.map (fun e => ((e.2 : ℚ) / b.S) *
        ineqCoeff b.profileLo b.profileHi e.1 tVar)).sum := by
  induction l with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul]
    rw [add_div, ih, rawCoeff_t]
    field_simp

lemma nu_sum_plain_div (b : Box) (hS : b.S ≠ 0)
    (l : List (EqCoord × Int)) (v : VarCoord) :
    (((l.map (fun e => e.2 * eqCoeffInt e.1 v)).sum : Int) : ℚ) / b.S =
      (l.map (fun e => ((e.2 : ℚ) / b.S) * eqCoeff e.1 v)).sum := by
  induction l with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul]
    rw [add_div, ih, eqCoeffInt_cast]
    field_simp

lemma residual1_div_y (b : Box) (c : Certificate) (k : ProductCoord)
    (hS : b.S ≠ 0) :
    (residual1 b c (yVar k) : ℚ) / b.S =
      SparseListDualLeaf.residual b.profileLo b.profileHi (toSparse b c) (yVar k) := by
  rw [sparse_residual_toSparse]
  change (((if yVar k = tVar then b.S else 0) +
      (c.mu.map (fun e => e.2 * rawCoeff b e.1 (yVar k))).sum +
      (c.nu.map (fun e => e.2 * eqCoeffInt e.1 (yVar k))).sum : Int) : ℚ) / b.S = _
  rw [Int.cast_add, Int.cast_add, add_div, add_div,
    raw_mu_sum_div_y b hS, nu_sum_plain_div b hS]
  have hyt : yVar k ≠ tVar := ne_comm.mp (SparseListDualLeaf.tVar_ne_yVar k)
  simp [hyt, DualLeaf.objective]

lemma residual1_div_p (b : Box) (c : Certificate) (a : AtomCoord)
    (hS : b.S ≠ 0) :
    (residual1 b c (pVar a) : ℚ) / b.S =
      SparseListDualLeaf.residual b.profileLo b.profileHi (toSparse b c) (pVar a) := by
  rw [sparse_residual_toSparse]
  change (((if pVar a = tVar then b.S else 0) +
      (c.mu.map (fun e => e.2 * rawCoeff b e.1 (pVar a))).sum +
      (c.nu.map (fun e => e.2 * eqCoeffInt e.1 (pVar a))).sum : Int) : ℚ) / b.S = _
  rw [Int.cast_add, Int.cast_add, add_div, add_div,
    raw_mu_sum_div_p b hS, nu_sum_plain_div b hS]
  have hpt : pVar a ≠ tVar := ne_comm.mp (SparseListDualLeaf.tVar_ne_pVar a)
  simp [hpt, DualLeaf.objective]

lemma residual1_div_t (b : Box) (c : Certificate) (hS : b.S ≠ 0) :
    (residual1 b c tVar : ℚ) / b.S =
      SparseListDualLeaf.residual b.profileLo b.profileHi (toSparse b c) tVar := by
  rw [sparse_residual_toSparse]
  change (((if tVar = tVar then b.S else 0) +
      (c.mu.map (fun e => e.2 * rawCoeff b e.1 tVar)).sum +
      (c.nu.map (fun e => e.2 * eqCoeffInt e.1 tVar)).sum : Int) : ℚ) / b.S = _
  rw [Int.cast_add, Int.cast_add, add_div, add_div,
    raw_mu_sum_div_t b hS, nu_sum_plain_div b hS]
  simp [DualLeaf.objective, hS]

end PeaceableQueens.UpperBound.ScaledIntDualLeaf
