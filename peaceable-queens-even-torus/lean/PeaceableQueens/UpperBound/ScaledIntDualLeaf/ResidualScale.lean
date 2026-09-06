import PeaceableQueens.UpperBound.ScaledIntDualLeaf.Coefficients

namespace PeaceableQueens.UpperBound.ScaledIntDualLeaf

open LPModel DualLeaf

lemma sparse_residual_toSparse (b : Box) (c : Certificate) (v : VarCoord) :
    SparseListDualLeaf.residual b.profileLo b.profileHi (toSparse b c) v =
      DualLeaf.objective v +
        (c.mu.map (fun e => ((e.2 : ℚ) / b.S) *
          ineqCoeff b.profileLo b.profileHi e.1 v)).sum +
        (c.nu.map (fun e => ((e.2 : ℚ) / b.S) * eqCoeff e.1 v)).sum := by
  unfold SparseListDualLeaf.residual
  simp only [List.get_eq_getElem]
  rw [Fin.sum_univ_fun_getElem (toSparse b c).mu
      (fun e => e.2 * ineqCoeff b.profileLo b.profileHi e.1 v)]
  rw [Fin.sum_univ_fun_getElem (toSparse b c).nu
      (fun e => e.2 * eqCoeff e.1 v)]
  simp [toSparse, Function.comp_def]

lemma mu_sum_div (b : Box) (hS : b.S ≠ 0)
    (l : List (IneqCoord × Int)) (v : VarCoord) :
    (((l.map (fun e => e.2 * coeffNum b e.1 v)).sum : Int) : ℚ) /
        (b.S * b.S) =
      (l.map (fun e => ((e.2 : ℚ) / b.S) *
        ineqCoeff b.profileLo b.profileHi e.1 v)).sum := by
  have hSq : (b.S : ℚ) ≠ 0 := by exact_mod_cast hS
  induction l with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul]
      rw [add_div, ih]
      congr 1
      rw [← coeffNum_div b hS e.1 v]
      field_simp

lemma nu_sum_div (b : Box) (hS : b.S ≠ 0)
    (l : List (EqCoord × Int)) (v : VarCoord) :
    (((l.map (fun e => e.2 * b.S * eqCoeffInt e.1 v)).sum : Int) : ℚ) /
        (b.S * b.S) =
      (l.map (fun e => ((e.2 : ℚ) / b.S) * eqCoeff e.1 v)).sum := by
  have hSq : (b.S : ℚ) ≠ 0 := by exact_mod_cast hS
  induction l with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul]
      rw [add_div, ih, eqCoeffInt_cast]
      congr 1
      field_simp

lemma residual2_div (b : Box) (c : Certificate) (v : VarCoord) (hS : b.S ≠ 0) :
    (residual2 b c v : ℚ) / (b.S * b.S) =
      SparseListDualLeaf.residual b.profileLo b.profileHi (toSparse b c) v := by
  rw [sparse_residual_toSparse]
  change (((if v = tVar then b.S * b.S else 0) +
      (c.mu.map (fun e => e.2 * coeffNum b e.1 v)).sum +
      (c.nu.map (fun e => e.2 * b.S * eqCoeffInt e.1 v)).sum : Int) : ℚ) /
        (b.S * b.S) = _
  rw [Int.cast_add, Int.cast_add, add_div, add_div,
    mu_sum_div b hS, nu_sum_div b hS]
  by_cases hv : v = tVar <;> simp [DualLeaf.objective, hv]
  exact hS

#print axioms residual2_div

end PeaceableQueens.UpperBound.ScaledIntDualLeaf
