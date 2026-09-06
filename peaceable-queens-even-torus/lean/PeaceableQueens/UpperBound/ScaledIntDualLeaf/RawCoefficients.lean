import PeaceableQueens.UpperBound.ScaledIntDualLeaf.ResidualScale
namespace PeaceableQueens.UpperBound.ScaledIntDualLeaf
open LPModel DualLeaf
set_option maxRecDepth 100000
set_option maxHeartbeats 0
lemma y_lt_30 (k : ProductCoord) : yVar k < 30 := by
  change 8 + k.val < 30
  omega
lemma y_not_lt_8 (k : ProductCoord) : ¬ yVar k < 8 := by
  change ¬ (8 + k.val < 8)
  norm_num
lemma y_ne_small (k : ProductCoord) (i : ProfileCoord) : yVar k ≠ xVar i := by
  exact SparseListDualLeaf.yVar_ne_xVar k i
lemma rawCoeff_y (b : Box) (r : IneqCoord) (k : ProductCoord) :
    (rawCoeff b r (yVar k) : ℚ) = ineqCoeff b.profileLo b.profileHi r (yVar k) := by
  have h0 : yVar k ≠ (0 : VarCoord) := by simpa [xVar] using y_ne_small k 0
  have h1 : yVar k ≠ (1 : VarCoord) := by simpa [xVar] using y_ne_small k 1
  have h2 : yVar k ≠ (2 : VarCoord) := by simpa [xVar] using y_ne_small k 2
  have h3 : yVar k ≠ (3 : VarCoord) := by simpa [xVar] using y_ne_small k 3
  have h4 : yVar k ≠ (4 : VarCoord) := by simpa [xVar] using y_ne_small k 4
  have h5 : yVar k ≠ (5 : VarCoord) := by simpa [xVar] using y_ne_small k 5
  have h6 : yVar k ≠ (6 : VarCoord) := by simpa [xVar] using y_ne_small k 6
  have h7 : yVar k ≠ (7 : VarCoord) := by simpa [xVar] using y_ne_small k 7
  fin_cases r <;> simp [rawCoeff, ineqCoeff, y_not_lt_8, h0, h1, h2, h3, h4, h5, h6, h7]

lemma p_not_lt_8 (a : AtomCoord) : ¬ pVar a < 8 := by
  change ¬ (30 + a.val < 8)
  omega
lemma p_ge_30 (a : AtomCoord) : 30 ≤ pVar a := by
  change 30 ≤ 30 + a.val
  omega
lemma p_lt_94 (a : AtomCoord) : pVar a < 94 := by
  change 30 + a.val < 94
  omega
lemma p_ne_small (a : AtomCoord) (i : ProfileCoord) : pVar a ≠ xVar i := by
  exact SparseListDualLeaf.pVar_ne_xVar a i
lemma rawCoeff_p (b : Box) (r : IneqCoord) (a : AtomCoord) :
    (rawCoeff b r (pVar a) : ℚ) = ineqCoeff b.profileLo b.profileHi r (pVar a) := by
  have h0 : pVar a ≠ (0 : VarCoord) := by simpa [xVar] using p_ne_small a 0
  have h1 : pVar a ≠ (1 : VarCoord) := by simpa [xVar] using p_ne_small a 1
  have h2 : pVar a ≠ (2 : VarCoord) := by simpa [xVar] using p_ne_small a 2
  have h3 : pVar a ≠ (3 : VarCoord) := by simpa [xVar] using p_ne_small a 3
  have h4 : pVar a ≠ (4 : VarCoord) := by simpa [xVar] using p_ne_small a 4
  have h5 : pVar a ≠ (5 : VarCoord) := by simpa [xVar] using p_ne_small a 5
  have h6 : pVar a ≠ (6 : VarCoord) := by simpa [xVar] using p_ne_small a 6
  have h7 : pVar a ≠ (7 : VarCoord) := by simpa [xVar] using p_ne_small a 7
  fin_cases r <;> simp [rawCoeff, ineqCoeff, p_not_lt_8, p_ge_30, p_lt_94,
    h0, h1, h2, h3, h4, h5, h6, h7]

lemma t_not_lt_8 : ¬ tVar < 8 := by
  decide
lemma t_not_range : ¬ (30 ≤ tVar ∧ tVar < 94) := by
  decide
lemma t_ne_small (i : ProfileCoord) : tVar ≠ xVar i := SparseListDualLeaf.tVar_ne_xVar i
lemma rawCoeff_t (b : Box) (r : IneqCoord) :
    (rawCoeff b r tVar : ℚ) = ineqCoeff b.profileLo b.profileHi r tVar := by
  have h0 : tVar ≠ (0 : VarCoord) := by simpa [xVar] using t_ne_small 0
  have h1 : tVar ≠ (1 : VarCoord) := by simpa [xVar] using t_ne_small 1
  have h2 : tVar ≠ (2 : VarCoord) := by simpa [xVar] using t_ne_small 2
  have h3 : tVar ≠ (3 : VarCoord) := by simpa [xVar] using t_ne_small 3
  have h4 : tVar ≠ (4 : VarCoord) := by simpa [xVar] using t_ne_small 4
  have h5 : tVar ≠ (5 : VarCoord) := by simpa [xVar] using t_ne_small 5
  have h6 : tVar ≠ (6 : VarCoord) := by simpa [xVar] using t_ne_small 6
  have h7 : tVar ≠ (7 : VarCoord) := by simpa [xVar] using t_ne_small 7
  fin_cases r <;> simp [rawCoeff, ineqCoeff, t_not_lt_8,
    h0, h1, h2, h3, h4, h5, h6, h7]
end PeaceableQueens.UpperBound.ScaledIntDualLeaf
