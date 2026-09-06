import PeaceableQueens.UpperBound.ScaledIntDualLeaf.EndpointScale
namespace PeaceableQueens.UpperBound.ScaledIntDualLeaf
open LPModel DualLeaf
set_option maxRecDepth 100000
set_option maxHeartbeats 0
lemma mu_rhs_scale (b : Box) (hS : b.S ≠ 0) (l : List (IneqCoord × Int)) :
 (((l.map (fun e => (-e.2)*rhsNum b e.1)).sum : Int):ℚ)/(b.S*b.S*b.S) =
 (l.map (fun e => (-(e.2:ℚ)/b.S)*ineqRhs b.profileLo b.profileHi e.1)).sum := by
 induction l with
 | nil => simp
 | cons e es ih =>
  simp only [List.map_cons,List.sum_cons,Int.cast_add,Int.cast_mul]
  rw [add_div,ih, ← rhsNum_div b hS e.1]
  field_simp
  congr 1
  push_cast
  ring
lemma nu_rhs_scale (b : Box) (hS : b.S ≠ 0) (l : List (EqCoord × Int)) :
 (((l.map (fun e => (-e.2)*b.S*b.S*eqRhsInt e.1)).sum : Int):ℚ)/(b.S*b.S*b.S) =
 (l.map (fun e => (-(e.2:ℚ)/b.S)*eqRhs e.1)).sum := by
 induction l with
 | nil => simp
 | cons e es ih =>
  simp only [List.map_cons,List.sum_cons,Int.cast_add,Int.cast_mul]
  rw [add_div,ih,eqRhsInt_cast]
  field_simp [hS]
  congr 1
  push_cast
  ring
lemma x_sum_scale (b : Box) (c : Certificate) (hS:0<b.S) :
 ((∑ i : ProfileCoord, (neg (residual2 b c (xVar i)) * (-b.lo i) + pos (residual2 b c (xVar i))*b.hi i):Int):ℚ)/(b.S*b.S*b.S) =
 ∑ i : ProfileCoord, (negativePart (SparseListDualLeaf.residual b.profileLo b.profileHi (toSparse b c) (xVar i))*(-b.profileLo i)+positivePart (SparseListDualLeaf.residual b.profileLo b.profileHi (toSparse b c) (xVar i))*b.profileHi i) := by
 rw [Int.cast_sum, Finset.sum_div]
 apply Finset.sum_congr rfl
 intro i _
 rw [endpoint_x_scale b.S (residual2 b c (xVar i)) (b.lo i) (b.hi i) hS, residual2_div b c (xVar i) (ne_of_gt hS)]
 rw [show b.profileLo i = (b.lo i : ℚ) / b.S by rfl,
   show b.profileHi i = (b.hi i : ℚ) / b.S by rfl]
 ring
lemma y_sum_scale (b : Box) (c : Certificate) (hS:0<b.S) :
 ((∑ k : ProductCoord, (neg (residual1 b c (yVar k)) * (-productLoNum b k) + pos (residual1 b c (yVar k))*productHiNum b k):Int):ℚ)/(b.S*b.S*b.S) =
 ∑ k : ProductCoord, (negativePart (SparseListDualLeaf.residual b.profileLo b.profileHi (toSparse b c) (yVar k))*(-productLower b.profileLo k)+positivePart (SparseListDualLeaf.residual b.profileLo b.profileHi (toSparse b c) (yVar k))*productUpper b.profileHi k) := by
 rw [Int.cast_sum, Finset.sum_div]
 apply Finset.sum_congr rfl
 intro k _
 rw [endpoint_y_scale b.S (residual1 b c (yVar k)) (productLoNum b k) (productHiNum b k) hS, residual1_div_y b c k (ne_of_gt hS)]
 simp [productLoNum,productHiNum,productLower,productUpper,Box.profileLo,Box.profileHi]
 field_simp

lemma recomputedBoundNum_scale (b : Box) (c : Certificate) (hS : 0 < b.S) :
    (recomputedBoundNum b c : ℚ) / (b.S*b.S*b.S) =
      SparseListDualLeaf.recomputedBound b.profileLo b.profileHi (toSparse b c) := by
  unfold recomputedBoundNum SparseListDualLeaf.recomputedBound
  rw [Int.cast_add, Int.cast_add, Int.cast_add]
  rw [add_div, add_div, add_div, mu_rhs_scale b (ne_of_gt hS) c.mu,
    x_sum_scale b c hS, y_sum_scale b c hS, nu_rhs_scale b (ne_of_gt hS) c.nu]
  simp only [List.get_eq_getElem]
  simp only [SparseListDualLeaf.equalityWeight, SparseListDualLeaf.equalityRhs]
  simp only [List.get_eq_getElem]
  rw [Fin.sum_univ_fun_getElem (toSparse b c).mu
    (fun e => (-e.2) * ineqRhs b.profileLo b.profileHi e.1)]
  rw [Fin.sum_univ_fun_getElem (toSparse b c).nu
    (fun e => (-e.2) * eqRhs e.1)]
  simp [toSparse]
  have hmu : (c.mu.map (fun e => (-(e.2 : ℚ) / b.S) *
      ineqRhs b.profileLo b.profileHi e.1)) =
      (c.mu.map ((fun e => -(e.2 * ineqRhs b.profileLo b.profileHi e.1)) ∘
        fun e => (e.1, (e.2 : ℚ) / b.S))) := by
    apply List.map_congr_left
    intro e he
    dsimp
    ring
  rw [hmu]
  have hnu : (c.nu.map (fun e => (-(e.2 : ℚ) / b.S) * eqRhs e.1)) =
      (c.nu.map ((fun e => -(e.2 * eqRhs e.1)) ∘
        fun e => (e.1, (e.2 : ℚ) / b.S))) := by
    apply List.map_congr_left
    intro e he
    dsimp
    ring
  rw [hnu]
end PeaceableQueens.UpperBound.ScaledIntDualLeaf
