import PeaceableQueens.UpperBound.ReducedCornerCheck

/-!
# Support-reduced finite-corner checking

A cut does not depend on every coordinate of a box.  This checker collapses
each unsupported coordinate to its lower endpoint before running the reduced
corner traversal.  The equalities below are algebraic and do not use the
multi-affine (`NoDiagonal`) assumption.
-/

namespace PeaceableQueens.UpperBound.SupportReducedCornerCheck

open FiniteLattice ReducedCornerCheck

/-- A coordinate is relevant exactly when it has a nonzero linear coefficient
or occurs on either side of a nonzero bilinear coefficient. -/
def CoordinateSupported {n : Nat} (cut : Cut n) (i : Fin n) : Prop :=
  cut.linear i ≠ 0 ∨
    (∃ j, cut.bilinear i j ≠ 0) ∨
      ∃ j, cut.bilinear j i ≠ 0

instance coordinateSupportedDecidable {n : Nat} (cut : Cut n) (i : Fin n) :
    Decidable (CoordinateSupported cut i) := by
  unfold CoordinateSupported
  infer_instance

/-- Fix every coordinate which cannot affect `cut.eval`. -/
def supportCollapsedBox {n : Nat} (cut : Cut n) (b : Box n) : Box n :=
  { lower := b.lower
    upper := fun i => if CoordinateSupported cut i then b.upper i else b.lower i }

/-- A cut has the same value at points which agree at every relevant
coordinate. -/
theorem eval_eq_of_agree_on_support {n : Nat} (cut : Cut n) (q : Nat)
    (x y : Point n)
    (hxy : ∀ i, CoordinateSupported cut i → x i = y i) :
    cut.eval q x = cut.eval q y := by
  have hlinear :
      (∑ i, cut.linear i * ((q : Int) * x i)) =
        ∑ i, cut.linear i * ((q : Int) * y i) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : CoordinateSupported cut i
    · rw [hxy i hi]
    · have hzero : cut.linear i = 0 := by
        by_contra hnonzero
        exact hi (Or.inl hnonzero)
      simp [hzero]
  have hbilinear :
      (∑ i, ∑ j, cut.bilinear i j * (x i * x j)) =
        ∑ i, ∑ j, cut.bilinear i j * (y i * y j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hi : CoordinateSupported cut i
    · by_cases hj : CoordinateSupported cut j
      · rw [hxy i hi, hxy j hj]
      · have hzero : cut.bilinear i j = 0 := by
          by_contra hnonzero
          exact hj (Or.inr (Or.inr ⟨i, hnonzero⟩))
        simp [hzero]
    · have hzero : cut.bilinear i j = 0 := by
        by_contra hnonzero
        exact hi (Or.inr (Or.inl ⟨j, hnonzero⟩))
      simp [hzero]
  unfold Cut.eval
  rw [hlinear, hbilinear]

/-- Collapsing unsupported upper endpoints does not change the value of a
corner selected by any particular Boolean mask. -/
theorem corner_eval_supportCollapsed_eq {n : Nat} (cut : Cut n) (q : Nat)
    (b : Box n) (mask : Fin n → Bool) :
    cut.eval q (cornerPoint (supportCollapsedBox cut b) mask) =
      cut.eval q (cornerPoint b mask) := by
  apply eval_eq_of_agree_on_support cut q
  intro i hi
  simp [cornerPoint, supportCollapsedBox, hi]

/-- The ordinary all-mask corner check is unchanged after support collapse. -/
theorem finiteCornerCheck_supportCollapsed_eq {n : Nat} (cut : Cut n)
    (q : Nat) (b : Box n) (threshold : Int) :
    finiteCornerCheck cut q (supportCollapsedBox cut b) threshold =
      finiteCornerCheck cut q b threshold := by
  apply bool_eq_of_true_iff
  simp only [finiteCornerCheck, decide_eq_true_eq]
  constructor
  · intro h mask
    rw [← corner_eval_supportCollapsed_eq cut q b mask]
    exact h mask
  · intro h mask
    rw [corner_eval_supportCollapsed_eq cut q b mask]
    exact h mask

/-- Combining support collapse with the distinct-corner traversal gives the
same Boolean result as the original finite-mask checker. -/
theorem reducedCornerCheck_supportCollapsed_eq {n : Nat} (cut : Cut n)
    (q : Nat) (b : Box n) (threshold : Int) :
    reducedCornerCheck cut q (supportCollapsedBox cut b) threshold =
      finiteCornerCheck cut q b threshold := by
  calc
    reducedCornerCheck cut q (supportCollapsedBox cut b) threshold =
        finiteCornerCheck cut q (supportCollapsedBox cut b) threshold :=
      reducedCornerCheck_eq_finiteCornerCheck cut q (supportCollapsedBox cut b) threshold
    _ = finiteCornerCheck cut q b threshold :=
      finiteCornerCheck_supportCollapsed_eq cut q b threshold

theorem reducedCornerCheck_supportCollapsed_eq_original {n : Nat} (cut : Cut n)
    (q : Nat) (b : Box n) (threshold : Int) :
    reducedCornerCheck cut q (supportCollapsedBox cut b) threshold =
      reducedCornerCheck cut q b threshold := by
  rw [reducedCornerCheck_supportCollapsed_eq,
    reducedCornerCheck_eq_finiteCornerCheck]

#print axioms reducedCornerCheck_supportCollapsed_eq_original

end PeaceableQueens.UpperBound.SupportReducedCornerCheck
