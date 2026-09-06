import PeaceableQueens.UpperBound.FiniteLattice

/-!
# Unrolled eight-coordinate cut evaluation

The finite certificates use only `Cut 8`.  This optional evaluator avoids the
generic `Finset` summation path at each corner, and guards every point read by
the corresponding coefficient test.  It remains propositionally equal to the
proof-facing `Cut.eval`.
-/

namespace PeaceableQueens.UpperBound.FastCutEval

open FiniteLattice

/-- An explicitly unrolled sum over `Fin 8`.  The right-associated shape
matches repeated `Fin.sum_univ_succ` expansion. -/
@[inline] def sum8 (f : Fin 8 → Int) : Int :=
  f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + 0)))))))

theorem sum8_eq_finset_sum (f : Fin 8 → Int) :
    sum8 f = ∑ i, f i := by
  simp [sum8, Fin.sum_univ_succ]

/-- A specialized `Cut.eval` for eight coordinates.  A zero coefficient
returns before consulting its associated point coordinate(s). -/
@[inline] def fastCutEval8 (cut : Cut 8) (q : Nat) (x : Point 8) : Int :=
  cut.constant * (q : Int) * (q : Int) +
    sum8 (fun i =>
      if cut.linear i = 0 then 0 else cut.linear i * ((q : Int) * x i)) +
      sum8 (fun i => sum8 (fun j =>
        if cut.bilinear i j = 0 then 0 else cut.bilinear i j * (x i * x j)))

theorem fastCutEval8_eq_Cut_eval (cut : Cut 8) (q : Nat) (x : Point 8) :
    fastCutEval8 cut q x = cut.eval q x := by
  have hlinear :
      sum8 (fun i =>
        if cut.linear i = 0 then 0 else cut.linear i * ((q : Int) * x i)) =
        ∑ i, cut.linear i * ((q : Int) * x i) := by
    rw [sum8_eq_finset_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hzero : cut.linear i = 0 <;> simp [hzero]
  have hbilinear :
      sum8 (fun i => sum8 (fun j =>
        if cut.bilinear i j = 0 then 0 else cut.bilinear i j * (x i * x j))) =
        ∑ i, ∑ j, cut.bilinear i j * (x i * x j) := by
    rw [sum8_eq_finset_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [sum8_eq_finset_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hzero : cut.bilinear i j = 0 <;> simp [hzero]
  unfold fastCutEval8 Cut.eval
  rw [hlinear, hbilinear]

#print axioms fastCutEval8_eq_Cut_eval

/-- Unroll the affine coordinate slope, skipping zero matrix coefficients
before reading a reference coordinate. -/
@[inline] def fastSlope8 (cut : Cut 8) (q : Nat) (x : Point 8) (i : Fin 8) : Int :=
  cut.linear i * (q : Int) +
    sum8 (fun j => if cut.bilinear i j = 0 then 0 else cut.bilinear i j * x j) +
    sum8 (fun j => if cut.bilinear j i = 0 then 0 else cut.bilinear j i * x j)

theorem fastSlope8_eq (cut : Cut 8) (q : Nat) (x : Point 8) (i : Fin 8) :
    fastSlope8 cut q x i = coordinateSlope cut q x i := by
  have hr :
      sum8 (fun j => if cut.bilinear i j = 0 then 0 else cut.bilinear i j * x j) =
        ∑ j, cut.bilinear i j * x j := by
    rw [sum8_eq_finset_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : cut.bilinear i j = 0 <;> simp [h]
  have hc :
      sum8 (fun j => if cut.bilinear j i = 0 then 0 else cut.bilinear j i * x j) =
        ∑ j, cut.bilinear j i * x j := by
    rw [sum8_eq_finset_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : cut.bilinear j i = 0 <;> simp [h]
  unfold fastSlope8 coordinateSlope
  rw [hr, hc]

#print axioms fastSlope8_eq

end PeaceableQueens.UpperBound.FastCutEval
