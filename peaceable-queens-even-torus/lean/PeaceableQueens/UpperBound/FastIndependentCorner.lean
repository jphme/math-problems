import PeaceableQueens.UpperBound.IndependentCornerCheck
import PeaceableQueens.UpperBound.FastCutEval
import PeaceableQueens.UpperBound.FastReducedCornerCheck
import PeaceableQueens.UpperBound.SparseCutEval
import PeaceableQueens.UpperBound.CachedFiniteChecker

/-!
# Cached independent-coordinate corner checking

The reference and maximizing point are each materialized once per residual
corner. Coefficient lists are prepared once per leaf, outside the traversal.
All execution-shape changes are transported to the generic equality theorem.
-/

namespace PeaceableQueens.UpperBound.FastIndependentCorner

open FiniteLattice IndependentCornerMax IndependentCornerCheck CachedFiniteChecker

def maximizingEval (cut : Cut 8) (sparse : SparseCutEval.SparseCut8) (q : Nat)
    (b : Box 8) (xs : List (Fin 8)) (reference : Point 8) : Int :=
  let ref := Array.ofFn reference
  let refPoint : Point 8 := fun i => ref[i.val]'(by simp [ref])
  let point := Array.ofFn (fun i : Fin 8 =>
    if i ∈ xs then
      if 0 ≤ FastCutEval.fastSlope8 cut q refPoint i then b.upper i else b.lower i
    else refPoint i)
  sparse.eval q (fun i => point[i.val]'(by simp [point]))

theorem maximizingEval_eq (cut : Cut 8) (q : Nat) (b : Box 8)
    (xs : List (Fin 8)) (reference : Point 8) :
    maximizingEval cut (SparseCutEval.SparseCut8.ofCut cut) q b xs reference =
      cut.eval q (maximizingPoint cut q b reference xs) := by
  simp only [maximizingEval, Array.getElem_ofFn,
    SparseCutEval.SparseCut8.eval_ofCut_eq, FastCutEval.fastSlope8_eq]
  rfl

def check (cut : Cut 8) (q : Nat) (b : Box 8) (xs : List (Fin 8))
    (threshold : Int) : Bool :=
  let box := cachedBox b
  if box.WellFormed then
    let sparse := SparseCutEval.SparseCut8.ofCut cut
    let collapsed := cachedBox (collapseIndependentBox box xs)
    FastReducedCornerCheck.fastReducedForallCorners 8 collapsed.lower collapsed.upper
      (fun reference => decide (maximizingEval cut sparse q box xs reference ≤ threshold))
  else finiteCornerCheck cut q box threshold

theorem check_eq (cut : Cut 8) (q : Nat) (b : Box 8) (xs : List (Fin 8))
    (threshold : Int) (hd : NoDiagonal cut) (hS : IndependentOn cut xs.toFinset) :
    check cut q b xs threshold = finiteCornerCheck cut q b threshold := by
  calc
    check cut q b xs threshold =
        guardedIndependentCornerCheck cut q b xs threshold := by
      simp [check, guardedIndependentCornerCheck, independentCornerCheck,
        FastReducedCornerCheck.fastReducedForallCorners_eq, maximizingEval_eq,
        collapseIndependentBox]
    _ = finiteCornerCheck cut q b threshold :=
      guardedIndependentCornerCheck_eq_finiteCornerCheck cut q b xs threshold hd hS

#print axioms check_eq

end PeaceableQueens.UpperBound.FastIndependentCorner
