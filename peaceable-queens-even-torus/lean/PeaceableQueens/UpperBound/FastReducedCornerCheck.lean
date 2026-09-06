import PeaceableQueens.UpperBound.ReducedCornerCheck

/-!
# Array-friendly reduced-corner traversal

`Fin.cons` is definitionally convenient but its runtime path is expressed
through `Fin.induction`.  This implementation presents the same prepend
operation by inspecting `Fin.val` directly, then proves that its recursive
corner traversal is extensionally the established reduced traversal.
-/

namespace PeaceableQueens.UpperBound.FastReducedCornerCheck

open FiniteLattice ReducedCornerCheck

/-- Prepend one coordinate without evaluating through `Fin.cons`.  The proof
that the tail index is in range is erased before runtime evaluation. -/
def fastPrepend {n : Nat} (head : Int) (tail : Point n) : Point (n + 1) :=
  fun i => if hzero : i.val = 0 then head
    else tail ⟨i.val - 1, by omega⟩

/-- `fastPrepend` is the ordinary finite-function prepend extensionally. -/
theorem fastPrepend_eq_Fin_cons {n : Nat} (head : Int) (tail : Point n) :
    fastPrepend head tail = Fin.cons head tail := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [fastPrepend]
  · intro j
    simp [fastPrepend]

/-- The same reduced endpoint traversal as `reducedForallCorners`, with the
runtime-friendly prepend at each recursive level. -/
def fastReducedForallCorners : ∀ (n : Nat), (lower upper : Point n) →
    (Point n → Bool) → Bool
  | 0, lower, _, p => p lower
  | n + 1, lower, upper, p =>
      let lowerTail : Point n := fun i => lower i.succ
      let upperTail : Point n := fun i => upper i.succ
      if lower 0 = upper 0 then
        fastReducedForallCorners n lowerTail upperTail
          (fun tail => p (fastPrepend (lower 0) tail))
      else
        fastReducedForallCorners n lowerTail upperTail
          (fun tail => p (fastPrepend (lower 0) tail)) &&
        fastReducedForallCorners n lowerTail upperTail
          (fun tail => p (fastPrepend (upper 0) tail))

/-- The fast traversal has exactly the Boolean result of the existing reduced
corner traversal. -/
theorem fastReducedForallCorners_eq : ∀ (n : Nat) (lower upper : Point n)
    (p : Point n → Bool),
    fastReducedForallCorners n lower upper p =
      reducedForallCorners n lower upper p := by
  intro n
  induction n with
  | zero =>
      intro lower upper p
      rfl
  | succ n ih =>
      intro lower upper p
      let lowerTail : Point n := fun i => lower i.succ
      let upperTail : Point n := fun i => upper i.succ
      change
        (if lower 0 = upper 0 then
            fastReducedForallCorners n lowerTail upperTail
              (fun tail => p (fastPrepend (lower 0) tail))
          else
            fastReducedForallCorners n lowerTail upperTail
              (fun tail => p (fastPrepend (lower 0) tail)) &&
            fastReducedForallCorners n lowerTail upperTail
              (fun tail => p (fastPrepend (upper 0) tail))) =
          (if lower 0 = upper 0 then
            reducedForallCorners n lowerTail upperTail
              (fun tail => p (Fin.cons (lower 0) tail))
          else
            reducedForallCorners n lowerTail upperTail
              (fun tail => p (Fin.cons (lower 0) tail)) &&
            reducedForallCorners n lowerTail upperTail
              (fun tail => p (Fin.cons (upper 0) tail)))
      have hprependLower :
          (fun tail : Point n => p (fastPrepend (lower 0) tail)) =
            (fun tail : Point n => p (Fin.cons (lower 0) tail)) := by
        funext tail
        rw [fastPrepend_eq_Fin_cons]
      have hprependUpper :
          (fun tail : Point n => p (fastPrepend (upper 0) tail)) =
            (fun tail : Point n => p (Fin.cons (upper 0) tail)) := by
        funext tail
        rw [fastPrepend_eq_Fin_cons]
      by_cases hfixed : lower 0 = upper 0
      · simp only [if_pos hfixed, hprependLower]
        exact ih lowerTail upperTail (fun tail => p (Fin.cons (lower 0) tail))
      · simp only [if_neg hfixed, hprependLower, hprependUpper]
        rw [ih lowerTail upperTail (fun tail => p (Fin.cons (lower 0) tail))]
        rw [ih lowerTail upperTail (fun tail => p (Fin.cons (upper 0) tail))]

/-- A drop-in expression for the reduced checker, retained separately until
benchmarking demonstrates that the alternate evaluation shape is worthwhile. -/
def fastReducedCornerCheck {n : Nat} (cut : Cut n) (q : Nat)
    (b : Box n) (threshold : Int) : Bool :=
  fastReducedForallCorners n b.lower b.upper
    (fun x => decide (cut.eval q x ≤ threshold))

theorem fastReducedCornerCheck_eq {n : Nat} (cut : Cut n) (q : Nat)
    (b : Box n) (threshold : Int) :
    fastReducedCornerCheck cut q b threshold =
      reducedCornerCheck cut q b threshold :=
  fastReducedForallCorners_eq n b.lower b.upper
    (fun x => decide (cut.eval q x ≤ threshold))

#print axioms fastReducedCornerCheck_eq

end PeaceableQueens.UpperBound.FastReducedCornerCheck
