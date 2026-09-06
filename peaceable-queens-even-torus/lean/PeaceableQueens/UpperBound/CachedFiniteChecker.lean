import PeaceableQueens.UpperBound.FiniteLattice
import PeaceableQueens.UpperBound.ReducedCornerCheck
import PeaceableQueens.UpperBound.SupportReducedCornerCheck

/-!
# Cached executable mirror of finite action validation

This backend is used by the checked finite certificates. Every cached
operation is proved extensionally equal to `FiniteLattice.validateCompleteBool`
or its corresponding specification operation.
The arrays cut through the function-update chains introduced by propagation
and child boxes before a cut or a corner is evaluated repeatedly.
-/

namespace PeaceableQueens.UpperBound.CachedFiniteChecker

open FiniteLattice

/-- Materialize a finite point once, then serve coordinate reads from its
array.  The proof in the index expression is erased at execution time. -/
def cachedPoint {n : Nat} (f : Point n) : Point n :=
  let arr := Array.ofFn f
  fun i => arr[i.val]'(by simp [arr])

@[simp] theorem cachedPoint_apply {n : Nat} (f : Point n) (i : Fin n) :
    cachedPoint f i = f i := by
  simp [cachedPoint]

@[simp] theorem cachedPoint_eq {n : Nat} (f : Point n) : cachedPoint f = f := by
  funext i
  exact cachedPoint_apply f i

/-- Cache both endpoint functions of a box. Keep the arrays outside the
returned coordinate lambdas: a helper returning a function can be eta-expanded
by the compiler, rebuilding its array on every coordinate access. -/
def cachedBox {n : Nat} (b : Box n) : Box n :=
  let lower := Array.ofFn b.lower
  let upper := Array.ofFn b.upper
  { lower := fun i => lower[i.val]'(by simp [lower])
    upper := fun i => upper[i.val]'(by simp [upper]) }

@[simp] theorem cachedBox_eq {n : Nat} (b : Box n) : cachedBox b = b := by
  cases b
  simp [cachedBox]

/-- Coefficient functions generated as nested `Fin.cons` chains are also
materialized once, rather than traversed for each term of each corner. -/
def cachedCut {n : Nat} (cut : Cut n) : Cut n :=
  let linear := Array.ofFn cut.linear
  let matrix := Array.ofFn (fun i => Array.ofFn (cut.bilinear i))
  { constant := cut.constant
    linear := fun i => linear[i.val]'(by simp [linear])
    bilinear := fun i j => (matrix[i.val]'(by simp [matrix]))[j.val]'(by simp [matrix]) }

@[simp] theorem cachedCut_eq {n : Nat} (cut : Cut n) : cachedCut cut = cut := by
  have hb : (cachedCut cut).bilinear = cut.bilinear := by
    funext i j
    simp [cachedCut]
  cases cut
  simp_all [cachedCut]

/-- Cache a point before the many coordinate accesses in `Cut.eval`. -/
def cachedCutEval {n : Nat} (cut : Cut n) (q : Nat) (x : Point n) : Int :=
  let point := Array.ofFn x
  cut.eval q (fun i => point[i.val]'(by simp [point]))

@[simp] theorem cachedCutEval_eq {n : Nat} (cut : Cut n) (q : Nat)
    (x : Point n) : cachedCutEval cut q x = cut.eval q x := by
  simp [cachedCutEval]

/-- Cache the propagated result before it becomes a leaf or is split. -/
def cachedRunPropagation {n m : Nat} (rows : Fin m → Row n) (b : Box n)
    (ops : List (PropOp n m)) : Option (Box n) :=
  match runPropagation rows b ops with
  | none => none
  | some eff => some (cachedBox eff)

@[simp] theorem cachedRunPropagation_eq {n m : Nat} (rows : Fin m → Row n)
    (b : Box n) (ops : List (PropOp n m)) :
    cachedRunPropagation rows b ops = runPropagation rows b ops := by
  cases h : runPropagation rows b ops <;> simp [cachedRunPropagation, h]

/-- A cache-aware `modeCheck`.  The corner branch materializes each corner
before evaluating its constant, linear, and bilinear terms. -/
def cachedModeCheck {n k : Nat} (table : CutTable n k) (mode : DischargeMode)
    (c : Fin k) (q : Nat) (b : Box n) (threshold : Int) : Bool :=
  let box := cachedBox b
  let cut := cachedCut (table.cuts c)
  match mode with
  | .interval => decide (intervalUpper cut q box ≤ threshold)
  | .corner =>
      let supported := cachedBox (SupportReducedCornerCheck.supportCollapsedBox cut box)
      ReducedCornerCheck.reducedForallCorners n supported.lower supported.upper
        (fun point => decide (cachedCutEval cut q point ≤ threshold))
  | .eval => decide (IsSingleton box ∧
      cachedCutEval cut q box.lower ≤ threshold)

@[simp] theorem cachedModeCheck_eq {n k : Nat} (table : CutTable n k)
    (mode : DischargeMode) (c : Fin k) (q : Nat) (b : Box n)
    (threshold : Int) :
    cachedModeCheck table mode c q b threshold =
      modeCheck table mode c q b threshold := by
  cases mode with
  | interval => simp [cachedModeCheck, modeCheck, intervalCheck]
  | eval => simp [cachedModeCheck, modeCheck, evalCheck, EvalDischarge, singletonPoint]
  | corner =>
    simpa only [cachedModeCheck, cachedBox_eq, cachedCut_eq, cachedCutEval_eq,
      modeCheck, ReducedCornerCheck.reducedCornerCheck] using
      SupportReducedCornerCheck.reducedCornerCheck_supportCollapsed_eq
        (table.cuts c) q b threshold

/-! The recursive equations deliberately retain the same one-action-list
discipline as `validateNodeBool`; only the operational representation of
points and boxes differs. -/
def validateNodeBoolCached {n m k : Nat}
    (rows : Fin m → Row n) (table : CutTable n k) (q : Nat) (threshold : Int)
    (b : Box n) : List (Action n m k) → Bool
  | [] => false
  | [.prune row ops] =>
      match cachedRunPropagation rows b ops with
      | none => false
      | some eff => decide ((rows row).rhs < endpointMin (rows row) eff)
  | [.discharge cut mode ops] =>
      match cachedRunPropagation rows b ops with
      | none => false
      | some eff => cachedModeCheck table mode cut q eff threshold
  | [.split coord mid ops left right] =>
      match cachedRunPropagation rows b ops with
      | none => false
      | some eff =>
          decide (midpoint eff coord = mid) &&
          decide (eff.lower coord < eff.upper coord) &&
          validateNodeBoolCached rows table q threshold
            (cachedBox (leftChild eff coord mid)) left &&
          validateNodeBoolCached rows table q threshold
            (cachedBox (rightChild eff coord mid)) right
  | _ :: _ :: _ => false

mutual
  theorem validateCachedAction_eq {n m k : Nat}
      (rows : Fin m → Row n) (table : CutTable n k) (q : Nat)
      (threshold : Int) (b : Box n) (action : Action n m k) :
      validateNodeBoolCached rows table q threshold b [action] =
        validateNodeBool rows table q threshold b [action] := by
    cases action with
    | prune row ops =>
        simp only [validateNodeBoolCached, validateNodeBool]
        rw [cachedRunPropagation_eq]
        cases h : runPropagation rows b ops <;> simp [h]
    | discharge cut mode ops =>
        simp only [validateNodeBoolCached, validateNodeBool]
        rw [cachedRunPropagation_eq]
        cases h : runPropagation rows b ops <;> simp [h]
    | split coord mid ops left right =>
        simp only [validateNodeBoolCached, validateNodeBool]
        rw [cachedRunPropagation_eq]
        cases h : runPropagation rows b ops with
        | none => simp [h]
        | some eff =>
            simp only [h, cachedBox_eq]
            rw [validateNodeBoolCached_eq rows table q threshold
              (leftChild eff coord mid) left]
            rw [validateNodeBoolCached_eq rows table q threshold
              (rightChild eff coord mid) right]
  theorem validateNodeBoolCached_eq {n m k : Nat}
      (rows : Fin m → Row n) (table : CutTable n k) (q : Nat)
      (threshold : Int) (b : Box n) (stream : List (Action n m k)) :
      validateNodeBoolCached rows table q threshold b stream =
        validateNodeBool rows table q threshold b stream := by
    cases stream with
    | nil => simp only [validateNodeBoolCached, validateNodeBool]
    | cons action rest =>
        cases rest with
        | nil => exact validateCachedAction_eq rows table q threshold b action
        | cons second tail => simp only [validateNodeBoolCached, validateNodeBool]
end

/-- The cache-aware complete checker is propositionally the established
checker, so callers may benchmark it without widening the proof boundary. -/
def validateCompleteBoolCached {n m k : Nat}
    (rows : Fin m → Row n) (table : CutTable n k) (q : Nat) (threshold : Int)
    (root : Box n) (stream : List (Action n m k)) : Bool :=
  validateNodeBoolCached rows table q threshold root stream

theorem validateCompleteBoolCached_eq {n m k : Nat}
    (rows : Fin m → Row n) (table : CutTable n k) (q : Nat) (threshold : Int)
    (root : Box n) (stream : List (Action n m k)) :
    validateCompleteBoolCached rows table q threshold root stream =
      validateCompleteBool rows table q threshold root stream :=
  validateNodeBoolCached_eq rows table q threshold root stream

#print axioms validateCompleteBoolCached_eq

end PeaceableQueens.UpperBound.CachedFiniteChecker
