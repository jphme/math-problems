import PeaceableQueens.UpperBound.EncodedFiniteCertificate
import PeaceableQueens.UpperBound.FastCutEval
import PeaceableQueens.UpperBound.FastReducedCornerCheck
import PeaceableQueens.UpperBound.FastFiniteTables
import PeaceableQueens.UpperBound.SparseCutEval
import PeaceableQueens.UpperBound.FastIndependentCorner
import PeaceableQueens.UpperBound.IndependentCutMasks

/-!
# Isolated fast finite-certificate backend

This backend retains the established
decoder and proof-facing tables, while using direct-array coefficients,
support-reduced corners, and unrolled eight-coordinate evaluation.  Every
public Boolean is proved equal to the already checked backend before its
soundness theorem is reused.
-/

namespace PeaceableQueens.UpperBound.FastFiniteChecker

open FiniteLattice FiniteCertificates
open CachedFiniteChecker FastFiniteTables

/-- Materialize a corner point before the unrolled evaluator receives its
coordinate closure.  Keeping the array in the enclosing `let` prevents an
eta-expanded closure from rebuilding it for each read. -/
def fastCutEvalCached (cut : Cut 8) (q : Nat) (x : Point 8) : Int :=
  let point := Array.ofFn x
  FastCutEval.fastCutEval8 cut q
    (fun i => point[i.val]'(by simp [point]))

@[simp] theorem fastCutEvalCached_eq (cut : Cut 8) (q : Nat) (x : Point 8) :
    fastCutEvalCached cut q x = cut.eval q x := by
  simp [fastCutEvalCached, FastCutEval.fastCutEval8_eq_Cut_eval]

/-- Evaluate the precomputed nonzero terms at one cached corner. -/
def sparseCutEvalCached (cut : SparseCutEval.SparseCut8) (q : Nat)
    (x : Point 8) : Int :=
  let point := Array.ofFn x
  cut.eval q (fun i => point[i.val]'(by simp [point]))

@[simp] theorem sparseCutEvalCached_ofCut_eq (cut : Cut 8) (q : Nat)
    (x : Point 8) :
    sparseCutEvalCached (SparseCutEval.SparseCut8.ofCut cut) q x = cut.eval q x := by
  simp [sparseCutEvalCached, SparseCutEval.SparseCut8.eval_ofCut_eq]

/-- Fast reduced-corner checking for a single cut.  It first freezes both the
support-collapsed box and each point passed to the unrolled evaluator. -/
def fastCornerCheck (cut : Cut 8) (q : Nat) (b : Box 8)
    (threshold : Int) : Bool :=
  let sparse := SparseCutEval.SparseCut8.ofCut cut
  let supported := cachedBox
    (SupportReducedCornerCheck.supportCollapsedBox cut b)
  FastReducedCornerCheck.fastReducedForallCorners 8
    supported.lower supported.upper
    (fun point => decide (sparseCutEvalCached sparse q point ≤ threshold))

theorem fastCornerCheck_eq (cut : Cut 8) (q : Nat) (b : Box 8)
    (threshold : Int) :
    fastCornerCheck cut q b threshold = finiteCornerCheck cut q b threshold := by
  calc
    fastCornerCheck cut q b threshold =
        ReducedCornerCheck.reducedCornerCheck cut q
          (SupportReducedCornerCheck.supportCollapsedBox cut (cachedBox b)) threshold := by
      simp [fastCornerCheck, ReducedCornerCheck.reducedCornerCheck,
        FastReducedCornerCheck.fastReducedForallCorners_eq]
    _ = finiteCornerCheck cut q (cachedBox b) threshold :=
      SupportReducedCornerCheck.reducedCornerCheck_supportCollapsed_eq
        cut q (cachedBox b) threshold
    _ = finiteCornerCheck cut q b threshold := by simp

/-- Specialize all data accesses to the direct 76-cut Array table. -/
def fastModeCheck (mode : DischargeMode) (c : Fin 76) (q : Nat)
    (b : Box 8) (threshold : Int) : Bool :=
  let box := cachedBox b
  let cut := fastCuts c
  match mode with
  | .interval => decide (intervalUpper cut q box ≤ threshold)
  | .corner => FastIndependentCorner.check cut q
      (SupportReducedCornerCheck.supportCollapsedBox cut box)
      (IndependentCutMasks.coordinates c) threshold
  | .eval => decide (IsSingleton box ∧
      fastCutEvalCached cut q box.lower ≤ threshold)

theorem fastModeCheck_eq (mode : DischargeMode) (c : Fin 76) (q : Nat)
    (b : Box 8) (threshold : Int) :
    fastModeCheck mode c q b threshold =
      modeCheck cutTable mode c q b threshold := by
  cases mode with
  | interval =>
      simp [fastModeCheck, modeCheck, intervalCheck, fastCuts_eq, cutTable]
  | corner =>
      calc
        fastModeCheck .corner c q b threshold =
            FastIndependentCorner.check (fastCuts c) q
              (SupportReducedCornerCheck.supportCollapsedBox (fastCuts c) (cachedBox b))
              (IndependentCutMasks.coordinates c) threshold := rfl
        _ = finiteCornerCheck (fastCuts c) q
            (SupportReducedCornerCheck.supportCollapsedBox (fastCuts c) (cachedBox b))
            threshold :=
          FastIndependentCorner.check_eq _ _ _ _ _ (fastCutTable.noDiagonal c)
            (IndependentCutMasks.coordinates_independent c)
        _ = finiteCornerCheck (fastCuts c) q (cachedBox b) threshold :=
          SupportReducedCornerCheck.finiteCornerCheck_supportCollapsed_eq
            (fastCuts c) q (cachedBox b) threshold
        _ = finiteCornerCheck (cuts c) q b threshold := by
          simp [fastCuts_eq]
        _ = modeCheck cutTable .corner c q b threshold := rfl
  | eval =>
      simp [fastModeCheck, modeCheck, evalCheck, EvalDischarge, singletonPoint,
        fastCuts_eq, cutTable]

/-- A specialized mirror of the cached recursive checker.  Its shape is kept
separate from `CachedFiniteChecker` so benchmarking cannot affect the proof
boundary. -/
def validateNodeBoolFast (q : Nat) (threshold : Int) (b : Box 8) :
    List (Action 8 5 76) → Bool
  | [] => false
  | [.prune row ops] =>
      match cachedRunPropagation (fastDomainRows q) b ops with
      | none => false
      | some eff => decide ((fastDomainRows q row).rhs <
          endpointMin (fastDomainRows q row) eff)
  | [.discharge cut mode ops] =>
      match cachedRunPropagation (fastDomainRows q) b ops with
      | none => false
      | some eff => fastModeCheck mode cut q eff threshold
  | [.split coord mid ops left right] =>
      match cachedRunPropagation (fastDomainRows q) b ops with
      | none => false
      | some eff =>
          decide (midpoint eff coord = mid) &&
          decide (eff.lower coord < eff.upper coord) &&
          validateNodeBoolFast q threshold (cachedBox (leftChild eff coord mid)) left &&
          validateNodeBoolFast q threshold (cachedBox (rightChild eff coord mid)) right
  | _ :: _ :: _ => false

mutual
  theorem validateFastAction_eq (q : Nat) (threshold : Int) (b : Box 8)
      (action : Action 8 5 76) :
      validateNodeBoolFast q threshold b [action] =
        validateNodeBoolCached (domainRows q) cutTable q threshold b [action] := by
    cases action with
    | prune row ops =>
        simp only [validateNodeBoolFast, validateNodeBoolCached,
          cachedRunPropagation_eq, fastDomainRows_eq]
        cases h : runPropagation (domainRows q) b ops <;> simp [h]
    | discharge cut mode ops =>
        simp only [validateNodeBoolFast, validateNodeBoolCached]
        rw [fastDomainRows_eq]
        cases h : cachedRunPropagation (domainRows q) b ops <;>
          simp [h, fastModeCheck_eq]
    | split coord mid ops left right =>
        simp only [validateNodeBoolFast, validateNodeBoolCached]
        rw [fastDomainRows_eq]
        cases h : cachedRunPropagation (domainRows q) b ops with
        | none => simp [h]
        | some eff =>
            simp only [h]
            rw [validateNodeBoolFast_eq q threshold
              (cachedBox (leftChild eff coord mid)) left]
            rw [validateNodeBoolFast_eq q threshold
              (cachedBox (rightChild eff coord mid)) right]
  theorem validateNodeBoolFast_eq (q : Nat) (threshold : Int) (b : Box 8)
      (stream : List (Action 8 5 76)) :
      validateNodeBoolFast q threshold b stream =
        validateNodeBoolCached (domainRows q) cutTable q threshold b stream := by
    cases stream with
    | nil => simp only [validateNodeBoolFast, validateNodeBoolCached]
    | cons action rest =>
        cases rest with
        | nil => exact validateFastAction_eq q threshold b action
        | cons second tail => simp only [validateNodeBoolFast, validateNodeBoolCached]
end

def validateCompleteBoolFast (q : Nat) (threshold : Int) (root : Box 8)
    (stream : List (Action 8 5 76)) : Bool :=
  validateNodeBoolFast q threshold root stream

theorem validateCompleteBoolFast_eq (q : Nat) (threshold : Int) (root : Box 8)
    (stream : List (Action 8 5 76)) :
    validateCompleteBoolFast q threshold root stream =
      validateCompleteBool (domainRows q) cutTable q threshold root stream := by
  calc
    validateCompleteBoolFast q threshold root stream =
        validateNodeBoolCached (domainRows q) cutTable q threshold root stream :=
      validateNodeBoolFast_eq q threshold root stream
    _ = validateCompleteBool (domainRows q) cutTable q threshold root stream :=
      validateCompleteBoolCached_eq (domainRows q) cutTable q threshold root stream

/-- Decode with the established fail-closed parser, then validate with the
isolated fast backend. -/
def acceptedFast (q bound : Nat) (encoded : String) : Bool :=
  match EncodedFiniteCertificate.decode encoded with
  | none => false
  | some tree => validateCompleteBoolFast q (paperThreshold bound) (fullBox 8 q) [tree]

theorem acceptedFast_eq (q bound : Nat) (encoded : String) :
    acceptedFast q bound encoded = EncodedFiniteCertificate.acceptedCached q bound encoded := by
  calc
    acceptedFast q bound encoded = EncodedFiniteCertificate.accepted q bound encoded := by
      cases hdecode : EncodedFiniteCertificate.decode encoded <;>
        simp [acceptedFast, EncodedFiniteCertificate.accepted, hdecode,
          validateCompleteBoolFast_eq]
    _ = EncodedFiniteCertificate.acceptedCached q bound encoded :=
      (EncodedFiniteCertificate.acceptedCached_eq q bound encoded).symm

theorem acceptedFast_sound (q bound : Nat) (encoded : String)
    (hcheck : acceptedFast q bound encoded = true) :
    Nonempty (ActionCoverTree (Canonical q) (PrunedBy (domainRows q))
      (DischargedBy cutTable q (paperThreshold bound)) (fullBox 8 q)) :=
  EncodedFiniteCertificate.acceptedCached_sound q bound encoded
    ((acceptedFast_eq q bound encoded).symm.trans hcheck)

#print axioms acceptedFast_eq
#print axioms acceptedFast_sound

end PeaceableQueens.UpperBound.FastFiniteChecker
