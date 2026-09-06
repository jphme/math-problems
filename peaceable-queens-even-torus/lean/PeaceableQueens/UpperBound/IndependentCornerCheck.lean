import PeaceableQueens.UpperBound.ReducedCornerCheck
import PeaceableQueens.UpperBound.IndependentCornerMax

/-!
# Independent-coordinate corner checking

An independent coordinate set need not be enumerated.  The remaining
coordinates are enumerated as corners of a box in which the independent set
has been collapsed to its lower endpoints; for each such reference point,
`maximizingPoint` selects the value-maximizing original endpoints of the
independent coordinates.

The guarded checker retains `finiteCornerCheck` for malformed boxes.  This
makes its equality theorem unconditional while keeping the fast path's proof
explicit about the well-formedness needed for its domination argument.
-/

namespace PeaceableQueens.UpperBound.IndependentCornerCheck

open FiniteLattice ReducedCornerCheck IndependentCornerMax

instance {n : Nat} (b : Box n) : Decidable b.WellFormed := by
  unfold Box.WellFormed
  infer_instance

/-- Collapse coordinates in `xs` to their lower endpoint, leaving all other
coordinates unchanged. -/
def collapseIndependentBox {n : Nat} (b : Box n) (xs : List (Fin n)) : Box n :=
  { lower := b.lower
    upper := fun i => if i ∈ xs then b.lower i else b.upper i }

/-- Fix the independent coordinates of a point to the lower endpoints. -/
def collapseReference {n : Nat} (b : Box n) (xs : List (Fin n))
    (x : Point n) : Point n :=
  fun i => if i ∈ xs then b.lower i else x i

/-- Enumerate the distinct corners of the collapsed box, evaluating the
maximizing original-box point associated with each one. -/
def independentCornerCheck {n : Nat} (cut : Cut n) (q : Nat) (b : Box n)
    (xs : List (Fin n)) (threshold : Int) : Bool :=
  reducedForallCorners n b.lower (collapseIndependentBox b xs).upper
    (fun reference => decide
      (cut.eval q (maximizingPoint cut q b reference xs) ≤ threshold))

private theorem cornerPoint_endpointSelection {n : Nat} (b : Box n)
    (mask : Fin n → Bool) :
    EndpointSelection b.lower b.upper (cornerPoint b mask) := by
  intro i
  by_cases hi : mask i <;> simp [cornerPoint, hi]

private theorem collapseReference_endpointSelection {n : Nat} (b : Box n)
    (xs : List (Fin n)) {x : Point n}
    (hx : EndpointSelection b.lower b.upper x) :
    EndpointSelection b.lower (collapseIndependentBox b xs).upper
      (collapseReference b xs x) := by
  intro i
  by_cases hi : i ∈ xs
  · simp [collapseReference, collapseIndependentBox, hi]
  · simpa [collapseReference, collapseIndependentBox, hi] using hx i

private theorem collapseReference_agrees_outside {n : Nat} (b : Box n)
    (xs : List (Fin n)) (x : Point n) :
    ∀ i, i ∉ xs → collapseReference b xs x i = x i := by
  intro i hi
  simp [collapseReference, hi]

private theorem collapsed_endpoint_contains {n : Nat} {b : Box n}
    {xs : List (Fin n)} (hb : b.WellFormed) {reference : Point n}
    (href : EndpointSelection b.lower (collapseIndependentBox b xs).upper
      reference) : b.Contains reference := by
  intro i
  rcases href i with hlow | hupp
  · rw [hlow]
    exact ⟨le_rfl, hb i⟩
  · by_cases hi : i ∈ xs
    · have hvalue : reference i = b.lower i := by
        simpa [collapseIndependentBox, hi] using hupp
      rw [hvalue]
      exact ⟨le_rfl, hb i⟩
    · have hvalue : reference i = b.upper i := by
        simpa [collapseIndependentBox, hi] using hupp
      rw [hvalue]
      exact ⟨hb i, le_rfl⟩

/-- Maximization keeps every coordinate at an original-box endpoint whenever
the reference is an endpoint selection of the collapsed box. -/
private theorem maximizingPoint_endpointSelection {n : Nat} (cut : Cut n)
    (q : Nat) (b : Box n) (xs : List (Fin n)) (reference : Point n)
    (href : EndpointSelection b.lower (collapseIndependentBox b xs).upper
      reference) :
    EndpointSelection b.lower b.upper
      (maximizingPoint cut q b reference xs) := by
  intro i
  by_cases hi : i ∈ xs
  · simp only [maximizingPoint, hi, if_true]
    unfold selectedEndpoint
    split <;> simp
  · simpa [maximizingPoint, collapseIndependentBox, hi] using href i

private theorem finiteCornerCheck_endpoint_bound {n : Nat} (cut : Cut n)
    (q : Nat) (b : Box n) (threshold : Int)
    (hcheck : finiteCornerCheck cut q b threshold = true) {x : Point n}
    (hx : EndpointSelection b.lower b.upper x) :
    cut.eval q x ≤ threshold := by
  have hmasks : ∀ mask : Fin n → Bool,
      cut.eval q (cornerPoint b mask) ≤ threshold := by
    unfold finiteCornerCheck at hcheck
    exact of_decide_eq_true hcheck
  have hmaskBools : ∀ mask : Fin n → Bool,
      decide (cut.eval q (cornerPoint b mask) ≤ threshold) = true := by
    intro mask
    exact decide_eq_true_eq.mpr (hmasks mask)
  have hselections : ∀ y, EndpointSelection b.lower b.upper y →
      decide (cut.eval q y ≤ threshold) = true :=
    (endpointMasks_iff b.lower b.upper
      (fun y => decide (cut.eval q y ≤ threshold))).mp hmaskBools
  exact decide_eq_true_eq.mp (hselections x hx)

/-- The independent traversal is extensionally the established all-mask
finite corner check under the independent-set and well-formed-box hypotheses. -/
theorem independentCornerCheck_true_iff {n : Nat} (cut : Cut n) (q : Nat)
    (b : Box n) (xs : List (Fin n)) (threshold : Int) (hd : NoDiagonal cut)
    (hS : IndependentOn cut xs.toFinset) (hb : b.WellFormed) :
    independentCornerCheck cut q b xs threshold = true ↔
      finiteCornerCheck cut q b threshold = true := by
  constructor
  · intro hcheck
    have hreduced : ∀ reference,
        EndpointSelection b.lower (collapseIndependentBox b xs).upper reference →
          cut.eval q (maximizingPoint cut q b reference xs) ≤ threshold := by
      intro reference href
      have hbool := (reducedForallCorners_correct n b.lower
        (collapseIndependentBox b xs).upper
        (fun y => decide (cut.eval q (maximizingPoint cut q b y xs) ≤ threshold))).mp
          hcheck reference href
      exact decide_eq_true_eq.mp hbool
    unfold finiteCornerCheck
    rw [decide_eq_true_eq]
    intro mask
    let reference := collapseReference b xs (cornerPoint b mask)
    have hcorner : EndpointSelection b.lower b.upper (cornerPoint b mask) :=
      cornerPoint_endpointSelection b mask
    have href : EndpointSelection b.lower (collapseIndependentBox b xs).upper
        reference :=
      collapseReference_endpointSelection b xs hcorner
    have houtside : ∀ i, i ∉ xs → cornerPoint b mask i = reference i := by
      intro i hi
      symm
      exact collapseReference_agrees_outside b xs (cornerPoint b mask) i hi
    have hcorner_contains : b.Contains (cornerPoint b mask) := by
      intro i
      cases hi : mask i <;> simp [cornerPoint, hi, hb i]
    have hdom := maximizingPoint_dominates hd q xs hS reference
      hcorner_contains houtside
    exact hdom.trans (hreduced reference href)
  · intro hcheck
    apply (reducedForallCorners_correct n b.lower
      (collapseIndependentBox b xs).upper
      (fun reference => decide
        (cut.eval q (maximizingPoint cut q b reference xs) ≤ threshold))).mpr
    intro reference href
    apply decide_eq_true_eq.mpr
    apply finiteCornerCheck_endpoint_bound cut q b threshold hcheck
    exact maximizingPoint_endpointSelection cut q b xs reference href

theorem independentCornerCheck_eq_finiteCornerCheck {n : Nat} (cut : Cut n)
    (q : Nat) (b : Box n) (xs : List (Fin n)) (threshold : Int)
    (hd : NoDiagonal cut) (hS : IndependentOn cut xs.toFinset)
    (hb : b.WellFormed) :
    independentCornerCheck cut q b xs threshold =
      finiteCornerCheck cut q b threshold :=
  bool_eq_of_true_iff
    (independentCornerCheck_true_iff cut q b xs threshold hd hS hb)

/-- Use the independent traversal only on well-formed boxes; otherwise retain
the established checker exactly. -/
def guardedIndependentCornerCheck {n : Nat} (cut : Cut n) (q : Nat)
    (b : Box n) (xs : List (Fin n)) (threshold : Int) : Bool :=
  if b.WellFormed then independentCornerCheck cut q b xs threshold
  else finiteCornerCheck cut q b threshold

/-- The guarded form is unconditionally equivalent to `finiteCornerCheck`. -/
theorem guardedIndependentCornerCheck_eq_finiteCornerCheck {n : Nat}
    (cut : Cut n) (q : Nat) (b : Box n) (xs : List (Fin n))
    (threshold : Int) (hd : NoDiagonal cut)
    (hS : IndependentOn cut xs.toFinset) :
    guardedIndependentCornerCheck cut q b xs threshold =
      finiteCornerCheck cut q b threshold := by
  by_cases hb : b.WellFormed
  · unfold guardedIndependentCornerCheck
    rw [if_pos hb]
    exact independentCornerCheck_eq_finiteCornerCheck cut q b xs threshold hd hS hb
  · simp [guardedIndependentCornerCheck, hb]

#print axioms guardedIndependentCornerCheck_eq_finiteCornerCheck

end PeaceableQueens.UpperBound.IndependentCornerCheck
