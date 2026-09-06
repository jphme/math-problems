import PeaceableQueens.UpperBound.FiniteLattice

/-!
# Reduced finite-corner checking

`finiteCornerCheck` ranges over every Boolean mask.  That is convenient for
the proof boundary, but a mask bit has no effect when a box coordinate is
already fixed.  The checker below recurses over coordinates and only creates
the second branch when its two endpoints differ.

The final theorem identifies this executable traversal with the
`FiniteLattice` specification, so its optimizations preserve acceptance.
-/

namespace PeaceableQueens.UpperBound.ReducedCornerCheck

open FiniteLattice

/-- Select an endpoint at each coordinate.  This is definitionally the same
point constructor used by `FiniteLattice.cornerPoint`, but is written with
separate endpoint functions for the structural recursion below. -/
def endpointPoint {n : Nat} (lower upper : Point n)
    (mask : Fin n → Bool) : Point n :=
  fun i => if mask i then upper i else lower i

/-- A point is an endpoint selection if every coordinate is one of the two
box endpoints. -/
def EndpointSelection {n : Nat} (lower upper : Point n) (x : Point n) : Prop :=
  ∀ i, x i = lower i ∨ x i = upper i

/-- Recursively check all *distinct* endpoint points.  At a fixed coordinate
the two Boolean-mask choices coincide, so only one recursive call is needed. -/
def reducedForallCorners : ∀ (n : Nat), (lower upper : Point n) →
    (Point n → Bool) → Bool
  | 0, lower, _, p => p lower
  | n + 1, lower, upper, p =>
      let lowerTail : Point n := fun i => lower i.succ
      let upperTail : Point n := fun i => upper i.succ
      if lower 0 = upper 0 then
        reducedForallCorners n lowerTail upperTail
          (fun tail => p (Fin.cons (lower 0) tail))
      else
        reducedForallCorners n lowerTail upperTail
          (fun tail => p (Fin.cons (lower 0) tail)) &&
        reducedForallCorners n lowerTail upperTail
          (fun tail => p (Fin.cons (upper 0) tail))

/-- The reduced traversal has exactly the expected endpoint-selection
semantics.  The predicate is Boolean so this theorem can be used directly by
an executable checker. -/
theorem reducedForallCorners_correct : ∀ (n : Nat) (lower upper : Point n)
    (p : Point n → Bool),
    reducedForallCorners n lower upper p = true ↔
      ∀ x, EndpointSelection lower upper x → p x = true := by
  intro n
  induction n with
  | zero =>
      intro lower upper p
      constructor
      · intro h x _
        have hxl : x = lower := by
          funext i
          exact Fin.elim0 i
        simpa [reducedForallCorners, hxl] using h
      · intro h
        simpa [reducedForallCorners] using h lower (by
          intro i
          exact Fin.elim0 i)
  | succ n ih =>
      intro lower upper p
      let lowerTail : Point n := fun i => lower i.succ
      let upperTail : Point n := fun i => upper i.succ
      change
        (if lower 0 = upper 0 then
            reducedForallCorners n lowerTail upperTail
              (fun tail => p (Fin.cons (lower 0) tail))
          else
            reducedForallCorners n lowerTail upperTail
              (fun tail => p (Fin.cons (lower 0) tail)) &&
            reducedForallCorners n lowerTail upperTail
              (fun tail => p (Fin.cons (upper 0) tail))) = true ↔
          ∀ x, EndpointSelection lower upper x → p x = true
      by_cases hfixed : lower 0 = upper 0
      · rw [if_pos hfixed]
        constructor
        · intro h x hx
          have htail : EndpointSelection lowerTail upperTail
              (fun i => x i.succ) := by
            intro i
            exact hx i.succ
          have hrec := (ih lowerTail upperTail
            (fun tail => p (Fin.cons (lower 0) tail))).mp h
          have hvalue := hrec (fun i => x i.succ) htail
          have hhead : x 0 = lower 0 := by
            rcases hx 0 with hlow | hupp
            · exact hlow
            · exact hupp.trans hfixed.symm
          have hpoint : Fin.cons (lower 0) (fun i => x i.succ) = x := by
            funext i
            refine Fin.cases ?_ ?_ i
            · exact hhead.symm
            · intro j
              rfl
          rw [hpoint] at hvalue
          exact hvalue
        · intro hall
          apply (ih lowerTail upperTail
            (fun tail => p (Fin.cons (lower 0) tail))).mpr
          intro tail htail
          apply hall (Fin.cons (lower 0) tail)
          intro i
          refine Fin.cases ?_ ?_ i
          · exact Or.inl rfl
          · intro j
            exact htail j
      · rw [if_neg hfixed]
        simp only [Bool.and_eq_true_iff]
        constructor
        · rintro ⟨hlow, hupp⟩ x hx
          rcases hx 0 with hhead | hhead
          · have htail : EndpointSelection lowerTail upperTail
                (fun i => x i.succ) := by
              intro i
              exact hx i.succ
            have hvalue := (ih lowerTail upperTail
              (fun tail => p (Fin.cons (lower 0) tail))).mp hlow
                (fun i => x i.succ) htail
            have hpoint : Fin.cons (lower 0) (fun i => x i.succ) = x := by
              funext i
              refine Fin.cases ?_ ?_ i
              · exact hhead.symm
              · intro j
                rfl
            rw [hpoint] at hvalue
            exact hvalue
          · have htail : EndpointSelection lowerTail upperTail
                (fun i => x i.succ) := by
              intro i
              exact hx i.succ
            have hvalue := (ih lowerTail upperTail
              (fun tail => p (Fin.cons (upper 0) tail))).mp hupp
                (fun i => x i.succ) htail
            have hpoint : Fin.cons (upper 0) (fun i => x i.succ) = x := by
              funext i
              refine Fin.cases ?_ ?_ i
              · exact hhead.symm
              · intro j
                rfl
            rw [hpoint] at hvalue
            exact hvalue
        · intro hall
          constructor
          · apply (ih lowerTail upperTail
              (fun tail => p (Fin.cons (lower 0) tail))).mpr
            intro tail htail
            apply hall (Fin.cons (lower 0) tail)
            intro i
            refine Fin.cases ?_ ?_ i
            · exact Or.inl rfl
            · intro j
              exact htail j
          · apply (ih lowerTail upperTail
              (fun tail => p (Fin.cons (upper 0) tail))).mpr
            intro tail htail
            apply hall (Fin.cons (upper 0) tail)
            intro i
            refine Fin.cases ?_ ?_ i
            · exact Or.inr rfl
            · intro j
              exact htail j

/-- Boolean masks enumerate precisely the endpoint selections. -/
theorem endpointMasks_iff {n : Nat} (lower upper : Point n)
    (p : Point n → Bool) :
    (∀ mask : Fin n → Bool, p (endpointPoint lower upper mask) = true) ↔
      ∀ x, EndpointSelection lower upper x → p x = true := by
  constructor
  · intro hall x hx
    let mask : Fin n → Bool := fun i => decide (x i = upper i)
    have hpoint : endpointPoint lower upper mask = x := by
      funext i
      by_cases hi : x i = upper i
      · simp [endpointPoint, mask, hi]
      · have hlow : x i = lower i := (hx i).resolve_right hi
        simpa only [endpointPoint, mask, hi, decide_false, Bool.false_eq_true,
          if_false] using hlow.symm
    rw [← hpoint]
    exact hall mask
  · intro hall mask
    apply hall (endpointPoint lower upper mask)
    intro i
    by_cases hi : mask i
    · right
      simp [endpointPoint, hi]
    · left
      simp [endpointPoint, hi]

/-- A drop-in corner checker which omits duplicate evaluations at fixed box
coordinates. -/
def reducedCornerCheck {n : Nat} (cut : Cut n) (q : Nat)
    (b : Box n) (threshold : Int) : Bool :=
  reducedForallCorners n b.lower b.upper
    (fun x => decide (cut.eval q x ≤ threshold))

theorem reducedCornerCheck_true_iff {n : Nat} (cut : Cut n) (q : Nat)
    (b : Box n) (threshold : Int) :
    reducedCornerCheck cut q b threshold = true ↔
      finiteCornerCheck cut q b threshold = true := by
  have hselection := reducedForallCorners_correct n b.lower b.upper
    (fun x => decide (cut.eval q x ≤ threshold))
  have hmasks := endpointMasks_iff b.lower b.upper
    (fun x => decide (cut.eval q x ≤ threshold))
  have h := hselection.trans hmasks.symm
  simp only [decide_eq_true_eq] at h
  unfold reducedCornerCheck finiteCornerCheck
  rw [decide_eq_true_eq]
  exact h

theorem bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The optimized traversal is extensionally the existing finite-mask
checker, preserving the established checker as the proof boundary. -/
theorem reducedCornerCheck_eq_finiteCornerCheck {n : Nat} (cut : Cut n)
    (q : Nat) (b : Box n) (threshold : Int) :
    reducedCornerCheck cut q b threshold = finiteCornerCheck cut q b threshold :=
  bool_eq_of_true_iff (reducedCornerCheck_true_iff cut q b threshold)

#print axioms reducedCornerCheck_eq_finiteCornerCheck

end PeaceableQueens.UpperBound.ReducedCornerCheck
