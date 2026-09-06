import PeaceableQueens.UpperBound.FiniteLattice

/-!
# Independent-coordinate corner maximization

For a cut with no diagonal terms, a coordinate can be rounded to an endpoint
according to the sign of its affine slope.  If a finite set of coordinates has
no bilinear terms between any two of its members, that sign is unchanged by
rounding the other members.  Thus all of those coordinates can be selected at
once after the complementary coordinates have been fixed.

The executable object below is a list of updates. Executable callers supply
that list directly; `S.toList` is used only in the proof-facing corollaries
because Finset-to-list conversion is noncomputable in this development.
-/

namespace PeaceableQueens.UpperBound.IndependentCornerMax

open FiniteLattice

/-- `S` is an independent set for the directed bilinear coefficient matrix.
Both directions are required because `Cut.eval` stores an ordered double sum. -/
def IndependentOn {n : Nat} (cut : Cut n) (S : Finset (Fin n)) : Prop :=
  ∀ i j, i ∈ S → j ∈ S → cut.bilinear i j = 0

/-- The endpoint prescribed by the slope after the complementary coordinates
have been fixed.  A zero slope deliberately chooses the upper endpoint. -/
def selectedEndpoint {n : Nat} (cut : Cut n) (q : Nat) (b : Box n)
    (reference : Point n) (i : Fin n) : Int :=
  if 0 ≤ coordinateSlope cut q reference i then b.upper i else b.lower i

/-- Updating any coordinates in `xs` to their prescribed endpoints.  The
endpoint choice is always read from `reference`, not from the evolving point. -/
def roundIndependent {n : Nat} (cut : Cut n) (q : Nat) (b : Box n)
    (reference : Point n) : List (Fin n) → Point n → Point n
  | [], x => x
  | i :: xs, x =>
      roundIndependent cut q b reference xs
        (Function.update x i (selectedEndpoint cut q b reference i))

/-- Direct coordinate access avoids rebuilding a whole update sweep when the
compiler eta-expands a function-valued definition. -/
def maximizingPoint {n : Nat} (cut : Cut n) (q : Nat) (b : Box n)
    (reference : Point n) (xs : List (Fin n)) : Point n :=
  fun i => if i ∈ xs then selectedEndpoint cut q b reference i else reference i

theorem roundIndependent_apply {n : Nat} (cut : Cut n) (q : Nat) (b : Box n)
    (reference : Point n) (xs : List (Fin n)) (x : Point n) (i : Fin n) :
    roundIndependent cut q b reference xs x i =
      if i ∈ xs then selectedEndpoint cut q b reference i else x i := by
  induction xs generalizing x with
  | nil => simp [roundIndependent]
  | cons j xs ih =>
      simp only [roundIndependent, ih, List.mem_cons]
      by_cases hij : i = j
      · subst j
        simp
      · by_cases hi : i ∈ xs <;> simp [hij, hi, Function.update_apply]

theorem roundIndependent_reference_eq {n : Nat} (cut : Cut n) (q : Nat)
    (b : Box n) (reference : Point n) (xs : List (Fin n)) :
    roundIndependent cut q b reference xs reference =
      maximizingPoint cut q b reference xs := by
  funext i
  exact roundIndependent_apply cut q b reference xs reference i

/-- Inside an independent set, the coordinate slope depends only on the
coordinates outside that set.  This is the formal affine-independence fact
used by the maximizing traversal. -/
theorem coordinateSlope_eq_of_agree_outside {n : Nat} {cut : Cut n}
    {S : Finset (Fin n)} (hS : IndependentOn cut S) {q : Nat}
    {x y : Point n} {i : Fin n} (hi : i ∈ S)
    (hxy : ∀ j, j ∉ S → x j = y j) :
    coordinateSlope cut q x i = coordinateSlope cut q y i := by
  classical
  have hrow : (∑ j, cut.bilinear i j * x j) =
      ∑ j, cut.bilinear i j * y j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ S
    · rw [hS i j hi hj]
      simp
    · rw [hxy j hj]
  have hcolumn : (∑ j, cut.bilinear j i * x j) =
      ∑ j, cut.bilinear j i * y j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ S
    · rw [hS j i hj hi]
      simp
    · rw [hxy j hj]
  simp only [coordinateSlope, hrow, hcolumn]

private lemma selectedEndpoint_bounds_of_contains {n : Nat} {cut : Cut n}
    {q : Nat} {b : Box n} {reference x : Point n} (hx : b.Contains x)
    (i : Fin n) :
    b.lower i ≤ selectedEndpoint cut q b reference i ∧
      selectedEndpoint cut q b reference i ≤ b.upper i := by
  have hwell : b.lower i ≤ b.upper i := (hx i).1.trans (hx i).2
  unfold selectedEndpoint
  split
  · exact ⟨hwell, le_rfl⟩
  · exact ⟨le_rfl, hwell⟩

/-- The prescribed endpoint is nondecreasing whenever its slope agrees with
the slope at the current point. -/
private lemma selectedEndpoint_step {n : Nat} {cut : Cut n}
    (hd : NoDiagonal cut) (q : Nat) {b : Box n} {reference x : Point n}
    (hx : b.Contains x) (i : Fin n)
    (hslope : coordinateSlope cut q x i = coordinateSlope cut q reference i) :
    cut.eval q x ≤ cut.eval q
      (Function.update x i (selectedEndpoint cut q b reference i)) := by
  unfold selectedEndpoint
  split_ifs with hs
  · rw [eval_update_affine hd]
    apply le_add_of_nonneg_right
    rw [hslope]
    exact mul_nonneg (sub_nonneg.mpr (hx i).2) hs
  · rw [eval_update_affine hd]
    apply le_add_of_nonneg_right
    rw [hslope]
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hx i).1)
      (le_of_not_ge hs)

private lemma update_agrees_outside {n : Nat} {S : Finset (Fin n)}
    {x reference : Point n} {i : Fin n} {z : Int}
    (houtside : ∀ j, j ∉ S → x j = reference j) (hi : i ∈ S) :
    ∀ j, j ∉ S → Function.update x i z j = reference j := by
  intro j hj
  by_cases hji : j = i
  · subst j
    exact (hj hi).elim
  · simpa [hji] using houtside j hj

/-- A prescribed update sweep depends only on the coordinates it does not
touch.  This identifies the traversal from any admissible point with the one
started from the fixed outside-coordinate reference. -/
theorem roundIndependent_congr_outside {n : Nat} {cut : Cut n}
    (q : Nat) {b : Box n} (reference : Point n) :
    ∀ (xs : List (Fin n)) {x y : Point n},
      (∀ i, i ∉ xs → x i = y i) →
        roundIndependent cut q b reference xs x =
          roundIndependent cut q b reference xs y := by
  intro xs
  induction xs with
  | nil =>
      intro x y hxy
      have hpoint : x = y := by
        funext i
        exact hxy i (by simp)
      simpa [roundIndependent, hpoint]
  | cons i xs ih =>
      intro x y hxy
      have hupdate : ∀ j, j ∉ xs →
          Function.update x i (selectedEndpoint cut q b reference i) j =
            Function.update y i (selectedEndpoint cut q b reference i) j := by
        intro j hj
        by_cases hji : j = i
        · subst j
          simp
        · have hnot : j ∉ i :: xs := by
            intro hmem
            rcases List.mem_cons.mp hmem with hmem | hmem
            · exact hji hmem
            · exact hj hmem
          have hcoord := hxy j hnot
          simpa [hji] using hcoord
      have htail := ih hupdate
      simpa only [roundIndependent] using htail

/-- Every prescribed update over an independent coordinate set is
nondecreasing.  The initial point may be arbitrary inside the box, provided
it agrees with `reference` outside `S`. -/
theorem roundIndependent_dominates {n : Nat} {cut : Cut n}
    (hd : NoDiagonal cut) (q : Nat) {b : Box n} (S : Finset (Fin n))
    (hS : IndependentOn cut S) (reference : Point n) (xs : List (Fin n))
    (hxs : ∀ i, i ∈ xs → i ∈ S) {x : Point n} (hx : b.Contains x)
    (houtside : ∀ i, i ∉ S → x i = reference i) :
    cut.eval q x ≤ cut.eval q (roundIndependent cut q b reference xs x) := by
  induction xs generalizing x with
  | nil => simp [roundIndependent]
  | cons i xs ih =>
      have hi : i ∈ S := hxs i List.mem_cons_self
      have hslope : coordinateSlope cut q x i =
          coordinateSlope cut q reference i :=
        coordinateSlope_eq_of_agree_outside hS hi houtside
      have hstep := selectedEndpoint_step hd q hx i hslope
      have hbounds : b.lower i ≤ selectedEndpoint cut q b reference i ∧
          selectedEndpoint cut q b reference i ≤ b.upper i :=
        selectedEndpoint_bounds_of_contains hx i
      have hx' : b.Contains
          (Function.update x i (selectedEndpoint cut q b reference i)) :=
        update_contains hx i hbounds
      have houtside' : ∀ j, j ∉ S →
          Function.update x i (selectedEndpoint cut q b reference i) j =
            reference j :=
        update_agrees_outside houtside hi
          (z := selectedEndpoint cut q b reference i)
      have hxs' : ∀ j, j ∈ xs → j ∈ S := by
        intro j hj
        exact hxs j (List.mem_cons_of_mem i hj)
      have htail := ih hxs' hx' houtside'
      simpa only [roundIndependent] using hstep.trans htail

/-- A finite independent coordinate set can be maximized after all coordinates
outside it are fixed.  Taking `xs = S.toList` makes the right-hand side an
endpoint choice for every member of `S`; its endpoint signs are computed once
from `reference` and are invariant under all of the updates. -/
theorem independent_subset_dominates {n : Nat} {cut : Cut n}
    (hd : NoDiagonal cut) (q : Nat) {b : Box n} (S : Finset (Fin n))
    (hS : IndependentOn cut S) (reference : Point n) {x : Point n}
    (hx : b.Contains x)
    (houtside : ∀ i, i ∉ S → x i = reference i) :
    cut.eval q x ≤ cut.eval q
      (roundIndependent cut q b reference S.toList x) := by
  classical
  apply roundIndependent_dominates hd q S hS reference S.toList
  · intro i hi
    exact Finset.mem_toList.mp hi
  · exact hx
  · exact houtside

/-- The canonical form of `independent_subset_dominates`: after the
coordinates outside `S` have been fixed by `reference`, one endpoint point
dominates every point in the corresponding box fiber. -/
theorem independent_subset_maximizes {n : Nat} {cut : Cut n}
    (hd : NoDiagonal cut) (q : Nat) {b : Box n} (S : Finset (Fin n))
    (hS : IndependentOn cut S) (reference : Point n) {x : Point n}
    (hx : b.Contains x)
    (houtside : ∀ i, i ∉ S → x i = reference i) :
    cut.eval q x ≤ cut.eval q
      (roundIndependent cut q b reference S.toList reference) := by
  classical
  calc
    cut.eval q x ≤ cut.eval q
        (roundIndependent cut q b reference S.toList x) :=
      independent_subset_dominates hd q S hS reference hx houtside
    _ = cut.eval q (roundIndependent cut q b reference S.toList reference) := by
      exact congrArg (cut.eval q)
        (roundIndependent_congr_outside (cut := cut) (b := b) q reference
          S.toList (x := x) (y := reference) (by
            intro i hi
            exact houtside i (by simpa using hi)))

/-- Executable callers can provide an ordinary list instead of a
noncomputable `Finset.toList` conversion. Repetitions are harmless. -/
theorem independent_list_maximizes {n : Nat} {cut : Cut n}
    (hd : NoDiagonal cut) (q : Nat) {b : Box n} (xs : List (Fin n))
    (hS : IndependentOn cut xs.toFinset) (reference : Point n) {x : Point n}
    (hx : b.Contains x)
    (houtside : ∀ i, i ∉ xs → x i = reference i) :
    cut.eval q x ≤ cut.eval q
      (roundIndependent cut q b reference xs reference) := by
  have hdom := roundIndependent_dominates hd q xs.toFinset hS reference xs
    (by intro i hi; simpa using hi) hx
    (by intro i hi; exact houtside i (by simpa using hi))
  rw [roundIndependent_congr_outside (cut := cut) (b := b) q reference xs
    houtside] at hdom
  exact hdom

#print axioms independent_list_maximizes

theorem maximizingPoint_dominates {n : Nat} {cut : Cut n}
    (hd : NoDiagonal cut) (q : Nat) {b : Box n} (xs : List (Fin n))
    (hS : IndependentOn cut xs.toFinset) (reference : Point n) {x : Point n}
    (hx : b.Contains x)
    (houtside : ∀ i, i ∉ xs → x i = reference i) :
    cut.eval q x ≤ cut.eval q (maximizingPoint cut q b reference xs) := by
  rw [← roundIndependent_reference_eq]
  exact independent_list_maximizes hd q xs hS reference hx houtside

#print axioms maximizingPoint_dominates

end PeaceableQueens.UpperBound.IndependentCornerMax
