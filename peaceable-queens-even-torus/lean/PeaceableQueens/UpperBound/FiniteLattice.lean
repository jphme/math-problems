import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Integer-box soundness for the finite range

Paper `lem:boxops` and `lem:boxsound` (S56/S57), in integer form.  The geometry
is intentionally over integer points, rather than closed rational boxes:
`[l,c]` and `[c+1,u]` then cover every lattice point with no real gap
obligation.  All arithmetic is over mathematical `Int`, so the paper's
64-bit overflow clause `lem:boxops`(vi) has no counterpart here.
-/

namespace PeaceableQueens.UpperBound.FiniteLattice

abbrev Point (n : Nat) := Fin n → Int

structure Box (n : Nat) where
  lower : Point n
  upper : Point n

def Box.WellFormed {n : Nat} (b : Box n) : Prop :=
  ∀ i, b.lower i ≤ b.upper i

def Box.Contains {n : Nat} (b : Box n) (x : Point n) : Prop :=
  ∀ i, b.lower i ≤ x i ∧ x i ≤ b.upper i

def fullBox (n q : Nat) : Box n :=
  { lower := fun _ => 0, upper := fun _ => q }

def leftChild {n : Nat} (b : Box n) (i : Fin n) (c : Int) : Box n :=
  { lower := b.lower, upper := fun j => if j = i then c else b.upper j }

def rightChild {n : Nat} (b : Box n) (i : Fin n) (c : Int) : Box n :=
  { lower := fun j => if j = i then c + 1 else b.lower j, upper := b.upper }

/-- Paper `lem:boxops`(v): the children `x_i ≤ c` and `x_i ≥ c + 1` cover every
integer point of the parent box. -/
theorem split_covers_integer {n : Nat} {b : Box n} {i : Fin n} {c : Int}
    (hc : b.lower i ≤ c ∧ c < b.upper i) (x : Point n)
    (hx : b.Contains x) :
    (leftChild b i c).Contains x ∨ (rightChild b i c).Contains x := by
  by_cases h : x i ≤ c
  · left
    intro j
    by_cases hji : j = i
    · subst j
      simp [leftChild]
      exact ⟨(hx i).1, h⟩
    · simp [leftChild, hji]
      exact hx j
  · right
    intro j
    by_cases hji : j = i
    · subst j
      have hci : c + 1 ≤ x i := by omega
      simp [rightChild]
      exact ⟨hci, (hx i).2⟩
    · simp [rightChild, hji]
      exact hx j

theorem split_children_wellFormed {n : Nat} {b : Box n} {i : Fin n} {c : Int}
    (hb : b.WellFormed) (hc : b.lower i ≤ c ∧ c < b.upper i) :
    (leftChild b i c).WellFormed ∧ (rightChild b i c).WellFormed := by
  constructor <;> intro j <;> by_cases hji : j = i <;> simp [leftChild, rightChild, hji]
  · exact hc.1
  · exact hb j
  · omega
  · exact hb j

def midpoint {n : Nat} (b : Box n) (i : Fin n) : Int :=
  (b.lower i + b.upper i) / 2

theorem midpoint_valid {n : Nat} {b : Box n} {i : Fin n}
    (hb : b.WellFormed) (hwidth : b.lower i < b.upper i) :
    b.lower i ≤ midpoint b i ∧ midpoint b i < b.upper i := by
  unfold midpoint
  constructor <;> omega

theorem split_covers_at_midpoint {n : Nat} {b : Box n} {i : Fin n}
    (hb : b.WellFormed) (hwidth : b.lower i < b.upper i) (x : Point n)
    (hx : b.Contains x) :
    (leftChild b i (midpoint b i)).Contains x ∨
      (rightChild b i (midpoint b i)).Contains x := by
  exact split_covers_integer (midpoint_valid hb hwidth) x hx

/-! ## Endpoint propagation -/

structure Row (n : Nat) where
  coeff : Point n
  rhs : Int

def dot {n : Nat} (a x : Point n) : Int := ∑ i, a i * x i

def endpointMin {n : Nat} (row : Row n) (b : Box n) : Int :=
  ∑ i, row.coeff i * (if 0 ≤ row.coeff i then b.lower i else b.upper i)

theorem endpointMin_le {n : Nat} {row : Row n} {b : Box n} {x : Point n}
    (hx : b.Contains x) : endpointMin row b ≤ dot row.coeff x := by
  unfold endpointMin dot
  apply Finset.sum_le_sum
  intro i hi
  split_ifs with ha
  · exact mul_le_mul_of_nonneg_left (hx i).1 ha
  · exact mul_le_mul_of_nonpos_left (hx i).2 (le_of_not_ge ha)

def Row.Satisfied {n : Nat} (row : Row n) (x : Point n) : Prop :=
  dot row.coeff x ≤ row.rhs

/-- Paper `lem:boxops`(i), pruning: a row whose endpoint minimum exceeds its
right-hand side excludes every point of the box. -/
theorem endpoint_prune_sound {n : Nat} {row : Row n} {b : Box n}
    (hprune : row.rhs < endpointMin row b) :
    ∀ x, b.Contains x → ¬ row.Satisfied x := by
  intro x hx hs
  exact (not_lt_of_ge hs) (lt_of_lt_of_le hprune (endpointMin_le hx))

inductive Direction
  | upper
  | lower
  deriving DecidableEq, Repr

def propagationCandidate {n : Nat} (row : Row n) (b : Box n)
    (i : Fin n) (direction : Direction) : Int :=
  match direction with
  | .upper => row.rhs - ∑ j, if j = i then 0 else
      row.coeff j * (if 0 ≤ row.coeff j then b.lower j else b.upper j)
  | .lower => (∑ j, if j = i then 0 else
      row.coeff j * (if 0 ≤ row.coeff j then b.lower j else b.upper j)) - row.rhs

def tightenUpper {n : Nat} (b : Box n) (i : Fin n) (v : Int) : Box n :=
  { lower := b.lower, upper := fun j => if j = i then v else b.upper j }

def tightenLower {n : Nat} (b : Box n) (i : Fin n) (v : Int) : Box n :=
  { lower := fun j => if j = i then v else b.lower j, upper := b.upper }

theorem propagation_upper_sound {n : Nat} {row : Row n} {b : Box n}
    {i : Fin n} (hcoeff : row.coeff i = 1)
    {x : Point n} (hx : b.Contains x) (hs : row.Satisfied x) :
    x i ≤ propagationCandidate row b i .upper := by
  unfold Row.Satisfied dot at hs
  change x i ≤ row.rhs - ∑ j, if j = i then 0 else
    row.coeff j * (if 0 ≤ row.coeff j then b.lower j else b.upper j)
  have hrest : (∑ j, if j = i then 0 else
      row.coeff j * (if 0 ≤ row.coeff j then b.lower j else b.upper j)) ≤
      ∑ j, if j = i then 0 else row.coeff j * x j := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · split_ifs with ha
      · exact mul_le_mul_of_nonneg_left (hx j).1 ha
      · exact mul_le_mul_of_nonpos_left (hx j).2 (le_of_not_ge ha)
  have hi : x i + (∑ j, if j = i then 0 else row.coeff j * x j) ≤ row.rhs := by
    have hdecomp : (∑ j, row.coeff j * x j) =
        row.coeff i * x i + ∑ j, if j = i then 0 else row.coeff j * x j := by
      classical
      calc
        (∑ j, row.coeff j * x j) =
            ∑ j, ((if j = i then row.coeff i * x i else 0) +
              (if j = i then 0 else row.coeff j * x j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hji : j = i <;> simp [hji]
        _ = (∑ j, if j = i then row.coeff i * x i else 0) +
            ∑ j, if j = i then 0 else row.coeff j * x j :=
          Finset.sum_add_distrib
        _ = row.coeff i * x i + ∑ j, if j = i then 0 else row.coeff j * x j := by
          simp
    rw [hdecomp] at hs
    simpa [hcoeff] using hs
  omega

theorem propagation_lower_sound {n : Nat} {row : Row n} {b : Box n}
    {i : Fin n} (hcoeff : row.coeff i = -1)
    {x : Point n} (hx : b.Contains x) (hs : row.Satisfied x) :
    propagationCandidate row b i .lower ≤ x i := by
  unfold Row.Satisfied dot at hs
  change (∑ j, if j = i then 0 else
    row.coeff j * (if 0 ≤ row.coeff j then b.lower j else b.upper j)) - row.rhs ≤ x i
  have hrest : (∑ j, if j = i then 0 else
      row.coeff j * (if 0 ≤ row.coeff j then b.lower j else b.upper j)) ≤
      ∑ j, if j = i then 0 else row.coeff j * x j := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · split_ifs with ha
      · exact mul_le_mul_of_nonneg_left (hx j).1 ha
      · exact mul_le_mul_of_nonpos_left (hx j).2 (le_of_not_ge ha)
  have hi : -x i + (∑ j, if j = i then 0 else row.coeff j * x j) ≤ row.rhs := by
    have hdecomp : (∑ j, row.coeff j * x j) =
        row.coeff i * x i + ∑ j, if j = i then 0 else row.coeff j * x j := by
      classical
      calc
        (∑ j, row.coeff j * x j) =
            ∑ j, ((if j = i then row.coeff i * x i else 0) +
              (if j = i then 0 else row.coeff j * x j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hji : j = i <;> simp [hji]
        _ = (∑ j, if j = i then row.coeff i * x i else 0) +
            ∑ j, if j = i then 0 else row.coeff j * x j :=
          Finset.sum_add_distrib
        _ = row.coeff i * x i + ∑ j, if j = i then 0 else row.coeff j * x j := by
          simp
    rw [hdecomp] at hs
    simpa [hcoeff] using hs
  omega

/-! A validator can accept a tightening only when it is an actual endpoint
  improvement and the row coefficient has the expected unit sign. -/
def ValidTighten {n : Nat} (row : Row n) (b : Box n)
    (i : Fin n) (direction : Direction) (bound : Int) : Prop :=
  (direction = .upper ∧ row.coeff i = 1 ∧
      bound = propagationCandidate row b i .upper ∧ b.lower i ≤ bound ∧
        bound < b.upper i) ∨
  (direction = .lower ∧ row.coeff i = -1 ∧
      bound = propagationCandidate row b i .lower ∧ b.lower i < bound ∧
        bound ≤ b.upper i)

/-- Paper `lem:boxops`(i), tightening: a unit-coefficient row implies the
propagated endpoint for every point of the box satisfying the row. -/
theorem validTighten_sound {n : Nat} {row : Row n} {b : Box n}
    {i : Fin n} {direction : Direction} {bound : Int}
    (hv : ValidTighten row b i direction bound) {x : Point n}
    (hx : b.Contains x) (hs : row.Satisfied x) :
    (direction = .upper → x i ≤ bound) ∧
    (direction = .lower → bound ≤ x i) := by
  rcases hv with h | h
  · rcases h with ⟨hd, hc, hb, _⟩
    subst direction
    constructor
    · simpa [hb] using propagation_upper_sound hc hx hs
    · intro hd'; cases hd'
  · rcases h with ⟨hd, hc, hb, _⟩
    subst direction
    constructor
    · intro hd'; cases hd'
    · simpa [hb] using propagation_lower_sound hc hx hs

def applyTighten {n : Nat} (b : Box n) (i : Fin n) (direction : Direction)
    (bound : Int) : Box n :=
  match direction with
  | .upper => tightenUpper b i bound
  | .lower => tightenLower b i bound

theorem validTighten_apply_contains {n : Nat} {row : Row n} {b : Box n}
    {i : Fin n} {direction : Direction} {bound : Int}
    (hv : ValidTighten row b i direction bound) {x : Point n}
    (hx : b.Contains x) (hs : row.Satisfied x) :
    (applyTighten b i direction bound).Contains x := by
  rcases validTighten_sound hv hx hs with ⟨hu, hl⟩
  intro j
  by_cases hji : j = i
  · subst j
    cases direction
    · simpa [applyTighten, tightenUpper] using (And.intro (hx i).1 (hu rfl))
    · simpa [applyTighten, tightenLower] using (And.intro (hl rfl) (hx i).2)
  · cases direction <;> simp [applyTighten, tightenUpper, tightenLower, hji]
    all_goals exact hx j

theorem validTighten_wellFormed {n : Nat} {row : Row n} {b : Box n}
    {i : Fin n} {direction : Direction} {bound : Int}
    (hb : b.WellFormed) (hv : ValidTighten row b i direction bound) :
    (applyTighten b i direction bound).WellFormed := by
  rcases hv with h | h
  · rcases h with ⟨hd, hc, hval, hlo, hhi⟩
    subst direction
    intro j
    by_cases hji : j = i
    · subst j
      simp [applyTighten, tightenUpper, hlo, hhi]
    · simp [applyTighten, tightenUpper, hji]
      exact hb j
  · rcases h with ⟨hd, hc, hval, hlo, hhi⟩
    subst direction
    intro j
    by_cases hji : j = i
    · subst j
      simp [applyTighten, tightenLower, hlo, hhi]
    · simp [applyTighten, tightenLower, hji]
      exact hb j

structure PropOp (n m : Nat) where
  row : Fin m
  coord : Fin n
  direction : Direction
  bound : Int

instance {n m : Nat} (rows : Fin m → Row n) (b : Box n)
    (op : PropOp n m) : Decidable
      (ValidTighten (rows op.row) b op.coord op.direction op.bound) := by
  unfold ValidTighten
  infer_instance

def runPropagation {n m : Nat} (rows : Fin m → Row n) (b : Box n) :
    List (PropOp n m) → Option (Box n)
  | [] => some b
  | op :: rest =>
      if ValidTighten (rows op.row) b op.coord op.direction op.bound then
        runPropagation rows (applyTighten b op.coord op.direction op.bound) rest
      else none

theorem runPropagation_wellFormed {n m : Nat} {rows : Fin m → Row n}
    {b b' : Box n} (hb : b.WellFormed) {ops : List (PropOp n m)}
    (hrun : runPropagation rows b ops = some b') : b'.WellFormed := by
  induction ops generalizing b b' with
  | nil => cases hrun; exact hb
  | cons op rest ih =>
      by_cases hv : ValidTighten (rows op.row) b op.coord op.direction op.bound
      · simp [runPropagation, hv] at hrun
        exact ih (validTighten_wellFormed hb hv) hrun
      · simp [runPropagation, hv] at hrun

theorem runPropagation_sound {n m : Nat} {rows : Fin m → Row n}
    {b b' : Box n} {ops : List (PropOp n m)}
    (hrun : runPropagation rows b ops = some b') :
    ∀ x, b.Contains x → (∀ r, (rows r).Satisfied x) → b'.Contains x := by
  induction ops generalizing b b' with
  | nil =>
      intro x hx _
      cases hrun
      exact hx
  | cons op rest ih =>
      intro x hx hrows
      by_cases hv : ValidTighten (rows op.row) b op.coord op.direction op.bound
      · simp [runPropagation, hv] at hrun
        apply ih hrun x
        · exact validTighten_apply_contains ‹_› hx (hrows op.row)
        · exact hrows
      · simp [runPropagation, hv] at hrun

def Box.Nonnegative {n : Nat} (b : Box n) : Prop := ∀ i, 0 ≤ b.lower i

theorem validTighten_nonnegative {n : Nat} {row : Row n} {b : Box n}
    {i : Fin n} {direction : Direction} {bound : Int}
    (hb : b.Nonnegative) (hv : ValidTighten row b i direction bound) :
    (applyTighten b i direction bound).Nonnegative := by
  rcases hv with h | h
  · rcases h with ⟨hd, hc, hval, hlo, hhi⟩
    subst direction
    intro j
    by_cases hji : j = i
    · subst j
      simpa [applyTighten, tightenUpper] using hb i
    · simp [applyTighten, tightenUpper, hji]
      exact hb j
  · rcases h with ⟨hd, hc, hval, hlo, hhi⟩
    subst direction
    intro j
    by_cases hji : j = i
    · subst j
      change 0 ≤ if i = i then bound else b.lower i
      have hif : (if i = i then bound else b.lower i) = bound := by
        split <;> simp_all
      rw [hif]
      exact (hb i).trans (le_of_lt hlo)
    · simp [applyTighten, tightenLower, hji]
      exact hb j
theorem runPropagation_nonnegative {n m : Nat} {rows : Fin m → Row n}
    {b b' : Box n} (hb : b.Nonnegative) {ops : List (PropOp n m)}
    (hrun : runPropagation rows b ops = some b') : b'.Nonnegative := by
  induction ops generalizing b b' with
  | nil => cases hrun; exact hb
  | cons op rest ih =>
      by_cases hv : ValidTighten (rows op.row) b op.coord op.direction op.bound
      · simp [runPropagation, hv] at hrun
        exact ih (validTighten_nonnegative hb hv) hrun
      · simp [runPropagation, hv] at hrun

/-! ## A concrete multi-affine interval discharge mode -/

structure Cut (n : Nat) where
  constant : Int
  linear : Point n
  bilinear : Fin n → Fin n → Int

def Cut.eval {n : Nat} (cut : Cut n) (q : Nat) (x : Point n) : Int :=
  cut.constant * (q : Int) * (q : Int) +
    (∑ i, cut.linear i * ((q : Int) * x i)) +
      ∑ i, ∑ j, cut.bilinear i j * (x i * x j)

/-- The polynomial represented by a cut on normalized rational profile
coordinates.  `Cut.eval` is its exact integer count-scale version. -/
def Cut.normalizedEval {n : Nat} (cut : Cut n) (p : Fin n → ℚ) : ℚ :=
  cut.constant + (∑ i, cut.linear i * p i) +
    ∑ i, ∑ j, cut.bilinear i j * (p i * p j)

lemma Cut.eval_eq_sq_mul_normalizedEval {n : Nat} (cut : Cut n) (q : Nat)
    (x : Point n) (hq : (q : ℚ) ≠ 0) :
    (cut.eval q x : ℚ) = (q : ℚ) ^ 2 *
      cut.normalizedEval (fun i => (x i : ℚ) / q) := by
  have hlin :
      (∑ i, (cut.linear i : ℚ) * ((q : ℚ) * (x i : ℚ))) =
        (q : ℚ) ^ 2 * ∑ i, (cut.linear i : ℚ) * ((x i : ℚ) / q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hbil :
      (∑ i, ∑ j, (cut.bilinear i j : ℚ) * ((x i : ℚ) * (x j : ℚ))) =
        (q : ℚ) ^ 2 * ∑ i, ∑ j,
          (cut.bilinear i j : ℚ) *
            (((x i : ℚ) / q) * ((x j : ℚ) / q)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  simp only [Cut.eval, Cut.normalizedEval]
  push_cast
  rw [hlin, hbil]
  ring

def bilinearUpper {n : Nat} (a : Fin n → Fin n → Int)
    (l u : Point n) (i j : Fin n) : Int :=
  if 0 ≤ a i j then a i j * (u i * u j) else a i j * (l i * l j)

def intervalUpper {n : Nat} (cut : Cut n) (q : Nat) (b : Box n) : Int :=
  cut.constant * (q : Int) * (q : Int) +
    (∑ i, if 0 ≤ cut.linear i then cut.linear i * ((q : Int) * b.upper i)
      else cut.linear i * ((q : Int) * b.lower i)) +
    ∑ i, ∑ j, bilinearUpper cut.bilinear b.lower b.upper i j

theorem mul_nonneg_of_bounds {a b l u : Int} (hl : 0 ≤ l) (ha : l ≤ a)
    (hb : 0 ≤ b) (hbu : b ≤ u) : 0 ≤ a * b := by
  exact mul_nonneg (hl.trans ha) hb

theorem product_le_upper {l₁ u₁ l₂ u₂ x₁ x₂ : Int}
    (hl₁ : 0 ≤ l₁) (hu₁ : l₁ ≤ x₁) (hx₁ : x₁ ≤ u₁)
    (hl₂ : 0 ≤ l₂) (hu₂ : l₂ ≤ x₂) (hx₂ : x₂ ≤ u₂) :
    l₁ * l₂ ≤ x₁ * x₂ ∧ x₁ * x₂ ≤ u₁ * u₂ := by
  constructor
  · calc
      l₁ * l₂ ≤ x₁ * l₂ := mul_le_mul_of_nonneg_right hu₁ hl₂
      _ ≤ x₁ * x₂ := mul_le_mul_of_nonneg_left hu₂ (by omega)
  · calc
      x₁ * x₂ ≤ u₁ * x₂ := mul_le_mul_of_nonneg_right hx₁ (by omega)
      _ ≤ u₁ * u₂ := mul_le_mul_of_nonneg_left hx₂ (by omega)

/-- Paper `lem:boxops`(iv): the term-wise interval bound dominates the cut on a
box with nonnegative lower endpoints. -/
theorem intervalUpper_sound {n : Nat} {cut : Cut n} {q : Nat} {b : Box n}
    (hbounds : ∀ i, 0 ≤ b.lower i) {x : Point n} (hx : b.Contains x) :
  cut.eval q x ≤ intervalUpper cut q b := by
  unfold Cut.eval intervalUpper bilinearUpper
  have hlin :
      (∑ i, cut.linear i * ((q : Int) * x i)) ≤
        ∑ i, if 0 ≤ cut.linear i then cut.linear i * ((q : Int) * b.upper i)
          else cut.linear i * ((q : Int) * b.lower i) := by
    apply Finset.sum_le_sum
    intro i hi
    split_ifs with ha
    · apply mul_le_mul_of_nonneg_left _ ha
      exact mul_le_mul_of_nonneg_left (hx i).2 (by omega)
    · apply mul_le_mul_of_nonpos_left _ (le_of_not_ge ha)
      exact mul_le_mul_of_nonneg_left (hx i).1 (by omega)
  have hquad :
      (∑ i, ∑ j, cut.bilinear i j * (x i * x j)) ≤
        ∑ i, ∑ j, if 0 ≤ cut.bilinear i j then
          cut.bilinear i j * (b.upper i * b.upper j) else
          cut.bilinear i j * (b.lower i * b.lower j) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with ha
    · exact mul_le_mul_of_nonneg_left
        (product_le_upper (hbounds i) (hx i).1 (hx i).2
          (hbounds j) (hx j).1 (hx j).2).2 ha
    · exact mul_le_mul_of_nonpos_left
        (product_le_upper (hbounds i) (hx i).1 (hx i).2
          (hbounds j) (hx j).1 (hx j).2).1 (le_of_not_ge ha)
  omega

def IntervalDischarge {n : Nat} (cut : Cut n) (q : Nat) (b : Box n) (threshold : Int) : Prop :=
  intervalUpper cut q b ≤ threshold

/-- Paper `lem:boxops`(iv), discharge form. -/
theorem interval_discharge_sound {n : Nat} {cut : Cut n} {q : Nat} {b : Box n}
    {threshold : Int} (hbounds : ∀ i, 0 ≤ b.lower i)
    (hd : IntervalDischarge cut q b threshold) :
    ∀ x, b.Contains x → cut.eval q x ≤ threshold := by
  intro x hx
  exact (intervalUpper_sound hbounds hx).trans hd

def IsSingleton {n : Nat} (b : Box n) : Prop := ∀ i, b.lower i = b.upper i

def singletonPoint {n : Nat} (b : Box n) : Point n := b.lower

def EvalDischarge {n : Nat} (cut : Cut n) (q : Nat) (b : Box n)
    (threshold : Int) : Prop :=
  IsSingleton b ∧ cut.eval q (singletonPoint b) ≤ threshold

instance {n : Nat} (b : Box n) : Decidable (IsSingleton b) := by
  unfold IsSingleton
  infer_instance

instance {n : Nat} (cut : Cut n) (q : Nat) (b : Box n) (threshold : Int) :
    Decidable (EvalDischarge cut q b threshold) := by
  unfold EvalDischarge
  infer_instance

theorem eval_discharge_sound {n : Nat} {cut : Cut n} {q : Nat} {b : Box n}
    {threshold : Int} (hd : EvalDischarge cut q b threshold) :
    ∀ x, b.Contains x → cut.eval q x ≤ threshold := by
  rcases hd with ⟨hsingle, heval⟩
  intro x hx
  have hpoint : x = singletonPoint b := by
    funext i
    apply le_antisymm
    · simpa [singletonPoint, ← hsingle i] using (hx i).2
    · simpa [singletonPoint] using (hx i).1
  simpa [hpoint] using heval

/-! ## Exact finite-corner discharge

The released cuts are multi-affine: their diagonal quadratic coefficients
vanish.  Rounding one coordinate at a time can therefore only increase a
cut value until an endpoint corner is reached.  This turns exhaustive corner
evaluation into a concrete, kernel-checked discharge mode. -/

def NoDiagonal {n : Nat} (cut : Cut n) : Prop :=
  ∀ i, cut.bilinear i i = 0

instance {n : Nat} (cut : Cut n) : Decidable (NoDiagonal cut) := by
  unfold NoDiagonal
  infer_instance

def cornerPoint {n : Nat} (b : Box n) (mask : Fin n → Bool) : Point n :=
  fun i => if mask i then b.upper i else b.lower i

def finiteCornerCheck {n : Nat} (cut : Cut n) (q : Nat)
    (b : Box n) (threshold : Int) : Bool :=
  decide (∀ mask : Fin n → Bool, cut.eval q (cornerPoint b mask) ≤ threshold)

/-- The exact S56/S58 threshold after multiplying every released cut by the
common denominator 12. -/
def paperThreshold (h : Nat) : Int := 12 * (h : Int) + 6

/-- Since the objective is integral, a scaled bound by `12h + 6` rounds down
to the desired bound by `h`. -/
lemma of_twelve_mul_le_paperThreshold {m h : Nat}
    (hm : 12 * (m : Int) ≤ paperThreshold h) : m ≤ h := by
  unfold paperThreshold at hm
  omega

theorem finiteCornerCheck_sound {n : Nat} {cut : Cut n} {q : Nat}
    {b : Box n} {threshold : Int}
    (h : finiteCornerCheck cut q b threshold = true) :
    ∀ mask : Fin n → Bool, cut.eval q (cornerPoint b mask) ≤ threshold := by
  unfold finiteCornerCheck at h
  exact of_decide_eq_true h

def coordinateSlope {n : Nat} (cut : Cut n) (q : Nat)
    (x : Point n) (i : Fin n) : Int :=
  cut.linear i * (q : Int) + (∑ j, cut.bilinear i j * x j) +
    (∑ j, cut.bilinear j i * x j)

lemma eval_update_affine {n : Nat} {cut : Cut n} (hd : NoDiagonal cut)
    (q : Nat) (x : Point n) (i : Fin n) (y : Int) :
    cut.eval q (Function.update x i y) = cut.eval q x +
      (y - x i) * coordinateSlope cut q x i := by
  classical
  unfold Cut.eval coordinateSlope NoDiagonal at *
  simp only [Function.update_apply]
  have hlin : (∑ k, cut.linear k * ((q : Int) * if k = i then y else x k)) =
      (∑ k, cut.linear k * ((q : Int) * x k)) +
        (y - x i) * (cut.linear i * (q : Int)) := by
    calc
      _ = ∑ k, (cut.linear k * ((q : Int) * x k) +
            if k = i then cut.linear k * ((q : Int) * y) -
              cut.linear k * ((q : Int) * x k) else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases hki : k = i <;> simp [hki] <;> ring
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp
        ring
  have hterm : ∀ k j : Fin n,
      cut.bilinear k j * ((if k = i then y else x k) *
          (if j = i then y else x j)) =
        cut.bilinear k j * (x k * x j) +
          (if k = i then
            (if j = i then 0 else cut.bilinear k j * (y * x j) -
              cut.bilinear k j * (x k * x j))
          else if j = i then
            cut.bilinear k j * (x k * y) - cut.bilinear k j * (x k * x j)
          else 0) := by
    intro k j
    by_cases hki : k = i <;> by_cases hji : j = i <;>
      simp [hki, hji, hd] <;> ring
  have hquad :
      (∑ k, ∑ j, cut.bilinear k j *
        ((if k = i then y else x k) * (if j = i then y else x j))) =
      (∑ k, ∑ j, cut.bilinear k j * (x k * x j)) +
        (y - x i) * ((∑ j, cut.bilinear i j * x j) +
          (∑ j, cut.bilinear j i * x j)) := by
    simp_rw [hterm]
    have inner (k : Fin n) :
        (∑ j, (cut.bilinear k j * (x k * x j) +
          (if k = i then (if j = i then 0 else
            cut.bilinear k j * (y * x j) - cut.bilinear k j * (x k * x j))
          else if j = i then
            cut.bilinear k j * (x k * y) - cut.bilinear k j * (x k * x j)
          else 0))) =
          (∑ j, cut.bilinear k j * (x k * x j)) +
            (∑ j, (if k = i then (if j = i then 0 else
              cut.bilinear k j * (y * x j) - cut.bilinear k j * (x k * x j))
            else if j = i then
              cut.bilinear k j * (x k * y) - cut.bilinear k j * (x k * x j)
            else 0)) := by
      exact Finset.sum_add_distrib
    simp_rw [inner]
    have outer :
        (∑ k, ((∑ j, cut.bilinear k j * (x k * x j)) +
          (∑ j, (if k = i then (if j = i then 0 else
            cut.bilinear k j * (y * x j) - cut.bilinear k j * (x k * x j))
          else if j = i then
            cut.bilinear k j * (x k * y) - cut.bilinear k j * (x k * x j)
          else 0)))) =
        (∑ k, ∑ j, cut.bilinear k j * (x k * x j)) +
          (∑ k, ∑ j, (if k = i then (if j = i then 0 else
            cut.bilinear k j * (y * x j) - cut.bilinear k j * (x k * x j))
          else if j = i then
            cut.bilinear k j * (x k * y) - cut.bilinear k j * (x k * x j)
          else 0)) := by
      exact Finset.sum_add_distrib
    rw [outer]
    have hsum (f : Fin n → Int) :
        (Finset.univ.filter (fun j : Fin n => ¬ j = i)).sum f =
          Finset.univ.sum f - f i := by
      have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
      have hsplit :
          (Finset.univ.erase i).sum f + f i = Finset.univ.sum f := by
        exact Finset.sum_erase_add (Finset.univ : Finset (Fin n)) f hi
      have heq : (Finset.univ.filter (fun j : Fin n => ¬ j = i)) =
          (Finset.univ : Finset (Fin n)).erase i := by
        ext j
        simp
      rw [heq]
      linarith
    have hsumEq (f : Fin n → Int) :
        (Finset.univ.filter (fun j : Fin n => j = i)).sum f = f i := by
      have heq : (Finset.univ.filter (fun j : Fin n => j = i)) =
          ({i} : Finset (Fin n)) := by
        ext j
        simp
      rw [heq]
      simp
    simp [Finset.sum_ite, hd, hsum, hsumEq]
    have h1 : (∑ j, cut.bilinear i j * (y * x j)) =
        y * (∑ j, cut.bilinear i j * x j) := by
      calc
        _ = ∑ j, y * (cut.bilinear i j * x j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [Finset.mul_sum]
    have h2 : (∑ j, cut.bilinear i j * (x i * x j)) =
        x i * (∑ j, cut.bilinear i j * x j) := by
      calc
        _ = ∑ j, x i * (cut.bilinear i j * x j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [Finset.mul_sum]
    have h3 : (∑ k, cut.bilinear k i * (x k * y)) =
        y * (∑ k, cut.bilinear k i * x k) := by
      calc
        _ = ∑ k, y * (cut.bilinear k i * x k) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = _ := by rw [Finset.mul_sum]
    have h4 : (∑ k, cut.bilinear k i * (x k * x i)) =
        x i * (∑ k, cut.bilinear k i * x k) := by
      calc
        _ = ∑ k, x i * (cut.bilinear k i * x k) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = _ := by rw [Finset.mul_sum]
    rw [h1, h2, h3, h4]
    ring
  rw [hlin, hquad]
  ring

lemma endpoint_round {n : Nat} {cut : Cut n} (hd : NoDiagonal cut)
    (q : Nat) {b : Box n} {x : Point n} (hx : b.Contains x) (i : Fin n) :
    ∃ z : Int, (z = b.lower i ∨ z = b.upper i) ∧
      cut.eval q x ≤ cut.eval q (Function.update x i z) := by
  by_cases hs : 0 ≤ coordinateSlope cut q x i
  · refine ⟨b.upper i, Or.inr rfl, ?_⟩
    rw [eval_update_affine hd]
    apply le_add_of_nonneg_right
    exact mul_nonneg (by have := hx i; omega) hs
  · refine ⟨b.lower i, Or.inl rfl, ?_⟩
    rw [eval_update_affine hd]
    apply le_add_of_nonneg_right
    exact mul_nonneg_of_nonpos_of_nonpos (by have := hx i; omega) (le_of_not_ge hs)

lemma update_contains {n : Nat} {b : Box n} {x : Point n}
    (hx : b.Contains x) (i : Fin n) {z : Int}
    (hz : b.lower i ≤ z ∧ z ≤ b.upper i) :
    b.Contains (Function.update x i z) := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [hz]
  · simp [hji]
    exact hx j

lemma round_coordinates {n : Nat} {cut : Cut n} (hd : NoDiagonal cut)
    (q : Nat) {b : Box n} (xs : List (Fin n))
    (hnodup : xs.Nodup) {x : Point n} (hx : b.Contains x) :
    ∃ y : Point n, b.Contains y ∧ cut.eval q x ≤ cut.eval q y ∧
      (∀ i, i ∈ xs → (y i = b.lower i ∨ y i = b.upper i)) ∧
      (∀ i, i ∉ xs → y i = x i) := by
  induction xs generalizing x with
  | nil => exact ⟨x, hx, le_rfl, by simp, by simp⟩
  | cons i rest ih =>
      have hiRest : i ∉ rest := by
        intro h
        exact (List.nodup_cons.mp hnodup).1 h
      rcases endpoint_round hd q hx i with ⟨z, hz, hstep⟩
      have hinterval : b.lower i ≤ z ∧ z ≤ b.upper i := by
        have hxi := hx i
        rcases hz with rfl | rfl <;> omega
      rcases ih (List.nodup_cons.mp hnodup).2 (update_contains hx i hinterval)
        with ⟨y, hy, hxy, hrest, hunchanged⟩
      refine ⟨y, hy, hstep.trans hxy, ?_, ?_⟩
      · intro j hj
        by_cases hji : j = i
        · subst j
          have hz' : y i = z := by
            rw [hunchanged i hiRest]
            simp
          rw [hz']
          exact hz
        · exact hrest j (List.mem_cons.mp hj |>.resolve_left hji)
      · intro j hj
        have hj' : j ∉ rest := by
          intro h
          exact hj (List.mem_cons_of_mem i h)
        rw [hunchanged j hj']
        have hji : ¬ j = i := by
          intro h
          exact hj (h ▸ List.mem_cons_self)
        simp [Function.update, hji]

/-- Paper `lem:boxops`(ii)--(iii): a multi-affine cut (no diagonal quadratic
terms) is dominated at some corner of the box. -/
theorem corner_extremum {n : Nat} {cut : Cut n} (hd : NoDiagonal cut) :
    ∀ q b x, b.Contains x →
      ∃ mask : Fin n → Bool,
        cut.eval q x ≤ cut.eval q (cornerPoint b mask) := by
  intro q b x hx
  let xs : List (Fin n) := Finset.univ.toList
  have hxs : xs.Nodup := Finset.nodup_toList Finset.univ
  rcases round_coordinates hd q xs hxs hx with ⟨y, hy, hvalue, hend, hunchanged⟩
  let mask : Fin n → Bool := fun i => decide (y i = b.upper i)
  have hpoint : y = cornerPoint b mask := by
    funext i
    have hi : i ∈ xs := Finset.mem_toList.mpr (Finset.mem_univ i)
    rcases hend i hi with hlo | hhi
    · by_cases heq : y i = b.upper i
      · simp [cornerPoint, mask, heq]
      · simp [cornerPoint, mask, heq, hlo]
    · simp [cornerPoint, mask, hhi]
  exact ⟨mask, hpoint ▸ hvalue⟩

/-- Paper `lem:boxops`(iii), discharge form: if no corner exceeds the
threshold, no point of the box does. -/
theorem corner_check_discharge {n : Nat} {cut : Cut n} {q : Nat}
    {b : Box n} {threshold : Int} (hd : NoDiagonal cut)
    (hcheck : finiteCornerCheck cut q b threshold = true) :
    ∀ x, b.Contains x → cut.eval q x ≤ threshold := by
  intro x hx
  rcases corner_extremum hd q b x hx with ⟨mask, hmax⟩
  exact hmax.trans (finiteCornerCheck_sound hcheck mask)

inductive DischargeMode
  | interval
  | corner
  | eval
  deriving DecidableEq, Repr

structure CutTable (n k : Nat) where
  cuts : Fin k → Cut n
  noDiagonal : ∀ c, NoDiagonal (cuts c)

def CornerDischarge {n k : Nat} (table : CutTable n k) (c : Fin k)
    (q : Nat) (b : Box n) (threshold : Int) : Prop :=
  ∀ x, b.Contains x → (table.cuts c).eval q x ≤ threshold

def ModeDischarge {n k : Nat} (table : CutTable n k) (mode : DischargeMode)
    (c : Fin k) (q : Nat) (b : Box n) (threshold : Int) : Prop :=
  match mode with
  | .interval => IntervalDischarge (table.cuts c) q b threshold
  | .corner => CornerDischarge table c q b threshold
  | .eval => EvalDischarge (table.cuts c) q b threshold

def DischargedBy {n k : Nat} (table : CutTable n k)
    (q : Nat) (threshold : Int) (b : Box n) : Prop :=
  ∃ c, ∀ x, b.Contains x → (table.cuts c).eval q x ≤ threshold

def intervalCheck {n k : Nat} (table : CutTable n k) (c : Fin k)
    (q : Nat) (b : Box n) (threshold : Int) : Bool :=
  decide (intervalUpper (table.cuts c) q b ≤ threshold)

def evalCheck {n k : Nat} (table : CutTable n k) (c : Fin k)
    (q : Nat) (b : Box n) (threshold : Int) : Bool :=
  decide (EvalDischarge (table.cuts c) q b threshold)

def modeCheck {n k : Nat} (table : CutTable n k) (mode : DischargeMode)
    (c : Fin k) (q : Nat) (b : Box n) (threshold : Int) : Bool :=
  match mode with
  | .interval => intervalCheck table c q b threshold
  | .corner => finiteCornerCheck (table.cuts c) q b threshold
  | .eval => evalCheck table c q b threshold

theorem modeCheck_sound {n k : Nat} (table : CutTable n k)
    {mode : DischargeMode} {c : Fin k} {q : Nat} {b : Box n} {threshold : Int}
    (hnonneg : ∀ i, 0 ≤ b.lower i)
    (hcheck : modeCheck table mode c q b threshold = true) :
    ModeDischarge table mode c q b threshold := by
  cases mode with
  | interval =>
      unfold modeCheck intervalCheck at hcheck
      change intervalUpper (table.cuts c) q b ≤ threshold
      exact of_decide_eq_true hcheck
  | corner =>
      exact corner_check_discharge (table.noDiagonal c) hcheck
  | eval =>
      unfold modeCheck evalCheck at hcheck
      change EvalDischarge (table.cuts c) q b threshold
      exact of_decide_eq_true hcheck

theorem dischargedBy_sound {n k : Nat} (table : CutTable n k)
    {q : Nat} {b : Box n} {threshold : Int}
    (hnonneg : ∀ i, 0 ≤ b.lower i)
    (hc : ∃ c, ∃ mode, modeCheck table mode c q b threshold = true) :
    DischargedBy table q threshold b := by
  rcases hc with ⟨c, mode, hcheck⟩
  refine ⟨c, ?_⟩
  have hmode := modeCheck_sound table hnonneg hcheck
  cases mode with
  | interval => exact interval_discharge_sound hnonneg hmode
  | corner => exact hmode
  | eval => exact eval_discharge_sound hmode

/-! ## Recursive, propagation-aware action stream

The ordinary `CoverTree` above is useful for already-normalized boxes.  A
search node, however, first tightens its incoming box.  `ActionCoverTree`
records that transition explicitly; its split coverage is restricted to
canonical points, which is exactly what propagation soundness permits. -/

def PrunedBy {n m : Nat} (rows : Fin m → Row n) (b : Box n) : Prop :=
  ∃ r, (rows r).rhs < endpointMin (rows r) b

inductive ActionCoverTree {n : Nat} (Canonical : Point n → Prop)
    (Pruned Discharged : Box n → Prop) : Box n → Type
  | leaf {b eff : Box n}
      (prop : ∀ x, Canonical x → b.Contains x → eff.Contains x)
      (result : Pruned eff ∨ Discharged eff) :
      ActionCoverTree Canonical Pruned Discharged b
  | split {b eff l r : Box n}
      (prop : ∀ x, Canonical x → b.Contains x → eff.Contains x)
      (part : ∀ x, Canonical x → eff.Contains x → l.Contains x ∨ r.Contains x)
      (left : ActionCoverTree Canonical Pruned Discharged l)
      (right : ActionCoverTree Canonical Pruned Discharged r) :
      ActionCoverTree Canonical Pruned Discharged b

theorem ActionCoverTree.locate {n : Nat} {Canonical : Point n → Prop}
    {Pruned Discharged : Box n → Prop} {root : Box n}
    (tree : ActionCoverTree Canonical Pruned Discharged root)
    {x : Point n} (hcanon : Canonical x) (hx : root.Contains x) :
    ∃ leaf, leaf.Contains x ∧ (Pruned leaf ∨ Discharged leaf) := by
  induction tree with
  | leaf prop result =>
      exact ⟨_, prop x hcanon hx, result⟩
  | split prop part left right ihl ihr =>
      rcases part x hcanon (prop x hcanon hx) with hl | hr
      · exact ihl hl
      · exact ihr hr

/-- Paper `lem:boxsound`, coverage part: every canonical integer point of the
root lies in a discharged terminal box, because pruned boxes contain no
canonical point. -/
theorem ActionCoverTree.canonical_discharge {n m k : Nat}
    {Canonical : Point n → Prop} {rows : Fin m → Row n}
    {table : CutTable n k} {q : Nat} {threshold : Int} {root : Box n}
    (tree : ActionCoverTree Canonical (PrunedBy rows)
      (DischargedBy table q threshold) root)
    (hrows : ∀ x, Canonical x → ∀ r, (rows r).Satisfied x)
    {x : Point n} (hcanon : Canonical x) (hx : root.Contains x) :
    ∃ leaf, leaf.Contains x ∧ DischargedBy table q threshold leaf := by
  rcases tree.locate hcanon hx with ⟨leaf, hleaf, hp | hd⟩
  · rcases hp with ⟨row, hprune⟩
    exact False.elim (endpoint_prune_sound hprune x hleaf (hrows x hcanon row))
  · exact ⟨leaf, hleaf, hd⟩

inductive Action (n m k : Nat)
  | prune (row : Fin m) (ops : List (PropOp n m))
  | discharge (cut : Fin k) (mode : DischargeMode) (ops : List (PropOp n m))
  | split (coord : Fin n) (midpoint : Int) (ops : List (PropOp n m))
      (left right : List (Action n m k))

def validateNode {n m k : Nat} {Canonical : Point n → Prop}
    (rows : Fin m → Row n) (table : CutTable n k) (q : Nat) (threshold : Int)
    (hcanonRows : ∀ x, Canonical x → ∀ r, (rows r).Satisfied x)
    (b : Box n) (hb : b.WellFormed) (hn : b.Nonnegative) :
    List (Action n m k) → Option (ActionCoverTree Canonical
      (PrunedBy rows) (DischargedBy table q threshold) b)
  | [] => none
  | [.prune row ops] =>
      match hrun : runPropagation rows b ops with
      | none => none
      | some eff =>
          if hp : (rows row).rhs < endpointMin (rows row) eff then
            some (.leaf
              (fun x hc hx => runPropagation_sound hrun x hx (hcanonRows x hc))
              (Or.inl ⟨row, hp⟩))
          else none
  | [.discharge cut mode ops] =>
      match hrun : runPropagation rows b ops with
      | none => none
      | some eff =>
          if hc : modeCheck table mode cut q eff threshold = true then
            some (.leaf
              (fun x hcan hx => runPropagation_sound hrun x hx (hcanonRows x hcan))
              (Or.inr (dischargedBy_sound table
                (runPropagation_nonnegative hn hrun) ⟨cut, mode, hc⟩)))
          else none
  | [.split coord mid ops left right] =>
      match hrun : runPropagation rows b ops with
      | none => none
      | some eff =>
          if hmid : midpoint eff coord = mid then
            if hwidth : eff.lower coord < eff.upper coord then
              let heff := runPropagation_wellFormed hb hrun
              let hneff := runPropagation_nonnegative hn hrun
              let hm : eff.lower coord ≤ mid ∧ mid < eff.upper coord := by
                rw [← hmid]
                exact midpoint_valid heff hwidth
              let hchildren := split_children_wellFormed heff hm
              let lnon : (leftChild eff coord mid).Nonnegative := by
                intro i
                by_cases hi : i = coord
                · subst i
                  simp [leftChild]
                  exact hneff coord
                · simp [leftChild, hi]
                  exact hneff i
              let rnon : (rightChild eff coord mid).Nonnegative := by
                intro i
                by_cases hi : i = coord
                · subst i
                  have hlow := hm.1
                  have hzero := hneff coord
                  have hmid0 : 0 ≤ mid + 1 := by omega
                  simpa [rightChild] using hmid0
                · simp [rightChild, hi]
                  exact hneff i
              match validateNode rows table q threshold hcanonRows
                  (leftChild eff coord mid) hchildren.1 lnon left with
              | none => none
              | some lt =>
                  match validateNode rows table q threshold hcanonRows
                      (rightChild eff coord mid) hchildren.2 rnon right with
                  | none => none
                  | some rt =>
                      some (.split
                        (fun x hcan hx => runPropagation_sound hrun x hx
                          (hcanonRows x hcan))
                        (fun x hcan hx =>
                          split_covers_integer hm x hx)
                        lt rt)
            else none
          else none
  | _ :: _ :: _ => none

def validateComplete {n m k : Nat} {Canonical : Point n → Prop}
    (rows : Fin m → Row n) (table : CutTable n k) (q : Nat) (threshold : Int)
    (hcanonRows : ∀ x, Canonical x → ∀ r, (rows r).Satisfied x)
    (root : Box n) (hroot : root.WellFormed) (hn : root.Nonnegative)
    (stream : List (Action n m k)) :
    Option (ActionCoverTree Canonical (PrunedBy rows)
      (DischargedBy table q threshold) root) :=
  validateNode rows table q threshold hcanonRows root hroot hn stream

/- A proof-free mirror of `validateNode`.  The only state threaded through an
 action is the effective box returned by endpoint propagation; no dependent
 tree or proof is built while this reduces. -/
def validateNodeBool {n m k : Nat}
    (rows : Fin m → Row n) (table : CutTable n k) (q : Nat) (threshold : Int)
    (b : Box n) : List (Action n m k) → Bool
  | [] => false
  | [.prune row ops] =>
      match runPropagation rows b ops with
      | none => false
      | some eff => decide ((rows row).rhs < endpointMin (rows row) eff)
  | [.discharge cut mode ops] =>
      match runPropagation rows b ops with
      | none => false
      | some eff => modeCheck table mode cut q eff threshold
  | [.split coord mid ops left right] =>
      match runPropagation rows b ops with
      | none => false
      | some eff =>
          decide (midpoint eff coord = mid) &&
          decide (eff.lower coord < eff.upper coord) &&
          validateNodeBool rows table q threshold (leftChild eff coord mid) left &&
          validateNodeBool rows table q threshold (rightChild eff coord mid) right
  | _ :: _ :: _ => false

def validateCompleteBool {n m k : Nat}
    (rows : Fin m → Row n) (table : CutTable n k) (q : Nat) (threshold : Int)
    (root : Box n) (stream : List (Action n m k)) : Bool :=
  validateNodeBool rows table q threshold root stream

mutual
  def actionSize {n m k : Nat} : Action n m k → Nat
    | .prune _ _ => 1
    | .discharge _ _ _ => 1
    | .split _ _ _ left right => 1 + streamSize left + streamSize right
  def streamSize {n m k : Nat} : List (Action n m k) → Nat
    | [] => 0
    | a :: rest => actionSize a + streamSize rest
end

theorem validateNodeBool_sound {n m k : Nat} {Canonical : Point n → Prop}
    (rows : Fin m → Row n) (table : CutTable n k) (q : Nat) (threshold : Int)
    (hcanonRows : ∀ x, Canonical x → ∀ r, (rows r).Satisfied x)
    (b : Box n) (hb : b.WellFormed) (hn : b.Nonnegative)
    (stream : List (Action n m k))
    (hcheck : validateNodeBool rows table q threshold b stream = true) :
    Nonempty (ActionCoverTree Canonical (PrunedBy rows)
      (DischargedBy table q threshold) b) := by
  cases stream with
  | nil => simp [validateNodeBool] at hcheck
  | cons a rest =>
      cases rest with
      | nil =>
          cases a with
          | prune row ops =>
              cases hrun : runPropagation rows b ops with
              | none => simp [validateNodeBool, hrun] at hcheck
              | some eff =>
                rw [validateNodeBool, hrun] at hcheck
                have heff : runPropagation rows b ops = some eff := hrun
                have hp : (rows row).rhs < endpointMin (rows row) eff :=
                  of_decide_eq_true hcheck
                exact ⟨.leaf
                  (fun x hc hx => runPropagation_sound heff x hx
                    (hcanonRows x hc))
                  (Or.inl ⟨row, hp⟩)⟩
          | discharge cut mode ops =>
              cases hrun : runPropagation rows b ops with
              | none => simp [validateNodeBool, hrun] at hcheck
              | some eff =>
                rw [validateNodeBool, hrun] at hcheck
                have heff : runPropagation rows b ops = some eff := hrun
                have hmode : modeCheck table mode cut q eff threshold = true := hcheck
                exact ⟨.leaf
                  (fun x hc hx => runPropagation_sound heff x hx
                    (hcanonRows x hc))
                  (Or.inr (dischargedBy_sound table
                    (runPropagation_nonnegative hn heff)
                    ⟨cut, mode, hmode⟩))⟩
          | split coord mid ops left right =>
              cases hrun : runPropagation rows b ops with
              | none => simp [validateNodeBool, hrun] at hcheck
              | some eff =>
                rw [validateNodeBool, hrun] at hcheck
                have heff : runPropagation rows b ops = some eff := hrun
                have hparts := Bool.and_eq_true_iff.mp hcheck
                have hparts' := Bool.and_eq_true_iff.mp hparts.1
                have hparts'' := Bool.and_eq_true_iff.mp hparts'.1
                have hmid : midpoint eff coord = mid := of_decide_eq_true hparts''.1
                have hwidth : eff.lower coord < eff.upper coord := of_decide_eq_true hparts''.2
                have heffwf := runPropagation_wellFormed hb heff
                have heffnon := runPropagation_nonnegative hn heff
                have hm : eff.lower coord ≤ mid ∧ mid < eff.upper coord := by
                  rw [← hmid]
                  exact midpoint_valid heffwf hwidth
                have hchildren := split_children_wellFormed heffwf hm
                have lnon : (leftChild eff coord mid).Nonnegative := by
                  intro i
                  by_cases hi : i = coord
                  · subst i
                    simp [leftChild]
                    exact heffnon coord
                  · simp [leftChild, hi]
                    exact heffnon i
                have rnon : (rightChild eff coord mid).Nonnegative := by
                  intro i
                  by_cases hi : i = coord
                  · subst i
                    have hlow := hm.1
                    have hzero := heffnon coord
                    have hmid0 : 0 ≤ mid + 1 := by omega
                    simpa [rightChild] using hmid0
                  · simp [rightChild, hi]
                    exact heffnon i
                have hleft : validateNodeBool rows table q threshold
                    (leftChild eff coord mid) left = true := hparts'.2
                have hright : validateNodeBool rows table q threshold
                    (rightChild eff coord mid) right = true := hparts.2
                rcases validateNodeBool_sound rows table q threshold hcanonRows
                    (leftChild eff coord mid) hchildren.1 lnon left hleft with ⟨lt⟩
                rcases validateNodeBool_sound rows table q threshold hcanonRows
                    (rightChild eff coord mid) hchildren.2 rnon right hright with ⟨rt⟩
                exact ⟨.split
                  (fun x hcan hx => runPropagation_sound heff x hx
                    (hcanonRows x hcan))
                  (fun x hcan hx => split_covers_integer hm x hx)
                  lt rt⟩
      | cons b' rest' =>
          rw [validateNodeBool] at hcheck
          cases hcheck

theorem validateCompleteBool_sound {n m k : Nat} {Canonical : Point n → Prop}
    (rows : Fin m → Row n) (table : CutTable n k) (q : Nat) (threshold : Int)
    (hcanonRows : ∀ x, Canonical x → ∀ r, (rows r).Satisfied x)
    (root : Box n) (hroot : root.WellFormed) (hn : root.Nonnegative)
    (stream : List (Action n m k))
    (hcheck : validateCompleteBool rows table q threshold root stream = true) :
    Nonempty (ActionCoverTree Canonical (PrunedBy rows)
      (DischargedBy table q threshold) root) :=
  validateNodeBool_sound rows table q threshold hcanonRows root hroot hn stream hcheck

theorem validateNode_rejects_trailing {n m k : Nat} {Canonical : Point n → Prop}
    (rows : Fin m → Row n) (table : CutTable n k) (q : Nat) (threshold : Int)
    (hcanonRows : ∀ x, Canonical x → ∀ r, (rows r).Satisfied x)
    (b : Box n) (hb : b.WellFormed) (hn : b.Nonnegative)
    (a b' : Action n m k) (rest : List (Action n m k)) :
    validateNode rows table q threshold hcanonRows b hb hn (a :: b' :: rest) = none := by
  cases a <;> simp [validateNode]

theorem validateComplete_locate {n m k : Nat} {Canonical : Point n → Prop}
    (rows : Fin m → Row n) (table : CutTable n k) (q : Nat) (threshold : Int)
    (hcanonRows : ∀ x, Canonical x → ∀ r, (rows r).Satisfied x)
    (root : Box n) (hroot : root.WellFormed) (hn : root.Nonnegative)
    (stream : List (Action n m k))
    (tree : ActionCoverTree Canonical (PrunedBy rows)
      (DischargedBy table q threshold) root)
    (hvalid : validateComplete rows table q threshold hcanonRows root hroot hn stream = some tree)
    {x : Point n} (hcanon : Canonical x) (hx : root.Contains x) :
    ∃ leaf, leaf.Contains x ∧
      (PrunedBy rows leaf ∨ DischargedBy table q threshold leaf) := by
  exact tree.locate hcanon hx

/-! ## Lattice-aware full tree and S57 inference -/

inductive CoverTree {n : Nat} (Canonical : Point n → Prop)
    (Pruned Discharged : Box n → Prop) : Box n → Type
  | leaf {b : Box n} (h : Pruned b ∨ Discharged b) : CoverTree Canonical Pruned Discharged b
  | split {b l r : Box n}
      (part : ∀ x, b.Contains x → l.Contains x ∨ r.Contains x)
      (left : CoverTree Canonical Pruned Discharged l)
      (right : CoverTree Canonical Pruned Discharged r) :
      CoverTree Canonical Pruned Discharged b

theorem CoverTree.locate {n : Nat} {Canonical : Point n → Prop}
    {Pruned Discharged : Box n → Prop} {root : Box n}
    (tree : CoverTree Canonical Pruned Discharged root) (x : Point n)
    (hx : root.Contains x) :
    ∃ leaf, leaf.Contains x ∧ (Pruned leaf ∨ Discharged leaf) := by
  induction tree with
  | leaf h => exact ⟨_, hx, h⟩
  | split part left right ihl ihr =>
      rcases part x hx with hl | hr
      · exact ihl hl
      · exact ihr hr

theorem CoverTree.canonical_discharge {n : Nat} {Canonical : Point n → Prop}
    {Pruned Discharged : Box n → Prop} {root : Box n}
    (tree : CoverTree Canonical Pruned Discharged root)
    (hpruned : ∀ b, Pruned b → ∀ x, b.Contains x → ¬ Canonical x)
    {x : Point n} (hroot : root.Contains x) (hcanon : Canonical x) :
    ∃ leaf, leaf.Contains x ∧ Discharged leaf := by
  rcases tree.locate x hroot with ⟨leaf, hmem, hleaf⟩
  rcases hleaf with hp | hd
  · exact False.elim (hpruned leaf hp x hmem hcanon)
  · exact ⟨leaf, hmem, hd⟩

/-- Paper `lem:boxsound` (S57), abstract form: a complete cover tree over the
full integer cube places every canonical point in a discharged leaf. -/
theorem integer_box_inference {n : Nat} {q : Nat}
    {Canonical : Point n → Prop} {Pruned Discharged : Box n → Prop}
    (tree : CoverTree Canonical Pruned Discharged (fullBox n q))
    (hpruned : ∀ b, Pruned b → ∀ x, b.Contains x → ¬ Canonical x)
    (hcanon_bounds : ∀ x, Canonical x → ∀ i, 0 ≤ x i ∧ x i ≤ q)
    : ∀ x, Canonical x → ∃ leaf, leaf.Contains x ∧ Discharged leaf := by
  intro x hcanon
  apply tree.canonical_discharge hpruned
  · intro i
    have hb := hcanon_bounds x hcanon i
    exact hb
  · exact hcanon

/-! A tiny closed instance exercises the exact interval mode (including the
  count-scale `q` factor on linear terms). -/

def oneBox : Box 1 := { lower := fun _ => 0, upper := fun _ => 1 }

def singleBox : Box 1 := { lower := fun _ => 1, upper := fun _ => 1 }

def oneCut : Cut 1 :=
  { constant := 0
    linear := fun _ => 1
    bilinear := fun _ _ => 0 }

example : IntervalDischarge oneCut 3 oneBox 3 := by
  norm_num [IntervalDischarge, intervalUpper, bilinearUpper, oneCut, oneBox]

example : ∀ x, oneBox.Contains x → Cut.eval oneCut 3 x ≤ 3 := by
  intro x hx
  apply interval_discharge_sound (cut := oneCut) (q := 3)
    (b := oneBox) (threshold := 3) (fun _ => by norm_num [oneBox])
    (by norm_num [IntervalDischarge, intervalUpper, bilinearUpper, oneCut, oneBox]) x hx

def noRows : Fin 0 → Row 1 := Fin.elim0

def singletonTable : CutTable 1 1 :=
  { cuts := fun _ => oneCut
    noDiagonal := by intro c i; rfl }

def trivialCanonical : Point 1 → Prop := fun _ => True

-- Closed parser exercise: the singleton-evaluation action is accepted.
#eval Option.isSome (validateComplete (Canonical := trivialCanonical)
  noRows singletonTable 3 3
  (by intro x _ r; exact Fin.elim0 r)
  singleBox (by intro i; change (1 : Int) ≤ 1; exact le_rfl)
  (by intro i; change (0 : Int) ≤ 1; omega)
  [.discharge 0 .eval []])

#print axioms split_covers_integer
#print axioms endpoint_prune_sound
#print axioms propagation_upper_sound
#print axioms intervalUpper_sound
#print axioms eval_discharge_sound
#print axioms corner_extremum
#print axioms corner_check_discharge
#print axioms of_twelve_mul_le_paperThreshold
#print axioms Cut.eval_eq_sq_mul_normalizedEval
#print axioms modeCheck_sound
#print axioms validateCompleteBool_sound
#print axioms validateComplete_locate
#print axioms ActionCoverTree.canonical_discharge
#print axioms integer_box_inference

end PeaceableQueens.UpperBound.FiniteLattice
