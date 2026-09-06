import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-!
# Exact certificate soundness for the upper bound

This module contains certificate-independent lemmas used by the completed
upper-bound half of the even-torus theorem.  It deliberately proves the
soundness layer before any of the large certificate objects are imported.

The four McCormick lemmas are statement S30 of `FORMAL_PROOF.md` (paper
`eq:mccormick`).  The endpoint and dual-combination lemmas are the algebraic
core of S33 (paper `lem:dualleaf`); the support-dual lemmas are paper
`lem:cutsound` (S39); `CoverTree.locate` is paper `lem:branchsound` (S35).
All arithmetic is exact over `ℚ`.
-/

namespace PeaceableQueens.UpperBound

/-- A fixed-size vector over the rationals. -/
abbrev RatVec (n : ℕ) := Fin n → ℚ

/-- Exact dot product for rational vectors. -/
def dot {n : ℕ} (x y : RatVec n) : ℚ := ∑ i, x i * y i

/-- Dot product indexed by an arbitrary finite type. -/
def finiteDot {ι : Type*} [Fintype ι] (x y : ι → ℚ) : ℚ :=
  ∑ i, x i * y i

/-- A rational coordinate box.  Well-formedness is kept as a separate
predicate because a checker must establish it rather than receive it as
trusted input. -/
structure RatBox (n : ℕ) where
  lower : RatVec n
  upper : RatVec n

namespace RatBox

/-- Every lower endpoint is at most its upper endpoint. -/
def WellFormed {n : ℕ} (box : RatBox n) : Prop :=
  ∀ i, box.lower i ≤ box.upper i

/-- Point membership in a closed rational box. -/
def Contains {n : ℕ} (box : RatBox n) (x : RatVec n) : Prop :=
  ∀ i, box.lower i ≤ x i ∧ x i ≤ box.upper i

end RatBox

/-- The endpoint contribution maximizing `coefficient * x` on `[lower, upper]`. -/
def endpointContribution (coefficient lower upper : ℚ) : ℚ :=
  if 0 ≤ coefficient then coefficient * upper else coefficient * lower

theorem mul_le_endpointContribution
    {coefficient lower x upper : ℚ}
    (hl : lower ≤ x) (hu : x ≤ upper) :
    coefficient * x ≤ endpointContribution coefficient lower upper := by
  rw [endpointContribution]
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left hu h
  · exact mul_le_mul_of_nonpos_left hl (le_of_not_ge h)

/-- A linear form on a box is bounded by choosing the endpoint indicated by
the sign of each coefficient.  This is the endpoint step in S33. -/
theorem dot_le_endpoint_sum {n : ℕ} (box : RatBox n) (x coefficients : RatVec n)
    (hx : box.Contains x) :
    dot coefficients x ≤
      ∑ i, endpointContribution (coefficients i) (box.lower i) (box.upper i) := by
  unfold dot
  exact Finset.sum_le_sum fun i _ =>
    mul_le_endpointContribution (hx i).1 (hx i).2

/-! ## McCormick inequalities (S30) -/

theorem mccormick_lower_lower
    {lowerX lowerY x y : ℚ} (hx : lowerX ≤ x) (hy : lowerY ≤ y) :
    -x * y + lowerX * y + lowerY * x ≤ lowerX * lowerY := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

theorem mccormick_upper_upper
    {x y upperX upperY : ℚ} (hx : x ≤ upperX) (hy : y ≤ upperY) :
    -x * y + upperX * y + upperY * x ≤ upperX * upperY := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

theorem mccormick_upper_lower
    {lowerY x y upperX : ℚ} (hx : x ≤ upperX) (hy : lowerY ≤ y) :
    x * y - upperX * y - lowerY * x ≤ -upperX * lowerY := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

theorem mccormick_lower_upper
    {lowerX x y upperY : ℚ} (hx : lowerX ≤ x) (hy : y ≤ upperY) :
    x * y - lowerX * y - upperY * x ≤ -lowerX * upperY := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]

/-! ## Exact linear-combination soundness -/

/-- A nonnegative combination of valid `≤` rows remains valid. -/
theorem nonnegative_inequality_combination {vars rows : ℕ}
    (matrix : Fin rows → RatVec vars) (rhs : RatVec rows)
    (z : RatVec vars) (weights : RatVec rows)
    (hrows : ∀ i, dot (matrix i) z ≤ rhs i)
    (hweights : ∀ i, 0 ≤ weights i) :
    ∑ i, weights i * dot (matrix i) z ≤ ∑ i, weights i * rhs i := by
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hrows i) (hweights i)

/-- An arbitrary combination of valid equality rows remains an equality. -/
theorem equality_combination {vars rows : ℕ}
    (matrix : Fin rows → RatVec vars) (rhs : RatVec rows)
    (z : RatVec vars) (weights : RatVec rows)
    (hrows : ∀ i, dot (matrix i) z = rhs i) :
    ∑ i, weights i * dot (matrix i) z = ∑ i, weights i * rhs i := by
  exact Finset.sum_congr rfl fun i _ => congrArg (weights i * ·) (hrows i)

/-- A finite double sum can be collected by variable. -/
theorem weighted_rows_eq_dot_combination {vars rows : ℕ}
    (matrix : Fin rows → RatVec vars) (weights : RatVec rows)
    (z : RatVec vars) :
    ∑ i, weights i * dot (matrix i) z =
      dot (fun j => ∑ i, weights i * matrix i j) z := by
  simp only [dot, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Arbitrary-finite-type version of `weighted_rows_eq_dot_combination`. -/
theorem weighted_finite_rows_eq_dot_combination
    {Variable Row : Type*} [Fintype Variable] [Fintype Row]
    (matrix : Row → Variable → ℚ) (weights : Row → ℚ)
    (z : Variable → ℚ) :
    ∑ row, weights row * finiteDot (matrix row) z =
      finiteDot (fun v => ∑ row, weights row * matrix row v) z := by
  simp only [finiteDot, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro row _
  ring

/-- Exact finite-dimensional dual-certificate soundness.

No LP duality theorem or optimizer-existence claim is used: if the supplied
row multipliers reconstruct the objective coefficients, summing already-valid
rows proves the bound directly.  This is the linear algebra at the heart of
the dual-leaf argument, paper `lem:dualleaf` (S33). -/
theorem linear_dual_upper_bound {vars inequalities equalities : ℕ}
    (ineqMatrix : Fin inequalities → RatVec vars)
    (ineqRhs : RatVec inequalities)
    (eqMatrix : Fin equalities → RatVec vars)
    (eqRhs : RatVec equalities)
    (objective z : RatVec vars)
    (ineqWeights : RatVec inequalities)
    (eqWeights : RatVec equalities)
    (hineq : ∀ i, dot (ineqMatrix i) z ≤ ineqRhs i)
    (heq : ∀ i, dot (eqMatrix i) z = eqRhs i)
    (hweights : ∀ i, 0 ≤ ineqWeights i)
    (hcoeff : ∀ j,
      objective j =
        (∑ i, ineqWeights i * ineqMatrix i j) +
        (∑ i, eqWeights i * eqMatrix i j)) :
    dot objective z ≤
      (∑ i, ineqWeights i * ineqRhs i) +
      (∑ i, eqWeights i * eqRhs i) := by
  have hi := nonnegative_inequality_combination
    ineqMatrix ineqRhs z ineqWeights hineq hweights
  have he := equality_combination eqMatrix eqRhs z eqWeights heq
  rw [weighted_rows_eq_dot_combination] at hi he
  have hobjective :
      objective = fun j =>
        (∑ i, ineqWeights i * ineqMatrix i j) +
        (∑ i, eqWeights i * eqMatrix i j) := by
    funext j
    exact hcoeff j
  calc
    dot objective z =
        dot (fun j => ∑ i, ineqWeights i * ineqMatrix i j) z +
        dot (fun j => ∑ i, eqWeights i * eqMatrix i j) z := by
      rw [hobjective]
      simp [dot, add_mul, Finset.sum_add_distrib]
    _ ≤ (∑ i, ineqWeights i * ineqRhs i) +
        (∑ i, eqWeights i * eqRhs i) :=
      add_le_add hi (le_of_eq he)

/-- Exact dual-certificate soundness over arbitrary finite index types. -/
theorem linear_dual_upper_bound_finite
    {Variable Inequality Equality : Type*}
    [Fintype Variable] [Fintype Inequality] [Fintype Equality]
    (ineqMatrix : Inequality → Variable → ℚ)
    (ineqRhs : Inequality → ℚ)
    (eqMatrix : Equality → Variable → ℚ)
    (eqRhs : Equality → ℚ)
    (objective z : Variable → ℚ)
    (ineqWeights : Inequality → ℚ)
    (eqWeights : Equality → ℚ)
    (hineq : ∀ row, finiteDot (ineqMatrix row) z ≤ ineqRhs row)
    (heq : ∀ row, finiteDot (eqMatrix row) z = eqRhs row)
    (hweights : ∀ row, 0 ≤ ineqWeights row)
    (hcoeff : ∀ v,
      objective v =
        (∑ row, ineqWeights row * ineqMatrix row v) +
        (∑ row, eqWeights row * eqMatrix row v)) :
    finiteDot objective z ≤
      (∑ row, ineqWeights row * ineqRhs row) +
      (∑ row, eqWeights row * eqRhs row) := by
  have hi :
      ∑ row, ineqWeights row * finiteDot (ineqMatrix row) z ≤
        ∑ row, ineqWeights row * ineqRhs row :=
    Finset.sum_le_sum fun row _ =>
      mul_le_mul_of_nonneg_left (hineq row) (hweights row)
  have he :
      ∑ row, eqWeights row * finiteDot (eqMatrix row) z =
        ∑ row, eqWeights row * eqRhs row :=
    Finset.sum_congr rfl fun row _ => congrArg (eqWeights row * ·) (heq row)
  rw [weighted_finite_rows_eq_dot_combination] at hi he
  calc
    finiteDot objective z =
        finiteDot (fun v => ∑ row, ineqWeights row * ineqMatrix row v) z +
        finiteDot (fun v => ∑ row, eqWeights row * eqMatrix row v) z := by
      unfold finiteDot
      simp_rw [hcoeff]
      simp [add_mul, Finset.sum_add_distrib]
    _ ≤ (∑ row, ineqWeights row * ineqRhs row) +
        (∑ row, eqWeights row * eqRhs row) := add_le_add hi (le_of_eq he)

/-- Soundness of a support dual for the black/white objective.

The distinguished atom `blackAtom` contributes to the black count and
`whiteAtom` to the white count.  A coefficient `theta ∈ [0,1]` first bounds
their minimum by a convex combination.  The columnwise support inequalities,
nonnegativity of the atom weights, and the exact moment equalities then bound
that combination by the dual right-hand side.  This is the generic proof
behind paper `lem:cutsound` (S39); concrete support cuts only have to supply
finite exact data. -/
theorem support_dual_sound
    {Atom Row : Type*} [Fintype Atom] [Fintype Row] [DecidableEq Atom]
    (theta : ℚ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (moment : Row → Atom → ℚ) (dual : Row → ℚ)
    (atomWeight : Atom → ℚ) (momentRhs : Row → ℚ)
    (blackAtom whiteAtom : Atom) (hatoms : blackAtom ≠ whiteAtom)
    (hatom : ∀ atom, 0 ≤ atomWeight atom)
    (hmoment : ∀ row, ∑ atom, moment row atom * atomWeight atom = momentRhs row)
    (hsupport : ∀ atom,
      (if atom = blackAtom then theta else 0) +
          (if atom = whiteAtom then 1 - theta else 0) ≤
        ∑ row, dual row * moment row atom) :
    min (∑ atom, if atom = blackAtom then atomWeight atom else 0)
        (∑ atom, if atom = whiteAtom then atomWeight atom else 0) ≤
      ∑ row, dual row * momentRhs row := by
  have hconv : min (∑ atom, if atom = blackAtom then atomWeight atom else 0)
          (∑ atom, if atom = whiteAtom then atomWeight atom else 0) ≤
      theta * (∑ atom, if atom = blackAtom then atomWeight atom else 0) +
          (1 - theta) * (∑ atom, if atom = whiteAtom then atomWeight atom else 0) := by
    rcases le_total (∑ atom, if atom = blackAtom then atomWeight atom else 0)
        (∑ atom, if atom = whiteAtom then atomWeight atom else 0) with h | h
    · calc
        min (∑ atom, if atom = blackAtom then atomWeight atom else 0)
            (∑ atom, if atom = whiteAtom then atomWeight atom else 0) ≤
            (∑ atom, if atom = blackAtom then atomWeight atom else 0) := min_le_left _ _
        _ = theta * (∑ atom, if atom = blackAtom then atomWeight atom else 0) +
              (1 - theta) * (∑ atom, if atom = blackAtom then atomWeight atom else 0) := by ring
        _ ≤ theta * (∑ atom, if atom = blackAtom then atomWeight atom else 0) +
              (1 - theta) * (∑ atom, if atom = whiteAtom then atomWeight atom else 0) := by
          simpa [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_left h (sub_nonneg.mpr htheta1))
            (theta * (∑ atom, if atom = blackAtom then atomWeight atom else 0))
    · calc
        min (∑ atom, if atom = blackAtom then atomWeight atom else 0)
            (∑ atom, if atom = whiteAtom then atomWeight atom else 0) ≤
            (∑ atom, if atom = whiteAtom then atomWeight atom else 0) := min_le_right _ _
        _ = theta * (∑ atom, if atom = whiteAtom then atomWeight atom else 0) +
              (1 - theta) * (∑ atom, if atom = whiteAtom then atomWeight atom else 0) := by ring
        _ ≤ theta * (∑ atom, if atom = blackAtom then atomWeight atom else 0) +
              (1 - theta) * (∑ atom, if atom = whiteAtom then atomWeight atom else 0) := by
          simpa [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_left h htheta0)
            ((1 - theta) * (∑ atom, if atom = whiteAtom then atomWeight atom else 0))
  apply le_trans hconv
  calc
    theta * (∑ atom, if atom = blackAtom then atomWeight atom else 0) +
          (1 - theta) * (∑ atom, if atom = whiteAtom then atomWeight atom else 0)
        = ∑ atom,
        (((if atom = blackAtom then theta else 0) +
          (if atom = whiteAtom then 1 - theta else 0)) * atomWeight atom) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro atom _
      by_cases hb : atom = blackAtom <;> by_cases hw : atom = whiteAtom <;>
        simp [hb, hw, hatoms, hatoms.symm]
    _ ≤ ∑ atom, ((∑ row, dual row * moment row atom) * atomWeight atom) := by
      exact Finset.sum_le_sum fun atom _ =>
        mul_le_mul_of_nonneg_right (hsupport atom) (hatom atom)
    _ = ∑ row, dual row * momentRhs row := by
      calc
        _ = ∑ atom, ∑ row, dual row * (moment row atom * atomWeight atom) := by
          apply Finset.sum_congr rfl
          intro atom _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro row _
          ring
        _ = ∑ row, ∑ atom, dual row * (moment row atom * atomWeight atom) :=
          Finset.sum_comm
        _ = ∑ row, dual row * momentRhs row := by
          apply Finset.sum_congr rfl
          intro row _
          rw [← Finset.mul_sum, hmoment row]

/-- Predicate form of `support_dual_sound` before taking the minimum: the
weighted inequality `θ·B + (1-θ)·W ≤ λᵀb` of paper `lem:cutsound`, which at
`θ = 1` and `θ = 0` gives the individual black and white bounds of `lem:cuts`.
It is the form used by the concrete 64-column model, where the black and white
objectives each select one atom in every parity block rather than one globally
distinguished column. -/
theorem support_weighted_dual_sound_indicator
    {Atom Row : Type*} [Fintype Atom] [Fintype Row]
    (theta : ℚ)
    (moment : Row → Atom → ℚ) (dual : Row → ℚ)
    (atomWeight : Atom → ℚ) (momentRhs : Row → ℚ)
    (isBlack isWhite : Atom → Bool)
    (hatom : ∀ atom, 0 ≤ atomWeight atom)
    (hmoment : ∀ row, ∑ atom, moment row atom * atomWeight atom = momentRhs row)
    (hsupport : ∀ atom,
      (if isBlack atom then theta else 0) +
          (if isWhite atom then 1 - theta else 0) ≤
        ∑ row, dual row * moment row atom) :
    theta * (∑ atom, if isBlack atom then atomWeight atom else 0) +
        (1 - theta) * (∑ atom, if isWhite atom then atomWeight atom else 0) ≤
      ∑ row, dual row * momentRhs row := by
  calc
    _ = ∑ atom,
        (((if isBlack atom then theta else 0) +
          (if isWhite atom then 1 - theta else 0)) * atomWeight atom) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro atom _
      cases hb : isBlack atom <;> cases hw : isWhite atom
      all_goals simp
      all_goals ring
    _ ≤ ∑ atom, ((∑ row, dual row * moment row atom) * atomWeight atom) := by
      exact Finset.sum_le_sum fun atom _ =>
        mul_le_mul_of_nonneg_right (hsupport atom) (hatom atom)
    _ = ∑ row, dual row * momentRhs row := by
      calc
        _ = ∑ atom, ∑ row, dual row * (moment row atom * atomWeight atom) := by
          apply Finset.sum_congr rfl
          intro atom _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro row _
          ring
        _ = ∑ row, ∑ atom, dual row * (moment row atom * atomWeight atom) :=
          Finset.sum_comm
        _ = ∑ row, dual row * momentRhs row := by
          apply Finset.sum_congr rfl
          intro row _
          rw [← Finset.mul_sum, hmoment row]

/-- The minimum-objective consequence of the weighted support inequality.
The weighted theorem also exposes the paper's individual black/white bounds. -/
theorem support_dual_sound_indicator
    {Atom Row : Type*} [Fintype Atom] [Fintype Row]
    (theta : ℚ) (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (moment : Row → Atom → ℚ) (dual : Row → ℚ)
    (atomWeight : Atom → ℚ) (momentRhs : Row → ℚ)
    (isBlack isWhite : Atom → Bool)
    (hatom : ∀ atom, 0 ≤ atomWeight atom)
    (hmoment : ∀ row, ∑ atom, moment row atom * atomWeight atom = momentRhs row)
    (hsupport : ∀ atom,
      (if isBlack atom then theta else 0) +
          (if isWhite atom then 1 - theta else 0) ≤
        ∑ row, dual row * moment row atom) :
    min (∑ atom, if isBlack atom then atomWeight atom else 0)
        (∑ atom, if isWhite atom then atomWeight atom else 0) ≤
      ∑ row, dual row * momentRhs row := by
  let blackTotal := ∑ atom, if isBlack atom then atomWeight atom else 0
  let whiteTotal := ∑ atom, if isWhite atom then atomWeight atom else 0
  have hconv : min blackTotal whiteTotal ≤
      theta * blackTotal + (1 - theta) * whiteTotal := by
    rcases le_total blackTotal whiteTotal with h | h
    · calc
        min blackTotal whiteTotal ≤ blackTotal := min_le_left _ _
        _ = theta * blackTotal + (1 - theta) * blackTotal := by ring
        _ ≤ theta * blackTotal + (1 - theta) * whiteTotal := by
          simpa [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_left h (sub_nonneg.mpr htheta1))
            (theta * blackTotal)
    · calc
        min blackTotal whiteTotal ≤ whiteTotal := min_le_right _ _
        _ = theta * whiteTotal + (1 - theta) * whiteTotal := by ring
        _ ≤ theta * blackTotal + (1 - theta) * whiteTotal := by
          simpa [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_left h htheta0)
            ((1 - theta) * whiteTotal)
  exact hconv.trans (support_weighted_dual_sound_indicator theta
    moment dual atomWeight momentRhs isBlack isWhite hatom hmoment hsupport)

/-! ## Abstract branch coverage (S35) -/

/-- A proof tree whose leaves are either safe or exceptional.  The split
constructor records the only geometric fact needed for soundness: its two
children cover the parent box. -/
inductive CoverTree {n : ℕ} (Safe Exceptional : RatBox n → Prop) : RatBox n → Type
  | leaf {box} (result : Safe box ∨ Exceptional box) : CoverTree Safe Exceptional box
  | split {box left right}
      (cover : ∀ x, box.Contains x → left.Contains x ∨ right.Contains x)
      (leftTree : CoverTree Safe Exceptional left)
      (rightTree : CoverTree Safe Exceptional right) :
      CoverTree Safe Exceptional box

/-- Every point in the root belongs to a terminal box carrying one of the
declared outcomes.  This is paper `lem:branchsound` (S35), independent of any
concrete certificate. -/
theorem CoverTree.locate {n : ℕ} {Safe Exceptional : RatBox n → Prop}
    {root : RatBox n} (tree : CoverTree Safe Exceptional root)
    (x : RatVec n) (hx : root.Contains x) :
    ∃ leaf, leaf.Contains x ∧ (Safe leaf ∨ Exceptional leaf) := by
  induction tree with
  | leaf result => exact ⟨_, hx, result⟩
  | split cover leftTree rightTree leftIH rightIH =>
      rcases cover x hx with hleft | hright
      · exact leftIH hleft
      · exact rightIH hright

#print axioms linear_dual_upper_bound
#print axioms linear_dual_upper_bound_finite
#print axioms support_dual_sound
#print axioms support_weighted_dual_sound_indicator
#print axioms support_dual_sound_indicator
#print axioms CoverTree.locate

end PeaceableQueens.UpperBound
