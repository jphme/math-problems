import PeaceableQueens.UpperBound.LPModel

/-!
# Concrete dual-leaf checker and soundness

This module turns the abstract finite-dimensional dual lemma into the exact
leaf checker needed for S33.  Box and nonnegativity constraints are represented
as additional `≤` rows.  Endpoint multipliers are recomputed from the stored
McCormick/equality multipliers, and acceptance rechecks every objective
coefficient and the claimed bound over `ℚ`.
-/

namespace PeaceableQueens.UpperBound.DualLeaf

open LPModel

/-- The 95 stored inequalities plus box and atom-nonnegativity rows. -/
inductive ExpandedIneq
  | base (row : IneqCoord)
  | xLower (coord : ProfileCoord)
  | xUpper (coord : ProfileCoord)
  | yLower (coord : ProductCoord)
  | yUpper (coord : ProductCoord)
  | pLower (coord : AtomCoord)
  deriving DecidableEq, Fintype, Repr

def productLower (lo : Profile) (coord : ProductCoord) : ℚ :=
  lo (productPair coord).1 * lo (productPair coord).2

def productUpper (hi : Profile) (coord : ProductCoord) : ℚ :=
  hi (productPair coord).1 * hi (productPair coord).2

/-- Coefficients of all inequalities available to the generic dual theorem. -/
def expandedCoeff (lo hi : Profile) : ExpandedIneq → VarCoord → ℚ
  | .base row => ineqCoeff lo hi row
  | .xLower coord => fun v => if v = xVar coord then -1 else 0
  | .xUpper coord => fun v => if v = xVar coord then 1 else 0
  | .yLower coord => fun v => if v = yVar coord then -1 else 0
  | .yUpper coord => fun v => if v = yVar coord then 1 else 0
  | .pLower coord => fun v => if v = pVar coord then -1 else 0

def expandedRhs (lo hi : Profile) : ExpandedIneq → ℚ
  | .base row => ineqRhs lo hi row
  | .xLower coord => -lo coord
  | .xUpper coord => hi coord
  | .yLower coord => -productLower lo coord
  | .yUpper coord => productUpper hi coord
  | .pLower _ => 0

/-- Feasibility facts supplied by the configuration-to-leaf bridge S32. -/
def LeafFeasible (lo hi : Profile) (z : LPVector) : Prop :=
  (∀ row, dot (ineqCoeff lo hi row) z ≤ ineqRhs lo hi row) ∧
  (∀ row, dot (eqCoeff row) z = eqRhs row) ∧
  (∀ coord, lo coord ≤ z (xVar coord) ∧ z (xVar coord) ≤ hi coord) ∧
  (∀ coord, productLower lo coord ≤ z (yVar coord) ∧
    z (yVar coord) ≤ productUpper hi coord) ∧
  (∀ coord, 0 ≤ z (pVar coord))

theorem LeafFeasible.expanded {lo hi : Profile} {z : LPVector}
    (hz : LeafFeasible lo hi z) :
    ∀ row, finiteDot (expandedCoeff lo hi row) z ≤ expandedRhs lo hi row := by
  rintro (row | coord | coord | coord | coord | coord)
  · simpa only [expandedCoeff, expandedRhs, finiteDot, dot] using hz.1 row
  · have h := (hz.2.2.1 coord).1
    simpa [finiteDot, expandedCoeff, expandedRhs] using neg_le_neg h
  · have h := (hz.2.2.1 coord).2
    simpa [finiteDot, expandedCoeff, expandedRhs] using h
  · have h := (hz.2.2.2.1 coord).1
    simpa [finiteDot, expandedCoeff, expandedRhs] using neg_le_neg h
  · have h := (hz.2.2.2.1 coord).2
    simpa [finiteDot, expandedCoeff, expandedRhs] using h
  · have h := hz.2.2.2.2 coord
    have : -z (pVar coord) ≤ 0 := by linarith
    simpa [finiteDot, expandedCoeff, expandedRhs] using this

/-- The stored portion of a McCormick dual leaf. -/
structure Certificate where
  mu : IneqCoord → ℚ
  nu : EqCoord → ℚ
  claimed : ℚ

def objective : VarCoord → ℚ := fun v => if v = tVar then 1 else 0

/-- Coefficient left after adding the stored partial Lagrangian to `t`. -/
def residual (lo hi : Profile) (certificate : Certificate) (v : VarCoord) : ℚ :=
  objective v +
    (∑ row, certificate.mu row * ineqCoeff lo hi row v) +
    (∑ row, certificate.nu row * eqCoeff row v)

def positivePart (value : ℚ) : ℚ := if 0 ≤ value then value else 0
def negativePart (value : ℚ) : ℚ := if value ≤ 0 then -value else 0

theorem positivePart_nonnegative (value : ℚ) : 0 ≤ positivePart value := by
  unfold positivePart
  split_ifs with h
  · exact h
  · exact le_rfl

theorem negativePart_nonnegative (value : ℚ) : 0 ≤ negativePart value := by
  unfold negativePart
  split_ifs with h
  · exact neg_nonneg.mpr h
  · exact le_rfl

/-- Nonnegative multipliers for the expanded inequality system. -/
def expandedWeight (lo hi : Profile) (certificate : Certificate) :
    ExpandedIneq → ℚ
  | .base row => -certificate.mu row
  | .xLower coord => negativePart (residual lo hi certificate (xVar coord))
  | .xUpper coord => positivePart (residual lo hi certificate (xVar coord))
  | .yLower coord => negativePart (residual lo hi certificate (yVar coord))
  | .yUpper coord => positivePart (residual lo hi certificate (yVar coord))
  | .pLower coord => negativePart (residual lo hi certificate (pVar coord))

def equalityWeight (certificate : Certificate) (row : EqCoord) : ℚ :=
  -certificate.nu row

/-- Recomputed exact dual bound. -/
def recomputedBound (lo hi : Profile) (certificate : Certificate) : ℚ :=
  (∑ row, expandedWeight lo hi certificate row * expandedRhs lo hi row) +
  (∑ row, equalityWeight certificate row * eqRhs row)

/-- Acceptance checks multiplier signs, all 95 reconstructed objective
coefficients, and the stored bound. -/
def Accepted (lo hi : Profile) (certificate : Certificate) : Prop :=
  (∀ row, certificate.mu row ≤ 0) ∧
  (∀ v, objective v =
    (∑ row, expandedWeight lo hi certificate row * expandedCoeff lo hi row v) +
    (∑ row, equalityWeight certificate row * eqCoeff row v)) ∧
  certificate.claimed = recomputedBound lo hi certificate

instance (lo hi : Profile) (certificate : Certificate) :
    Decidable (Accepted lo hi certificate) := by
  unfold Accepted
  infer_instance

/-- Executable exact-rational acceptance predicate. -/
def check (lo hi : Profile) (certificate : Certificate) : Bool :=
  decide (Accepted lo hi certificate)

theorem check_iff (lo hi : Profile) (certificate : Certificate) :
    check lo hi certificate = true ↔ Accepted lo hi certificate := by
  simp [check]

private theorem expandedWeight_nonnegative {lo hi : Profile}
    {certificate : Certificate} (hmu : ∀ row, certificate.mu row ≤ 0) :
    ∀ row, 0 ≤ expandedWeight lo hi certificate row := by
  rintro (row | coord | coord | coord | coord | coord)
  · exact neg_nonneg.mpr (hmu row)
  · exact negativePart_nonnegative _
  · exact positivePart_nonnegative _
  · exact negativePart_nonnegative _
  · exact positivePart_nonnegative _
  · exact negativePart_nonnegative _

/-- A Boolean-accepted concrete leaf bounds every feasible LP point by its
stored rational value.  This is the checker-acceptance theorem required by
S33; no LP duality result is assumed. -/
theorem check_sound {lo hi : Profile} {certificate : Certificate} {z : LPVector}
    (hz : LeafFeasible lo hi z) (hcheck : check lo hi certificate = true) :
    z tVar ≤ certificate.claimed := by
  have ha : Accepted lo hi certificate := (check_iff lo hi certificate).mp hcheck
  rcases ha with ⟨hmu, hcoeff, hbound⟩
  have hdual := linear_dual_upper_bound_finite
    (expandedCoeff lo hi) (expandedRhs lo hi) eqCoeff eqRhs
    objective z (expandedWeight lo hi certificate) (equalityWeight certificate)
    hz.expanded hz.2.1 (expandedWeight_nonnegative hmu) hcoeff
  have hobjective : finiteDot objective z = z tVar := by
    simp [finiteDot, objective]
  rw [hobjective] at hdual
  rw [hbound]
  simpa [recomputedBound] using hdual

/-- Acceptance at a requested threshold. -/
def AcceptedAt (threshold : ℚ) (lo hi : Profile) (certificate : Certificate) : Prop :=
  Accepted lo hi certificate ∧ certificate.claimed ≤ threshold

instance (threshold : ℚ) (lo hi : Profile) (certificate : Certificate) :
    Decidable (AcceptedAt threshold lo hi certificate) := by
  unfold AcceptedAt
  infer_instance

def checkAt (threshold : ℚ) (lo hi : Profile) (certificate : Certificate) : Bool :=
  decide (AcceptedAt threshold lo hi certificate)

theorem checkAt_sound {threshold : ℚ} {lo hi : Profile}
    {certificate : Certificate} {z : LPVector}
    (hz : LeafFeasible lo hi z)
    (hcheck : checkAt threshold lo hi certificate = true) :
    z tVar ≤ threshold := by
  have ha : AcceptedAt threshold lo hi certificate := by
    exact of_decide_eq_true hcheck
  have hc : check lo hi certificate = true :=
    (check_iff lo hi certificate).mpr ha.1
  exact (check_sound hz hc).trans ha.2

#print axioms check_sound
#print axioms checkAt_sound

end PeaceableQueens.UpperBound.DualLeaf
