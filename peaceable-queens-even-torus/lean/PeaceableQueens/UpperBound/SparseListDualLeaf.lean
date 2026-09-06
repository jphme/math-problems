import PeaceableQueens.UpperBound.DualLeaf

/-!
# Executable sparse McCormick dual-leaf checker

The stored multiplier lists are themselves the finite dual index types.  Thus
checking a certificate is proportional to its support and never reconstructs
the 95- and 42-entry dense functions.
-/

namespace PeaceableQueens.UpperBound.SparseListDualLeaf

open LPModel DualLeaf

structure Certificate where
  mu : List (IneqCoord × ℚ)
  nu : List (EqCoord × ℚ)
  claimed : ℚ

inductive ExpandedIneq (storedRows : Nat)
  | base (entry : Fin storedRows)
  | xLower (coord : ProfileCoord)
  | xUpper (coord : ProfileCoord)
  | yLower (coord : ProductCoord)
  | yUpper (coord : ProductCoord)
  | pLower (coord : AtomCoord)
  deriving DecidableEq, Fintype, Repr

def expandedCoeff (lo hi : Profile) (certificate : Certificate) :
    ExpandedIneq certificate.mu.length → VarCoord → ℚ
  | .base entry => ineqCoeff lo hi (certificate.mu.get entry).1
  | .xLower coord => fun v => if v = xVar coord then -1 else 0
  | .xUpper coord => fun v => if v = xVar coord then 1 else 0
  | .yLower coord => fun v => if v = yVar coord then -1 else 0
  | .yUpper coord => fun v => if v = yVar coord then 1 else 0
  | .pLower coord => fun v => if v = pVar coord then -1 else 0

def expandedRhs (lo hi : Profile) (certificate : Certificate) :
    ExpandedIneq certificate.mu.length → ℚ
  | .base entry => ineqRhs lo hi (certificate.mu.get entry).1
  | .xLower coord => -lo coord
  | .xUpper coord => hi coord
  | .yLower coord => -productLower lo coord
  | .yUpper coord => productUpper hi coord
  | .pLower _ => 0

def equalityCoeff (certificate : Certificate) (entry : Fin certificate.nu.length) :
    VarCoord → ℚ := eqCoeff (certificate.nu.get entry).1

def equalityRhs (certificate : Certificate) (entry : Fin certificate.nu.length) : ℚ :=
  eqRhs (certificate.nu.get entry).1

lemma LeafFeasible.expandedSparse {lo hi : Profile} {certificate : Certificate}
    {z : LPVector} (hz : LeafFeasible lo hi z) :
    ∀ row, finiteDot (expandedCoeff lo hi certificate row) z ≤
      expandedRhs lo hi certificate row := by
  rintro (entry | coord | coord | coord | coord | coord)
  · simpa only [expandedCoeff, expandedRhs, finiteDot, dot] using
      hz.1 (certificate.mu.get entry).1
  · have h := (hz.2.2.1 coord).1
    simpa [finiteDot, expandedCoeff, expandedRhs] using neg_le_neg h
  · simpa [finiteDot, expandedCoeff, expandedRhs] using (hz.2.2.1 coord).2
  · have h := (hz.2.2.2.1 coord).1
    simpa [finiteDot, expandedCoeff, expandedRhs] using neg_le_neg h
  · simpa [finiteDot, expandedCoeff, expandedRhs] using (hz.2.2.2.1 coord).2
  · have h : -z (pVar coord) ≤ 0 := by linarith [hz.2.2.2.2 coord]
    simpa [finiteDot, expandedCoeff, expandedRhs] using h

lemma LeafFeasible.equalitySparse {lo hi : Profile} {certificate : Certificate}
    {z : LPVector} (hz : LeafFeasible lo hi z) :
    ∀ entry, finiteDot (equalityCoeff certificate entry) z =
      equalityRhs certificate entry := by
  intro entry
  simpa [equalityCoeff, equalityRhs, finiteDot, dot] using
    hz.2.1 (certificate.nu.get entry).1

def residual (lo hi : Profile) (certificate : Certificate) (v : VarCoord) : ℚ :=
  objective v +
    (∑ entry : Fin certificate.mu.length,
      (certificate.mu.get entry).2 * ineqCoeff lo hi (certificate.mu.get entry).1 v) +
    (∑ entry : Fin certificate.nu.length,
      (certificate.nu.get entry).2 * eqCoeff (certificate.nu.get entry).1 v)

def expandedWeight (lo hi : Profile) (certificate : Certificate) :
    ExpandedIneq certificate.mu.length → ℚ
  | .base entry => -(certificate.mu.get entry).2
  | .xLower coord => negativePart (residual lo hi certificate (xVar coord))
  | .xUpper coord => positivePart (residual lo hi certificate (xVar coord))
  | .yLower coord => negativePart (residual lo hi certificate (yVar coord))
  | .yUpper coord => positivePart (residual lo hi certificate (yVar coord))
  | .pLower coord => negativePart (residual lo hi certificate (pVar coord))

def equalityWeight (certificate : Certificate) (entry : Fin certificate.nu.length) : ℚ :=
  -(certificate.nu.get entry).2

def recomputedBound (lo hi : Profile) (certificate : Certificate) : ℚ :=
  (∑ entry : Fin certificate.mu.length,
    (-(certificate.mu.get entry).2) * ineqRhs lo hi (certificate.mu.get entry).1) +
  (∑ coord : ProfileCoord,
    (negativePart (residual lo hi certificate (xVar coord)) * (-lo coord) +
      positivePart (residual lo hi certificate (xVar coord)) * hi coord)) +
  (∑ coord : ProductCoord,
    (negativePart (residual lo hi certificate (yVar coord)) * (-productLower lo coord) +
      positivePart (residual lo hi certificate (yVar coord)) * productUpper hi coord)) +
  (∑ entry, equalityWeight certificate entry * equalityRhs certificate entry)

def AcceptedAt (threshold : ℚ) (lo hi : Profile) (certificate : Certificate) : Prop :=
  (∀ entry, (certificate.mu.get entry).2 ≤ 0) ∧
  residual lo hi certificate tVar = 0 ∧
  (∀ coord, residual lo hi certificate (pVar coord) ≤ 0) ∧
  certificate.claimed = recomputedBound lo hi certificate ∧
  certificate.claimed ≤ threshold

instance (threshold : ℚ) (lo hi : Profile) (certificate : Certificate) :
    Decidable (AcceptedAt threshold lo hi certificate) := by
  unfold AcceptedAt
  infer_instance

def checkAt (threshold : ℚ) (lo hi : Profile) (certificate : Certificate) : Bool :=
  decide (AcceptedAt threshold lo hi certificate)

lemma positive_sub_negative (value : ℚ) :
    positivePart value - negativePart value = value := by
  unfold positivePart negativePart
  split_ifs <;> linarith

@[simp] lemma xVar_eq_xVar {i j : ProfileCoord} : xVar i = xVar j ↔ i = j := by
  constructor
  · intro h; exact Fin.ext (by simpa [xVar] using congrArg Fin.val h)
  · exact congrArg xVar

@[simp] lemma yVar_eq_yVar {i j : ProductCoord} : yVar i = yVar j ↔ i = j := by
  constructor
  · intro h; exact Fin.ext (by simpa [yVar] using congrArg Fin.val h)
  · exact congrArg yVar

@[simp] lemma pVar_eq_pVar {i j : AtomCoord} : pVar i = pVar j ↔ i = j := by
  constructor
  · intro h; exact Fin.ext (by simpa [pVar] using congrArg Fin.val h)
  · exact congrArg pVar

@[simp] lemma xVar_ne_yVar (i : ProfileCoord) (j : ProductCoord) : xVar i ≠ yVar j := by
  intro h; have h' := congrArg Fin.val h; simp [xVar, yVar] at h'; omega

@[simp] lemma xVar_ne_pVar (i : ProfileCoord) (j : AtomCoord) : xVar i ≠ pVar j := by
  intro h; have h' := congrArg Fin.val h; simp [xVar, pVar] at h'; omega

@[simp] lemma yVar_ne_xVar (i : ProductCoord) (j : ProfileCoord) : yVar i ≠ xVar j :=
  ne_comm.mp (xVar_ne_yVar j i)

@[simp] lemma yVar_ne_pVar (i : ProductCoord) (j : AtomCoord) : yVar i ≠ pVar j := by
  intro h; have h' := congrArg Fin.val h; simp [yVar, pVar] at h'; omega

@[simp] lemma pVar_ne_xVar (i : AtomCoord) (j : ProfileCoord) : pVar i ≠ xVar j :=
  ne_comm.mp (xVar_ne_pVar j i)

@[simp] lemma pVar_ne_yVar (i : AtomCoord) (j : ProductCoord) : pVar i ≠ yVar j :=
  ne_comm.mp (yVar_ne_pVar j i)

@[simp] lemma tVar_ne_xVar (i : ProfileCoord) : tVar ≠ xVar i := by
  intro h; have h' := congrArg Fin.val h; simp [tVar, xVar] at h'
  have := i.isLt; omega

@[simp] lemma tVar_ne_yVar (i : ProductCoord) : tVar ≠ yVar i := by
  intro h; have h' := congrArg Fin.val h; simp [tVar, yVar] at h'; omega

@[simp] lemma tVar_ne_pVar (i : AtomCoord) : tVar ≠ pVar i := by
  intro h; have h' := congrArg Fin.val h; simp [tVar, pVar] at h'; omega

def expandedEquiv (storedRows : Nat) : ExpandedIneq storedRows ≃
    Fin storedRows ⊕ (ProfileCoord ⊕ (ProfileCoord ⊕
      (ProductCoord ⊕ (ProductCoord ⊕ AtomCoord)))) where
  toFun
    | .base row => .inl row
    | .xLower coord => .inr (.inl coord)
    | .xUpper coord => .inr (.inr (.inl coord))
    | .yLower coord => .inr (.inr (.inr (.inl coord)))
    | .yUpper coord => .inr (.inr (.inr (.inr (.inl coord))))
    | .pLower coord => .inr (.inr (.inr (.inr (.inr coord))))
  invFun
    | .inl row => .base row
    | .inr (.inl coord) => .xLower coord
    | .inr (.inr (.inl coord)) => .xUpper coord
    | .inr (.inr (.inr (.inl coord))) => .yLower coord
    | .inr (.inr (.inr (.inr (.inl coord)))) => .yUpper coord
    | .inr (.inr (.inr (.inr (.inr coord)))) => .pLower coord
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with x | x
    · rfl
    rcases x with x | x
    · rfl
    rcases x with x | x
    · rfl
    rcases x with x | x
    · rfl
    rcases x with x | x <;> rfl

lemma sum_expanded {storedRows : Nat} (f : ExpandedIneq storedRows → ℚ) :
    (∑ row, f row) =
      (∑ row : Fin storedRows, f (.base row)) +
      (∑ coord : ProfileCoord, f (.xLower coord)) +
      (∑ coord : ProfileCoord, f (.xUpper coord)) +
      (∑ coord : ProductCoord, f (.yLower coord)) +
      (∑ coord : ProductCoord, f (.yUpper coord)) +
      (∑ coord : AtomCoord, f (.pLower coord)) := by
  let g : Fin storedRows ⊕ (ProfileCoord ⊕ (ProfileCoord ⊕
      (ProductCoord ⊕ (ProductCoord ⊕ AtomCoord)))) → ℚ
    | .inl row => f (.base row)
    | .inr (.inl coord) => f (.xLower coord)
    | .inr (.inr (.inl coord)) => f (.xUpper coord)
    | .inr (.inr (.inr (.inl coord))) => f (.yLower coord)
    | .inr (.inr (.inr (.inr (.inl coord)))) => f (.yUpper coord)
    | .inr (.inr (.inr (.inr (.inr coord)))) => f (.pLower coord)
  calc
    (∑ row, f row) = ∑ x, g x := by
      apply Fintype.sum_equiv (expandedEquiv storedRows)
      intro x; cases x <;> rfl
    _ = _ := by simp only [Fintype.sum_sum_type, g]; ring

lemma expanded_bound_eq_recomputedBound (lo hi : Profile) (certificate : Certificate) :
    (∑ row, expandedWeight lo hi certificate row * expandedRhs lo hi certificate row) +
      (∑ entry, equalityWeight certificate entry * equalityRhs certificate entry) =
    recomputedBound lo hi certificate := by
  rw [sum_expanded]
  simp only [expandedWeight, expandedRhs, recomputedBound, Finset.sum_add_distrib,
    mul_zero, Finset.sum_const_zero, add_zero]
  ring

private lemma coefficient_identity (lo hi : Profile) (certificate : Certificate)
    (ht : residual lo hi certificate tVar = 0)
    (hp : ∀ coord, residual lo hi certificate (pVar coord) ≤ 0) :
    ∀ v, objective v =
      (∑ row, expandedWeight lo hi certificate row * expandedCoeff lo hi certificate row v) +
      (∑ entry, equalityWeight certificate entry * equalityCoeff certificate entry v) := by
  intro v
  rw [sum_expanded]
  by_cases hx : v.val < 8
  · let i : ProfileCoord := ⟨v.val, hx⟩
    have hv : v = xVar i := by ext; simp [i, xVar]
    rw [hv]
    simp only [expandedWeight, expandedCoeff, equalityWeight, equalityCoeff]
    simp
    simp only [← List.get_eq_getElem]
    simp only [residual]
    have hparts := positive_sub_negative (residual lo hi certificate (xVar i))
    simp only [residual] at hparts
    linarith
  · by_cases hy : v.val < 30
    · have hlo : 8 ≤ v.val := by omega
      let i : ProductCoord := ⟨v.val - 8, by omega⟩
      have hv : v = yVar i := by ext; simp [i, yVar]; omega
      rw [hv]
      simp only [expandedWeight, expandedCoeff, equalityWeight, equalityCoeff]
      simp
      simp only [← List.get_eq_getElem]
      simp only [residual]
      have hparts := positive_sub_negative (residual lo hi certificate (yVar i))
      simp only [residual] at hparts
      linarith
    · by_cases hpv : v.val < 94
      · have hlo : 30 ≤ v.val := by omega
        let i : AtomCoord := ⟨v.val - 30, by omega⟩
        have hv : v = pVar i := by ext; simp [i, pVar]; omega
        rw [hv]
        have hpi := hp i
        simp only [expandedWeight, expandedCoeff, equalityWeight, equalityCoeff]
        simp
        simp only [← List.get_eq_getElem]
        unfold negativePart
        rw [if_pos hpi]
        simp only [residual]
        ring
      · have hv : v = tVar := by ext; simp [tVar]; omega
        rw [hv]
        simp only [expandedWeight, expandedCoeff, equalityWeight, equalityCoeff]
        simp
        simp only [← List.get_eq_getElem]
        simp only [residual] at ht
        linarith

private lemma expandedWeight_nonnegative {lo hi : Profile} {certificate : Certificate}
    (hmu : ∀ entry, (certificate.mu.get entry).2 ≤ 0) :
    ∀ row, 0 ≤ expandedWeight lo hi certificate row := by
  rintro (entry | coord | coord | coord | coord | coord)
  · exact neg_nonneg.mpr (hmu entry)
  · exact negativePart_nonnegative _
  · exact positivePart_nonnegative _
  · exact negativePart_nonnegative _
  · exact positivePart_nonnegative _
  · exact negativePart_nonnegative _

theorem checkAt_sound {threshold : ℚ} {lo hi : Profile}
    {certificate : Certificate} {z : LPVector}
    (hz : LeafFeasible lo hi z)
    (hcheck : checkAt threshold lo hi certificate = true) :
    z tVar ≤ threshold := by
  have ha : AcceptedAt threshold lo hi certificate := of_decide_eq_true hcheck
  rcases ha with ⟨hmu, ht, hp, hbound, hthreshold⟩
  have hdual := linear_dual_upper_bound_finite
    (expandedCoeff lo hi certificate) (expandedRhs lo hi certificate)
    (equalityCoeff certificate) (equalityRhs certificate)
    objective z (expandedWeight lo hi certificate) (equalityWeight certificate)
    (LeafFeasible.expandedSparse (certificate := certificate) hz)
    (LeafFeasible.equalitySparse (certificate := certificate) hz)
    (expandedWeight_nonnegative hmu)
    (coefficient_identity lo hi certificate ht hp)
  have hobjective : finiteDot objective z = z tVar := by
    simp [finiteDot, objective]
  rw [hobjective] at hdual
  rw [expanded_bound_eq_recomputedBound] at hdual
  rw [← hbound] at hdual
  exact hdual.trans hthreshold

#print axioms checkAt_sound

end PeaceableQueens.UpperBound.SparseListDualLeaf
