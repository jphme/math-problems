import PeaceableQueens.UpperBound.CertificateCore

/-!
# Decidable empty and exceptional leaf checks

These are the exact endpoint tests used by the released branch-certificate
checker.  Their soundness is proved independently of any certificate data.
-/

namespace PeaceableQueens.UpperBound.LeafChecks

abbrev Profile := RatVec 8
abbrev ProfileBox := RatBox 8

/-- The five canonical-chamber inequalities in released coordinate order
`r0,r1,c0,c1,d0,d1,a0,a1`. -/
def InChamber (x : Profile) : Prop :=
  x 0 ≤ x 1 ∧
  x 2 ≤ x 3 ∧
  x 0 + x 1 ≤ x 2 + x 3 ∧
  x 4 + x 5 ≤ x 6 + x 7 ∧
  x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 ≤ 4

inductive EmptyReason
  | rowSort | columnSort | rowColumnSum | diagonalSum | budget
  deriving DecidableEq, Repr

private def row1Min (box : ProfileBox) := max (box.lower 1) (box.lower 0)
private def rowSumMin (box : ProfileBox) := box.lower 0 + row1Min box
private def column1Min (box : ProfileBox) := max (box.lower 3) (box.lower 2)
private def columnBaseMin (box : ProfileBox) := box.lower 2 + column1Min box
private def columnSumMax (box : ProfileBox) := box.upper 3 + min (box.upper 2) (box.upper 3)
private def columnNeed (box : ProfileBox) := max (columnBaseMin box) (rowSumMin box)
private def diagonalSumMin (box : ProfileBox) := box.lower 4 + box.lower 5
private def antidiagonalBaseMin (box : ProfileBox) := box.lower 6 + box.lower 7
private def antidiagonalSumMax (box : ProfileBox) := box.upper 6 + box.upper 7
private def antidiagonalNeed (box : ProfileBox) :=
  max (antidiagonalBaseMin box) (diagonalSumMin box)

/-- Exact proposition tested for each empty-leaf reason. -/
def EmptyReason.holds (reason : EmptyReason) (box : ProfileBox) : Prop :=
  match reason with
  | .rowSort => row1Min box > box.upper 1
  | .columnSort => column1Min box > box.upper 3
  | .rowColumnSum => columnNeed box > columnSumMax box
  | .diagonalSum => antidiagonalNeed box > antidiagonalSumMax box
  | .budget =>
      rowSumMin box + columnNeed box + diagonalSumMin box +
          antidiagonalNeed box > 4

instance (reason : EmptyReason) (box : ProfileBox) : Decidable (reason.holds box) :=
  by
    unfold EmptyReason.holds
    cases reason <;> infer_instance

/-- Boolean empty-leaf checker suitable for generated certificate data. -/
def checkEmpty (reason : EmptyReason) (box : ProfileBox) : Bool :=
  decide (reason.holds box)

private theorem rowSumMin_le {box : ProfileBox} {x : Profile}
    (hx : box.Contains x) (hc : InChamber x) :
    rowSumMin box ≤ x 0 + x 1 := by
  have hmax : row1Min box ≤ x 1 :=
    max_le (hx 1).1 ((hx 0).1.trans hc.1)
  exact add_le_add (hx 0).1 hmax

private theorem columnBaseMin_le {box : ProfileBox} {x : Profile}
    (hx : box.Contains x) (hc : InChamber x) :
    columnBaseMin box ≤ x 2 + x 3 := by
  have hmax : column1Min box ≤ x 3 :=
    max_le (hx 3).1 ((hx 2).1.trans hc.2.1)
  exact add_le_add (hx 2).1 hmax

private theorem columnNeed_le {box : ProfileBox} {x : Profile}
    (hx : box.Contains x) (hc : InChamber x) :
    columnNeed box ≤ x 2 + x 3 := by
  exact max_le (columnBaseMin_le hx hc) ((rowSumMin_le hx hc).trans hc.2.2.1)

private theorem columnSum_le_max {box : ProfileBox} {x : Profile}
    (hx : box.Contains x) (hc : InChamber x) :
    x 2 + x 3 ≤ columnSumMax box := by
  have hxmin : x 2 ≤ min (box.upper 2) (box.upper 3) :=
    le_min (hx 2).2 (hc.2.1.trans (hx 3).2)
  calc
    x 2 + x 3 ≤ min (box.upper 2) (box.upper 3) + box.upper 3 :=
      add_le_add hxmin (hx 3).2
    _ = columnSumMax box := add_comm _ _

private theorem antidiagonalNeed_le {box : ProfileBox} {x : Profile}
    (hx : box.Contains x) (hc : InChamber x) :
    antidiagonalNeed box ≤ x 6 + x 7 := by
  apply max_le
  · exact add_le_add (hx 6).1 (hx 7).1
  · exact (add_le_add (hx 4).1 (hx 5).1).trans hc.2.2.2.1

/-- Acceptance of an empty-leaf reason (the five exact empty leaves of paper
Section `sec:cert`) proves that no point of the box lies in the canonical
chamber. -/
theorem checkEmpty_sound (reason : EmptyReason) (box : ProfileBox)
    (hcheck : checkEmpty reason box = true) :
    ∀ x, box.Contains x → InChamber x → False := by
  have hh : reason.holds box := of_decide_eq_true hcheck
  intro x hx hc
  rcases hc with ⟨hr, hcSort, hrc, hda, hbudget⟩
  have hcFull : InChamber x := ⟨hr, hcSort, hrc, hda, hbudget⟩
  cases reason with
  | rowSort =>
      exact (not_lt_of_ge
        ((max_le (hx 1).1 ((hx 0).1.trans hr)).trans (hx 1).2)) hh
  | columnSort =>
      exact (not_lt_of_ge
        ((max_le (hx 3).1 ((hx 2).1.trans hcSort)).trans (hx 3).2)) hh
  | rowColumnSum =>
      exact (not_lt_of_ge ((columnNeed_le hx hcFull).trans
        (columnSum_le_max hx hcFull))) hh
  | diagonalSum =>
      exact (not_lt_of_ge ((antidiagonalNeed_le hx hcFull).trans
        (add_le_add (hx 6).2 (hx 7).2))) hh
  | budget =>
      have hrMin := rowSumMin_le hx hcFull
      have hcMin := columnNeed_le hx hcFull
      have hdMin : diagonalSumMin box ≤ x 4 + x 5 :=
        add_le_add (hx 4).1 (hx 5).1
      have haMin := antidiagonalNeed_le hx hcFull
      have htotal :
          rowSumMin box + columnNeed box + diagonalSumMin box +
              antidiagonalNeed box ≤
            x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 := by
        linarith
      exact (not_lt_of_ge (htotal.trans hbudget)) hh

/-! ## Exceptional regions -/

inductive TemplateValue
  | zero | variable | one
  deriving DecidableEq, Repr

/-- The four rational plaid templates, selected by square parity and row
parity. -/
def templateValue (squareParity rowParity : Fin 2) (coord : Fin 8) : TemplateValue :=
  let columnParity : Fin 2 :=
    ⟨(rowParity.val + squareParity.val) % 2, by omega⟩
  if coord.val = rowParity.val then .variable
  else if coord.val = 2 + columnParity.val then .variable
  else if coord.val = 4 + squareParity.val then .one
  else if coord.val = 6 + squareParity.val then .one
  else .zero

/-- A whole box lies in one of the four rational plaid neighbourhoods. -/
def InPlaidBox (squareParity rowParity : Fin 2) (box : ProfileBox) : Prop :=
  ∀ coord,
    match templateValue squareParity rowParity coord with
    | .zero => box.upper coord ≤ 1 / 10
    | .variable => 3 / 5 ≤ box.lower coord ∧ box.upper coord ≤ 7 / 8
    | .one => 19 / 20 ≤ box.lower coord

instance (squareParity rowParity : Fin 2) (box : ProfileBox) :
    Decidable (InPlaidBox squareParity rowParity box) := by
  let predicate : Fin 8 → Prop := fun coord =>
    match templateValue squareParity rowParity coord with
    | .zero => box.upper coord ≤ 1 / 10
    | .variable => 3 / 5 ≤ box.lower coord ∧ box.upper coord ≤ 7 / 8
    | .one => 19 / 20 ≤ box.lower coord
  have hp : DecidablePred predicate := by
    intro coord
    cases h : templateValue squareParity rowParity coord <;>
      simp [predicate, h] <;> infer_instance
  change Decidable (∀ coord, predicate coord)
  exact Fintype.decidableForallFintype

def checkPlaid (squareParity rowParity : Fin 2) (box : ProfileBox) : Bool :=
  decide (InPlaidBox squareParity rowParity box)

theorem checkPlaid_sound (squareParity rowParity : Fin 2) (box : ProfileBox)
    (hcheck : checkPlaid squareParity rowParity box = true) :
    InPlaidBox squareParity rowParity box := of_decide_eq_true hcheck

/-- Pointwise form of a rational plaid neighbourhood. -/
def InPlaid (squareParity rowParity : Fin 2) (x : Profile) : Prop :=
  ∀ coord,
    match templateValue squareParity rowParity coord with
    | .zero => x coord ≤ 1 / 10
    | .variable => 3 / 5 ≤ x coord ∧ x coord ≤ 7 / 8
    | .one => 19 / 20 ≤ x coord

theorem checkPlaid_contains (squareParity rowParity : Fin 2) (box : ProfileBox)
    (hcheck : checkPlaid squareParity rowParity box = true) :
    ∀ x, box.Contains x → InPlaid squareParity rowParity x := by
  have hb := checkPlaid_sound squareParity rowParity box hcheck
  intro x hx coord
  have hcoord := hb coord
  cases h : templateValue squareParity rowParity coord <;>
    simp only [h] at hcoord ⊢
  · exact (hx coord).2.trans hcoord
  · exact ⟨hcoord.1.trans (hx coord).1, (hx coord).2.trans hcoord.2⟩
  · exact hcoord.trans (hx coord).1

/-- Aggregate local core used by the second branch certificate. -/
def InCore (x : Profile) : Prop :=
  36 / 25 ≤ x 1 + x 3 ∧
  x 1 + x 3 ≤ 37 / 25 ∧
  x 0 + x 2 ≤ 9 / 100 ∧
  x 5 + x 7 ≤ 9 / 200 ∧
  49 / 25 ≤ x 4 + x 6

/-- Endpoint test that a whole box is contained in the aggregate core. -/
def CoreBox (box : ProfileBox) : Prop :=
  36 / 25 ≤ box.lower 1 + box.lower 3 ∧
  box.upper 1 + box.upper 3 ≤ 37 / 25 ∧
  box.upper 0 + box.upper 2 ≤ 9 / 100 ∧
  box.upper 5 + box.upper 7 ≤ 9 / 200 ∧
  49 / 25 ≤ box.lower 4 + box.lower 6

instance (box : ProfileBox) : Decidable (CoreBox box) := by
  unfold CoreBox
  infer_instance

def checkCore (box : ProfileBox) : Bool := decide (CoreBox box)

theorem checkCore_sound (box : ProfileBox) (hcheck : checkCore box = true) :
    ∀ x, box.Contains x → InCore x := by
  have hc : CoreBox box := of_decide_eq_true hcheck
  intro x hx
  rcases hc with ⟨hlower, hupper, hsmall, hdefect, hnearOne⟩
  constructor
  · exact hlower.trans (add_le_add (hx 1).1 (hx 3).1)
  constructor
  · exact (add_le_add (hx 1).2 (hx 3).2).trans hupper
  constructor
  · exact (add_le_add (hx 0).2 (hx 2).2).trans hsmall
  constructor
  · exact (add_le_add (hx 5).2 (hx 7).2).trans hdefect
  · exact hnearOne.trans (add_le_add (hx 4).1 (hx 6).1)

#print axioms checkEmpty_sound
#print axioms checkPlaid_contains
#print axioms checkCore_sound

end PeaceableQueens.UpperBound.LeafChecks
