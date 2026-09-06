import PeaceableQueens.UpperBound.CertificateCore

/-!
# The concrete 42-row moment model

Paper `lem:moments` and the rows of `def:OPT` (S27).  This file defines the finite index types and exact coefficient matrix used by
the upper-bound certificates.  The definitions are semantic rather than a
trusted transcription of the JSON arrays: rows are built from parity blocks
and Boolean line-colour atoms.  A generator translating released certificate
indices must map into these constructors.

There are four parity blocks, sixteen atoms per block, ten ordinary moment
rows per block, and two aggregated diagonal/antidiagonal rows.  Thus the model
has 64 atom columns and 42 equality rows.  The D/A rows are deliberately
aggregated across the two blocks of a fixed square parity; per-block D/A
factorization is false on even tori.
-/

namespace PeaceableQueens.UpperBound.MomentModel

/-- A parity class. -/
abbrev Parity := Fin 2

/-- The four line families, in released coordinate order `R,C,D,A`. -/
inductive Family
  | row | column | diagonal | antidiagonal
  deriving DecidableEq, Fintype, Repr

/-- One of the eight normalized outer-count coordinates. -/
structure OuterCoord where
  family : Family
  parity : Parity
  deriving DecidableEq, Fintype, Repr

/-- A row/column parity block. -/
structure Block where
  rowParity : Parity
  columnParity : Parity
  deriving DecidableEq, Fintype, Repr

/-- Square parity in a row/column parity block. -/
def Block.squareParity (block : Block) : Parity :=
  ⟨(block.rowParity.val + block.columnParity.val) % 2, by omega⟩

/-- A Boolean atom records membership in the four line sets `R,C,D,A`. -/
structure Atom where
  row : Bool
  column : Bool
  diagonal : Bool
  antidiagonal : Bool
  deriving DecidableEq, Fintype, Repr

/-- One atom column in one parity block. -/
structure InnerAtom where
  block : Block
  atom : Atom
  deriving DecidableEq, Fintype, Repr

/-- The ten per-block moments.  D/A is absent here and appears only in the
aggregated rows below. -/
inductive BlockMoment
  | normalization
  | row | column | diagonal | antidiagonal
  | rowColumn | rowDiagonal | rowAntidiagonal
  | columnDiagonal | columnAntidiagonal
  deriving DecidableEq, Fintype, Repr

/-- Forty per-block rows plus the two aggregated D/A rows. -/
inductive MomentRow
  | block (parityBlock : Block) (moment : BlockMoment)
  | aggregateDA (parity : Parity)
  deriving DecidableEq, Fintype, Repr

/-- The all-white atom. -/
def whiteAtom : Atom := ⟨false, false, false, false⟩

/-- The all-black atom. -/
def blackAtom : Atom := ⟨true, true, true, true⟩

theorem blackAtom_ne_whiteAtom : blackAtom ≠ whiteAtom := by decide

/-- Evaluate a per-block Boolean moment on an atom. -/
def BlockMoment.eval : BlockMoment → Atom → Bool
  | .normalization, _ => true
  | .row, atom => atom.row
  | .column, atom => atom.column
  | .diagonal, atom => atom.diagonal
  | .antidiagonal, atom => atom.antidiagonal
  | .rowColumn, atom => atom.row && atom.column
  | .rowDiagonal, atom => atom.row && atom.diagonal
  | .rowAntidiagonal, atom => atom.row && atom.antidiagonal
  | .columnDiagonal, atom => atom.column && atom.diagonal
  | .columnAntidiagonal, atom => atom.column && atom.antidiagonal

/-- Exact `0/1` coefficient of an atom column in one of the 42 rows. -/
def coefficient (row : MomentRow) (inner : InnerAtom) : ℚ :=
  match row with
  | .block block moment =>
      if inner.block = block && moment.eval inner.atom then 1 else 0
  | .aggregateDA parity =>
      if inner.block.squareParity = parity &&
          inner.atom.diagonal && inner.atom.antidiagonal then 1 else 0

/-- Symbolic right-hand sides of the moment equations. -/
inductive RhsTerm
  | one
  | linear (coord : OuterCoord)
  | product (factor : ℚ) (left right : OuterCoord)
  deriving DecidableEq, Repr

/-- Evaluate a symbolic right-hand side at a normalized profile. -/
def RhsTerm.eval (profile : OuterCoord → ℚ) : RhsTerm → ℚ
  | .one => 1
  | .linear coord => profile coord
  | .product factor left right => factor * profile left * profile right

/-- Outer coordinate used by a family in a parity block. -/
def blockCoord (block : Block) : Family → OuterCoord
  | .row => ⟨.row, block.rowParity⟩
  | .column => ⟨.column, block.columnParity⟩
  | .diagonal => ⟨.diagonal, block.squareParity⟩
  | .antidiagonal => ⟨.antidiagonal, block.squareParity⟩

/-- Symbolic right-hand side for each of the 42 rows. -/
def rhsTerm : MomentRow → RhsTerm
  | .block _ .normalization => .one
  | .block block .row => .linear (blockCoord block .row)
  | .block block .column => .linear (blockCoord block .column)
  | .block block .diagonal => .linear (blockCoord block .diagonal)
  | .block block .antidiagonal => .linear (blockCoord block .antidiagonal)
  | .block block .rowColumn =>
      .product 1 (blockCoord block .row) (blockCoord block .column)
  | .block block .rowDiagonal =>
      .product 1 (blockCoord block .row) (blockCoord block .diagonal)
  | .block block .rowAntidiagonal =>
      .product 1 (blockCoord block .row) (blockCoord block .antidiagonal)
  | .block block .columnDiagonal =>
      .product 1 (blockCoord block .column) (blockCoord block .diagonal)
  | .block block .columnAntidiagonal =>
      .product 1 (blockCoord block .column) (blockCoord block .antidiagonal)
  | .aggregateDA parity =>
      .product 2 ⟨.diagonal, parity⟩ ⟨.antidiagonal, parity⟩

/-- Concrete moment-matrix row as a rational vector. -/
def matrixRow (row : MomentRow) : InnerAtom → ℚ := coefficient row

/-- Concrete moment right-hand side at a profile. -/
def rhs (profile : OuterCoord → ℚ) (row : MomentRow) : ℚ :=
  (rhsTerm row).eval profile

/-- An atom-weight vector satisfies the concrete 42 moment equations. -/
def SatisfiesMoments (profile : OuterCoord → ℚ) (weights : InnerAtom → ℚ) : Prop :=
  ∀ row, ∑ inner, matrixRow row inner * weights inner = rhs profile row

/-- Nonnegativity of all atom weights. -/
def Nonnegative (weights : InnerAtom → ℚ) : Prop := ∀ inner, 0 ≤ weights inner

/-- Total mass of a specified atom across the four parity blocks. -/
def atomTotal (weights : InnerAtom → ℚ) (atom : Atom) : ℚ :=
  ∑ inner, if inner.atom = atom then weights inner else 0

/-- Normalized black-cell mass. -/
def blackTotal (weights : InnerAtom → ℚ) : ℚ := atomTotal weights blackAtom

/-- Normalized white-cell mass. -/
def whiteTotal (weights : InnerAtom → ℚ) : ℚ := atomTotal weights whiteAtom

/-- The concrete model has exactly the dimensions claimed in S27. -/
theorem card_outerCoord : Fintype.card OuterCoord = 8 := by decide
theorem card_block : Fintype.card Block = 4 := by decide
theorem card_atom : Fintype.card Atom = 16 := by decide
theorem card_innerAtom : Fintype.card InnerAtom = 64 := by decide
theorem card_blockMoment : Fintype.card BlockMoment = 10 := by decide
theorem card_momentRow : Fintype.card MomentRow = 42 := by decide

/-- The two objective atoms are distinct at every block. -/
theorem inner_black_ne_white (block : Block) :
    (InnerAtom.mk block blackAtom) ≠ InnerAtom.mk block whiteAtom := by
  intro h
  exact blackAtom_ne_whiteAtom (congrArg InnerAtom.atom h)

#print axioms card_momentRow

end PeaceableQueens.UpperBound.MomentModel
