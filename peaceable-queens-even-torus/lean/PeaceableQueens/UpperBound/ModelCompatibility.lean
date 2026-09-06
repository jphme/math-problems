import PeaceableQueens.UpperBound.LPModel
import PeaceableQueens.UpperBound.MomentModel

/-!
# Semantic/flat moment-model compatibility

The certificate files use flat integer indices.  `MomentModel` uses semantic
constructors.  This module gives the explicit released-order decoding and
checks that every one of the 42 × 64 flat moment coefficients agrees with the
semantic definition.  No derived `Fintype` enumeration is trusted.
-/

namespace PeaceableQueens.UpperBound.ModelCompatibility

open MomentModel

def blockOfFlat (block : Fin 4) : Block :=
  ⟨LPModel.blockRow block, LPModel.blockCol block⟩

def atomOfFlat (atom : Fin 64) : Atom :=
  ⟨LPModel.bit atom 0, LPModel.bit atom 1,
    LPModel.bit atom 2, LPModel.bit atom 3⟩

def innerOfFlat (atom : Fin 64) : InnerAtom :=
  ⟨blockOfFlat (LPModel.blockOfAtom atom), atomOfFlat atom⟩

def blockMomentOfFlat (feature : Fin 10) : BlockMoment :=
  match feature.val with
  | 0 => .normalization
  | 1 => .row
  | 2 => .column
  | 3 => .diagonal
  | 4 => .antidiagonal
  | 5 => .rowColumn
  | 6 => .rowDiagonal
  | 7 => .rowAntidiagonal
  | 8 => .columnDiagonal
  | _ => .columnAntidiagonal

def rowOfFlat (row : Fin 42) : MomentRow :=
  if h : row.val < 40 then
    .block
      (blockOfFlat ⟨row.val / 10, by omega⟩)
      (blockMomentOfFlat ⟨row.val % 10, Nat.mod_lt _ (by omega)⟩)
  else
    .aggregateDA ⟨row.val - 40, by omega⟩

/-- Certificate-order index of a semantic outer coordinate. -/
def flatOfOuter : OuterCoord → Fin 8
  | ⟨.row, parity⟩ => ⟨parity, by omega⟩
  | ⟨.column, parity⟩ => ⟨2 + parity, by omega⟩
  | ⟨.diagonal, parity⟩ => ⟨4 + parity, by omega⟩
  | ⟨.antidiagonal, parity⟩ => ⟨6 + parity, by omega⟩

/-- Constant term of the semantic right-hand side. -/
def rhsConstant : RhsTerm → ℚ
  | .one => 1
  | .linear _ => 0
  | .product _ _ _ => 0

/-- Coefficient with which one of the 30 profile/product variables is moved
to the left-hand side of a semantic moment equation. -/
def rhsVariableCoeff (term : RhsTerm) (coordinate : Fin 30) : ℚ :=
  match term with
  | .one => 0
  | .linear coord =>
      if coordinate.val = (flatOfOuter coord).val then -1 else 0
  | .product factor left right =>
      if h : 8 ≤ coordinate.val then
        let product : Fin 22 := ⟨coordinate.val - 8, by omega⟩
        if LPModel.productPair product = (flatOfOuter left, flatOfOuter right)
          then -factor else 0
      else 0

/-- All 2,688 entries of the certificate-order matrix equal the independently
defined semantic coefficients.  `decide` performs kernel reduction over the
closed finite index space. -/
theorem moment_coefficients_compatible :
    ∀ row atom,
      LPModel.momentCoeff row atom =
        MomentModel.coefficient (rowOfFlat row) (innerOfFlat atom) := by
  decide

/-- The constant side of all 42 flat equations agrees with the semantic
right-hand-side constructor. -/
theorem moment_rhs_constants_compatible :
    ∀ row,
      LPModel.eqRhs row = rhsConstant (MomentModel.rhsTerm (rowOfFlat row)) := by
  decide

/-- All 42 × 30 coefficients of the profile and product variables agree with
the semantic right-hand-side constructor, including the two aggregated D/A
rows with coefficient `-2`. -/
theorem moment_rhs_variables_compatible :
    ∀ row coordinate,
      LPModel.eqCoeff row ⟨coordinate.val, by omega⟩ =
        rhsVariableCoeff (MomentModel.rhsTerm (rowOfFlat row)) coordinate := by
  decide

#print axioms moment_coefficients_compatible
#print axioms moment_rhs_constants_compatible
#print axioms moment_rhs_variables_compatible

end PeaceableQueens.UpperBound.ModelCompatibility
