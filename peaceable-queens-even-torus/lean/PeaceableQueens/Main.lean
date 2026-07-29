import PeaceableQueens.Defs
import PeaceableQueens.LowerBound
import PeaceableQueens.LineColouring
import PeaceableQueens.Values

/-!
# The even-torus theorem: statement and formalized part

Theorem 1 of the paper states `t (2*q) = H q` for every `q ≥ 1` (in the
paper's notation, `t(2q) = H(2q)`).  Its proof splits into

* the **lower bound** `H q ≤ t (2*q)` — the parity-separated construction,
  formalized here in full for every `q` (`PeaceableQueens.H_le_t`); and
* the **upper bound** `t (2*q) ≤ H q` — proved in the paper by an exact
  moment relaxation, two rational branch certificates, an algebraic finish
  for `q ≥ 130` and an exact finite computation for `q ≤ 129`.  This half is
  *not* formalized; `FORMAL_PROOF.md` specifies it as precise finite
  statements suitable for a verified-checker formalization.

`evenTorusTheorem_of_upperBound` isolates the exact missing statement: the
theorem follows from this development once the upper bound is provided.
`PeaceableQueens.Values` proves unconditional small instances of Theorem 1,
upper bound included, by exhaustive decision over the line-colouring space.
-/

namespace PeaceableQueens

/-- Theorem 1 of the paper: `t(2q) = H(2q)` for every positive `q`. -/
def EvenTorusTheorem : Prop := ∀ q : ℕ, 0 < q → t (2 * q) = H q

/-- The upper bound `t(2q) ≤ H(2q)` — established in the paper by exact
certificates and computation (Sections 3–6), not formalized here. -/
def UpperBoundStatement : Prop := ∀ q : ℕ, 0 < q → t (2 * q) ≤ H q

/-- The even-torus theorem follows from this formalization together with the
upper bound: the lower bound `H_le_t` is proved here for every `q`. -/
theorem evenTorusTheorem_of_upperBound (upper : UpperBoundStatement) :
    EvenTorusTheorem :=
  fun q hq => le_antisymm (upper q hq) (H_le_t q hq)

end PeaceableQueens
