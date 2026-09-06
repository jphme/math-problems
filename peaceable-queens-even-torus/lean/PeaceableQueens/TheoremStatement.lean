import PeaceableQueens.Defs
import PeaceableQueens.LowerBound
import PeaceableQueens.LineColouring

/-!
# Statements of the even-torus theorem

This module keeps the public propositions and the lower-bound assembly lemma
independent of the computational upper-bound certificates. `PeaceableQueens.Main`
provides the unconditional endpoints after importing the checked certificates.
-/

namespace PeaceableQueens

/-- the main theorem (`thm:main`) of the paper: `t(2q) = H(2q)` for every positive `q`.
The paper's `H(2q)` is called `H q` in this development. -/
def EvenTorusTheorem : Prop := ∀ q : ℕ, 0 < q → t (2 * q) = H q

/-- The upper-bound half of the even-torus theorem. -/
def UpperBoundStatement : Prop := ∀ q : ℕ, 0 < q → t (2 * q) ≤ H q

/-- Combine any proof of the upper bound with the parity-separated
construction, retaining the original public compatibility lemma. -/
theorem evenTorusTheorem_of_upperBound (upper : UpperBoundStatement) :
    EvenTorusTheorem :=
  fun q hq => le_antisymm (upper q hq) (H_le_t q hq)

end PeaceableQueens
