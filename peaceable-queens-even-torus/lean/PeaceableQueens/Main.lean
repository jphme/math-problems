import PeaceableQueens.UpperBound.Assembly
import PeaceableQueens.UpperBound.Generated.FiniteRange

/-!
# The even-torus theorem

The main theorem (`thm:main`) of the paper states `t (2*q) = H q` for every `q ≥ 1` (in the
paper's notation, `t(2q) = H(2q)`).  Its proof splits into

* the **lower bound** `H q ≤ t (2*q)` — the parity-separated construction,
  formalized here in full for every `q` (`PeaceableQueens.H_le_t`); and
* the **upper bound** `t (2*q) ≤ H q` — proved in the paper by an exact
  moment relaxation, two rational branch certificates, an algebraic finish
  for `q ≥ 130` and an exact finite computation for `q ≤ 129`.  This half is
  assembled here from the checked finite and large-order certificates.

`evenTorusTheorem_of_upperBound` remains available as a compatibility lemma.
`PeaceableQueens.SmallBoards` proves the two base cases with a translated
small-board argument and kernel decisions. The optional table and named
consequences live in `Values` and `Corollaries`.
-/

namespace PeaceableQueens

/-- The certificate-backed upper bound for every positive even order. -/
theorem upperBoundStatement : UpperBoundStatement :=
  UpperBound.Assembly.upperBoundStatement_of_finite
    UpperBound.Generated.Finite.finite_range_bound

/-- The parity-separated construction is optimal for every positive even order. -/
theorem evenTorusTheorem :
    EvenTorusTheorem :=
  evenTorusTheorem_of_upperBound upperBoundStatement

end PeaceableQueens

#print axioms PeaceableQueens.upperBoundStatement
#print axioms PeaceableQueens.evenTorusTheorem
