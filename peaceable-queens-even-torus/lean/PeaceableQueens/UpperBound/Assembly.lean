import PeaceableQueens.TheoremStatement
import PeaceableQueens.SmallBoards
import PeaceableQueens.UpperBound.CertificateConsequences
import PeaceableQueens.UpperBound.FiniteCertificateConsequences
import PeaceableQueens.UpperBound.LargeOrderCertified

/-!
# Final upper-bound assembly

The computational certificates enter only through the two hypotheses below:
the finite interval and the large-order branch certificates.  This theorem
also records explicitly that the already checked `q = 1,2` values close the
bottom of the range.
-/

namespace PeaceableQueens.UpperBound.Assembly

/-- Once the finite certificate family and the two large-order trees have
been checked, they cover every positive order without a gap. -/
theorem upperBoundStatement_of_components
    (hfinite : ∀ q : ℕ, 3 ≤ q → q ≤ 129 → t (2 * q) ≤ H q)
    (hlarge : ∀ q : ℕ, 130 ≤ q → t (2 * q) ≤ H q) :
    UpperBoundStatement := by
  intro q hq
  by_cases hsmall : q ≤ 2
  · interval_cases q
    · simpa using t_two.le
    · simpa using t_four.le
  · have hthree : 3 ≤ q := by omega
    by_cases hfiniteRange : q ≤ 129
    · exact hfinite q hthree hfiniteRange
    · exact hlarge q (by omega)

/-- The unconditional equality theorem follows immediately once the upper
bound endpoint has been assembled. -/
theorem evenTorusTheorem_of_components
    (hfinite : ∀ q : ℕ, 3 ≤ q → q ≤ 129 → t (2 * q) ≤ H q)
    (hlarge : ∀ q : ℕ, 130 ≤ q → t (2 * q) ≤ H q) :
    EvenTorusTheorem :=
  evenTorusTheorem_of_upperBound
    (upperBoundStatement_of_components hfinite hlarge)

/-- With the released large-order trees checked in Lean, only the finite
interval remains as an input to the final upper-bound statement. -/
theorem upperBoundStatement_of_finite
    (hfinite : ∀ q : ℕ, 3 ≤ q → q ≤ 129 → t (2 * q) ≤ H q) :
    UpperBoundStatement :=
  upperBoundStatement_of_components hfinite
    LargeOrderCertified.large_order_bound

/-- Equality at every positive even order, reduced solely to the finite
certificate family `3 ≤ q ≤ 129`. -/
theorem evenTorusTheorem_of_finite
    (hfinite : ∀ q : ℕ, 3 ≤ q → q ≤ 129 → t (2 * q) ≤ H q) :
    EvenTorusTheorem :=
  evenTorusTheorem_of_components hfinite
    LargeOrderCertified.large_order_bound

end PeaceableQueens.UpperBound.Assembly

#print axioms PeaceableQueens.UpperBound.Assembly.upperBoundStatement_of_components
#print axioms PeaceableQueens.UpperBound.Assembly.evenTorusTheorem_of_components
#print axioms PeaceableQueens.UpperBound.Assembly.upperBoundStatement_of_finite
#print axioms PeaceableQueens.UpperBound.Assembly.evenTorusTheorem_of_finite
