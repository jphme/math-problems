import PeaceableQueens.UpperBound.Generated.Even.C527LeafDispatcher
import PeaceableQueens.UpperBound.Generated.Even.CoreLeafDispatcher

/-!
# Unconditional large-order certificate consequence

This module normalizes the two generated certificate roots to the semantic
roots used by `CertificateConsequences`, then discharges S55 without any
certificate hypothesis.
-/

namespace PeaceableQueens.UpperBound.LargeOrderCertified

open PeaceableQueens.UpperBound CertificateConsequences

theorem global_tree :
    Nonempty (CoverTree BranchSafe PlaidExceptional globalRoot) := by
  simpa [Generated.Even.C527.node_box_0, globalRoot] using
    Generated.Even.C527.checked_tree

theorem local_tree :
    Nonempty (CoverTree BranchSafe CoreExceptional localRoot) := by
  simpa [Generated.Even.Core.node_box_0, localRoot] using
    Generated.Even.Core.checked_tree

/-- Paper `thm:q130` (S55): every even order `2q` with `q ≥ 130` satisfies the
target upper bound, with both released branch-and-bound trees checked inside
Lean. -/
theorem large_order_bound (q : ℕ) (hq : 130 ≤ q) :
    t (2 * q) ≤ H q := by
  rcases global_tree with ⟨globalTree⟩
  rcases local_tree with ⟨localTree⟩
  exact large_order_bound_of_trees q hq globalTree localTree

end PeaceableQueens.UpperBound.LargeOrderCertified

#print axioms PeaceableQueens.UpperBound.LargeOrderCertified.global_tree
#print axioms PeaceableQueens.UpperBound.LargeOrderCertified.local_tree
#print axioms PeaceableQueens.UpperBound.LargeOrderCertified.large_order_bound
