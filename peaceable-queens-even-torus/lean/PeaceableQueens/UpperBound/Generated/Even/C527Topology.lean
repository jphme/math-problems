import PeaceableQueens.UpperBound.BranchCertificate
import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even.C527
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.BranchCertificate

abbrev ProfileBox := RatBox 8

/-- Marker for the fail-closed bottom-up certificate representation.
Every generated split theorem checks strictness and both exact child boxes;
forward-only declaration dependencies make cycles or bad child indices fail. -/
def certifiedNodeCount : Nat := 6929

end PeaceableQueens.UpperBound.Generated.Even.C527
