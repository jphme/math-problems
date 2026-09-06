import PeaceableQueens.UpperBound.CertificateCore
import PeaceableQueens.UpperBound.LeafChecks

/-!
# Checked split nodes for the branch certificates

Paper `lem:branchsound` (S35), split step.  The two released branch trees are
compiled bottom-up in small generated modules: every internal node is checked
locally by `splitNodeOK`, and `splitNodeOK_coverTree` combines two already
certified child trees into the parent `CoverTree`.  Since a generated parent
module may only import modules containing larger child indices, the Lean
module graph itself rules out cycles; no array traversal is on the trust path.
-/

namespace PeaceableQueens.UpperBound.BranchCertificate

abbrev ProfileBox := RatBox 8

def leftBox (box : ProfileBox) (d : Fin 8) (cut : ℚ) : ProfileBox :=
  { lower := box.lower
    upper := fun i => if i = d then cut else box.upper i }

def rightBox (box : ProfileBox) (d : Fin 8) (cut : ℚ) : ProfileBox :=
  { lower := fun i => if i = d then cut else box.lower i
    upper := box.upper }

/-- The two closed children `x_d ≤ cut` and `x_d ≥ cut` cover the parent box
(paper `lem:branchsound`: the overlap on the cutting hyperplane is harmless). -/
theorem splitCover (box : ProfileBox) (d : Fin 8) (cut : ℚ) :
    ∀ x, box.Contains x →
      (leftBox box d cut).Contains x ∨ (rightBox box d cut).Contains x := by
  intro x hx
  by_cases h : x d ≤ cut
  · left
    intro i
    by_cases hi : i = d
    · subst i
      simpa [leftBox] using (And.intro (hx d).1 h)
    · simp [leftBox, hi]
      exact hx i
  · right
    have hc : cut ≤ x d := le_of_not_ge h
    intro i
    by_cases hi : i = d
    · subst i
      simpa [rightBox] using (And.intro hc (hx d).2)
    · simp [rightBox, hi]
      exact hx i

def boxEq (a b : ProfileBox) : Bool :=
  decide (∀ i : Fin 8, a.lower i = b.lower i ∧ a.upper i = b.upper i)

theorem boxEq_iff (a b : ProfileBox) :
    boxEq a b = true ↔ ∀ i : Fin 8, a.lower i = b.lower i ∧ a.upper i = b.upper i := by
  simp [boxEq]

/-- The complete local check for one internal node: the cut is strictly inside
the parent interval and the two stored child boxes are exactly the two halves. -/
def splitNodeOK (box left right : ProfileBox) (d : Fin 8) (cut : ℚ) : Bool :=
  decide (box.lower d < cut) &&
  decide (cut < box.upper d) &&
  boxEq left (leftBox box d cut) &&
  boxEq right (rightBox box d cut)

/-- A locally accepted split and two proof-carrying child trees produce the
parent tree.  The strict-cut checks are retained as part of the fail-closed
certificate format even though coverage itself needs only the two box checks. -/
theorem splitNodeOK_coverTree
    (Safe Exceptional : ProfileBox → Prop)
    (box left right : ProfileBox) (d : Fin 8) (cut : ℚ)
    (hcheck : splitNodeOK box left right d cut = true)
    (hleft : Nonempty (CoverTree Safe Exceptional left))
    (hright : Nonempty (CoverTree Safe Exceptional right)) :
    Nonempty (CoverTree Safe Exceptional box) := by
  have hlast := Bool.and_eq_true_iff.mp hcheck
  have hpenultimate := Bool.and_eq_true_iff.mp hlast.1
  have hleftCheck := hpenultimate.2
  have hrightCheck := hlast.2
  rcases hleft with ⟨leftTree⟩
  rcases hright with ⟨rightTree⟩
  have hleftBox := (boxEq_iff left (leftBox box d cut)).mp hleftCheck
  have hrightBox := (boxEq_iff right (rightBox box d cut)).mp hrightCheck
  refine ⟨CoverTree.split ?_ leftTree rightTree⟩
  intro x hx
  rcases splitCover box d cut x hx with h | h
  · left
    intro i
    constructor
    · rw [(hleftBox i).1]
      exact (h i).1
    · rw [(hleftBox i).2]
      exact (h i).2
  · right
    intro i
    constructor
    · rw [(hrightBox i).1]
      exact (h i).1
    · rw [(hrightBox i).2]
      exact (h i).2

end PeaceableQueens.UpperBound.BranchCertificate

#print axioms PeaceableQueens.UpperBound.BranchCertificate.splitCover
#print axioms PeaceableQueens.UpperBound.BranchCertificate.splitNodeOK_coverTree
