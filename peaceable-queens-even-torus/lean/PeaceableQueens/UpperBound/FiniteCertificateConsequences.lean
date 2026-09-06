import PeaceableQueens.UpperBound.CertificateConsequences
import PeaceableQueens.UpperBound.FiniteCutTable

/-!
# Configuration consequence of a checked finite discharge tree

This file is the bridge (paper `lem:boxsound` and `prop:ladder`, S57--S59)
from the integer-profile search to the original peaceable-queens objective.  The concrete per-order certificates only need to
supply an accepted action tree; the support-dual hypotheses are shared by all
orders.
-/

namespace PeaceableQueens.UpperBound.FiniteCertificateConsequences

open ConfigurationBridge CertificateConsequences
open FiniteLattice FiniteCertificates

/-- The eight unnormalized integer profile coordinates used by the finite
box search. -/
def countPoint (cfg : Configuration q) : Point 8 :=
  fun i => (outerCount cfg (outerOfFlat i) : Int)

lemma countPoint_mem_fullBox (cfg : Configuration q) (hq : 0 < q) :
    (fullBox 8 q).Contains (countPoint cfg) := by
  intro i
  have hupper := outerCount_le cfg hq (outerOfFlat i)
  constructor
  · simp [fullBox, countPoint]
  · simp only [fullBox, countPoint]
    exact_mod_cast hupper

lemma chamber_countPoint_canonical (cfg : Configuration q)
    (hchamber : chamber q cfg) : Canonical q (countPoint cfg) := by
  rcases hchamber with ⟨hr, hc, hrc, hda, hbudget⟩
  intro row
  fin_cases row <;>
    simp [domainRows, Row.Satisfied, FiniteLattice.dot, countPoint, outerOfFlat,
      Fin.sum_univ_succ] <;>
    try omega
  unfold totalLineCount at hbudget
  have hR := outerCount_pair_sum cfg .row
  have hC := outerCount_pair_sum cfg .column
  have hD := outerCount_pair_sum cfg .diagonal
  have hA := outerCount_pair_sum cfg .antidiagonal
  simp at hR hC hD hA
  omega

/-- A checked finite tree plus the 76 support-dual consequences bounds the
objective of every canonical configuration at this order. -/
theorem configuration_bound_of_tree_at (q bound : ℕ) (hq : 0 < q)
    [NeZero (2 * q)]
    (tree : ActionCoverTree (Canonical q) (PrunedBy (domainRows q))
      (DischargedBy cutTable q (paperThreshold bound)) (fullBox 8 q))
    (cutSound : ∀ (c : Fin 76) (cfg : Configuration q),
      ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
        (cuts c).eval q (countPoint cfg))
    (cfg : Configuration q) (hchamber : chamber q cfg) :
    min cfg.blackCells.card cfg.whiteCells.card ≤ bound := by
  have hcanon := chamber_countPoint_canonical cfg hchamber
  rcases tree.canonical_discharge (canonical_rows q) hcanon
      (countPoint_mem_fullBox cfg hq) with ⟨leaf, hleaf, c, hcut⟩
  have hscaled :
      ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
        paperThreshold bound :=
    (cutSound c cfg).trans (hcut (countPoint cfg) hleaf)
  exact of_twelve_mul_le_paperThreshold hscaled

/-- The original S57 interface at the symbolic optimum. -/
theorem configuration_bound_of_tree (q : ℕ) (hq : 0 < q)
    [NeZero (2 * q)]
    (tree : ActionCoverTree (Canonical q) (PrunedBy (domainRows q))
      (DischargedBy cutTable q (paperThreshold (H q))) (fullBox 8 q))
    (cutSound : ∀ (c : Fin 76) (cfg : Configuration q),
      ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
        (cuts c).eval q (countPoint cfg))
    (cfg : Configuration q) (hchamber : chamber q cfg) :
    min cfg.blackCells.card cfg.whiteCells.card ≤ H q :=
  configuration_bound_of_tree_at q (H q) hq tree cutSound cfg hchamber

/-- Paper `lem:boxsound` with `prop:ladder`'s conclusion (S57--S59), using a
concrete threshold `bound` and a four-coordinate witness for `bound ≤ H q`.
This avoids evaluating the `(q+1)^4` profile maximum inside certificate replay.
The conclusion is still the original upper bound `t(2q) ≤ H(2q)`. -/
theorem finite_order_bound_of_tree_at (q bound : ℕ) (hq : 0 < q)
    [NeZero (2 * q)]
    (hbound : bound ≤ H q)
    (tree : ActionCoverTree (Canonical q) (PrunedBy (domainRows q))
      (DischargedBy cutTable q (paperThreshold bound)) (fullBox 8 q))
    (cutSound : ∀ (c : Fin 76) (cfg : Configuration q),
      ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
        (cuts c).eval q (countPoint cfg)) :
    t (2 * q) ≤ H q := by
  apply t_le_H_of_chamber_configuration q
  intro cfg hchamber
  exact (configuration_bound_of_tree_at q bound hq tree cutSound cfg hchamber).trans hbound

/-- S57 in the form consumed by the final finite-order assembly. -/
theorem finite_order_bound_of_tree (q : ℕ) (hq : 0 < q)
    [NeZero (2 * q)]
    (tree : ActionCoverTree (Canonical q) (PrunedBy (domainRows q))
      (DischargedBy cutTable q (paperThreshold (H q))) (fullBox 8 q))
    (cutSound : ∀ (c : Fin 76) (cfg : Configuration q),
      ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
        (cuts c).eval q (countPoint cfg)) :
    t (2 * q) ≤ H q := by
  apply t_le_H_of_chamber_configuration q
  intro cfg hchamber
  exact configuration_bound_of_tree q hq tree cutSound cfg hchamber

end PeaceableQueens.UpperBound.FiniteCertificateConsequences

#print axioms PeaceableQueens.UpperBound.FiniteCertificateConsequences.countPoint_mem_fullBox
#print axioms PeaceableQueens.UpperBound.FiniteCertificateConsequences.chamber_countPoint_canonical
#print axioms PeaceableQueens.UpperBound.FiniteCertificateConsequences.configuration_bound_of_tree
#print axioms PeaceableQueens.UpperBound.FiniteCertificateConsequences.configuration_bound_of_tree_at
#print axioms PeaceableQueens.UpperBound.FiniteCertificateConsequences.finite_order_bound_of_tree_at
#print axioms PeaceableQueens.UpperBound.FiniteCertificateConsequences.finite_order_bound_of_tree
