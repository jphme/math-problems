import PeaceableQueens.LowerBound
import PeaceableQueens.FiniteGeometry

/-!
# The two small boards needed by the general endpoint

The `2 × 2` board has no nonattacking pair. On the `4 × 4` board, translate
one black queen to the origin: only four cells remain available to white.
Each of their four three-element subsets leaves at most two cells for black.
Both finite lemmas use kernel `decide`; neither
adds a native-computation axiom. The optional table lives in `Values.lean`.

These are the `q = 1,2` conclusions of paper `prop:small-even`.
-/

namespace PeaceableQueens

theorem H_one : H 1 = 0 := by decide
set_option maxRecDepth 10000 in
theorem H_two : H 2 = 2 := by decide

private theorem sharesLine_two : ∀ b w : Cell 2, SharesLine b w := by decide

theorem t_two : t 2 = H 1 := by
  rw [H_one]
  apply Nat.eq_zero_of_not_pos
  intro ht
  obtain ⟨B, W, hpeace, hB, hW⟩ := hasPeaceable_t 2
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < W.card by omega)
  exact hpeace b hb w hw (sharesLine_two b w)

/-- Cells available to the opposite army after fixing a black subset. -/
def availableCells {n : ℕ} [NeZero n] (B : Finset (Cell n)) : Finset (Cell n) :=
  Finset.univ.filter fun w => ∀ b ∈ B, ¬ SharesLine b w

private theorem three_cells_four :
    ∀ B ∈ (availableCells ({(0, 0)} : Finset (Cell 4))).powersetCard 3,
      (availableCells B).card ≤ 2 := by
  have htriples : (availableCells ({(0, 0)} : Finset (Cell 4))).powersetCard 3 =
      { {(1, 2), (2, 1), (2, 3)}, {(1, 2), (2, 1), (3, 2)},
        {(1, 2), (2, 3), (3, 2)}, {(2, 1), (2, 3), (3, 2)} } := by decide
  intro B hB
  rw [htriples] at hB
  simp only [Finset.mem_insert, Finset.mem_singleton] at hB
  rcases hB with rfl | rfl | rfl | rfl <;> decide

theorem t_four : t 4 = H 2 := by
  apply le_antisymm
  · rw [H_two]
    by_contra! hlarge
    obtain ⟨B, W, hpeace, hB, hW⟩ := hasPeaceable_t 4
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
    let e := BoardEquiv.translation (-b.1, -b.2)
    let B' := B.image e.toEquiv
    let W' := W.image e.toEquiv
    have hp : IsPeaceable B' W' := e.isPeaceable_image hpeace
    have hBc : B'.card = B.card := e.card_image B
    have hWc : W'.card = W.card := e.card_image W
    have hzero : (0, 0) ∈ B' := by
      apply Finset.mem_image.mpr
      refine ⟨b, hb, ?_⟩
      change (b.1 + -b.1, b.2 + -b.2) = (0, 0)
      simp
    have hWsub : W' ⊆ availableCells ({(0, 0)} : Finset (Cell 4)) := by
      intro w hw
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro z hz
      have hz0 : z = (0, 0) := Finset.mem_singleton.mp hz
      simpa only [hz0] using hp (0, 0) hzero w hw
    obtain ⟨S, hSW, hS⟩ := Finset.exists_subset_card_eq (show 3 ≤ W'.card by omega)
    have hsmall := three_cells_four S (Finset.mem_powersetCard.mpr ⟨hSW.trans hWsub, hS⟩)
    have hBsub : B' ⊆ availableCells S := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun w hw hline =>
        hp z hz w (hSW hw) hline.symm⟩
    have := (Finset.card_le_card hBsub).trans hsmall
    omega
  · exact H_le_t 2 (by decide)

#print axioms t_two
#print axioms t_four

end PeaceableQueens
