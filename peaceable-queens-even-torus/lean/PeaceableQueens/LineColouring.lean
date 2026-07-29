import PeaceableQueens.Defs

/-!
# The line-colouring equivalence

This file proves Lemma 2 (`lem:lines`, "Line-colouring equivalence") of the
paper *Peaceable queens on even toroidal boards*
(`paper/peace_even_torus.tex`): a peaceable placement of `m` black and `m`
white queens on the `n × n` torus exists **iff** there are line sets
`R, C, D, A ⊆ ZMod n` (black rows, columns, diagonals, antidiagonals) with
`m ≤ |Bl(R,C,D,A)|` and `m ≤ |Wh(R,C,D,A)|`.

* `hasPeaceable_iff_lineSets` — the equivalence itself.
* `t_eq_lineMax` — the consequence `t n = max_{R,C,D,A} min (|Bl|, |Wh|)`
  stated in the paper right after the lemma ("the queens have disappeared");
  this makes `t` computable by finite enumeration, which
  `PeaceableQueens.Values` exploits for `n = 2, 4`.
-/

namespace PeaceableQueens

variable {n : ℕ} [NeZero n]

/-- Membership in `blackCells`, unfolded. -/
theorem mem_blackCells {R C D A : Finset (ZMod n)} {p : Cell n} :
    p ∈ blackCells R C D A ↔
      p.1 ∈ R ∧ p.2 ∈ C ∧ p.1 - p.2 ∈ D ∧ p.1 + p.2 ∈ A := by
  simp [blackCells]

/-- Membership in `whiteCells`, unfolded: all four line labels avoid the
black line sets. -/
theorem mem_whiteCells {R C D A : Finset (ZMod n)} {p : Cell n} :
    p ∈ whiteCells R C D A ↔
      p.1 ∉ R ∧ p.2 ∉ C ∧ p.1 - p.2 ∉ D ∧ p.1 + p.2 ∉ A := by
  simp [whiteCells, blackCells, Finset.mem_compl]

/-- A black cell and a white cell of the same line colouring never share a
line: each shared line would lie simultaneously in one of the black line
sets and in its complement. -/
theorem isPeaceable_blackCells_whiteCells (R C D A : Finset (ZMod n)) :
    IsPeaceable (blackCells R C D A) (whiteCells R C D A) := by
  intro b hb w hw hshare
  rw [mem_blackCells] at hb
  rw [mem_whiteCells] at hw
  rcases hshare with h | h | h | h
  · exact hw.1 (h ▸ hb.1)
  · exact hw.2.1 (h ▸ hb.2.1)
  · exact hw.2.2.1 (h ▸ hb.2.2.1)
  · exact hw.2.2.2 (h ▸ hb.2.2.2)

/-- **Line-colouring equivalence** (Lemma 2 of the paper).  A peaceable
placement of `m` black and `m` white queens exists iff some choice of black
line sets `R, C, D, A` yields at least `m` all-black cells and at least `m`
all-white cells.

Forward direction: colour every line carrying a black queen black; each
black queen lies on four black lines, and no line of a white queen can be
black (the two queens would attack).  Backward direction: place the armies
on any `m` cells of `blackCells` resp. `whiteCells`. -/
theorem hasPeaceable_iff_lineSets {n : ℕ} [NeZero n] {m : ℕ} :
    HasPeaceable n m ↔ ∃ R C D A : Finset (ZMod n),
      m ≤ (blackCells R C D A).card ∧ m ≤ (whiteCells R C D A).card := by
  constructor
  · rintro ⟨B, W, hp, hB, hW⟩
    refine ⟨B.image Prod.fst, B.image Prod.snd,
      B.image (fun p : Cell n => p.1 - p.2),
      B.image (fun p : Cell n => p.1 + p.2), ?_, ?_⟩
    · -- every black queen lies on four black lines
      rw [← hB]
      apply Finset.card_le_card
      intro b hb
      rw [mem_blackCells]
      exact ⟨Finset.mem_image_of_mem _ hb, Finset.mem_image_of_mem _ hb,
        Finset.mem_image_of_mem _ hb, Finset.mem_image_of_mem _ hb⟩
    · -- no line of a white queen carries a black queen
      rw [← hW]
      apply Finset.card_le_card
      intro w hw
      rw [mem_whiteCells]
      refine ⟨fun hmem => ?_, fun hmem => ?_, fun hmem => ?_, fun hmem => ?_⟩
      · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hmem
        exact hp b hb w hw (Or.inl hbe)
      · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hmem
        exact hp b hb w hw (Or.inr (Or.inl hbe))
      · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hmem
        exact hp b hb w hw (Or.inr (Or.inr (Or.inl hbe)))
      · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hmem
        exact hp b hb w hw (Or.inr (Or.inr (Or.inr hbe)))
  · rintro ⟨R, C, D, A, hbm, hwm⟩
    obtain ⟨B', hB', hBc⟩ := Finset.exists_subset_card_eq hbm
    obtain ⟨W', hW', hWc⟩ := Finset.exists_subset_card_eq hwm
    exact ⟨B', W',
      (isPeaceable_blackCells_whiteCells R C D A).mono hB' hW', hBc, hWc⟩

/-- Every choice of black line sets bounds `lineMax` from below. -/
theorem le_lineMax (R C D A : Finset (ZMod n)) :
    min (blackCells R C D A).card (whiteCells R C D A).card ≤ lineMax n := by
  unfold lineMax
  exact Finset.le_sup
    (f := fun x : (Finset (ZMod n) × Finset (ZMod n)) ×
        Finset (ZMod n) × Finset (ZMod n) =>
      min (blackCells x.1.1 x.1.2 x.2.1 x.2.2).card
        (whiteCells x.1.1 x.1.2 x.2.1 x.2.2).card)
    (Finset.mem_univ ((R, C), D, A))

/-- `lineMax` is the least upper bound over all line colourings. -/
theorem lineMax_le {b : ℕ}
    (h : ∀ R C D A : Finset (ZMod n),
      min (blackCells R C D A).card (whiteCells R C D A).card ≤ b) :
    lineMax n ≤ b := by
  unfold lineMax
  apply Finset.sup_le
  rintro ⟨⟨R, C⟩, D, A⟩ -
  exact h R C D A

/-- "The queens have disappeared": the toroidal peaceable-queens function
equals the optimum of the line-colouring reformulation.  Combined with the
computability of `lineMax`, this determines `t n` by finite enumeration. -/
theorem t_eq_lineMax (n : ℕ) [NeZero n] : t n = lineMax n := by
  apply le_antisymm
  · obtain ⟨R, C, D, A, hb, hw⟩ :=
      hasPeaceable_iff_lineSets.mp (hasPeaceable_t n)
    exact le_trans (le_min hb hw) (le_lineMax R C D A)
  · apply lineMax_le
    intro R C D A
    exact le_t_iff.mpr <| hasPeaceable_iff_lineSets.mpr
      ⟨R, C, D, A, min_le_left _ _, min_le_right _ _⟩

end PeaceableQueens
