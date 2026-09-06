import PeaceableQueens.Parity

/-!
# Peaceable queens on the even torus — the lower bound `H q ≤ t (2q)`

This file formalizes Proposition "Parity separation" (`prop:lower`) of the paper
*Peaceable queens on even tori: an exact parity formula* (`peace_even_torus.tex`,
published together with this Lean project at
https://github.com/jphme/math-problems/tree/main/peaceable-queens-even-torus),
i.e. the lower bound of the main theorem (`thm:main`).

Let `n = 2q`.  Every residue of `ZMod (2q)` has a well-defined parity, given
by the ring homomorphism `π : ZMod (2q) →+* ZMod 2`.  For a parity profile
`(r0, r1, c0, c1) ∈ {0,…,q}⁴` we place

* the **black** army on cells whose row and column labels have *opposite*
  parity: rows are the first `r0` even and first `r1` odd labels, columns the
  first `c0` even and first `c1` odd labels, and a black cell pairs a row
  with a column of the other parity;
* the **white** army on cells whose row and column labels have the *same*
  parity, drawn from the remaining `q - r0` even / `q - r1` odd rows and
  `q - c0` even / `q - c1` odd columns.

A black cell has diagonal and antidiagonal labels of odd parity, a white cell
of even parity, so the two armies never share a diagonal or antidiagonal;
rows and columns are separated either by parity or by the disjointness of the
chosen index ranges.  Counting gives `|B| = profileBlack r0 r1 c0 c1` and
`|W| = profileWhite q r0 r1 c0 c1`, hence
`min (profileBlack …) (profileWhite …) ≤ t (2q)`; taking the maximum over all
profiles yields the main result `PeaceableQueens.H_le_t : H q ≤ t (2*q)`.
-/

namespace PeaceableQueens

/-! ## Labels and their parity -/

/-- The `j`-th residue of parity `i` in `ZMod (2q)`: the label `2j + i`.
For `i ≤ 1` and `j < q` these `2q` labels are pairwise distinct and exhaust
`ZMod (2q)`. -/
private abbrev lab := Parity.labelNat
private abbrev par := Parity.parityMap
private alias par_lab := Parity.parityMap_labelNat
private alias lab_inj := Parity.labelNat_inj

/-- A cell with coordinates of different parity and a cell with coordinates of
equal parity never share a diagonal. -/
private lemma sub_ne {q : ℕ} {x y x' y' : ZMod (2 * q)}
    (hxy : par q x ≠ par q y) (hxy' : par q x' = par q y') :
    x - y ≠ x' - y' := by
  intro h
  apply hxy
  have e := congrArg (par q) h
  rw [map_sub, map_sub, hxy'] at e
  exact (by decide : ∀ a b c : ZMod 2, a - b = c - c → a = b) _ _ _ e

/-- A cell with coordinates of different parity and a cell with coordinates of
equal parity never share an antidiagonal. -/
private lemma add_ne {q : ℕ} {x y x' y' : ZMod (2 * q)}
    (hxy : par q x ≠ par q y) (hxy' : par q x' = par q y') :
    x + y ≠ x' + y' := by
  intro h
  apply hxy
  have e := congrArg (par q) h
  rw [map_add, map_add, hxy'] at e
  exact (by decide : ∀ a b c : ZMod 2, a + b = c + c → a = b) _ _ _ e

/-! ## Cardinalities -/

/-- The first `r` labels of parity `i` are `r` distinct residues. -/
private lemma card_image_range {q : ℕ} {i : ℕ} (hi : i ≤ 1)
    {r : ℕ} (hr : r ≤ q) : ((Finset.range r).image (lab q i)).card = r := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro j hj j' hj' h
  simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
  exact lab_inj hi (by omega) (by omega) h

/-! ## Assembly -/

/-- A peaceable pair supports armies of the minimum of the two sizes. -/
private lemma hasPeaceable_min {n : ℕ} {B W : Finset (Cell n)}
    (h : IsPeaceable B W) : HasPeaceable n (min B.card W.card) := by
  obtain ⟨B', hB', hBcard⟩ :=
    Finset.exists_subset_card_eq (min_le_left B.card W.card)
  obtain ⟨W', hW', hWcard⟩ :=
    Finset.exists_subset_card_eq (min_le_right B.card W.card)
  exact ⟨B', W', h.mono hB' hW', hBcard, hWcard⟩

/-- The parity-separated black and white cell sets for arbitrary row and column sets. -/
def parityBlackCells {q : ℕ} (R C : Finset (ZMod (2 * q))) : Finset (Cell (2 * q)) :=
  (R ×ˢ C).filter fun p => par q p.1 ≠ par q p.2

def parityWhiteCells {q : ℕ} [NeZero (2 * q)] (R C : Finset (ZMod (2 * q))) :
    Finset (Cell (2 * q)) :=
  (Rᶜ ×ˢ Cᶜ).filter fun p => par q p.1 = par q p.2

/-- These are exactly the black homogeneous cells when both diagonal
families select their odd labels, as in paper `prop:lower`. -/
theorem parityBlackCells_eq_lineCells {q : ℕ} [NeZero (2 * q)]
    (R C : Finset (ZMod (2 * q))) :
    parityBlackCells R C = blackCells R C (Parity.parityClass q 1) (Parity.parityClass q 1) := by
  have hp : ∀ a b : ZMod 2, a ≠ b ↔ a - b = 1 ∧ a + b = 1 := by decide
  ext p
  have h := hp (par q p.1) (par q p.2)
  simp only [parityBlackCells, blackCells, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and, Parity.parityClass, Fin.val_one, Nat.cast_one,
    map_sub, map_add]
  tauto

/-- The complementary homogeneous cells are precisely the same-parity
construction on the remaining rows and columns. -/
theorem parityWhiteCells_eq_lineCells {q : ℕ} [NeZero (2 * q)]
    (R C : Finset (ZMod (2 * q))) :
    parityWhiteCells R C = whiteCells R C (Parity.parityClass q 1) (Parity.parityClass q 1) := by
  have hp : ∀ a b : ZMod 2, a = b ↔ a - b ≠ 1 ∧ a + b ≠ 1 := by decide
  ext p
  have h := hp (par q p.1) (par q p.2)
  simp only [parityWhiteCells, whiteCells, blackCells, Finset.mem_filter,
    Finset.mem_product, Finset.mem_compl, Finset.mem_univ, true_and,
    Parity.parityClass, Fin.val_one, Nat.cast_one, map_sub, map_add]
  tauto

/-- Paper `prop:lower` / S13: arbitrary sets with the given parity counts
have exactly the displayed black and white counts and are peaceable. -/
theorem paritySeparated_counts {q : ℕ} [NeZero (2 * q)]
    (R C : Finset (ZMod (2 * q))) :
    IsPeaceable (parityBlackCells R C) (parityWhiteCells R C) ∧
    (parityBlackCells R C).card =
      profileBlack (R.filter fun x => par q x = 0).card (R.filter fun x => par q x = 1).card
        (C.filter fun x => par q x = 0).card (C.filter fun x => par q x = 1).card ∧
    (parityWhiteCells R C).card =
      profileWhite q (R.filter fun x => par q x = 0).card (R.filter fun x => par q x = 1).card
        (C.filter fun x => par q x = 0).card (C.filter fun x => par q x = 1).card := by
  have hneq : ∀ a b : ZMod 2, a ≠ b ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
  have heq : ∀ a b : ZMod 2, a = b ↔ (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by decide
  have hdisj (S T U V : Finset (ZMod (2 * q))) :
      Disjoint ((S.filter fun x => par q x = 0) ×ˢ T)
        ((U.filter fun x => par q x = 1) ×ˢ V) := by
    rw [Finset.disjoint_left]
    rintro ⟨x, y⟩ h0 h1
    have hx0 := (Finset.mem_filter.mp (Finset.mem_product.mp h0).1).2
    have hx1 := (Finset.mem_filter.mp (Finset.mem_product.mp h1).1).2
    exact (by decide : (0 : ZMod 2) ≠ 1) (hx0.symm.trans hx1)
  have hblack : parityBlackCells R C =
      (R.filter fun x => par q x = 0) ×ˢ (C.filter fun x => par q x = 1) ∪
      (R.filter fun x => par q x = 1) ×ˢ (C.filter fun x => par q x = 0) := by
    ext p
    simp only [parityBlackCells, Finset.mem_filter, Finset.mem_product, Finset.mem_union]
    rw [hneq]
    tauto
  have hwhite : parityWhiteCells R C =
      (Rᶜ.filter fun x => par q x = 0) ×ˢ (Cᶜ.filter fun x => par q x = 0) ∪
      (Rᶜ.filter fun x => par q x = 1) ×ˢ (Cᶜ.filter fun x => par q x = 1) := by
    ext p
    simp only [parityWhiteCells, Finset.mem_filter, Finset.mem_product, Finset.mem_union]
    rw [heq]
    tauto
  refine ⟨?_, ?_, ?_⟩
  · intro b hb w hw hline
    rcases Finset.mem_filter.mp hb with ⟨hb, hbp⟩
    rcases Finset.mem_filter.mp hw with ⟨hw, hwp⟩
    rcases Finset.mem_product.mp hb with ⟨hbR, hbC⟩
    rcases Finset.mem_product.mp hw with ⟨hwR, hwC⟩
    rcases hline with h | h | h | h
    · exact (Finset.mem_compl.mp hwR) (h ▸ hbR)
    · exact (Finset.mem_compl.mp hwC) (h ▸ hbC)
    · exact sub_ne hbp hwp h
    · exact add_ne hbp hwp h
  · rw [hblack, Finset.card_union_of_disjoint (hdisj _ _ _ _)]
    simp only [Finset.card_product, profileBlack]
  · rw [hwhite, Finset.card_union_of_disjoint (hdisj _ _ _ _)]
    simp only [Finset.card_product, profileWhite]
    have hc (S : Finset (ZMod (2 * q))) (p : Fin 2) :=
      Parity.card_parity_filter_compl q S p
    simpa only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one] using
      congrArg₂ (fun a b : ℕ => a + b)
        (congrArg₂ (fun a b : ℕ => a * b) (hc R 0) (hc C 0))
        (congrArg₂ (fun a b : ℕ => a * b) (hc R 1) (hc C 1))

/-- Every admissible four-count profile is realized. The geometric counting
is shared with the arbitrary-set theorem; only the choice of labels remains. -/
private theorem hasPeaceable_profile {q : ℕ} {r0 r1 c0 c1 : ℕ}
    (h0 : r0 ≤ q) (h1 : r1 ≤ q) (h2 : c0 ≤ q) (h3 : c1 ≤ q) :
    HasPeaceable (2 * q)
      (min (profileBlack r0 r1 c0 c1) (profileWhite q r0 r1 c0 c1)) := by
  by_cases hq : q = 0
  · subst q
    have : r0 = 0 ∧ r1 = 0 ∧ c0 = 0 ∧ c1 = 0 := by omega
    rcases this with ⟨rfl, rfl, rfl, rfl⟩
    exact hasPeaceable_zero 0
  letI : NeZero (2 * q) := ⟨by omega⟩
  let choose (a b : ℕ) := (Finset.range a).image (lab q 0) ∪ (Finset.range b).image (lab q 1)
  have hcount0 (a b : ℕ) (ha : a ≤ q) :
      ((choose a b).filter fun x => par q x = 0).card = a := by
    simpa [choose, Finset.filter_union, Finset.filter_image, par_lab] using
      card_image_range (i := 0) (by decide) ha
  have hcount1 (a b : ℕ) (hb : b ≤ q) :
      ((choose a b).filter fun x => par q x = 1).card = b := by
    simpa [choose, Finset.filter_union, Finset.filter_image, par_lab] using
      card_image_range (i := 1) (by decide) hb
  obtain ⟨hp, hB, hW⟩ := paritySeparated_counts (choose r0 r1) (choose c0 c1)
  have h := hasPeaceable_min hp
  rw [hB, hW, hcount0 _ _ h0, hcount1 _ _ h1, hcount0 _ _ h2, hcount1 _ _ h3] at h
  exact h

/-- **Lower bound of the main theorem (`thm:main`)**: the parity-profile optimum `H q = H(2q)` is
achieved by peaceable armies on the `2q × 2q` torus, so `H q ≤ t (2q)`. -/
theorem H_le_t (q : ℕ) (hq : 0 < q) : H q ≤ t (2 * q) := by
  haveI : NeZero (2 * q) := ⟨by omega⟩
  exact H_le fun r0 r1 c0 c1 h0 h1 h2 h3 =>
    le_t_iff.mpr (hasPeaceable_profile h0 h1 h2 h3)

end PeaceableQueens
