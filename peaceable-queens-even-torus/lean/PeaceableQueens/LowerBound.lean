import PeaceableQueens.Defs

/-!
# Peaceable queens on the even torus — the lower bound `H q ≤ t (2q)`

This file formalizes Proposition "Parity separation" of the paper
*Peaceable queens on even toroidal boards* (`paper/peace_even_torus.tex`),
i.e. the lower bound of Theorem 1.

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
private def lab (q i j : ℕ) : ZMod (2 * q) := ((2 * j + i : ℕ) : ZMod (2 * q))

/-- The parity ring homomorphism `ZMod (2q) →+* ZMod 2`. -/
private def par (q : ℕ) : ZMod (2 * q) →+* ZMod 2 :=
  ZMod.castHom ⟨q, rfl⟩ (ZMod 2)

/-- The label `2j + i` has parity `i`. -/
private lemma par_lab (q i j : ℕ) : par q (lab q i j) = (i : ZMod 2) := by
  rw [lab, par, map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
    zero_mul, zero_add]

/-- Distinct indices below `q` give distinct labels of the same parity. -/
private lemma lab_inj {q : ℕ} {i j j' : ℕ} (hi : i ≤ 1)
    (hj : j < q) (hj' : j' < q) (h : lab q i j = lab q i j') : j = j' := by
  have h' := congrArg ZMod.val h
  rw [lab, lab, ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)]
    at h'
  omega

/-- Everything in the image of `lab q i` has parity `i`. -/
private lemma par_of_mem {q i : ℕ} {s : Finset ℕ} {x : ZMod (2 * q)}
    (hx : x ∈ s.image (lab q i)) : par q x = (i : ZMod 2) := by
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
  exact par_lab q i j

/-! ## Separation lemmas: the four line families -/

/-- Labels of different parities are distinct (rows or columns, parity case). -/
private lemma ne_of_par_ne {q i k : ℕ} {s t : Finset ℕ} {x x' : ZMod (2 * q)}
    (hik : (i : ZMod 2) ≠ (k : ZMod 2))
    (hx : x ∈ s.image (lab q i)) (hx' : x' ∈ t.image (lab q k)) : x ≠ x' := by
  intro h
  exact hik (by rw [← par_of_mem hx, ← par_of_mem hx', h])

/-- Same-parity labels with indices below and above the threshold `r` are
distinct (rows or columns, disjoint-range case). -/
private lemma ne_of_range_Ico {q : ℕ} {i r : ℕ} (hi : i ≤ 1)
    {x x' : ZMod (2 * q)} (hx : x ∈ (Finset.range r).image (lab q i))
    (hx' : x' ∈ (Finset.Ico r q).image (lab q i)) : x ≠ x' := by
  rintro rfl
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j', hj', h⟩ := Finset.mem_image.mp hx'
  rw [Finset.mem_range] at hj
  rw [Finset.mem_Ico] at hj'
  have := lab_inj hi hj'.2 (by omega) h
  omega

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

/-- The last `q - r` labels of parity `i` are `q - r` distinct residues. -/
private lemma card_image_Ico {q : ℕ} {i : ℕ} (hi : i ≤ 1)
    (r : ℕ) : ((Finset.Ico r q).image (lab q i)).card = q - r := by
  rw [Finset.card_image_of_injOn, Nat.card_Ico]
  intro j hj j' hj' h
  simp only [Finset.coe_Ico, Set.mem_Ico] at hj hj'
  exact lab_inj hi hj.2 hj'.2 h

/-! ## Assembly -/

/-- A peaceable pair supports armies of the minimum of the two sizes. -/
private lemma hasPeaceable_min {n : ℕ} {B W : Finset (Cell n)}
    (h : IsPeaceable B W) : HasPeaceable n (min B.card W.card) := by
  obtain ⟨B', hB', hBcard⟩ :=
    Finset.exists_subset_card_eq (min_le_left B.card W.card)
  obtain ⟨W', hW', hWcard⟩ :=
    Finset.exists_subset_card_eq (min_le_right B.card W.card)
  exact ⟨B', W', h.mono hB' hW', hBcard, hWcard⟩

/-- **Parity separation** (Proposition of the paper): every parity profile
`(r0, r1, c0, c1) ∈ {0,…,q}⁴` is realized by a peaceable placement on the
`2q × 2q` torus with `profileBlack r0 r1 c0 c1` black and
`profileWhite q r0 r1 c0 c1` white queens. -/
private theorem hasPeaceable_profile {q : ℕ} {r0 r1 c0 c1 : ℕ}
    (h0 : r0 ≤ q) (h1 : r1 ≤ q) (h2 : c0 ≤ q) (h3 : c1 ≤ q) :
    HasPeaceable (2 * q)
      (min (profileBlack r0 r1 c0 c1) (profileWhite q r0 r1 c0 c1)) := by
  classical
  -- Chosen (black) rows and columns of each parity, and the remaining
  -- (white) rows and columns.
  set R0 : Finset (ZMod (2 * q)) := (Finset.range r0).image (lab q 0) with hR0
  set R1 : Finset (ZMod (2 * q)) := (Finset.range r1).image (lab q 1) with hR1
  set C0 : Finset (ZMod (2 * q)) := (Finset.range c0).image (lab q 0) with hC0
  set C1 : Finset (ZMod (2 * q)) := (Finset.range c1).image (lab q 1) with hC1
  set R0' : Finset (ZMod (2 * q)) := (Finset.Ico r0 q).image (lab q 0) with hR0'
  set R1' : Finset (ZMod (2 * q)) := (Finset.Ico r1 q).image (lab q 1) with hR1'
  set C0' : Finset (ZMod (2 * q)) := (Finset.Ico c0 q).image (lab q 0) with hC0'
  set C1' : Finset (ZMod (2 * q)) := (Finset.Ico c1 q).image (lab q 1) with hC1'
  -- Black cells pair a row and a column of opposite parity, white cells a
  -- remaining row and column of equal parity.
  have hpeace : IsPeaceable (R0 ×ˢ C1 ∪ R1 ×ˢ C0) (R0' ×ˢ C0' ∪ R1' ×ˢ C1') := by
    rintro ⟨x, y⟩ hb ⟨x', y'⟩ hw hline
    rw [Finset.mem_union, Finset.mem_product, Finset.mem_product] at hb hw
    have h01 : ((0 : ℕ) : ZMod 2) ≠ ((1 : ℕ) : ZMod 2) := by decide
    obtain ⟨hx, hy⟩ | ⟨hx, hy⟩ := hb <;> obtain ⟨hx', hy'⟩ | ⟨hx', hy'⟩ := hw <;>
      obtain h | h | h | h := hline
    -- (R0 × C1) vs (R0' × C0')
    · exact ne_of_range_Ico (by omega) hx hx' h
    · exact ne_of_par_ne h01.symm hy hy' h
    · exact sub_ne (by rw [par_of_mem hx, par_of_mem hy]; exact h01)
        (by rw [par_of_mem hx', par_of_mem hy']) h
    · exact add_ne (by rw [par_of_mem hx, par_of_mem hy]; exact h01)
        (by rw [par_of_mem hx', par_of_mem hy']) h
    -- (R0 × C1) vs (R1' × C1')
    · exact ne_of_par_ne h01 hx hx' h
    · exact ne_of_range_Ico (by omega) hy hy' h
    · exact sub_ne (by rw [par_of_mem hx, par_of_mem hy]; exact h01)
        (by rw [par_of_mem hx', par_of_mem hy']) h
    · exact add_ne (by rw [par_of_mem hx, par_of_mem hy]; exact h01)
        (by rw [par_of_mem hx', par_of_mem hy']) h
    -- (R1 × C0) vs (R0' × C0')
    · exact ne_of_par_ne h01.symm hx hx' h
    · exact ne_of_range_Ico (by omega) hy hy' h
    · exact sub_ne (by rw [par_of_mem hx, par_of_mem hy]; exact h01.symm)
        (by rw [par_of_mem hx', par_of_mem hy']) h
    · exact add_ne (by rw [par_of_mem hx, par_of_mem hy]; exact h01.symm)
        (by rw [par_of_mem hx', par_of_mem hy']) h
    -- (R1 × C0) vs (R1' × C1')
    · exact ne_of_range_Ico (by omega) hx hx' h
    · exact ne_of_par_ne h01 hy hy' h
    · exact sub_ne (by rw [par_of_mem hx, par_of_mem hy]; exact h01.symm)
        (by rw [par_of_mem hx', par_of_mem hy']) h
    · exact add_ne (by rw [par_of_mem hx, par_of_mem hy]; exact h01.symm)
        (by rw [par_of_mem hx', par_of_mem hy']) h
  -- Black army size: `r0 * c1 + r1 * c0`.
  have hBcard : (R0 ×ˢ C1 ∪ R1 ×ˢ C0).card = profileBlack r0 r1 c0 c1 := by
    have hdisj : Disjoint (R0 ×ˢ C1) (R1 ×ˢ C0) := by
      rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ ha hb
      rw [Finset.mem_product] at ha hb
      have e0 := par_of_mem (hR0 ▸ ha.1)
      have e1 := par_of_mem (hR1 ▸ hb.1)
      rw [e0] at e1
      exact absurd e1 (by decide)
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_product,
      Finset.card_product, hR0, hR1, hC0, hC1,
      card_image_range (by omega) h0, card_image_range (by omega) h3,
      card_image_range (by omega) h1, card_image_range (by omega) h2]
    rfl
  -- White army size: `(q - r0) * (q - c0) + (q - r1) * (q - c1)`.
  have hWcard : (R0' ×ˢ C0' ∪ R1' ×ˢ C1').card = profileWhite q r0 r1 c0 c1 := by
    have hdisj : Disjoint (R0' ×ˢ C0') (R1' ×ˢ C1') := by
      rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ ha hb
      rw [Finset.mem_product] at ha hb
      have e0 := par_of_mem (hR0' ▸ ha.1)
      have e1 := par_of_mem (hR1' ▸ hb.1)
      rw [e0] at e1
      exact absurd e1 (by decide)
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_product,
      Finset.card_product, hR0', hR1', hC0', hC1',
      card_image_Ico (by omega) r0, card_image_Ico (by omega) c0,
      card_image_Ico (by omega) r1, card_image_Ico (by omega) c1]
    rfl
  have := hasPeaceable_min hpeace
  rwa [hBcard, hWcard] at this

/-- **Lower bound of Theorem 1**: the parity-profile optimum `H q = H(2q)` is
achieved by peaceable armies on the `2q × 2q` torus, so `H q ≤ t (2q)`. -/
theorem H_le_t (q : ℕ) (hq : 0 < q) : H q ≤ t (2 * q) := by
  haveI : NeZero (2 * q) := ⟨by omega⟩
  exact H_le fun r0 r1 c0 c1 h0 h1 h2 h3 =>
    le_t_iff.mpr (hasPeaceable_profile h0 h1 h2 h3)

end PeaceableQueens
