import Mathlib

/-!
# Peaceable queens on the `n × n` torus — basic definitions

This file defines the toroidal peaceable-queens problem (OEIS A279405) and the
even-order value function `H` of the paper

  *Peaceable queens on even toroidal boards* (`paper/peace_even_torus.tex`),

whose Theorem 1 states `t (2*q) = H q` for every `q ≥ 1` (in the paper's
notation, `t(2q) = H(2q)`).

* `Cell n` — a board cell, a pair of coordinates in `ZMod n`.
* `SharesLine p p'` — the two cells lie on a common row, column, diagonal or
  antidiagonal (queens attack along these four line families; on the torus all
  four wrap around, which is exactly the `ZMod n` arithmetic).
* `IsPeaceable B W` — no cell of `B` shares a line with a cell of `W`.
  Since a cell shares a row with itself, `B` and `W` are automatically
  disjoint.
* `HasPeaceable n m` — some peaceable pair of armies of size `m` each exists.
* `t n` — the largest such `m` (the sequence A279405).
* `H q` — the parity-profile optimum `H(2q)` of Definition 1 of the paper.
  Natural subtraction is harmless there because all profile entries are `≤ q`.
* `blackCells`/`whiteCells`/`lineMax` — the line-colouring reformulation used
  by `PeaceableQueens.LineColouring` (Lemma 2 of the paper).
-/

namespace PeaceableQueens

/-- A cell of the `n × n` toroidal board: (row, column) in `ZMod n × ZMod n`. -/
abbrev Cell (n : ℕ) : Type := ZMod n × ZMod n

/-- Two cells lie on a common line: same row, same column, same diagonal
(`r - c`), or same antidiagonal (`r + c`).  Two queens attack each other
exactly when their cells share a line; equal cells share all four lines. -/
def SharesLine {n : ℕ} (p p' : Cell n) : Prop :=
  p.1 = p'.1 ∨ p.2 = p'.2 ∨ p.1 - p.2 = p'.1 - p'.2 ∨ p.1 + p.2 = p'.1 + p'.2

instance {n : ℕ} (p p' : Cell n) : Decidable (SharesLine p p') := by
  unfold SharesLine; infer_instance

/-- Every cell shares a line with itself (its row). -/
theorem sharesLine_refl {n : ℕ} (p : Cell n) : SharesLine p p := Or.inl rfl

/-- Sharing a line is symmetric. -/
theorem SharesLine.symm {n : ℕ} {p p' : Cell n} (h : SharesLine p p') :
    SharesLine p' p := by
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inr (Or.inr h.symm))

/-- A placement of two armies is peaceable when no black cell shares a line
with a white cell.  (Attacks within one army are allowed.) -/
def IsPeaceable {n : ℕ} (B W : Finset (Cell n)) : Prop :=
  ∀ b ∈ B, ∀ w ∈ W, ¬ SharesLine b w

/-- The two armies are automatically disjoint: a common cell would share a
line (its own row) with itself. -/
theorem IsPeaceable.disjoint {n : ℕ} {B W : Finset (Cell n)}
    (h : IsPeaceable B W) : Disjoint B W := by
  rw [Finset.disjoint_left]
  intro p hpB hpW
  exact h p hpB p hpW (sharesLine_refl p)

/-- The `n × n` torus admits `m` black and `m` white mutually non-attacking
queens. -/
def HasPeaceable (n m : ℕ) : Prop :=
  ∃ B W : Finset (Cell n), IsPeaceable B W ∧ B.card = m ∧ W.card = m

open Classical in
/-- The toroidal peaceable-queens function: the largest army size `m` such
that `m + m` queens can be placed peaceably on the `n × n` torus.  For
`n ≥ 1` this is OEIS A279405. -/
noncomputable def t (n : ℕ) : ℕ := Nat.findGreatest (HasPeaceable n) (n ^ 2)

/-- The empty placement is peaceable. -/
theorem hasPeaceable_zero (n : ℕ) : HasPeaceable n 0 :=
  ⟨∅, ∅, by simp [IsPeaceable], Finset.card_empty, Finset.card_empty⟩

/-- Discarding queens keeps a placement peaceable. -/
theorem IsPeaceable.mono {n : ℕ} {B W B' W' : Finset (Cell n)}
    (h : IsPeaceable B W) (hB : B' ⊆ B) (hW : W' ⊆ W) : IsPeaceable B' W' :=
  fun b hb w hw => h b (hB hb) w (hW hw)

/-- Army sizes can be decreased. -/
theorem HasPeaceable.mono {n m m' : ℕ} (h : HasPeaceable n m) (hle : m' ≤ m) :
    HasPeaceable n m' := by
  obtain ⟨B, W, hp, hB, hW⟩ := h
  obtain ⟨B', hB', hB'card⟩ := Finset.exists_subset_card_eq (hB ▸ hle)
  obtain ⟨W', hW', hW'card⟩ := Finset.exists_subset_card_eq (hW ▸ hle)
  exact ⟨B', W', hp.mono hB' hW', hB'card, hW'card⟩

/-- An army fits on the board. -/
theorem HasPeaceable.le_sq {n m : ℕ} [NeZero n] (h : HasPeaceable n m) :
    m ≤ n ^ 2 := by
  obtain ⟨B, _, _, hB, _⟩ := h
  calc m = B.card := hB.symm
    _ ≤ Fintype.card (Cell n) := Finset.card_le_univ B
    _ = n ^ 2 := by simp [Cell, sq]

/-- The maximum is attained. -/
theorem hasPeaceable_t (n : ℕ) : HasPeaceable n (t n) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (hasPeaceable_zero n)

/-- Characterization of `t`: `m ≤ t n` iff `m` peaceable queens per army fit.
This is the interface through which both bounds of the theorem are stated. -/
theorem le_t_iff {n m : ℕ} [NeZero n] : m ≤ t n ↔ HasPeaceable n m := by
  classical
  constructor
  · intro h
    exact (hasPeaceable_t n).mono h
  · intro h
    exact Nat.le_findGreatest h.le_sq h

/-! ## The value function `H` -/

/-- Black homogeneous-cell count of a parity profile (paper, Definition 1). -/
def profileBlack (r0 r1 c0 c1 : ℕ) : ℕ := r0 * c1 + r1 * c0

/-- White homogeneous-cell count of a parity profile (paper, Definition 1).
Natural subtraction agrees with integer subtraction when the entries are
`≤ q`, which is the only regime in which `H` reads this function. -/
def profileWhite (q r0 r1 c0 c1 : ℕ) : ℕ :=
  (q - r0) * (q - c0) + (q - r1) * (q - c1)

/-- `H q` is the paper's `H(2q)` (Definition 1): the best guaranteed army
size over all parity profiles `(r0, r1, c0, c1) ∈ {0,…,q}⁴`. -/
def H (q : ℕ) : ℕ :=
  ((Finset.range (q + 1) ×ˢ Finset.range (q + 1)) ×ˢ
      (Finset.range (q + 1) ×ˢ Finset.range (q + 1))).sup
    fun x => min (profileBlack x.1.1 x.1.2 x.2.1 x.2.2)
      (profileWhite q x.1.1 x.1.2 x.2.1 x.2.2)

/-- Every admissible profile bounds `H` from below. -/
theorem le_H {q r0 r1 c0 c1 : ℕ} (h0 : r0 ≤ q) (h1 : r1 ≤ q) (h2 : c0 ≤ q)
    (h3 : c1 ≤ q) :
    min (profileBlack r0 r1 c0 c1) (profileWhite q r0 r1 c0 c1) ≤ H q := by
  have hmem : ((r0, r1), (c0, c1)) ∈
      (Finset.range (q + 1) ×ˢ Finset.range (q + 1)) ×ˢ
        (Finset.range (q + 1) ×ˢ Finset.range (q + 1)) := by
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  exact Finset.le_sup
    (f := fun x : (ℕ × ℕ) × ℕ × ℕ => min (profileBlack x.1.1 x.1.2 x.2.1 x.2.2)
      (profileWhite q x.1.1 x.1.2 x.2.1 x.2.2)) hmem

/-- `H` is the least upper bound of the profile values. -/
theorem H_le {q b : ℕ}
    (h : ∀ r0 r1 c0 c1 : ℕ, r0 ≤ q → r1 ≤ q → c0 ≤ q → c1 ≤ q →
      min (profileBlack r0 r1 c0 c1) (profileWhite q r0 r1 c0 c1) ≤ b) :
    H q ≤ b := by
  unfold H
  apply Finset.sup_le
  rintro ⟨⟨r0, r1⟩, ⟨c0, c1⟩⟩ hx
  simp only [Finset.mem_product, Finset.mem_range] at hx
  exact h r0 r1 c0 c1 (by omega) (by omega) (by omega) (by omega)

/-! ## The line-colouring reformulation (Lemma 2 of the paper) -/

section LineSets

variable {n : ℕ} [NeZero n]

/-- Cells all four of whose lines are black, given black line sets `R` (rows),
`C` (columns), `D` (diagonals `r - c`), `A` (antidiagonals `r + c`). -/
def blackCells (R C D A : Finset (ZMod n)) : Finset (Cell n) :=
  Finset.univ.filter fun p : Cell n =>
    p.1 ∈ R ∧ p.2 ∈ C ∧ p.1 - p.2 ∈ D ∧ p.1 + p.2 ∈ A

/-- Cells all four of whose lines are white: the black cells of the
complemented line sets. -/
def whiteCells (R C D A : Finset (ZMod n)) : Finset (Cell n) :=
  blackCells Rᶜ Cᶜ Dᶜ Aᶜ

/-- The optimum of the line-colouring reformulation.  `t_eq_lineMax` in
`PeaceableQueens.LineColouring` shows `t n = lineMax n`; this makes `t`
computable by finite enumeration for small `n`. -/
def lineMax (n : ℕ) [NeZero n] : ℕ :=
  (Finset.univ :
      Finset ((Finset (ZMod n) × Finset (ZMod n)) ×
        (Finset (ZMod n) × Finset (ZMod n)))).sup
    fun x => min (blackCells x.1.1 x.1.2 x.2.1 x.2.2).card
      (whiteCells x.1.1 x.1.2 x.2.1 x.2.2).card

end LineSets

end PeaceableQueens
