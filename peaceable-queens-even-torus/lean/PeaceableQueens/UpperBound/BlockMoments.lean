import PeaceableQueens.UpperBound.Incidence
import PeaceableQueens.FiniteGeometry

/-!
# Parity-block atom frequencies

The S24 parity blocks are parametrized by `Fin q × Fin q`.  This gives an
exact finite model of the atom frequencies attached to a configuration and
proves the normalization, marginal, pair and aggregate D/A equations of
paper `lem:moments` (S24--S26).
-/

namespace PeaceableQueens.UpperBound.BlockMoments

open MomentModel
open ConfigurationBridge
open Incidence

/-- The `q²` cells in the row/column parity block, parametrized by two `Fin q`
coordinates. -/
def blockCell (q : ℕ) (block : Block) : Fin q × Fin q → Cell (2 * q) :=
  fun uv => (parityLabel q block.rowParity uv.1,
    parityLabel q block.columnParity uv.2)

/-- The actual finite set of cells in a parity block. -/
def blockCells (q : ℕ) (block : Block) : Finset (Cell (2 * q)) :=
  Finset.univ.image (blockCell q block)

lemma blockCell_injective (q : ℕ) (block : Block) :
    Function.Injective (blockCell q block) := by
  intro x y h
  apply Prod.ext
  · exact parityLabel_injective q block.rowParity (congrArg Prod.fst h)
  · exact parityLabel_injective q block.columnParity (congrArg Prod.snd h)

/-- Each block really is the indicated row/column parity cell fibre. -/
lemma mem_blockCells_iff (q : ℕ) [NeZero (2 * q)] (block : Block) (x : Cell (2 * q)) :
    x ∈ blockCells q block ↔
      parityMap q x.1 = (block.rowParity.val : ZMod 2) ∧
      parityMap q x.2 = (block.columnParity.val : ZMod 2) := by
  constructor
  · intro hx
    change x ∈ Finset.univ.image (blockCell q block) at hx
    obtain ⟨uv, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨parityMap_label q block.rowParity uv.1,
      parityMap_label q block.columnParity uv.2⟩
  · rintro ⟨hr, hc⟩
    have hr' : x.1 ∈ parityLabels q block.rowParity := by
      rw [parityLabels_eq_class]
      simp [parityClass, hr]
    have hc' : x.2 ∈ parityLabels q block.columnParity := by
      rw [parityLabels_eq_class]
      simp [parityClass, hc]
    obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hr'
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hc'
    refine Finset.mem_image.mpr ⟨(u, v), Finset.mem_univ _, ?_⟩
    simp [blockCell, hu, hv]

theorem card_blockCells (q : ℕ) (block : Block) :
    (blockCells q block).card = q ^ 2 := by
  unfold blockCells
  rw [Finset.card_image_of_injOn]
  simp [pow_two]
  intro x _ y _ h
  exact blockCell_injective q block h

/-- The Boolean line-colour atom carried by one board cell. -/
def atomOfCell (cfg : Configuration q) (x : Cell (2 * q)) : Atom :=
  ⟨decide (x.1 ∈ cfg.R), decide (x.2 ∈ cfg.C),
    decide (x.1 - x.2 ∈ cfg.D), decide (x.1 + x.2 ∈ cfg.A)⟩

/-- Number of cells in a block having a given line-colour atom. -/
def atomCount (cfg : Configuration q) (block : Block) (atom : Atom) : ℕ :=
  (Finset.univ.filter fun uv => atomOfCell cfg (blockCell q block uv) = atom).card

/-- The same count expressed directly on the geometric parity block. -/
def cellAtomCount (cfg : Configuration q) (block : Block) (atom : Atom) : ℕ :=
  (blockCells q block).filter (fun x => atomOfCell cfg x = atom) |>.card

theorem atomCount_eq_cellAtomCount (cfg : Configuration q) (block : Block) (atom : Atom) :
    atomCount cfg block atom = cellAtomCount cfg block atom := by
  unfold cellAtomCount blockCells
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  · rfl
  · intro x _ y _ h
    exact blockCell_injective q block h

/-- Exact rational frequency of an atom in a block. -/
def atomFrequency (cfg : Configuration q) (block : Block) (atom : Atom) : ℚ :=
  (atomCount cfg block atom : ℚ) / (q ^ 2 : ℚ)

/-- Count the cells of a block satisfying any ordinary moment predicate in
`MomentModel`.  The five remaining pair-moment proofs share this interface. -/
def blockMomentCount (cfg : Configuration q) (block : Block) (moment : BlockMoment) : ℕ :=
  ∑ atom, if moment.eval atom then atomCount cfg block atom else 0

theorem atomCount_normalization (cfg : Configuration q) (block : Block) :
    ∑ atom, atomCount cfg block atom = q ^ 2 := by
  unfold atomCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp [pow_two]

theorem atomFrequency_normalization (cfg : Configuration q) (hq : 0 < q) (block : Block) :
    ∑ atom, atomFrequency cfg block atom = 1 := by
  simp_rw [atomFrequency]
  rw [← Finset.sum_div]
  have hcount : (∑ atom, (atomCount cfg block atom : ℚ)) = (q ^ 2 : ℚ) := by
    exact_mod_cast atomCount_normalization cfg block
  rw [hcount]
  have hq2 : (q ^ 2 : ℚ) ≠ 0 := by positivity
  exact div_self hq2

export PeaceableQueens.Parity
  (selectedParityLabels selectedParityLabels_image card_selectedParityLabels
   parityIndex parityLabel_index)

theorem atomCount_row_marginal (cfg : Configuration q) (hq : 0 < q) (block : Block) :
    ∑ atom ∈ Finset.univ.filter (fun atom => atom.row), atomCount cfg block atom =
      rowCount cfg block.rowParity * q := by
  letI : NeZero (2 * q) := ⟨by omega⟩
  unfold atomCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter :
      Finset.univ.filter (fun uv : Fin q × Fin q =>
        atomOfCell cfg (blockCell q block uv) ∈ Finset.univ.filter (fun atom => atom.row)) =
      (selectedParityLabels q block.rowParity cfg.R).product Finset.univ := by
    ext uv
    simp [atomOfCell, blockCell, selectedParityLabels]
  rw [hfilter, Finset.product_eq_sprod, Finset.card_product, card_selectedParityLabels]
  simp [rowCount]

theorem blockMomentCount_row (cfg : Configuration q) (hq : 0 < q) (block : Block) :
    blockMomentCount cfg block .row = rowCount cfg block.rowParity * q := by
  change (∑ atom, if atom.row = true then atomCount cfg block atom else 0) = _
  rw [← Finset.sum_filter]
  exact atomCount_row_marginal cfg hq block

lemma diagonal_parity (q : ℕ) (block : Block) (uv : Fin q × Fin q) :
    parityMap q (blockCell q block uv).1 - parityMap q (blockCell q block uv).2 =
      (block.squareParity.val : ZMod 2) := by
  rcases block with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · simp [blockCell, Block.squareParity, parityMap_label]
  · simp [blockCell, Block.squareParity, parityMap_label]
  · simp [blockCell, Block.squareParity, parityMap_label]
  · simp only [blockCell, Block.squareParity, parityMap_label]
    change (1 : ZMod 2) + 1 = 0
    rw [show (1 : ZMod 2) + 1 = (2 : ZMod 2) by norm_num]
    exact ZMod.natCast_self 2

lemma antidiagonal_parity (q : ℕ) (block : Block) (uv : Fin q × Fin q) :
    parityMap q (blockCell q block uv).1 + parityMap q (blockCell q block uv).2 =
      (block.squareParity.val : ZMod 2) := by
  rcases block with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · simp [blockCell, Block.squareParity, parityMap_label]
  · simp [blockCell, Block.squareParity, parityMap_label]
  · simp [blockCell, Block.squareParity, parityMap_label]
  · simp only [blockCell, Block.squareParity, parityMap_label]
    change (1 : ZMod 2) + 1 = 0
    rw [show (1 : ZMod 2) + 1 = (2 : ZMod 2) by norm_num]
    exact ZMod.natCast_self 2

/-- Block coordinates `(row, diagonal)` in their respective parity fibres. -/
def rowDiagonalCoordinates (q : ℕ) [NeZero q] (block : Block) :
    Fin q × Fin q → Fin q × Fin q := fun uv =>
  (uv.1, parityIndex q ((blockCell q block uv).1 - (blockCell q block uv).2))

lemma rowDiagonalCoordinates_injective (q : ℕ) [NeZero q] (block : Block) :
    Function.Injective (rowDiagonalCoordinates q block) := by
  intro u v h
  dsimp [rowDiagonalCoordinates] at h
  have hrow : u.1 = v.1 := (Prod.ext_iff.mp h).1
  have hindex : parityIndex q ((blockCell q block u).1 - (blockCell q block u).2) =
      parityIndex q ((blockCell q block v).1 - (blockCell q block v).2) :=
    (Prod.ext_iff.mp h).2
  have hdiag : (blockCell q block u).1 - (blockCell q block u).2 =
      (blockCell q block v).1 - (blockCell q block v).2 := by
    have hdu : parityMap q ((blockCell q block u).1 - (blockCell q block u).2) =
        (block.squareParity.val : ZMod 2) := by
      simpa only [map_sub] using diagonal_parity q block u
    have hdv : parityMap q ((blockCell q block v).1 - (blockCell q block v).2) =
        (block.squareParity.val : ZMod 2) := by
      simpa only [map_sub] using diagonal_parity q block v
    calc
      (blockCell q block u).1 - (blockCell q block u).2 =
          parityLabel q block.squareParity
            (parityIndex q ((blockCell q block u).1 - (blockCell q block u).2)) :=
        (parityLabel_index q block.squareParity _ hdu).symm
      _ = parityLabel q block.squareParity
            (parityIndex q ((blockCell q block v).1 - (blockCell q block v).2)) := by
        rw [hindex]
      _ = (blockCell q block v).1 - (blockCell q block v).2 :=
        parityLabel_index q block.squareParity _ hdv
  have hrow' : (blockCell q block u).1 = (blockCell q block v).1 := by
    simp [blockCell, hrow]
  have hcell : blockCell q block u = blockCell q block v := by
    apply (rowDiagonal_bijective (2 * q)).1
    exact Prod.ext hrow' hdiag
  exact blockCell_injective q block hcell

lemma rowDiagonalCoordinates_bijective (q : ℕ) [NeZero q] (block : Block) :
    Function.Bijective (rowDiagonalCoordinates q block) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨rowDiagonalCoordinates_injective q block, ?_⟩
  simp

/-- A bijection of `q × q` parameters preserves the cardinality of a
predicate on its second target coordinate. -/
lemma card_selected_second_of_bijective (q : ℕ) (f : Fin q × Fin q → Fin q × Fin q)
    (hf : Function.Bijective f) (S : Finset (Fin q)) :
    (Finset.univ.filter fun uv => (f uv).2 ∈ S).card = q * S.card := by
  rw [card_filter_of_bijective f hf (fun uv => uv.2 ∈ S)]
  have htarget : (Finset.univ.filter fun uv : Fin q × Fin q => uv.2 ∈ S) =
      Finset.univ.product S := by
    ext uv
    simp
  rw [htarget, Finset.product_eq_sprod, Finset.card_product]
  simp

/-- A bijection of `q × q` parameters preserves a product predicate on its
two target coordinates. -/
lemma card_selected_pair_of_bijective (q : ℕ) (f : Fin q × Fin q → Fin q × Fin q)
    (hf : Function.Bijective f) (S T : Finset (Fin q)) :
    (Finset.univ.filter fun uv => (f uv).1 ∈ S ∧ (f uv).2 ∈ T).card = S.card * T.card := by
  rw [card_filter_of_bijective f hf (fun uv => uv.1 ∈ S ∧ uv.2 ∈ T)]
  have htarget : (Finset.univ.filter fun uv : Fin q × Fin q => uv.1 ∈ S ∧ uv.2 ∈ T) =
      S.product T := by
    ext uv
    simp
  rw [htarget, Finset.product_eq_sprod, Finset.card_product]

theorem atomCount_rowDiagonal_pair (cfg : Configuration q) (hq : 0 < q) (block : Block) :
    ∑ atom ∈ Finset.univ.filter (fun atom => atom.row && atom.diagonal), atomCount cfg block atom =
      rowCount cfg block.rowParity * diagonalCount cfg block.squareParity := by
  letI : NeZero q := ⟨by omega⟩
  letI : NeZero (2 * q) := ⟨by omega⟩
  unfold atomCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter :
      Finset.univ.filter (fun uv : Fin q × Fin q =>
        atomOfCell cfg (blockCell q block uv) ∈
          Finset.univ.filter (fun atom => atom.row && atom.diagonal)) =
      Finset.univ.filter fun uv =>
        (rowDiagonalCoordinates q block uv).1 ∈
          selectedParityLabels q block.rowParity cfg.R ∧
        (rowDiagonalCoordinates q block uv).2 ∈
          selectedParityLabels q block.squareParity cfg.D := by
    ext uv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change ((decide ((blockCell q block uv).1 ∈ cfg.R) &&
      decide ((blockCell q block uv).1 - (blockCell q block uv).2 ∈ cfg.D)) = true) ↔ _
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    simp only [selectedParityLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    change ((blockCell q block uv).1 ∈ cfg.R ∧
      (blockCell q block uv).1 - (blockCell q block uv).2 ∈ cfg.D) ↔
      (parityLabel q block.rowParity uv.1 ∈ cfg.R ∧
      parityLabel q block.squareParity
        (parityIndex q ((blockCell q block uv).1 - (blockCell q block uv).2)) ∈ cfg.D)
    have hpar : parityMap q ((blockCell q block uv).1 - (blockCell q block uv).2) =
        (block.squareParity.val : ZMod 2) := by
      simpa only [map_sub] using diagonal_parity q block uv
    rw [parityLabel_index q block.squareParity _ hpar]
    simp [blockCell]
  rw [hfilter, card_selected_pair_of_bijective q _
    (rowDiagonalCoordinates_bijective q block), card_selectedParityLabels,
    card_selectedParityLabels]
  simp [rowCount, diagonalCount]

theorem atomCount_diagonal_marginal (cfg : Configuration q) (hq : 0 < q) (block : Block) :
    ∑ atom ∈ Finset.univ.filter (fun atom => atom.diagonal), atomCount cfg block atom =
      diagonalCount cfg block.squareParity * q := by
  letI : NeZero q := ⟨by omega⟩
  letI : NeZero (2 * q) := ⟨by omega⟩
  unfold atomCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter :
      Finset.univ.filter (fun uv : Fin q × Fin q =>
        atomOfCell cfg (blockCell q block uv) ∈ Finset.univ.filter (fun atom => atom.diagonal)) =
      Finset.univ.filter fun uv =>
        (rowDiagonalCoordinates q block uv).2 ∈
          selectedParityLabels q block.squareParity cfg.D := by
    ext uv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (decide ((blockCell q block uv).1 - (blockCell q block uv).2 ∈ cfg.D) = true) ↔ _
    simp only [decide_eq_true_eq]
    simp only [selectedParityLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    change ((blockCell q block uv).1 - (blockCell q block uv).2 ∈ cfg.D) ↔
      parityLabel q block.squareParity
        (parityIndex q ((blockCell q block uv).1 - (blockCell q block uv).2)) ∈ cfg.D
    have hpar : parityMap q ((blockCell q block uv).1 - (blockCell q block uv).2) =
        (block.squareParity.val : ZMod 2) := by
      simpa only [map_sub] using diagonal_parity q block uv
    rw [parityLabel_index q block.squareParity _ hpar]
  rw [hfilter, card_selected_second_of_bijective q _
    (rowDiagonalCoordinates_bijective q block), card_selectedParityLabels]
  simp [diagonalCount, Nat.mul_comm]

/-- Block coordinates `(row, antidiagonal)` in their respective parity fibres. -/
def rowAntidiagonalCoordinates (q : ℕ) [NeZero q] (block : Block) :
    Fin q × Fin q → Fin q × Fin q := fun uv =>
  (uv.1, parityIndex q ((blockCell q block uv).1 + (blockCell q block uv).2))

lemma rowAntidiagonalCoordinates_injective (q : ℕ) [NeZero q] (block : Block) :
    Function.Injective (rowAntidiagonalCoordinates q block) := by
  intro u v h
  dsimp [rowAntidiagonalCoordinates] at h
  have hrow : u.1 = v.1 := (Prod.ext_iff.mp h).1
  have hindex : parityIndex q ((blockCell q block u).1 + (blockCell q block u).2) =
      parityIndex q ((blockCell q block v).1 + (blockCell q block v).2) :=
    (Prod.ext_iff.mp h).2
  have hanti : (blockCell q block u).1 + (blockCell q block u).2 =
      (blockCell q block v).1 + (blockCell q block v).2 := by
    have hau : parityMap q ((blockCell q block u).1 + (blockCell q block u).2) =
        (block.squareParity.val : ZMod 2) := by
      simpa only [map_add] using antidiagonal_parity q block u
    have hav : parityMap q ((blockCell q block v).1 + (blockCell q block v).2) =
        (block.squareParity.val : ZMod 2) := by
      simpa only [map_add] using antidiagonal_parity q block v
    calc
      (blockCell q block u).1 + (blockCell q block u).2 =
          parityLabel q block.squareParity
            (parityIndex q ((blockCell q block u).1 + (blockCell q block u).2)) :=
        (parityLabel_index q block.squareParity _ hau).symm
      _ = parityLabel q block.squareParity
            (parityIndex q ((blockCell q block v).1 + (blockCell q block v).2)) := by
        rw [hindex]
      _ = (blockCell q block v).1 + (blockCell q block v).2 :=
        parityLabel_index q block.squareParity _ hav
  have hrow' : (blockCell q block u).1 = (blockCell q block v).1 := by
    simp [blockCell, hrow]
  have hcell : blockCell q block u = blockCell q block v := by
    apply (rowAntidiagonal_bijective (2 * q)).1
    exact Prod.ext hrow' hanti
  exact blockCell_injective q block hcell

lemma rowAntidiagonalCoordinates_bijective (q : ℕ) [NeZero q] (block : Block) :
    Function.Bijective (rowAntidiagonalCoordinates q block) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨rowAntidiagonalCoordinates_injective q block, ?_⟩
  simp

theorem atomCount_antidiagonal_marginal (cfg : Configuration q) (hq : 0 < q)
    (block : Block) :
    ∑ atom ∈ Finset.univ.filter (fun atom => atom.antidiagonal), atomCount cfg block atom =
      antidiagonalCount cfg block.squareParity * q := by
  letI : NeZero q := ⟨by omega⟩
  letI : NeZero (2 * q) := ⟨by omega⟩
  unfold atomCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter :
      Finset.univ.filter (fun uv : Fin q × Fin q =>
        atomOfCell cfg (blockCell q block uv) ∈ Finset.univ.filter (fun atom => atom.antidiagonal)) =
      Finset.univ.filter fun uv =>
        (rowAntidiagonalCoordinates q block uv).2 ∈
          selectedParityLabels q block.squareParity cfg.A := by
    ext uv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (decide ((blockCell q block uv).1 + (blockCell q block uv).2 ∈ cfg.A) = true) ↔ _
    simp only [decide_eq_true_eq]
    simp only [selectedParityLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    change ((blockCell q block uv).1 + (blockCell q block uv).2 ∈ cfg.A) ↔
      parityLabel q block.squareParity
        (parityIndex q ((blockCell q block uv).1 + (blockCell q block uv).2)) ∈ cfg.A
    have hpar : parityMap q ((blockCell q block uv).1 + (blockCell q block uv).2) =
        (block.squareParity.val : ZMod 2) := by
      simpa only [map_add] using antidiagonal_parity q block uv
    rw [parityLabel_index q block.squareParity _ hpar]
  rw [hfilter, card_selected_second_of_bijective q _
    (rowAntidiagonalCoordinates_bijective q block), card_selectedParityLabels]
  simp [antidiagonalCount, Nat.mul_comm]

theorem atomCount_column_marginal (cfg : Configuration q) (hq : 0 < q) (block : Block) :
    ∑ atom ∈ Finset.univ.filter (fun atom => atom.column), atomCount cfg block atom =
      columnCount cfg block.columnParity * q := by
  letI : NeZero (2 * q) := ⟨by omega⟩
  unfold atomCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter :
      Finset.univ.filter (fun uv : Fin q × Fin q =>
        atomOfCell cfg (blockCell q block uv) ∈ Finset.univ.filter (fun atom => atom.column)) =
      Finset.univ.product (selectedParityLabels q block.columnParity cfg.C) := by
    ext uv
    simp [atomOfCell, blockCell, selectedParityLabels]
  rw [hfilter, Finset.product_eq_sprod, Finset.card_product, card_selectedParityLabels]
  simp [columnCount, Nat.mul_comm]

theorem atomCount_rowAntidiagonal_pair (cfg : Configuration q) (hq : 0 < q) (block : Block) :
    ∑ atom ∈ Finset.univ.filter (fun atom => atom.row && atom.antidiagonal), atomCount cfg block atom =
      rowCount cfg block.rowParity * antidiagonalCount cfg block.squareParity := by
  letI : NeZero q := ⟨by omega⟩
  letI : NeZero (2 * q) := ⟨by omega⟩
  unfold atomCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter :
      Finset.univ.filter (fun uv : Fin q × Fin q =>
        atomOfCell cfg (blockCell q block uv) ∈
          Finset.univ.filter (fun atom => atom.row && atom.antidiagonal)) =
      Finset.univ.filter fun uv =>
        (rowAntidiagonalCoordinates q block uv).1 ∈ selectedParityLabels q block.rowParity cfg.R ∧
        (rowAntidiagonalCoordinates q block uv).2 ∈ selectedParityLabels q block.squareParity cfg.A := by
    ext uv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change ((decide ((blockCell q block uv).1 ∈ cfg.R) &&
      decide ((blockCell q block uv).1 + (blockCell q block uv).2 ∈ cfg.A)) = true) ↔ _
    simp only [Bool.and_eq_true, decide_eq_true_eq, selectedParityLabels,
      Finset.mem_filter, Finset.mem_univ, true_and]
    change ((blockCell q block uv).1 ∈ cfg.R ∧
      (blockCell q block uv).1 + (blockCell q block uv).2 ∈ cfg.A) ↔
      (parityLabel q block.rowParity uv.1 ∈ cfg.R ∧
      parityLabel q block.squareParity
        (parityIndex q ((blockCell q block uv).1 + (blockCell q block uv).2)) ∈ cfg.A)
    have hpar : parityMap q ((blockCell q block uv).1 + (blockCell q block uv).2) =
        (block.squareParity.val : ZMod 2) := by
      simpa only [map_add] using antidiagonal_parity q block uv
    rw [parityLabel_index q block.squareParity _ hpar]
    simp [blockCell]
  rw [hfilter, card_selected_pair_of_bijective q _
    (rowAntidiagonalCoordinates_bijective q block), card_selectedParityLabels,
    card_selectedParityLabels]
  simp [rowCount, antidiagonalCount]

theorem atomCount_rowColumn_pair (cfg : Configuration q) (hq : 0 < q) (block : Block) :
    ∑ atom ∈ Finset.univ.filter (fun atom => atom.row && atom.column), atomCount cfg block atom =
      rowCount cfg block.rowParity * columnCount cfg block.columnParity := by
  letI : NeZero (2 * q) := ⟨by omega⟩
  unfold atomCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter :
      Finset.univ.filter (fun uv : Fin q × Fin q =>
        atomOfCell cfg (blockCell q block uv) ∈
          Finset.univ.filter (fun atom => atom.row && atom.column)) =
      (selectedParityLabels q block.rowParity cfg.R).product
        (selectedParityLabels q block.columnParity cfg.C) := by
    ext uv
    simp [atomOfCell, blockCell, selectedParityLabels]
  rw [hfilter, Finset.product_eq_sprod, Finset.card_product, card_selectedParityLabels,
    card_selectedParityLabels]
  simp [rowCount, columnCount]

def columnDiagonalCoordinates (q : ℕ) [NeZero q] (block : Block) :
    Fin q × Fin q → Fin q × Fin q := fun uv =>
  (uv.2, parityIndex q ((blockCell q block uv).1 - (blockCell q block uv).2))

lemma columnDiagonalCoordinates_bijective (q : ℕ) [NeZero q] (block : Block) :
    Function.Bijective (columnDiagonalCoordinates q block) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simp⟩
  intro u v h
  dsimp [columnDiagonalCoordinates] at h
  have hcol : u.2 = v.2 := (Prod.ext_iff.mp h).1
  have hindex := (Prod.ext_iff.mp h).2
  change parityIndex q ((blockCell q block u).1 - (blockCell q block u).2) =
    parityIndex q ((blockCell q block v).1 - (blockCell q block v).2) at hindex
  have hdiag : (blockCell q block u).1 - (blockCell q block u).2 =
      (blockCell q block v).1 - (blockCell q block v).2 := by
    have hdu : parityMap q ((blockCell q block u).1 - (blockCell q block u).2) =
        (block.squareParity.val : ZMod 2) := by simpa only [map_sub] using diagonal_parity q block u
    have hdv : parityMap q ((blockCell q block v).1 - (blockCell q block v).2) =
        (block.squareParity.val : ZMod 2) := by simpa only [map_sub] using diagonal_parity q block v
    calc
      (blockCell q block u).1 - (blockCell q block u).2 = parityLabel q block.squareParity
          (parityIndex q ((blockCell q block u).1 - (blockCell q block u).2)) :=
        (parityLabel_index q block.squareParity _ hdu).symm
      _ = parityLabel q block.squareParity
          (parityIndex q ((blockCell q block v).1 - (blockCell q block v).2)) := by rw [hindex]
      _ = (blockCell q block v).1 - (blockCell q block v).2 := parityLabel_index q block.squareParity _ hdv
  have hcol' : (blockCell q block u).2 = (blockCell q block v).2 := by simp [blockCell, hcol]
  apply blockCell_injective q block
  apply (columnDiagonal_bijective (2 * q)).1
  exact Prod.ext hcol' hdiag

theorem atomCount_columnDiagonal_pair (cfg : Configuration q) (hq : 0 < q) (block : Block) :
    ∑ atom ∈ Finset.univ.filter (fun atom => atom.column && atom.diagonal), atomCount cfg block atom =
      columnCount cfg block.columnParity * diagonalCount cfg block.squareParity := by
  letI : NeZero q := ⟨by omega⟩
  letI : NeZero (2 * q) := ⟨by omega⟩
  unfold atomCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter :
      Finset.univ.filter (fun uv : Fin q × Fin q => atomOfCell cfg (blockCell q block uv) ∈
        Finset.univ.filter (fun atom => atom.column && atom.diagonal)) =
      Finset.univ.filter fun uv =>
        (columnDiagonalCoordinates q block uv).1 ∈ selectedParityLabels q block.columnParity cfg.C ∧
        (columnDiagonalCoordinates q block uv).2 ∈ selectedParityLabels q block.squareParity cfg.D := by
    ext uv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change ((decide ((blockCell q block uv).2 ∈ cfg.C) &&
      decide ((blockCell q block uv).1 - (blockCell q block uv).2 ∈ cfg.D)) = true) ↔ _
    simp only [Bool.and_eq_true, decide_eq_true_eq, selectedParityLabels,
      Finset.mem_filter, Finset.mem_univ, true_and]
    change ((blockCell q block uv).2 ∈ cfg.C ∧ (blockCell q block uv).1 - (blockCell q block uv).2 ∈ cfg.D) ↔
      (parityLabel q block.columnParity uv.2 ∈ cfg.C ∧ parityLabel q block.squareParity
        (parityIndex q ((blockCell q block uv).1 - (blockCell q block uv).2)) ∈ cfg.D)
    have hpar : parityMap q ((blockCell q block uv).1 - (blockCell q block uv).2) =
        (block.squareParity.val : ZMod 2) := by simpa only [map_sub] using diagonal_parity q block uv
    rw [parityLabel_index q block.squareParity _ hpar]
    simp [blockCell]
  rw [hfilter, card_selected_pair_of_bijective q _
    (columnDiagonalCoordinates_bijective q block), card_selectedParityLabels, card_selectedParityLabels]
  simp [columnCount, diagonalCount]

def columnAntidiagonalCoordinates (q : ℕ) [NeZero q] (block : Block) :
    Fin q × Fin q → Fin q × Fin q := fun uv =>
  (uv.2, parityIndex q ((blockCell q block uv).1 + (blockCell q block uv).2))

lemma columnAntidiagonalCoordinates_bijective (q : ℕ) [NeZero q] (block : Block) :
    Function.Bijective (columnAntidiagonalCoordinates q block) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simp⟩
  intro u v h
  dsimp [columnAntidiagonalCoordinates] at h
  have hcol : u.2 = v.2 := (Prod.ext_iff.mp h).1
  have hindex := (Prod.ext_iff.mp h).2
  change parityIndex q ((blockCell q block u).1 + (blockCell q block u).2) =
    parityIndex q ((blockCell q block v).1 + (blockCell q block v).2) at hindex
  have hanti : (blockCell q block u).1 + (blockCell q block u).2 =
      (blockCell q block v).1 + (blockCell q block v).2 := by
    have hau : parityMap q ((blockCell q block u).1 + (blockCell q block u).2) =
        (block.squareParity.val : ZMod 2) := by simpa only [map_add] using antidiagonal_parity q block u
    have hav : parityMap q ((blockCell q block v).1 + (blockCell q block v).2) =
        (block.squareParity.val : ZMod 2) := by simpa only [map_add] using antidiagonal_parity q block v
    calc
      (blockCell q block u).1 + (blockCell q block u).2 = parityLabel q block.squareParity
          (parityIndex q ((blockCell q block u).1 + (blockCell q block u).2)) :=
        (parityLabel_index q block.squareParity _ hau).symm
      _ = parityLabel q block.squareParity
          (parityIndex q ((blockCell q block v).1 + (blockCell q block v).2)) := by rw [hindex]
      _ = (blockCell q block v).1 + (blockCell q block v).2 := parityLabel_index q block.squareParity _ hav
  have hcol' : (blockCell q block u).2 = (blockCell q block v).2 := by simp [blockCell, hcol]
  apply blockCell_injective q block
  apply (columnAntidiagonal_bijective (2 * q)).1
  exact Prod.ext hcol' hanti

theorem atomCount_columnAntidiagonal_pair (cfg : Configuration q) (hq : 0 < q) (block : Block) :
    ∑ atom ∈ Finset.univ.filter (fun atom => atom.column && atom.antidiagonal), atomCount cfg block atom =
      columnCount cfg block.columnParity * antidiagonalCount cfg block.squareParity := by
  letI : NeZero q := ⟨by omega⟩
  letI : NeZero (2 * q) := ⟨by omega⟩
  unfold atomCount
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have hfilter :
      Finset.univ.filter (fun uv : Fin q × Fin q => atomOfCell cfg (blockCell q block uv) ∈
        Finset.univ.filter (fun atom => atom.column && atom.antidiagonal)) =
      Finset.univ.filter fun uv =>
        (columnAntidiagonalCoordinates q block uv).1 ∈ selectedParityLabels q block.columnParity cfg.C ∧
        (columnAntidiagonalCoordinates q block uv).2 ∈ selectedParityLabels q block.squareParity cfg.A := by
    ext uv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change ((decide ((blockCell q block uv).2 ∈ cfg.C) &&
      decide ((blockCell q block uv).1 + (blockCell q block uv).2 ∈ cfg.A)) = true) ↔ _
    simp only [Bool.and_eq_true, decide_eq_true_eq, selectedParityLabels,
      Finset.mem_filter, Finset.mem_univ, true_and]
    change ((blockCell q block uv).2 ∈ cfg.C ∧ (blockCell q block uv).1 + (blockCell q block uv).2 ∈ cfg.A) ↔
      (parityLabel q block.columnParity uv.2 ∈ cfg.C ∧ parityLabel q block.squareParity
        (parityIndex q ((blockCell q block uv).1 + (blockCell q block uv).2)) ∈ cfg.A)
    have hpar : parityMap q ((blockCell q block uv).1 + (blockCell q block uv).2) =
        (block.squareParity.val : ZMod 2) := by simpa only [map_add] using antidiagonal_parity q block uv
    rw [parityLabel_index q block.squareParity _ hpar]
    simp [blockCell]
  rw [hfilter, card_selected_pair_of_bijective q _
    (columnAntidiagonalCoordinates_bijective q block), card_selectedParityLabels, card_selectedParityLabels]
  simp [columnCount, antidiagonalCount]

/-! ## S26: aggregated diagonal/antidiagonal moment -/

def selectedDA (cfg : Configuration q) [NeZero (2 * q)] (e : Parity) : Finset (Cell (2 * q)) :=
  Finset.univ.filter fun x => x.1 - x.2 ∈ cfg.D ∧
    parityMap q (x.1 - x.2) = (e.val : ZMod 2) ∧ x.1 + x.2 ∈ cfg.A

def selectedDAPairs (cfg : Configuration q) (e : Parity) : Finset (Cell (2 * q)) :=
  (cfg.D.filter fun d => parityMap q d = (e.val : ZMod 2)).product
    (cfg.A.filter fun a => parityMap q a = (e.val : ZMod 2))

lemma selectedDAPairs_card (cfg : Configuration q) (e : Parity) :
    (selectedDAPairs cfg e).card = diagonalCount cfg e * antidiagonalCount cfg e := by
  unfold selectedDAPairs diagonalCount antidiagonalCount
  rw [Finset.product_eq_sprod, Finset.card_product]

lemma selectedDA_eq_label_preimage (cfg : Configuration q) [NeZero (2 * q)] (e : Parity) :
    selectedDA cfg e = Finset.univ.filter fun x =>
      diagonalAntidiagonalLabels (2 * q) x ∈ selectedDAPairs cfg e := by
  ext x
  simp only [selectedDA, selectedDAPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    diagonalAntidiagonalLabels]
  constructor
  · rintro ⟨hd, he, ha⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hd, he⟩, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
    exact (parity_diagonal_eq_antidiagonal q x).symm.trans he
  · intro hx
    have hx' := Finset.mem_product.mp hx
    obtain ⟨hd, he⟩ := Finset.mem_filter.mp hx'.1
    obtain ⟨ha, _⟩ := Finset.mem_filter.mp hx'.2
    exact ⟨hd, he, ha⟩

theorem card_selectedDA (cfg : Configuration q) [NeZero q] (hq : 0 < q) (e : Parity) :
    (selectedDA cfg e).card = 2 * diagonalCount cfg e * antidiagonalCount cfg e := by
  letI : NeZero (2 * q) := ⟨by omega⟩
  rw [selectedDA_eq_label_preimage, ← Finset.sum_card_fiberwise_eq_card_filter]
  have hfib (y : Cell (2 * q)) (hy : y ∈ selectedDAPairs cfg e) :
      (Finset.univ.filter fun x => diagonalAntidiagonalLabels (2 * q) x = y).card = 2 := by
    have hpar : parityMap q y.1 = parityMap q y.2 := by
      have hy' := Finset.mem_product.mp hy
      exact (Finset.mem_filter.mp hy'.1).2.trans (Finset.mem_filter.mp hy'.2).2.symm
    obtain ⟨x, hx⟩ := (diagonalAntidiagonal_mem_range_iff q y.1 y.2).mpr hpar
    rw [← Prod.eta y, ← hx]
    exact card_diagonalAntidiagonalFibre_of_image q x
  calc
    ∑ y ∈ selectedDAPairs cfg e, (Finset.univ.filter fun x =>
        diagonalAntidiagonalLabels (2 * q) x = y).card =
      ∑ _y ∈ selectedDAPairs cfg e, 2 := by
        apply Finset.sum_congr rfl; intro y hy; exact hfib y hy
    _ = 2 * (selectedDAPairs cfg e).card := by simp [Nat.mul_comm]
    _ = 2 * diagonalCount cfg e * antidiagonalCount cfg e := by rw [selectedDAPairs_card]; ring

def blockSelectedDA (cfg : Configuration q) [NeZero (2 * q)] (block : Block) : Finset (Cell (2 * q)) :=
  (blockCells q block).filter fun x => x.1 - x.2 ∈ cfg.D ∧ x.1 + x.2 ∈ cfg.A

def aggregateDAAtomCount (cfg : Configuration q) (e : Parity) : ℕ :=
  ∑ block ∈ Finset.univ.filter (fun block => block.squareParity = e),
    ∑ atom ∈ Finset.univ.filter (fun atom => atom.diagonal && atom.antidiagonal), atomCount cfg block atom

def selectedBlocks (e : Parity) : Finset Block := Finset.univ.filter fun block => block.squareParity = e

def cellBlock (q : ℕ) (x : Cell (2 * q)) : Block :=
  ⟨⟨(parityMap q x.1).val, (parityMap q x.1).isLt⟩,
    ⟨(parityMap q x.2).val, (parityMap q x.2).isLt⟩⟩

lemma mem_blockCells_cellBlock (q : ℕ) [NeZero (2 * q)] (x : Cell (2 * q)) :
    x ∈ blockCells q (cellBlock q x) := by
  apply (mem_blockCells_iff q (cellBlock q x) x).mpr
  exact ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩

lemma diagonalParity_cellBlock (q : ℕ) (x : Cell (2 * q)) :
    parityMap q (x.1 - x.2) = ((cellBlock q x).squareParity.val : ZMod 2) := by
  rw [map_sub]
  change parityMap q x.1 - parityMap q x.2 = _
  simp only [cellBlock, Block.squareParity]
  generalize parityMap q x.1 = r
  generalize parityMap q x.2 = c
  fin_cases r <;> fin_cases c <;> decide

def blockSelectedDAUnion (cfg : Configuration q) [NeZero (2 * q)] (e : Parity) : Finset (Cell (2 * q)) :=
  (selectedBlocks e).biUnion (blockSelectedDA cfg)

lemma blockSelectedDA_subset_selectedDA (cfg : Configuration q) [NeZero (2 * q)]
    (e : Parity) (block : Block) (hblock : block.squareParity = e) :
    blockSelectedDA cfg block ⊆ selectedDA cfg e := by
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  have hmem := (mem_blockCells_iff q block x).mp hx'.1
  have hpar : parityMap q (x.1 - x.2) = (e.val : ZMod 2) := by
    rw [← hblock]
    rcases block with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [Block.squareParity] at hmem ⊢ <;>
      simpa [hmem.1, hmem.2]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'.2.1, hpar, hx'.2.2⟩

lemma blockSelectedDAUnion_eq_selectedDA (cfg : Configuration q) [NeZero (2 * q)] (e : Parity) :
    blockSelectedDAUnion cfg e = selectedDA cfg e := by
  ext x
  constructor
  · rintro hx
    obtain ⟨block, hb, hx⟩ := Finset.mem_biUnion.mp hx
    exact blockSelectedDA_subset_selectedDA cfg e block (Finset.mem_filter.mp hb).2 hx
  · intro hx
    have hx' := Finset.mem_filter.mp hx
    let block := cellBlock q x
    have hsq : block.squareParity = e := by
      apply Fin.ext
      have hlabel : ((block.squareParity.val : ℕ) : ZMod 2) = (e.val : ZMod 2) :=
        (diagonalParity_cellBlock q x).symm.trans hx'.2.2.1
      generalize hs : block.squareParity = s at hlabel ⊢
      fin_cases s <;> fin_cases e <;> simp_all
    apply Finset.mem_biUnion.mpr
    refine ⟨block, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsq⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨mem_blockCells_cellBlock q x, hx'.2.1, hx'.2.2.2⟩

lemma blockSelectedDA_pairwiseDisjoint (cfg : Configuration q) [NeZero (2 * q)] (e : Parity) :
    (selectedBlocks e : Set Block).PairwiseDisjoint (blockSelectedDA cfg) := by
  intro b _ c _ hne
  change Disjoint (blockSelectedDA cfg b) (blockSelectedDA cfg c)
  rw [Finset.disjoint_left]
  intro x hxb hxc
  apply hne
  have pb := (mem_blockCells_iff q b x).mp (Finset.mem_filter.mp hxb).1
  have pc := (mem_blockCells_iff q c x).mp (Finset.mem_filter.mp hxc).1
  have hr : b.rowParity = c.rowParity := by
    apply Fin.ext
    have hv := congrArg ZMod.val (pb.1.symm.trans pc.1)
    have hv' : b.rowParity.val % 2 = c.rowParity.val % 2 := by simpa using hv
    omega
  have hc : b.columnParity = c.columnParity := by
    apply Fin.ext
    have hv := congrArg ZMod.val (pb.2.symm.trans pc.2)
    have hv' : b.columnParity.val % 2 = c.columnParity.val % 2 := by simpa using hv
    omega
  cases b; cases c; simp_all

lemma atomDA_sum_eq_blockSelectedDA_card (cfg : Configuration q) [NeZero (2 * q)] (block : Block) :
    ∑ atom ∈ Finset.univ.filter (fun atom => atom.diagonal && atom.antidiagonal), atomCount cfg block atom =
      (blockSelectedDA cfg block).card := by
  simp_rw [atomCount_eq_cellAtomCount]
  unfold cellAtomCount blockSelectedDA
  change (∑ atom ∈ Finset.univ.filter (fun atom => atom.diagonal && atom.antidiagonal),
    ((blockCells q block).filter fun x => atomOfCell cfg x = atom).card) = _
  rw [Finset.sum_card_fiberwise_eq_card_filter (blockCells q block)
    (Finset.univ.filter fun atom => atom.diagonal && atom.antidiagonal) (atomOfCell cfg)]
  congr 1; ext x; simp [atomOfCell]

/-- Paper `lem:inc` (even fibres) and the two aggregate rows `eq:mom3` of
`lem:moments` (S26): the two blocks of square parity `e` together contain
exactly `2·d_e·a_e` cells whose diagonal and antidiagonal are both black.
The argument is uniform in `q` (disjoint blocks cover the selected two-cell
fibres), so it covers `4 ∣ 2q`, where both lifts land in one block. -/
theorem aggregateDAAtomCount_eq (cfg : Configuration q) (hq : 0 < q) (e : Parity) :
    aggregateDAAtomCount cfg e = 2 * diagonalCount cfg e * antidiagonalCount cfg e := by
  letI : NeZero q := ⟨by omega⟩
  letI : NeZero (2 * q) := ⟨by omega⟩
  rw [aggregateDAAtomCount]
  simp_rw [atomDA_sum_eq_blockSelectedDA_card cfg]
  change (∑ block ∈ selectedBlocks e, (blockSelectedDA cfg block).card) = _
  rw [← Finset.card_biUnion (blockSelectedDA_pairwiseDisjoint cfg e)]
  change (blockSelectedDAUnion cfg e).card = _
  rw [blockSelectedDAUnion_eq_selectedDA]
  exact card_selectedDA cfg hq e

#print axioms card_blockCells
#print axioms atomCount_normalization
#print axioms atomFrequency_normalization
#print axioms atomCount_row_marginal
#print axioms atomCount_diagonal_marginal
#print axioms atomCount_antidiagonal_marginal
#print axioms atomCount_column_marginal
#print axioms atomCount_rowDiagonal_pair
#print axioms atomCount_rowAntidiagonal_pair
#print axioms atomCount_rowColumn_pair
#print axioms atomCount_columnDiagonal_pair
#print axioms atomCount_columnAntidiagonal_pair
#print axioms aggregateDAAtomCount_eq

end PeaceableQueens.UpperBound.BlockMoments
