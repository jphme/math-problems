import PeaceableQueens.UpperBound.BlockMoments

namespace PeaceableQueens.UpperBound.ConfigurationMoments

open MomentModel ConfigurationBridge BlockMoments Incidence

def configurationWeights (cfg : Configuration q) : InnerAtom → ℚ :=
  fun inner => atomFrequency cfg inner.block inner.atom

def innerAtomEquiv : InnerAtom ≃ Block × Atom where
  toFun x := (x.block, x.atom)
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

lemma sum_inner_eq_sum_blocks (f : InnerAtom → ℚ) :
    ∑ inner, f inner = ∑ block : Block, ∑ atom : Atom, f ⟨block, atom⟩ := by
  rw [Fintype.sum_equiv innerAtomEquiv f (fun x => f ⟨x.1, x.2⟩) (fun x => by cases x; rfl)]
  simp only [Fintype.sum_prod_type]

lemma block_coefficient_sum (cfg : Configuration q) (block : Block) (moment : BlockMoment) :
    ∑ inner, matrixRow (.block block moment) inner * configurationWeights cfg inner =
      ∑ atom, if moment.eval atom then atomFrequency cfg block atom else 0 := by
  rw [sum_inner_eq_sum_blocks]
  simp only [matrixRow, coefficient, configurationWeights]
  classical
  rw [Finset.sum_eq_single block]
  · simp
  · intro b _ hne
    apply Finset.sum_eq_zero; intro atom _; simp [hne]
  · simp

lemma frequency_sum_filter_eq_div (cfg : Configuration q) (block : Block) (P : Atom → Prop)
    [DecidablePred P] (n : ℕ)
    (hcount : ∑ atom ∈ Finset.univ.filter P, atomCount cfg block atom = n) :
    ∑ atom : Atom, (if P atom then atomFrequency cfg block atom else (0 : ℚ)) =
      (n : ℚ) / (q ^ 2 : ℚ) := by
  rw [← Finset.sum_filter]
  simp_rw [atomFrequency]
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast hcount

lemma frequency_linear (cfg : Configuration q) (hq : 0 < q) (block : Block) (P : Atom → Prop)
    [DecidablePred P] (n : ℕ)
    (hcount : ∑ atom ∈ Finset.univ.filter P, atomCount cfg block atom = n * q) :
    ∑ atom : Atom, (if P atom then atomFrequency cfg block atom else (0 : ℚ)) = (n : ℚ) / q := by
  rw [frequency_sum_filter_eq_div cfg block P (n*q) hcount]
  push_cast; field_simp

lemma frequency_product (cfg : Configuration q) (hq : 0 < q) (block : Block) (P : Atom → Prop)
    [DecidablePred P] (m n : ℕ)
    (hcount : ∑ atom ∈ Finset.univ.filter P, atomCount cfg block atom = m * n) :
    ∑ atom : Atom, (if P atom then atomFrequency cfg block atom else (0 : ℚ)) =
      ((m : ℚ) / q) * ((n : ℚ) / q) := by
  rw [frequency_sum_filter_eq_div cfg block P (m*n) hcount]
  push_cast; field_simp

lemma block_moment_equation (cfg : Configuration q) (hq : 0 < q) (block : Block)
    (moment : BlockMoment) :
    ∑ inner, matrixRow (.block block moment) inner * configurationWeights cfg inner =
      rhs (normalizedProfile cfg) (.block block moment) := by
  rw [block_coefficient_sum]
  cases moment with
  | normalization =>
      have hfreq : (∑ atom : Atom, if BlockMoment.normalization.eval atom = true then
          atomFrequency cfg block atom else 0) = 1 := by
        simpa only [BlockMoment.eval, if_true] using atomFrequency_normalization cfg hq block
      simpa [rhs, rhsTerm, RhsTerm.eval] using hfreq
  | row =>
      rw [frequency_linear cfg hq block _ (rowCount cfg block.rowParity) (by
        simpa only [BlockMoment.eval] using atomCount_row_marginal cfg hq block)]
      simp [rhs, rhsTerm, RhsTerm.eval, normalizedProfile, outerCount, blockCoord]
  | column =>
      rw [frequency_linear cfg hq block _ (columnCount cfg block.columnParity) (by
        simpa only [BlockMoment.eval] using atomCount_column_marginal cfg hq block)]
      simp [rhs, rhsTerm, RhsTerm.eval, normalizedProfile, outerCount, blockCoord]
  | diagonal =>
      rw [frequency_linear cfg hq block _ (diagonalCount cfg block.squareParity) (by
        simpa only [BlockMoment.eval] using atomCount_diagonal_marginal cfg hq block)]
      simp [rhs, rhsTerm, RhsTerm.eval, normalizedProfile, outerCount, blockCoord]
  | antidiagonal =>
      rw [frequency_linear cfg hq block _ (antidiagonalCount cfg block.squareParity) (by
        simpa only [BlockMoment.eval] using atomCount_antidiagonal_marginal cfg hq block)]
      simp [rhs, rhsTerm, RhsTerm.eval, normalizedProfile, outerCount, blockCoord]
  | rowColumn =>
      rw [frequency_product cfg hq block _ (rowCount cfg block.rowParity) (columnCount cfg block.columnParity) (by
        simpa only [BlockMoment.eval] using atomCount_rowColumn_pair cfg hq block)]
      simp [rhs, rhsTerm, RhsTerm.eval, normalizedProfile, outerCount, blockCoord]
  | rowDiagonal =>
      rw [frequency_product cfg hq block _ (rowCount cfg block.rowParity) (diagonalCount cfg block.squareParity) (by
        simpa only [BlockMoment.eval] using atomCount_rowDiagonal_pair cfg hq block)]
      simp [rhs, rhsTerm, RhsTerm.eval, normalizedProfile, outerCount, blockCoord]
  | rowAntidiagonal =>
      rw [frequency_product cfg hq block _ (rowCount cfg block.rowParity) (antidiagonalCount cfg block.squareParity) (by
        simpa only [BlockMoment.eval] using atomCount_rowAntidiagonal_pair cfg hq block)]
      simp [rhs, rhsTerm, RhsTerm.eval, normalizedProfile, outerCount, blockCoord]
  | columnDiagonal =>
      rw [frequency_product cfg hq block _ (columnCount cfg block.columnParity) (diagonalCount cfg block.squareParity) (by
        simpa only [BlockMoment.eval] using atomCount_columnDiagonal_pair cfg hq block)]
      simp [rhs, rhsTerm, RhsTerm.eval, normalizedProfile, outerCount, blockCoord]
  | columnAntidiagonal =>
      rw [frequency_product cfg hq block _ (columnCount cfg block.columnParity) (antidiagonalCount cfg block.squareParity) (by
        simpa only [BlockMoment.eval] using atomCount_columnAntidiagonal_pair cfg hq block)]
      simp [rhs, rhsTerm, RhsTerm.eval, normalizedProfile, outerCount, blockCoord]

lemma aggregate_coefficient_sum (cfg : Configuration q) (e : Parity) :
    ∑ inner, matrixRow (.aggregateDA e) inner * configurationWeights cfg inner =
      ∑ block ∈ selectedBlocks e, ∑ atom ∈ Finset.univ.filter
        (fun atom => atom.diagonal && atom.antidiagonal), atomFrequency cfg block atom := by
  rw [sum_inner_eq_sum_blocks]
  simp only [matrixRow, coefficient, configurationWeights, selectedBlocks]
  classical
  simp only [Bool.and_eq_true, ite_mul, one_mul, zero_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro block _
  by_cases h : block.squareParity = e <;> simp [h]

lemma aggregate_moment_equation (cfg : Configuration q) (hq : 0 < q) (e : Parity) :
    ∑ inner, matrixRow (.aggregateDA e) inner * configurationWeights cfg inner =
      rhs (normalizedProfile cfg) (.aggregateDA e) := by
  rw [aggregate_coefficient_sum]
  simp_rw [atomFrequency, ← Finset.sum_div]
  rw [show (∑ block ∈ selectedBlocks e,
      ∑ atom ∈ Finset.univ.filter (fun atom => atom.diagonal && atom.antidiagonal),
        (atomCount cfg block atom : ℚ)) = (aggregateDAAtomCount cfg e : ℚ) by exact_mod_cast rfl]
  rw [aggregateDAAtomCount_eq cfg hq e]
  simp [rhs, rhsTerm, RhsTerm.eval, normalizedProfile, outerCount]
  field_simp

lemma cellBlock_eq_of_mem (q : ℕ) [NeZero (2 * q)] (x : Cell (2 * q)) (block : Block)
    (hx : x ∈ blockCells q block) : cellBlock q x = block := by
  have hp := (mem_blockCells_iff q block x).mp hx
  cases block with
  | mk i j =>
    fin_cases i <;> fin_cases j <;>
      simp only [cellBlock, Block.mk.injEq] at * <;>
      constructor <;> apply Fin.ext <;>
      simp_all only [ZMod.val_natCast]

lemma blockCells_pairwiseDisjoint (q : ℕ) [NeZero (2 * q)] :
    Set.PairwiseDisjoint (Finset.univ : Finset Block) (blockCells q) := by
  intro b₁ _ b₂ _ hne
  change Disjoint (blockCells q b₁) (blockCells q b₂)
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  exact hne ((cellBlock_eq_of_mem q x b₁ hx₁).symm.trans (cellBlock_eq_of_mem q x b₂ hx₂))

lemma biUnion_blockCells (q : ℕ) [NeZero (2 * q)] :
    (Finset.univ : Finset Block).biUnion (blockCells q) =
      (Finset.univ : Finset (Cell (2 * q))) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ]
  constructor
  · intro _; trivial
  · intro _
    exact ⟨cellBlock q x, trivial, mem_blockCells_cellBlock q x⟩

lemma atomCount_total (cfg : Configuration q) [NeZero (2 * q)] (atom : Atom) :
    ∑ block, atomCount cfg block atom =
      (Finset.univ.filter fun x : Cell (2 * q) => atomOfCell cfg x = atom).card := by
  simp_rw [atomCount_eq_cellAtomCount]
  unfold cellAtomCount
  have hdis : Set.PairwiseDisjoint (Finset.univ : Finset Block)
      (fun block => (blockCells q block).filter fun x => atomOfCell cfg x = atom) := by
    intro b _ c _ hne
    change Disjoint ((blockCells q b).filter fun x => atomOfCell cfg x = atom)
      ((blockCells q c).filter fun x => atomOfCell cfg x = atom)
    rw [Finset.disjoint_left]
    intro x hxb hxc
    have hbase : Disjoint (blockCells q b) (blockCells q c) :=
      blockCells_pairwiseDisjoint q (Finset.mem_univ _) (Finset.mem_univ _) hne
    exact Finset.disjoint_left.mp hbase (Finset.mem_filter.mp hxb).1
      (Finset.mem_filter.mp hxc).1
  rw [← Finset.card_biUnion hdis]
  have hunion : (Finset.univ : Finset Block).biUnion
      (fun block => (blockCells q block).filter fun x => atomOfCell cfg x = atom) =
      ((Finset.univ : Finset Block).biUnion (blockCells q)).filter
        (fun x => atomOfCell cfg x = atom) := by
    ext x
    simp
  rw [hunion, biUnion_blockCells]

lemma atomOfCell_eq_blackAtom_iff (cfg : Configuration q) (x : Cell (2 * q)) :
    atomOfCell cfg x = blackAtom ↔
      x.1 ∈ cfg.R ∧ x.2 ∈ cfg.C ∧ x.1 - x.2 ∈ cfg.D ∧ x.1 + x.2 ∈ cfg.A := by
  simp [atomOfCell, blackAtom]

lemma atomOfCell_eq_whiteAtom_iff (cfg : Configuration q) (x : Cell (2 * q)) :
    atomOfCell cfg x = whiteAtom ↔
      x.1 ∉ cfg.R ∧ x.2 ∉ cfg.C ∧ x.1 - x.2 ∉ cfg.D ∧ x.1 + x.2 ∉ cfg.A := by
  simp [atomOfCell, whiteAtom]

theorem atomCount_black_total (cfg : Configuration q) [NeZero (2 * q)] :
    ∑ block, atomCount cfg block blackAtom = cfg.blackCells.card := by
  rw [atomCount_total]
  congr 1
  ext x
  simp [Configuration.blackCells, PeaceableQueens.blackCells, atomOfCell_eq_blackAtom_iff]

theorem atomCount_white_total (cfg : Configuration q) [NeZero (2 * q)] :
    ∑ block, atomCount cfg block whiteAtom = cfg.whiteCells.card := by
  rw [atomCount_total]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change atomOfCell cfg x = whiteAtom ↔
    x ∈ PeaceableQueens.blackCells cfg.Rᶜ cfg.Cᶜ cfg.Dᶜ cfg.Aᶜ
  rw [atomOfCell_eq_whiteAtom_iff]
  simp [PeaceableQueens.blackCells]

theorem configurationWeights_nonnegative (cfg : Configuration q) :
    Nonnegative (configurationWeights cfg) := by
  intro inner
  unfold configurationWeights atomFrequency
  positivity

/-- Paper `lem:moments` (S27): the atom frequencies of every configuration
satisfy all 42 moment equations at its normalized profile. -/
theorem configurationWeights_satisfiesMoments (cfg : Configuration q) (hq : 0 < q) :
    SatisfiesMoments (normalizedProfile cfg) (configurationWeights cfg) := by
  intro row
  cases row with
  | block block moment => exact block_moment_equation cfg hq block moment
  | aggregateDA e => exact aggregate_moment_equation cfg hq e

/-- Paper `eq:BW`: the black objective of the moment system is `|B|/q²`. -/
theorem configurationWeights_blackTotal (cfg : Configuration q) [NeZero (2 * q)] :
    blackTotal (configurationWeights cfg) =
      (cfg.blackCells.card : ℚ) / (q ^ 2 : ℚ) := by
  unfold blackTotal atomTotal
  rw [sum_inner_eq_sum_blocks]
  simp only [configurationWeights]
  simp
  simp_rw [atomFrequency]
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast atomCount_black_total cfg

/-- Paper `eq:BW`: the white objective of the moment system is `|W|/q²`. -/
theorem configurationWeights_whiteTotal (cfg : Configuration q) [NeZero (2 * q)] :
    whiteTotal (configurationWeights cfg) =
      (cfg.whiteCells.card : ℚ) / (q ^ 2 : ℚ) := by
  unfold whiteTotal atomTotal
  rw [sum_inner_eq_sum_blocks]
  simp only [configurationWeights]
  simp
  simp_rw [atomFrequency]
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast atomCount_white_total cfg

#print axioms configurationWeights_nonnegative
#print axioms configurationWeights_satisfiesMoments
#print axioms configurationWeights_blackTotal
#print axioms configurationWeights_whiteTotal

end PeaceableQueens.UpperBound.ConfigurationMoments
