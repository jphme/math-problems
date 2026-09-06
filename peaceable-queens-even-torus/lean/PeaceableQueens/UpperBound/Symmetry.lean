import PeaceableQueens.UpperBound.Configuration
import PeaceableQueens.FiniteGeometry

namespace PeaceableQueens.UpperBound.ConfigurationBridge

open MomentModel

/-! Paper `lem:budget` and `lem:chamber` (S23, S28--S29): the symmetry actions
on configurations and the canonical-chamber normalization. -/

section Complement

def complementConfig {q : ℕ} [NeZero (2 * q)] (cfg : Configuration q) : Configuration q :=
  ⟨cfg.Rᶜ, cfg.Cᶜ, cfg.Dᶜ, cfg.Aᶜ⟩

export PeaceableQueens.Parity (parity_filter_subset_class card_parity_filter_compl)

@[simp] theorem blackCells_complementConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    (complementConfig cfg).blackCells = cfg.whiteCells := rfl

@[simp] theorem whiteCells_complementConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    (complementConfig cfg).whiteCells = cfg.blackCells := by
  ext p
  simp [Configuration.whiteCells, PeaceableQueens.whiteCells,
    Configuration.blackCells, PeaceableQueens.blackCells, complementConfig]

theorem outerCount_complementConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (coord : OuterCoord) :
    outerCount (complementConfig cfg) coord = q - outerCount cfg coord := by
  cases coord with
  | mk family p =>
    cases family with
    | row => simpa [outerCount, rowCount, complementConfig] using card_parity_filter_compl q cfg.R p
    | column => simpa [outerCount, columnCount, complementConfig] using card_parity_filter_compl q cfg.C p
    | diagonal => simpa [outerCount, diagonalCount, complementConfig] using card_parity_filter_compl q cfg.D p
    | antidiagonal => simpa [outerCount, antidiagonalCount, complementConfig] using card_parity_filter_compl q cfg.A p

theorem normalizedProfile_complementConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (coord : OuterCoord) :
    normalizedProfile (complementConfig cfg) coord =
      ((q - outerCount cfg coord : ℕ) : ℚ) / (q : ℚ) := by
  rw [normalizedProfile_eq_div, outerCount_complementConfig]

/-- Total number of black-labelled lines across the four families. -/
def totalLineCount {q : ℕ} (cfg : Configuration q) : ℕ :=
  cfg.R.card + cfg.C.card + cfg.D.card + cfg.A.card

theorem totalLineCount_complementConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    totalLineCount (complementConfig cfg) = 8 * q - totalLineCount cfg := by
  have hcard (s : Finset (ZMod (2 * q))) : sᶜ.card = 2 * q - s.card := by
    rw [Finset.card_compl]
    simp [ZMod.card]
  have hle (s : Finset (ZMod (2 * q))) : s.card ≤ 2 * q := by
    calc
      s.card ≤ (Finset.univ : Finset (ZMod (2 * q))).card := Finset.card_le_univ s
      _ = 2 * q := by simp [ZMod.card]
  simp only [totalLineCount, complementConfig, hcard]
  have := hle cfg.R
  have := hle cfg.C
  have := hle cfg.D
  have := hle cfg.A
  omega

/-- Paper `lem:budget` (S23): a configuration or its colour complement obeys the `2n = 4q`
line-budget bound.  The preceding cell-set lemmas show that the complement
only exchanges the two objective armies. -/
theorem budget_or_complement {q : ℕ} [NeZero (2 * q)] (cfg : Configuration q) :
    totalLineCount cfg ≤ 4 * q ∨
      totalLineCount (complementConfig cfg) ≤ 4 * q := by
  by_cases h : totalLineCount cfg ≤ 4 * q
  · exact Or.inl h
  · right
    rw [totalLineCount_complementConfig]
    omega

end Complement

section Transpose

def transposeCell {n : ℕ} (p : Cell n) : Cell n := (p.2, p.1)

def negSet {n : ℕ} (s : Finset (ZMod n)) : Finset (ZMod n) :=
  s.image Neg.neg

def transposeConfig {q : ℕ} (cfg : Configuration q) : Configuration q :=
  ⟨cfg.C, cfg.R, negSet cfg.D, cfg.A⟩

private lemma negSet_compl {n : ℕ} [NeZero n]
    (s : Finset (ZMod n)) : negSet sᶜ = (negSet s)ᶜ := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_compl]
    intro hxs
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hxs
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    have hz' : z ∉ s := by simpa only [Finset.mem_compl] using hz
    have hyz : y = z := by
      calc
        y = -(-y) := by simp
        _ = -x := by rw [hxy]
        _ = -(-z) := by rw [hzx]
        _ = z := by simp
    exact hz' (hyz ▸ hy)
  · intro hx
    simp only [Finset.mem_compl] at hx
    apply Finset.mem_image.mpr
    refine ⟨-x, ?_, by simp⟩
    simp only [Finset.mem_compl]
    intro h
    apply hx
    exact Finset.mem_image.mpr ⟨-x, h, by simp⟩

private lemma complement_transposeConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    complementConfig (transposeConfig cfg) = transposeConfig (complementConfig cfg) := by
  cases cfg with
  | mk R C D A =>
    simp only [complementConfig, transposeConfig]
    congr 1
    exact (negSet_compl D).symm

private lemma neg_self_zmod_two (x : ZMod 2) : -x = x := by
  have hx : x.val < 2 := ZMod.val_lt x
  rcases (show x.val = 0 ∨ x.val = 1 by omega) with h | h
  · exact (ZMod.val_eq_zero x).mp h ▸ by simp
  · rw [← ZMod.natCast_zmod_val x, h]
    decide

private lemma parity_neg (q : ℕ) (x : ZMod (2 * q)) :
    parityMap q (-x) = parityMap q x := by
  rw [map_neg, neg_self_zmod_two]

private lemma negSet_filter
    {n : ℕ} [NeZero n] (s : Finset (ZMod n))
    (P : ZMod n → Prop) [DecidablePred P]
    (hP : ∀ x, P (-x) ↔ P x) :
    (negSet s).filter P = (s.filter P).image Neg.neg := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_filter] at hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx.1
    rw [Finset.mem_image]
    refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, hxy⟩
    apply (hP y).mp
    simpa [hxy] using hx.2
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨y, (Finset.mem_filter.mp hy).1, hxy⟩, ?_⟩
    have hneg : P (-y) := (hP y).mpr (Finset.mem_filter.mp hy).2
    simpa [hxy] using hneg

private lemma card_negSet_filter_eq
    {q : ℕ} [NeZero (2 * q)] (s : Finset (ZMod (2 * q))) (p : Parity) :
    ((negSet s).filter (fun x => parityMap q x = (p.val : ZMod 2))).card =
      (s.filter (fun x => parityMap q x = (p.val : ZMod 2))).card := by
  rw [negSet_filter s _ (fun x => by rw [parity_neg])]
  exact Finset.card_image_of_injective _ (by
    intro x y h
    exact neg_neg x ▸ neg_neg y ▸ congrArg Neg.neg h)

@[simp] theorem outerCount_transposeConfig_row {q : ℕ}
    (cfg : Configuration q) (p : Parity) :
    rowCount (transposeConfig cfg) p = columnCount cfg p := rfl

@[simp] theorem outerCount_transposeConfig_column {q : ℕ}
    (cfg : Configuration q) (p : Parity) :
    columnCount (transposeConfig cfg) p = rowCount cfg p := rfl

@[simp] theorem outerCount_transposeConfig_diagonal {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (p : Parity) :
    diagonalCount (transposeConfig cfg) p = diagonalCount cfg p := by
  exact card_negSet_filter_eq cfg.D p

@[simp] theorem outerCount_transposeConfig_antidiagonal {q : ℕ}
    (cfg : Configuration q) (p : Parity) :
    antidiagonalCount (transposeConfig cfg) p = antidiagonalCount cfg p := rfl

theorem outerCount_transposeConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (coord : OuterCoord) :
    outerCount (transposeConfig cfg) coord =
      outerCount cfg (match coord.family with
        | .row => ⟨.column, coord.parity⟩
        | .column => ⟨.row, coord.parity⟩
        | .diagonal => coord
        | .antidiagonal => coord) := by
  cases coord with
  | mk family p =>
    cases family <;> simp [outerCount]

theorem transposeCell_involutive {n : ℕ} (p : Cell n) :
    transposeCell (transposeCell p) = p := by
  rfl

theorem blackCells_transposeConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    (transposeConfig cfg).blackCells = cfg.blackCells.image transposeCell := by
  ext p
  constructor
  · intro hp
    rw [Configuration.blackCells, blackCells, Finset.mem_filter] at hp
    have hq : transposeCell p ∈ cfg.blackCells := by
      rw [Configuration.blackCells, blackCells, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hp.2 with ⟨hr, hc, hd, ha⟩
      refine ⟨hc, hr, ?_, ?_⟩
      · obtain ⟨d, hdD, hdEq⟩ := Finset.mem_image.mp hd
        change p.2 - p.1 ∈ cfg.D
        have heq : p.2 - p.1 = d := by
          calc
            p.2 - p.1 = -(p.1 - p.2) := by ring
            _ = -(-d) := by rw [hdEq]
            _ = d := neg_neg d
        rw [heq]
        exact hdD
      · change p.1 + p.2 ∈ cfg.A at ha
        simpa only [transposeCell, add_comm] using ha
    rw [Finset.mem_image]
    exact ⟨transposeCell p, hq, rfl⟩
  · intro hp
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp hp
    subst p
    rw [Configuration.blackCells, blackCells, Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx.2 with ⟨hr, hc, hd, ha⟩
    refine ⟨hc, hr, ?_, ?_⟩
    · change x.2 - x.1 ∈ (negSet cfg.D)
      exact Finset.mem_image.mpr ⟨x.1 - x.2, hd, by ring⟩
    · change x.2 + x.1 ∈ cfg.A
      change x.1 + x.2 ∈ cfg.A at ha
      simpa only [add_comm] using ha

@[simp] theorem whiteCells_transposeConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    (transposeConfig cfg).whiteCells = cfg.whiteCells.image transposeCell := by
  calc
    (transposeConfig cfg).whiteCells =
        (complementConfig (transposeConfig cfg)).blackCells := rfl
    _ = (transposeConfig (complementConfig cfg)).blackCells := by
      rw [complement_transposeConfig]
    _ = (complementConfig cfg).blackCells.image transposeCell :=
      blackCells_transposeConfig (complementConfig cfg)
    _ = cfg.whiteCells.image transposeCell := by rfl

end Transpose

section UnitTranslations

def paritySwap (p : Parity) : Parity :=
  ⟨(p.val + 1) % 2, Nat.mod_lt _ (by decide)⟩

def translateSet {n : ℕ} (s : Finset (ZMod n)) (k : ZMod n) : Finset (ZMod n) :=
  s.image (fun x => x + k)

private lemma translateSet_compl {n : ℕ} [NeZero n]
    (s : Finset (ZMod n)) (k : ZMod n) :
    translateSet sᶜ k = (translateSet s k)ᶜ := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_compl]
    intro hxs
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hxs
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    have hz' : z ∉ s := by simpa only [Finset.mem_compl] using hz
    have hyz : y = z := by
      calc
        y = (y + k) - k := by ring
        _ = x - k := by rw [hxy]
        _ = z := by rw [← hzx]; ring
    exact hz' (hyz ▸ hy)
  · intro hx
    simp only [Finset.mem_compl] at hx
    apply Finset.mem_image.mpr
    refine ⟨x - k, ?_, by ring⟩
    simp only [Finset.mem_compl]
    intro h
    apply hx
    exact Finset.mem_image.mpr ⟨x - k, h, by ring⟩

def translateRowCell {n : ℕ} (p : Cell n) : Cell n := (p.1 + 1, p.2)

def translateColumnCell {n : ℕ} (p : Cell n) : Cell n := (p.1, p.2 + 1)

def translateRowConfig {q : ℕ} (cfg : Configuration q) : Configuration q :=
  ⟨translateSet cfg.R 1, cfg.C, translateSet cfg.D 1, translateSet cfg.A 1⟩

def translateColumnConfig {q : ℕ} (cfg : Configuration q) : Configuration q :=
  ⟨cfg.R, translateSet cfg.C 1, translateSet cfg.D (-1), translateSet cfg.A 1⟩

private lemma complement_translateRowConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    complementConfig (translateRowConfig cfg) =
      translateRowConfig (complementConfig cfg) := by
  cases cfg with
  | mk R C D A =>
    simp only [complementConfig, translateRowConfig]
    congr 1
    · exact (translateSet_compl R 1).symm
    · exact (translateSet_compl D 1).symm
    · exact (translateSet_compl A 1).symm

private lemma complement_translateColumnConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    complementConfig (translateColumnConfig cfg) =
      translateColumnConfig (complementConfig cfg) := by
  cases cfg with
  | mk R C D A =>
    simp only [complementConfig, translateColumnConfig]
    congr 1
    · exact (translateSet_compl C 1).symm
    · exact (translateSet_compl D (-1)).symm
    · exact (translateSet_compl A 1).symm

private lemma paritySwap_cast (p : Parity) :
    (paritySwap p).val = (p.val + 1) % 2 := rfl

private lemma parityMap_one (q : ℕ) [NeZero (2 * q)] :
    parityMap q (1 : ZMod (2 * q)) = (1 : ZMod 2) := by
  simp [parityMap]

private lemma parityTranslate_iff (q : ℕ) [NeZero (2 * q)]
    (k : ZMod (2 * q)) (hk : parityMap q k = (1 : ZMod 2))
    (x : ZMod (2 * q)) (p : Parity) :
    parityMap q (x + k) = (p.val : ZMod 2) ↔
      parityMap q x = (paritySwap p).val := by
  rw [map_add, hk]
  have hflip : ((paritySwap p).val : ZMod 2) =
      (p.val : ZMod 2) + 1 := by
    fin_cases p <;> decide
  rw [hflip]
  have htwo : (1 : ZMod 2) + 1 = 0 := by
    rw [← Nat.cast_one (R := ZMod 2), ← Nat.cast_add, ZMod.natCast_self]
  constructor
  · intro h
    calc
      parityMap q x = parityMap q x + 0 := by simp
      _ = parityMap q x + (1 + 1) := by rw [htwo]
      _ = (parityMap q x + 1) + 1 := by ring
      _ = (p.val : ZMod 2) + 1 := by rw [h]
  · intro h
    calc
      parityMap q x + 1 = ((p.val : ZMod 2) + 1) + 1 := by rw [h]
      _ = (p.val : ZMod 2) + (1 + 1) := by ring
      _ = (p.val : ZMod 2) := by rw [htwo]; simp

private lemma translateSet_filter
    {q : ℕ} [NeZero (2 * q)] (s : Finset (ZMod (2 * q)))
    (k : ZMod (2 * q)) (hk : parityMap q k = (1 : ZMod 2)) (p : Parity) :
    (translateSet s k).filter (fun x => parityMap q x = (p.val : ZMod 2)) =
      (s.filter (fun x => parityMap q x = (paritySwap p).val)).image
        (fun x => x + k) := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_filter] at hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx.1
    rw [Finset.mem_image]
    refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, hxy⟩
    exact (parityTranslate_iff q k hk y p).mp (by simpa [hxy] using hx.2)
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨y, (Finset.mem_filter.mp hy).1, hxy⟩, ?_⟩
    simpa [hxy] using
      (parityTranslate_iff q k hk y p).mpr (Finset.mem_filter.mp hy).2

private lemma card_translateSet_filter
    {q : ℕ} [NeZero (2 * q)] (s : Finset (ZMod (2 * q)))
    (k : ZMod (2 * q)) (hk : parityMap q k = (1 : ZMod 2)) (p : Parity) :
    ((translateSet s k).filter
      (fun x => parityMap q x = (p.val : ZMod 2))).card =
      (s.filter
        (fun x => parityMap q x = (paritySwap p).val)).card := by
  rw [translateSet_filter s k hk p]
  exact Finset.card_image_of_injective _ (by
    intro x y h
    exact add_right_cancel h)

private lemma parityMap_neg_one (q : ℕ) [NeZero (2 * q)] :
    parityMap q (-1 : ZMod (2 * q)) = (1 : ZMod 2) := by
  rw [map_neg, parityMap_one]
  decide

@[simp] theorem rowCount_translateRowConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (p : Parity) :
    rowCount (translateRowConfig cfg) p = rowCount cfg (paritySwap p) := by
  exact card_translateSet_filter cfg.R 1 (parityMap_one q) p

@[simp] theorem columnCount_translateRowConfig {q : ℕ}
    (cfg : Configuration q) (p : Parity) :
    columnCount (translateRowConfig cfg) p = columnCount cfg p := rfl

@[simp] theorem diagonalCount_translateRowConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (p : Parity) :
    diagonalCount (translateRowConfig cfg) p = diagonalCount cfg (paritySwap p) := by
  exact card_translateSet_filter cfg.D 1 (parityMap_one q) p

@[simp] theorem antidiagonalCount_translateRowConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (p : Parity) :
    antidiagonalCount (translateRowConfig cfg) p = antidiagonalCount cfg (paritySwap p) := by
  exact card_translateSet_filter cfg.A 1 (parityMap_one q) p

@[simp] theorem rowCount_translateColumnConfig {q : ℕ}
    (cfg : Configuration q) (p : Parity) :
    rowCount (translateColumnConfig cfg) p = rowCount cfg p := rfl

@[simp] theorem columnCount_translateColumnConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (p : Parity) :
    columnCount (translateColumnConfig cfg) p = columnCount cfg (paritySwap p) := by
  exact card_translateSet_filter cfg.C 1 (parityMap_one q) p

@[simp] theorem diagonalCount_translateColumnConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (p : Parity) :
    diagonalCount (translateColumnConfig cfg) p = diagonalCount cfg (paritySwap p) := by
  exact card_translateSet_filter cfg.D (-1) (parityMap_neg_one q) p

@[simp] theorem antidiagonalCount_translateColumnConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (p : Parity) :
    antidiagonalCount (translateColumnConfig cfg) p = antidiagonalCount cfg (paritySwap p) := by
  exact card_translateSet_filter cfg.A 1 (parityMap_one q) p

theorem outerCount_translateRowConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (coord : OuterCoord) :
    outerCount (translateRowConfig cfg) coord =
      outerCount cfg (match coord.family with
        | .row => ⟨.row, paritySwap coord.parity⟩
        | .column => coord
        | .diagonal => ⟨.diagonal, paritySwap coord.parity⟩
        | .antidiagonal => ⟨.antidiagonal, paritySwap coord.parity⟩) := by
  cases coord with
  | mk family p =>
    cases family <;> simp [outerCount]

theorem outerCount_translateColumnConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (coord : OuterCoord) :
    outerCount (translateColumnConfig cfg) coord =
      outerCount cfg (match coord.family with
        | .row => coord
        | .column => ⟨.column, paritySwap coord.parity⟩
        | .diagonal => ⟨.diagonal, paritySwap coord.parity⟩
        | .antidiagonal => ⟨.antidiagonal, paritySwap coord.parity⟩) := by
  cases coord with
  | mk family p =>
    cases family <;> simp [outerCount]

theorem blackCells_translateRowConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    (translateRowConfig cfg).blackCells = cfg.blackCells.image translateRowCell := by
  ext p
  constructor
  · intro hp
    rw [Configuration.blackCells, blackCells, Finset.mem_filter] at hp
    have hq : (p.1 - 1, p.2) ∈ cfg.blackCells := by
      rw [Configuration.blackCells, blackCells, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hp.2 with ⟨hr, hc, hd, ha⟩
      obtain ⟨r, hrR, hrEq⟩ := Finset.mem_image.mp hr
      obtain ⟨d, hdD, hdEq⟩ := Finset.mem_image.mp hd
      obtain ⟨a, haA, haEq⟩ := Finset.mem_image.mp ha
      refine ⟨?_, hc, ?_, ?_⟩
      · change p.1 - 1 ∈ cfg.R
        have heq : p.1 - 1 = r := by rw [← hrEq]; ring
        rw [heq]
        exact hrR
      · change (p.1 - 1) - p.2 ∈ cfg.D
        have heq : (p.1 - 1) - p.2 = d := by
          calc
            (p.1 - 1) - p.2 = (p.1 - p.2) - 1 := by ring
            _ = d + 1 - 1 := by rw [← hdEq]
            _ = d := by ring
        rw [heq]
        exact hdD
      · change (p.1 - 1) + p.2 ∈ cfg.A
        have heq : (p.1 - 1) + p.2 = a := by
          calc
            (p.1 - 1) + p.2 = (p.1 + p.2) - 1 := by ring
            _ = a + 1 - 1 := by rw [← haEq]
            _ = a := by ring
        rw [heq]
        exact haA
    rw [Finset.mem_image]
    exact ⟨(p.1 - 1, p.2), hq, by ext <;> simp [translateRowCell]⟩
  · intro hp
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp hp
    subst p
    rw [Configuration.blackCells, blackCells, Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx.2 with ⟨hr, hc, hd, ha⟩
    refine ⟨?_, hc, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x.1, hr, by simp [translateRowCell]⟩
    · exact Finset.mem_image.mpr ⟨x.1 - x.2, hd, by simp [translateRowCell]; ring⟩
    · exact Finset.mem_image.mpr ⟨x.1 + x.2, ha, by simp [translateRowCell]; ring⟩

theorem blackCells_translateColumnConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    (translateColumnConfig cfg).blackCells = cfg.blackCells.image translateColumnCell := by
  ext p
  constructor
  · intro hp
    rw [Configuration.blackCells, blackCells, Finset.mem_filter] at hp
    have hq : (p.1, p.2 - 1) ∈ cfg.blackCells := by
      rw [Configuration.blackCells, blackCells, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hp.2 with ⟨hr, hc, hd, ha⟩
      obtain ⟨c, hcC, hcEq⟩ := Finset.mem_image.mp hc
      obtain ⟨d, hdD, hdEq⟩ := Finset.mem_image.mp hd
      obtain ⟨a, haA, haEq⟩ := Finset.mem_image.mp ha
      refine ⟨hr, ?_, ?_, ?_⟩
      · change p.2 - 1 ∈ cfg.C
        have heq : p.2 - 1 = c := by rw [← hcEq]; ring
        rw [heq]
        exact hcC
      · change p.1 - (p.2 - 1) ∈ cfg.D
        have heq : p.1 - (p.2 - 1) = d := by
          calc
            p.1 - (p.2 - 1) = (p.1 - p.2) + 1 := by ring
            _ = d + -1 + 1 := by rw [← hdEq]
            _ = d := by ring
        rw [heq]
        exact hdD
      · change p.1 + (p.2 - 1) ∈ cfg.A
        have heq : p.1 + (p.2 - 1) = a := by
          calc
            p.1 + (p.2 - 1) = (p.1 + p.2) - 1 := by ring
            _ = a + 1 - 1 := by rw [← haEq]
            _ = a := by ring
        rw [heq]
        exact haA
    rw [Finset.mem_image]
    exact ⟨(p.1, p.2 - 1), hq, by ext <;> simp [translateColumnCell]⟩
  · intro hp
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp hp
    subst p
    rw [Configuration.blackCells, blackCells, Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx.2 with ⟨hr, hc, hd, ha⟩
    refine ⟨hr, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x.2, hc, by simp [translateColumnCell]⟩
    · exact Finset.mem_image.mpr ⟨x.1 - x.2, hd, by simp [translateColumnCell]; ring⟩
    · exact Finset.mem_image.mpr ⟨x.1 + x.2, ha, by simp [translateColumnCell]; ring⟩

@[simp] theorem whiteCells_translateRowConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    (translateRowConfig cfg).whiteCells = cfg.whiteCells.image translateRowCell := by
  calc
    (translateRowConfig cfg).whiteCells =
        (complementConfig (translateRowConfig cfg)).blackCells := rfl
    _ = (translateRowConfig (complementConfig cfg)).blackCells := by
      rw [complement_translateRowConfig]
    _ = (complementConfig cfg).blackCells.image translateRowCell :=
      blackCells_translateRowConfig (complementConfig cfg)
    _ = cfg.whiteCells.image translateRowCell := by rfl

@[simp] theorem whiteCells_translateColumnConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    (translateColumnConfig cfg).whiteCells = cfg.whiteCells.image translateColumnCell := by
  calc
    (translateColumnConfig cfg).whiteCells =
        (complementConfig (translateColumnConfig cfg)).blackCells := rfl
    _ = (translateColumnConfig (complementConfig cfg)).blackCells := by
      rw [complement_translateColumnConfig]
    _ = (complementConfig cfg).blackCells.image translateColumnCell :=
      blackCells_translateColumnConfig (complementConfig cfg)
    _ = cfg.whiteCells.image translateColumnCell := by rfl

end UnitTranslations

section Reflection

def reflectCell {n : ℕ} (p : Cell n) : Cell n := (p.1, -p.2)

def reflectConfig {q : ℕ} (cfg : Configuration q) : Configuration q :=
  ⟨cfg.R, negSet cfg.C, cfg.A, cfg.D⟩

private lemma complement_reflectConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    complementConfig (reflectConfig cfg) = reflectConfig (complementConfig cfg) := by
  cases cfg with
  | mk R C D A =>
    simp only [complementConfig, reflectConfig]
    congr 1
    exact (negSet_compl C).symm

@[simp] theorem rowCount_reflectConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (p : Parity) :
    rowCount (reflectConfig cfg) p = rowCount cfg p := rfl

@[simp] theorem columnCount_reflectConfig {q : ℕ} [NeZero (2 * q)]
  (cfg : Configuration q) (p : Parity) :
  columnCount (reflectConfig cfg) p = columnCount cfg p := by
  exact card_negSet_filter_eq cfg.C p

@[simp] theorem diagonalCount_reflectConfig {q : ℕ}
    (cfg : Configuration q) (p : Parity) :
    diagonalCount (reflectConfig cfg) p = antidiagonalCount cfg p := rfl

@[simp] theorem antidiagonalCount_reflectConfig {q : ℕ}
    (cfg : Configuration q) (p : Parity) :
    antidiagonalCount (reflectConfig cfg) p = diagonalCount cfg p := rfl

theorem outerCount_reflectConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) (coord : OuterCoord) :
    outerCount (reflectConfig cfg) coord =
      outerCount cfg (match coord.family with
        | .row => coord
        | .column => coord
        | .diagonal => ⟨.antidiagonal, coord.parity⟩
        | .antidiagonal => ⟨.diagonal, coord.parity⟩) := by
  cases coord with
  | mk family p =>
    cases family <;> simp [outerCount]

theorem blackCells_reflectConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    (reflectConfig cfg).blackCells = cfg.blackCells.image reflectCell := by
  ext p
  constructor
  · intro hp
    rw [Configuration.blackCells, blackCells, Finset.mem_filter] at hp
    have hq : (p.1, -p.2) ∈ cfg.blackCells := by
      rw [Configuration.blackCells, blackCells, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hp.2 with ⟨hr, hc, hd, ha⟩
      obtain ⟨c, hcC, hcEq⟩ := Finset.mem_image.mp hc
      refine ⟨hr, ?_, ?_, ?_⟩
      · change -p.2 ∈ cfg.C
        have heq : -p.2 = c := by rw [← hcEq]; simp
        rw [heq]
        exact hcC
      · change p.1 - -p.2 ∈ cfg.D
        change p.1 + p.2 ∈ cfg.D at ha
        simpa only [sub_neg_eq_add] using ha
      · change p.1 + -p.2 ∈ cfg.A
        change p.1 - p.2 ∈ cfg.A at hd
        simpa only [sub_eq_add_neg] using hd
    rw [Finset.mem_image]
    exact ⟨(p.1, -p.2), hq, by simp [reflectCell]⟩
  · intro hp
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp hp
    subst p
    rw [Configuration.blackCells, blackCells, Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx.2 with ⟨hr, hc, hd, ha⟩
    refine ⟨hr, ?_, ?_, ?_⟩
    · change -x.2 ∈ negSet cfg.C
      exact Finset.mem_image.mpr ⟨x.2, hc, rfl⟩
    · change x.1 - -x.2 ∈ cfg.A
      change x.1 + x.2 ∈ cfg.A at ha
      simpa only [sub_neg_eq_add] using ha
    · change x.1 + -x.2 ∈ cfg.D
      change x.1 - x.2 ∈ cfg.D at hd
      simpa only [sub_eq_add_neg] using hd

@[simp] theorem whiteCells_reflectConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    (reflectConfig cfg).whiteCells = cfg.whiteCells.image reflectCell := by
  calc
    (reflectConfig cfg).whiteCells =
        (complementConfig (reflectConfig cfg)).blackCells := rfl
    _ = (reflectConfig (complementConfig cfg)).blackCells := by
      rw [complement_reflectConfig]
    _ = (complementConfig cfg).blackCells.image reflectCell :=
      blackCells_reflectConfig (complementConfig cfg)
    _ = cfg.whiteCells.image reflectCell := by rfl

end Reflection

section S29

/-- The canonical chamber inequalities from S29. -/
def chamber (q : ℕ) (cfg : Configuration q) : Prop :=
  outerCount cfg ⟨.row, 0⟩ ≤ outerCount cfg ⟨.row, 1⟩ ∧
  outerCount cfg ⟨.column, 0⟩ ≤ outerCount cfg ⟨.column, 1⟩ ∧
  (outerCount cfg ⟨.row, 0⟩ + outerCount cfg ⟨.row, 1⟩) ≤
    (outerCount cfg ⟨.column, 0⟩ + outerCount cfg ⟨.column, 1⟩) ∧
  (outerCount cfg ⟨.diagonal, 0⟩ + outerCount cfg ⟨.diagonal, 1⟩) ≤
    (outerCount cfg ⟨.antidiagonal, 0⟩ + outerCount cfg ⟨.antidiagonal, 1⟩) ∧
  totalLineCount cfg ≤ 4 * q

/-- Equality of black/white cardinalities, allowing the two colours to swap. -/
def objectiveEquivalent {q : ℕ} [NeZero (2 * q)]
    (cfg cfg' : Configuration q) : Prop :=
  ((cfg'.blackCells.card = cfg.blackCells.card ∧
      cfg'.whiteCells.card = cfg.whiteCells.card) ∨
    (cfg'.blackCells.card = cfg.whiteCells.card ∧
      cfg'.whiteCells.card = cfg.blackCells.card))

private lemma objectiveEquivalent_trans {q : ℕ} [NeZero (2 * q)]
    {a b c : Configuration q} (hab : objectiveEquivalent a b)
    (hbc : objectiveEquivalent b c) : objectiveEquivalent a c := by
  rcases hab with ⟨hbb, hww⟩ | ⟨hbb, hww⟩ <;>
    rcases hbc with ⟨hbb', hww'⟩ | ⟨hbb', hww'⟩
  · left; constructor <;> omega
  · right; constructor <;> omega
  · right; constructor <;> omega
  · left; constructor <;> omega

private lemma card_translateSet {n : ℕ} [NeZero n]
    (s : Finset (ZMod n)) (k : ZMod n) :
    (translateSet s k).card = s.card := by
  exact Finset.card_image_of_injective _ (by
    intro x y h
    exact add_right_cancel h)

private lemma card_negSet {n : ℕ} [NeZero n] (s : Finset (ZMod n)) :
    (negSet s).card = s.card := by
  exact Finset.card_image_of_injective _ (by
    intro x y h
    exact neg_neg x ▸ neg_neg y ▸ congrArg Neg.neg h)

private lemma totalLineCount_translateRowConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    totalLineCount (translateRowConfig cfg) = totalLineCount cfg := by
  simp only [totalLineCount, translateRowConfig, card_translateSet]

private lemma totalLineCount_translateColumnConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    totalLineCount (translateColumnConfig cfg) = totalLineCount cfg := by
  simp only [totalLineCount, translateColumnConfig, card_translateSet]

private lemma totalLineCount_transposeConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    totalLineCount (transposeConfig cfg) = totalLineCount cfg := by
  simp only [totalLineCount, transposeConfig, card_negSet]
  omega

private lemma totalLineCount_reflectConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    totalLineCount (reflectConfig cfg) = totalLineCount cfg := by
  simp only [totalLineCount, reflectConfig, card_negSet]
  omega

private lemma objectiveEquivalent_complementConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) : objectiveEquivalent cfg (complementConfig cfg) := by
  right
  simp

/-- Board equivalences transport both armies with one cardinality argument. -/
theorem objectiveEquivalent_of_images {q : ℕ} [NeZero (2 * q)]
    (cfg cfg' : Configuration q) (e : BoardEquiv (2 * q))
    (hB : cfg'.blackCells = cfg.blackCells.image e.toEquiv)
    (hW : cfg'.whiteCells = cfg.whiteCells.image e.toEquiv) :
    objectiveEquivalent cfg cfg' := by
  left
  constructor
  · rw [hB]
    exact e.card_image _
  · rw [hW]
    exact e.card_image _

/-- The translateRow symmetry as an explicit attack-preserving equivalence. -/
def translateRowEquiv (n : ℕ) : BoardEquiv n where
  toFun := translateRowCell
  invFun p := (p.1 - 1, p.2)
  left_inv p := by ext <;> simp [translateRowCell]
  right_inv p := by ext <;> simp [translateRowCell]
  sharesLine_iff p q := by
    change SharesLine (translateRowCell p) (translateRowCell q) ↔ SharesLine p q
    simp only [SharesLine, translateRowCell]
    constructor <;> rintro (h | h | h | h)
    all_goals first
      | exact Or.inl (by first | linear_combination h | linear_combination -h)
      | exact Or.inr (Or.inl (by first | linear_combination h | linear_combination -h))
      | exact Or.inr (Or.inr (Or.inl (by first | linear_combination h | linear_combination -h)))
      | exact Or.inr (Or.inr (Or.inr (by first | linear_combination h | linear_combination -h)))

private lemma objectiveEquivalent_translateRowConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) : objectiveEquivalent cfg (translateRowConfig cfg) :=
  objectiveEquivalent_of_images cfg (translateRowConfig cfg) (translateRowEquiv (2 * q))
    (blackCells_translateRowConfig cfg) (whiteCells_translateRowConfig cfg)

/-- The translateColumn symmetry as an explicit attack-preserving equivalence. -/
def translateColumnEquiv (n : ℕ) : BoardEquiv n where
  toFun := translateColumnCell
  invFun p := (p.1, p.2 - 1)
  left_inv p := by ext <;> simp [translateColumnCell]
  right_inv p := by ext <;> simp [translateColumnCell]
  sharesLine_iff p q := by
    change SharesLine (translateColumnCell p) (translateColumnCell q) ↔ SharesLine p q
    simp only [SharesLine, translateColumnCell]
    constructor <;> rintro (h | h | h | h)
    all_goals first
      | exact Or.inl (by first | linear_combination h | linear_combination -h)
      | exact Or.inr (Or.inl (by first | linear_combination h | linear_combination -h))
      | exact Or.inr (Or.inr (Or.inl (by first | linear_combination h | linear_combination -h)))
      | exact Or.inr (Or.inr (Or.inr (by first | linear_combination h | linear_combination -h)))

private lemma objectiveEquivalent_translateColumnConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) : objectiveEquivalent cfg (translateColumnConfig cfg) :=
  objectiveEquivalent_of_images cfg (translateColumnConfig cfg) (translateColumnEquiv (2 * q))
    (blackCells_translateColumnConfig cfg) (whiteCells_translateColumnConfig cfg)

/-- The transpose symmetry as an explicit attack-preserving equivalence. -/
def transposeEquiv (n : ℕ) : BoardEquiv n where
  toFun := transposeCell
  invFun p := (p.2, p.1)
  left_inv p := by ext <;> simp [transposeCell]
  right_inv p := by ext <;> simp [transposeCell]
  sharesLine_iff p q := by
    change SharesLine (transposeCell p) (transposeCell q) ↔ SharesLine p q
    simp only [SharesLine, transposeCell]
    constructor <;> rintro (h | h | h | h)
    all_goals first
      | exact Or.inl (by first | linear_combination h | linear_combination -h)
      | exact Or.inr (Or.inl (by first | linear_combination h | linear_combination -h))
      | exact Or.inr (Or.inr (Or.inl (by first | linear_combination h | linear_combination -h)))
      | exact Or.inr (Or.inr (Or.inr (by first | linear_combination h | linear_combination -h)))

private lemma objectiveEquivalent_transposeConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) : objectiveEquivalent cfg (transposeConfig cfg) :=
  objectiveEquivalent_of_images cfg (transposeConfig cfg) (transposeEquiv (2 * q))
    (blackCells_transposeConfig cfg) (whiteCells_transposeConfig cfg)

/-- The reflect symmetry as an explicit attack-preserving equivalence. -/
def reflectEquiv (n : ℕ) : BoardEquiv n where
  toFun := reflectCell
  invFun p := (p.1, -p.2)
  left_inv p := by ext <;> simp [reflectCell]
  right_inv p := by ext <;> simp [reflectCell]
  sharesLine_iff p q := by
    change SharesLine (reflectCell p) (reflectCell q) ↔ SharesLine p q
    simp only [SharesLine, reflectCell]
    constructor <;> rintro (h | h | h | h)
    all_goals first
      | exact Or.inl (by first | linear_combination h | linear_combination -h)
      | exact Or.inr (Or.inl (by first | linear_combination h | linear_combination -h))
      | exact Or.inr (Or.inr (Or.inl (by first | linear_combination h | linear_combination -h)))
      | exact Or.inr (Or.inr (Or.inr (by first | linear_combination h | linear_combination -h)))

private lemma objectiveEquivalent_reflectConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) : objectiveEquivalent cfg (reflectConfig cfg) :=
  objectiveEquivalent_of_images cfg (reflectConfig cfg) (reflectEquiv (2 * q))
    (blackCells_reflectConfig cfg) (whiteCells_reflectConfig cfg)

private lemma paritySwap_zero : paritySwap (0 : Parity) = 1 := by decide
private lemma paritySwap_one : paritySwap (1 : Parity) = 0 := by decide

private lemma row_total_transposeConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    outerCount (transposeConfig cfg) ⟨.row, 0⟩ +
      outerCount (transposeConfig cfg) ⟨.row, 1⟩ =
    outerCount cfg ⟨.column, 0⟩ + outerCount cfg ⟨.column, 1⟩ := by
  simp [outerCount_transposeConfig]

private lemma column_total_transposeConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    outerCount (transposeConfig cfg) ⟨.column, 0⟩ +
      outerCount (transposeConfig cfg) ⟨.column, 1⟩ =
    outerCount cfg ⟨.row, 0⟩ + outerCount cfg ⟨.row, 1⟩ := by
  simp [outerCount_transposeConfig]

private lemma diagonal_total_reflectConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    outerCount (reflectConfig cfg) ⟨.diagonal, 0⟩ +
      outerCount (reflectConfig cfg) ⟨.diagonal, 1⟩ =
    outerCount cfg ⟨.antidiagonal, 0⟩ + outerCount cfg ⟨.antidiagonal, 1⟩ := by
  simp [outerCount_reflectConfig]

private lemma antidiagonal_total_reflectConfig {q : ℕ} [NeZero (2 * q)]
    (cfg : Configuration q) :
    outerCount (reflectConfig cfg) ⟨.antidiagonal, 0⟩ +
      outerCount (reflectConfig cfg) ⟨.antidiagonal, 1⟩ =
    outerCount cfg ⟨.diagonal, 0⟩ + outerCount cfg ⟨.diagonal, 1⟩ := by
  simp [outerCount_reflectConfig]

/-- Paper `lem:chamber` (S29): every configuration is objective-equivalent to
one satisfying the five canonical chamber inequalities, via complementation,
unit row/column translations, transpose and the reflection `(r,c) ↦ (r,-c)`. -/
theorem exists_chamber {q : ℕ} [NeZero (2 * q)] (cfg : Configuration q) :
    ∃ cfg' : Configuration q, chamber q cfg' ∧
      objectiveEquivalent cfg cfg' := by
  let cfg₀ : Configuration q := if h : totalLineCount cfg ≤ 4 * q then cfg
    else complementConfig cfg
  have h₀budget : totalLineCount cfg₀ ≤ 4 * q := by
    dsimp [cfg₀]
    split
    · assumption
    · exact (budget_or_complement cfg).resolve_left (by assumption)
  have h₀obj : objectiveEquivalent cfg cfg₀ := by
    dsimp [cfg₀]
    split
    · exact Or.inl ⟨rfl, rfl⟩
    · exact objectiveEquivalent_complementConfig cfg
  let cfg₁ : Configuration q := if h : outerCount cfg₀ ⟨.row, 0⟩ ≤
      outerCount cfg₀ ⟨.row, 1⟩ then cfg₀ else translateRowConfig cfg₀
  have h₁row : outerCount cfg₁ ⟨.row, 0⟩ ≤ outerCount cfg₁ ⟨.row, 1⟩ := by
    dsimp [cfg₁]
    by_cases h : outerCount cfg₀ ⟨.row, 0⟩ ≤ outerCount cfg₀ ⟨.row, 1⟩
    · simpa only [if_pos h] using h
    · simp only [if_neg h]
      change rowCount (translateRowConfig cfg₀) 0 ≤
        rowCount (translateRowConfig cfg₀) 1
      rw [rowCount_translateRowConfig, rowCount_translateRowConfig,
        paritySwap_zero, paritySwap_one]
      have h' : ¬ rowCount cfg₀ 0 ≤ rowCount cfg₀ 1 := by
        simpa [outerCount] using h
      omega
  have h₁budget : totalLineCount cfg₁ ≤ 4 * q := by
    dsimp [cfg₁]
    split
    · exact h₀budget
    · simpa [totalLineCount_translateRowConfig]
  have h₁obj : objectiveEquivalent cfg cfg₁ := by
    dsimp [cfg₁]
    split
    · exact h₀obj
    · exact objectiveEquivalent_trans h₀obj (objectiveEquivalent_translateRowConfig cfg₀)
  let cfg₂ : Configuration q := if h : outerCount cfg₁ ⟨.column, 0⟩ ≤
      outerCount cfg₁ ⟨.column, 1⟩ then cfg₁ else translateColumnConfig cfg₁
  have h₂row : outerCount cfg₂ ⟨.row, 0⟩ ≤ outerCount cfg₂ ⟨.row, 1⟩ := by
    dsimp [cfg₂]
    by_cases h : outerCount cfg₁ ⟨.column, 0⟩ ≤ outerCount cfg₁ ⟨.column, 1⟩
    · simpa [h] using h₁row
    · simp only [if_neg h]
      change rowCount (translateColumnConfig cfg₁) 0 ≤
        rowCount (translateColumnConfig cfg₁) 1
      simpa [outerCount] using h₁row
  have h₂col : outerCount cfg₂ ⟨.column, 0⟩ ≤ outerCount cfg₂ ⟨.column, 1⟩ := by
    dsimp [cfg₂]
    by_cases h : outerCount cfg₁ ⟨.column, 0⟩ ≤ outerCount cfg₁ ⟨.column, 1⟩
    · simpa only [if_pos h] using h
    · simp only [if_neg h]
      change columnCount (translateColumnConfig cfg₁) 0 ≤
        columnCount (translateColumnConfig cfg₁) 1
      rw [columnCount_translateColumnConfig, columnCount_translateColumnConfig,
        paritySwap_zero, paritySwap_one]
      have h' : ¬ columnCount cfg₁ 0 ≤ columnCount cfg₁ 1 := by
        simpa [outerCount] using h
      omega
  have h₂budget : totalLineCount cfg₂ ≤ 4 * q := by
    dsimp [cfg₂]
    split
    · exact h₁budget
    · simpa [totalLineCount_translateColumnConfig]
  have h₂obj : objectiveEquivalent cfg cfg₂ := by
    dsimp [cfg₂]
    split
    · exact h₁obj
    · exact objectiveEquivalent_trans h₁obj (objectiveEquivalent_translateColumnConfig cfg₁)
  let cfg₃ : Configuration q := if h : outerCount cfg₂ ⟨.row, 0⟩ +
      outerCount cfg₂ ⟨.row, 1⟩ ≤ outerCount cfg₂ ⟨.column, 0⟩ +
      outerCount cfg₂ ⟨.column, 1⟩ then cfg₂ else transposeConfig cfg₂
  have h₃row : outerCount cfg₃ ⟨.row, 0⟩ ≤ outerCount cfg₃ ⟨.row, 1⟩ := by
    dsimp [cfg₃]
    split
    · exact h₂row
    · change outerCount cfg₂ ⟨.column, 0⟩ ≤
        outerCount (transposeConfig cfg₂) ⟨.row, 1⟩
      rw [outerCount_transposeConfig]
      exact h₂col
  have h₃col : outerCount cfg₃ ⟨.column, 0⟩ ≤ outerCount cfg₃ ⟨.column, 1⟩ := by
    dsimp [cfg₃]
    split
    · exact h₂col
    · change outerCount cfg₂ ⟨.row, 0⟩ ≤
        outerCount (transposeConfig cfg₂) ⟨.column, 1⟩
      rw [outerCount_transposeConfig]
      exact h₂row
  have h₃rc : outerCount cfg₃ ⟨.row, 0⟩ + outerCount cfg₃ ⟨.row, 1⟩ ≤
      outerCount cfg₃ ⟨.column, 0⟩ + outerCount cfg₃ ⟨.column, 1⟩ := by
    dsimp [cfg₃]
    split
    · assumption
    · rw [row_total_transposeConfig, column_total_transposeConfig]
      omega
  have h₃budget : totalLineCount cfg₃ ≤ 4 * q := by
    dsimp [cfg₃]
    split
    · exact h₂budget
    · simpa [totalLineCount_transposeConfig]
  have h₃obj : objectiveEquivalent cfg cfg₃ := by
    dsimp [cfg₃]
    split
    · exact h₂obj
    · exact objectiveEquivalent_trans h₂obj (objectiveEquivalent_transposeConfig cfg₂)
  let cfg₄ : Configuration q := if h : outerCount cfg₃ ⟨.diagonal, 0⟩ +
      outerCount cfg₃ ⟨.diagonal, 1⟩ ≤ outerCount cfg₃ ⟨.antidiagonal, 0⟩ +
      outerCount cfg₃ ⟨.antidiagonal, 1⟩ then cfg₃ else reflectConfig cfg₃
  have h₄row : outerCount cfg₄ ⟨.row, 0⟩ ≤ outerCount cfg₄ ⟨.row, 1⟩ := by
    dsimp [cfg₄]
    split
    · exact h₃row
    · rw [outerCount_reflectConfig, outerCount_reflectConfig]
      exact h₃row
  have h₄col : outerCount cfg₄ ⟨.column, 0⟩ ≤ outerCount cfg₄ ⟨.column, 1⟩ := by
    dsimp [cfg₄]
    split
    · exact h₃col
    · rw [outerCount_reflectConfig, outerCount_reflectConfig]
      exact h₃col
  have h₄rc : outerCount cfg₄ ⟨.row, 0⟩ + outerCount cfg₄ ⟨.row, 1⟩ ≤
      outerCount cfg₄ ⟨.column, 0⟩ + outerCount cfg₄ ⟨.column, 1⟩ := by
    dsimp [cfg₄]
    split
    · exact h₃rc
    · rw [outerCount_reflectConfig, outerCount_reflectConfig,
        outerCount_reflectConfig, outerCount_reflectConfig]
      exact h₃rc
  have h₄da : outerCount cfg₄ ⟨.diagonal, 0⟩ + outerCount cfg₄ ⟨.diagonal, 1⟩ ≤
      outerCount cfg₄ ⟨.antidiagonal, 0⟩ + outerCount cfg₄ ⟨.antidiagonal, 1⟩ := by
    dsimp [cfg₄]
    split
    · assumption
    · rw [diagonal_total_reflectConfig, antidiagonal_total_reflectConfig]
      omega
  have h₄budget : totalLineCount cfg₄ ≤ 4 * q := by
    dsimp [cfg₄]
    split
    · exact h₃budget
    · rw [totalLineCount_reflectConfig]
      exact h₃budget
  have h₄obj : objectiveEquivalent cfg cfg₄ := by
    dsimp [cfg₄]
    split
    · exact h₃obj
    · exact objectiveEquivalent_trans h₃obj (objectiveEquivalent_reflectConfig cfg₃)
  exact ⟨cfg₄, ⟨h₄row, h₄col, h₄rc, h₄da, h₄budget⟩, h₄obj⟩

end S29

#print axioms outerCount_complementConfig
#print axioms blackCells_complementConfig
#print axioms whiteCells_complementConfig
#print axioms normalizedProfile_complementConfig
#print axioms budget_or_complement
#print axioms blackCells_transposeConfig
#print axioms whiteCells_transposeConfig
#print axioms outerCount_transposeConfig
#print axioms rowCount_translateRowConfig
#print axioms columnCount_translateRowConfig
#print axioms diagonalCount_translateRowConfig
#print axioms antidiagonalCount_translateRowConfig
#print axioms rowCount_translateColumnConfig
#print axioms columnCount_translateColumnConfig
#print axioms diagonalCount_translateColumnConfig
#print axioms antidiagonalCount_translateColumnConfig
#print axioms outerCount_translateRowConfig
#print axioms outerCount_translateColumnConfig
#print axioms blackCells_translateRowConfig
#print axioms whiteCells_translateRowConfig
#print axioms blackCells_translateColumnConfig
#print axioms whiteCells_translateColumnConfig
#print axioms rowCount_reflectConfig
#print axioms columnCount_reflectConfig
#print axioms diagonalCount_reflectConfig
#print axioms antidiagonalCount_reflectConfig
#print axioms outerCount_reflectConfig
#print axioms blackCells_reflectConfig
#print axioms whiteCells_reflectConfig
#print axioms exists_chamber

end PeaceableQueens.UpperBound.ConfigurationBridge
