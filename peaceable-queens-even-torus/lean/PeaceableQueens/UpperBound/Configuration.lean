import PeaceableQueens.Parity
import PeaceableQueens.UpperBound.MomentModel

/-!
# Even-torus configurations and normalized profiles

This file formalizes S21.  It exposes the reduction modulo two on `ZMod (2*q)`,
proves that each parity class has exactly `q` labels, packages the four line
sets, and defines the eight normalized outer-count coordinates in the exact
`R,C,D,A` order used by the moment model and released certificates.
-/

namespace PeaceableQueens.UpperBound.ConfigurationBridge

open MomentModel

-- Compatibility aliases keep the geometric API stable.
export PeaceableQueens.Parity
  (parityMap parityLabel parityLabels parityClass parityMap_label parityLabel_injective card_parityLabels parityMap_val parityLabels_eq_class card_parityClass)

/-- A line-colouring configuration on the `2q` torus. -/
structure Configuration (q : ℕ) where
  R : Finset (ZMod (2 * q))
  C : Finset (ZMod (2 * q))
  D : Finset (ZMod (2 * q))
  A : Finset (ZMod (2 * q))

/-- The black-cell and white-cell sets of a configuration. -/
def Configuration.blackCells (cfg : Configuration q) [NeZero (2 * q)] :
    Finset (Cell (2 * q)) :=
  PeaceableQueens.blackCells cfg.R cfg.C cfg.D cfg.A

def Configuration.whiteCells (cfg : Configuration q) [NeZero (2 * q)] :
    Finset (Cell (2 * q)) :=
  PeaceableQueens.whiteCells cfg.R cfg.C cfg.D cfg.A

/-- The four family-specific count functions used by the S21 coordinate order. -/
def rowCount (cfg : Configuration q) (p : Parity) : ℕ :=
  (cfg.R.filter fun x => parityMap q x = (p.val : ZMod 2)).card

def columnCount (cfg : Configuration q) (p : Parity) : ℕ :=
  (cfg.C.filter fun x => parityMap q x = (p.val : ZMod 2)).card

def diagonalCount (cfg : Configuration q) (p : Parity) : ℕ :=
  (cfg.D.filter fun x => parityMap q x = (p.val : ZMod 2)).card

def antidiagonalCount (cfg : Configuration q) (p : Parity) : ℕ :=
  (cfg.A.filter fun x => parityMap q x = (p.val : ZMod 2)).card


/-- The eight outer parity counts, in `R,C,D,A` family order. -/
def outerCount (cfg : Configuration q) : OuterCoord → ℕ
  | ⟨.row, p⟩ => rowCount cfg p
  | ⟨.column, p⟩ => columnCount cfg p
  | ⟨.diagonal, p⟩ => diagonalCount cfg p
  | ⟨.antidiagonal, p⟩ => antidiagonalCount cfg p

/-- The S21 normalized profile, as the profile function expected by `MomentModel`. -/
def normalizedProfile (cfg : Configuration q) : OuterCoord → ℚ :=
  fun coord => (outerCount cfg coord : ℚ) / (q : ℚ)

lemma outerCount_le (cfg : Configuration q) (hq : 0 < q) (coord : OuterCoord) :
    outerCount cfg coord ≤ q := by
  letI : NeZero (2 * q) := ⟨by omega⟩
  cases coord with
  | mk family p =>
    have hfilter (s : Finset (ZMod (2 * q))) :
        s.filter (fun x => parityMap q x = (p.val : ZMod 2)) ⊆ parityClass q p := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    cases family with
    | row =>
      simpa [outerCount, rowCount] using (Finset.card_le_card (hfilter cfg.R)).trans_eq (card_parityClass q p)
    | column =>
      simpa [outerCount, columnCount] using (Finset.card_le_card (hfilter cfg.C)).trans_eq (card_parityClass q p)
    | diagonal =>
      simpa [outerCount, diagonalCount] using (Finset.card_le_card (hfilter cfg.D)).trans_eq (card_parityClass q p)
    | antidiagonal =>
      simpa [outerCount, antidiagonalCount] using (Finset.card_le_card (hfilter cfg.A)).trans_eq (card_parityClass q p)

/-- Every normalized outer coordinate lies in the unit interval. -/
theorem normalizedProfile_range (cfg : Configuration q) (hq : 0 < q)
    (coord : OuterCoord) :
    0 ≤ normalizedProfile cfg coord ∧ normalizedProfile cfg coord ≤ 1 := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hqQ)
  · apply (div_le_iff₀ hqQ).2
    have hcount : (outerCount cfg coord : ℚ) ≤ (q : ℚ) := by
      exact_mod_cast outerCount_le cfg hq coord
    simpa using hcount

lemma normalizedProfile_eq_div (cfg : Configuration q) (coord : OuterCoord) :
    normalizedProfile cfg coord = (outerCount cfg coord : ℚ) / (q : ℚ) := rfl

#print axioms card_parityClass
#print axioms outerCount_le
#print axioms normalizedProfile_range

end PeaceableQueens.UpperBound.ConfigurationBridge
