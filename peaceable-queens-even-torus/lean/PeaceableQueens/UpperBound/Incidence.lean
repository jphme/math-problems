import PeaceableQueens.Defs
import PeaceableQueens.UpperBound.Configuration

/-!
# Torus line-pair incidences

The algebraic core of paper `lem:inc` (S22) for a board of order `2*q`.

Every pair of distinct line families except diagonal/antidiagonal gives a
bijection from cells to pairs of line labels.  The diagonal/antidiagonal map
instead has two-element nonempty fibres, whose points differ by the
simultaneous half-turn.  In particular, this file does *not* assert the
false per-parity-block diagonal/antidiagonal factorization.
-/

namespace PeaceableQueens.UpperBound.Incidence

open MomentModel
open ConfigurationBridge

/-- A positive half-order gives a nonzero even board order. -/
instance evenOrderNeZero (q : ℕ) [NeZero q] : NeZero (2 * q) :=
  ⟨Nat.mul_ne_zero (by decide) (NeZero.ne q)⟩

/-! ## The five determinant-`±1` line-pair maps -/

/-- Row/column labels of a cell. -/
def rowColumnLabels (n : ℕ) : Cell n → Cell n := fun p => (p.1, p.2)

/-- Row/diagonal labels of a cell. -/
def rowDiagonalLabels (n : ℕ) : Cell n → Cell n := fun p => (p.1, p.1 - p.2)

/-- Row/antidiagonal labels of a cell. -/
def rowAntidiagonalLabels (n : ℕ) : Cell n → Cell n := fun p => (p.1, p.1 + p.2)

/-- Column/diagonal labels of a cell. -/
def columnDiagonalLabels (n : ℕ) : Cell n → Cell n := fun p => (p.2, p.1 - p.2)

/-- Column/antidiagonal labels of a cell. -/
def columnAntidiagonalLabels (n : ℕ) : Cell n → Cell n := fun p => (p.2, p.1 + p.2)

def rowColumnInverse (n : ℕ) : Cell n → Cell n := fun p => (p.1, p.2)
def rowDiagonalInverse (n : ℕ) : Cell n → Cell n := fun p => (p.1, p.1 - p.2)
def rowAntidiagonalInverse (n : ℕ) : Cell n → Cell n := fun p => (p.1, p.2 - p.1)
def columnDiagonalInverse (n : ℕ) : Cell n → Cell n := fun p => (p.1 + p.2, p.1)
def columnAntidiagonalInverse (n : ℕ) : Cell n → Cell n := fun p => (p.2 - p.1, p.1)

lemma rowColumn_leftInv (n : ℕ) :
    Function.LeftInverse (rowColumnInverse n) (rowColumnLabels n) := by
  intro p; ext <;> simp [rowColumnLabels, rowColumnInverse]

lemma rowColumn_rightInv (n : ℕ) :
    Function.RightInverse (rowColumnInverse n) (rowColumnLabels n) := by
  intro p; ext <;> simp [rowColumnLabels, rowColumnInverse]

lemma rowDiagonal_leftInv (n : ℕ) :
    Function.LeftInverse (rowDiagonalInverse n) (rowDiagonalLabels n) := by
  intro p; ext <;> simp [rowDiagonalLabels, rowDiagonalInverse]

lemma rowDiagonal_rightInv (n : ℕ) :
    Function.RightInverse (rowDiagonalInverse n) (rowDiagonalLabels n) := by
  intro p; ext <;> simp [rowDiagonalLabels, rowDiagonalInverse]

lemma rowAntidiagonal_leftInv (n : ℕ) :
    Function.LeftInverse (rowAntidiagonalInverse n) (rowAntidiagonalLabels n) := by
  intro p; ext <;> simp [rowAntidiagonalLabels, rowAntidiagonalInverse]

lemma rowAntidiagonal_rightInv (n : ℕ) :
    Function.RightInverse (rowAntidiagonalInverse n) (rowAntidiagonalLabels n) := by
  intro p; ext <;> simp [rowAntidiagonalLabels, rowAntidiagonalInverse]

lemma columnDiagonal_leftInv (n : ℕ) :
    Function.LeftInverse (columnDiagonalInverse n) (columnDiagonalLabels n) := by
  intro p; ext <;> simp [columnDiagonalLabels, columnDiagonalInverse]

lemma columnDiagonal_rightInv (n : ℕ) :
    Function.RightInverse (columnDiagonalInverse n) (columnDiagonalLabels n) := by
  intro p; ext <;> simp [columnDiagonalLabels, columnDiagonalInverse]

lemma columnAntidiagonal_leftInv (n : ℕ) :
    Function.LeftInverse (columnAntidiagonalInverse n) (columnAntidiagonalLabels n) := by
  intro p; ext <;> simp [columnAntidiagonalLabels, columnAntidiagonalInverse]

lemma columnAntidiagonal_rightInv (n : ℕ) :
    Function.RightInverse (columnAntidiagonalInverse n) (columnAntidiagonalLabels n) := by
  intro p; ext <;> simp [columnAntidiagonalLabels, columnAntidiagonalInverse]

lemma rowColumn_bijective (n : ℕ) : Function.Bijective (rowColumnLabels n) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨rowColumnInverse n, rowColumn_leftInv n, rowColumn_rightInv n⟩

lemma rowDiagonal_bijective (n : ℕ) : Function.Bijective (rowDiagonalLabels n) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨rowDiagonalInverse n, rowDiagonal_leftInv n, rowDiagonal_rightInv n⟩

lemma rowAntidiagonal_bijective (n : ℕ) : Function.Bijective (rowAntidiagonalLabels n) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨rowAntidiagonalInverse n, rowAntidiagonal_leftInv n, rowAntidiagonal_rightInv n⟩

lemma columnDiagonal_bijective (n : ℕ) : Function.Bijective (columnDiagonalLabels n) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨columnDiagonalInverse n, columnDiagonal_leftInv n, columnDiagonal_rightInv n⟩

lemma columnAntidiagonal_bijective (n : ℕ) :
    Function.Bijective (columnAntidiagonalLabels n) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨columnAntidiagonalInverse n, columnAntidiagonal_leftInv n,
      columnAntidiagonal_rightInv n⟩

/-! ## The determinant-two diagonal/antidiagonal map -/

/-- The diagonal/antidiagonal label pair of a cell. -/
def diagonalAntidiagonalLabels (n : ℕ) : Cell n → Cell n :=
  fun p => (p.1 - p.2, p.1 + p.2)

/-- Simultaneous translation of both coordinates by the half-order. -/
def halfTurn (q : ℕ) : Cell (2 * q) → Cell (2 * q) :=
  fun p => (p.1 + q, p.2 + q)

/-- The kernel of multiplication by two on `ZMod (2*q)`. -/
lemma two_mul_eq_zero_iff_eq_zero_or_half (q : ℕ) [NeZero q] (x : ZMod (2 * q)) :
    2 * x = 0 ↔ x = 0 ∨ x = (q : ZMod (2 * q)) := by
  constructor
  · intro hx
    have hneg : -x = x := (neg_eq_iff_add_eq_zero).mpr (by simpa [two_mul] using hx)
    rw [ZMod.neg_eq_self_iff] at hneg
    rcases hneg with hzero | hval
    · exact Or.inl hzero
    · right
      rw [← x.natCast_zmod_val]
      congr
      omega
  · rintro (rfl | rfl)
    · simp
    · calc
        2 * (q : ZMod (2 * q)) = (q : ZMod (2 * q)) + q := two_mul _
        _ = ((q + q : ℕ) : ZMod (2 * q)) := (Nat.cast_add _ _).symm
        _ = ((2 * q : ℕ) : ZMod (2 * q)) := by
          congr 1
          omega
        _ = 0 := ZMod.natCast_self _

lemma diagonalAntidiagonal_halfTurn (q : ℕ) [NeZero q] (p : Cell (2 * q)) :
    diagonalAntidiagonalLabels (2 * q) (halfTurn q p) =
      diagonalAntidiagonalLabels (2 * q) p := by
  ext
  · dsimp [diagonalAntidiagonalLabels, halfTurn]
    ring
  · have hq : 2 * (q : ZMod (2 * q)) = 0 :=
      two_mul_eq_zero_iff_eq_zero_or_half q (q : ZMod (2 * q)) |>.mpr (Or.inr rfl)
    dsimp [diagonalAntidiagonalLabels, halfTurn]
    linear_combination hq

/-- Two cells with equal diagonal/antidiagonal labels are equal or differ by
the simultaneous half-turn. -/
lemma diagonalAntidiagonal_collision (q : ℕ) [NeZero q] {p p' : Cell (2 * q)}
    (h : diagonalAntidiagonalLabels (2 * q) p = diagonalAntidiagonalLabels (2 * q) p') :
    p = p' ∨ p = halfTurn q p' := by
  have hsub : p.1 - p.2 = p'.1 - p'.2 := congrArg Prod.fst h
  have hadd : p.1 + p.2 = p'.1 + p'.2 := congrArg Prod.snd h
  have htwo : 2 * (p.1 - p'.1) = 0 := by
    linear_combination hsub + hadd
  rcases two_mul_eq_zero_iff_eq_zero_or_half q (p.1 - p'.1) |>.mp htwo with hr | hr
  · left
    ext
    · exact sub_eq_zero.mp hr
    · have hr' : p.1 = p'.1 := sub_eq_zero.mp hr
      calc
        p.2 = p.1 - (p.1 - p.2) := by ring
        _ = p'.1 - (p'.1 - p'.2) := by rw [hsub, hr']
        _ = p'.2 := by ring
  · right
    ext
    · dsimp [halfTurn]
      exact sub_eq_iff_eq_add'.mp hr
    · dsimp [halfTurn]
      have hr' : p.1 = p'.1 + q := sub_eq_iff_eq_add'.mp hr
      calc
        p.2 = p.1 - (p.1 - p.2) := by ring
        _ = (p'.1 + q) - (p'.1 - p'.2) := by rw [hsub, hr']
        _ = p'.2 + q := by ring

lemma half_modulus_ne_zero (q : ℕ) [NeZero q] : (q : ZMod (2 * q)) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hle : 2 * q ≤ q := Nat.le_of_dvd (by omega) h
  omega

lemma ne_halfTurn (q : ℕ) [NeZero q] (p : Cell (2 * q)) : p ≠ halfTurn q p := by
  intro h
  have hfst := congrArg Prod.fst h
  dsimp [halfTurn] at hfst
  have hzero : (q : ZMod (2 * q)) = 0 := by
    calc
      (q : ZMod (2 * q)) = (p.1 + q) - p.1 := by ring
      _ = 0 := by rw [← hfst]; simp
  exact half_modulus_ne_zero q hzero

/-- The finite fibre of the diagonal/antidiagonal label map. -/
def diagonalAntidiagonalFibre (q : ℕ) [NeZero q] (label : Cell (2 * q)) :
    Finset (Cell (2 * q)) :=
  Finset.univ.filter fun p => diagonalAntidiagonalLabels (2 * q) p = label

lemma diagonalAntidiagonalFibre_eq_pair (q : ℕ) [NeZero q] (p : Cell (2 * q)) :
    diagonalAntidiagonalFibre q (diagonalAntidiagonalLabels (2 * q) p) =
      {p, halfTurn q p} := by
  ext x
  simp only [diagonalAntidiagonalFibre, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    exact diagonalAntidiagonal_collision q hx
  · rintro (rfl | rfl)
    · rfl
    · exact diagonalAntidiagonal_halfTurn q p

/-- Every nonempty diagonal/antidiagonal fibre on a `2q`-torus has two cells. -/
lemma card_diagonalAntidiagonalFibre_of_image (q : ℕ) [NeZero q] (p : Cell (2 * q)) :
    (diagonalAntidiagonalFibre q (diagonalAntidiagonalLabels (2 * q) p)).card = 2 := by
  rw [diagonalAntidiagonalFibre_eq_pair]
  simp [ne_halfTurn]

/-- A preimage of two diagonal/antidiagonal labels represented in one parity class. -/
def diagonalAntidiagonalPreimage (q : ℕ) (p : Parity) (j k : Fin q) : Cell (2 * q) :=
  ((j.val : ZMod (2 * q)) + k.val + p.val, k.val - j.val)

lemma diagonalAntidiagonal_preimage_labels (q : ℕ) (p : Parity) (j k : Fin q) :
    diagonalAntidiagonalLabels (2 * q) (diagonalAntidiagonalPreimage q p j k) =
      (parityLabel q p j, parityLabel q p k) := by
  ext <;> simp only [diagonalAntidiagonalLabels, diagonalAntidiagonalPreimage,
    parityLabel, Nat.cast_add, Nat.cast_mul]
  · ring
  · ring

lemma parity_diagonal_eq_antidiagonal (q : ℕ) (x : Cell (2 * q)) :
    parityMap q (x.1 - x.2) = parityMap q (x.1 + x.2) := by
  rw [map_sub, map_add, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

/-- A diagonal/antidiagonal label pair occurs on the `2q`-torus precisely
when its two labels have equal parity. -/
theorem diagonalAntidiagonal_mem_range_iff (q : ℕ) [NeZero q]
    (d a : ZMod (2 * q)) :
    (∃ x : Cell (2 * q), diagonalAntidiagonalLabels (2 * q) x = (d, a)) ↔
      parityMap q d = parityMap q a := by
  constructor
  · rintro ⟨x, hx⟩
    have hfst : x.1 - x.2 = d := congrArg Prod.fst hx
    have hsnd : x.1 + x.2 = a := congrArg Prod.snd hx
    rw [← hfst, ← hsnd]
    exact parity_diagonal_eq_antidiagonal q x
  · intro hpar
    let p : Parity := ⟨(parityMap q d).val, (parityMap q d).isLt⟩
    have hdp : parityMap q d = (p.val : ZMod 2) := by
      dsimp [p]
      exact (ZMod.natCast_zmod_val _).symm
    have hap : parityMap q a = (p.val : ZMod 2) := hpar.symm.trans hdp
    have hd : d ∈ parityClass q p := by
      simp only [parityClass, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdp
    have ha : a ∈ parityClass q p := by
      simp only [parityClass, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hap
    rw [← parityLabels_eq_class q p] at hd ha
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hd
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp ha
    refine ⟨diagonalAntidiagonalPreimage q p j k, ?_⟩
    rw [diagonalAntidiagonal_preimage_labels]
    simp [hj, hk]

#print axioms rowColumn_bijective
#print axioms columnAntidiagonal_bijective
#print axioms two_mul_eq_zero_iff_eq_zero_or_half
#print axioms card_diagonalAntidiagonalFibre_of_image
#print axioms diagonalAntidiagonal_mem_range_iff

end PeaceableQueens.UpperBound.Incidence
