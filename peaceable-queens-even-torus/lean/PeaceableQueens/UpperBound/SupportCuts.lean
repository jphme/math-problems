import PeaceableQueens.UpperBound.ConfigurationBridge

namespace PeaceableQueens.UpperBound.SupportCuts

open MomentModel LPModel ConfigurationMoments ModelCompatibility DualLeaf ConfigurationBridge

abbrev E := EqCoord

/-- Support dual 609 of the paper's certified cut library (`new_dual_cuts.json`
in the ancillary bundle, shipped there again as `even_finite_support_cuts.json`),
transcribed from its 42 stored multipliers in the released row order into the
semantic rows of `MomentModel`; its weight is `alpha = 1`, so it bounds the black
count (paper `lem:cuts`, `eq:FB`).  The transcription is checked, not trusted:
`cut609_columnwise_kernel` re-proves all 64 columnwise support inequalities in
the kernel and `cut609_rhs_local` re-derives the paper's polynomial `F_B`. -/
def dual609 : MomentRow → ℚ
  | .block ⟨0, 0⟩ .normalization => 1
  | .block ⟨0, 0⟩ .diagonal => -1
  | .block ⟨0, 0⟩ .antidiagonal => -1
  | .block ⟨0, 0⟩ .rowColumn => 1
  | .block ⟨1, 1⟩ .normalization => 3
  | .block ⟨1, 1⟩ .row => -2
  | .block ⟨1, 1⟩ .column => -2
  | .block ⟨1, 1⟩ .diagonal => -2
  | .block ⟨1, 1⟩ .antidiagonal => -2
  | .block ⟨1, 1⟩ .rowColumn => 1
  | .block ⟨1, 1⟩ .rowDiagonal => 1
  | .block ⟨1, 1⟩ .rowAntidiagonal => 1
  | .block ⟨1, 1⟩ .columnDiagonal => 1
  | .block ⟨1, 1⟩ .columnAntidiagonal => 1
  | .aggregateDA 0 => 1
  | .aggregateDA 1 => 1
  | _ => 0

/-- Support dual 559 of the same library, transcribed in the same way; its weight
is `alpha = 0`, so it bounds the white count (paper `lem:cuts`, `eq:FW`).
`cut559_columnwise_kernel` and `cut559_rhs_local` check it as for 609. -/
def dual559 : MomentRow → ℚ
  | .block ⟨0, 0⟩ .normalization => 1
  | .block ⟨0, 0⟩ .diagonal => -1
  | .block ⟨0, 0⟩ .antidiagonal => -1
  | .block ⟨0, 1⟩ .normalization => 1
  | .block ⟨0, 1⟩ .row => -1
  | .block ⟨0, 1⟩ .column => -1
  | .block ⟨0, 1⟩ .diagonal => -1
  | .block ⟨0, 1⟩ .antidiagonal => -1
  | .block ⟨0, 1⟩ .rowColumn => 1
  | .block ⟨0, 1⟩ .rowDiagonal => 1
  | .block ⟨0, 1⟩ .rowAntidiagonal => 1
  | .block ⟨0, 1⟩ .columnDiagonal => 1
  | .block ⟨0, 1⟩ .columnAntidiagonal => 1
  | .block ⟨1, 0⟩ .normalization => 1
  | .block ⟨1, 0⟩ .row => -1
  | .block ⟨1, 0⟩ .column => -1
  | .block ⟨1, 0⟩ .diagonal => -1
  | .block ⟨1, 0⟩ .antidiagonal => -1
  | .block ⟨1, 0⟩ .rowColumn => 1
  | .block ⟨1, 0⟩ .rowDiagonal => 1
  | .block ⟨1, 0⟩ .rowAntidiagonal => 1
  | .block ⟨1, 0⟩ .columnDiagonal => 1
  | .block ⟨1, 0⟩ .columnAntidiagonal => 1
  | .block ⟨1, 1⟩ .normalization => 1
  | .block ⟨1, 1⟩ .diagonal => -1
  | .block ⟨1, 1⟩ .antidiagonal => -1
  | .aggregateDA 0 => 1
  | .aggregateDA 1 => 1
  | _ => 0

set_option maxRecDepth 1000000 in
lemma row_bij : Function.Bijective rowOfFlat := by decide

lemma sum_rows (f : MomentRow → ℚ) :
    (∑ row, f row) = ∑ e : EqCoord, f (rowOfFlat e) := by
  symm
  exact Fintype.sum_equiv (Equiv.ofBijective rowOfFlat row_bij) _ _ (by intro e; rfl)

lemma sum_rows_explicit (f : MomentRow → ℚ) :
    (∑ row, f row) =
      f (.block ⟨0,0⟩ .normalization) + f (.block ⟨0,0⟩ .row) +
      f (.block ⟨0,0⟩ .column) + f (.block ⟨0,0⟩ .diagonal) +
      f (.block ⟨0,0⟩ .antidiagonal) + f (.block ⟨0,0⟩ .rowColumn) +
      f (.block ⟨0,0⟩ .rowDiagonal) + f (.block ⟨0,0⟩ .rowAntidiagonal) +
      f (.block ⟨0,0⟩ .columnDiagonal) + f (.block ⟨0,0⟩ .columnAntidiagonal) +
      f (.block ⟨0,1⟩ .normalization) + f (.block ⟨0,1⟩ .row) +
      f (.block ⟨0,1⟩ .column) + f (.block ⟨0,1⟩ .diagonal) +
      f (.block ⟨0,1⟩ .antidiagonal) + f (.block ⟨0,1⟩ .rowColumn) +
      f (.block ⟨0,1⟩ .rowDiagonal) + f (.block ⟨0,1⟩ .rowAntidiagonal) +
      f (.block ⟨0,1⟩ .columnDiagonal) + f (.block ⟨0,1⟩ .columnAntidiagonal) +
      f (.block ⟨1,0⟩ .normalization) + f (.block ⟨1,0⟩ .row) +
      f (.block ⟨1,0⟩ .column) + f (.block ⟨1,0⟩ .diagonal) +
      f (.block ⟨1,0⟩ .antidiagonal) + f (.block ⟨1,0⟩ .rowColumn) +
      f (.block ⟨1,0⟩ .rowDiagonal) + f (.block ⟨1,0⟩ .rowAntidiagonal) +
      f (.block ⟨1,0⟩ .columnDiagonal) + f (.block ⟨1,0⟩ .columnAntidiagonal) +
      f (.block ⟨1,1⟩ .normalization) + f (.block ⟨1,1⟩ .row) +
      f (.block ⟨1,1⟩ .column) + f (.block ⟨1,1⟩ .diagonal) +
      f (.block ⟨1,1⟩ .antidiagonal) + f (.block ⟨1,1⟩ .rowColumn) +
      f (.block ⟨1,1⟩ .rowDiagonal) + f (.block ⟨1,1⟩ .rowAntidiagonal) +
      f (.block ⟨1,1⟩ .columnDiagonal) + f (.block ⟨1,1⟩ .columnAntidiagonal) +
      f (.aggregateDA 0) + f (.aggregateDA 1) := by
  rw [sum_rows]
  simp [Fin.sum_univ_succ, rowOfFlat, blockOfFlat, blockRow, blockCol,
    blockMomentOfFlat, fin4, fin10]
  ring

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
lemma cut609_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) else 0) +
      (if inner.atom = whiteAtom then (0 : ℚ) else 0) ≤
        ∑ row, dual609 row * coefficient row inner := by
  intro inner
  have hsum := sum_rows_explicit (fun row : MomentRow =>
    dual609 row * coefficient row inner)
  rw [hsum]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual609, coefficient, BlockMoment.eval, Block.squareParity, Fin.ext_iff,
        blackAtom, whiteAtom] <;> norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
lemma cut559_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (0 : ℚ) else 0) +
      (if inner.atom = whiteAtom then (1 : ℚ) else 0) ≤
        ∑ row, dual559 row * coefficient row inner := by
  intro inner
  have hsum := sum_rows_explicit (fun row : MomentRow =>
    dual559 row * coefficient row inner)
  rw [hsum]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual559, coefficient, BlockMoment.eval, Block.squareParity, Fin.ext_iff,
        blackAtom, whiteAtom] <;> norm_num

lemma cut609_columnwise : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) else 0) +
      (if inner.atom = whiteAtom then (0 : ℚ) else 0) ≤
        ∑ row, dual609 row * coefficient row inner := by
  exact cut609_columnwise_kernel

lemma cut559_columnwise : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (0 : ℚ) else 0) +
      (if inner.atom = whiteAtom then (1 : ℚ) else 0) ≤
        ∑ row, dual559 row * coefficient row inner := by
  exact cut559_columnwise_kernel

lemma cut609_rhs (p : OuterCoord → ℚ) :
    (∑ row, dual609 row * rhs p row) =
      4 + p ⟨.row, 0⟩ * p ⟨.column, 0⟩ - 2 * p ⟨.row, 1⟩ -
        2 * p ⟨.column, 1⟩ +
        p ⟨.row, 1⟩ * p ⟨.column, 1⟩ +
        p ⟨.row, 1⟩ * p ⟨.diagonal, 0⟩ +
        p ⟨.row, 1⟩ * p ⟨.antidiagonal, 0⟩ +
        p ⟨.column, 1⟩ * p ⟨.diagonal, 0⟩ +
        p ⟨.column, 1⟩ * p ⟨.antidiagonal, 0⟩ -
        3 * p ⟨.diagonal, 0⟩ +
        2 * p ⟨.diagonal, 0⟩ * p ⟨.antidiagonal, 0⟩ +
        2 * p ⟨.diagonal, 1⟩ * p ⟨.antidiagonal, 1⟩ -
        3 * p ⟨.antidiagonal, 0⟩ := by
  rw [sum_rows_explicit]
  simp [dual609, rowOfFlat, rhs, rhsTerm, RhsTerm.eval, blockCoord,
    Block.squareParity, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 2000000 in
lemma cut559_rhs (p : OuterCoord → ℚ) :
    (∑ row, dual559 row * rhs p row) =
      4 - p ⟨.row, 0⟩ + p ⟨.row, 0⟩ * p ⟨.column, 1⟩ +
        p ⟨.row, 0⟩ * p ⟨.diagonal, 1⟩ +
        p ⟨.row, 0⟩ * p ⟨.antidiagonal, 1⟩ -
        p ⟨.row, 1⟩ + p ⟨.row, 1⟩ * p ⟨.column, 0⟩ +
        p ⟨.row, 1⟩ * p ⟨.diagonal, 1⟩ +
        p ⟨.row, 1⟩ * p ⟨.antidiagonal, 1⟩ -
        p ⟨.column, 0⟩ + p ⟨.column, 0⟩ * p ⟨.diagonal, 1⟩ +
        p ⟨.column, 0⟩ * p ⟨.antidiagonal, 1⟩ -
        p ⟨.column, 1⟩ + p ⟨.column, 1⟩ * p ⟨.diagonal, 1⟩ +
        p ⟨.column, 1⟩ * p ⟨.antidiagonal, 1⟩ -
        2 * p ⟨.diagonal, 0⟩ +
        2 * p ⟨.diagonal, 0⟩ * p ⟨.antidiagonal, 0⟩ -
        2 * p ⟨.diagonal, 1⟩ + 2 * p ⟨.diagonal, 1⟩ * p ⟨.antidiagonal, 1⟩ -
        2 * p ⟨.antidiagonal, 0⟩ - 2 * p ⟨.antidiagonal, 1⟩ := by
  rw [sum_rows_explicit]
  simp [dual559, rowOfFlat, rhs, rhsTerm, RhsTerm.eval, blockCoord,
    Block.squareParity, Fin.sum_univ_succ]
  ring

/-- Paper `lem:cuts`: the black-only moment-dual bound. -/
lemma cut609_black_bound (cfg : Configuration q) (hq : 0 < q) :
    blackTotal (configurationWeights cfg) ≤
      ∑ row, dual609 row * rhs (normalizedProfile cfg) row := by
  simpa [blackTotal, whiteTotal, atomTotal] using
    (support_weighted_dual_sound_indicator (1 : ℚ)
    coefficient dual609 (configurationWeights cfg)
    (fun row => rhs (normalizedProfile cfg) row)
    (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    (configurationWeights_nonnegative cfg)
    (configurationWeights_satisfiesMoments cfg hq)
    (by intro inner; simpa using cut609_columnwise inner))

/-- Paper `lem:cuts`: the white-only moment-dual bound. -/
lemma cut559_white_bound (cfg : Configuration q) (hq : 0 < q) :
    whiteTotal (configurationWeights cfg) ≤
      ∑ row, dual559 row * rhs (normalizedProfile cfg) row := by
  simpa [blackTotal, whiteTotal, atomTotal] using
    (support_weighted_dual_sound_indicator (0 : ℚ)
    coefficient dual559 (configurationWeights cfg)
    (fun row => rhs (normalizedProfile cfg) row)
    (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    (configurationWeights_nonnegative cfg)
    (configurationWeights_satisfiesMoments cfg hq)
    (by intro inner; simpa using cut559_columnwise inner))

/-- Compatibility minimum-objective bounds used by the finite/large assembly. -/
lemma cut609_bound (cfg : Configuration q) (hq : 0 < q) :
    min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual609 row * rhs (normalizedProfile cfg) row :=
  (min_le_left _ _).trans (cut609_black_bound cfg hq)

lemma cut559_bound (cfg : Configuration q) (hq : 0 < q) :
    min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual559 row * rhs (normalizedProfile cfg) row :=
  (min_le_right _ _).trans (cut559_white_bound cfg hq)

def localProfile (u R v C g e h f : ℚ) : OuterCoord → ℚ
  | ⟨.row, 0⟩ => u
  | ⟨.row, 1⟩ => R
  | ⟨.column, 0⟩ => v
  | ⟨.column, 1⟩ => C
  | ⟨.diagonal, 0⟩ => 1 - g
  | ⟨.diagonal, 1⟩ => e
  | ⟨.antidiagonal, 0⟩ => 1 - h
  | ⟨.antidiagonal, 1⟩ => f

def cut609Local (u R v C g e h f : ℚ) : ℚ :=
  (u * v + R * C) - (R + C - 1) * (g + h) + 2 * g * h + 2 * e * f

def cut559Local (u R v C g e h f : ℚ) : ℚ :=
  ((1 - u) * (1 - C) + (1 - R) * (1 - v)) -
      (2 - (R + C + u + v)) * (e + f) + 2 * e * f + 2 * g * h

lemma cut609_rhs_local (u R v C g e h f : ℚ) :
    (∑ row, dual609 row * rhs (localProfile u R v C g e h f) row) =
      cut609Local u R v C g e h f := by
  rw [cut609_rhs]
  simp [localProfile, cut609Local]
  ring

lemma cut559_rhs_local (u R v C g e h f : ℚ) :
    (∑ row, dual559 row * rhs (localProfile u R v C g e h f) row) =
      cut559Local u R v C g e h f := by
  rw [cut559_rhs]
  simp [localProfile, cut559Local]
  ring

#print axioms cut609_columnwise_kernel
#print axioms cut559_columnwise_kernel
#print axioms cut609_columnwise
#print axioms cut559_columnwise
#print axioms cut609_bound
#print axioms cut559_bound
#print axioms cut609_rhs_local
#print axioms cut559_rhs_local

end PeaceableQueens.UpperBound.SupportCuts
