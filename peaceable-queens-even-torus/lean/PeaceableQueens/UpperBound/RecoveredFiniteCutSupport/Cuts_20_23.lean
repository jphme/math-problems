import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCutTable

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open PeaceableQueens.UpperBound.FiniteCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def dual4_20 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 4 else
  if row = rowOfFlat 3 then -4 else
  if row = rowOfFlat 10 then 4 else
  if row = rowOfFlat 11 then -4 else
  if row = rowOfFlat 12 then -4 else
  if row = rowOfFlat 15 then 4 else
  if row = rowOfFlat 20 then 4 else
  if row = rowOfFlat 21 then -4 else
  if row = rowOfFlat 22 then -4 else
  if row = rowOfFlat 25 then 4 else
  if row = rowOfFlat 30 then 4 else
  if row = rowOfFlat 33 then -4 else
  0
def dual_20 (row : MomentRow) : ℚ := (dual4_20 row : ℚ) / 4

lemma cut_20_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (0 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (0 : ℚ) / 1) else 0) ≤
        ∑ row, dual_20 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_20, dual4_20, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_20_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_20 row * rhs p row) =
      (FiniteCertificates.cuts 20).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_20, dual4_20, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_20_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 20).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_20 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((0 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_20 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_20_columnwise_kernel inner
  rw [cut_20_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 20).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_21 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 4 else
  if row = rowOfFlat 4 then -4 else
  if row = rowOfFlat 10 then 4 else
  if row = rowOfFlat 11 then -4 else
  if row = rowOfFlat 12 then -4 else
  if row = rowOfFlat 15 then 4 else
  if row = rowOfFlat 20 then 4 else
  if row = rowOfFlat 21 then -4 else
  if row = rowOfFlat 22 then -4 else
  if row = rowOfFlat 25 then 4 else
  if row = rowOfFlat 30 then 4 else
  if row = rowOfFlat 34 then -4 else
  0
def dual_21 (row : MomentRow) : ℚ := (dual4_21 row : ℚ) / 4

lemma cut_21_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (0 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (0 : ℚ) / 1) else 0) ≤
        ∑ row, dual_21 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_21, dual4_21, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_21_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_21 row * rhs p row) =
      (FiniteCertificates.cuts 21).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_21, dual4_21, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_21_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 21).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_21 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((0 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_21 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_21_columnwise_kernel inner
  rw [cut_21_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 21).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_22 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 5 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 11 then -2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 15 then 2 else
  if row = rowOfFlat 17 then 2 else
  if row = rowOfFlat 19 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 27 then 2 else
  if row = rowOfFlat 28 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 32 then -2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 35 then 2 else
  if row = rowOfFlat 36 then 2 else
  if row = rowOfFlat 37 then 2 else
  if row = rowOfFlat 38 then 2 else
  if row = rowOfFlat 39 then 2 else
  if row = rowOfFlat 40 then 2 else
  0
def dual_22 (row : MomentRow) : ℚ := (dual4_22 row : ℚ) / 4

lemma cut_22_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_22 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_22, dual4_22, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_22_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_22 row * rhs p row) =
      (FiniteCertificates.cuts 22).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_22, dual4_22, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_22_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 22).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_22 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_22 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_22_columnwise_kernel inner
  rw [cut_22_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 22).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_23 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 5 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 11 then -2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 15 then 2 else
  if row = rowOfFlat 16 then 2 else
  if row = rowOfFlat 18 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 26 then 2 else
  if row = rowOfFlat 29 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 32 then -2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 35 then 2 else
  if row = rowOfFlat 36 then 2 else
  if row = rowOfFlat 37 then 2 else
  if row = rowOfFlat 38 then 2 else
  if row = rowOfFlat 39 then 2 else
  if row = rowOfFlat 40 then 2 else
  0
def dual_23 (row : MomentRow) : ℚ := (dual4_23 row : ℚ) / 4

lemma cut_23_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_23 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_23, dual4_23, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_23_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_23 row * rhs p row) =
      (FiniteCertificates.cuts 23).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_23, dual4_23, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_23_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 23).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_23 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_23 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_23_columnwise_kernel inner
  rw [cut_23_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 23).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith


end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
