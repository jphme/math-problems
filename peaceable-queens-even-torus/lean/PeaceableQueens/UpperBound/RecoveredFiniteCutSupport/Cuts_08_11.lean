import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCutTable

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open PeaceableQueens.UpperBound.FiniteCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def dual4_8 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 4 else
  if row = rowOfFlat 2 then -4 else
  if row = rowOfFlat 3 then -4 else
  if row = rowOfFlat 8 then 4 else
  if row = rowOfFlat 10 then 4 else
  if row = rowOfFlat 12 then -4 else
  if row = rowOfFlat 13 then -4 else
  if row = rowOfFlat 18 then 4 else
  if row = rowOfFlat 20 then 4 else
  if row = rowOfFlat 22 then -4 else
  if row = rowOfFlat 23 then -4 else
  if row = rowOfFlat 28 then 4 else
  if row = rowOfFlat 30 then 4 else
  if row = rowOfFlat 32 then -4 else
  if row = rowOfFlat 33 then -4 else
  if row = rowOfFlat 38 then 4 else
  0
def dual_8 (row : MomentRow) : ℚ := (dual4_8 row : ℚ) / 4

lemma cut_8_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (0 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (0 : ℚ) / 1) else 0) ≤
        ∑ row, dual_8 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_8, dual4_8, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_8_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_8 row * rhs p row) =
      (FiniteCertificates.cuts 8).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_8, dual4_8, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_8_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 8).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_8 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((0 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_8 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_8_columnwise_kernel inner
  rw [cut_8_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 8).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_9 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 4 else
  if row = rowOfFlat 2 then -4 else
  if row = rowOfFlat 4 then -4 else
  if row = rowOfFlat 9 then 4 else
  if row = rowOfFlat 10 then 4 else
  if row = rowOfFlat 12 then -4 else
  if row = rowOfFlat 14 then -4 else
  if row = rowOfFlat 19 then 4 else
  if row = rowOfFlat 20 then 4 else
  if row = rowOfFlat 22 then -4 else
  if row = rowOfFlat 24 then -4 else
  if row = rowOfFlat 29 then 4 else
  if row = rowOfFlat 30 then 4 else
  if row = rowOfFlat 32 then -4 else
  if row = rowOfFlat 34 then -4 else
  if row = rowOfFlat 39 then 4 else
  0
def dual_9 (row : MomentRow) : ℚ := (dual4_9 row : ℚ) / 4

lemma cut_9_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (0 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (0 : ℚ) / 1) else 0) ≤
        ∑ row, dual_9 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_9, dual4_9, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_9_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_9 row * rhs p row) =
      (FiniteCertificates.cuts 9).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_9, dual4_9, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_9_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 9).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_9 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((0 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_9 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_9_columnwise_kernel inner
  rw [cut_9_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 9).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_10 : MomentRow → Int := fun row =>
  if row = rowOfFlat 40 then 4 else
  if row = rowOfFlat 41 then 4 else
  0
def dual_10 (row : MomentRow) : ℚ := (dual4_10 row : ℚ) / 4

lemma cut_10_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 1) else 0) ≤
        ∑ row, dual_10 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_10, dual4_10, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_10_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_10 row * rhs p row) =
      (FiniteCertificates.cuts 10).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_10, dual4_10, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_10_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 10).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_10 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_10 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_10_columnwise_kernel inner
  rw [cut_10_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 10).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_11 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 4 else
  if row = rowOfFlat 3 then -4 else
  if row = rowOfFlat 4 then -4 else
  if row = rowOfFlat 10 then 4 else
  if row = rowOfFlat 13 then -4 else
  if row = rowOfFlat 14 then -4 else
  if row = rowOfFlat 20 then 4 else
  if row = rowOfFlat 23 then -4 else
  if row = rowOfFlat 24 then -4 else
  if row = rowOfFlat 30 then 4 else
  if row = rowOfFlat 33 then -4 else
  if row = rowOfFlat 34 then -4 else
  if row = rowOfFlat 40 then 4 else
  if row = rowOfFlat 41 then 4 else
  0
def dual_11 (row : MomentRow) : ℚ := (dual4_11 row : ℚ) / 4

lemma cut_11_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (0 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (0 : ℚ) / 1) else 0) ≤
        ∑ row, dual_11 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_11, dual4_11, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_11_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_11 row * rhs p row) =
      (FiniteCertificates.cuts 11).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_11, dual4_11, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_11_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 11).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_11 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((0 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_11 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_11_columnwise_kernel inner
  rw [cut_11_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 11).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith


end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
