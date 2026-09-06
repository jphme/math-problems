import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCutTable

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open PeaceableQueens.UpperBound.FiniteCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def dual4_60 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 3 else
  if row = rowOfFlat 1 then -3 else
  if row = rowOfFlat 2 then -3 else
  if row = rowOfFlat 4 then -1 else
  if row = rowOfFlat 5 then 3 else
  if row = rowOfFlat 7 then 1 else
  if row = rowOfFlat 9 then 1 else
  if row = rowOfFlat 10 then 3 else
  if row = rowOfFlat 11 then -2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 15 then 1 else
  if row = rowOfFlat 16 then 1 else
  if row = rowOfFlat 17 then 1 else
  if row = rowOfFlat 18 then 1 else
  if row = rowOfFlat 19 then 1 else
  if row = rowOfFlat 20 then 3 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 25 then 1 else
  if row = rowOfFlat 26 then 1 else
  if row = rowOfFlat 27 then 1 else
  if row = rowOfFlat 28 then 1 else
  if row = rowOfFlat 29 then 1 else
  if row = rowOfFlat 30 then 3 else
  if row = rowOfFlat 31 then -3 else
  if row = rowOfFlat 32 then -3 else
  if row = rowOfFlat 34 then -1 else
  if row = rowOfFlat 35 then 3 else
  if row = rowOfFlat 37 then 1 else
  if row = rowOfFlat 39 then 1 else
  if row = rowOfFlat 41 then 1 else
  0
def dual_60 (row : MomentRow) : ℚ := (dual4_60 row : ℚ) / 4

lemma cut_60_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 4 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 4) else 0) ≤
        ∑ row, dual_60 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_60, dual4_60, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_60_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_60 row * rhs p row) =
      (FiniteCertificates.cuts 60).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_60, dual4_60, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_60_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 60).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_60 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 4) (by norm_num) (by norm_num)
      coefficient dual_60 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_60_columnwise_kernel inner
  rw [cut_60_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 60).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_61 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 3 else
  if row = rowOfFlat 1 then -3 else
  if row = rowOfFlat 2 then -3 else
  if row = rowOfFlat 3 then -1 else
  if row = rowOfFlat 5 then 3 else
  if row = rowOfFlat 6 then 1 else
  if row = rowOfFlat 8 then 1 else
  if row = rowOfFlat 10 then 3 else
  if row = rowOfFlat 11 then -2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 15 then 1 else
  if row = rowOfFlat 16 then 1 else
  if row = rowOfFlat 17 then 1 else
  if row = rowOfFlat 18 then 1 else
  if row = rowOfFlat 19 then 1 else
  if row = rowOfFlat 20 then 3 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 25 then 1 else
  if row = rowOfFlat 26 then 1 else
  if row = rowOfFlat 27 then 1 else
  if row = rowOfFlat 28 then 1 else
  if row = rowOfFlat 29 then 1 else
  if row = rowOfFlat 30 then 3 else
  if row = rowOfFlat 31 then -3 else
  if row = rowOfFlat 32 then -3 else
  if row = rowOfFlat 33 then -1 else
  if row = rowOfFlat 35 then 3 else
  if row = rowOfFlat 36 then 1 else
  if row = rowOfFlat 38 then 1 else
  if row = rowOfFlat 41 then 1 else
  0
def dual_61 (row : MomentRow) : ℚ := (dual4_61 row : ℚ) / 4

lemma cut_61_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 4 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 4) else 0) ≤
        ∑ row, dual_61 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_61, dual4_61, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_61_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_61 row * rhs p row) =
      (FiniteCertificates.cuts 61).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_61, dual4_61, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_61_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 61).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_61 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 4) (by norm_num) (by norm_num)
      coefficient dual_61 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_61_columnwise_kernel inner
  rw [cut_61_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 61).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_62 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 4 then -2 else
  if row = rowOfFlat 8 then 2 else
  if row = rowOfFlat 9 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 11 then -2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 16 then 2 else
  if row = rowOfFlat 17 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 26 then 2 else
  if row = rowOfFlat 27 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 32 then -2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 38 then 2 else
  if row = rowOfFlat 39 then 2 else
  if row = rowOfFlat 40 then 2 else
  if row = rowOfFlat 41 then 2 else
  0
def dual_62 (row : MomentRow) : ℚ := (dual4_62 row : ℚ) / 4

lemma cut_62_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_62 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_62, dual4_62, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_62_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_62 row * rhs p row) =
      (FiniteCertificates.cuts 62).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_62, dual4_62, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_62_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 62).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_62 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_62 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_62_columnwise_kernel inner
  rw [cut_62_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 62).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_63 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 4 then -2 else
  if row = rowOfFlat 6 then 2 else
  if row = rowOfFlat 7 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 18 then 2 else
  if row = rowOfFlat 19 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 28 then 2 else
  if row = rowOfFlat 29 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 36 then 2 else
  if row = rowOfFlat 37 then 2 else
  if row = rowOfFlat 40 then 2 else
  if row = rowOfFlat 41 then 2 else
  0
def dual_63 (row : MomentRow) : ℚ := (dual4_63 row : ℚ) / 4

lemma cut_63_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_63 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_63, dual4_63, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_63_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_63 row * rhs p row) =
      (FiniteCertificates.cuts 63).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_63, dual4_63, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_63_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 63).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_63 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_63 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_63_columnwise_kernel inner
  rw [cut_63_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 63).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith


end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
