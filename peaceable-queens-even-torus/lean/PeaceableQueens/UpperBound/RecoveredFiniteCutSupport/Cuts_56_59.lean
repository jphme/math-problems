import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCutTable

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open PeaceableQueens.UpperBound.FiniteCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def dual4_56 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 1 else
  if row = rowOfFlat 1 then -1 else
  if row = rowOfFlat 2 then -1 else
  if row = rowOfFlat 4 then -1 else
  if row = rowOfFlat 5 then 3 else
  if row = rowOfFlat 7 then 1 else
  if row = rowOfFlat 9 then 1 else
  if row = rowOfFlat 10 then 1 else
  if row = rowOfFlat 11 then -1 else
  if row = rowOfFlat 12 then -1 else
  if row = rowOfFlat 13 then -1 else
  if row = rowOfFlat 14 then -1 else
  if row = rowOfFlat 15 then 1 else
  if row = rowOfFlat 16 then 1 else
  if row = rowOfFlat 17 then 1 else
  if row = rowOfFlat 18 then 1 else
  if row = rowOfFlat 19 then 1 else
  if row = rowOfFlat 20 then 1 else
  if row = rowOfFlat 21 then -1 else
  if row = rowOfFlat 22 then -1 else
  if row = rowOfFlat 23 then -1 else
  if row = rowOfFlat 24 then -1 else
  if row = rowOfFlat 25 then 1 else
  if row = rowOfFlat 26 then 1 else
  if row = rowOfFlat 27 then 1 else
  if row = rowOfFlat 28 then 1 else
  if row = rowOfFlat 29 then 1 else
  if row = rowOfFlat 30 then 1 else
  if row = rowOfFlat 31 then -1 else
  if row = rowOfFlat 32 then -1 else
  if row = rowOfFlat 34 then -1 else
  if row = rowOfFlat 35 then 3 else
  if row = rowOfFlat 37 then 1 else
  if row = rowOfFlat 39 then 1 else
  if row = rowOfFlat 41 then 1 else
  0
def dual_56 (row : MomentRow) : ℚ := (dual4_56 row : ℚ) / 4

lemma cut_56_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (3 : ℚ) / 4 else 0) +
      (if inner.atom = whiteAtom then (1 - (3 : ℚ) / 4) else 0) ≤
        ∑ row, dual_56 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_56, dual4_56, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_56_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_56 row * rhs p row) =
      (FiniteCertificates.cuts 56).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_56, dual4_56, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_56_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 56).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_56 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((3 : ℚ) / 4) (by norm_num) (by norm_num)
      coefficient dual_56 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_56_columnwise_kernel inner
  rw [cut_56_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 56).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_57 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 1 else
  if row = rowOfFlat 1 then -1 else
  if row = rowOfFlat 2 then -1 else
  if row = rowOfFlat 3 then -1 else
  if row = rowOfFlat 5 then 3 else
  if row = rowOfFlat 6 then 1 else
  if row = rowOfFlat 8 then 1 else
  if row = rowOfFlat 10 then 1 else
  if row = rowOfFlat 11 then -1 else
  if row = rowOfFlat 12 then -1 else
  if row = rowOfFlat 13 then -1 else
  if row = rowOfFlat 14 then -1 else
  if row = rowOfFlat 15 then 1 else
  if row = rowOfFlat 16 then 1 else
  if row = rowOfFlat 17 then 1 else
  if row = rowOfFlat 18 then 1 else
  if row = rowOfFlat 19 then 1 else
  if row = rowOfFlat 20 then 1 else
  if row = rowOfFlat 21 then -1 else
  if row = rowOfFlat 22 then -1 else
  if row = rowOfFlat 23 then -1 else
  if row = rowOfFlat 24 then -1 else
  if row = rowOfFlat 25 then 1 else
  if row = rowOfFlat 26 then 1 else
  if row = rowOfFlat 27 then 1 else
  if row = rowOfFlat 28 then 1 else
  if row = rowOfFlat 29 then 1 else
  if row = rowOfFlat 30 then 1 else
  if row = rowOfFlat 31 then -1 else
  if row = rowOfFlat 32 then -1 else
  if row = rowOfFlat 33 then -1 else
  if row = rowOfFlat 35 then 3 else
  if row = rowOfFlat 36 then 1 else
  if row = rowOfFlat 38 then 1 else
  if row = rowOfFlat 41 then 1 else
  0
def dual_57 (row : MomentRow) : ℚ := (dual4_57 row : ℚ) / 4

lemma cut_57_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (3 : ℚ) / 4 else 0) +
      (if inner.atom = whiteAtom then (1 - (3 : ℚ) / 4) else 0) ≤
        ∑ row, dual_57 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_57, dual4_57, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_57_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_57 row * rhs p row) =
      (FiniteCertificates.cuts 57).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_57, dual4_57, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_57_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 57).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_57 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((3 : ℚ) / 4) (by norm_num) (by norm_num)
      coefficient dual_57 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_57_columnwise_kernel inner
  rw [cut_57_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 57).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_58 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 3 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 4 then -2 else
  if row = rowOfFlat 5 then 1 else
  if row = rowOfFlat 6 then 1 else
  if row = rowOfFlat 7 then 1 else
  if row = rowOfFlat 8 then 1 else
  if row = rowOfFlat 9 then 1 else
  if row = rowOfFlat 10 then 3 else
  if row = rowOfFlat 11 then -3 else
  if row = rowOfFlat 12 then -3 else
  if row = rowOfFlat 14 then -1 else
  if row = rowOfFlat 15 then 3 else
  if row = rowOfFlat 17 then 1 else
  if row = rowOfFlat 19 then 1 else
  if row = rowOfFlat 20 then 3 else
  if row = rowOfFlat 21 then -3 else
  if row = rowOfFlat 22 then -3 else
  if row = rowOfFlat 24 then -1 else
  if row = rowOfFlat 25 then 3 else
  if row = rowOfFlat 27 then 1 else
  if row = rowOfFlat 29 then 1 else
  if row = rowOfFlat 30 then 3 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 32 then -2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 35 then 1 else
  if row = rowOfFlat 36 then 1 else
  if row = rowOfFlat 37 then 1 else
  if row = rowOfFlat 38 then 1 else
  if row = rowOfFlat 39 then 1 else
  if row = rowOfFlat 40 then 1 else
  0
def dual_58 (row : MomentRow) : ℚ := (dual4_58 row : ℚ) / 4

lemma cut_58_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 4 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 4) else 0) ≤
        ∑ row, dual_58 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_58, dual4_58, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_58_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_58 row * rhs p row) =
      (FiniteCertificates.cuts 58).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_58, dual4_58, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_58_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 58).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_58 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 4) (by norm_num) (by norm_num)
      coefficient dual_58 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_58_columnwise_kernel inner
  rw [cut_58_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 58).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_59 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 3 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 4 then -2 else
  if row = rowOfFlat 5 then 1 else
  if row = rowOfFlat 6 then 1 else
  if row = rowOfFlat 7 then 1 else
  if row = rowOfFlat 8 then 1 else
  if row = rowOfFlat 9 then 1 else
  if row = rowOfFlat 10 then 3 else
  if row = rowOfFlat 11 then -3 else
  if row = rowOfFlat 12 then -3 else
  if row = rowOfFlat 13 then -1 else
  if row = rowOfFlat 15 then 3 else
  if row = rowOfFlat 16 then 1 else
  if row = rowOfFlat 18 then 1 else
  if row = rowOfFlat 20 then 3 else
  if row = rowOfFlat 21 then -3 else
  if row = rowOfFlat 22 then -3 else
  if row = rowOfFlat 23 then -1 else
  if row = rowOfFlat 25 then 3 else
  if row = rowOfFlat 26 then 1 else
  if row = rowOfFlat 28 then 1 else
  if row = rowOfFlat 30 then 3 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 32 then -2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 35 then 1 else
  if row = rowOfFlat 36 then 1 else
  if row = rowOfFlat 37 then 1 else
  if row = rowOfFlat 38 then 1 else
  if row = rowOfFlat 39 then 1 else
  if row = rowOfFlat 40 then 1 else
  0
def dual_59 (row : MomentRow) : ℚ := (dual4_59 row : ℚ) / 4

lemma cut_59_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 4 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 4) else 0) ≤
        ∑ row, dual_59 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_59, dual4_59, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_59_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_59 row * rhs p row) =
      (FiniteCertificates.cuts 59).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_59, dual4_59, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_59_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 59).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_59 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 4) (by norm_num) (by norm_num)
      coefficient dual_59 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_59_columnwise_kernel inner
  rw [cut_59_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 59).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith


end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
