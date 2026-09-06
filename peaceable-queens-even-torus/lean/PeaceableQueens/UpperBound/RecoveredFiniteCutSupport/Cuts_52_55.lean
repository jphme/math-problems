import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCutTable

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open PeaceableQueens.UpperBound.FiniteCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def dual4_52 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 6 else
  if row = rowOfFlat 1 then -4 else
  if row = rowOfFlat 2 then -4 else
  if row = rowOfFlat 3 then -4 else
  if row = rowOfFlat 4 then -4 else
  if row = rowOfFlat 5 then 2 else
  if row = rowOfFlat 6 then 2 else
  if row = rowOfFlat 7 then 2 else
  if row = rowOfFlat 8 then 2 else
  if row = rowOfFlat 9 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 11 then -2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 15 then 2 else
  if row = rowOfFlat 17 then 2 else
  if row = rowOfFlat 19 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 26 then 2 else
  if row = rowOfFlat 29 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 35 then 2 else
  if row = rowOfFlat 40 then 2 else
  0
def dual_52 (row : MomentRow) : ℚ := (dual4_52 row : ℚ) / 4

lemma cut_52_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_52 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_52, dual4_52, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_52_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_52 row * rhs p row) =
      (FiniteCertificates.cuts 52).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_52, dual4_52, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_52_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 52).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_52 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_52 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_52_columnwise_kernel inner
  rw [cut_52_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 52).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_53 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 6 else
  if row = rowOfFlat 1 then -4 else
  if row = rowOfFlat 2 then -4 else
  if row = rowOfFlat 3 then -4 else
  if row = rowOfFlat 4 then -4 else
  if row = rowOfFlat 5 then 2 else
  if row = rowOfFlat 6 then 2 else
  if row = rowOfFlat 7 then 2 else
  if row = rowOfFlat 8 then 2 else
  if row = rowOfFlat 9 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 11 then -2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 15 then 2 else
  if row = rowOfFlat 16 then 2 else
  if row = rowOfFlat 18 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 27 then 2 else
  if row = rowOfFlat 28 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 35 then 2 else
  if row = rowOfFlat 40 then 2 else
  0
def dual_53 (row : MomentRow) : ℚ := (dual4_53 row : ℚ) / 4

lemma cut_53_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_53 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_53, dual4_53, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_53_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_53 row * rhs p row) =
      (FiniteCertificates.cuts 53).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_53, dual4_53, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_53_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 53).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_53 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_53 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_53_columnwise_kernel inner
  rw [cut_53_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 53).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_54 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 1 else
  if row = rowOfFlat 1 then -1 else
  if row = rowOfFlat 2 then -1 else
  if row = rowOfFlat 3 then -1 else
  if row = rowOfFlat 4 then -1 else
  if row = rowOfFlat 5 then 1 else
  if row = rowOfFlat 6 then 1 else
  if row = rowOfFlat 7 then 1 else
  if row = rowOfFlat 8 then 1 else
  if row = rowOfFlat 9 then 1 else
  if row = rowOfFlat 10 then 1 else
  if row = rowOfFlat 11 then -1 else
  if row = rowOfFlat 12 then -1 else
  if row = rowOfFlat 14 then -1 else
  if row = rowOfFlat 15 then 3 else
  if row = rowOfFlat 17 then 1 else
  if row = rowOfFlat 19 then 1 else
  if row = rowOfFlat 20 then 1 else
  if row = rowOfFlat 21 then -1 else
  if row = rowOfFlat 22 then -1 else
  if row = rowOfFlat 24 then -1 else
  if row = rowOfFlat 25 then 3 else
  if row = rowOfFlat 27 then 1 else
  if row = rowOfFlat 29 then 1 else
  if row = rowOfFlat 30 then 1 else
  if row = rowOfFlat 31 then -1 else
  if row = rowOfFlat 32 then -1 else
  if row = rowOfFlat 33 then -1 else
  if row = rowOfFlat 34 then -1 else
  if row = rowOfFlat 35 then 1 else
  if row = rowOfFlat 36 then 1 else
  if row = rowOfFlat 37 then 1 else
  if row = rowOfFlat 38 then 1 else
  if row = rowOfFlat 39 then 1 else
  if row = rowOfFlat 40 then 1 else
  0
def dual_54 (row : MomentRow) : ℚ := (dual4_54 row : ℚ) / 4

lemma cut_54_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (3 : ℚ) / 4 else 0) +
      (if inner.atom = whiteAtom then (1 - (3 : ℚ) / 4) else 0) ≤
        ∑ row, dual_54 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_54, dual4_54, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_54_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_54 row * rhs p row) =
      (FiniteCertificates.cuts 54).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_54, dual4_54, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_54_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 54).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_54 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((3 : ℚ) / 4) (by norm_num) (by norm_num)
      coefficient dual_54 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_54_columnwise_kernel inner
  rw [cut_54_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 54).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_55 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 1 else
  if row = rowOfFlat 1 then -1 else
  if row = rowOfFlat 2 then -1 else
  if row = rowOfFlat 3 then -1 else
  if row = rowOfFlat 4 then -1 else
  if row = rowOfFlat 5 then 1 else
  if row = rowOfFlat 6 then 1 else
  if row = rowOfFlat 7 then 1 else
  if row = rowOfFlat 8 then 1 else
  if row = rowOfFlat 9 then 1 else
  if row = rowOfFlat 10 then 1 else
  if row = rowOfFlat 11 then -1 else
  if row = rowOfFlat 12 then -1 else
  if row = rowOfFlat 13 then -1 else
  if row = rowOfFlat 15 then 3 else
  if row = rowOfFlat 16 then 1 else
  if row = rowOfFlat 18 then 1 else
  if row = rowOfFlat 20 then 1 else
  if row = rowOfFlat 21 then -1 else
  if row = rowOfFlat 22 then -1 else
  if row = rowOfFlat 23 then -1 else
  if row = rowOfFlat 25 then 3 else
  if row = rowOfFlat 26 then 1 else
  if row = rowOfFlat 28 then 1 else
  if row = rowOfFlat 30 then 1 else
  if row = rowOfFlat 31 then -1 else
  if row = rowOfFlat 32 then -1 else
  if row = rowOfFlat 33 then -1 else
  if row = rowOfFlat 34 then -1 else
  if row = rowOfFlat 35 then 1 else
  if row = rowOfFlat 36 then 1 else
  if row = rowOfFlat 37 then 1 else
  if row = rowOfFlat 38 then 1 else
  if row = rowOfFlat 39 then 1 else
  if row = rowOfFlat 40 then 1 else
  0
def dual_55 (row : MomentRow) : ℚ := (dual4_55 row : ℚ) / 4

lemma cut_55_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (3 : ℚ) / 4 else 0) +
      (if inner.atom = whiteAtom then (1 - (3 : ℚ) / 4) else 0) ≤
        ∑ row, dual_55 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_55, dual4_55, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_55_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_55 row * rhs p row) =
      (FiniteCertificates.cuts 55).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_55, dual4_55, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_55_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 55).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_55 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((3 : ℚ) / 4) (by norm_num) (by norm_num)
      coefficient dual_55 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_55_columnwise_kernel inner
  rw [cut_55_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 55).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith


end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
