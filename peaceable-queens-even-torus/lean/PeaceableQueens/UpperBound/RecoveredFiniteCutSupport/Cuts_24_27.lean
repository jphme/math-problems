import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCutTable

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open PeaceableQueens.UpperBound.FiniteCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def dual4_24 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 4 then -2 else
  if row = rowOfFlat 5 then 2 else
  if row = rowOfFlat 7 then 2 else
  if row = rowOfFlat 9 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 11 then -2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 15 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 25 then 2 else
  if row = rowOfFlat 26 then 2 else
  if row = rowOfFlat 27 then 2 else
  if row = rowOfFlat 28 then 2 else
  if row = rowOfFlat 29 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 32 then -2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 37 then 2 else
  if row = rowOfFlat 38 then 2 else
  if row = rowOfFlat 41 then 2 else
  0
def dual_24 (row : MomentRow) : ℚ := (dual4_24 row : ℚ) / 4

lemma cut_24_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_24 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_24, dual4_24, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_24_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_24 row * rhs p row) =
      (FiniteCertificates.cuts 24).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_24, dual4_24, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_24_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 24).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_24 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_24 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_24_columnwise_kernel inner
  rw [cut_24_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 24).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_25 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 5 then 2 else
  if row = rowOfFlat 6 then 2 else
  if row = rowOfFlat 8 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 11 then -2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 15 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 25 then 2 else
  if row = rowOfFlat 26 then 2 else
  if row = rowOfFlat 27 then 2 else
  if row = rowOfFlat 28 then 2 else
  if row = rowOfFlat 29 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 32 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 36 then 2 else
  if row = rowOfFlat 39 then 2 else
  if row = rowOfFlat 41 then 2 else
  0
def dual_25 (row : MomentRow) : ℚ := (dual4_25 row : ℚ) / 4

lemma cut_25_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_25 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_25, dual4_25, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_25_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_25 row * rhs p row) =
      (FiniteCertificates.cuts 25).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_25, dual4_25, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_25_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 25).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_25 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_25 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_25_columnwise_kernel inner
  rw [cut_25_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 25).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_26 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 7 then 2 else
  if row = rowOfFlat 8 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 11 then -2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 15 then 2 else
  if row = rowOfFlat 16 then 2 else
  if row = rowOfFlat 17 then 2 else
  if row = rowOfFlat 18 then 2 else
  if row = rowOfFlat 19 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 25 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 32 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 35 then 2 else
  if row = rowOfFlat 37 then 2 else
  if row = rowOfFlat 39 then 2 else
  if row = rowOfFlat 41 then 2 else
  0
def dual_26 (row : MomentRow) : ℚ := (dual4_26 row : ℚ) / 4

lemma cut_26_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_26 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_26, dual4_26, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_26_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_26 row * rhs p row) =
      (FiniteCertificates.cuts 26).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_26, dual4_26, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_26_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 26).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_26 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_26 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_26_columnwise_kernel inner
  rw [cut_26_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 26).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_27 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 4 then -2 else
  if row = rowOfFlat 6 then 2 else
  if row = rowOfFlat 9 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 11 then -2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 15 then 2 else
  if row = rowOfFlat 16 then 2 else
  if row = rowOfFlat 17 then 2 else
  if row = rowOfFlat 18 then 2 else
  if row = rowOfFlat 19 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 25 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 32 then -2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 35 then 2 else
  if row = rowOfFlat 36 then 2 else
  if row = rowOfFlat 38 then 2 else
  if row = rowOfFlat 41 then 2 else
  0
def dual_27 (row : MomentRow) : ℚ := (dual4_27 row : ℚ) / 4

lemma cut_27_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_27 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_27, dual4_27, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_27_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_27 row * rhs p row) =
      (FiniteCertificates.cuts 27).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_27, dual4_27, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_27_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 27).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_27 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_27 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_27_columnwise_kernel inner
  rw [cut_27_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 27).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith


end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
