import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCutTable

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open PeaceableQueens.UpperBound.FiniteCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def dual4_40 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 4 then -2 else
  if row = rowOfFlat 5 then 2 else
  if row = rowOfFlat 7 then 2 else
  if row = rowOfFlat 9 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 15 then 2 else
  if row = rowOfFlat 20 then 6 else
  if row = rowOfFlat 21 then -4 else
  if row = rowOfFlat 22 then -4 else
  if row = rowOfFlat 23 then -4 else
  if row = rowOfFlat 24 then -4 else
  if row = rowOfFlat 25 then 2 else
  if row = rowOfFlat 26 then 2 else
  if row = rowOfFlat 27 then 2 else
  if row = rowOfFlat 28 then 2 else
  if row = rowOfFlat 29 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 37 then 2 else
  if row = rowOfFlat 38 then 2 else
  if row = rowOfFlat 41 then 2 else
  0
def dual_40 (row : MomentRow) : ℚ := (dual4_40 row : ℚ) / 4

lemma cut_40_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_40 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_40, dual4_40, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_40_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_40 row * rhs p row) =
      (FiniteCertificates.cuts 40).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_40, dual4_40, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_40_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 40).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_40 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_40 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_40_columnwise_kernel inner
  rw [cut_40_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 40).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_41 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 5 then 2 else
  if row = rowOfFlat 6 then 2 else
  if row = rowOfFlat 8 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 15 then 2 else
  if row = rowOfFlat 20 then 6 else
  if row = rowOfFlat 21 then -4 else
  if row = rowOfFlat 22 then -4 else
  if row = rowOfFlat 23 then -4 else
  if row = rowOfFlat 24 then -4 else
  if row = rowOfFlat 25 then 2 else
  if row = rowOfFlat 26 then 2 else
  if row = rowOfFlat 27 then 2 else
  if row = rowOfFlat 28 then 2 else
  if row = rowOfFlat 29 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 36 then 2 else
  if row = rowOfFlat 39 then 2 else
  if row = rowOfFlat 41 then 2 else
  0
def dual_41 (row : MomentRow) : ℚ := (dual4_41 row : ℚ) / 4

lemma cut_41_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_41 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_41, dual4_41, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_41_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_41 row * rhs p row) =
      (FiniteCertificates.cuts 41).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_41, dual4_41, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_41_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 41).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_41 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_41 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_41_columnwise_kernel inner
  rw [cut_41_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 41).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_42 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 4 then -2 else
  if row = rowOfFlat 7 then 2 else
  if row = rowOfFlat 8 then 2 else
  if row = rowOfFlat 10 then 6 else
  if row = rowOfFlat 11 then -4 else
  if row = rowOfFlat 12 then -4 else
  if row = rowOfFlat 13 then -4 else
  if row = rowOfFlat 14 then -4 else
  if row = rowOfFlat 15 then 2 else
  if row = rowOfFlat 16 then 2 else
  if row = rowOfFlat 17 then 2 else
  if row = rowOfFlat 18 then 2 else
  if row = rowOfFlat 19 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 24 then -2 else
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
def dual_42 (row : MomentRow) : ℚ := (dual4_42 row : ℚ) / 4

lemma cut_42_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_42 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_42, dual4_42, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_42_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_42 row * rhs p row) =
      (FiniteCertificates.cuts 42).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_42, dual4_42, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_42_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 42).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_42 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_42 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_42_columnwise_kernel inner
  rw [cut_42_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 42).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_43 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 6 then 2 else
  if row = rowOfFlat 9 then 2 else
  if row = rowOfFlat 10 then 6 else
  if row = rowOfFlat 11 then -4 else
  if row = rowOfFlat 12 then -4 else
  if row = rowOfFlat 13 then -4 else
  if row = rowOfFlat 14 then -4 else
  if row = rowOfFlat 15 then 2 else
  if row = rowOfFlat 16 then 2 else
  if row = rowOfFlat 17 then 2 else
  if row = rowOfFlat 18 then 2 else
  if row = rowOfFlat 19 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 24 then -2 else
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
def dual_43 (row : MomentRow) : ℚ := (dual4_43 row : ℚ) / 4

lemma cut_43_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_43 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_43, dual4_43, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_43_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_43 row * rhs p row) =
      (FiniteCertificates.cuts 43).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_43, dual4_43, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_43_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 43).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_43 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_43 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_43_columnwise_kernel inner
  rw [cut_43_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 43).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith


end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
