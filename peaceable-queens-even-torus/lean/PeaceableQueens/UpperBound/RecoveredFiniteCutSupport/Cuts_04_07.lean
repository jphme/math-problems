import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCutTable

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open PeaceableQueens.UpperBound.FiniteCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def dual4_4 : MomentRow → Int := fun row =>
  if row = rowOfFlat 8 then 4 else
  if row = rowOfFlat 18 then 4 else
  if row = rowOfFlat 28 then 4 else
  if row = rowOfFlat 38 then 4 else
  0
def dual_4 (row : MomentRow) : ℚ := (dual4_4 row : ℚ) / 4

lemma cut_4_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 1) else 0) ≤
        ∑ row, dual_4 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_4, dual4_4, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_4_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_4 row * rhs p row) =
      (FiniteCertificates.cuts 4).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_4, dual4_4, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_4_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 4).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_4 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_4 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_4_columnwise_kernel inner
  rw [cut_4_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 4).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_5 : MomentRow → Int := fun row =>
  if row = rowOfFlat 9 then 4 else
  if row = rowOfFlat 19 then 4 else
  if row = rowOfFlat 29 then 4 else
  if row = rowOfFlat 39 then 4 else
  0
def dual_5 (row : MomentRow) : ℚ := (dual4_5 row : ℚ) / 4

lemma cut_5_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 1) else 0) ≤
        ∑ row, dual_5 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_5, dual4_5, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_5_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_5 row * rhs p row) =
      (FiniteCertificates.cuts 5).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_5, dual4_5, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_5_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 5).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_5 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_5 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_5_columnwise_kernel inner
  rw [cut_5_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 5).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_6 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 4 else
  if row = rowOfFlat 1 then -4 else
  if row = rowOfFlat 3 then -4 else
  if row = rowOfFlat 6 then 4 else
  if row = rowOfFlat 10 then 4 else
  if row = rowOfFlat 11 then -4 else
  if row = rowOfFlat 13 then -4 else
  if row = rowOfFlat 16 then 4 else
  if row = rowOfFlat 20 then 4 else
  if row = rowOfFlat 21 then -4 else
  if row = rowOfFlat 23 then -4 else
  if row = rowOfFlat 26 then 4 else
  if row = rowOfFlat 30 then 4 else
  if row = rowOfFlat 31 then -4 else
  if row = rowOfFlat 33 then -4 else
  if row = rowOfFlat 36 then 4 else
  0
def dual_6 (row : MomentRow) : ℚ := (dual4_6 row : ℚ) / 4

lemma cut_6_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (0 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (0 : ℚ) / 1) else 0) ≤
        ∑ row, dual_6 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_6, dual4_6, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_6_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_6 row * rhs p row) =
      (FiniteCertificates.cuts 6).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_6, dual4_6, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_6_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 6).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_6 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((0 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_6 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_6_columnwise_kernel inner
  rw [cut_6_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 6).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_7 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 4 else
  if row = rowOfFlat 1 then -4 else
  if row = rowOfFlat 4 then -4 else
  if row = rowOfFlat 7 then 4 else
  if row = rowOfFlat 10 then 4 else
  if row = rowOfFlat 11 then -4 else
  if row = rowOfFlat 14 then -4 else
  if row = rowOfFlat 17 then 4 else
  if row = rowOfFlat 20 then 4 else
  if row = rowOfFlat 21 then -4 else
  if row = rowOfFlat 24 then -4 else
  if row = rowOfFlat 27 then 4 else
  if row = rowOfFlat 30 then 4 else
  if row = rowOfFlat 31 then -4 else
  if row = rowOfFlat 34 then -4 else
  if row = rowOfFlat 37 then 4 else
  0
def dual_7 (row : MomentRow) : ℚ := (dual4_7 row : ℚ) / 4

lemma cut_7_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (0 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (0 : ℚ) / 1) else 0) ≤
        ∑ row, dual_7 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_7, dual4_7, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_7_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_7 row * rhs p row) =
      (FiniteCertificates.cuts 7).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_7, dual4_7, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_7_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 7).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_7 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((0 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_7 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_7_columnwise_kernel inner
  rw [cut_7_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 7).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith


end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
