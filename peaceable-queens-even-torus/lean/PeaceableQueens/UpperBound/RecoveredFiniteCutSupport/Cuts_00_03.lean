import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCutTable

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open PeaceableQueens.UpperBound.FiniteCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def dual4_0 : MomentRow → Int := fun row =>
  if row = rowOfFlat 5 then 4 else
  if row = rowOfFlat 15 then 4 else
  if row = rowOfFlat 25 then 4 else
  if row = rowOfFlat 35 then 4 else
  0
def dual_0 (row : MomentRow) : ℚ := (dual4_0 row : ℚ) / 4

lemma cut_0_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 1) else 0) ≤
        ∑ row, dual_0 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_0, dual4_0, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_0_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_0 row * rhs p row) =
      (FiniteCertificates.cuts 0).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_0, dual4_0, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_0_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 0).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_0 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_0 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_0_columnwise_kernel inner
  rw [cut_0_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 0).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_1 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 4 else
  if row = rowOfFlat 1 then -4 else
  if row = rowOfFlat 2 then -4 else
  if row = rowOfFlat 5 then 4 else
  if row = rowOfFlat 10 then 4 else
  if row = rowOfFlat 11 then -4 else
  if row = rowOfFlat 12 then -4 else
  if row = rowOfFlat 15 then 4 else
  if row = rowOfFlat 20 then 4 else
  if row = rowOfFlat 21 then -4 else
  if row = rowOfFlat 22 then -4 else
  if row = rowOfFlat 25 then 4 else
  if row = rowOfFlat 30 then 4 else
  if row = rowOfFlat 31 then -4 else
  if row = rowOfFlat 32 then -4 else
  if row = rowOfFlat 35 then 4 else
  0
def dual_1 (row : MomentRow) : ℚ := (dual4_1 row : ℚ) / 4

lemma cut_1_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (0 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (0 : ℚ) / 1) else 0) ≤
        ∑ row, dual_1 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_1, dual4_1, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_1_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_1 row * rhs p row) =
      (FiniteCertificates.cuts 1).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_1, dual4_1, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_1_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 1).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_1 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((0 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_1 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_1_columnwise_kernel inner
  rw [cut_1_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 1).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_2 : MomentRow → Int := fun row =>
  if row = rowOfFlat 6 then 4 else
  if row = rowOfFlat 16 then 4 else
  if row = rowOfFlat 26 then 4 else
  if row = rowOfFlat 36 then 4 else
  0
def dual_2 (row : MomentRow) : ℚ := (dual4_2 row : ℚ) / 4

lemma cut_2_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 1) else 0) ≤
        ∑ row, dual_2 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_2, dual4_2, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_2_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_2 row * rhs p row) =
      (FiniteCertificates.cuts 2).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_2, dual4_2, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_2_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 2).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_2 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_2 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_2_columnwise_kernel inner
  rw [cut_2_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 2).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_3 : MomentRow → Int := fun row =>
  if row = rowOfFlat 7 then 4 else
  if row = rowOfFlat 17 then 4 else
  if row = rowOfFlat 27 then 4 else
  if row = rowOfFlat 37 then 4 else
  0
def dual_3 (row : MomentRow) : ℚ := (dual4_3 row : ℚ) / 4

lemma cut_3_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 1) else 0) ≤
        ∑ row, dual_3 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_3, dual4_3, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_3_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_3 row * rhs p row) =
      (FiniteCertificates.cuts 3).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_3, dual4_3, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_3_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 3).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_3 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_3 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_3_columnwise_kernel inner
  rw [cut_3_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 3).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith


end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
