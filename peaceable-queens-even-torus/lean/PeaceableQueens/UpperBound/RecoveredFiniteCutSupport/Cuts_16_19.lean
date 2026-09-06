import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCutTable

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open PeaceableQueens.UpperBound.FiniteCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def dual4_16 : MomentRow → Int := fun row =>
  if row = rowOfFlat 3 then 4 else
  if row = rowOfFlat 15 then 4 else
  if row = rowOfFlat 25 then 4 else
  if row = rowOfFlat 33 then 4 else
  0
def dual_16 (row : MomentRow) : ℚ := (dual4_16 row : ℚ) / 4

lemma cut_16_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 1) else 0) ≤
        ∑ row, dual_16 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_16, dual4_16, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_16_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_16 row * rhs p row) =
      (FiniteCertificates.cuts 16).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_16, dual4_16, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_16_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 16).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_16 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_16 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_16_columnwise_kernel inner
  rw [cut_16_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 16).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_17 : MomentRow → Int := fun row =>
  if row = rowOfFlat 4 then 4 else
  if row = rowOfFlat 15 then 4 else
  if row = rowOfFlat 25 then 4 else
  if row = rowOfFlat 34 then 4 else
  0
def dual_17 (row : MomentRow) : ℚ := (dual4_17 row : ℚ) / 4

lemma cut_17_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 1) else 0) ≤
        ∑ row, dual_17 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_17, dual4_17, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_17_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_17 row * rhs p row) =
      (FiniteCertificates.cuts 17).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_17, dual4_17, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_17_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 17).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_17 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_17 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_17_columnwise_kernel inner
  rw [cut_17_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 17).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_18 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 4 else
  if row = rowOfFlat 1 then -4 else
  if row = rowOfFlat 2 then -4 else
  if row = rowOfFlat 5 then 4 else
  if row = rowOfFlat 10 then 4 else
  if row = rowOfFlat 13 then -4 else
  if row = rowOfFlat 20 then 4 else
  if row = rowOfFlat 23 then -4 else
  if row = rowOfFlat 30 then 4 else
  if row = rowOfFlat 31 then -4 else
  if row = rowOfFlat 32 then -4 else
  if row = rowOfFlat 35 then 4 else
  0
def dual_18 (row : MomentRow) : ℚ := (dual4_18 row : ℚ) / 4

lemma cut_18_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (0 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (0 : ℚ) / 1) else 0) ≤
        ∑ row, dual_18 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_18, dual4_18, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_18_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_18 row * rhs p row) =
      (FiniteCertificates.cuts 18).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_18, dual4_18, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_18_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 18).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_18 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((0 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_18 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_18_columnwise_kernel inner
  rw [cut_18_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 18).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_19 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 4 else
  if row = rowOfFlat 1 then -4 else
  if row = rowOfFlat 2 then -4 else
  if row = rowOfFlat 5 then 4 else
  if row = rowOfFlat 10 then 4 else
  if row = rowOfFlat 14 then -4 else
  if row = rowOfFlat 20 then 4 else
  if row = rowOfFlat 24 then -4 else
  if row = rowOfFlat 30 then 4 else
  if row = rowOfFlat 31 then -4 else
  if row = rowOfFlat 32 then -4 else
  if row = rowOfFlat 35 then 4 else
  0
def dual_19 (row : MomentRow) : ℚ := (dual4_19 row : ℚ) / 4

lemma cut_19_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (0 : ℚ) / 1 else 0) +
      (if inner.atom = whiteAtom then (1 - (0 : ℚ) / 1) else 0) ≤
        ∑ row, dual_19 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_19, dual4_19, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_19_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_19 row * rhs p row) =
      (FiniteCertificates.cuts 19).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_19, dual4_19, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_19_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 19).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_19 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((0 : ℚ) / 1) (by norm_num) (by norm_num)
      coefficient dual_19 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_19_columnwise_kernel inner
  rw [cut_19_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 19).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith


end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
