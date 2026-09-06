import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCutTable

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open PeaceableQueens.UpperBound.FiniteCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def dual4_64 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 4 then -2 else
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
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 25 then 2 else
  if row = rowOfFlat 26 then 2 else
  if row = rowOfFlat 28 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 36 then 2 else
  if row = rowOfFlat 37 then 2 else
  if row = rowOfFlat 40 then 2 else
  0
def dual_64 (row : MomentRow) : ℚ := (dual4_64 row : ℚ) / 4

lemma cut_64_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_64 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_64, dual4_64, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_64_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_64 row * rhs p row) =
      (FiniteCertificates.cuts 64).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_64, dual4_64, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_64_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 64).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_64 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_64 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_64_columnwise_kernel inner
  rw [cut_64_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 64).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_65 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 4 then -2 else
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
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 25 then 2 else
  if row = rowOfFlat 27 then 2 else
  if row = rowOfFlat 29 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 36 then 2 else
  if row = rowOfFlat 37 then 2 else
  if row = rowOfFlat 40 then 2 else
  0
def dual_65 (row : MomentRow) : ℚ := (dual4_65 row : ℚ) / 4

lemma cut_65_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_65 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_65, dual4_65, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_65_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_65 row * rhs p row) =
      (FiniteCertificates.cuts 65).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_65, dual4_65, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_65_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 65).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_65 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_65 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_65_columnwise_kernel inner
  rw [cut_65_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 65).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_66 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 4 then -2 else
  if row = rowOfFlat 5 then 2 else
  if row = rowOfFlat 7 then 2 else
  if row = rowOfFlat 9 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 18 then 2 else
  if row = rowOfFlat 19 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 26 then 2 else
  if row = rowOfFlat 27 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 32 then -2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 35 then 2 else
  if row = rowOfFlat 36 then 2 else
  if row = rowOfFlat 38 then 2 else
  if row = rowOfFlat 41 then 2 else
  0
def dual_66 (row : MomentRow) : ℚ := (dual4_66 row : ℚ) / 4

lemma cut_66_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_66 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_66, dual4_66, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_66_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_66 row * rhs p row) =
      (FiniteCertificates.cuts 66).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_66, dual4_66, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_66_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 66).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_66 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_66 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_66_columnwise_kernel inner
  rw [cut_66_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 66).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_67 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 1 then -2 else
  if row = rowOfFlat 2 then -2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 5 then 2 else
  if row = rowOfFlat 6 then 2 else
  if row = rowOfFlat 8 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 18 then 2 else
  if row = rowOfFlat 19 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 26 then 2 else
  if row = rowOfFlat 27 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 31 then -2 else
  if row = rowOfFlat 32 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 35 then 2 else
  if row = rowOfFlat 37 then 2 else
  if row = rowOfFlat 39 then 2 else
  if row = rowOfFlat 41 then 2 else
  0
def dual_67 (row : MomentRow) : ℚ := (dual4_67 row : ℚ) / 4

lemma cut_67_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_67 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_67, dual4_67, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_67_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_67 row * rhs p row) =
      (FiniteCertificates.cuts 67).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_67, dual4_67, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_67_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 67).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_67 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_67 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_67_columnwise_kernel inner
  rw [cut_67_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 67).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith


end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
