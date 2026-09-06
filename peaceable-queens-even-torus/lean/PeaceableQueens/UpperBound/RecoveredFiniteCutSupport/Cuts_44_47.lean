import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCutTable

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open PeaceableQueens.UpperBound.FiniteCertificates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0


def dual4_44 : MomentRow → Int := fun row =>
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
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 17 then 2 else
  if row = rowOfFlat 18 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 25 then 2 else
  if row = rowOfFlat 27 then 2 else
  if row = rowOfFlat 29 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 35 then 2 else
  if row = rowOfFlat 40 then 2 else
  0
def dual_44 (row : MomentRow) : ℚ := (dual4_44 row : ℚ) / 4

lemma cut_44_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_44 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_44, dual4_44, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_44_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_44 row * rhs p row) =
      (FiniteCertificates.cuts 44).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_44, dual4_44, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_44_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 44).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_44 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_44 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_44_columnwise_kernel inner
  rw [cut_44_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 44).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_45 : MomentRow → Int := fun row =>
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
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 16 then 2 else
  if row = rowOfFlat 19 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 25 then 2 else
  if row = rowOfFlat 26 then 2 else
  if row = rowOfFlat 28 then 2 else
  if row = rowOfFlat 30 then 2 else
  if row = rowOfFlat 33 then -2 else
  if row = rowOfFlat 34 then -2 else
  if row = rowOfFlat 35 then 2 else
  if row = rowOfFlat 40 then 2 else
  0
def dual_45 (row : MomentRow) : ℚ := (dual4_45 row : ℚ) / 4

lemma cut_45_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_45 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_45, dual4_45, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_45_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_45 row * rhs p row) =
      (FiniteCertificates.cuts 45).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_45, dual4_45, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_45_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 45).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_45 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_45 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_45_columnwise_kernel inner
  rw [cut_45_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 45).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_46 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 4 then -2 else
  if row = rowOfFlat 5 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 14 then -2 else
  if row = rowOfFlat 16 then 2 else
  if row = rowOfFlat 19 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 24 then -2 else
  if row = rowOfFlat 25 then 2 else
  if row = rowOfFlat 27 then 2 else
  if row = rowOfFlat 29 then 2 else
  if row = rowOfFlat 30 then 6 else
  if row = rowOfFlat 31 then -4 else
  if row = rowOfFlat 32 then -4 else
  if row = rowOfFlat 33 then -4 else
  if row = rowOfFlat 34 then -4 else
  if row = rowOfFlat 35 then 2 else
  if row = rowOfFlat 36 then 2 else
  if row = rowOfFlat 37 then 2 else
  if row = rowOfFlat 38 then 2 else
  if row = rowOfFlat 39 then 2 else
  if row = rowOfFlat 40 then 2 else
  0
def dual_46 (row : MomentRow) : ℚ := (dual4_46 row : ℚ) / 4

lemma cut_46_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_46 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_46, dual4_46, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_46_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_46 row * rhs p row) =
      (FiniteCertificates.cuts 46).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_46, dual4_46, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_46_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 46).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_46 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_46 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_46_columnwise_kernel inner
  rw [cut_46_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 46).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith

def dual4_47 : MomentRow → Int := fun row =>
  if row = rowOfFlat 0 then 2 else
  if row = rowOfFlat 3 then -2 else
  if row = rowOfFlat 4 then -2 else
  if row = rowOfFlat 5 then 2 else
  if row = rowOfFlat 10 then 2 else
  if row = rowOfFlat 12 then -2 else
  if row = rowOfFlat 13 then -2 else
  if row = rowOfFlat 17 then 2 else
  if row = rowOfFlat 18 then 2 else
  if row = rowOfFlat 20 then 2 else
  if row = rowOfFlat 21 then -2 else
  if row = rowOfFlat 22 then -2 else
  if row = rowOfFlat 23 then -2 else
  if row = rowOfFlat 25 then 2 else
  if row = rowOfFlat 26 then 2 else
  if row = rowOfFlat 28 then 2 else
  if row = rowOfFlat 30 then 6 else
  if row = rowOfFlat 31 then -4 else
  if row = rowOfFlat 32 then -4 else
  if row = rowOfFlat 33 then -4 else
  if row = rowOfFlat 34 then -4 else
  if row = rowOfFlat 35 then 2 else
  if row = rowOfFlat 36 then 2 else
  if row = rowOfFlat 37 then 2 else
  if row = rowOfFlat 38 then 2 else
  if row = rowOfFlat 39 then 2 else
  if row = rowOfFlat 40 then 2 else
  0
def dual_47 (row : MomentRow) : ℚ := (dual4_47 row : ℚ) / 4

lemma cut_47_columnwise_kernel : ∀ inner : InnerAtom,
    (if inner.atom = blackAtom then (1 : ℚ) / 2 else 0) +
      (if inner.atom = whiteAtom then (1 - (1 : ℚ) / 2) else 0) ≤
        ∑ row, dual_47 row * coefficient row inner := by
  intro inner
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  rcases inner with ⟨⟨rb, cb⟩, ⟨r, c, d, a⟩⟩
  fin_cases rb <;> fin_cases cb <;> fin_cases r <;> fin_cases c <;>
    fin_cases d <;> fin_cases a <;>
      simp [dual_47, dual4_47, coefficient, BlockMoment.eval, Block.squareParity,
        rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
        blackAtom, whiteAtom] <;> norm_num

lemma cut_47_rhs_normalized (p : OuterCoord → ℚ) :
    (∑ row, dual_47 row * rhs p row) =
      (FiniteCertificates.cuts 47).normalizedEval (fun j => p (outerOfFlat j)) / 12 := by
  rw [PeaceableQueens.UpperBound.SupportCuts.sum_rows_explicit]
  simp [dual_47, dual4_47, rowOfFlat, blockOfFlat, blockRow, blockCol, blockMomentOfFlat,
    rhs, rhsTerm, RhsTerm.eval,
    blockCoord, Block.squareParity, FiniteCertificates.cuts, FiniteLattice.Cut.normalizedEval,
    outerOfFlat, Fin.sum_univ_succ]
  ring

lemma cut_47_normalized_sound (cfg : Configuration q) (hq : 0 < q) :
    12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts 47).normalizedEval (flatProfile cfg) := by
  have h : min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
      ∑ row, dual_47 row * rhs (normalizedProfile cfg) row := by
    apply support_dual_sound_indicator ((1 : ℚ) / 2) (by norm_num) (by norm_num)
      coefficient dual_47 (configurationWeights cfg)
      (fun row => rhs (normalizedProfile cfg) row)
      (fun inner => inner.atom == blackAtom) (fun inner => inner.atom == whiteAtom)
    · exact configurationWeights_nonnegative cfg
    · exact configurationWeights_satisfiesMoments cfg hq
    · intro inner
      simpa using cut_47_columnwise_kernel inner
  rw [cut_47_rhs_normalized] at h
  change 12 * min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) ≤
    (FiniteCertificates.cuts 47).normalizedEval (fun j => normalizedProfile cfg (outerOfFlat j))
  nlinarith


end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
