import PeaceableQueens.UpperBound.SupportCuts
import PeaceableQueens.UpperBound.FiniteCertificateConsequences

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open FiniteCertificateConsequences
open PeaceableQueens.UpperBound.FiniteCertificates

theorem normalized_cut_to_count_scale
    (cut : FiniteLattice.Cut 8) (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q)
    (hnormal : 12 * min (blackTotal (configurationWeights cfg))
        (whiteTotal (configurationWeights cfg)) ≤ cut.normalizedEval (flatProfile cfg)) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      cut.eval q (countPoint cfg) := by
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hq2 : (0 : ℚ) < (q : ℚ) ^ 2 := sq_pos_of_pos hqQ
  rw [configurationWeights_blackTotal, configurationWeights_whiteTotal] at hnormal
  have hnormal' :
      (12 * min (cfg.blackCells.card : ℚ) (cfg.whiteCells.card : ℚ)) / (q : ℚ) ^ 2 ≤
        cut.normalizedEval (flatProfile cfg) := by
    calc
      (12 * min (cfg.blackCells.card : ℚ) (cfg.whiteCells.card : ℚ)) / (q : ℚ) ^ 2 =
          12 * (min (cfg.blackCells.card : ℚ) (cfg.whiteCells.card : ℚ) / (q : ℚ) ^ 2) := by ring
      _ = 12 * min ((cfg.blackCells.card : ℚ) / (q : ℚ) ^ 2)
          ((cfg.whiteCells.card : ℚ) / (q : ℚ) ^ 2) := by
            rw [min_div_div_right (sq_nonneg (q : ℚ))]
      _ ≤ cut.normalizedEval (flatProfile cfg) := hnormal
  have hscaled :
      12 * min (cfg.blackCells.card : ℚ) (cfg.whiteCells.card : ℚ) ≤
        (q : ℚ) ^ 2 * cut.normalizedEval (flatProfile cfg) :=
    by simpa [mul_comm] using (div_le_iff₀ hq2).mp hnormal'
  have hpoint : (fun i => (countPoint cfg i : ℚ) / (q : ℚ)) = flatProfile cfg := by
    funext i
    simp [countPoint, flatProfile, normalizedProfile]
  have heval := FiniteLattice.Cut.eval_eq_sq_mul_normalizedEval cut q (countPoint cfg)
    (ne_of_gt hqQ)
  rw [hpoint] at heval
  have hfinal :
      12 * min (cfg.blackCells.card : ℚ) (cfg.whiteCells.card : ℚ) ≤
        (cut.eval q (countPoint cfg) : ℚ) := by
    rw [heval]
    exact hscaled
  exact_mod_cast hfinal

theorem generated_cut_count_consequence (c : Fin 76) (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q)
    (hnormal : 12 * min (blackTotal (configurationWeights cfg))
        (whiteTotal (configurationWeights cfg)) ≤
      (FiniteCertificates.cuts c).normalizedEval (flatProfile cfg)) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts c).eval q (countPoint cfg) :=
  normalized_cut_to_count_scale (FiniteCertificates.cuts c) cfg hq hnormal

#print axioms normalized_cut_to_count_scale
#print axioms generated_cut_count_consequence

end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
