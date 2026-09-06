import PeaceableQueens.Main
import PeaceableQueens.Values
import PeaceableQueens.UpperBound.Asymptotics

/-!
# Paper-facing consequences of the even theorem

This optional endpoint states paper `cor:asym` and `cor:values` explicitly.
The main theorem remains independent of the value table and topology imports.
The limit is along positive even board orders, indexed by their half-order `q`.
-/

namespace PeaceableQueens

open UpperBound Filter Asymptotics
open scoped Topology

/-- Paper `cor:asym`, with the exact constants and natural floor. -/
theorem even_bounds (q : ℕ) (hq : 0 < q) :
    kappa * (q : ℝ) ^ 2 - gamma * q - 1 / 4 ≤ (t (2 * q) : ℝ) ∧
      t (2 * q) ≤ ⌊kappa * (q : ℝ) ^ 2⌋₊ := by
  rw [evenTorusTheorem q hq]
  exact H_bounds q hq

theorem even_error_bound (q : ℕ) (hq : 0 < q) :
    ‖(t (2 * q) : ℝ) - kappa * (q : ℝ) ^ 2‖ ≤ (q : ℝ) := by
  rw [evenTorusTheorem q hq]
  exact H_error_bound q hq

/-- Paper `cor:asym`: the linear error along even board orders. -/
theorem even_asymptotic :
    (fun q : ℕ => (t (2 * q) : ℝ) - (2 - Real.sqrt 3) / 2 * (2 * (q : ℝ)) ^ 2)
      =O[atTop] (fun q : ℕ => 2 * (q : ℝ)) := by
  apply H_asymptotic.congr'
  · filter_upwards [eventually_ge_atTop 1] with q hq
    rw [evenTorusTheorem q (by omega)]
  · exact Eventually.of_forall fun _ => rfl

/-- Paper `cor:asym`: the even-subsequence density limit. -/
theorem even_density_limit :
    Tendsto (fun q : ℕ => (t (2 * q) : ℝ) / (2 * (q : ℝ)) ^ 2)
      atTop (𝓝 ((2 - Real.sqrt 3) / 2)) := by
  apply Filter.Tendsto.congr' ?_ H_density_limit
  filter_upwards [eventually_ge_atTop 1] with q hq
  rw [evenTorusTheorem q (by omega)]

theorem t_sixteen : t 16 = 32 := (evenTorusTheorem 8 (by decide)).trans H_eight
theorem t_eighteen : t 18 = 42 := (evenTorusTheorem 9 (by decide)).trans H_nine
theorem t_twenty : t 20 = 51 := (evenTorusTheorem 10 (by decide)).trans H_ten
theorem t_forty : t 40 = 210 := (evenTorusTheorem 20 (by decide)).trans H_twenty

#print axioms even_asymptotic
#print axioms even_density_limit

end PeaceableQueens
