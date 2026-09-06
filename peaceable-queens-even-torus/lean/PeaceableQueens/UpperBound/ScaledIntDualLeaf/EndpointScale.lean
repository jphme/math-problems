import PeaceableQueens.UpperBound.ScaledIntDualLeaf.ResidualScaleFinal

namespace PeaceableQueens.UpperBound.ScaledIntDualLeaf
open LPModel DualLeaf
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma endpoint_x_scale (S r lo hi : Int) (hS : 0 < S) :
    ((neg r * (-lo) + pos r * hi : Int) : ℚ) / (S*S*S) =
      negativePart ((r : ℚ) / (S*S)) * (-(lo : ℚ) / S) +
      positivePart ((r : ℚ) / (S*S)) * ((hi : ℚ) / S) := by
  have hs : (S : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hS)
  have hs2 : (0:ℚ) < S*S := mul_pos (by exact_mod_cast hS) (by exact_mod_cast hS)
  by_cases hp : 0 ≤ r
  · have hpq : 0 ≤ (r:ℚ) / (S*S) := div_nonneg (by exact_mod_cast hp) (le_of_lt hs2)
    by_cases hn : r ≤ 0
    · have hr : r = 0 := le_antisymm hn hp
      subst r
      simp [pos, neg, positivePart, negativePart]
    · have hnq : ¬ (r:ℚ) / (S*S) ≤ 0 := by
        intro h
        have : (r:ℚ) ≤ 0 := by linarith [(div_le_iff₀ hs2).mp h]
        have : r ≤ 0 := by exact_mod_cast this
        exact hn this
      simp [pos, neg, hp, hn, positivePart, negativePart, hpq, hnq]
      field_simp
  · have hn : r ≤ 0 := le_of_not_ge hp
    have hnq : (r:ℚ) / (S*S) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (by exact_mod_cast hn) (le_of_lt hs2)
    have hpq : ¬ 0 ≤ (r:ℚ) / (S*S) := by
      intro h
      have : (0:ℚ) ≤ r := by linarith [(le_div_iff₀ hs2).mp h]
      exact hp (by exact_mod_cast this)
    simp [pos, neg, hp, hn, positivePart, negativePart, hnq, hpq]
    field_simp

lemma endpoint_y_scale (S r lo hi : Int) (hS : 0 < S) :
    ((neg r * (-lo) + pos r * hi : Int) : ℚ) / (S*S*S) =
      negativePart ((r : ℚ) / S) * (-(lo : ℚ) / (S*S)) +
      positivePart ((r : ℚ) / S) * ((hi : ℚ) / (S*S)) := by
  have hs : (S : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hS)
  have hs2 : (0:ℚ) < S*S := mul_pos (by exact_mod_cast hS) (by exact_mod_cast hS)
  by_cases hp : 0 ≤ r
  · have hpq : 0 ≤ (r:ℚ) / S := div_nonneg (by exact_mod_cast hp) (le_of_lt (by exact_mod_cast hS))
    by_cases hn : r ≤ 0
    · have hr : r = 0 := le_antisymm hn hp
      subst r
      simp [pos, neg, positivePart, negativePart]
    · have hnq : ¬ (r:ℚ) / S ≤ 0 := by
        intro h
        have hs' : (0:ℚ) < S := by exact_mod_cast hS
        have : (r:ℚ) ≤ 0 := by linarith [(div_le_iff₀ hs').mp h]
        have : r ≤ 0 := by exact_mod_cast this
        exact hn this
      simp [pos, neg, hp, hn, positivePart, negativePart, hpq, hnq]
      field_simp
  · have hn : r ≤ 0 := le_of_not_ge hp
    have hnq : (r:ℚ) / S ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (by exact_mod_cast hn) (le_of_lt (by exact_mod_cast hS))
    have hs' : (0:ℚ) < S := by exact_mod_cast hS
    have hpq : ¬ 0 ≤ (r:ℚ) / S := by
      intro h
      have : (0:ℚ) ≤ r := by linarith [(le_div_iff₀ hs').mp h]
      exact hp (by exact_mod_cast this)
    simp [pos, neg, hp, hn, positivePart, negativePart, hnq, hpq]
    field_simp

end PeaceableQueens.UpperBound.ScaledIntDualLeaf
