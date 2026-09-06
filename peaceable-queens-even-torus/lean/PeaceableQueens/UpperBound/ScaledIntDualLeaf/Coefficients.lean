import PeaceableQueens.UpperBound.ScaledIntDualLeaf

namespace PeaceableQueens.UpperBound.ScaledIntDualLeaf

open LPModel DualLeaf

-- The exhaustive case proofs below intentionally carry a uniform simp/tactic
-- vocabulary across all 95 inequality and 42 equality rows.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

lemma coeffNum_div (b : Box) (hS : b.S ≠ 0) (r : IneqCoord) (v : VarCoord) :
    (coeffNum b r v : ℚ) / b.S = ineqCoeff b.profileLo b.profileHi r v := by
  have hSq : (b.S : ℚ) ≠ 0 := by exact_mod_cast hS
  by_cases h0 : r = 0
  · subst r
    by_cases hv : v < 8 <;>
      simp [coeffNum, ineqCoeff, Box.profileLo, Box.profileHi, hv, hSq]
  by_cases h1 : r = 1
  · subst r
    by_cases hv0 : v = 0 <;> by_cases hv1 : v = 1 <;>
      simp [coeffNum, ineqCoeff, Box.profileLo, Box.profileHi, hv0, hv1, hSq]
  by_cases h2 : r = 2
  · subst r
    by_cases hv2 : v = 2 <;> by_cases hv3 : v = 3 <;>
      simp [coeffNum, ineqCoeff, Box.profileLo, Box.profileHi, hv2, hv3, hSq]
  by_cases h3 : r = 3
  · subst r
    by_cases hv01 : v = 0 ∨ v = 1 <;> by_cases hv23 : v = 2 ∨ v = 3 <;>
      simp [coeffNum, ineqCoeff, Box.profileLo, Box.profileHi, hv01, hv23, hSq]
  by_cases h4 : r = 4
  · subst r
    by_cases hv45 : v = 4 ∨ v = 5 <;> by_cases hv67 : v = 6 ∨ v = 7 <;>
      simp [coeffNum, ineqCoeff, Box.profileLo, Box.profileHi, hv45, hv67, hSq]
  by_cases h5 : r = 5
  · subst r
    by_cases hvt : v = tVar <;>
      by_cases hvp : 30 ≤ v ∧ v < 94 <;>
      by_cases hva : localAtom (fin64 (v - 30)) = 15 <;>
      simp [coeffNum, ineqCoeff, Box.profileLo, Box.profileHi, hvt, hvp, hva, hSq]
  by_cases h6 : r = 6
  · subst r
    by_cases hvt : v = tVar <;>
      by_cases hvp : 30 ≤ v ∧ v < 94 <;>
      by_cases hva : localAtom (fin64 (v - 30)) = 0 <;>
      simp [coeffNum, ineqCoeff, Box.profileLo, Box.profileHi, hvt, hvp, hva, hSq]
  have hstep : (r - 7) % 4 = 0 ∨ (r - 7) % 4 = 1 ∨
      (r - 7) % 4 = 2 ∨ (r - 7) % 4 = 3 := by
    have hs : ((r - 7) % 4).val < 4 := by
      change (r - 7).val % 4 < 4
      exact Nat.mod_lt _ (by omega)
    have hs' : ((r - 7) % 4).val = 0 ∨ ((r - 7) % 4).val = 1 ∨
        ((r - 7) % 4).val = 2 ∨ ((r - 7) % 4).val = 3 := by omega
    rcases hs' with hs' | hs' | hs' | hs'
    · exact Or.inl (Fin.ext (by simpa using hs'))
    · exact Or.inr (Or.inl (Fin.ext (by simpa using hs')))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using hs'))))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext (by simpa using hs'))))
  rcases hstep with hs | hs | hs | hs <;>
    by_cases hvy : v = yVar (fin22 ((r - 7) / 4)) <;>
    by_cases hvi : v = xVar (productPair (fin22 ((r - 7) / 4))).1 <;>
    by_cases hvj : v = xVar (productPair (fin22 ((r - 7) / 4))).2 <;>
    by_cases hp : (productPair (fin22 ((r - 7) / 4))).2 =
      (productPair (fin22 ((r - 7) / 4))).1 <;>
    simp [coeffNum, ineqCoeff, Box.profileLo, Box.profileHi, h0, h1, h2, h3, h4, h5, h6,
      hs, hvy, hvi, hvj, hp, hSq] <;> ring

lemma rhsNum_div (b : Box) (hS : b.S ≠ 0) (r : IneqCoord) :
    (rhsNum b r : ℚ) / (b.S * b.S) = ineqRhs b.profileLo b.profileHi r := by
  have hSq : (b.S : ℚ) ≠ 0 := by exact_mod_cast hS
  by_cases h0 : r = 0
  · subst r
    simp [rhsNum, ineqRhs, Box.profileLo, Box.profileHi]
    field_simp
  by_cases hr : 7 ≤ r
  · have hstep : (r - 7) % 4 = 0 ∨ (r - 7) % 4 = 1 ∨
        (r - 7) % 4 = 2 ∨ (r - 7) % 4 = 3 := by
      have hs : ((r - 7) % 4).val < 4 := by
        change (r - 7).val % 4 < 4
        exact Nat.mod_lt _ (by omega)
      have hs' : ((r - 7) % 4).val = 0 ∨ ((r - 7) % 4).val = 1 ∨
          ((r - 7) % 4).val = 2 ∨ ((r - 7) % 4).val = 3 := by omega
      rcases hs' with hs' | hs' | hs' | hs'
      · exact Or.inl (Fin.ext (by simpa using hs'))
      · exact Or.inr (Or.inl (Fin.ext (by simpa using hs')))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext (by simpa using hs'))))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext (by simpa using hs'))))
    rcases hstep with hs | hs | hs | hs <;>
      simp [rhsNum, ineqRhs, Box.profileLo, Box.profileHi, h0, hr, hs, hSq] <;> field_simp
  · simp [rhsNum, ineqRhs, h0, hr]

lemma eqCoeffInt_cast (r : EqCoord) (v : VarCoord) :
    (eqCoeffInt r v : ℚ) = eqCoeff r v := by
  unfold eqCoeffInt eqCoeff momentCoeff
  all_goals first | split | skip
  all_goals try simp_all
  all_goals first | split | skip
  all_goals try simp_all
  all_goals first | split | skip
  all_goals try simp_all
  all_goals first | split | skip
  all_goals try simp_all
  all_goals first | split | skip
  all_goals try simp_all
  all_goals first | split | skip
  all_goals try simp_all

lemma eqRhsInt_cast (r : EqCoord) : (eqRhsInt r : ℚ) = eqRhs r := by
  unfold eqRhsInt eqRhs
  split <;> simp_all


#print axioms coeffNum_div
#print axioms rhsNum_div
#print axioms eqCoeffInt_cast
#print axioms eqRhsInt_cast

end PeaceableQueens.UpperBound.ScaledIntDualLeaf
