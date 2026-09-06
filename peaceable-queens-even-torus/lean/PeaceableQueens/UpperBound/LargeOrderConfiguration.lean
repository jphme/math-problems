import PeaceableQueens.UpperBound.LargeOrderAlgebra
import PeaceableQueens.UpperBound.LeafChecks

namespace PeaceableQueens.UpperBound.LargeOrderConfiguration

open ConfigurationBridge LeafChecks LargeOrderAlgebra MomentModel

def localOfConfiguration (cfg : Configuration q) : Local :=
  { q := q
    u := outerCount cfg ⟨.row, 0⟩
    R := outerCount cfg ⟨.row, 1⟩
    v := outerCount cfg ⟨.column, 0⟩
    C := outerCount cfg ⟨.column, 1⟩
    e := outerCount cfg ⟨.diagonal, 1⟩
    f := outerCount cfg ⟨.antidiagonal, 1⟩
    g := q - outerCount cfg ⟨.diagonal, 0⟩
    h := q - outerCount cfg ⟨.antidiagonal, 0⟩ }

theorem localOfConfiguration_nonnegative (cfg : Configuration q) (hq : 0 < q) :
    (localOfConfiguration cfg).Nonnegative := by
  have hr0 := outerCount_le cfg hq (⟨.row, 0⟩ : OuterCoord)
  have hr1 := outerCount_le cfg hq (⟨.row, 1⟩ : OuterCoord)
  have hc0 := outerCount_le cfg hq (⟨.column, 0⟩ : OuterCoord)
  have hc1 := outerCount_le cfg hq (⟨.column, 1⟩ : OuterCoord)
  have hd0 := outerCount_le cfg hq (⟨.diagonal, 0⟩ : OuterCoord)
  have hd1 := outerCount_le cfg hq (⟨.diagonal, 1⟩ : OuterCoord)
  have ha0 := outerCount_le cfg hq (⟨.antidiagonal, 0⟩ : OuterCoord)
  have ha1 := outerCount_le cfg hq (⟨.antidiagonal, 1⟩ : OuterCoord)
  unfold LargeOrderAlgebra.Local.Nonnegative localOfConfiguration
  norm_num
  constructor <;> exact_mod_cast (by assumption)

theorem localOfConfiguration_core (cfg : Configuration q) (hq : 0 < q)
    (hcore : InCore (flatProfile cfg)) :
    (localOfConfiguration cfg).Core := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  rcases hcore with ⟨hslo, hshi, hm, hd, hz⟩
  norm_num [flatProfile, outerOfFlat, normalizedProfile_eq_div] at hslo hshi hm hd hz
  unfold LargeOrderAlgebra.Local.Core LargeOrderAlgebra.Local.sigma
    LargeOrderAlgebra.Local.m LargeOrderAlgebra.Local.delta LargeOrderAlgebra.Local.zeta
    localOfConfiguration
  simp only
  norm_num at ⊢
  constructor
  · field_simp at hslo
    linarith
  constructor
  · field_simp at hshi
    linarith
  constructor
  · field_simp at hm
    linarith
  constructor
  · field_simp at hd
    linarith
  · field_simp at hz
    linarith

#print axioms localOfConfiguration_nonnegative
#print axioms localOfConfiguration_core

end PeaceableQueens.UpperBound.LargeOrderConfiguration
