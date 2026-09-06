import PeaceableQueens.LineColouring
import PeaceableQueens.UpperBound.LargeOrderFinish

/-!
# Configuration-level consequences of the two branch certificates

This file isolates the algebraic S38 and final line-colouring reductions from
the generated certificate data.  The eventual checked trees only need to
supply the two stated safe-or-exceptional disjunctions.
-/

namespace PeaceableQueens.UpperBound.CertificateConsequences

open ConfigurationBridge ConfigurationMoments LeafChecks MomentModel
open LargeOrderFinish

/-- The natural canonical chamber transports to the rational predicate used
by exact empty-leaf checks. -/
lemma chamber_flatProfile (cfg : Configuration n) (hq : 0 < n)
    (h : chamber n cfg) : InChamber (flatProfile cfg) := by
  rcases h with ⟨hr, hc, hrc, hda, hbudget⟩
  have hqQ : (0 : ℚ) < n := by exact_mod_cast hq
  have htot :
      outerCount cfg ⟨.row, 0⟩ + outerCount cfg ⟨.row, 1⟩ +
      outerCount cfg ⟨.column, 0⟩ + outerCount cfg ⟨.column, 1⟩ +
      outerCount cfg ⟨.diagonal, 0⟩ + outerCount cfg ⟨.diagonal, 1⟩ +
      outerCount cfg ⟨.antidiagonal, 0⟩ + outerCount cfg ⟨.antidiagonal, 1⟩ ≤ 4 * n := by
    have hrp := outerCount_pair_sum cfg .row
    have hcp := outerCount_pair_sum cfg .column
    have hdp := outerCount_pair_sum cfg .diagonal
    have hap := outerCount_pair_sum cfg .antidiagonal
    simp at hrp hcp hdp hap
    unfold totalLineCount at hbudget
    omega
  norm_num [InChamber, flatProfile, outerOfFlat, normalizedProfile_eq_div]
  constructor
  · apply (div_le_div_iff_of_pos_right hqQ).mpr
    exact_mod_cast hr
  constructor
  · apply (div_le_div_iff_of_pos_right hqQ).mpr
    exact_mod_cast hc
  constructor
  · field_simp
    exact_mod_cast hrc
  constructor
  · field_simp
    exact_mod_cast hda
  · field_simp
    have htotQ :
        (outerCount cfg ⟨.row, 0⟩ : ℚ) + outerCount cfg ⟨.row, 1⟩ +
        outerCount cfg ⟨.column, 0⟩ + outerCount cfg ⟨.column, 1⟩ +
        outerCount cfg ⟨.diagonal, 0⟩ + outerCount cfg ⟨.diagonal, 1⟩ +
        outerCount cfg ⟨.antidiagonal, 0⟩ + outerCount cfg ⟨.antidiagonal, 1⟩ ≤ 4 * n := by
      exact_mod_cast htot
    linarith

/-- The only plaid template surviving in the global certificate is exactly
the integer neighbourhood consumed by the S42--S54 finish. -/
lemma plaid01_neighborhood (cfg : Configuration n) (hq : 0 < n)
    (h : InPlaid (0 : Fin 2) (1 : Fin 2) (flatProfile cfg)) :
    InLargeOrderNeighborhood cfg := by
  have hr0 := h (0 : Fin 8)
  have hr1 := h (1 : Fin 8)
  have hc0 := h (2 : Fin 8)
  have hc1 := h (3 : Fin 8)
  have hd1 := h (5 : Fin 8)
  have ha1 := h (7 : Fin 8)
  norm_num [InPlaid, templateValue, flatProfile, outerOfFlat,
    normalizedProfile_eq_div] at hr0 hr1 hc0 hc1 hd1 ha1
  constructor
  · have : (10 : ℚ) * outerCount cfg ⟨.row, 0⟩ ≤ n := by
      field_simp at hr0
      linarith
    exact_mod_cast this
  constructor
  · have : (10 : ℚ) * outerCount cfg ⟨.column, 0⟩ ≤ n := by
      field_simp at hc0
      linarith
    exact_mod_cast this
  constructor
  · have : (10 : ℚ) * outerCount cfg ⟨.diagonal, 1⟩ ≤ n := by
      field_simp at hd1
      linarith
    exact_mod_cast this
  constructor
  · have : (10 : ℚ) * outerCount cfg ⟨.antidiagonal, 1⟩ ≤ n := by
      field_simp at ha1
      linarith
    exact_mod_cast this
  constructor
  · have : (3 : ℚ) * n ≤ 5 * outerCount cfg ⟨.row, 1⟩ := by
      field_simp at hr1
      linarith
    exact_mod_cast this
  constructor
  · have : (8 : ℚ) * outerCount cfg ⟨.row, 1⟩ ≤ 7 * n := by
      field_simp at hr1
      linarith
    exact_mod_cast this
  constructor
  · have : (3 : ℚ) * n ≤ 5 * outerCount cfg ⟨.column, 1⟩ := by
      field_simp at hc1
      linarith
    exact_mod_cast this
  · have : (8 : ℚ) * outerCount cfg ⟨.column, 1⟩ ≤ 7 * n := by
      field_simp at hc1
      linarith
    exact_mod_cast this

lemma configurationLP_t_eq_scaled_cards (cfg : Configuration n) [NeZero (2 * n)] :
    configurationLPVector cfg LPModel.tVar =
      (min cfg.blackCells.card cfg.whiteCells.card : ℚ) / (n : ℚ) ^ 2 := by
  rw [configurationLPVector_t, configurationWeights_blackTotal,
    configurationWeights_whiteTotal]
  have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
  rw [min_div_div_right hn2]

/-! ## Semantic interface for the generated branch trees -/

/-- A terminal rational box is safe when it either carries the checked
McCormick upper bound or is provably disjoint from the canonical chamber. -/
def BranchSafe (box : RatBox 8) : Prop :=
  ((∀ i, 0 ≤ box.lower i ∧ 0 ≤ box.upper i) ∧
    ∀ z : LPModel.LPVector, DualLeaf.LeafFeasible box.lower box.upper z →
      z LPModel.tVar ≤ (527 : ℚ) / 1000) ∨
    (∀ x, box.Contains x → InChamber x → False)

/-- A global exceptional box lies wholly in the one plaid neighbourhood that
survives the chamber normalization. -/
def PlaidExceptional (box : RatBox 8) : Prop :=
  ∀ x, box.Contains x → InPlaid (0 : Fin 2) (1 : Fin 2) x

/-- A local exceptional box lies wholly in the aggregate core. -/
def CoreExceptional (box : RatBox 8) : Prop :=
  ∀ x, box.Contains x → InCore x

/-- Exact root box of the released global certificate. -/
def globalRoot : RatBox 8 :=
  { lower := ![0, 0, 0, 0, 0, 0, 0, 0]
    upper := ![1, 1, 1, 1, 1, 1, 1, 1] }

/-- Exact root box of the released local certificate.  This is precisely the
`(squareParity,rowParity) = (0,1)` plaid neighbourhood. -/
def localRoot : RatBox 8 :=
  { lower := ![0, 3 / 5, 0, 3 / 5, 19 / 20, 0, 19 / 20, 0]
    upper := ![1 / 10, 7 / 8, 1 / 10, 7 / 8, 1, 1 / 10, 1, 1 / 10] }

lemma flatProfile_mem_globalRoot (cfg : Configuration n) (hq : 0 < n) :
    globalRoot.Contains (flatProfile cfg) := by
  intro i
  have h := normalizedProfile_range cfg hq (outerOfFlat i)
  fin_cases i <;> simpa [globalRoot, flatProfile] using h

lemma plaid01_mem_localRoot {x : RatVec 8}
    (hunit : globalRoot.Contains x)
    (h : InPlaid (0 : Fin 2) (1 : Fin 2) x) :
    localRoot.Contains x := by
  intro i
  have hi := h i
  have hxi := hunit i
  fin_cases i <;>
    norm_num [InPlaid, templateValue, globalRoot, localRoot] at hi hxi ⊢ <;>
    constructor <;> linarith

/-- Certificate-independent semantic consequence of a checked branch tree.
The generated modules only have to construct the `CoverTree` and establish
root containment; all use of configuration feasibility happens here. -/
lemma branch_tree_consequence {Exceptional : RatBox 8 → Prop}
    {root : RatBox 8}
    (tree : CoverTree BranchSafe Exceptional root)
    (cfg : Configuration n) [NeZero (2 * n)] (hq : 0 < n)
    (hchamber : chamber n cfg) (hroot : root.Contains (flatProfile cfg)) :
    configurationLPVector cfg LPModel.tVar ≤ (527 : ℚ) / 1000 ∨
      ∃ leaf, leaf.Contains (flatProfile cfg) ∧ Exceptional leaf := by
  rcases tree.locate (flatProfile cfg) hroot with
    ⟨leaf, hleaf, hsafe | hexceptional⟩
  · rcases hsafe with ⟨hnonnegative, hdual⟩ | hempty
    · left
      apply hdual (configurationLPVector cfg)
      exact configurationLPVector_leafFeasible cfg hq hchamber
        leaf.lower leaf.upper hleaf
        (fun i => (hnonnegative i).1) (fun i => (hnonnegative i).2)
    · exact False.elim (hempty (flatProfile cfg) hleaf
        (chamber_flatProfile cfg hq hchamber))
  · exact Or.inr ⟨leaf, hleaf, hexceptional⟩

/-- Paper `thm:cert1` (S36) in configuration form: a checked global tree either
bounds the configuration's own LP objective by `527/1000` or places its
profile in the plaid neighbourhood `N`. -/
lemma global_tree_consequence {root : RatBox 8}
    (tree : CoverTree BranchSafe PlaidExceptional root)
    (cfg : Configuration n) [NeZero (2 * n)] (hq : 0 < n)
    (hchamber : chamber n cfg) (hroot : root.Contains (flatProfile cfg)) :
    configurationLPVector cfg LPModel.tVar ≤ (527 : ℚ) / 1000 ∨
      InPlaid (0 : Fin 2) (1 : Fin 2) (flatProfile cfg) := by
  rcases branch_tree_consequence tree cfg hq hchamber hroot with hsmall | hlocal
  · exact Or.inl hsmall
  · rcases hlocal with ⟨leaf, hleaf, hexceptional⟩
    exact Or.inr (hexceptional (flatProfile cfg) hleaf)

/-- Paper `thm:cert2` (S37) in configuration form: a checked local tree either
bounds the configuration's own LP objective by `527/1000` or places its
profile in the aggregate core `eq:core`. -/
lemma local_tree_consequence {root : RatBox 8}
    (tree : CoverTree BranchSafe CoreExceptional root)
    (cfg : Configuration n) [NeZero (2 * n)] (hq : 0 < n)
    (hchamber : chamber n cfg) (hroot : root.Contains (flatProfile cfg)) :
    configurationLPVector cfg LPModel.tVar ≤ (527 : ℚ) / 1000 ∨
      InCore (flatProfile cfg) := by
  rcases branch_tree_consequence tree cfg hq hchamber hroot with hsmall | hlocal
  · exact Or.inl hsmall
  · rcases hlocal with ⟨leaf, hleaf, hexceptional⟩
    exact Or.inr (hexceptional (flatProfile cfg) hleaf)

/-- Paper `lem:escape` (S20) makes a certificate leaf at threshold `527/1000`
incompatible with a configuration whose actual objective is at least `H n`. -/
lemma threshold_contradicts_H (cfg : Configuration n) [NeZero (2 * n)]
    (hq : 64 ≤ n) (hlarge : H n ≤ min cfg.blackCells.card cfg.whiteCells.card)
    (hsmall : configurationLPVector cfg LPModel.tVar ≤ (527 : ℚ) / 1000) : False := by
  have hnpos : 0 < n := by omega
  rw [configurationLP_t_eq_scaled_cards cfg] at hsmall
  have hn2Q : (0 : ℚ) < (n : ℚ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hnpos)
  have hcardsQ : (min cfg.blackCells.card cfg.whiteCells.card : ℚ) ≤
      (527 : ℚ) / 1000 * (n : ℚ) ^ 2 := by
    have := (div_le_iff₀ hn2Q).mp hsmall
    nlinarith
  let m : ℕ := min cfg.blackCells.card cfg.whiteCells.card
  have hcardsQ' : (m : ℚ) ≤ (527 : ℚ) / 1000 * (n : ℚ) ^ 2 := by
    simpa [m] using hcardsQ
  have hcardsR' : (m : ℝ) ≤ (527 : ℝ) / 1000 * (n : ℝ) ^ 2 := by
    have hc : ((m : ℚ) : ℝ) ≤
        (((527 : ℚ) / 1000 * (n : ℚ) ^ 2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hcardsQ'
    norm_num at hc ⊢
    simpa using hc
  have hcardsR : ((min cfg.blackCells.card cfg.whiteCells.card : ℕ) : ℝ) ≤
      (527 : ℝ) / 1000 * (n : ℝ) ^ 2 := by simpa [m] using hcardsR'
  have hescape := H_escape_s20 n hq
  have hlargeR : (H n : ℝ) ≤
      ((min cfg.blackCells.card cfg.whiteCells.card : ℕ) : ℝ) := by
    exact_mod_cast hlarge
  nlinarith

/-- Paper `cor:escape` (S38) from the two checked-tree conclusions, with
certificate data kept out of this algebraic theorem. -/
lemma configuration_escape_of_certificates (cfg : Configuration n) [NeZero (2 * n)]
    (hq : 64 ≤ n) (hlarge : H n ≤ min cfg.blackCells.card cfg.whiteCells.card)
    (hglobal : configurationLPVector cfg LPModel.tVar ≤ (527 : ℚ) / 1000 ∨
      InPlaid (0 : Fin 2) (1 : Fin 2) (flatProfile cfg))
    (hlocal : InPlaid (0 : Fin 2) (1 : Fin 2) (flatProfile cfg) →
      configurationLPVector cfg LPModel.tVar ≤ (527 : ℚ) / 1000 ∨
        InCore (flatProfile cfg)) :
    InLargeOrderNeighborhood cfg ∧ InCore (flatProfile cfg) := by
  have hnpos : 0 < n := by omega
  rcases hglobal with hsmall | hplaid
  · exact False.elim (threshold_contradicts_H cfg hq hlarge hsmall)
  · constructor
    · exact plaid01_neighborhood cfg hnpos hplaid
    · rcases hlocal hplaid with hsmall | hcore
      · exact False.elim (threshold_contradicts_H cfg hq hlarge hsmall)
      · exact hcore

/-- It is enough to bound configurations in the canonical chamber: the line
colouring equivalence (paper `lem:lines`) and the chamber normalization
(paper `lem:chamber`, S29) transfer that bound to `t`. -/
lemma t_le_H_of_chamber_configuration (q : ℕ) [NeZero (2 * q)]
    (hbound : ∀ cfg : Configuration q, chamber q cfg →
      min cfg.blackCells.card cfg.whiteCells.card ≤ H q) :
    t (2 * q) ≤ H q := by
  rcases hasPeaceable_iff_lineSets.mp (hasPeaceable_t (2 * q)) with
    ⟨R, C, D, A, hblack, hwhite⟩
  let cfg : Configuration q := ⟨R, C, D, A⟩
  rcases exists_chamber cfg with ⟨cfg', hchamber, hequiv⟩
  have ht : t (2 * q) ≤ min cfg.blackCells.card cfg.whiteCells.card :=
    le_min hblack hwhite
  have heq : min cfg.blackCells.card cfg.whiteCells.card =
      min cfg'.blackCells.card cfg'.whiteCells.card := by
    rcases hequiv with hequiv | hequiv
    · rcases hequiv with ⟨hb, hw⟩
      omega
    · rcases hequiv with ⟨hb, hw⟩
      omega
  rw [heq] at ht
  exact ht.trans (hbound cfg' hchamber)

/-- Paper `thm:q130` (S55) reduced to the two concrete checked branch trees at
their exact roots `[0,1]^8` and `N`. -/
lemma large_order_bound_of_trees (q : ℕ) (hq : 130 ≤ q)
    (globalTree : CoverTree BranchSafe PlaidExceptional globalRoot)
    (localTree : CoverTree BranchSafe CoreExceptional localRoot) :
    t (2 * q) ≤ H q := by
  have hqpos : 0 < q := by omega
  letI : NeZero (2 * q) := ⟨by omega⟩
  apply t_le_H_of_chamber_configuration q
  intro cfg hchamber
  by_cases hlarge : H q ≤ min cfg.blackCells.card cfg.whiteCells.card
  · have hglobal := global_tree_consequence globalTree cfg hqpos hchamber
      (flatProfile_mem_globalRoot cfg hqpos)
    have hlocal : InPlaid (0 : Fin 2) (1 : Fin 2) (flatProfile cfg) →
        configurationLPVector cfg LPModel.tVar ≤ (527 : ℚ) / 1000 ∨
          InCore (flatProfile cfg) := by
      intro hplaid
      exact local_tree_consequence localTree cfg hqpos hchamber
        (plaid01_mem_localRoot (flatProfile_mem_globalRoot cfg hqpos) hplaid)
    rcases configuration_escape_of_certificates cfg (by omega) hlarge hglobal hlocal with
      ⟨hneighborhood, hcore⟩
    exact configuration_finish cfg hqpos hq hneighborhood hcore
  · omega

end PeaceableQueens.UpperBound.CertificateConsequences

#print axioms PeaceableQueens.UpperBound.CertificateConsequences.chamber_flatProfile
#print axioms PeaceableQueens.UpperBound.CertificateConsequences.plaid01_neighborhood
#print axioms PeaceableQueens.UpperBound.CertificateConsequences.branch_tree_consequence
#print axioms PeaceableQueens.UpperBound.CertificateConsequences.flatProfile_mem_globalRoot
#print axioms PeaceableQueens.UpperBound.CertificateConsequences.plaid01_mem_localRoot
#print axioms PeaceableQueens.UpperBound.CertificateConsequences.global_tree_consequence
#print axioms PeaceableQueens.UpperBound.CertificateConsequences.local_tree_consequence
#print axioms PeaceableQueens.UpperBound.CertificateConsequences.threshold_contradicts_H
#print axioms PeaceableQueens.UpperBound.CertificateConsequences.configuration_escape_of_certificates
#print axioms PeaceableQueens.UpperBound.CertificateConsequences.large_order_bound_of_trees
#print axioms PeaceableQueens.UpperBound.CertificateConsequences.t_le_H_of_chamber_configuration
