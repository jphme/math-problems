import PeaceableQueens.UpperBound.Symmetry
import PeaceableQueens.UpperBound.ConfigurationMoments
import PeaceableQueens.UpperBound.ModelCompatibility
import PeaceableQueens.UpperBound.DualLeaf

namespace PeaceableQueens.UpperBound.ConfigurationBridge

open MomentModel LPModel ConfigurationMoments ModelCompatibility DualLeaf

def outerOfFlat (i : ProfileCoord) : OuterCoord :=
  match i.val with
  | 0 => ⟨.row, 0⟩
  | 1 => ⟨.row, 1⟩
  | 2 => ⟨.column, 0⟩
  | 3 => ⟨.column, 1⟩
  | 4 => ⟨.diagonal, 0⟩
  | 5 => ⟨.diagonal, 1⟩
  | 6 => ⟨.antidiagonal, 0⟩
  | _ => ⟨.antidiagonal, 1⟩

lemma outerOfFlat_flatOfOuter (c : OuterCoord) :
    outerOfFlat (flatOfOuter c) = c := by
  cases c with
  | mk family p => cases family <;> fin_cases p <;> rfl

def flatProfile (cfg : Configuration q) : Profile :=
  fun i => normalizedProfile cfg (outerOfFlat i)

lemma flatProfile_eq (cfg : Configuration q) (c : OuterCoord) :
    flatProfile cfg (flatOfOuter c) = normalizedProfile cfg c := by
  rw [flatProfile, outerOfFlat_flatOfOuter]

lemma flatProfile_box (cfg : Configuration q) (hq : 0 < q) :
    ∀ i, 0 ≤ flatProfile cfg i ∧ flatProfile cfg i ≤ 1 := by
  intro i
  exact normalizedProfile_range cfg hq (outerOfFlat i)

def flatAtomWeight (cfg : Configuration q) (a : AtomCoord) : ℚ :=
  configurationWeights cfg (innerOfFlat a)

def configurationLPVector (cfg : Configuration q) : LPVector := fun v =>
  if h : v.val < 8 then
    flatProfile cfg ⟨v.val, h⟩
  else if h : v.val < 30 then
    let k : ProductCoord := ⟨v.val - 8, by omega⟩
    flatProfile cfg (productPair k).1 * flatProfile cfg (productPair k).2
  else if h : v.val < 94 then
    flatAtomWeight cfg ⟨v.val - 30, by omega⟩
  else
    min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg))

lemma configurationLPVector_x (cfg : Configuration q) (i : ProfileCoord) :
    configurationLPVector cfg (xVar i) = flatProfile cfg i := by
  simp [configurationLPVector, xVar]

lemma configurationLPVector_y (cfg : Configuration q) (k : ProductCoord) :
    configurationLPVector cfg (yVar k) =
      flatProfile cfg (productPair k).1 * flatProfile cfg (productPair k).2 := by
  have hk := k.isLt
  have h8 : ¬ (8 + k.val < 8) := by omega
  have h30 : 8 + k.val < 30 := by omega
  simp [configurationLPVector, yVar, h8, h30]

lemma configurationLPVector_p (cfg : Configuration q) (a : AtomCoord) :
    configurationLPVector cfg (pVar a) = flatAtomWeight cfg a := by
  have ha := a.isLt
  have h8 : ¬ (30 + a.val < 8) := by omega
  have h30 : ¬ (30 + a.val < 30) := by omega
  have h94 : 30 + a.val < 94 := by omega
  simp [configurationLPVector, pVar, h8, h30, h94]

lemma configurationLPVector_t (cfg : Configuration q) :
    configurationLPVector cfg tVar =
      min (blackTotal (configurationWeights cfg)) (whiteTotal (configurationWeights cfg)) := by
  simp [configurationLPVector, tVar]

set_option maxRecDepth 100000 in
lemma innerOfFlat_bijective : Function.Bijective innerOfFlat := by decide

lemma atom_flat_sum (f : InnerAtom → ℚ) :
    (∑ a : AtomCoord, f (innerOfFlat a)) = ∑ x : InnerAtom, f x := by
  exact Fintype.sum_equiv (Equiv.ofBijective innerOfFlat innerOfFlat_bijective) _ _
    (by intro a; rfl)

def varToFin : ProfileCoord ⊕ (ProductCoord ⊕ (AtomCoord ⊕ Unit)) → VarCoord
  | .inl i => xVar i
  | .inr (.inl k) => yVar k
  | .inr (.inr (.inl a)) => pVar a
  | .inr (.inr (.inr _)) => tVar

set_option maxRecDepth 100000 in
lemma varToFin_bijective : Function.Bijective varToFin := by decide

noncomputable def varEquiv :
    (ProfileCoord ⊕ (ProductCoord ⊕ (AtomCoord ⊕ Unit))) ≃ VarCoord :=
  Equiv.ofBijective varToFin varToFin_bijective

lemma sum_var (f : VarCoord → ℚ) :
    (∑ v, f v) = (∑ i, f (xVar i)) + (∑ k, f (yVar k)) +
      (∑ a, f (pVar a)) + f tVar := by
  rw [Fintype.sum_equiv varEquiv.symm f (fun v => f (varToFin v))]
  · simp only [Fintype.sum_sum_type]
    simp [varToFin]
    ring
  · intro v
    exact congrArg f (varEquiv.apply_symm_apply v).symm

lemma atom_coefficient_sum (cfg : Configuration q) (row : EqCoord) :
    ∑ a : AtomCoord, eqCoeff row (pVar a) * configurationLPVector cfg (pVar a) =
      ∑ inner, coefficient (rowOfFlat row) inner * configurationWeights cfg inner := by
  rw [show (∑ a : AtomCoord, eqCoeff row (pVar a) * configurationLPVector cfg (pVar a)) =
    ∑ a : AtomCoord, coefficient (rowOfFlat row) (innerOfFlat a) * configurationWeights cfg (innerOfFlat a) by
      apply Finset.sum_congr rfl
      intro a _
      rw [configurationLPVector_p, flatAtomWeight]
      have hp : eqCoeff row (pVar a) = momentCoeff row a := by
        have ha := a.isLt
        have hrange : 30 ≤ pVar a ∧ pVar a < 94 := by
          change 30 ≤ 30 + a.val ∧ 30 + a.val < 94
          omega
        rw [eqCoeff, if_pos hrange]
        congr 1
        apply Fin.ext
        simp [fin64, pVar]
      rw [hp, moment_coefficients_compatible row a]]
  exact Fintype.sum_equiv (Equiv.ofBijective innerOfFlat innerOfFlat_bijective) _ _
    (by intro a; rfl)

lemma productPair_injective : Function.Injective productPair := by decide

lemma xsum_linear (cfg : Configuration q) (coord : OuterCoord) :
    (∑ i : ProfileCoord, rhsVariableCoeff (.linear coord) ⟨i.val, by omega⟩ *
      flatProfile cfg i) = -normalizedProfile cfg coord := by
  classical
  rw [Finset.sum_eq_single (flatOfOuter coord)]
  · simp [rhsVariableCoeff, flatProfile_eq]
  · intro i _ hne
    simp only [rhsVariableCoeff]
    have hval : i.val ≠ (flatOfOuter coord).val := by
      intro h
      exact hne (Fin.ext h)
    simp [hval]
  · simp

lemma ysum_linear (cfg : Configuration q) (coord : OuterCoord) :
    (∑ k : ProductCoord, rhsVariableCoeff (.linear coord) ⟨8 + k.val, by omega⟩ *
      (flatProfile cfg (productPair k).1 * flatProfile cfg (productPair k).2)) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have hk := k.isLt
  have hc := (flatOfOuter coord).isLt
  simp only [rhsVariableCoeff]
  rw [if_neg (by omega)]
  simp

lemma xsum_product (cfg : Configuration q) (factor : ℚ)
    (left right : OuterCoord) :
    (∑ i : ProfileCoord, rhsVariableCoeff (.product factor left right) ⟨i.val, by omega⟩ *
      flatProfile cfg i) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi := i.isLt
  simp [rhsVariableCoeff, show ¬ 8 ≤ i.val by omega]

lemma ysum_product (cfg : Configuration q) (factor : ℚ)
    (left right : OuterCoord) (k : ProductCoord)
    (hk : productPair k = (flatOfOuter left, flatOfOuter right)) :
    (∑ j : ProductCoord, rhsVariableCoeff (.product factor left right) ⟨8 + j.val, by omega⟩ *
      (flatProfile cfg (productPair j).1 * flatProfile cfg (productPair j).2)) =
      -factor * (normalizedProfile cfg left * normalizedProfile cfg right) := by
  classical
  have hy (j : ProductCoord) :
      rhsVariableCoeff (.product factor left right) ⟨8 + j.val, by omega⟩ =
        if productPair j = (flatOfOuter left, flatOfOuter right) then -factor else 0 := by
    simp [rhsVariableCoeff]
  simp_rw [hy]
  rw [Finset.sum_eq_single k]
  · rw [if_pos hk]
    simp only [neg_mul]
    rw [hk, flatProfile_eq, flatProfile_eq]
  · intro j _ hne
    rw [if_neg]
    · simp
    · intro hj
      apply hne
      exact productPair_injective (hj.trans hk.symm)
  · simp

def HasProductIndex : RhsTerm → Prop
  | .product _ left right => ∃ k, productPair k = (flatOfOuter left, flatOfOuter right)
  | _ => True

instance (term : RhsTerm) : Decidable (HasProductIndex term) := by
  unfold HasProductIndex
  cases term <;> infer_instance

lemma rhsTerm_hasProductIndex (row : EqCoord) :
    HasProductIndex (rhsTerm (rowOfFlat row)) := by
  revert row
  decide

lemma rhs_flat_balance (cfg : Configuration q) (term : RhsTerm)
    (hterm : HasProductIndex term) :
    (∑ i : ProfileCoord, rhsVariableCoeff term ⟨i.val, by omega⟩ * flatProfile cfg i) +
      (∑ k : ProductCoord, rhsVariableCoeff term ⟨8 + k.val, by omega⟩ *
        (flatProfile cfg (productPair k).1 * flatProfile cfg (productPair k).2)) +
      term.eval (normalizedProfile cfg) = rhsConstant term := by
  cases term with
  | one => simp [rhsVariableCoeff, rhsConstant, RhsTerm.eval]
  | linear coord =>
      rw [xsum_linear, ysum_linear]
      simp [rhsConstant, RhsTerm.eval]
  | product factor left right =>
      obtain ⟨k, hk⟩ := hterm
      rw [xsum_product, ysum_product cfg factor left right k hk]
      simp [rhsConstant, RhsTerm.eval]
      ring

lemma flat_rhs_balance (cfg : Configuration q) (row : EqCoord) :
    (∑ i : ProfileCoord, eqCoeff row (xVar i) * configurationLPVector cfg (xVar i)) +
      (∑ k : ProductCoord, eqCoeff row (yVar k) * configurationLPVector cfg (yVar k)) +
      rhs (normalizedProfile cfg) (rowOfFlat row) = eqRhs row := by
  let term := rhsTerm (rowOfFlat row)
  have hx (i : ProfileCoord) : eqCoeff row (xVar i) =
      rhsVariableCoeff term ⟨i.val, by omega⟩ := by
    simpa [term, xVar] using moment_rhs_variables_compatible row ⟨i.val, by omega⟩
  have hy (k : ProductCoord) : eqCoeff row (yVar k) =
      rhsVariableCoeff term ⟨8 + k.val, by omega⟩ := by
    simpa [term, yVar] using moment_rhs_variables_compatible row ⟨8 + k.val, by omega⟩
  rw [moment_rhs_constants_compatible row]
  simp_rw [configurationLPVector_x, configurationLPVector_y, hx, hy]
  change _ + _ + RhsTerm.eval (normalizedProfile cfg) (rhsTerm (rowOfFlat row)) =
    rhsConstant (rhsTerm (rowOfFlat row))
  exact rhs_flat_balance cfg _ (rhsTerm_hasProductIndex row)

theorem configurationLPVector_equalities (cfg : Configuration q) (hq : 0 < q) :
    ∀ row, dot (eqCoeff row) (configurationLPVector cfg) = eqRhs row := by
  intro row
  rw [dot, sum_var]
  rw [atom_coefficient_sum]
  have hm := configurationWeights_satisfiesMoments cfg hq (rowOfFlat row)
  have hcoeff : ∑ inner, coefficient (rowOfFlat row) inner * configurationWeights cfg inner =
      rhs (normalizedProfile cfg) (rowOfFlat row) := by
    simpa [matrixRow] using hm
  rw [hcoeff]
  have ht : eqCoeff row tVar = 0 := by
    have htx (i : ProfileCoord) : tVar ≠ xVar i := by
      intro h
      have hval : 94 = i.val := congrArg Fin.val h
      omega
    have hty (k : ProductCoord) : tVar ≠ yVar k := by
      intro h
      have hval : 94 = 8 + k.val := congrArg Fin.val h
      omega
    have ht94 : ¬ (30 ≤ tVar ∧ tVar < 94) := by
      simp [tVar]
    rw [eqCoeff, if_neg ht94]
    cases hblock : eqBlock? row with
    | some bf =>
        obtain ⟨b, f⟩ := bf
        simp only
        cases hs : featureSingle? f with
        | some family => simp [htx]
        | none =>
            cases hp : featurePair? f with
            | none => simp
            | some families =>
                obtain ⟨family₁, family₂⟩ := families
                simp only
                cases hpi : productIndex? (outerOf b family₁, outerOf b family₂) with
                | none => simp
                | some product => simp [hty]
    | none =>
        simp only
        cases hp : eqAggregateParity? row <;> simp [hty]
  rw [ht]
  simp only [zero_mul, add_zero]
  simpa [add_assoc] using flat_rhs_balance cfg row


def BoxContained (lo hi : Profile) (cfg : Configuration q) : Prop :=
  ∀ i, lo i ≤ flatProfile cfg i ∧ flatProfile cfg i ≤ hi i

lemma configurationLPVector_profile_box (cfg : Configuration q)
    (lo hi : Profile) (hbox : BoxContained lo hi cfg) :
    ∀ i, lo i ≤ configurationLPVector cfg (xVar i) ∧
      configurationLPVector cfg (xVar i) ≤ hi i := by
  intro i
  simpa only [configurationLPVector_x] using hbox i

lemma configurationLPVector_product_box (cfg : Configuration q)
    (lo hi : Profile) (hq : 0 < q) (hbox : BoxContained lo hi cfg)
    (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, 0 ≤ hi i) :
    ∀ k, productLower lo k ≤ configurationLPVector cfg (yVar k) ∧
      configurationLPVector cfg (yVar k) ≤ productUpper hi k := by
  intro k
  let i := (productPair k).1
  let j := (productPair k).2
  have hxi := hbox i
  have hxj := hbox j
  have hxi0 : 0 ≤ flatProfile cfg i := (flatProfile_box cfg hq i).1
  have hxj0 : 0 ≤ flatProfile cfg j := (flatProfile_box cfg hq j).1
  constructor
  · rw [configurationLPVector_y]
    exact mul_le_mul hxi.1 hxj.1 (hlo j) hxi0
  · rw [configurationLPVector_y]
    exact mul_le_mul hxi.2 hxj.2 hxj0 (hhi i)

lemma configurationLPVector_atoms_nonnegative (cfg : Configuration q)
    [NeZero (2 * q)] :
    ∀ a, 0 ≤ configurationLPVector cfg (pVar a) := by
  intro a
  rw [configurationLPVector_p, flatAtomWeight]
  exact configurationWeights_nonnegative cfg (innerOfFlat a)

lemma configurationLPVector_t_le_black (cfg : Configuration q)
    [NeZero (2 * q)] :
    configurationLPVector cfg tVar ≤
      (cfg.blackCells.card : ℚ) / (q ^ 2 : ℚ) := by
  rw [configurationLPVector_t, configurationWeights_blackTotal]
  exact min_le_left _ _

lemma configurationLPVector_t_le_white (cfg : Configuration q)
    [NeZero (2 * q)] :
    configurationLPVector cfg tVar ≤
      (cfg.whiteCells.card : ℚ) / (q ^ 2 : ℚ) := by
  rw [configurationLPVector_t, configurationWeights_whiteTotal]
  exact min_le_right _ _

lemma ineq_zero_x (lo hi : Profile) (i : ProfileCoord) :
    ineqCoeff lo hi 0 (xVar i) = 1 := by
  unfold ineqCoeff
  rw [if_pos rfl]
  apply if_pos
  change i.val < 8
  exact i.isLt

lemma ineq_zero_notx (lo hi : Profile) (k : ProductCoord) :
    ineqCoeff lo hi 0 (yVar k) = 0 := by
  unfold ineqCoeff
  rw [if_pos rfl]
  apply if_neg
  change ¬ 8 + k.val < 8
  omega

lemma zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx := ZMod.natCast_zmod_val x
  have hlt := ZMod.val_lt x
  interval_cases h : x.val <;> simp_all

lemma card_parity_split (q : ℕ) (s : Finset (ZMod (2 * q))) :
    (s.filter fun x => parityMap q x = (0 : ZMod 2)).card +
      (s.filter fun x => parityMap q x = (1 : ZMod 2)).card = s.card := by
  classical
  let P : ZMod (2 * q) → Prop := fun x => parityMap q x = (0 : ZMod 2)
  have h := Finset.card_filter_add_card_filter_not (s := s) P
  rw [show (s.filter fun x => ¬ P x) =
      s.filter fun x => parityMap q x = (1 : ZMod 2) by
    ext x
    simp only [Finset.mem_filter, P]
    constructor
    · rintro ⟨hs, hn⟩
      rcases zmod_two_eq_zero_or_one (parityMap q x) with h0 | h1
      · exact False.elim (hn h0)
      · exact ⟨hs, h1⟩
    · rintro ⟨hs, h1⟩
      refine ⟨hs, ?_⟩
      intro h0
      have h01 : (0 : ZMod 2) = 1 := h0.symm.trans h1
      norm_num at h01
  ] at h
  exact h

lemma outerCount_pair_sum (cfg : Configuration q) (family : Family) :
    outerCount cfg ⟨family, 0⟩ + outerCount cfg ⟨family, 1⟩ =
      match family with
      | .row => cfg.R.card
      | .column => cfg.C.card
      | .diagonal => cfg.D.card
      | .antidiagonal => cfg.A.card := by
  cases family
  · simpa [outerCount, rowCount] using card_parity_split q cfg.R
  · simpa [outerCount, columnCount] using card_parity_split q cfg.C
  · simpa [outerCount, diagonalCount] using card_parity_split q cfg.D
  · simpa [outerCount, antidiagonalCount] using card_parity_split q cfg.A

lemma xVar_injective : Function.Injective xVar := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun v : VarCoord => v.val) h

lemma yVar_injective : Function.Injective yVar := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun v : VarCoord => v.val) h
  simp [yVar] at hv
  omega

@[simp] lemma xVar_inj {i j : ProfileCoord} : xVar i = xVar j ↔ i = j :=
  xVar_injective.eq_iff
@[simp] lemma yVar_inj {i j : ProductCoord} : yVar i = yVar j ↔ i = j :=
  yVar_injective.eq_iff

lemma dot_sparse_three (z : LPVector) (a b c : VarCoord) (ca cb cc : ℚ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    dot (fun v => if v = a then ca else if v = b then cb else if v = c then cc else 0) z =
      ca * z a + cb * z b + cc * z c := by
  classical
  unfold dot
  have hpoint (v : VarCoord) :
      (if v = a then ca else if v = b then cb else if v = c then cc else 0) * z v =
        (if v = a then ca * z v else 0) + (if v = b then cb * z v else 0) +
          (if v = c then cc * z v else 0) := by
    by_cases ha : v = a <;> by_cases hb : v = b <;> by_cases hc : v = c <;> simp_all
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp

lemma dot_sparse_two (z : LPVector) (a b : VarCoord) (ca cb : ℚ) (hab : a ≠ b) :
    dot (fun v => if v = a then ca else if v = b then cb else 0) z =
      ca * z a + cb * z b := by
  classical
  unfold dot
  have hpoint (v : VarCoord) :
      (if v = a then ca else if v = b then cb else 0) * z v =
        (if v = a then ca * z v else 0) + (if v = b then cb * z v else 0) := by
    by_cases ha : v = a <;> by_cases hb : v = b <;> simp_all
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

lemma dot_sparse_four (z : LPVector) (a b c d : VarCoord) (ca cb cc cd : ℚ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    dot (fun v => if v = a then ca else if v = b then cb else if v = c then cc else
      if v = d then cd else 0) z = ca*z a + cb*z b + cc*z c + cd*z d := by
  classical
  unfold dot
  have hpoint (v : VarCoord) :
      (if v = a then ca else if v = b then cb else if v = c then cc else if v = d then cd else 0) * z v =
      (if v = a then ca*z v else 0) + (if v = b then cb*z v else 0) +
      (if v = c then cc*z v else 0) + (if v = d then cd*z v else 0) := by
    by_cases ha : v=a <;> by_cases hb : v=b <;> by_cases hc : v=c <;> by_cases hd : v=d <;> simp_all
  simp_rw [hpoint]
  repeat' rw [Finset.sum_add_distrib]
  simp

lemma productPair_ne (k : ProductCoord) : (productPair k).1 ≠ (productPair k).2 := by
  revert k
  decide

set_option maxRecDepth 100000 in
lemma ineq_dot_mccormick (cfg : Configuration q) (lo hi : Profile)
    (r : IneqCoord) (hr : 7 ≤ r.val) :
    dot (ineqCoeff lo hi r) (configurationLPVector cfg) =
      let k : ProductCoord := fin22 ((r.val - 7) / 4)
      let step := (r - 7) % 4
      let (i, j) := productPair k
      match step with
      | 0 => -flatProfile cfg i * flatProfile cfg j + lo j * flatProfile cfg i + lo i * flatProfile cfg j
      | 1 => -flatProfile cfg i * flatProfile cfg j + hi j * flatProfile cfg i + hi i * flatProfile cfg j
      | 2 => flatProfile cfg i * flatProfile cfg j - lo j * flatProfile cfg i - hi i * flatProfile cfg j
      | _ => flatProfile cfg i * flatProfile cfg j - hi j * flatProfile cfg i - lo i * flatProfile cfg j := by
  have hr0 : r ≠ 0 := by intro h; subst r; omega
  have hr1 : r ≠ 1 := by intro h; subst r; omega
  have hr2 : r ≠ 2 := by intro h; subst r; omega
  have hr3 : r ≠ 3 := by intro h; subst r; omega
  have hr4 : r ≠ 4 := by intro h; subst r; omega
  have hr5 : r ≠ 5 := by intro h; subst r; omega
  have hr6 : r ≠ 6 := by intro h; subst r; omega
  unfold ineqCoeff
  simp_rw [if_neg hr0, if_neg hr1, if_neg hr2, if_neg hr3, if_neg hr4,
    if_neg hr5, if_neg hr6]
  let k : ProductCoord := fin22 ((r.val - 7) / 4)
  let step := (r - 7) % 4
  let i := (productPair k).1
  let j := (productPair k).2
  change dot (fun v =>
      if v = yVar k then if step < 2 then -1 else 1
      else if v = xVar i then match step with | 0 => lo j | 1 => hi j | 2 => -lo j | _ => -hi j
      else if v = xVar j then match step with | 0 => lo i | 1 => hi i | 2 => -hi i | _ => -lo i
      else 0) (configurationLPVector cfg) = _
  have hyx1 : yVar k ≠ xVar i := by
    intro h; have hv := congrArg (fun v : VarCoord => v.val) h
    have hk := k.isLt; have hi := i.isLt
    simp [yVar, xVar] at hv; omega
  have hyx2 : yVar k ≠ xVar j := by
    intro h; have hv := congrArg (fun v : VarCoord => v.val) h
    have hk := k.isLt; have hj := j.isLt
    simp [yVar, xVar] at hv; omega
  have hij : xVar i ≠ xVar j := by
    intro h; exact productPair_ne k (xVar_injective h)
  rw [dot_sparse_three (configurationLPVector cfg) (yVar k) (xVar i) (xVar j)
    (if step < 2 then -1 else 1)
    (match step with | 0 => lo j | 1 => hi j | 2 => -lo j | _ => -hi j)
    (match step with | 0 => lo i | 1 => hi i | 2 => -hi i | _ => -lo i) hyx1 hyx2 hij]
  simp only [configurationLPVector_x, configurationLPVector_y]
  change _ = (match step with
    | 0 => _ | 1 => _ | 2 => _ | _ => _)
  have hs : step.val < 4 := by
    dsimp [step]
    exact Nat.mod_lt _ (by omega)
  interval_cases h : step.val
  · have hstep : step = 0 := Fin.ext h
    rw [hstep]; simp [i, j]; ring
  · have hstep : step = 1 := Fin.ext h
    rw [hstep]; simp [i, j]; ring
  · have hstep : step = 2 := Fin.ext h
    rw [hstep]; simp [i, j]; ring
  · have hstep : step = 3 := Fin.ext h
    rw [hstep]; simp [i, j]; ring

theorem configurationLPVector_mccormick_rows (cfg : Configuration q) (lo hi : Profile)
    (hbox : BoxContained lo hi cfg) (r : IneqCoord) (hr : 7 ≤ r.val) :
    dot (ineqCoeff lo hi r) (configurationLPVector cfg) ≤ ineqRhs lo hi r := by
  rw [ineq_dot_mccormick cfg lo hi r hr]
  have hr0 : r ≠ 0 := by intro h; subst r; omega
  have hrFin : 7 ≤ r := by
    change 7 ≤ r.val
    exact hr
  simp only [ineqRhs, if_neg hr0, dif_pos hrFin]
  let k : ProductCoord := fin22 ((r.val - 7) / 4)
  let step := (r - 7) % 4
  let i := (productPair k).1
  let j := (productPair k).2
  have hxi := hbox i
  have hxj := hbox j
  change (match step with
    | 0 => _ | 1 => _ | 2 => _ | _ => _) ≤
    (match step with | 0 => _ | 1 => _ | 2 => _ | _ => _)
  have hs : step.val < 4 := by
    dsimp [step]
    exact Nat.mod_lt _ (by omega)
  interval_cases h : step.val
  · have hstep : step = 0 := Fin.ext h
    rw [hstep]
    simp only
    convert mccormick_lower_lower hxi.1 hxj.1 using 1 <;> dsimp [k, i, j] <;> ring
  · have hstep : step = 1 := Fin.ext h
    rw [hstep]
    simp only
    convert mccormick_upper_upper hxi.2 hxj.2 using 1 <;> dsimp [k, i, j] <;> ring
  · have hstep : step = 2 := Fin.ext h
    rw [hstep]
    simp only
    convert mccormick_upper_lower hxi.2 hxj.1 using 1 <;> dsimp [k, i, j] <;> ring
  · have hstep : step = 3 := Fin.ext h
    rw [hstep]
    simp only
    convert mccormick_lower_upper hxi.1 hxj.2 using 1 <;> dsimp [k, i, j] <;> ring

lemma ineq_dot_row1 (cfg : Configuration q) (lo hi : Profile) :
    dot (ineqCoeff lo hi 1) (configurationLPVector cfg) =
      flatProfile cfg 0 - flatProfile cfg 1 := by
  unfold ineqCoeff
  norm_num
  change dot (fun v => if v = xVar 0 then 1 else if v = xVar 1 then -1 else 0)
    (configurationLPVector cfg) = _
  rw [dot_sparse_two (configurationLPVector cfg) (xVar 0) (xVar 1) 1 (-1) (by
    intro h
    have hv := congrArg Fin.val h
    simp [xVar] at hv)]
  simp [configurationLPVector_x]
  ring

lemma ineq_dot_row2 (cfg : Configuration q) (lo hi : Profile) :
    dot (ineqCoeff lo hi 2) (configurationLPVector cfg) =
      flatProfile cfg 2 - flatProfile cfg 3 := by
  unfold ineqCoeff
  norm_num
  change dot (fun v => if v = xVar 2 then 1 else if v = xVar 3 then -1 else 0)
    (configurationLPVector cfg) = _
  rw [dot_sparse_two (configurationLPVector cfg) (xVar 2) (xVar 3) 1 (-1) (by decide)]
  simp [configurationLPVector_x]
  ring

lemma ineq_dot_row3 (cfg : Configuration q) (lo hi : Profile) :
    dot (ineqCoeff lo hi 3) (configurationLPVector cfg) =
      flatProfile cfg 0 + flatProfile cfg 1 - flatProfile cfg 2 - flatProfile cfg 3 := by
  unfold ineqCoeff
  norm_num
  change dot (fun v => if v = xVar 0 then 1 else if v = xVar 1 then 1 else
    if v = xVar 2 then -1 else if v = xVar 3 then -1 else 0) (configurationLPVector cfg) = _
  rw [dot_sparse_four (configurationLPVector cfg) (xVar 0) (xVar 1) (xVar 2) (xVar 3)
    1 1 (-1) (-1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  simp [configurationLPVector_x]
  ring

lemma ineq_dot_row4 (cfg : Configuration q) (lo hi : Profile) :
    dot (ineqCoeff lo hi 4) (configurationLPVector cfg) =
      flatProfile cfg 4 + flatProfile cfg 5 - flatProfile cfg 6 - flatProfile cfg 7 := by
  unfold ineqCoeff
  norm_num
  change dot (fun v => if v = xVar 4 then 1 else if v = xVar 5 then 1 else
    if v = xVar 6 then -1 else if v = xVar 7 then -1 else 0) (configurationLPVector cfg) = _
  rw [dot_sparse_four (configurationLPVector cfg) (xVar 4) (xVar 5) (xVar 6) (xVar 7)
    1 1 (-1) (-1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  simp [configurationLPVector_x]
  ring

lemma flatProfile_le_of_outer {cfg : Configuration q} (hq : 0 < q)
    {i j : ProfileCoord} (h : outerCount cfg (outerOfFlat i) ≤ outerCount cfg (outerOfFlat j)) :
    flatProfile cfg i ≤ flatProfile cfg j := by
  unfold flatProfile normalizedProfile
  apply div_le_div_of_nonneg_right
  · exact_mod_cast h
  · exact le_of_lt (by exact_mod_cast hq)

set_option maxRecDepth 100000 in
lemma innerOfFlat_black_iff (a : AtomCoord) :
    (innerOfFlat a).atom = blackAtom ↔ localAtom a = 15 := by
  revert a
  decide

set_option maxRecDepth 100000 in
lemma innerOfFlat_white_iff (a : AtomCoord) :
    (innerOfFlat a).atom = whiteAtom ↔ localAtom a = 0 := by
  revert a
  decide

lemma flat_atoms_black_sum (cfg : Configuration q) :
    (∑ a : AtomCoord, if localAtom a = 15 then flatAtomWeight cfg a else 0) =
      blackTotal (configurationWeights cfg) := by
  calc
    (∑ a : AtomCoord, if localAtom a = 15 then flatAtomWeight cfg a else 0) =
        ∑ a : AtomCoord, if (innerOfFlat a).atom = blackAtom then
          configurationWeights cfg (innerOfFlat a) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          simp only [flatAtomWeight, innerOfFlat_black_iff]
    _ = ∑ inner, if inner.atom = blackAtom then configurationWeights cfg inner else 0 :=
      atom_flat_sum (fun inner => if inner.atom = blackAtom then configurationWeights cfg inner else 0)
    _ = blackTotal (configurationWeights cfg) := rfl

lemma flat_atoms_white_sum (cfg : Configuration q) :
    (∑ a : AtomCoord, if localAtom a = 0 then flatAtomWeight cfg a else 0) =
      whiteTotal (configurationWeights cfg) := by
  calc
    (∑ a : AtomCoord, if localAtom a = 0 then flatAtomWeight cfg a else 0) =
        ∑ a : AtomCoord, if (innerOfFlat a).atom = whiteAtom then
          configurationWeights cfg (innerOfFlat a) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          simp only [flatAtomWeight, innerOfFlat_white_iff]
    _ = ∑ inner, if inner.atom = whiteAtom then configurationWeights cfg inner else 0 :=
      atom_flat_sum (fun inner => if inner.atom = whiteAtom then configurationWeights cfg inner else 0)
    _ = whiteTotal (configurationWeights cfg) := rfl

lemma ineq_dot_row5 (cfg : Configuration q) (lo hi : Profile) :
    dot (ineqCoeff lo hi 5) (configurationLPVector cfg) =
      configurationLPVector cfg tVar -
        ∑ a : AtomCoord, if localAtom a = 15 then flatAtomWeight cfg a else 0 := by
  rw [dot, sum_var]
  have hx (i : ProfileCoord) : ineqCoeff lo hi 5 (xVar i) = 0 := by
    have ht : xVar i ≠ tVar := by intro h; have := congrArg Fin.val h; simp [xVar, tVar] at this; omega
    have hrange : ¬ (30 ≤ xVar i ∧ xVar i < 94) := by
      intro h; have := i.isLt; change 30 ≤ i.val ∧ i.val < 94 at h; omega
    simp [ineqCoeff, ht, hrange]
  have hy (k : ProductCoord) : ineqCoeff lo hi 5 (yVar k) = 0 := by
    have ht : yVar k ≠ tVar := by intro h; have := congrArg Fin.val h; simp [yVar, tVar] at this; omega
    have hrange : ¬ (30 ≤ yVar k ∧ yVar k < 94) := by
      intro h; have := k.isLt; change 30 ≤ 8 + k.val ∧ 8 + k.val < 94 at h; omega
    simp [ineqCoeff, ht, hrange]
  have hp (a : AtomCoord) : ineqCoeff lo hi 5 (pVar a) =
      if localAtom a = 15 then -1 else 0 := by
    have ht : pVar a ≠ tVar := by intro h; have := congrArg Fin.val h; simp [pVar, tVar] at this; omega
    have hrange : 30 ≤ pVar a ∧ pVar a < 94 := by
      have ha := a.isLt
      change 30 ≤ 30 + a.val ∧ 30 + a.val < 94
      omega
    have hidx : fin64 (pVar a - 30) = a := by
      apply Fin.ext
      simp [pVar, fin64, Nat.mod_eq_of_lt a.isLt]
    simp [ineqCoeff, ht, hrange, hidx]
  have ht : ineqCoeff lo hi 5 tVar = 1 := by
    simp [ineqCoeff, tVar]
  simp_rw [hx, hy, hp, ht, configurationLPVector_p]
  simp only [zero_mul, one_mul]
  rw [show (∑ x : AtomCoord, (if localAtom x = 15 then -1 else 0) * flatAtomWeight cfg x) =
    -(∑ x : AtomCoord, if localAtom x = 15 then flatAtomWeight cfg x else 0) by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> ring]
  ring

lemma ineq_dot_row6 (cfg : Configuration q) (lo hi : Profile) :
    dot (ineqCoeff lo hi 6) (configurationLPVector cfg) =
      configurationLPVector cfg tVar -
        ∑ a : AtomCoord, if localAtom a = 0 then flatAtomWeight cfg a else 0 := by
  rw [dot, sum_var]
  have hx (i : ProfileCoord) : ineqCoeff lo hi 6 (xVar i) = 0 := by
    have ht : xVar i ≠ tVar := by intro h; have := congrArg Fin.val h; simp [xVar, tVar] at this; omega
    have hrange : ¬ (30 ≤ xVar i ∧ xVar i < 94) := by
      intro h; have := i.isLt; change 30 ≤ i.val ∧ i.val < 94 at h; omega
    simp [ineqCoeff, ht, hrange]
  have hy (k : ProductCoord) : ineqCoeff lo hi 6 (yVar k) = 0 := by
    have ht : yVar k ≠ tVar := by intro h; have := congrArg Fin.val h; simp [yVar, tVar] at this; omega
    have hrange : ¬ (30 ≤ yVar k ∧ yVar k < 94) := by
      intro h; have := k.isLt; change 30 ≤ 8 + k.val ∧ 8 + k.val < 94 at h; omega
    simp [ineqCoeff, ht, hrange]
  have hp (a : AtomCoord) : ineqCoeff lo hi 6 (pVar a) =
      if localAtom a = 0 then -1 else 0 := by
    have ht : pVar a ≠ tVar := by intro h; have := congrArg Fin.val h; simp [pVar, tVar] at this; omega
    have hrange : 30 ≤ pVar a ∧ pVar a < 94 := by
      have ha := a.isLt
      change 30 ≤ 30 + a.val ∧ 30 + a.val < 94
      omega
    have hidx : fin64 (pVar a - 30) = a := by
      apply Fin.ext
      simp [pVar, fin64, Nat.mod_eq_of_lt a.isLt]
    simp [ineqCoeff, ht, hrange, hidx]
  have ht : ineqCoeff lo hi 6 tVar = 1 := by simp [ineqCoeff, tVar]
  simp_rw [hx, hy, hp, ht, configurationLPVector_p]
  simp only [zero_mul, one_mul]
  rw [show (∑ x : AtomCoord, (if localAtom x = 0 then -1 else 0) * flatAtomWeight cfg x) =
    -(∑ x : AtomCoord, if localAtom x = 0 then flatAtomWeight cfg x else 0) by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> ring]
  ring


lemma ineq_row0 (cfg : Configuration q) (hq : 0 < q) (hch : chamber q cfg)
    (lo hi : Profile) :
    dot (ineqCoeff lo hi 0) (configurationLPVector cfg) ≤ ineqRhs lo hi 0 := by
  rw [dot, sum_var]
  simp_rw [ineq_zero_x]
  have hy (k : ProductCoord) : ineqCoeff lo hi 0 (yVar k) = 0 := by
    exact ineq_zero_notx _ _ k
  have hp (a : AtomCoord) : ineqCoeff lo hi 0 (pVar a) = 0 := by
    unfold ineqCoeff
    rw [if_pos rfl]
    apply if_neg
    change ¬ 30 + a.val < 8
    omega
  have ht : ineqCoeff lo hi 0 tVar = 0 := by
    simp [ineqCoeff, tVar]
  simp_rw [hy, hp, ht, configurationLPVector_x]
  simp [ineqRhs]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [flatProfile, outerOfFlat]
  simp only [normalizedProfile_eq_div]
  field_simp
  have hb :
      outerCount cfg ⟨.row, 0⟩ + outerCount cfg ⟨.row, 1⟩ +
      outerCount cfg ⟨.column, 0⟩ + outerCount cfg ⟨.column, 1⟩ +
      outerCount cfg ⟨.diagonal, 0⟩ + outerCount cfg ⟨.diagonal, 1⟩ +
      outerCount cfg ⟨.antidiagonal, 0⟩ + outerCount cfg ⟨.antidiagonal, 1⟩ ≤ 4 * q := by
    have hR := outerCount_pair_sum cfg Family.row
    have hC := outerCount_pair_sum cfg Family.column
    have hD := outerCount_pair_sum cfg Family.diagonal
    have hA := outerCount_pair_sum cfg Family.antidiagonal
    simp at hR hC hD hA
    have hbudget : totalLineCount cfg ≤ 4 * q := hch.2.2.2.2
    simp only [totalLineCount] at hbudget
    omega
  have hbQ :
      (outerCount cfg ⟨.row, 0⟩ : ℚ) + (outerCount cfg ⟨.row, 1⟩ : ℚ) +
      (outerCount cfg ⟨.column, 0⟩ : ℚ) + (outerCount cfg ⟨.column, 1⟩ : ℚ) +
      (outerCount cfg ⟨.diagonal, 0⟩ : ℚ) + (outerCount cfg ⟨.diagonal, 1⟩ : ℚ) +
      (outerCount cfg ⟨.antidiagonal, 0⟩ : ℚ) + (outerCount cfg ⟨.antidiagonal, 1⟩ : ℚ) ≤
        (4 : ℚ) * q := by
    exact_mod_cast hb
  linarith

theorem configurationLPVector_base_rows
    (cfg : Configuration q) (hq : 0 < q) (hch : chamber q cfg) (lo hi : Profile)
    (hbox : BoxContained lo hi cfg) :
    ∀ row, dot (ineqCoeff lo hi row) (configurationLPVector cfg) ≤ ineqRhs lo hi row := by
  intro row
  by_cases hmc : 7 ≤ row.val
  · exact configurationLPVector_mccormick_rows cfg lo hi hbox row hmc
  · have hrow : row.val < 7 := by omega
    interval_cases h : row.val
    · have hr : row = 0 := Fin.ext h
      subst row
      exact ineq_row0 cfg hq hch lo hi
    · have hr : row = 1 := Fin.ext h
      subst row
      rw [ineq_dot_row1]
      simp [ineqRhs]
      exact flatProfile_le_of_outer (i := 0) (j := 1) hq hch.1
    · have hr : row = 2 := Fin.ext h
      subst row
      rw [ineq_dot_row2]
      simp [ineqRhs]
      exact flatProfile_le_of_outer (i := 2) (j := 3) hq hch.2.1
    · have hr : row = 3 := Fin.ext h
      subst row
      rw [ineq_dot_row3]
      simp [ineqRhs]
      have hrc : flatProfile cfg 0 + flatProfile cfg 1 ≤ flatProfile cfg 2 + flatProfile cfg 3 := by
        unfold flatProfile normalizedProfile
        field_simp
        exact_mod_cast hch.2.2.1
      simpa [add_comm] using hrc
    · have hr : row = 4 := Fin.ext h
      subst row
      rw [ineq_dot_row4]
      simp [ineqRhs]
      have hda : flatProfile cfg 4 + flatProfile cfg 5 ≤ flatProfile cfg 6 + flatProfile cfg 7 := by
        unfold flatProfile normalizedProfile
        field_simp
        exact_mod_cast hch.2.2.2.1
      simpa [add_comm] using hda
    · have hr : row = 5 := Fin.ext h
      subst row
      rw [ineq_dot_row5, flat_atoms_black_sum, configurationLPVector_t]
      simp [ineqRhs]
    · have hr : row = 6 := Fin.ext h
      subst row
      rw [ineq_dot_row6, flat_atoms_white_sum, configurationLPVector_t]
      simp [ineqRhs]

theorem configurationLPVector_leafFeasible_of_base_rows
    (cfg : Configuration q) (hq : 0 < q) (hch : chamber q cfg) (lo hi : Profile)
    (hbox : BoxContained lo hi cfg) (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, 0 ≤ hi i)
    (heq : ∀ row, dot (eqCoeff row) (configurationLPVector cfg) = eqRhs row) :
    LeafFeasible lo hi (configurationLPVector cfg) := by
  haveI : NeZero (2 * q) := ⟨by omega⟩
  refine ⟨configurationLPVector_base_rows cfg hq hch lo hi hbox, heq,
    configurationLPVector_profile_box cfg lo hi hbox,
    configurationLPVector_product_box cfg lo hi hq hbox hlo hhi,
    configurationLPVector_atoms_nonnegative cfg⟩


/-- The configuration form of paper `def:OPT` and `eq:opt` (S32): the actual
normalized profile, its exact products, its atom frequencies and the objective
`min(B,W)/q²` form a feasible point of the leaf LP on every nonnegative box
containing the profile.  No optimum or attainment statement is needed. -/
theorem configurationLPVector_leafFeasible
    (cfg : Configuration q) (hq : 0 < q) (hch : chamber q cfg) (lo hi : Profile)
    (hbox : BoxContained lo hi cfg) (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, 0 ≤ hi i) :
    LeafFeasible lo hi (configurationLPVector cfg) :=
  configurationLPVector_leafFeasible_of_base_rows cfg hq hch lo hi hbox hlo hhi
    (configurationLPVector_equalities cfg hq)

end PeaceableQueens.UpperBound.ConfigurationBridge
