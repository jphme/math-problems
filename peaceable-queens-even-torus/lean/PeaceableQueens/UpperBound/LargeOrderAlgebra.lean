import PeaceableQueens.UpperBound.ConfigurationBridge

/-!
# Local rational algebra for the large-order finish

Paper Section `sec:local`, obligations S42--S52: the local coordinates
`eq:locvars` and aggregates `eq:aggregates`, `lem:basic`, `lem:dichotomy`, and
the purely algebraic steps of `prop:caseA` and `prop:caseB`.  Everything here
is over `ℚ`; the integrality step `eq:B29` enters through
`zeta_ge_two_of_natural_defects`, applied to natural counts in
`LargeOrderFinish`.
-/

namespace PeaceableQueens.UpperBound.LargeOrderAlgebra

/-- Paper `eq:locvars`: `u = r₀`, `R = r₁`, `v = c₀`, `C = c₁`, `e = d₁`,
`f = a₁`, `g = q - d₀`, `h = q - a₀`, as rationals. -/
structure Local where
  q : ℚ
  u : ℚ
  R : ℚ
  v : ℚ
  C : ℚ
  e : ℚ
  f : ℚ
  g : ℚ
  h : ℚ

namespace Local

def sigma (d : Local) : ℚ := d.R + d.C
def m (d : Local) : ℚ := d.u + d.v
def delta (d : Local) : ℚ := d.e + d.f
def zeta (d : Local) : ℚ := d.g + d.h
def alpha (d : Local) : ℚ := 2 * d.q - d.sigma - d.m
def beta (d : Local) : ℚ := d.sigma - d.q
def Q (d : Local) : ℚ := 2 * d.e * d.f + 2 * d.g * d.h
def X (d : Local) : ℚ := d.u * d.v + d.R * d.C
def Y (d : Local) : ℚ :=
  (d.q - d.u) * (d.q - d.C) + (d.q - d.R) * (d.q - d.v)
def L (d : Local) : ℚ := 2 * d.q - d.sigma
def FB (d : Local) : ℚ := d.X - d.beta * d.zeta + d.Q
def FW (d : Local) : ℚ := d.Y - d.alpha * d.delta + d.Q

def Nonnegative (d : Local) : Prop :=
  0 ≤ d.u ∧ 0 ≤ d.R ∧ 0 ≤ d.v ∧ 0 ≤ d.C ∧
  0 ≤ d.e ∧ 0 ≤ d.f ∧ 0 ≤ d.g ∧ 0 ≤ d.h

def Core (d : Local) : Prop :=
  36 / 25 * d.q ≤ d.sigma ∧ d.sigma ≤ 37 / 25 * d.q ∧
  d.m ≤ 9 / 100 * d.q ∧ d.delta ≤ 9 / 200 * d.q ∧
  d.zeta ≤ 1 / 25 * d.q

lemma alpha_eq_L_sub_m (d : Local) : d.alpha = d.L - d.m := by
  simp only [alpha, L, sigma, m]

/-- Paper `lem:basic` (S44): `α ≥ 43q/100`, `β ≥ 11q/25`, `δ < α`, `ζ < β`
under the aggregate core. -/
lemma basic (d : Local) (hq : 0 < d.q) (hcore : d.Core) :
    43 / 100 * d.q ≤ d.alpha ∧ 11 / 25 * d.q ≤ d.beta ∧
      d.delta < d.alpha ∧ d.zeta < d.beta := by
  rcases hcore with ⟨hslo, hshi, hm, hd, hz⟩
  dsimp [sigma, m, delta, zeta] at hslo hshi hm hd hz
  constructor
  · dsimp [alpha, sigma, m]
    norm_num at hslo hshi hm hd hz ⊢
    linarith
  constructor
  · dsimp [beta, sigma]
    norm_num at hslo hshi hm hd hz ⊢
    linarith
  constructor
  · dsimp [alpha, sigma, m, delta]
    norm_num at hslo hshi hm hd hz ⊢
    linarith
  · dsimp [beta, sigma, zeta]
    norm_num at hslo hshi hm hd hz ⊢
    linarith

/-- Paper `lem:dichotomy`, first inequality of `eq:dicho`: `2Q ≤ δ² + ζ²`. -/
lemma two_Q_le_squares (d : Local) :
    2 * d.Q ≤ d.delta ^ 2 + d.zeta ^ 2 := by
  dsimp [Q, delta, zeta]
  nlinarith [sq_nonneg (d.e - d.f), sq_nonneg (d.g - d.h)]

lemma squares_le_weighted (d : Local) (hnonneg : d.Nonnegative)
    (hdelta : d.delta ≤ d.alpha) (hzeta : d.zeta ≤ d.beta) :
    d.delta ^ 2 + d.zeta ^ 2 ≤ d.alpha * d.delta + d.beta * d.zeta := by
  rcases hnonneg with ⟨hu, hR, hv, hC, he, hf, hg, hh⟩
  dsimp [delta, zeta] at hdelta hzeta ⊢
  have hd0 : 0 ≤ d.e + d.f := by linarith
  have hz0 : 0 ≤ d.g + d.h := by linarith
  nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hdelta),
    mul_nonneg hz0 (sub_nonneg.mpr hzeta)]

/-- Paper `lem:dichotomy` (S45): `Q ≤ αδ` or `Q ≤ βζ`. -/
lemma defect_dichotomy (d : Local) (hnonneg : d.Nonnegative)
    (hdelta : d.delta < d.alpha) (hzeta : d.zeta < d.beta) :
    d.Q ≤ d.alpha * d.delta ∨ d.Q ≤ d.beta * d.zeta := by
  have htw := two_Q_le_squares d
  have hsq := squares_le_weighted d hnonneg (le_of_lt hdelta) (le_of_lt hzeta)
  by_cases h : d.alpha * d.delta ≤ d.beta * d.zeta
  · right
    nlinarith
  · left
    have h' : d.beta * d.zeta ≤ d.alpha * d.delta := le_of_not_ge h
    nlinarith

lemma two_gh_le_q_zeta_over_fifty (d : Local) (hnonneg : d.Nonnegative)
    (hcore : d.Core) : 2 * d.g * d.h ≤ d.q * d.zeta / 50 := by
  rcases hnonneg with ⟨hu, hR, hv, hC, he, hf, hg, hh⟩
  rcases hcore with ⟨hslo, hshi, hm, hd, hz⟩
  dsimp [sigma, m, delta, zeta] at hslo hshi hm hd hz
  have hsquare : 2 * d.g * d.h ≤ d.zeta ^ 2 / 2 := by
    dsimp [zeta]
    nlinarith [sq_nonneg (d.g - d.h)]
  have hz0 : 0 ≤ d.zeta := by dsimp [zeta]; linarith
  have hz' : d.zeta ≤ 1 / 25 * d.q := by
    dsimp [zeta]
    exact hz
  have hqz : d.zeta ^ 2 / 2 ≤ d.q * d.zeta / 50 := by
    norm_num at hz' ⊢
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz')]
  exact hsquare.trans hqz

lemma FB_le_X_add_two_ef (d : Local) (h : 2 * d.g * d.h ≤ d.beta * d.zeta) :
    d.FB ≤ d.X + 2 * d.e * d.f := by
  dsimp [FB, Q]
  linarith

lemma L_quarter_sub_m_ge_q_over_25 (d : Local) (hcore : d.Core) :
    d.q / 25 ≤ d.L / 4 - d.m := by
  rcases hcore with ⟨hslo, hshi, hm, hd, hz⟩
  dsimp [sigma, m, delta, zeta] at hslo hshi hm hd hz
  dsimp [L, sigma, m]
  norm_num at hslo hshi hm hd hz ⊢
  linarith

lemma large_defect_Q_lt_delta_q_over_25 (d : Local) (hq : 0 < d.q)
    (hnonneg : d.Nonnegative) (hcore : d.Core)
    (hlarge : d.beta * d.zeta < d.Q) :
    d.Q < d.delta * d.q / 25 := by
  rcases hnonneg with ⟨hu, hR, hv, hC, he, hf, hg, hh⟩
  rcases hcore with ⟨hslo, hshi, hm, hd, hz⟩
  have hbasic := basic d hq ⟨hslo, hshi, hm, hd, hz⟩
  have halpha : 43 / 100 * d.q ≤ d.alpha := hbasic.1
  have hbeta : 11 / 25 * d.q ≤ d.beta := hbasic.2.1
  have hqgh := two_gh_le_q_zeta_over_fifty d ⟨hu, hR, hv, hC, he, hf, hg, hh⟩
    ⟨hslo, hshi, hm, hd, hz⟩
  have hef : 2 * d.e * d.f ≤ d.delta ^ 2 / 2 := by
    dsimp [delta]
    nlinarith [sq_nonneg (d.e - d.f)]
  have hQsplit : d.Q = 2 * d.e * d.f + 2 * d.g * d.h := by rfl
  have hz0 : 0 ≤ d.zeta := by dsimp [zeta]; linarith
  have hd0 : 0 ≤ d.delta := by dsimp [delta]; linarith
  have hq0 : 0 ≤ d.q := le_of_lt hq
  have hbeta_zeta : 11 / 25 * d.q * d.zeta ≤ d.beta * d.zeta := by
    exact mul_le_mul_of_nonneg_right hbeta hz0
  have h_ef_big : 21 / 50 * d.q * d.zeta < 2 * d.e * d.f := by
    norm_num at hbeta_zeta hqgh ⊢
    nlinarith
  have hz_small : d.q * d.zeta / 50 < d.delta ^ 2 / 42 := by
    norm_num at h_ef_big hef ⊢
    nlinarith
  have hQsmall : d.Q < 11 / 21 * d.delta ^ 2 := by
    rw [hQsplit]
    norm_num at hqgh hz_small hef ⊢
    linarith
  have hdelta_sq : d.delta ^ 2 ≤ 9 / 200 * d.q * d.delta := by
    norm_num at hd ⊢
    simpa [pow_two] using mul_le_mul_of_nonneg_right hd hd0
  norm_num at hQsmall hdelta_sq ⊢
  nlinarith

lemma large_defect_affordable (d : Local) (hq : 0 < d.q)
    (hnonneg : d.Nonnegative) (hcore : d.Core)
    (hlarge : d.beta * d.zeta < d.Q) :
    d.Q ≤ d.delta * (d.L / 4 - d.m) := by
  have hsmall := large_defect_Q_lt_delta_q_over_25 d hq hnonneg hcore hlarge
  have hmargin := L_quarter_sub_m_ge_q_over_25 d hcore
  rcases hnonneg with ⟨hu, hR, hv, hC, he, hf, hg, hh⟩
  have hd0 : 0 ≤ d.delta := by dsimp [delta]; linarith
  have hmul := mul_le_mul_of_nonneg_left hmargin hd0
  nlinarith

/-- Paper `prop:caseB`, Step 1 (S51): `Q > αδ` forces `gh > 0`. -/
lemma gh_pos_of_Q_gt_alpha_delta (d : Local) (hq : 0 < d.q)
    (hnonneg : d.Nonnegative) (hcore : d.Core)
    (hlarge : d.alpha * d.delta < d.Q) : 0 < d.g * d.h := by
  rcases hnonneg with ⟨hu, hR, hv, hC, he, hf, hg, hh⟩
  have hbasic := basic d hq hcore
  have halpha : 43 / 100 * d.q ≤ d.alpha := hbasic.1
  have hd0 : 0 ≤ d.delta := by dsimp [delta]; linarith
  have hef : 2 * d.e * d.f ≤ d.delta ^ 2 / 2 := by
    dsimp [delta]
    nlinarith [sq_nonneg (d.e - d.f)]
  have hdelta_sq : d.delta ^ 2 ≤ 9 / 200 * d.q * d.delta := by
    have hd := hcore.2.2.2.1
    simpa [pow_two] using mul_le_mul_of_nonneg_right hd hd0
  by_contra hnot
  have hgh0 : d.g * d.h = 0 :=
    le_antisymm (le_of_not_gt hnot) (mul_nonneg hg hh)
  have hQ : d.Q = 2 * d.e * d.f := by
    dsimp [Q]
    rcases mul_eq_zero.mp hgh0 with hg0 | hh0
    · simp [hg0]
    · simp [hh0]
  rw [hQ] at hlarge
  norm_num at halpha hdelta_sq ⊢
  nlinarith

lemma nat_sum_ge_two_of_product_pos (g h : ℕ) (hprod : 0 < g * h) :
    2 ≤ g + h := by
  have hg : 0 < g := Nat.pos_of_ne_zero (by
    intro hz
    simp [hz] at hprod)
  have hh : 0 < h := Nat.pos_of_ne_zero (by
    intro hz
    simp [hz] at hprod)
  omega

/-- Paper `eq:B29`, the integrality step: positive natural defects `g, h` give
`ζ = g + h ≥ 2`. -/
lemma zeta_ge_two_of_natural_defects (g h : ℕ) (hprod : 0 < g * h) :
    (2 : ℚ) ≤ (g : ℚ) + h := by
  exact_mod_cast nat_sum_ge_two_of_product_pos g h hprod

lemma penalty_ge_zeta_beta_sub_zeta (d : Local) (hnonneg : d.Nonnegative)
    (hdelta : d.delta ≤ d.alpha) (hzeta : d.zeta ≤ d.beta) :
    d.zeta * (d.beta - d.zeta) ≤
      d.alpha * d.delta + d.beta * d.zeta - 2 * d.Q := by
  have htw := two_Q_le_squares d
  have hsq := squares_le_weighted d hnonneg hdelta hzeta
  have hd0 : 0 ≤ d.delta := by
    rcases hnonneg with ⟨hu, hR, hv, hC, he, hf, hg, hh⟩
    dsimp [delta]
    linarith
  have hdelta_sq : d.delta ^ 2 ≤ d.alpha * d.delta := by
    simpa [pow_two] using mul_le_mul_of_nonneg_right hdelta hd0
  rw [show d.zeta * (d.beta - d.zeta) = d.beta * d.zeta - d.zeta ^ 2 by ring]
  nlinarith

lemma beta_minus_two_le_half_zeta_beta_sub_zeta (d : Local)
    (hzeta2 : 2 ≤ d.zeta) (hgap : 2 ≤ d.beta - d.zeta) :
    d.beta - 2 ≤ d.zeta * (d.beta - d.zeta) / 2 := by
  have hprod : 0 ≤ (d.zeta - 2) * (d.beta - d.zeta - 2) :=
    mul_nonneg (sub_nonneg.mpr hzeta2) (sub_nonneg.mpr hgap)
  nlinarith

lemma min_FB_FW_le_average (d : Local) :
    min d.FB d.FW ≤
      (d.X + d.Y) / 2 -
        (d.alpha * d.delta + d.beta * d.zeta - 2 * d.Q) / 2 := by
  have hleft : min d.FB d.FW ≤ d.FB := min_le_left _ _
  have hright : min d.FB d.FW ≤ d.FW := min_le_right _ _
  dsimp [FB, FW] at hleft hright ⊢
  linarith

lemma min_FB_FW_le_average_sub_beta_minus_two (d : Local)
    (hnonneg : d.Nonnegative) (hdelta : d.delta ≤ d.alpha)
    (hzeta : d.zeta ≤ d.beta) (hzeta2 : 2 ≤ d.zeta)
    (hgap : 2 ≤ d.beta - d.zeta) :
    min d.FB d.FW ≤ (d.X + d.Y) / 2 - (d.beta - 2) := by
  have hp := penalty_ge_zeta_beta_sub_zeta d hnonneg hdelta hzeta
  have hmono := beta_minus_two_le_half_zeta_beta_sub_zeta d hzeta2 hgap
  have havg := min_FB_FW_le_average d
  linarith

end Local
end PeaceableQueens.UpperBound.LargeOrderAlgebra

#print axioms PeaceableQueens.UpperBound.LargeOrderAlgebra.Local.basic
#print axioms PeaceableQueens.UpperBound.LargeOrderAlgebra.Local.defect_dichotomy
#print axioms PeaceableQueens.UpperBound.LargeOrderAlgebra.Local.large_defect_affordable
#print axioms PeaceableQueens.UpperBound.LargeOrderAlgebra.Local.gh_pos_of_Q_gt_alpha_delta
#print axioms PeaceableQueens.UpperBound.LargeOrderAlgebra.Local.min_FB_FW_le_average_sub_beta_minus_two
