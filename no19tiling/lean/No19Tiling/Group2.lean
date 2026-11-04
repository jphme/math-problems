/-
Copyright (c) 2026 Jan Philipp Harries. All rights reserved.

Arithmetic content of Lemma `lem:group2` of no19tiling.tex (Section `sec:lemma`):
a Group-2 target (tile with a `2π/3` angle, primitive integer sides `(a, b, c)`) in one of
the four scalene configurations A-D never has a prime tile count.

Formalized here: primitivity of the four side vectors, integrality of the scale factor
(via `scale_nat_of_primitive3`), and non-primality of the four count formulas.
Taken from the paper as hypotheses (geometry/trigonometry, not formalized):
the side vector of each case, the count formula of each case (area ratio), and
boundary integrality (the sides of the tiled triangle are integers).
-/
import No19Tiling.Common

namespace No19Tiling

namespace G2Triple

variable (t : G2Triple)

/-! ## The four side vectors are primitive -/

/-- Case A side vector `(c^2, c(a+2b), 3b(a+b))` is primitive. -/
theorem primitive_A : Primitive3 (t.c ^ 2) (t.c * (t.a + 2 * t.b)) (3 * t.b * (t.a + t.b)) := by
  apply primitive3_of_prime
  intro q hq h1 _ h3
  have hqc : q ∣ t.c := hq.dvd_of_dvd_pow h1
  rcases (Nat.Prime.dvd_mul hq).mp h3 with h3 | h3
  · rcases (Nat.Prime.dvd_mul hq).mp h3 with h3 | h3
    · -- q ∣ 3, so q = 3, contradicting 3 ∤ c
      have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
      subst this
      exact t.not_three_dvd_c hqc
    · exact not_dvd_both_of_coprime hq t.coprime_bc h3 hqc
  · -- q ∣ a + b; then c^2 = a(a+b) + b^2 gives q ∣ b
    have hb : q ∣ t.b := by
      apply hq.dvd_of_dvd_pow (n := 2)
      have e : t.c ^ 2 = t.a * (t.a + t.b) + t.b ^ 2 := by rw [t.norm]; ring
      have h := dvd_pow hqc (two_ne_zero)
      rw [e] at h
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_right h3 _)).mp h
    exact not_dvd_both_of_coprime hq t.coprime_bc hb hqc

/-- Case B side vector `(ac, b(2a+b), c(a+b))` is primitive. -/
theorem primitive_B : Primitive3 (t.a * t.c) (t.b * (2 * t.a + t.b)) (t.c * (t.a + t.b)) := by
  apply primitive3_of_prime
  intro q hq h1 h2 _
  have nab : ¬ (q ∣ t.a ∧ q ∣ t.b) := fun h => not_dvd_both_of_coprime hq t.coprime_ab h.1 h.2
  have nac : ¬ (q ∣ t.a ∧ q ∣ t.c) := fun h => not_dvd_both_of_coprime hq t.coprime_ac h.1 h.2
  have nbc : ¬ (q ∣ t.b ∧ q ∣ t.c) := fun h => not_dvd_both_of_coprime hq t.coprime_bc h.1 h.2
  rcases (Nat.Prime.dvd_mul hq).mp h1 with ha | hc
  · -- q ∣ a: then q ∤ b, so q ∣ 2a + b, so q ∣ b
    rcases (Nat.Prime.dvd_mul hq).mp h2 with hb | hV
    · exact nab ⟨ha, hb⟩
    · exact nab ⟨ha, (Nat.dvd_add_right (dvd_mul_of_dvd_right ha 2)).mp hV⟩
  · rcases (Nat.Prime.dvd_mul hq).mp h2 with hb | hV
    · exact nbc ⟨hb, hc⟩
    · -- c^2 + a(2a+b) = 3a^2 + b(2a+b), so q ∣ 3a^2
      have e : t.c ^ 2 + t.a * (2 * t.a + t.b) = 3 * t.a ^ 2 + t.b * (2 * t.a + t.b) := by
        rw [t.norm]; ring
      have h : q ∣ 3 * t.a ^ 2 := by
        have h' : q ∣ t.c ^ 2 + t.a * (2 * t.a + t.b) :=
          dvd_add (dvd_pow hc two_ne_zero) (dvd_mul_of_dvd_right hV _)
        rw [e] at h'
        exact (Nat.dvd_add_left (dvd_mul_of_dvd_right hV _)).mp h'
      rcases (Nat.Prime.dvd_mul hq).mp h with h3 | ha2
      · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
        subst this
        exact t.not_three_dvd_c hc
      · exact nac ⟨hq.dvd_of_dvd_pow ha2, hc⟩

/-- Case C side vector `(a, c, a+b)` is primitive (since `gcd(a, c) = 1`). -/
theorem primitive_C : Primitive3 t.a t.c (t.a + t.b) :=
  primitive3_of_coprime_left t.coprime_ac

/-- Case D side vector `(a(a+2b), b(2a+b), c^2)` is primitive. -/
theorem primitive_D :
    Primitive3 (t.a * (t.a + 2 * t.b)) (t.b * (2 * t.a + t.b)) (t.c ^ 2) := by
  apply primitive3_of_prime
  intro q hq h1 h2 h3
  have hqc : q ∣ t.c := hq.dvd_of_dvd_pow h3
  have nac : ¬ q ∣ t.a := fun h => not_dvd_both_of_coprime hq t.coprime_ac h hqc
  have nbc : ¬ q ∣ t.b := fun h => not_dvd_both_of_coprime hq t.coprime_bc h hqc
  have hU : q ∣ t.a + 2 * t.b := ((Nat.Prime.dvd_mul hq).mp h1).resolve_left nac
  have hV : q ∣ 2 * t.a + t.b := ((Nat.Prime.dvd_mul hq).mp h2).resolve_left nbc
  -- 2(a+2b) = (2a+b) + 3b
  have h3b : q ∣ 3 * t.b := by
    have e : 2 * (t.a + 2 * t.b) = (2 * t.a + t.b) + 3 * t.b := by ring
    have h := dvd_mul_of_dvd_right hU 2
    rw [e] at h
    exact (Nat.dvd_add_right hV).mp h
  rcases (Nat.Prime.dvd_mul hq).mp h3b with h3 | hb
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3
    subst this
    exact t.not_three_dvd_c hqc
  · exact nbc hb

/-! ## The four tile counts are not prime -/

/-- Case A: `3 m^2 (a+2b)(a+b)` is not prime for `m ≥ 1`. -/
theorem countA_not_prime {m : ℕ} (hm : 0 < m) :
    ¬ (3 * m ^ 2 * (t.a + 2 * t.b) * (t.a + t.b)).Prime := by
  have ha := t.ha; have hb := t.hb
  have : 1 < m ^ 2 * (t.a + 2 * t.b) * (t.a + t.b) := by
    have h1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 (show 3 ≤ t.a + 2 * t.b by omega))
      (show 2 ≤ t.a + t.b by omega)
    linarith
  rw [show 3 * m ^ 2 * (t.a + 2 * t.b) * (t.a + t.b)
      = 3 * (m ^ 2 * (t.a + 2 * t.b) * (t.a + t.b)) by ring]
  exact Nat.not_prime_mul (by norm_num) this.ne'

/-- Case B: `m^2 (2a+b)(a+b)` is not prime for `m ≥ 1`. -/
theorem countB_not_prime {m : ℕ} (hm : 0 < m) :
    ¬ (m ^ 2 * (2 * t.a + t.b) * (t.a + t.b)).Prime := by
  have ha := t.ha; have hb := t.hb
  have : 1 < m ^ 2 * (2 * t.a + t.b) := by
    have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
    nlinarith
  exact Nat.not_prime_mul this.ne' (by omega)

/-- Case D: `m^2 (a+2b)(2a+b)` is not prime for `m ≥ 1`. -/
theorem countD_not_prime {m : ℕ} (hm : 0 < m) :
    ¬ (m ^ 2 * (t.a + 2 * t.b) * (2 * t.a + t.b)).Prime := by
  have ha := t.ha; have hb := t.hb
  have : 1 < m ^ 2 * (t.a + 2 * t.b) := by
    have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
    nlinarith
  exact Nat.not_prime_mul this.ne' (by omega)

/-- Case C: if `N * b = m^2 (a+b)` then `N` is not prime (proof of Lemma `lem:group2`, "Conclusion", case C).
This uses the norm equation: a prime `N` would equal `a + b`, and then
`c^2 ≡ a^2 (mod a+b)` forces `c = a` or `c = b`, both impossible. -/
theorem countC_not_prime {m N : ℕ} (hN : N * t.b = m ^ 2 * (t.a + t.b)) : ¬ N.Prime := by
  intro hp
  have ha := t.ha; have hb := t.hb
  -- b ∣ m^2, since gcd(b, a+b) = 1
  have hcop : Nat.Coprime t.b (t.a + t.b) := by
    have : Nat.Coprime t.b t.a := t.coprime_ab.symm
    simpa [Nat.coprime_add_self_right, add_comm] using this
  have hdvd : t.b ∣ m ^ 2 * (t.a + t.b) := ⟨N, by rw [← hN, mul_comm]⟩
  obtain ⟨r, hr⟩ := (Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd)
  have hNr : N = r * (t.a + t.b) := by
    rw [hr] at hN
    have : N * t.b = (r * (t.a + t.b)) * t.b := by rw [hN]; ring
    exact Nat.eq_of_mul_eq_mul_right hb this
  -- N = r (a+b) prime and a + b ≥ 2 force r = 1
  have hpab : N = t.a + t.b := by
    rw [hNr] at hp
    rcases Nat.prime_mul_iff.mp hp with h | h
    · omega
    · rw [hNr, h.2, one_mul]
  -- now (c - a)(c + a) = b (a + b) = b N in ℤ
  have hpZ : Prime (N : ℤ) := Nat.prime_iff_prime_int.mp hp
  have key : ((t.c : ℤ) - t.a) * ((t.c : ℤ) + t.a) = t.b * N := by
    have h := t.norm
    rw [hpab]; push_cast
    have h' : (t.c : ℤ) ^ 2 = (t.a : ℤ) ^ 2 + t.a * t.b + t.b ^ 2 := by exact_mod_cast h
    linear_combination h'
  have hdv : (N : ℤ) ∣ ((t.c : ℤ) - t.a) * ((t.c : ℤ) + t.a) := ⟨t.b, by rw [key]; ring⟩
  -- c < N
  have hcN : t.c < N := by
    have : t.c ^ 2 < (t.a + t.b) ^ 2 := by rw [t.norm]; nlinarith
    rw [hpab]; exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
  have hc := t.c_pos
  rcases hpZ.dvd_or_dvd hdv with h | h
  · -- N ∣ c - a with |c - a| < N, so c = a, impossible
    have h0 : (t.c : ℤ) - t.a = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h
      rw [abs_lt]; constructor <;> omega
    have hca : (t.c : ℤ) = t.a := by linarith
    have h' : (t.c : ℤ) ^ 2 = (t.a : ℤ) ^ 2 + t.a * t.b + t.b ^ 2 := by exact_mod_cast t.norm
    rw [hca] at h'
    nlinarith
  · -- N ∣ c + a with 0 < c + a < 2N, so c + a = N = a + b, c = b, impossible
    obtain ⟨s, hs⟩ := h
    have hs1 : s = 1 := by
      have h1 : 0 < (N : ℤ) * s := by rw [← hs]; positivity
      have h2 : (N : ℤ) * s < N * 2 := by rw [← hs]; omega
      have hN0 : (0 : ℤ) < N := by exact_mod_cast hp.pos
      have := pos_of_mul_pos_right h1 hN0.le
      have := lt_of_mul_lt_mul_left h2 hN0.le
      omega
    rw [hs1, mul_one, hpab] at hs
    push_cast at hs
    have hcb : (t.c : ℤ) = t.b := by linarith
    have h' : (t.c : ℤ) ^ 2 = (t.a : ℤ) ^ 2 + t.a * t.b + t.b ^ 2 := by exact_mod_cast t.norm
    rw [hcb] at h'
    have ha' : (0 : ℤ) < t.a := by exact_mod_cast ha
    nlinarith

/-! ## Lemma `lem:group2`, as a single statement over the four cases -/

/-- The four scalene Group-2 configurations of Lemma `lem:group2`
(Theorem `thm:classification`, Group 2): target angles
A `(α, 2α, 3β)`, B `(α, 2β, 2α+β)`, C `(α, α+β, α+2β)`, D `(2α, 2β, α+β)`. -/
inductive Case
  | A | B | C | D
  deriving DecidableEq

/-- The primitive integer side vector of the target in each case (table in the proof of
Lemma `lem:group2`). Taken from the paper; derived there from the laws of sines/cosines. -/
def sideVec : Case → ℕ × ℕ × ℕ
  | .A => (t.c ^ 2, t.c * (t.a + 2 * t.b), 3 * t.b * (t.a + t.b))
  | .B => (t.a * t.c, t.b * (2 * t.a + t.b), t.c * (t.a + t.b))
  | .C => (t.a, t.c, t.a + t.b)
  | .D => (t.a * (t.a + 2 * t.b), t.b * (2 * t.a + t.b), t.c ^ 2)

/-- The tile count `N` for target scale `m` in each case (table in the proof of
Lemma `lem:group2`; the ratio of areas). Case C is stated as `N * b = m^2 (a+b)`. -/
def countEq (m : ℚ) (N : ℕ) : Case → Prop
  | .A => (N : ℚ) = 3 * m ^ 2 * (t.a + 2 * t.b) * (t.a + t.b)
  | .B => (N : ℚ) = m ^ 2 * (2 * t.a + t.b) * (t.a + t.b)
  | .C => (N : ℚ) * t.b = m ^ 2 * (t.a + t.b)
  | .D => (N : ℚ) = m ^ 2 * (t.a + 2 * t.b) * (2 * t.a + t.b)

theorem sideVec_primitive : ∀ X : Case,
    Primitive3 (t.sideVec X).1 (t.sideVec X).2.1 (t.sideVec X).2.2
  | .A => t.primitive_A
  | .B => t.primitive_B
  | .C => t.primitive_C
  | .D => t.primitive_D

/-- **Lemma `lem:group2`, arithmetic content.** Let `(a, b, c)` be a primitive Group-2
triple, let the target be in case `X ∈ {A, B, C, D}`, and let `m > 0` be the rational scale
from the side vector of case `X` to the actual target sides. If those sides are integers
(boundary integrality) and `N` is the tile count given by the count formula of case `X`,
then `N` is not prime. -/
theorem lem_group2 (X : Case) {m : ℚ} (hm : 0 < m)
    (hsides : SidesIntegral m (t.sideVec X).1 (t.sideVec X).2.1 (t.sideVec X).2.2)
    {N : ℕ} (hN : t.countEq m N X) : ¬ N.Prime := by
  obtain ⟨n, hn, rfl⟩ := scale_nat_of_primitive3 (t.sideVec_primitive X) hm hsides
  cases X with
  | A =>
    simp only [countEq] at hN
    have : N = 3 * n ^ 2 * (t.a + 2 * t.b) * (t.a + t.b) := by exact_mod_cast hN
    rw [this]; exact t.countA_not_prime hn
  | B =>
    simp only [countEq] at hN
    have : N = n ^ 2 * (2 * t.a + t.b) * (t.a + t.b) := by exact_mod_cast hN
    rw [this]; exact t.countB_not_prime hn
  | C =>
    simp only [countEq] at hN
    have : N * t.b = n ^ 2 * (t.a + t.b) := by exact_mod_cast hN
    exact t.countC_not_prime this
  | D =>
    simp only [countEq] at hN
    have : N = n ^ 2 * (t.a + 2 * t.b) * (2 * t.a + t.b) := by exact_mod_cast hN
    rw [this]; exact t.countD_not_prime hn

/-- **Both labelings.** Lemma `lem:group2` holds for the triple and for its swap
`(b, a, c)`, i.e. for both readings `α ↔ β` of the Group-2 angle triples. -/
theorem lem_group2_both_labelings :
    (∀ (X : Case) {m : ℚ}, 0 < m →
      SidesIntegral m (t.sideVec X).1 (t.sideVec X).2.1 (t.sideVec X).2.2 →
      ∀ {N : ℕ}, t.countEq m N X → ¬ N.Prime) ∧
    (∀ (X : Case) {m : ℚ}, 0 < m →
      SidesIntegral m (t.swap.sideVec X).1 (t.swap.sideVec X).2.1 (t.swap.sideVec X).2.2 →
      ∀ {N : ℕ}, t.swap.countEq m N X → ¬ N.Prime) :=
  ⟨fun X _ hm hs _ hN => t.lem_group2 X hm hs hN,
   fun X _ hm hs _ hN => t.swap.lem_group2 X hm hs hN⟩

end G2Triple

end No19Tiling
