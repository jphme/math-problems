/-
Copyright (c) 2026 Jan Philipp Harries. All rights reserved.

Arithmetic of the Group-1 targets (`3α + 2β = π`; Section `sec:group1` of no19tiling.tex).
First the two shapes that Lemmas `lem:g1counts` and `lem:g1residues` treat by counting and
congruences: the *triquadratic* target `(2α, β, α+β)` and the *isosceles-β* target
`(β, β, 3α)`; then the other three shapes (`(α, 2α, 2β)`, Lemma `lem:shape4`, Lemma
`lem:shape5`).

The Group-1 tile, scaled to coprime integers, is `(mk, k^2 - m^2, k^2)` with coprime
`0 < m < k` (`sin(α/2) = m/(2k)`). The target side vectors and counts are taken from the
paper as data (their derivation by the laws of sines and cosines is not formalized):

* triquadratic: sides `j · (m(2k^2-m^2), k(k^2-m^2), k^3)`, count `N = j^2 (2k^2 - m^2)`;
* isosceles-β:  sides `j · (k^3, k^3, m(3k^2-m^2))`,        count `N = j^2 (3k^2 - m^2)`.

Formalized: primitivity of the tile and the two side vectors, integrality of the scale `j`,
`N` prime ⇒ `j = 1`, the residue facts (odd `2k^2-m^2 ≡ ±1 (mod 8)`,
`3k^2 - m^2 ≢ 1 (mod 3)`), and their consequences for primes `p ≡ 3 (mod 8)`,
`p ≡ 1 (mod 3)`, `p ≡ 19 (mod 24)`.

Natural-number subtraction: all differences `x k^2 - m^2` (x = 1, 2, 3) are taken in `ℕ`
under the standing hypothesis `m < k`, so they are the true differences (`G1Param.cast_h`,
`G1Param.cast_g` record this in `ℤ`).
-/
import No19Tiling.Common
import Mathlib.RingTheory.Coprime.Lemmas

namespace No19Tiling

/-- Parameters of a primitive Group-1 tile: coprime naturals `0 < m < k`. -/
structure G1Param where
  m : ℕ
  k : ℕ
  hm : 0 < m
  hmk : m < k
  cop : Nat.Coprime m k

namespace G1Param

variable (P : G1Param)

/-- `h = 2k^2 - m^2` (the triquadratic count factor). -/
def h : ℕ := 2 * P.k ^ 2 - P.m ^ 2

/-- `g = 3k^2 - m^2` (the isosceles-β count factor). -/
def g : ℕ := 3 * P.k ^ 2 - P.m ^ 2

theorem msq_lt_ksq : P.m ^ 2 < P.k ^ 2 := Nat.pow_lt_pow_left P.hmk two_ne_zero

theorem two_le_k : 2 ≤ P.k := by have := P.hm; have := P.hmk; omega

theorem cast_h : (P.h : ℤ) = 2 * (P.k : ℤ) ^ 2 - (P.m : ℤ) ^ 2 := by
  have := P.msq_lt_ksq
  unfold h; rw [Nat.cast_sub (by omega)]; push_cast; ring

theorem cast_g : (P.g : ℤ) = 3 * (P.k : ℤ) ^ 2 - (P.m : ℤ) ^ 2 := by
  have := P.msq_lt_ksq
  unfold g; rw [Nat.cast_sub (by omega)]; push_cast; ring

theorem two_le_h : 2 ≤ P.h := by
  have h1 := P.msq_lt_ksq
  have h2 : 4 ≤ P.k ^ 2 := by have := P.two_le_k; nlinarith
  unfold h; omega

theorem two_le_g : 2 ≤ P.g := by
  have h1 := P.msq_lt_ksq
  have h2 : 4 ≤ P.k ^ 2 := by have := P.two_le_k; nlinarith
  unfold g; omega

/-- A prime dividing `k` and `x k^2 - m^2` divides `m`. -/
private theorem dvd_m_of {q x : ℕ} (hq : q.Prime) (hk : q ∣ P.k) (hx : 1 ≤ x)
    (hd : q ∣ x * P.k ^ 2 - P.m ^ 2) : q ∣ P.m := by
  have hle : P.m ^ 2 ≤ x * P.k ^ 2 := by have := P.msq_lt_ksq; nlinarith
  have h1 : q ∣ x * P.k ^ 2 := dvd_mul_of_dvd_right (dvd_pow hk two_ne_zero) x
  have h2 := Nat.dvd_sub h1 hd
  rw [Nat.sub_sub_self hle] at h2
  exact hq.dvd_of_dvd_pow h2

/-- The Group-1 tile `(mk, k^2 - m^2, k^2)` is primitive. -/
theorem tile_primitive : Primitive3 (P.m * P.k) (P.k ^ 2 - P.m ^ 2) (P.k ^ 2) := by
  apply primitive3_of_prime
  intro q hq _ h2 h3
  have hk : q ∣ P.k := hq.dvd_of_dvd_pow h3
  have hm : q ∣ P.m := P.dvd_m_of hq hk le_rfl (by rw [one_mul]; exact h2)
  exact not_dvd_both_of_coprime hq P.cop hm hk

/-- Triquadratic side vector `(m(2k^2-m^2), k(k^2-m^2), k^3)`. -/
def triVec : ℕ × ℕ × ℕ := (P.m * P.h, P.k * (P.k ^ 2 - P.m ^ 2), P.k ^ 3)

/-- Isosceles-β side vector `(k^3, k^3, m(3k^2-m^2))`. -/
def isoVec : ℕ × ℕ × ℕ := (P.k ^ 3, P.k ^ 3, P.m * P.g)

/-- The triquadratic side vector is primitive. -/
theorem triVec_primitive : Primitive3 P.triVec.1 P.triVec.2.1 P.triVec.2.2 := by
  apply primitive3_of_prime
  intro q hq h1 _ h3
  have hk : q ∣ P.k := hq.dvd_of_dvd_pow h3
  have hm : q ∣ P.m := by
    rcases (Nat.Prime.dvd_mul hq).mp h1 with hm | hh
    · exact hm
    · exact P.dvd_m_of hq hk (by norm_num) hh
  exact not_dvd_both_of_coprime hq P.cop hm hk

/-- The isosceles-β side vector is primitive. -/
theorem isoVec_primitive : Primitive3 P.isoVec.1 P.isoVec.2.1 P.isoVec.2.2 := by
  apply primitive3_of_prime
  intro q hq h1 _ h3
  have hk : q ∣ P.k := hq.dvd_of_dvd_pow h1
  have hm : q ∣ P.m := by
    rcases (Nat.Prime.dvd_mul hq).mp h3 with hm | hg
    · exact hm
    · exact P.dvd_m_of hq hk (by norm_num) hg
  exact not_dvd_both_of_coprime hq P.cop hm hk

end G1Param

/-- If `N = j^2 x` is prime and `x ≥ 2`, then `j = 1`. -/
theorem eq_one_of_prime_sq_mul {j x N : ℕ} (hx : 2 ≤ x) (hN : N = j ^ 2 * x)
    (hp : N.Prime) : j = 1 := by
  rcases Nat.lt_or_ge j 2 with hj | hj
  · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · simp at hN; rw [hN] at hp; exact absurd hp Nat.not_prime_zero
    · rfl
  · exfalso
    rw [hN, show j ^ 2 * x = j * (j * x) by ring] at hp
    exact Nat.not_prime_mul (by omega) (by nlinarith) hp

/-! ## Residues -/

private theorem zmod8_key : ∀ x y : ZMod 8,
    2 * x ^ 2 - (2 * y + 1) ^ 2 = 1 ∨ 2 * x ^ 2 - (2 * y + 1) ^ 2 = 7 := by
  decide

/-- An odd value of `2k^2 - m^2` is `≡ ±1 (mod 8)` (Lemma `lem:g1residues`(a)). -/
theorem two_sq_sub_sq_mod_eight (k m : ℤ) (hodd : (2 * k ^ 2 - m ^ 2) % 2 = 1) :
    (2 * k ^ 2 - m ^ 2) % 8 = 1 ∨ (2 * k ^ 2 - m ^ 2) % 8 = 7 := by
  rcases Int.even_or_odd m with ⟨s, hs⟩ | ⟨s, hs⟩
  · exfalso
    have : 2 * k ^ 2 - m ^ 2 = 2 * (k ^ 2 - 2 * s ^ 2) := by rw [hs]; ring
    rw [this, Int.mul_emod_right] at hodd
    exact absurd hodd (by norm_num)
  · have hz := zmod8_key (k : ZMod 8) (s : ZMod 8)
    have e : ((2 * k ^ 2 - m ^ 2 : ℤ) : ZMod 8) = 2 * (k : ZMod 8) ^ 2 - (2 * (s : ZMod 8) + 1) ^ 2 := by
      rw [hs]; push_cast; ring
    rw [← e] at hz
    rcases hz with hz | hz
    · left
      have := (ZMod.intCast_eq_intCast_iff' (2 * k ^ 2 - m ^ 2) 1 8).mp (by rw [hz]; rfl)
      simpa using this
    · right
      have := (ZMod.intCast_eq_intCast_iff' (2 * k ^ 2 - m ^ 2) 7 8).mp (by rw [hz]; rfl)
      simpa using this

private theorem zmod3_key : ∀ x y : ZMod 3, 3 * x ^ 2 - y ^ 2 ≠ 1 := by
  decide

/-- `3k^2 - m^2` is never `≡ 1 (mod 3)` (Lemma `lem:g1residues`(b)). -/
theorem three_sq_sub_sq_mod_three (k m : ℤ) : (3 * k ^ 2 - m ^ 2) % 3 ≠ 1 := by
  intro h
  apply zmod3_key (k : ZMod 3) (m : ZMod 3)
  have := (ZMod.intCast_eq_intCast_iff' (3 * k ^ 2 - m ^ 2) 1 3).mpr (by simpa using h)
  push_cast at this
  exact this

namespace G1Param

variable (P : G1Param)

/-- A prime of the form `j^2 (2k^2 - m^2)` is not `≡ 3 (mod 8)`. -/
theorem h_count_prime_mod8 {j N : ℕ} (hN : N = j ^ 2 * P.h) (hp : N.Prime) : N % 8 ≠ 3 := by
  have hj := eq_one_of_prime_sq_mul P.two_le_h hN hp
  subst hj
  rw [one_pow, one_mul] at hN
  intro h8
  have hz : (N : ℤ) = 2 * (P.k : ℤ) ^ 2 - (P.m : ℤ) ^ 2 := by rw [hN, P.cast_h]
  have hodd : (2 * (P.k : ℤ) ^ 2 - (P.m : ℤ) ^ 2) % 2 = 1 := by rw [← hz]; omega
  rcases two_sq_sub_sq_mod_eight _ _ hodd with h | h <;> rw [← hz] at h <;> omega

/-- A prime of the form `j^2 (3k^2 - m^2)` is not `≡ 1 (mod 3)`. -/
theorem g_count_prime_mod3 {j N : ℕ} (hN : N = j ^ 2 * P.g) (hp : N.Prime) : N % 3 ≠ 1 := by
  have hj := eq_one_of_prime_sq_mul P.two_le_g hN hp
  subst hj
  rw [one_pow, one_mul] at hN
  intro h3
  have hz : (N : ℤ) = 3 * (P.k : ℤ) ^ 2 - (P.m : ℤ) ^ 2 := by rw [hN, P.cast_g]
  apply three_sq_sub_sq_mod_three P.k P.m
  rw [← hz]; omega

/-- **Triquadratic target.** Let the target sides be `j · triVec` with `j > 0` rational and
integral sides (boundary integrality), and let the count be `N = j^2 (2k^2 - m^2)`.
Then `j` is a positive integer; if `N` is prime then `j = 1`, `N = 2k^2 - m^2`, and
`N ≢ 3 (mod 8)`. -/
theorem triquadratic {j : ℚ} (hj : 0 < j) (hs : SidesIntegral j P.triVec.1 P.triVec.2.1 P.triVec.2.2)
    {N : ℕ} (hN : (N : ℚ) = j ^ 2 * P.h) (hp : N.Prime) :
    j = 1 ∧ N = P.h ∧ N % 8 ≠ 3 := by
  obtain ⟨n, -, rfl⟩ := scale_nat_of_primitive3 P.triVec_primitive hj hs
  have hN' : N = n ^ 2 * P.h := by exact_mod_cast hN
  have hn := eq_one_of_prime_sq_mul P.two_le_h hN' hp
  subst hn
  refine ⟨by norm_num, by simpa using hN', P.h_count_prime_mod8 hN' hp⟩

/-- **Isosceles-β target.** Let the target sides be `j · isoVec` with `j > 0` rational and
integral sides, and let the count be `N = j^2 (3k^2 - m^2)`. Then `j` is a positive integer;
if `N` is prime then `j = 1`, `N = 3k^2 - m^2`, and `N ≢ 1 (mod 3)`. -/
theorem isoBeta {j : ℚ} (hj : 0 < j) (hs : SidesIntegral j P.isoVec.1 P.isoVec.2.1 P.isoVec.2.2)
    {N : ℕ} (hN : (N : ℚ) = j ^ 2 * P.g) (hp : N.Prime) :
    j = 1 ∧ N = P.g ∧ N % 3 ≠ 1 := by
  obtain ⟨n, -, rfl⟩ := scale_nat_of_primitive3 P.isoVec_primitive hj hs
  have hN' : N = n ^ 2 * P.g := by exact_mod_cast hN
  have hn := eq_one_of_prime_sq_mul P.two_le_g hN' hp
  subst hn
  refine ⟨by norm_num, by simpa using hN', P.g_count_prime_mod3 hN' hp⟩

/-- No prime `p ≡ 19 (mod 24)` is a triquadratic count `j^2 (2k^2 - m^2)`. -/
theorem triquadratic_not_19_mod_24 {j N : ℕ} (hN : N = j ^ 2 * P.h) (hp : N.Prime) :
    N % 24 ≠ 19 := by
  have := P.h_count_prime_mod8 hN hp; omega

/-- No prime `p ≡ 19 (mod 24)` is an isosceles-β count `j^2 (3k^2 - m^2)`. -/
theorem isoBeta_not_19_mod_24 {j N : ℕ} (hN : N = j ^ 2 * P.g) (hp : N.Prime) :
    N % 24 ≠ 19 := by
  have := P.g_count_prime_mod3 hN hp; omega

end G1Param

/-! ## The other Group-1 targets (Lemmas `lem:g1counts`(c), `lem:shape4`, `lem:shape5`) -/

namespace G1Param

variable (P : G1Param)

/-- `b = k^2 - m^2`, the middle tile side. -/
def b : ℕ := P.k ^ 2 - P.m ^ 2

theorem b_pos : 0 < P.b := by have := P.msq_lt_ksq; unfold b; omega

theorem h_eq : P.h = P.b + P.k ^ 2 := by
  have := P.msq_lt_ksq; unfold h b; omega

/-- `gcd(k, b) = 1`. -/
theorem coprime_k_b : Nat.Coprime P.k P.b := by
  apply Nat.coprime_of_dvd
  intro q hq hk hb
  exact not_dvd_both_of_coprime hq P.cop (P.dvd_m_of hq hk le_rfl (by rw [one_mul]; exact hb)) hk

/-- `gcd(h, b) = 1`. -/
theorem coprime_h_b : Nat.Coprime P.h P.b := by
  apply Nat.coprime_of_dvd
  intro q hq hh hb
  have hk2 : q ∣ P.k ^ 2 := by rw [P.h_eq] at hh; exact (Nat.dvd_add_right hb).mp hh
  exact not_dvd_both_of_coprime hq P.coprime_k_b (hq.dvd_of_dvd_pow hk2) hb

/-- Side vector of the target `(α, 2α, 2β)`: `(k^4, k^2 h, b g)`. -/
def shape2Vec : ℕ × ℕ × ℕ := (P.k ^ 4, P.k ^ 2 * P.h, P.b * P.g)

theorem shape2Vec_primitive : Primitive3 P.shape2Vec.1 P.shape2Vec.2.1 P.shape2Vec.2.2 := by
  apply primitive3_of_prime
  intro q hq h1 _ h3
  have hk : q ∣ P.k := hq.dvd_of_dvd_pow h1
  have hm : q ∣ P.m := by
    rcases (Nat.Prime.dvd_mul hq).mp h3 with hb | hg
    · exact P.dvd_m_of hq hk le_rfl (by rw [one_mul]; exact hb)
    · exact P.dvd_m_of hq hk (by norm_num) hg
  exact not_dvd_both_of_coprime hq P.cop hm hk

/-- **Target `(α, 2α, 2β)`** (Lemma `lem:g1counts`(c)):
with sides `j · (k^4, k^2 h, b g)` (`j > 0` rational, integral sides) and count
`N = j^2 h g`, `N` is not prime. -/
theorem shape2_not_prime {j : ℚ} (hj : 0 < j)
    (hs : SidesIntegral j P.shape2Vec.1 P.shape2Vec.2.1 P.shape2Vec.2.2)
    {N : ℕ} (hN : (N : ℚ) = j ^ 2 * P.h * P.g) : ¬ N.Prime := by
  obtain ⟨n, hn, rfl⟩ := scale_nat_of_primitive3 P.shape2Vec_primitive hj hs
  have hN' : N = (n ^ 2 * P.h) * P.g := by exact_mod_cast hN
  rw [hN']
  have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  have h2 := P.two_le_h; have h3 := P.two_le_g
  exact Nat.not_prime_mul (by nlinarith) (by omega)

/-- **Target `(α, α, α + 2β)`** (Lemma `lem:shape5`):
sides `t (k^2, k^2, h)`, count `N * b = t^2 h`. If `N` is prime then `N = h`, `t^2 = b`, so
`N = k^2 + t^2` is a sum of two squares and `N ≢ 3 (mod 4)`. -/
theorem shape5_prime {t N : ℕ} (hN : N * P.b = t ^ 2 * P.h) (hp : N.Prime) :
    N = P.h ∧ t ^ 2 = P.b ∧ N = P.k ^ 2 + t ^ 2 := by
  have hhN : P.h ∣ N := by
    have : P.h ∣ N * P.b := ⟨t ^ 2, by rw [hN]; ring⟩
    exact P.coprime_h_b.dvd_of_dvd_mul_right this
  have hNh : N = P.h := by
    rcases (Nat.dvd_prime hp).mp hhN with h1 | h1
    · have := P.two_le_h; omega
    · exact h1.symm
  have htb : t ^ 2 = P.b := by
    rw [hNh] at hN
    have h0 : 0 < P.h := by have := P.two_le_h; omega
    apply Nat.eq_of_mul_eq_mul_left h0
    rw [mul_comm P.h, ← hN, mul_comm]
  refine ⟨hNh, htb, ?_⟩
  rw [hNh, P.h_eq, htb, add_comm]

theorem shape5_not_3_mod_4 {t N : ℕ} (hN : N * P.b = t ^ 2 * P.h) (hp : N.Prime) :
    N % 4 ≠ 3 := by
  obtain ⟨-, -, h⟩ := P.shape5_prime hN hp
  rw [h]; exact sq_add_sq_mod_four _ _

/-- **Target `(α+β, α+β, α)`, arithmetic part** (Lemma `lem:shape4`): sides `t (k, k, m)`,
count `N * b = t^2`, and the base (length `t m`) is a union of `A` a-edges, `B` b-edges and
`C` c-edges: `t m = A (mk) + B b + C k^2`. If `N` is prime, then `C = 0` (indeed `B s = m` with
`t = N s`, and the base consists of b-edges only). The geometric half of Lemma `shape4` (the
γ-angle pigeonhole on the base, not formalized) shows `C ≥ 1`; together, `N` is not prime. -/
theorem shape4_prime_no_c_edge {t N A B C : ℕ} (hN : N * P.b = t ^ 2)
    (hbase : t * P.m = A * (P.m * P.k) + B * P.b + C * P.k ^ 2) (hp : N.Prime) : C = 0 := by
  have hb0 := P.b_pos
  have hk0 : 0 < P.k := by have := P.two_le_k; omega
  have hm0 := P.hm
  have hN0 := hp.pos
  -- N ∣ t, t = N s, b = N s^2
  obtain ⟨s, rfl⟩ : N ∣ t := hp.dvd_of_dvd_pow ⟨P.b, hN.symm⟩
  have hbs : P.b = N * s ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left hN0
    rw [hN]; ring
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h] at hbs; simp at hbs; omega
    · exact h
  -- B s ≤ m, from B b ≤ N s m
  have hBs : B * s ≤ P.m := by
    have h1 : B * P.b ≤ N * s * P.m := by rw [hbase]; omega
    rw [hbs] at h1
    have h2 : (N * s) * (B * s) ≤ (N * s) * P.m := by
      calc (N * s) * (B * s) = B * (N * s ^ 2) := by ring
        _ ≤ N * s * P.m := h1
    exact Nat.le_of_mul_le_mul_left h2 (by positivity)
  -- k ∣ b (m - B s) in ℤ, and gcd(k, b) = 1
  have hdvd : (P.k : ℤ) ∣ (P.b : ℤ) * ((P.m : ℤ) - B * s) := by
    refine ⟨s * (A * P.m + C * P.k), ?_⟩
    have e1 : ((N * s * P.m : ℕ) : ℤ) = ((A * (P.m * P.k) + B * P.b + C * P.k ^ 2 : ℕ) : ℤ) := by
      rw [hbase]
    have e2 : (P.b : ℤ) = N * s ^ 2 := by exact_mod_cast hbs
    push_cast at e1
    linear_combination (s : ℤ) * e1 + (P.m : ℤ) * e2
  have hcop : IsCoprime (P.k : ℤ) (P.b : ℤ) := Nat.isCoprime_iff_coprime.mpr P.coprime_k_b
  have hk : (P.k : ℤ) ∣ (P.m : ℤ) - B * s := hcop.dvd_of_dvd_mul_left hdvd
  have hzero : (P.m : ℤ) - B * s = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hk
    have := P.hmk
    have hBs' : ((B * s : ℕ) : ℤ) ≤ P.m := by exact_mod_cast hBs
    push_cast at hBs'
    rw [abs_lt]; constructor <;> omega
  have hBs2 : B * s = P.m := by
    have : ((B * s : ℕ) : ℤ) = P.m := by push_cast; linarith
    exact_mod_cast this
  -- then B b = N s m, so A m k + C k^2 = 0
  have hBb : B * P.b = N * s * P.m := by
    rw [hbs, ← hBs2]; ring
  have hrest : A * (P.m * P.k) + C * P.k ^ 2 = 0 := by omega
  have hk2 : 0 < P.k ^ 2 := by positivity
  have : C * P.k ^ 2 = 0 := by omega
  rcases Nat.mul_eq_zero.mp this with h | h
  · exact h
  · omega

/-- Lemma `shape4` with its geometric half as a hypothesis: if the base contains at least one
c-edge (`1 ≤ C`), then `N` is not prime. -/
theorem shape4_not_prime {t N A B C : ℕ} (hN : N * P.b = t ^ 2)
    (hbase : t * P.m = A * (P.m * P.k) + B * P.b + C * P.k ^ 2) (hC : 1 ≤ C) : ¬ N.Prime :=
  fun hp => by have := P.shape4_prime_no_c_edge hN hbase hp; omega

/-- The shape-4 side vector `(k, k, m)` is primitive. -/
theorem shape4Vec_primitive : Primitive3 P.k P.k P.m := by
  unfold Primitive3; rw [Nat.gcd_self]; exact P.cop.symm

/-- Lemma `shape4` with a rational scale: sides `t (k, k, m)` with `t > 0` rational and integral
sides, count `N b = t^2`, base decomposition with `C ≥ 1` c-edges. Then `N` is not prime. -/
theorem shape4_not_prime_rat {t : ℚ} (ht : 0 < t) (hs : SidesIntegral t P.k P.k P.m)
    {N A B C : ℕ} (hN : (N : ℚ) * P.b = t ^ 2)
    (hbase : t * P.m = A * (P.m * P.k) + B * P.b + C * P.k ^ 2) (hC : 1 ≤ C) : ¬ N.Prime := by
  obtain ⟨n, -, rfl⟩ := scale_nat_of_primitive3 P.shape4Vec_primitive ht hs
  exact P.shape4_not_prime (t := n) (by exact_mod_cast hN) (by exact_mod_cast hbase) hC

/-- The shape-5 side vector `(k^2, k^2, h)` is primitive. -/
theorem shape5Vec_primitive : Primitive3 (P.k ^ 2) (P.k ^ 2) P.h := by
  unfold Primitive3; rw [Nat.gcd_self]
  apply Nat.coprime_of_dvd
  intro q hq hk2 hh
  have hk := hq.dvd_of_dvd_pow hk2
  exact not_dvd_both_of_coprime hq P.cop (P.dvd_m_of hq hk (by norm_num) hh) hk

/-- Lemma `shape5`(a) with a rational scale: sides `t (k^2, k^2, h)` with `t > 0` rational and
integral sides, count `N b = t^2 h`. A prime `N` is `≢ 3 (mod 4)`. -/
theorem shape5_not_3_mod_4_rat {t : ℚ} (ht : 0 < t) (hs : SidesIntegral t (P.k ^ 2) (P.k ^ 2) P.h)
    {N : ℕ} (hN : (N : ℚ) * P.b = t ^ 2 * P.h) (hp : N.Prime) : N % 4 ≠ 3 := by
  obtain ⟨n, -, rfl⟩ := scale_nat_of_primitive3 P.shape5Vec_primitive ht hs
  exact P.shape5_not_3_mod_4 (t := n) (by exact_mod_cast hN) hp

end G1Param

end No19Tiling
