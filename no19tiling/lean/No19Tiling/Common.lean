/-
Copyright (c) 2026 Jan Philipp Harries. All rights reserved.

Shared definitions for the formalization of the arithmetic of
"No triangle can be cut into nineteen congruent triangles" (no19tiling.tex).

* `Primitive3 x y z`: the gcd of three natural numbers is one.
* `SidesIntegral m x y z`: the rational multiples `m*x, m*y, m*z` are integers
  (this is what boundary integrality, a geometric statement, delivers).
* `scale_int_of_primitive3`: the scale lemma ("the scale factor is an integer").
* `G2Triple`: a primitive positive solution of `c^2 = a^2 + a*b + b^2`
  (a Group-2 tile with a `2π/3` angle opposite `c`), with its basic arithmetic:
  pairwise coprimality, `¬ 3 ∣ c`, and the labeling swap `a ↔ b`.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace No19Tiling

/-! ## Primitive triples and the scale lemma -/

/-- A triple of natural numbers is *primitive* if its greatest common divisor is `1`. -/
def Primitive3 (x y z : ℕ) : Prop := Nat.gcd (Nat.gcd x y) z = 1

/-- Prime-divisor criterion for primitivity: no prime divides all three entries. -/
theorem primitive3_of_prime {x y z : ℕ}
    (h : ∀ q : ℕ, q.Prime → q ∣ x → q ∣ y → q ∣ z → False) : Primitive3 x y z := by
  unfold Primitive3
  apply Nat.Coprime.gcd_eq_one
  apply Nat.coprime_of_dvd
  intro q hq hxy hz
  exact h q hq (hxy.trans (Nat.gcd_dvd_left x y)) (hxy.trans (Nat.gcd_dvd_right x y)) hz

/-- A prime cannot divide two coprime numbers. -/
theorem not_dvd_both_of_coprime {q x y : ℕ} (hq : q.Prime) (h : Nat.Coprime x y)
    (hx : q ∣ x) (hy : q ∣ y) : False :=
  Nat.Prime.not_coprime_iff_dvd.mpr ⟨q, hq, hx, hy⟩ h

/-- If two of the entries are coprime, the triple is primitive. -/
theorem primitive3_of_coprime_left {x y z : ℕ} (h : Nat.Coprime x y) : Primitive3 x y z := by
  unfold Primitive3
  rw [Nat.Coprime.gcd_eq_one h, Nat.gcd_one_left]

/-- The three rational numbers `m*x`, `m*y`, `m*z` are integers. In the paper this is
the output of boundary integrality: the sides of the tiled triangle are `m` times an
integer side vector `(x, y, z)` and are themselves integers. -/
def SidesIntegral (m : ℚ) (x y z : ℕ) : Prop :=
  (∃ n : ℤ, m * x = n) ∧ (∃ n : ℤ, m * y = n) ∧ (∃ n : ℤ, m * z = n)

/-- **Scale lemma** (proof of Lemma `lem:group2`, subsection "The scale factor is an integer";
reused in Lemmas `lem:rowI`, `lem:g1counts`, `lem:shape4`, `lem:shape5`).
If `v = (x, y, z)` is a primitive integer vector and `m` is a rational number with
`m * v_i ∈ ℤ` for all `i`, then `m ∈ ℤ`. The proof is the Bézout argument of the paper. -/
theorem scale_int_of_primitive3 {x y z : ℕ} (hp : Primitive3 x y z) {m : ℚ}
    (hm : SidesIntegral m x y z) : ∃ n : ℤ, m = n := by
  obtain ⟨⟨n1, h1⟩, ⟨n2, h2⟩, ⟨n3, h3⟩⟩ := hm
  set g := Nat.gcd x y
  have e1 : (g : ℤ) = x * Nat.gcdA x y + y * Nat.gcdB x y := Nat.gcd_eq_gcd_ab x y
  have e2 : ((Nat.gcd g z : ℕ) : ℤ) = g * Nat.gcdA g z + z * Nat.gcdB g z :=
    Nat.gcd_eq_gcd_ab g z
  have hp' : Nat.gcd g z = 1 := hp
  rw [hp', e1] at e2
  have e3 : (1 : ℚ) = ((x : ℚ) * Nat.gcdA x y + y * Nat.gcdB x y) * Nat.gcdA g z
      + z * Nat.gcdB g z := by exact_mod_cast e2
  refine ⟨n1 * (Nat.gcdA x y * Nat.gcdA g z) + n2 * (Nat.gcdB x y * Nat.gcdA g z)
    + n3 * Nat.gcdB g z, ?_⟩
  push_cast
  rw [← h1, ← h2, ← h3]
  linear_combination m * e3

/-- Positive version of the scale lemma: a positive rational scale of a primitive vector
with integral multiples is a positive natural number. -/
theorem scale_nat_of_primitive3 {x y z : ℕ} (hp : Primitive3 x y z) {m : ℚ} (hm0 : 0 < m)
    (hm : SidesIntegral m x y z) : ∃ n : ℕ, 0 < n ∧ m = n := by
  obtain ⟨n, rfl⟩ := scale_int_of_primitive3 hp hm
  have hn : 0 < n := by exact_mod_cast hm0
  refine ⟨n.toNat, by omega, ?_⟩
  have : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn.le
  rw [← this]
  push_cast
  rfl

/-! ## Sums of two squares -/

private theorem zmod4_key : ∀ x y : ZMod 4, x ^ 2 + y ^ 2 ≠ 3 := by decide

/-- A sum of two squares is never `≡ 3 (mod 4)`. -/
theorem sq_add_sq_mod_four (x y : ℕ) : (x ^ 2 + y ^ 2) % 4 ≠ 3 := by
  intro h
  apply zmod4_key (x : ZMod 4) (y : ZMod 4)
  have := (ZMod.natCast_eq_natCast_iff' (x ^ 2 + y ^ 2) 3 4).mpr (by simpa using h)
  push_cast at this
  exact this

/-! ## Primitive Group-2 triples -/

/-- A primitive positive solution of `c^2 = a^2 + a*b + b^2`: the side lengths of a
Group-2 tile (angle `2π/3` opposite `c`), scaled to coprime integers
(Lemma `lem:group2`, equation `eq:norm`). -/
structure G2Triple where
  a : ℕ
  b : ℕ
  c : ℕ
  ha : 0 < a
  hb : 0 < b
  norm : c ^ 2 = a ^ 2 + a * b + b ^ 2
  prim : Nat.gcd (Nat.gcd a b) c = 1

namespace G2Triple

variable (t : G2Triple)

/-- The other labeling of the two acute angles: `(a, b, c) ↦ (b, a, c)`. The hypotheses of
Lemma `lem:group2` are symmetric under this swap, which is how both labelings
`α ↔ β` of Theorem `thm:classification` are covered. -/
def swap : G2Triple where
  a := t.b
  b := t.a
  c := t.c
  ha := t.hb
  hb := t.ha
  norm := by rw [t.norm]; ring
  prim := by rw [Nat.gcd_comm t.b t.a]; exact t.prim

@[simp] theorem swap_a : t.swap.a = t.b := rfl
@[simp] theorem swap_b : t.swap.b = t.a := rfl
@[simp] theorem swap_c : t.swap.c = t.c := rfl
@[simp] theorem swap_swap : t.swap.swap = t := rfl

theorem c_pos : 0 < t.c := by
  have h := t.norm
  have ha := t.ha
  rcases Nat.eq_zero_or_pos t.c with h0 | h0
  · rw [h0] at h; nlinarith
  · exact h0

/-- No prime divides all of `a, b, c`. -/
theorem no_common_prime {q : ℕ} (hq : q.Prime) (hqa : q ∣ t.a) (hqb : q ∣ t.b)
    (hqc : q ∣ t.c) : False := by
  have h1 : q ∣ Nat.gcd (Nat.gcd t.a t.b) t.c := Nat.dvd_gcd (Nat.dvd_gcd hqa hqb) hqc
  rw [t.prim] at h1
  exact hq.one_lt.ne' (Nat.dvd_one.mp h1)

/-- Pairwise coprimality, `gcd(a, b) = 1` (proof of Lemma `lem:group2`, first paragraph). -/
theorem coprime_ab : Nat.Coprime t.a t.b := by
  apply Nat.coprime_of_dvd
  intro q hq hqa hqb
  apply t.no_common_prime hq hqa hqb
  apply hq.dvd_of_dvd_pow (n := 2)
  rw [t.norm]
  exact dvd_add (dvd_add (dvd_pow hqa two_ne_zero) (dvd_mul_of_dvd_left hqa _))
    (dvd_pow hqb two_ne_zero)

/-- Pairwise coprimality, `gcd(a, c) = 1`. -/
theorem coprime_ac : Nat.Coprime t.a t.c := by
  apply Nat.coprime_of_dvd
  intro q hq hqa hqc
  apply t.no_common_prime hq hqa _ hqc
  apply hq.dvd_of_dvd_pow (n := 2)
  have h1 : q ∣ t.c ^ 2 := dvd_pow hqc two_ne_zero
  rw [t.norm] at h1
  exact (Nat.dvd_add_right (dvd_add (dvd_pow hqa two_ne_zero)
    (dvd_mul_of_dvd_left hqa _))).mp h1

/-- Pairwise coprimality, `gcd(b, c) = 1` (the swap of `coprime_ac`). -/
theorem coprime_bc : Nat.Coprime t.b t.c := t.swap.coprime_ac

/-- Every residue pair modulo `9` with `x^2 + x*y + y^2 ≡ 0` has `3 ∣ x` and `3 ∣ y`
(finite check over the 81 residue pairs). -/
private theorem zmod9_key : ∀ x y : ZMod 9, x ^ 2 + x * y + y ^ 2 = 0 → 3 * x = 0 ∧ 3 * y = 0 := by
  decide

private theorem three_dvd_of_zmod9 {x : ℕ} (h : 3 * (x : ZMod 9) = 0) : 3 ∣ x := by
  have h' : ((3 * x : ℕ) : ZMod 9) = 0 := by push_cast; exact h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (by simpa using h')

/-- `3 ∤ c` (equation `eq:not3`). The paper's argument (reduce mod 3, then mod 9) is
replaced by a finite check of the residues modulo 9. -/
theorem not_three_dvd_c : ¬ 3 ∣ t.c := by
  intro h3
  obtain ⟨s, hs⟩ := h3
  have hn : ((t.a : ZMod 9)) ^ 2 + (t.a : ZMod 9) * t.b + (t.b : ZMod 9) ^ 2 = 0 := by
    have h := congrArg (fun n : ℕ => (n : ZMod 9)) t.norm
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at h
    rw [← h, hs]
    push_cast
    have : (9 : ZMod 9) = 0 := rfl
    linear_combination (s : ZMod 9) ^ 2 * this
  obtain ⟨h1, h2⟩ := zmod9_key _ _ hn
  exact t.no_common_prime Nat.prime_three (three_dvd_of_zmod9 h1) (three_dvd_of_zmod9 h2)
    ⟨s, hs⟩

end G2Triple

end No19Tiling
