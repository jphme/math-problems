import PeaceableQueens.LineColouring

/-!
# Machine-checked values

This file verifies, by compiled evaluation (`native_decide`):

* the values `H 1, …, H 20` of the paper's value function (Table 1 of
  *Peaceable queens on even toroidal boards*, `paper/peace_even_torus.tex`;
  `H q` here is the paper's `H(2q)`), and
* complete unconditional instances of Theorem 1, `t (2*q) = H q`, for the
  smallest boards: `t 2 = H 1` and `t 4 = H 2`.  Both bounds are included:
  via `t_eq_lineMax` the value `t n` equals the computable `lineMax n`,
  which enumerates all `2^(4n)` line colourings.

The trusted base is documented by the `#print axioms` commands at the end
(`native_decide` adds `Lean.ofReduceBool` to the usual axioms).
-/

namespace PeaceableQueens

/-! ## Values of `H` (paper Table 1: `H q` is the paper's `H(2q)`) -/

/-- `H(2) = 0`. -/
theorem H_one : H 1 = 0 := by native_decide

/-- `H(4) = 2`. -/
theorem H_two : H 2 = 2 := by native_decide

/-- `H(6) = 4`. -/
theorem H_three : H 3 = 4 := by native_decide

/-- `H(8) = 8`. -/
theorem H_four : H 4 = 8 := by native_decide

/-- `H(10) = 12`. -/
theorem H_five : H 5 = 12 := by native_decide

/-- `H(12) = 18`. -/
theorem H_six : H 6 = 18 := by native_decide

/-- `H(14) = 25`. -/
theorem H_seven : H 7 = 25 := by native_decide

/-- `H(16) = 32`. -/
theorem H_eight : H 8 = 32 := by native_decide

/-- `H(18) = 42`. -/
theorem H_nine : H 9 = 42 := by native_decide

/-- `H(20) = 51`. -/
theorem H_ten : H 10 = 51 := by native_decide

/-- `H(22) = 64`. -/
theorem H_eleven : H 11 = 64 := by native_decide

/-- `H(24) = 74`. -/
theorem H_twelve : H 12 = 74 := by native_decide

/-- `H(26) = 90`. -/
theorem H_thirteen : H 13 = 90 := by native_decide

/-- `H(28) = 101`. -/
theorem H_fourteen : H 14 = 101 := by native_decide

/-- `H(30) = 120`. -/
theorem H_fifteen : H 15 = 120 := by native_decide

/-- `H(32) = 133`. -/
theorem H_sixteen : H 16 = 133 := by native_decide

/-- `H(34) = 153`. -/
theorem H_seventeen : H 17 = 153 := by native_decide

/-- `H(36) = 170`. -/
theorem H_eighteen : H 18 = 170 := by native_decide

/-- `H(38) = 190`. -/
theorem H_nineteen : H 19 = 190 := by native_decide

/-- `H(40) = 210`. -/
theorem H_twenty : H 20 = 210 := by native_decide

/-! ## Unconditional instances of Theorem 1

Via `t_eq_lineMax`, the noncomputable `t n` equals the computable
`lineMax n`, so small instances of `t (2*q) = H q` — including the upper
bound — reduce to a finite enumeration of all line colourings. -/

/-- Theorem 1 for `q = 1`: `t 2 = H 1` (both sides are `0`). -/
theorem t_two : t 2 = H 1 := by
  rw [t_eq_lineMax]
  native_decide

/-- Theorem 1 for `q = 2`: `t 4 = H 2` (both sides are `2`).  The
enumeration covers all `2^16` line colourings of the `4 × 4` torus. -/
theorem t_four : t 4 = H 2 := by
  rw [t_eq_lineMax]
  native_decide

/-! ## Trusted base

`native_decide` proofs rely on the compiler: each adds a per-declaration
axiom `<decl>._native.native_decide.ax_1_1` (the `Lean.ofReduceBool`
mechanism) to the usual `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms t_four
#print axioms H_eight

end PeaceableQueens
