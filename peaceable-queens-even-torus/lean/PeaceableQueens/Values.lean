import PeaceableQueens.SmallBoards

/-!
# Optional exact value table

`H q` is the paper's `H(2q)`, Table `tab:Hvals`. This module checks the
entries through order 40 with native computation. The kernel proofs for
`H 1`, `H 2`, `t 2` and `t 4` are in `SmallBoards.lean`. The main endpoint
imports only that smaller module, so the optional table is outside its
source closure and trusted base.
-/

namespace PeaceableQueens

/-! ## Values of `H` (paper Table 1: `H q` is the paper's `H(2q)`) -/

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

/-! ## Trusted base

`native_decide` proofs rely on the compiler: each adds a per-declaration
axiom `<decl>._native.native_decide.ax_1_1` (the `Lean.ofReduceBool`
mechanism) to the usual `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms t_four
#print axioms H_eight

end PeaceableQueens
