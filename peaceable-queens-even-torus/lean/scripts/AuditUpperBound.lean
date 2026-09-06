import PeaceableQueens.Main

/-!
Final endpoint audit. Run only after every generated certificate has been
built sequentially. Keep its complete output in a log: the per-declaration
native-decision axioms are intentionally printed with fully qualified names.
-/

set_option pp.fullNames true

example : ∀ q : Nat, 0 < q → PeaceableQueens.t (2 * q) ≤ PeaceableQueens.H q :=
  PeaceableQueens.upperBoundStatement

example : ∀ q : Nat, 0 < q → PeaceableQueens.t (2 * q) = PeaceableQueens.H q :=
  PeaceableQueens.evenTorusTheorem

#print axioms PeaceableQueens.upperBoundStatement
#print axioms PeaceableQueens.evenTorusTheorem
