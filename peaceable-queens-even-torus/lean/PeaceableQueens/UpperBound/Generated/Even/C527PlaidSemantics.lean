import PeaceableQueens.UpperBound.CertificateConsequences

namespace PeaceableQueens.UpperBound.Generated.Even

open LeafChecks CertificateConsequences

abbrev ProfileBox := RatBox 8

private theorem plaid_empty_00 {box : ProfileBox}
    (h : checkPlaid (0 : Fin 2) (0 : Fin 2) box = true) :
    ∀ x, box.Contains x → InChamber x → False := by
  intro x hx hc
  have hp := checkPlaid_contains (0 : Fin 2) (0 : Fin 2) box h x hx
  have h0 := hp 0; have h1 := hp 1
  simp [InPlaid, templateValue] at h0 h1
  linarith [hc.1]

private theorem plaid_empty_10 {box : ProfileBox}
    (h : checkPlaid (1 : Fin 2) (0 : Fin 2) box = true) :
    ∀ x, box.Contains x → InChamber x → False := by
  intro x hx hc
  have hp := checkPlaid_contains (1 : Fin 2) (0 : Fin 2) box h x hx
  have h0 := hp 0; have h1 := hp 1
  simp [InPlaid, templateValue] at h0 h1
  linarith [hc.1]

private theorem plaid_empty_11 {box : ProfileBox}
    (h : checkPlaid (1 : Fin 2) (1 : Fin 2) box = true) :
    ∀ x, box.Contains x → InChamber x → False := by
  intro x hx hc
  have hp := checkPlaid_contains (1 : Fin 2) (1 : Fin 2) box h x hx
  have h2 := hp 2; have h3 := hp 3
  simp [InPlaid, templateValue] at h2 h3
  linarith [hc.2.1]

/-- The four archive local labels refine exactly to the released global
semantic interface: only label 1 remains exceptional. -/
theorem c527_local_semantics (p : Nat) (box : ProfileBox)
    (h : (match p with
      | 0 => checkPlaid (0 : Fin 2) (0 : Fin 2) box
      | 1 => checkPlaid (0 : Fin 2) (1 : Fin 2) box
      | 2 => checkPlaid (1 : Fin 2) (0 : Fin 2) box
      | 3 => checkPlaid (1 : Fin 2) (1 : Fin 2) box
      | _ => false) = true) :
    BranchSafe box ∨ PlaidExceptional box := by
  cases p with
  | zero => left; right; exact plaid_empty_00 h
  | succ p => cases p with
    | zero => right; exact checkPlaid_contains _ _ box h
    | succ p => cases p with
      | zero => left; right; exact plaid_empty_10 h
      | succ p => cases p with
        | zero => left; right; exact plaid_empty_11 h
        | succ p => simp at h

#print axioms c527_local_semantics
end PeaceableQueens.UpperBound.Generated.Even
