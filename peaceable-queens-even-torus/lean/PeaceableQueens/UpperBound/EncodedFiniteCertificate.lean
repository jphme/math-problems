import PeaceableQueens.UpperBound.FiniteCutTable
import PeaceableQueens.UpperBound.CachedFiniteChecker
import PeaceableQueens.UpperBound.FastFiniteTables

/-!
# Compact finite action certificates

A certificate is an ASCII string of three-hex-digit natural-number tokens.
The decoder reads its UTF-8 bytes with a cursor, without materializing lists
of characters or tokens. Decoding creates an ordinary `Action`
tree; the existing propagation, splitting, and discharge checker then checks
that tree in full.  Neither the string nor the decoder is an assertion of
coverage.  Malformed input, exhausted fuel, and trailing tokens are rejected.

Each node starts with a tag and a propagation-operation count.  An operation
has four tokens (row, coordinate, direction, signed bound in zigzag encoding).
The remaining node fields are a prune row (tag 0), a cut and discharge mode
(tag 1), or a split coordinate and signed midpoint followed by two complete
children (tag 2).  Direction 0 is upper and 1 is lower; modes 0, 1, 2 are
interval, corner, eval.  The token count bounds recursive decoding depth.
-/

namespace PeaceableQueens.UpperBound.EncodedFiniteCertificate

open FiniteLattice FiniteCertificates

private def readFin (n value : Nat) : Option (Fin n) :=
  if h : value < n then some ⟨value, h⟩ else none

private def signed (value : Nat) : Int :=
  if value % 2 = 0 then (value / 2 : Nat) else -((value / 2 : Nat) : Int) - 1

private def readDirection : Nat → Option Direction
  | 0 => some .upper
  | 1 => some .lower
  | _ => none

private def readMode : Nat → Option DischargeMode
  | 0 => some .interval
  | 1 => some .corner
  | 2 => some .eval
  | _ => none

private def hexDigit (byte : UInt8) : Option Nat :=
  let n := byte.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 87)
  else none

private def readToken (input : ByteArray) (pos : Nat) : Option (Nat × Nat) := do
  if pos + 3 > input.size then none else do
    let a ← hexDigit input[pos]!
    let b ← hexDigit input[pos + 1]!
    let c ← hexDigit input[pos + 2]!
    return (256 * a + 16 * b + c, pos + 3)

private def readOps (input : ByteArray) : Nat → Nat →
    Option (List (PropOp 8 5) × Nat)
  | 0, pos => some ([], pos)
  | count + 1, pos => do
      let (row, pos) ← readToken input pos
      let (coord, pos) ← readToken input pos
      let (direction, pos) ← readToken input pos
      let (bound, pos) ← readToken input pos
      let row ← readFin 5 row
      let coord ← readFin 8 coord
      let direction ← readDirection direction
      let (rest, pos) ← readOps input count pos
      return ({ row, coord, direction, bound := signed bound } :: rest, pos)

private def readAction (input : ByteArray) : Nat → Nat →
    Option (Action 8 5 76 × Nat)
  | 0, _ => none
  | fuel + 1, pos => do
      let (tag, pos) ← readToken input pos
      let (count, pos) ← readToken input pos
      if count > (input.size - pos) / 12 then none else do
       let (ops, pos) ← readOps input count pos
       match tag with
       | 0 =>
          let (row, pos) ← readToken input pos
          let row ← readFin 5 row
          return (.prune row ops, pos)
       | 1 =>
          let (cut, pos) ← readToken input pos
          let (mode, pos) ← readToken input pos
          let cut ← readFin 76 cut
          let mode ← readMode mode
          return (.discharge cut mode ops, pos)
       | 2 =>
          let (coord, pos) ← readToken input pos
          let (mid, pos) ← readToken input pos
          let coord ← readFin 8 coord
          let (left, pos) ← readAction input fuel pos
          let (right, pos) ← readAction input fuel pos
          return (.split coord (signed mid) ops [left] [right], pos)
       | _ => none

def decode (encoded : String) : Option (Action 8 5 76) := do
  let input := encoded.toUTF8
  if input.size % 3 != 0 then none else do
    let (tree, pos) ← readAction input (input.size / 3) 0
    if pos = input.size then some tree else none

def accepted (q bound : Nat) (encoded : String) : Bool :=
  match decode encoded with
  | none => false
  | some tree => validateCompleteBool (domainRows q) cutTable q
      (paperThreshold bound) (fullBox 8 q) [tree]

/-- Acceptance means that the fully decoded action tree covers every
canonical point of the full integer-profile box. -/
theorem accepted_sound (q bound : Nat) (encoded : String)
    (hcheck : accepted q bound encoded = true) :
    Nonempty (ActionCoverTree (Canonical q) (PrunedBy (domainRows q))
      (DischargedBy cutTable q (paperThreshold bound)) (fullBox 8 q)) := by
  cases hdecode : decode encoded with
  | none => simp [accepted, hdecode] at hcheck
  | some tree =>
      have hvalid : validateCompleteBool (domainRows q) cutTable q
          (paperThreshold bound) (fullBox 8 q) [tree] = true := by
        simpa [accepted, hdecode] using hcheck
      exact validateCompleteBool_sound (domainRows q) cutTable q
        (paperThreshold bound) (canonical_rows q) (fullBox 8 q)
        (by intro i; simp [fullBox]) (by intro i; simp [fullBox]) [tree] hvalid

#print axioms accepted_sound

/-- Execution-equivalent checker that materializes finite coordinate arrays
between propagation, splitting and repeated corner-polynomial evaluation. -/
def acceptedCached (q bound : Nat) (encoded : String) : Bool :=
  match decode encoded with
  | none => false
  | some tree => CachedFiniteChecker.validateCompleteBoolCached
      (FastFiniteTables.fastDomainRows q) FastFiniteTables.fastCutTable q
      (paperThreshold bound) (fullBox 8 q) [tree]

private theorem fastCutTable_eq : FastFiniteTables.fastCutTable = cutTable := by
  simp [FastFiniteTables.fastCutTable, FastFiniteTables.fastCuts_eq, cutTable]

theorem acceptedCached_eq (q bound : Nat) (encoded : String) :
    acceptedCached q bound encoded = accepted q bound encoded := by
  cases hdecode : decode encoded <;>
    simp [acceptedCached, accepted, hdecode,
      CachedFiniteChecker.validateCompleteBoolCached_eq,
      FastFiniteTables.fastDomainRows_eq, fastCutTable_eq]

theorem acceptedCached_sound (q bound : Nat) (encoded : String)
    (hcheck : acceptedCached q bound encoded = true) :
    Nonempty (ActionCoverTree (Canonical q) (PrunedBy (domainRows q))
      (DischargedBy cutTable q (paperThreshold bound)) (fullBox 8 q)) :=
  accepted_sound q bound encoded ((acceptedCached_eq q bound encoded).symm.trans hcheck)

#print axioms acceptedCached_eq
#print axioms acceptedCached_sound

end PeaceableQueens.UpperBound.EncodedFiniteCertificate
