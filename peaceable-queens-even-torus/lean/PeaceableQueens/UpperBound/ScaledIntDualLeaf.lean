import PeaceableQueens.UpperBound.SparseListDualLeaf

/-! Integer-only executable kernel for a common-denominator dual leaf.

`coeffNum` is `S * ineqCoeff`; `rhsNum` is `S^2 * ineqRhs`.  The full
residual is represented at scale `S^2`.  On y/p/t coordinates it has an
extra factor S, and `residual1` removes that factor before the product-bound
part of the dual objective is formed.  Thus `boundNum / S^3` is the dual
bound. -/

namespace PeaceableQueens.UpperBound.ScaledIntDualLeaf

open LPModel DualLeaf

structure Box where
  S : Int
  lo : ProfileCoord → Int
  hi : ProfileCoord → Int

def Box.profileLo (b : Box) : Profile := fun i => (b.lo i : ℚ) / b.S
def Box.profileHi (b : Box) : Profile := fun i => (b.hi i : ℚ) / b.S

structure Certificate where
  mu : List (IneqCoord × Int)
  nu : List (EqCoord × Int)
  /-- numerator of the claimed bound, with denominator S^3 -/
  claimed : Int

def coeffNum (b : Box) (r : IneqCoord) (v : VarCoord) : Int :=
  if r = 0 then if v < 8 then b.S else 0 else
  if r = 1 then if v = 0 then b.S else if v = 1 then -b.S else 0 else
  if r = 2 then if v = 2 then b.S else if v = 3 then -b.S else 0 else
  if r = 3 then if v = 0 ∨ v = 1 then b.S else if v = 2 ∨ v = 3 then -b.S else 0 else
  if r = 4 then if v = 4 ∨ v = 5 then b.S else if v = 6 ∨ v = 7 then -b.S else 0 else
  if r = 5 then if v = tVar then b.S else if 30 ≤ v ∧ v < 94 then
    if localAtom (fin64 (v-30)) = 15 then -b.S else 0 else 0 else
  if r = 6 then if v = tVar then b.S else if 30 ≤ v ∧ v < 94 then
    if localAtom (fin64 (v-30)) = 0 then -b.S else 0 else 0 else
  let k : ProductCoord := fin22 ((r - 7) / 4)
  let step := (r - 7) % 4
  let (i, j) := productPair k
  if v = yVar k then if step < 2 then -b.S else b.S else
  if v = xVar i then match step with | 0 => b.lo j | 1 => b.hi j | 2 => -b.lo j | _ => -b.hi j else
  if v = xVar j then match step with | 0 => b.lo i | 1 => b.hi i | 2 => -b.hi i | _ => -b.lo i else 0

def rhsNum (b : Box) (r : IneqCoord) : Int :=
  if r = 0 then 4 * b.S * b.S else
  if _ : 7 ≤ r then
    let k : ProductCoord := fin22 ((r - 7) / 4)
    let step := (r - 7) % 4
    let (i, j) := productPair k
    match step with
    | 0 => b.lo i * b.lo j
    | 1 => b.hi i * b.hi j
    | 2 => -b.hi i * b.lo j
    | _ => -b.lo i * b.hi j
  else 0

def eqCoeffInt (r : EqCoord) (v : VarCoord) : Int :=
  if 30 ≤ v ∧ v < 94 then
    match eqBlock? r with
    | some (b, f) => if blockOfAtom (fin64 (v - 30)) = b ∧ hasFeature f (fin64 (v - 30)) then 1 else 0
    | none => match eqAggregateParity? r with
      | some parity => if blockParity (blockOfAtom (fin64 (v - 30))) = parity ∧ bit (fin64 (v - 30)) 2 ∧ bit (fin64 (v - 30)) 3 then 1 else 0
      | none => 0
  else
    match eqBlock? r with
    | some (b, f) =>
      match featureSingle? f, featurePair? f with
      | some family, _ => if v = xVar (outerOf b family) then -1 else 0
      | _, some (family₁, family₂) =>
        match productIndex? (outerOf b family₁, outerOf b family₂) with
        | some product => if v = yVar product then -1 else 0
        | none => 0
      | _, _ => 0
    | none => match eqAggregateParity? r with
      | some parity => if v = yVar (if parity = 0 then 20 else 21) then -2 else 0
      | none => 0

def eqRhsInt (r : EqCoord) : Int :=
  match eqBlock? r with
  | some (_, f) => if f = 0 then 1 else 0
  | none => 0

def residual2 (b : Box) (c : Certificate) (v : VarCoord) : Int :=
  (if v = tVar then b.S * b.S else 0) +
    (c.mu.map (fun e => e.2 * coeffNum b e.1 v)).sum +
    (c.nu.map (fun e => e.2 * b.S * eqCoeffInt e.1 v)).sum

/-- On y, p and t, `residual2 = S * residual1`. -/
def rawCoeff (_b : Box) (r : IneqCoord) (v : VarCoord) : Int :=
  if r = 5 then if v = tVar then 1 else if 30 ≤ v ∧ v < 94 then
    if localAtom (fin64 (v-30)) = 15 then -1 else 0 else 0 else
  if r = 6 then if v = tVar then 1 else if 30 ≤ v ∧ v < 94 then
    if localAtom (fin64 (v-30)) = 0 then -1 else 0 else 0 else
  if 7 ≤ r then
    let k : ProductCoord := fin22 ((r - 7) / 4)
    let step := (r - 7) % 4
    if v = yVar k then if step < 2 then -1 else 1 else 0
  else 0

def residual1 (b : Box) (c : Certificate) (v : VarCoord) : Int :=
  (if v = tVar then b.S else 0) +
    (c.mu.map (fun e => e.2 * rawCoeff b e.1 v)).sum +
    (c.nu.map (fun e => e.2 * eqCoeffInt e.1 v)).sum

def pos (x : Int) : Int := if 0 ≤ x then x else 0
def neg (x : Int) : Int := if x ≤ 0 then -x else 0

def productLoNum (b : Box) (k : ProductCoord) : Int :=
  b.lo (productPair k).1 * b.lo (productPair k).2
def productHiNum (b : Box) (k : ProductCoord) : Int :=
  b.hi (productPair k).1 * b.hi (productPair k).2

def recomputedBoundNum (b : Box) (c : Certificate) : Int :=
  (c.mu.map (fun e => (-e.2) * rhsNum b e.1)).sum +
  (∑ i : ProfileCoord, (neg (residual2 b c (xVar i)) * (-b.lo i) +
    pos (residual2 b c (xVar i)) * b.hi i)) +
  (∑ k : ProductCoord, (neg (residual1 b c (yVar k)) * (-productLoNum b k) +
    pos (residual1 b c (yVar k)) * productHiNum b k)) +
  (c.nu.map (fun e => (-e.2) * b.S * b.S * eqRhsInt e.1)).sum

def AcceptedAt (thresholdNum thresholdDen : Int) (b : Box) (c : Certificate) : Prop :=
  0 < b.S ∧ 0 < thresholdDen ∧
  (∀ e ∈ c.mu, e.2 ≤ 0) ∧
  residual2 b c tVar = 0 ∧
  (∀ a, residual1 b c (pVar a) ≤ 0) ∧
  c.claimed = recomputedBoundNum b c ∧
  c.claimed * thresholdDen ≤ thresholdNum * b.S * b.S * b.S

instance (thresholdNum thresholdDen : Int) (b : Box) (c : Certificate) :
    Decidable (AcceptedAt thresholdNum thresholdDen b c) := by
  unfold AcceptedAt; infer_instance

def checkAt (thresholdNum thresholdDen : Int) (b : Box) (c : Certificate) : Bool :=
  decide (0 < b.S) && decide (0 < thresholdDen) &&
  c.mu.all (fun e => decide (e.2 ≤ 0)) &&
  decide (residual2 b c tVar = 0) &&
  (List.ofFn fun a : AtomCoord => decide (residual1 b c (pVar a) ≤ 0)).all id &&
  decide (c.claimed = recomputedBoundNum b c) &&
  decide (c.claimed * thresholdDen ≤ thresholdNum * b.S * b.S * b.S)

def toSparse (b : Box) (c : Certificate) : SparseListDualLeaf.Certificate := {
  mu := c.mu.map (fun e => (e.1, (e.2 : ℚ) / b.S))
  nu := c.nu.map (fun e => (e.1, (e.2 : ℚ) / b.S))
  claimed := (c.claimed : ℚ) / (b.S * b.S * b.S)
}

end PeaceableQueens.UpperBound.ScaledIntDualLeaf
