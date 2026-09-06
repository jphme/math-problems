import PeaceableQueens.UpperBound.MomentModel

/-!
# Flat LP model in certificate order

This module reconstructs the concrete 95-variable, 42-equality, 95-inequality
leaf LP used by the released certificates. Indices deliberately match the
Python/JSON order. The semantic moment matrix is defined separately in
`MomentModel.lean`; `ModelCompatibility.lean` proves that the two agree
coefficient by coefficient, so the flat order is checked rather than trusted.
-/

namespace PeaceableQueens.UpperBound.LPModel

abbrev ProfileCoord := Fin 8
abbrev ProductCoord := Fin 22
abbrev AtomCoord := Fin 64
abbrev EqCoord := Fin 42
abbrev IneqCoord := Fin 95
abbrev VarCoord := Fin 95

abbrev Profile := ProfileCoord → ℚ
abbrev LPVector := VarCoord → ℚ

def fin2 (n : Nat) : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by omega)⟩
def fin4 (n : Nat) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by omega)⟩
def fin10 (n : Nat) : Fin 10 := ⟨n % 10, Nat.mod_lt _ (by omega)⟩
def fin22 (n : Nat) : Fin 22 := ⟨n % 22, Nat.mod_lt _ (by omega)⟩
def fin64 (n : Nat) : Fin 64 := ⟨n % 64, Nat.mod_lt _ (by omega)⟩

def xVar (i : ProfileCoord) : VarCoord := ⟨i, by omega⟩
def yVar (i : ProductCoord) : VarCoord := ⟨8 + i, by omega⟩
def pVar (i : AtomCoord) : VarCoord := ⟨30 + i, by omega⟩
def tVar : VarCoord := ⟨94, by omega⟩

def blockOfAtom (a : AtomCoord) : Fin 4 := ⟨a / 16, by omega⟩
def localAtom (a : AtomCoord) : Fin 16 := ⟨a % 16, Nat.mod_lt _ (by omega)⟩
def bit (a : AtomCoord) (family : Fin 4) : Bool :=
  (localAtom a).val.testBit (3 - family.val)

def blockRow (b : Fin 4) : Fin 2 := ⟨b / 2, by omega⟩
def blockCol (b : Fin 4) : Fin 2 := ⟨b % 2, Nat.mod_lt _ (by omega)⟩
def blockParity (b : Fin 4) : Fin 2 :=
  ⟨(blockRow b + blockCol b) % 2, Nat.mod_lt _ (by omega)⟩

def outerOf (b : Fin 4) (family : Fin 4) : ProfileCoord :=
  match family with
  | ⟨0, _⟩ => ⟨blockRow b, by omega⟩
  | ⟨1, _⟩ => ⟨2 + blockCol b, by omega⟩
  | ⟨2, _⟩ => ⟨4 + blockParity b, by omega⟩
  | ⟨3, _⟩ => ⟨6 + blockParity b, by omega⟩

def productPair : ProductCoord → ProfileCoord × ProfileCoord := ![
  (⟨0, by omega⟩, ⟨2, by omega⟩), (⟨0, by omega⟩, ⟨3, by omega⟩),
  (⟨0, by omega⟩, ⟨4, by omega⟩), (⟨0, by omega⟩, ⟨5, by omega⟩),
  (⟨0, by omega⟩, ⟨6, by omega⟩), (⟨0, by omega⟩, ⟨7, by omega⟩),
  (⟨1, by omega⟩, ⟨2, by omega⟩), (⟨1, by omega⟩, ⟨3, by omega⟩),
  (⟨1, by omega⟩, ⟨4, by omega⟩), (⟨1, by omega⟩, ⟨5, by omega⟩),
  (⟨1, by omega⟩, ⟨6, by omega⟩), (⟨1, by omega⟩, ⟨7, by omega⟩),
  (⟨2, by omega⟩, ⟨4, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩),
  (⟨2, by omega⟩, ⟨6, by omega⟩), (⟨2, by omega⟩, ⟨7, by omega⟩),
  (⟨3, by omega⟩, ⟨4, by omega⟩), (⟨3, by omega⟩, ⟨5, by omega⟩),
  (⟨3, by omega⟩, ⟨6, by omega⟩), (⟨3, by omega⟩, ⟨7, by omega⟩),
  (⟨4, by omega⟩, ⟨6, by omega⟩), (⟨5, by omega⟩, ⟨7, by omega⟩)]

def productIndex? (p : ProfileCoord × ProfileCoord) : Option ProductCoord :=
  match p.1.val, p.2.val with
  | 0, 2 => some 0 | 0, 3 => some 1 | 0, 4 => some 2 | 0, 5 => some 3
  | 0, 6 => some 4 | 0, 7 => some 5 | 1, 2 => some 6 | 1, 3 => some 7
  | 1, 4 => some 8 | 1, 5 => some 9 | 1, 6 => some 10 | 1, 7 => some 11
  | 2, 4 => some 12 | 2, 5 => some 13 | 2, 6 => some 14 | 2, 7 => some 15
  | 3, 4 => some 16 | 3, 5 => some 17 | 3, 6 => some 18 | 3, 7 => some 19
  | 4, 6 => some 20 | 5, 7 => some 21 | _, _ => none

def featureDegree (f : Fin 10) : Nat := if f < 5 then if f = 0 then 0 else 1 else 2
def featureSingle? (f : Fin 10) : Option (Fin 4) :=
  match f.val with | 1 => some 0 | 2 => some 1 | 3 => some 2 | 4 => some 3 | _ => none
def featurePair? (f : Fin 10) : Option (Fin 4 × Fin 4) :=
  match f.val with
  | 5 => some (0, 1) | 6 => some (0, 2) | 7 => some (0, 3)
  | 8 => some (1, 2) | 9 => some (1, 3) | _ => none
def hasFeature (f : Fin 10) (a : AtomCoord) : Bool :=
  match featureSingle? f, featurePair? f with
  | none, none => f = 0
  | some i, none => bit a i
  | none, some (i, j) => bit a i && bit a j
  | _, _ => false

def eqBlock? (e : EqCoord) : Option (Fin 4 × Fin 10) :=
  if e < 40 then some (fin4 (e / 10), fin10 (e % 10)) else none
def eqAggregateParity? (e : EqCoord) : Option (Fin 2) :=
  if 40 ≤ e then some (fin2 (e - 40)) else none

def momentCoeff (e : EqCoord) (a : AtomCoord) : ℚ :=
  match eqBlock? e with
  | some (b, f) => if blockOfAtom a = b ∧ hasFeature f a then 1 else 0
  | none => match eqAggregateParity? e with
    | some parity => if blockParity (blockOfAtom a) = parity ∧ bit a 2 ∧ bit a 3 then 1 else 0
    | none => 0

def eqRhs (e : EqCoord) : ℚ :=
  match eqBlock? e with
  | some (_, f) => if f = 0 then 1 else 0
  | none => 0

def eqCoeff (e : EqCoord) (v : VarCoord) : ℚ :=
  if 30 ≤ v ∧ v < 94 then momentCoeff e (fin64 (v - 30)) else
  match eqBlock? e with
  | some (b, f) =>
    match featureSingle? f, featurePair? f with
    | some family, _ => if v = xVar (outerOf b family) then -1 else 0
    | _, some (family₁, family₂) =>
      match productIndex? (outerOf b family₁, outerOf b family₂) with
      | some product => if v = yVar product then -1 else 0
      | none => 0
    | _, _ => 0
  | none =>
    match eqAggregateParity? e with
    | some parity =>
      if v = yVar (if parity = 0 then 20 else 21) then -2 else 0
    | none => 0

def ineqRhs (lo hi : Profile) (r : IneqCoord) : ℚ :=
  if r = 0 then 4 else
  if _h : 7 ≤ r then
    let k : ProductCoord := fin22 ((r - 7) / 4)
    let step := (r - 7) % 4
    let (i, j) := productPair k
    match step with
    | 0 => lo i * lo j
    | 1 => hi i * hi j
    | 2 => -hi i * lo j
    | _ => -lo i * hi j
  else 0

def ineqCoeff (lo hi : Profile) (r : IneqCoord) (v : VarCoord) : ℚ :=
  if r = 0 then if v < 8 then 1 else 0 else
  if r = 1 then if v = 0 then 1 else if v = 1 then -1 else 0 else
  if r = 2 then if v = 2 then 1 else if v = 3 then -1 else 0 else
  if r = 3 then if v = 0 ∨ v = 1 then 1 else if v = 2 ∨ v = 3 then -1 else 0 else
  if r = 4 then if v = 4 ∨ v = 5 then 1 else if v = 6 ∨ v = 7 then -1 else 0 else
  if r = 5 then if v = tVar then 1 else if 30 ≤ v ∧ v < 94 then if localAtom (fin64 (v-30)) = 15 then -1 else 0 else 0 else
  if r = 6 then if v = tVar then 1 else if 30 ≤ v ∧ v < 94 then if localAtom (fin64 (v-30)) = 0 then -1 else 0 else 0 else
  let k : ProductCoord := fin22 ((r - 7) / 4)
  let step := (r - 7) % 4
  let (i, j) := productPair k
  if v = yVar k then if step < 2 then -1 else 1 else
  if v = xVar i then match step with | 0 => lo j | 1 => hi j | 2 => -lo j | _ => -hi j else
  if v = xVar j then match step with | 0 => lo i | 1 => hi i | 2 => -hi i | _ => -lo i else 0

theorem productPair_twenty : productPair 20 = (4, 6) := by decide
theorem productIndex_DA0 : productIndex? (4, 6) = some 20 := by decide
theorem last_block_row : eqBlock? 39 = some (3, 9) := by decide
theorem last_aggregate_row : eqAggregateParity? 41 = some 1 := by decide
theorem last_atom_block : blockOfAtom 63 = 3 := by decide
theorem last_atom_local : localAtom 63 = 15 := by decide
theorem last_atom_row_bit : bit 63 0 = true := by decide
theorem last_atom_antidiagonal_bit : bit 63 3 = true := by decide

#print axioms productIndex_DA0

end PeaceableQueens.UpperBound.LPModel
