#!/usr/bin/env python3
"""Exact checks for the symbolic part of the finite-even proof.

This script uses only the standard library.  It verifies:
  * exact support-dual validity of cuts 547, 609, and 559;
  * their exact transformation to F_B1, F_B2, F_W;
  * the four-profile switching identities used in crossed case A;
  * the average-cut identity used in crossed case B;
  * all rational and Q(sqrt(3)) constant comparisons, including q>=130
    and the 527/1000 escape comparison.

The inequalities relying on AM-GM and monotonicity are stated in the proof
file; this checker verifies their algebraic endpoints and constants.
"""
from __future__ import annotations

import itertools
import json
import sys
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path

CUTS = Path(sys.argv[1] if len(sys.argv) > 1 else "/mnt/data/even_finite_support_cuts.json")

# Polynomial representation: monomial is a sorted tuple of variable indices.
Poly = dict[tuple[int, ...], F]


def clean(p: Poly) -> Poly:
    return {m: c for m, c in p.items() if c}


def padd(p: Poly, q: Poly) -> Poly:
    out = dict(p)
    for m, c in q.items():
        out[m] = out.get(m, F(0)) + c
    return clean(out)


def pneg(p: Poly) -> Poly:
    return {m: -c for m, c in p.items()}


def psub(p: Poly, q: Poly) -> Poly:
    return padd(p, pneg(q))


def pmul(p: Poly, q: Poly) -> Poly:
    out: Poly = {}
    for m, a in p.items():
        for n, b in q.items():
            key = tuple(sorted(m + n))
            out[key] = out.get(key, F(0)) + a * b
    return clean(out)


def pscale(p: Poly, c: F | int) -> Poly:
    c = F(c)
    return clean({m: c * a for m, a in p.items()})


def C(c: F | int) -> Poly:
    return {(): F(c)} if c else {}


def V(i: int) -> Poly:
    return {(i,): F(1)}


def prod(*ps: Poly) -> Poly:
    out = C(1)
    for p in ps:
        out = pmul(out, p)
    return out


# Reconstruct the exact 42-row moment system.
BLOCKS = [(0, 0), (0, 1), (1, 0), (1, 1)]
ATOMS = list(itertools.product((0, 1), repeat=4))
I1111 = ATOMS.index((1, 1, 1, 1))
I0000 = ATOMS.index((0, 0, 0, 0))
A42: list[list[int]] = []
rhs_terms: list[tuple[str, tuple[int, ...]]] = []
rhs_factors: list[int] = []
for bi, (i, j) in enumerate(BLOCKS):
    parity = i ^ j
    ri, cj, de, ae = i, 2 + j, 4 + parity, 6 + parity

    def atom_row(fn):
        row = [0] * 64
        for ai, atom in enumerate(ATOMS):
            row[16 * bi + ai] = int(fn(atom))
        return row

    specs = [
        (lambda z: 1, ("const", ()), 1),
        (lambda z: z[0], ("lin", (ri,)), 1),
        (lambda z: z[1], ("lin", (cj,)), 1),
        (lambda z: z[2], ("lin", (de,)), 1),
        (lambda z: z[3], ("lin", (ae,)), 1),
        (lambda z: z[0] * z[1], ("prod", tuple(sorted((ri, cj)))), 1),
        (lambda z: z[0] * z[2], ("prod", tuple(sorted((ri, de)))), 1),
        (lambda z: z[0] * z[3], ("prod", tuple(sorted((ri, ae)))), 1),
        (lambda z: z[1] * z[2], ("prod", tuple(sorted((cj, de)))), 1),
        (lambda z: z[1] * z[3], ("prod", tuple(sorted((cj, ae)))), 1),
    ]
    for fn, term, fac in specs:
        A42.append(atom_row(fn))
        rhs_terms.append(term)
        rhs_factors.append(fac)
for parity in (0, 1):
    row = [0] * 64
    for bi, (i, j) in enumerate(BLOCKS):
        if (i ^ j) == parity:
            for ai, atom in enumerate(ATOMS):
                row[16 * bi + ai] = atom[2] * atom[3]
    A42.append(row)
    rhs_terms.append(("prod", (4 + parity, 6 + parity)))
    rhs_factors.append(2)
assert len(A42) == 42
Bcols = {16 * bi + I1111 for bi in range(4)}
Wcols = {16 * bi + I0000 for bi in range(4)}


def rat(x) -> F:
    return F(int(x[0]), int(x[1]))


def dense_dual(obj) -> list[F]:
    out = [F(0)] * 42
    for i, a, b in obj:
        assert out[int(i)] == 0
        out[int(i)] = F(int(a), int(b))
    return out


def support_poly(lam: list[F]) -> Poly:
    out: Poly = {}
    for k, lk in enumerate(lam):
        if not lk:
            continue
        typ, inds = rhs_terms[k]
        coeff = lk * rhs_factors[k]
        key = () if typ == "const" else tuple(inds)
        out[key] = out.get(key, F(0)) + coeff
    return clean(out)


def stored_poly(obj) -> Poly:
    out: Poly = {}
    for key, value in obj.items():
        mon = () if key == "" else tuple(map(int, key.split(",")))
        out[mon] = rat(value)
    return clean(out)


def substitute(poly: Poly, subst: list[Poly]) -> Poly:
    out: Poly = {}
    for mon, coeff in poly.items():
        term = C(coeff)
        for i in mon:
            term = pmul(term, subst[i])
        out = padd(out, term)
    return out


raw_cuts = json.loads(CUTS.read_text())
if isinstance(raw_cuts, list):
    cuts_by_index = {i: cut for i, cut in enumerate(raw_cuts)}
else:
    cuts_by_index = {int(cut["source_index"]): cut for cut in raw_cuts["cuts"]}
selected = {547: "FB1", 609: "FB2", 559: "FW"}

# Local normalized variables 0..7 are u,R,v,C,g,e,h,f.
u, R, v, Cc, g, e, h, f = map(V, range(8))
one = C(1)
subst = [u, R, v, Cc, psub(one, g), e, psub(one, h), f]
X = padd(prod(u, v), prod(R, Cc))
Y = padd(prod(psub(one, u), psub(one, Cc)), prod(psub(one, R), psub(one, v)))
beta = psub(padd(R, Cc), one)
alpha = psub(C(2), padd(padd(R, Cc), padd(u, v)))
a = padd(e, f)
b = padd(g, h)
Q = padd(pscale(prod(e, f), 2), pscale(prod(g, h), 2))
FB1 = padd(psub(X, prod(beta, b)), padd(pscale(prod(g, h), 2), prod(e, padd(u, v))))
FB2 = padd(psub(X, prod(beta, b)), Q)
FW = padd(psub(Y, prod(alpha, a)), Q)
expected = {"FB1": FB1, "FB2": FB2, "FW": FW}

for index, name in selected.items():
    cut = cuts_by_index[index]
    lam = dense_dual(cut["dual"])
    alpha_weight = rat(cut["alpha"])
    assert F(0) <= alpha_weight <= F(1)
    for col in range(64):
        lhs = sum(lam[r] * A42[r][col] for r in range(42))
        rhs = (alpha_weight if col in Bcols else 0) + ((1 - alpha_weight) if col in Wcols else 0)
        assert lhs >= rhs, (index, col, lhs, rhs)
    p = support_poly(lam)
    assert p == stored_poly(cut["poly"]), (index, "stored polynomial mismatch")
    local = substitute(p, subst)
    assert local == expected[name], (index, name, psub(local, expected[name]))

# Four crossed-case-A profiles (r0,r1,c0,c1)=(R,u+x,v+y,C).
pairs = [(e, pscale(f, 2)), (pscale(e, 2), f), (f, pscale(e, 2)), (pscale(f, 2), e)]
cost_sum: Poly = {}
for xx, yy in pairs:
    black = padd(prod(R, Cc), prod(padd(u, xx), padd(v, yy)))
    white = padd(prod(psub(one, R), psub(one, padd(v, yy))),
                  prod(psub(one, padd(u, xx)), psub(one, Cc)))
    expected_black = padd(X, padd(prod(u, yy), padd(prod(v, xx), prod(xx, yy))))
    expected_white = psub(Y, padd(prod(xx, psub(one, Cc)), prod(yy, psub(one, R))))
    assert black == expected_black
    assert white == expected_white
    cost_sum = padd(cost_sum, psub(Y, white))
L = psub(C(2), padd(R, Cc))
assert cost_sum == pscale(prod(a, L), 3)

# Average-cut identity.
assert pscale(padd(FB2, FW), F(1, 2)) == padd(
    pscale(padd(X, Y), F(1, 2)),
    pscale(psub(pscale(Q, 2), padd(prod(beta, b), prod(alpha, a))), F(1, 2)),
)


@dataclass(frozen=True)
class Q3:
    """a+b*sqrt(3), with exact sign tests."""
    a: F = F(0)
    b: F = F(0)

    def __add__(self, other):
        other = q3(other)
        return Q3(self.a + other.a, self.b + other.b)
    __radd__ = __add__

    def __neg__(self):
        return Q3(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-q3(other))

    def __rsub__(self, other):
        return q3(other) - self

    def __mul__(self, other):
        other = q3(other)
        return Q3(self.a * other.a + 3 * self.b * other.b,
                  self.a * other.b + self.b * other.a)
    __rmul__ = __mul__

    def sign(self) -> int:
        aa, bb = self.a, self.b
        if bb == 0:
            return (aa > 0) - (aa < 0)
        if bb > 0:
            if aa >= 0:
                return 1
            return (3 * bb * bb > aa * aa) - (3 * bb * bb < aa * aa)
        bb = -bb
        if aa <= 0:
            return -1
        return (aa * aa > 3 * bb * bb) - (aa * aa < 3 * bb * bb)

    def __lt__(self, other): return (self - other).sign() < 0
    def __le__(self, other): return (self - other).sign() <= 0
    def __gt__(self, other): return (self - other).sign() > 0
    def __ge__(self, other): return (self - other).sign() >= 0


def q3(x) -> Q3:
    return x if isinstance(x, Q3) else Q3(F(x), F(0))


sqrt3 = Q3(F(0), F(1))
kappa = 4 - 2 * sqrt3
c0 = 1 - sqrt3 * F(1, 3)  # 1-1/sqrt(3)

# Core endpoint arithmetic.
assert F(2) - F(37, 25) - F(9, 100) == F(43, 100)       # alpha lower bound
assert F(36, 25) - 1 == F(11, 25)                         # beta lower bound
assert (F(2) - F(37, 25)) / 4 - F(9, 100) == F(1, 25)    # L/4-n lower bound
assert F(11, 21) * F(9, 200) < F(1, 25)                  # Q < aq/25 in case A
assert F(43, 100) > F(9, 200)
assert F(11, 25) > F(1, 25)

# Balanced-plaid comparison: (11/25-c0)q >= 9/4 at q=130.
assert (F(11, 25) - c0) * 130 >= F(9, 4)
# Escape comparison: kappa-527/1000 > 1/125 and c0<1/2.
assert kappa - F(527, 1000) > F(1, 125)
assert c0 < F(1, 2)
# q^2/125-q/2-1/4 is positive at q=64 and strictly increasing thereafter.
assert F(64 * 64, 125) - F(64, 2) - F(1, 4) > 0
assert F(2 * 64 + 1, 125) - F(1, 2) > 0

print("cuts=547,609,559 support_duals=exact local_polynomials=exact")
print("switching_profile_identities=exact average_cut_identity=exact")
print("threshold_case_B=130 escape_threshold_at_most_64")
print("EVEN_FINITE_ALGEBRA_OK")
