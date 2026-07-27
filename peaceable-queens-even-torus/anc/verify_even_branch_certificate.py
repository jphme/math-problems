#!/usr/bin/env python3
"""Exact standard-library verifier for the two finite-even branch certificates.

Supported proof objects
-----------------------
* peaceable-even-c527-sym-mc-v1:
    On the canonical symmetry chamber, every point outside the four rational
    plaid boxes has 42-moment optimum at most 527/1000.
* peaceable-even-local-core-mc-v1:
    Inside the canonical rational plaid box N, every point outside the stated
    aggregate core has 42-moment optimum at most 527/1000.

The verifier reconstructs the 42 exact moment equations and all 95 inequality
rows.  It then checks every rational LP dual, every split, every local/core
leaf, and every exact empty-chamber leaf using fractions only.

Usage:
    python verify_even_branch_certificate.py CERT.json.gz [CERT2.json.gz ...]

With no arguments it verifies both certificate files beside this script.
"""
from __future__ import annotations

import gzip
import itertools
import json
import sys
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

VARS = ["r0", "r1", "c0", "c1", "d0", "d1", "a0", "a1"]
BLOCKS = [(0, 0), (0, 1), (1, 0), (1, 1)]
ATOMS = list(itertools.product((0, 1), repeat=4))
I1111 = ATOMS.index((1, 1, 1, 1))
I0000 = ATOMS.index((0, 0, 0, 0))
TARGET = F(527, 1000)
DELTA_FIELD = F(1, 20)
HERE = Path(__file__).resolve().parent


def rat(obj) -> F:
    if not (isinstance(obj, list) and len(obj) == 2):
        raise ValueError(f"bad rational {obj!r}")
    return F(int(obj[0]), int(obj[1]))


def sparse(obj, n: int) -> list[F]:
    out = [F(0) for _ in range(n)]
    seen: set[int] = set()
    for triple in obj:
        if not (isinstance(triple, list) and len(triple) == 3):
            raise ValueError("bad sparse entry")
        i, a, b = map(int, triple)
        if not (0 <= i < n) or i in seen or b == 0:
            raise ValueError("bad/duplicate sparse index")
        seen.add(i)
        out[i] = F(a, b)
    return out


# Reconstruct the 42 exact moment rows and their outer-variable right sides.
row_names: list[str] = []
rhs_terms: list[tuple[str, tuple[int, ...]]] = []
rhs_factors: list[int] = []
A42: list[list[int]] = []
for bi, (i, j) in enumerate(BLOCKS):
    parity = i ^ j
    ri, cj, de, ae = i, 2 + j, 4 + parity, 6 + parity

    def atom_row(fn):
        row = [0] * 64
        for ai, atom in enumerate(ATOMS):
            row[16 * bi + ai] = int(fn(atom))
        return row

    specs = [
        ("1", lambda z: 1, ("const", ()), 1),
        ("R", lambda z: z[0], ("lin", (ri,)), 1),
        ("C", lambda z: z[1], ("lin", (cj,)), 1),
        ("D", lambda z: z[2], ("lin", (de,)), 1),
        ("A", lambda z: z[3], ("lin", (ae,)), 1),
        ("RC", lambda z: z[0] * z[1], ("prod", tuple(sorted((ri, cj)))), 1),
        ("RD", lambda z: z[0] * z[2], ("prod", tuple(sorted((ri, de)))), 1),
        ("RA", lambda z: z[0] * z[3], ("prod", tuple(sorted((ri, ae)))), 1),
        ("CD", lambda z: z[1] * z[2], ("prod", tuple(sorted((cj, de)))), 1),
        ("CA", lambda z: z[1] * z[3], ("prod", tuple(sorted((cj, ae)))), 1),
    ]
    for name, fn, term, fac in specs:
        row_names.append(f"b{i}{j}:{name}")
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
    row_names.append(f"aggDA{parity}")
    rhs_terms.append(("prod", (4 + parity, 6 + parity)))
    rhs_factors.append(2)

assert len(A42) == 42
A42_NZ = [[(c, a) for c, a in enumerate(row) if a] for row in A42]
PROD_PAIRS = sorted({term[1] for term in rhs_terms if term[0] == "prod"})
PAIR_INDEX = {pair: k for k, pair in enumerate(PROD_PAIRS)}
assert len(PROD_PAIRS) == 22


def equality_points() -> list[list[int | str]]:
    pts: list[list[int | str]] = []
    for parity in (0, 1):
        for i in (0, 1):
            j = i ^ parity
            p: list[int | str] = [0] * 8
            p[i] = "s"
            p[2 + j] = "s"
            p[4 + parity] = 1
            p[6 + parity] = 1
            pts.append(p)
    return pts


EQPTS = equality_points()


def empty_chamber_reason(lo: tuple[F, ...], hi: tuple[F, ...]) -> str | None:
    """First exact obstruction to intersection with the canonical chamber.

    Chamber inequalities:
      r0 <= r1,
      c0 <= c1,
      r0+r1 <= c0+c1,
      d0+d1 <= a0+a1,
      sum(x_i) <= 4.

    The formulas below minimize each successive required sum inside the box.
    """
    r1min = max(lo[1], lo[0])
    if r1min > hi[1]:
        return "rsort"
    rsum = lo[0] + r1min

    c1min = max(lo[3], lo[2])
    if c1min > hi[3]:
        return "csort"
    cbase = lo[2] + c1min
    cmax = hi[3] + min(hi[2], hi[3])
    cneed = max(cbase, rsum)
    if cneed > cmax:
        return "rcsum"

    dsum = lo[4] + lo[5]
    abase = lo[6] + lo[7]
    amax = hi[6] + hi[7]
    aneed = max(abase, dsum)
    if aneed > amax:
        return "dasum"

    if rsum + cneed + dsum + aneed > 4:
        return "budget"
    return None


def c527_local_index(lo: tuple[F, ...], hi: tuple[F, ...]) -> int | None:
    """A whole box lies in one rational plaid neighborhood."""
    for pi, p in enumerate(EQPTS):
        ok = True
        for k, val in enumerate(p):
            if val == 0:
                ok = hi[k] <= F(1, 10)
            elif val == 1:
                ok = lo[k] >= F(19, 20)
            else:
                ok = lo[k] >= F(3, 5) and hi[k] <= F(7, 8)
            if not ok:
                break
        if ok:
            return pi
    return None


def core_local_index(lo: tuple[F, ...], hi: tuple[F, ...]) -> int | None:
    """A whole box lies in the aggregate local core.

    In local integer notation after scaling by q:
      p=R+C in [36q/25,37q/25],
      n=u+v <= 9q/100,
      a=e+f <= 9q/200,
      b=g+h <= q/25.
    Since x4=1-g and x6=1-h, b<=1/25 is x4+x6>=49/25.
    """
    if (
        lo[1] + lo[3] >= F(36, 25)
        and hi[1] + hi[3] <= F(37, 25)
        and hi[0] + hi[2] <= F(9, 100)
        and hi[5] + hi[7] <= F(9, 200)
        and lo[4] + lo[6] >= F(49, 25)
    ):
        return 0
    return None


def compute_stationarity(
    lo: tuple[F, ...],
    hi: tuple[F, ...],
    mu: list[F],
    nu: list[F],
) -> tuple[list[F], list[F], list[F], F]:
    """Return c-A_ub^T mu-A_eq^T nu by variable block."""
    qx = [F(0) for _ in range(8)]
    qy = [F(0) for _ in range(22)]
    qp = [F(0) for _ in range(64)]
    qt = F(-1)  # minimization objective is -t

    # Inequality rows 0..4: budget and four chamber inequalities.
    for i in range(8):
        qx[i] -= mu[0]
    sym = [
        [1, -1, 0, 0, 0, 0, 0, 0],
        [0, 0, 1, -1, 0, 0, 0, 0],
        [1, 1, -1, -1, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 1, -1, -1],
    ]
    for rr, coeffs in enumerate(sym, 1):
        for i, coeff in enumerate(coeffs):
            qx[i] -= coeff * mu[rr]

    # Rows 5 and 6: t <= black and t <= white.
    qt -= mu[5] + mu[6]
    for bi in range(4):
        qp[16 * bi + I1111] += mu[5]
        qp[16 * bi + I0000] += mu[6]

    # Rows 7..94: four McCormick inequalities for each of 22 products.
    row = 7
    for k, (i, j) in enumerate(PROD_PAIRS):
        li, ui, lj, uj = lo[i], hi[i], lo[j], hi[j]
        coeffs = [
            (lj, li, F(-1)),
            (uj, ui, F(-1)),
            (-lj, -ui, F(1)),
            (-uj, -li, F(1)),
        ]
        for cxi, cxj, cy in coeffs:
            m = mu[row]
            row += 1
            qx[i] -= cxi * m
            qx[j] -= cxj * m
            qy[k] -= cy * m
    if row != 95:
        raise AssertionError("bad inequality count")

    # The 42 equality rows.
    for k, nk in enumerate(nu):
        if nk:
            for p, coeff in A42_NZ[k]:
                qp[p] -= coeff * nk
            typ, inds = rhs_terms[k]
            fac = rhs_factors[k]
            if typ == "lin":
                qx[inds[0]] += fac * nk
            elif typ == "prod":
                qy[PAIR_INDEX[inds]] += fac * nk
    return qx, qy, qp, qt


def verify_mc_leaf(nd: dict, lo: tuple[F, ...], hi: tuple[F, ...]) -> None:
    mu = sparse(nd["mu"], 95)
    nu = sparse(nd["nu"], 42)
    if any(x > 0 for x in mu):
        raise AssertionError("positive multiplier on a <= inequality")
    if mu[5] + mu[6] != -1:
        raise AssertionError("the two t multipliers do not sum to -1")

    qx, qy, qp, qt = compute_stationarity(lo, hi, mu, nu)
    if qt != 0:
        raise AssertionError("nonzero reduced cost for free t")
    if min(qp) < 0:
        raise AssertionError("negative reduced cost for a p_atom >= 0 variable")

    # Exact dual lower bound D for the minimization objective -t.
    D = F(4) * mu[0]
    row = 7
    for i, j in PROD_PAIRS:
        li, ui, lj, uj = lo[i], hi[i], lo[j], hi[j]
        for rhs in (li * lj, ui * uj, -ui * lj, -li * uj):
            D += mu[row] * rhs
            row += 1
    if row != 95:
        raise AssertionError("bad McCormick row count")
    for k, nk in enumerate(nu):
        if rhs_terms[k][0] == "const":
            D += rhs_factors[k] * nk

    ylo = [lo[i] * lo[j] for i, j in PROD_PAIRS]
    yhi = [hi[i] * hi[j] for i, j in PROD_PAIRS]
    for reduced, lower, upper in zip(qx + qy, list(lo) + ylo, list(hi) + yhi):
        D += (lower if reduced >= 0 else upper) * reduced

    upper = -D
    stored = rat(nd["u"])
    if upper != stored:
        raise AssertionError(f"stored dual objective mismatch: {upper} != {stored}")
    if upper > TARGET:
        raise AssertionError(f"leaf upper bound {upper} exceeds 527/1000")


def verify_one(path: Path) -> None:
    with gzip.open(path, "rt", encoding="utf-8") as fh:
        data = json.load(fh)

    fmt = data.get("format")
    if fmt == "peaceable-even-c527-sym-mc-v1":
        root_lo = tuple(F(0) for _ in range(8))
        root_hi = tuple(F(1) for _ in range(8))
        local_index = c527_local_index
    elif fmt == "peaceable-even-local-core-mc-v1":
        root_lo = (F(0), F(3, 5), F(0), F(3, 5), F(19, 20), F(0), F(19, 20), F(0))
        root_hi = (F(1, 10), F(7, 8), F(1, 10), F(7, 8), F(1), F(1, 10), F(1), F(1, 10))
        local_index = core_local_index
    else:
        raise AssertionError(f"unsupported format {fmt!r}")

    if data.get("variables") != VARS:
        raise AssertionError("variable list mismatch")
    if rat(data.get("delta")) != DELTA_FIELD:
        raise AssertionError("delta metadata mismatch")
    if data.get("equality_points") != EQPTS:
        raise AssertionError("equality-point metadata mismatch")
    if data.get("row_names") != row_names:
        raise AssertionError("moment-row metadata mismatch")
    if [tuple(x) for x in data.get("product_pairs", [])] != PROD_PAIRS:
        raise AssertionError("product-pair metadata mismatch")

    nodes = data["nodes"]
    seen: set[int] = set()
    stats: Counter[str] = Counter()
    max_depth = 0
    stack = [(0, root_lo, root_hi, 0)]

    while stack:
        idx, lo, hi, depth = stack.pop()
        if idx in seen or not (0 <= idx < len(nodes)):
            raise AssertionError("cycle, duplicate reach, or bad node index")
        seen.add(idx)
        max_depth = max(max_depth, depth)
        nd = nodes[idx]
        typ = nd.get("t")

        if typ == "s":
            dim = int(nd["d"])
            cut = rat(nd["c"])
            left = int(nd["a"])
            right = int(nd["b"])
            if not (0 <= dim < 8 and lo[dim] < cut < hi[dim]):
                raise AssertionError("invalid split")
            lo0, hi0 = list(lo), list(hi)
            lo1, hi1 = list(lo), list(hi)
            hi0[dim] = cut
            lo1[dim] = cut
            stack.append((right, tuple(lo1), tuple(hi1), depth + 1))
            stack.append((left, tuple(lo0), tuple(hi0), depth + 1))
            stats["split"] += 1
        elif typ == "e":
            reason = empty_chamber_reason(lo, hi)
            stored = nd.get("r")
            if reason is None or stored != reason:
                raise AssertionError(f"invalid empty leaf: stored={stored!r}, exact={reason!r}")
            stats["empty_" + reason] += 1
        elif typ == "l":
            pi = local_index(lo, hi)
            if pi is None or int(nd["p"]) != pi:
                raise AssertionError("invalid local/core leaf")
            stats["local"] += 1
        elif typ == "m":
            verify_mc_leaf(nd, lo, hi)
            stats["mc"] += 1
        else:
            raise AssertionError(f"unknown node type {typ!r}")

    if len(seen) != len(nodes):
        raise AssertionError("unreachable nodes")
    expected = Counter({str(k): int(v) for k, v in data.get("stats", {}).items()})
    if stats != expected:
        raise AssertionError(f"statistics mismatch: exact={dict(stats)}, stored={dict(expected)}")
    if max_depth != int(data.get("max_depth")):
        raise AssertionError("maximum-depth mismatch")

    print(path.name)
    print(f"  format={fmt}")
    print(f"  moment_rows=42 product_variables=22 inner_atoms=64")
    print(f"  nodes={len(nodes)} max_depth={max_depth} stats={dict(stats)}")
    print("  EXACT_BRANCH_CERTIFICATE_OK")


def main() -> None:
    args = [Path(x) for x in sys.argv[1:]]
    if not args:
        args = [
            HERE / "even_c527_sym_mc.json.gz",
            HERE / "even_local_core_mc.json.gz",
        ]
    for path in args:
        verify_one(path)
    print("ALL_EVEN_BRANCH_CERTIFICATES_OK")


if __name__ == "__main__":
    main()
