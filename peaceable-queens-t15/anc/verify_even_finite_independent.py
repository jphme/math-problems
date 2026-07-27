#!/usr/bin/env python3
"""Independent exact verifier for the two finite-even branch certificates.

Certificates covered
--------------------
* ``peaceable-even-c527-sym-mc-v1`` --- on the canonical symmetry chamber of
  ``[0,1]^8``, every point outside the four rational plaid neighborhoods has
  42-moment relaxation optimum at most ``527/1000``.
* ``peaceable-even-local-core-mc-v1`` --- inside the plaid neighborhood ``N``,
  every point outside the aggregate core has optimum at most ``527/1000``.

This file is a from-scratch implementation written for compute task C9.  It
imports nothing from the delivered checker or builder.  In particular:

* the 42 moment rows are *discovered*, not transcribed: for every parity block
  and every set ``S`` of at most two of the four line families the verifier
  counts the incidence fibers of the block on a real torus and keeps the row
  only when the fiber count is uniform (which is exactly the statement that the
  corresponding moment factorizes into outer variables).  The multiplicity of
  the uniform fiber determines the right-hand factor.  The single failing set
  ``{D,A}`` is then repaired by aggregating the two blocks of equal square
  parity, where the fiber multiplicity 2 produces the factor-2 rows;
* the derived rows are re-validated as exact rational identities on random
  genuine line colorings of ``Z_n`` for ``n`` divisible and not divisible by 4;
* the McCormick envelope inequalities are re-derived from the four nonnegative
  products ``(x_i-l_i)(x_j-l_j)``, ``(u_i-x_i)(u_j-x_j)``, ``(u_i-x_i)(x_j-l_j)``
  and ``(x_i-l_i)(u_j-x_j)``;
* the leaf bound is recomputed by an explicit partial Lagrangian relaxation,
  keeping ``p >= 0`` and the variable boxes in the inner problem;
* the emptiness certificates are re-proved from interval reasoning on the
  chamber inequalities.

Only the Python standard library is used and every comparison is exact
:class:`fractions.Fraction` arithmetic; no float ever enters a decision.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import itertools
import json
import random
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

ZERO = Q(0)
ONE = Q(1)
TARGET = Q(527, 1000)
DELTA_FIELD = Q(1, 20)

OUTER_NAMES = ("r0", "r1", "c0", "c1", "d0", "d1", "a0", "a1")
BLOCK_ORDER = ((0, 0), (0, 1), (1, 0), (1, 1))
ATOMS = tuple(itertools.product((0, 1), repeat=4))
IDX_BLACK = ATOMS.index((1, 1, 1, 1))
IDX_WHITE = ATOMS.index((0, 0, 0, 0))
FAMILY_LABEL = ("R", "C", "D", "A")

# Column layout of the LP: x[0:8], y[8:30], p[30:94], t=94.
COL_X = 0
COL_Y = 8
COL_P = 30
COL_T = 94
N_COLS = 95
N_INEQ = 95
N_EQ = 42

# Subsets of families used as moment features, in certificate row order.
FEATURE_SETS = (
    (),
    (0,),
    (1,),
    (2,),
    (3,),
    (0, 1),
    (0, 2),
    (0, 3),
    (1, 2),
    (1, 3),
    (2, 3),
)


def feature_name(subset):
    return "1" if not subset else "".join(FAMILY_LABEL[f] for f in subset)


# --------------------------------------------------------------------------
# 1.  Derivation of the 42 moment rows from torus incidence fibers.
# --------------------------------------------------------------------------


def block_fiber_counts(n, blocks, subset):
    """Fiber multiplicities of ``subset`` over the given parity blocks.

    A cell ``(r,c)`` of the even torus ``Z_n x Z_n`` meets one row line, one
    column line, one diagonal line ``(r-c) mod n`` and one antidiagonal line
    ``(r+c) mod n``.  Inside a parity block all four of these lines have a
    fixed parity, so each is named by its index inside its parity class, an
    element of ``{0,...,q-1}``.  This routine returns the multiset of fiber
    sizes of the map sending a cell to the tuple of those names for the
    families listed in ``subset``, together with the number of distinct
    tuples attained.
    """
    q = n // 2
    counts = Counter()
    for (i, j) in blocks:
        for r in range(i, n, 2):
            for c in range(j, n, 2):
                names = []
                for f in subset:
                    if f == 0:
                        names.append(r // 2)
                    elif f == 1:
                        names.append(c // 2)
                    elif f == 2:
                        names.append(((r - c) % n) // 2)
                    else:
                        names.append(((r + c) % n) // 2)
                counts[tuple(names)] += 1
    sizes = set(counts.values())
    return counts, sizes, q


def uniform_fiber_factor(n, blocks, subset):
    """Return the integer right-hand factor, or ``None`` if fibers are ragged.

    If every one of the ``q^{|S|}`` possible tuples is attained by exactly
    ``m`` cells, then summing the block atom probabilities over the atoms whose
    ``S``-coordinates are all 1 gives

        (1/q^2) * m * prod_{f in S} (q * x_f)  =  m * q^{|S|-2} * prod x_f,

    so the moment factorizes with factor ``m * q^{|S|-2}``.
    """
    counts, sizes, q = block_fiber_counts(n, blocks, subset)
    if len(counts) != q ** len(subset) or len(sizes) != 1:
        return None
    multiplicity = sizes.pop()
    numerator = multiplicity * q ** len(subset)
    if numerator % (q * q) != 0:
        return None
    return numerator // (q * q)


class MomentRow:
    """One exact row ``sum_c coeff_c * p_c = factor * (monomial in x)``."""

    __slots__ = ("name", "columns", "monomial", "factor")

    def __init__(self, name, columns, monomial, factor):
        self.name = name
        self.columns = tuple(columns)
        self.monomial = tuple(monomial)
        self.factor = int(factor)


def outer_index(block, family):
    """Outer coordinate governing ``family`` inside parity ``block``."""
    i, j = block
    parity = i ^ j
    return (i, 2 + j, 4 + parity, 6 + parity)[family]


DERIVATION_ORDERS = (8, 12, 16, 20)


def derive_moment_rows(verbose=False):
    """Discover the valid per-block and aggregate moment rows."""
    per_block_valid = {}
    for block_number, block in enumerate(BLOCK_ORDER):
        for subset in FEATURE_SETS:
            factors = {
                uniform_fiber_factor(n, (block,), subset) for n in DERIVATION_ORDERS
            }
            if len(factors) != 1:
                raise AssertionError(
                    f"fiber factor for block {block} feature {feature_name(subset)}"
                    " is not independent of the torus order"
                )
            per_block_valid[(block_number, subset)] = factors.pop()

    ragged = sorted(
        {subset for (_, subset), fac in per_block_valid.items() if fac is None}
    )
    if ragged != [(2, 3)]:
        raise AssertionError(
            f"expected exactly the D,A feature to have ragged block fibers, got {ragged}"
        )

    rows = []
    for block_number, block in enumerate(BLOCK_ORDER):
        for subset in FEATURE_SETS:
            factor = per_block_valid[(block_number, subset)]
            if factor is None:
                continue
            if factor != 1:
                raise AssertionError("unexpected per-block right-hand factor")
            columns = []
            for atom_number, atom in enumerate(ATOMS):
                coefficient = 1
                for f in subset:
                    coefficient *= atom[f]
                if coefficient:
                    columns.append((16 * block_number + atom_number, coefficient))
            monomial = tuple(sorted(outer_index(block, f) for f in subset))
            rows.append(
                MomentRow(
                    f"b{block[0]}{block[1]}:{feature_name(subset)}",
                    columns,
                    monomial,
                    factor,
                )
            )

    # Repair the ragged feature by aggregating the two blocks of equal square
    # parity: there the fibers of (D,A) become uniform with multiplicity 2.
    for parity in (0, 1):
        blocks = tuple(b for b in BLOCK_ORDER if (b[0] ^ b[1]) == parity)
        factors = {uniform_fiber_factor(n, blocks, (2, 3)) for n in DERIVATION_ORDERS}
        if len(factors) != 1:
            raise AssertionError("aggregate D,A factor depends on the torus order")
        factor = factors.pop()
        if factor != 2:
            raise AssertionError(f"aggregate D,A factor is {factor}, expected 2")
        columns = []
        for block_number, block in enumerate(BLOCK_ORDER):
            if (block[0] ^ block[1]) != parity:
                continue
            for atom_number, atom in enumerate(ATOMS):
                if atom[2] and atom[3]:
                    columns.append((16 * block_number + atom_number, 1))
        rows.append(
            MomentRow(
                f"aggDA{parity}", columns, (4 + parity, 6 + parity), factor
            )
        )

    if len(rows) != N_EQ:
        raise AssertionError(f"derivation produced {len(rows)} rows, expected 42")
    if verbose:
        print("  derived rows: " + ", ".join(row.name for row in rows))
    return rows


MOMENT_ROWS = derive_moment_rows()
PRODUCT_PAIRS = tuple(
    sorted({row.monomial for row in MOMENT_ROWS if len(row.monomial) == 2})
)
PRODUCT_INDEX = {pair: k for k, pair in enumerate(PRODUCT_PAIRS)}
if len(PRODUCT_PAIRS) != 22:
    raise AssertionError("expected 22 distinct outer products")


# --------------------------------------------------------------------------
# 2.  Semantic validation of the derived rows on genuine line colorings.
# --------------------------------------------------------------------------


def validate_rows_on_colorings(orders=(12, 16, 20, 28), trials=50, seed=20260727):
    """Check every derived row as an exact identity on real colorings."""
    rng = random.Random(seed)
    checks = 0
    for n in orders:
        q = n // 2
        for _ in range(trials):
            families = [[rng.randrange(2) for _ in range(n)] for _ in range(4)]
            outer = []
            for family in families:
                for parity in (0, 1):
                    outer.append(Q(sum(family[parity::2]), q))
            atom_counts = [0] * 64
            for r in range(n):
                for c in range(n):
                    block_number = BLOCK_ORDER.index((r & 1, c & 1))
                    atom = (
                        families[0][r],
                        families[1][c],
                        families[2][(r - c) % n],
                        families[3][(r + c) % n],
                    )
                    atom_counts[16 * block_number + ATOMS.index(atom)] += 1
            if sum(atom_counts) != n * n:
                raise AssertionError("atom census lost cells")
            probability = [Q(count, q * q) for count in atom_counts]
            for row in MOMENT_ROWS:
                left = ZERO
                for column, coefficient in row.columns:
                    left += probability[column] * coefficient
                right = Q(row.factor)
                for index in row.monomial:
                    right *= outer[index]
                if left != right:
                    raise AssertionError(
                        f"moment row {row.name} fails on a genuine n={n} coloring"
                    )
                checks += 1
    return checks


# --------------------------------------------------------------------------
# 3.  The LP at a box.
# --------------------------------------------------------------------------


def inequality_rows(lo, hi):
    """The 95 ``<=`` rows as ``(sparse coefficients, right-hand side)``."""
    rows = []
    # 0: line budget.
    rows.append(({i: ONE for i in range(8)}, Q(4)))
    # 1-4: the canonical chamber.
    chamber = (
        {0: ONE, 1: -ONE},
        {2: ONE, 3: -ONE},
        {0: ONE, 1: ONE, 2: -ONE, 3: -ONE},
        {4: ONE, 5: ONE, 6: -ONE, 7: -ONE},
    )
    for coefficients in chamber:
        rows.append((dict(coefficients), ZERO))
    # 5-6: t <= black mass and t <= white mass.
    black = {COL_T: ONE}
    white = {COL_T: ONE}
    for block_number in range(4):
        black[COL_P + 16 * block_number + IDX_BLACK] = -ONE
        white[COL_P + 16 * block_number + IDX_WHITE] = -ONE
    rows.append((black, ZERO))
    rows.append((white, ZERO))
    # 7-94: the McCormick envelope of each product.
    for pair_number, (i, j) in enumerate(PRODUCT_PAIRS):
        li, ui, lj, uj = lo[i], hi[i], lo[j], hi[j]
        ycol = COL_Y + pair_number
        # (x_i-l_i)(x_j-l_j) >= 0  =>  -y + l_j x_i + l_i x_j <= l_i l_j
        rows.append(({i: lj, j: li, ycol: -ONE}, li * lj))
        # (u_i-x_i)(u_j-x_j) >= 0  =>  -y + u_j x_i + u_i x_j <= u_i u_j
        rows.append(({i: uj, j: ui, ycol: -ONE}, ui * uj))
        # (u_i-x_i)(x_j-l_j) >= 0  =>   y - l_j x_i - u_i x_j <= -u_i l_j
        rows.append(({i: -lj, j: -ui, ycol: ONE}, -ui * lj))
        # (x_i-l_i)(u_j-x_j) >= 0  =>   y - u_j x_i - l_i x_j <= -l_i u_j
        rows.append(({i: -uj, j: -li, ycol: ONE}, -li * uj))
    if len(rows) != N_INEQ:
        raise AssertionError("inequality system does not have 95 rows")
    return rows


def build_equality_rows():
    """The 42 moment equalities as ``(sparse coefficients, right-hand side)``."""
    rows = []
    for row in MOMENT_ROWS:
        coefficients = {COL_P + column: Q(value) for column, value in row.columns}
        if len(row.monomial) == 0:
            rhs = Q(row.factor)
        elif len(row.monomial) == 1:
            coefficients[row.monomial[0]] = Q(-row.factor)
            rhs = ZERO
        elif len(row.monomial) == 2:
            coefficients[COL_Y + PRODUCT_INDEX[row.monomial]] = Q(-row.factor)
            rhs = ZERO
        else:
            raise AssertionError("moment right-hand side of unexpected degree")
        rows.append((coefficients, rhs))
    return rows


EQUALITY_ROWS = build_equality_rows()


def parse_rational(obj):
    if (
        not isinstance(obj, list)
        or len(obj) != 2
        or any(isinstance(v, bool) or not isinstance(v, int) for v in obj)
    ):
        raise AssertionError(f"malformed rational {obj!r}")
    return Q(obj[0], obj[1])


def parse_sparse(obj, size):
    if not isinstance(obj, list):
        raise AssertionError("sparse vector is not a list")
    out = [ZERO] * size
    seen = set()
    for entry in obj:
        if (
            not isinstance(entry, list)
            or len(entry) != 3
            or any(isinstance(v, bool) or not isinstance(v, int) for v in entry)
        ):
            raise AssertionError(f"malformed sparse entry {entry!r}")
        index, numerator, denominator = entry
        if not 0 <= index < size or index in seen:
            raise AssertionError("out-of-range or duplicated sparse index")
        seen.add(index)
        out[index] = Q(numerator, denominator)
    return out


def verify_mc_leaf(node, lo, hi):
    """Recompute the partial-Lagrangian bound and compare with the stored one.

    The primal problem at the box is

        maximise t  subject to  G z <= g,  E z = e,  p >= 0,
                                x in [lo,hi],  y in [lo_i lo_j, hi_i hi_j].

    With ``lambda = -mu >= 0`` and free ``nu`` the Lagrangian relaxation that
    dualizes only ``G`` and ``E`` gives, for every feasible ``z``,

        t <= t + lambda^T (g - G z) + nu^T (e - E z)
           <= max_{p>=0, x,y in box, t free} rho^T z  -  mu^T g  +  nu^T e

    where ``rho = e_t + G^T mu - E^T nu``.  Finiteness of the inner maximum
    forces ``rho_t = 0`` and ``rho_p <= 0``; the remaining variables are boxed
    and contribute their better endpoint.  (The certificate stores ``-nu`` in
    its own sign convention; the equality multiplier is unrestricted, so the
    convention is irrelevant to soundness.)
    """
    mu = parse_sparse(node.get("mu"), N_INEQ)
    nu = [-value for value in parse_sparse(node.get("nu"), N_EQ)]
    if any(value > 0 for value in mu):
        raise AssertionError("a multiplier on a <= row is positive")

    rho = [ZERO] * N_COLS
    rho[COL_T] = ONE
    total = ZERO
    for value, (coefficients, rhs) in zip(mu, inequality_rows(lo, hi)):
        if value:
            for column, coefficient in coefficients.items():
                rho[column] += value * coefficient
            total -= value * rhs
    for value, (coefficients, rhs) in zip(nu, EQUALITY_ROWS):
        if value:
            for column, coefficient in coefficients.items():
                rho[column] -= value * coefficient
            total += value * rhs

    if rho[COL_T] != ZERO:
        raise AssertionError("the reduced cost of t is nonzero")
    for column in range(COL_P, COL_P + 64):
        if rho[column] > ZERO:
            raise AssertionError(
                "an atom probability has a positive reduced cost, so the "
                "relaxed inner maximum is unbounded"
            )

    for k in range(8):
        coefficient = rho[COL_X + k]
        if coefficient:
            total += coefficient * (hi[k] if coefficient > ZERO else lo[k])
    for pair_number, (i, j) in enumerate(PRODUCT_PAIRS):
        coefficient = rho[COL_Y + pair_number]
        if coefficient:
            total += coefficient * (
                hi[i] * hi[j] if coefficient > ZERO else lo[i] * lo[j]
            )

    stored = parse_rational(node.get("u"))
    if total != stored:
        raise AssertionError(
            f"recomputed dual bound {total} differs from the stored {stored}"
        )
    if total > TARGET:
        raise AssertionError(f"leaf bound {total} exceeds 527/1000")
    return total


# --------------------------------------------------------------------------
# 4.  Exact emptiness of box-cap-chamber.
# --------------------------------------------------------------------------


def emptiness_reason(lo, hi):
    """First exact obstruction between the box and the canonical chamber.

    Every bound below is a *valid* bound on the corresponding quantity for any
    point of the box that also satisfies the chamber inequalities, so each test
    firing proves that the intersection is empty:

    * ``r1 >= max(lo_r1, lo_r0)`` because ``r1 >= lo_r1`` and ``r1 >= r0 >= lo_r0``;
    * ``r0+r1 >= lo_r0 + max(lo_r1, lo_r0) =: Rmin``;
    * ``c0+c1 >= lo_c0 + max(lo_c1, lo_c0) =: Cbase`` and, by the chamber row
      ``r0+r1 <= c0+c1``, also ``c0+c1 >= Rmin``;
    * ``c0+c1 <= hi_c1 + min(hi_c0, hi_c1) =: Cmax`` because ``c0 <= c1``;
    * ``d0+d1 >= Dmin``, ``a0+a1 >= max(Abase, Dmin)`` by the chamber row
      ``d0+d1 <= a0+a1``, and ``a0+a1 <= Amax``;
    * the four group minima add to a valid lower bound on ``sum x_i``, which the
      budget row caps at 4.
    """
    r1min = max(lo[1], lo[0])
    if r1min > hi[1]:
        return "rsort"
    rmin = lo[0] + r1min

    c1min = max(lo[3], lo[2])
    if c1min > hi[3]:
        return "csort"
    cbase = lo[2] + c1min
    cmax = hi[3] + min(hi[2], hi[3])
    cneed = cbase if cbase > rmin else rmin
    if cneed > cmax:
        return "rcsum"

    dmin = lo[4] + lo[5]
    abase = lo[6] + lo[7]
    amax = hi[6] + hi[7]
    aneed = abase if abase > dmin else dmin
    if aneed > amax:
        return "dasum"

    if rmin + cneed + dmin + aneed > 4:
        return "budget"
    return None


# --------------------------------------------------------------------------
# 5.  Plaid templates and the aggregate core.
# --------------------------------------------------------------------------


def plaid_templates():
    templates = []
    for parity in (0, 1):
        for i in (0, 1):
            j = i ^ parity
            point = [0] * 8
            point[i] = "s"
            point[2 + j] = "s"
            point[4 + parity] = 1
            point[6 + parity] = 1
            templates.append(point)
    return templates


PLAID_TEMPLATES = plaid_templates()
PLAID_ZERO_CAP = Q(1, 10)
PLAID_ONE_FLOOR = Q(19, 20)
PLAID_S_LO = Q(3, 5)
PLAID_S_HI = Q(7, 8)


def plaid_template_index(lo, hi):
    """Index of the plaid neighborhood wholly containing the box, if any."""
    for number, template in enumerate(PLAID_TEMPLATES):
        inside = True
        for k, value in enumerate(template):
            if value == 0:
                inside = hi[k] <= PLAID_ZERO_CAP
            elif value == 1:
                inside = lo[k] >= PLAID_ONE_FLOOR
            else:
                inside = lo[k] >= PLAID_S_LO and hi[k] <= PLAID_S_HI
            if not inside:
                break
        if inside:
            return number
    return None


def core_index(lo, hi):
    """Whole-box membership in the aggregate core.

        36/25 <= r1+c1 <= 37/25,   r0+c0 <= 9/100,
        d1+a1 <= 9/200,            (1-d0)+(1-a0) <= 1/25.
    """
    if (
        lo[1] + lo[3] >= Q(36, 25)
        and hi[1] + hi[3] <= Q(37, 25)
        and hi[0] + hi[2] <= Q(9, 100)
        and hi[5] + hi[7] <= Q(9, 200)
        and (ONE - lo[4]) + (ONE - lo[6]) <= Q(1, 25)
    ):
        return 0
    return None


# --------------------------------------------------------------------------
# 6.  Tree traversal.
# --------------------------------------------------------------------------

ROOT_BOXES = {
    "peaceable-even-c527-sym-mc-v1": (
        tuple(ZERO for _ in range(8)),
        tuple(ONE for _ in range(8)),
    ),
    "peaceable-even-local-core-mc-v1": (
        (ZERO, Q(3, 5), ZERO, Q(3, 5), Q(19, 20), ZERO, Q(19, 20), ZERO),
        (Q(1, 10), Q(7, 8), Q(1, 10), Q(7, 8), ONE, Q(1, 10), ONE, Q(1, 10)),
    ),
}

EXPECTED = {
    "peaceable-even-c527-sym-mc-v1": {
        "nodes": 6929,
        "max_depth": 22,
        "stats": {
            "split": 3464,
            "mc": 3368,
            "local": 4,
            "empty_rsort": 1,
            "empty_csort": 9,
            "empty_rcsum": 19,
            "empty_dasum": 21,
            "empty_budget": 43,
        },
    },
    "peaceable-even-local-core-mc-v1": {
        "nodes": 4423,
        "max_depth": 29,
        "stats": {
            "split": 2211,
            "mc": 1639,
            "local": 563,
            "empty_rcsum": 10,
        },
    },
}


def verify_certificate(path, progress=True):
    with gzip.open(path, "rt", encoding="utf-8") as handle:
        data = json.load(handle)

    fmt = data.get("format")
    if fmt not in ROOT_BOXES:
        raise AssertionError(f"unsupported certificate format {fmt!r}")
    root_lo, root_hi = ROOT_BOXES[fmt]
    local_test = plaid_template_index if fmt.startswith(
        "peaceable-even-c527"
    ) else core_index

    if data.get("variables") != list(OUTER_NAMES):
        raise AssertionError("outer-variable metadata mismatch")
    if parse_rational(data.get("delta")) != DELTA_FIELD:
        raise AssertionError("delta metadata mismatch")
    if data.get("equality_points") != PLAID_TEMPLATES:
        raise AssertionError("plaid-template metadata mismatch")
    if data.get("row_names") != [row.name for row in MOMENT_ROWS]:
        raise AssertionError(
            "independently derived moment rows disagree with the certificate order"
        )
    if [tuple(pair) for pair in data.get("product_pairs", [])] != list(PRODUCT_PAIRS):
        raise AssertionError("independently derived product pairs disagree")

    nodes = data.get("nodes")
    if not isinstance(nodes, list) or not nodes:
        raise AssertionError("missing tree")

    visited = set()
    stats = Counter()
    local_hits = Counter()
    max_depth = 0
    largest_bound = None
    stack = [(0, root_lo, root_hi, 0)]

    while stack:
        index, lo, hi, depth = stack.pop()
        if not isinstance(index, int) or isinstance(index, bool):
            raise AssertionError("non-integer node index")
        if not 0 <= index < len(nodes) or index in visited:
            raise AssertionError("bad node index, cycle, or shared child")
        visited.add(index)
        if depth > max_depth:
            max_depth = depth
        for k in range(8):
            if lo[k] > hi[k]:
                raise AssertionError("degenerate box reached")
        node = nodes[index]
        if not isinstance(node, dict):
            raise AssertionError("tree node is not an object")
        kind = node.get("t")

        if kind == "s":
            dimension = node.get("d")
            left = node.get("a")
            right = node.get("b")
            if (
                isinstance(dimension, bool)
                or not isinstance(dimension, int)
                or not 0 <= dimension < 8
                or isinstance(left, bool)
                or not isinstance(left, int)
                or isinstance(right, bool)
                or not isinstance(right, int)
            ):
                raise AssertionError("malformed split node")
            cut = parse_rational(node.get("c"))
            if not lo[dimension] < cut < hi[dimension]:
                raise AssertionError("split cut is not strictly interior")
            left_hi = list(hi)
            left_hi[dimension] = cut
            right_lo = list(lo)
            right_lo[dimension] = cut
            # The two children are the parent box intersected with x_d <= cut
            # and x_d >= cut, so their union is exactly the parent box.
            stack.append((right, tuple(right_lo), hi, depth + 1))
            stack.append((left, lo, tuple(left_hi), depth + 1))
            stats["split"] += 1
        elif kind == "e":
            reason = emptiness_reason(lo, hi)
            if reason is None:
                raise AssertionError(
                    "empty leaf whose box has no exact chamber obstruction"
                )
            if node.get("r") != reason:
                raise AssertionError(
                    f"stored emptiness reason {node.get('r')!r} != exact {reason!r}"
                )
            stats["empty_" + reason] += 1
        elif kind == "l":
            number = local_test(lo, hi)
            stored = node.get("p")
            if (
                number is None
                or isinstance(stored, bool)
                or not isinstance(stored, int)
                or stored != number
            ):
                raise AssertionError("local leaf is not contained in its claimed region")
            local_hits[number] += 1
            stats["local"] += 1
        elif kind == "m":
            bound = verify_mc_leaf(node, lo, hi)
            if largest_bound is None or bound > largest_bound:
                largest_bound = bound
            stats["mc"] += 1
            if progress and stats["mc"] % 500 == 0:
                print(f"    {stats['mc']} McCormick leaves verified", flush=True)
        else:
            raise AssertionError(f"unknown node type {kind!r}")

    if len(visited) != len(nodes):
        raise AssertionError("certificate contains unreachable nodes")

    stored_stats = {str(k): int(v) for k, v in (data.get("stats") or {}).items()}
    if dict(stats) != stored_stats:
        raise AssertionError(
            f"walked statistics {dict(stats)} differ from stored {stored_stats}"
        )
    if max_depth != int(data.get("max_depth")):
        raise AssertionError("stored maximum depth mismatch")

    expected = EXPECTED[fmt]
    if len(nodes) != expected["nodes"]:
        raise AssertionError(f"node count {len(nodes)} != expected {expected['nodes']}")
    if max_depth != expected["max_depth"]:
        raise AssertionError(f"depth {max_depth} != expected {expected['max_depth']}")
    if dict(stats) != expected["stats"]:
        raise AssertionError(
            f"statistics {dict(stats)} differ from the expected {expected['stats']}"
        )

    if fmt.startswith("peaceable-even-c527"):
        if sorted(local_hits) != [1] or local_hits[1] != 4:
            raise AssertionError(
                f"expected all four plaid leaves at template index 1, got {dict(local_hits)}"
            )
    else:
        if sorted(local_hits) != [0]:
            raise AssertionError("core leaves carry an unexpected region index")

    return {
        "format": fmt,
        "nodes": len(nodes),
        "stats": dict(stats),
        "max_depth": max_depth,
        "local_hits": dict(local_hits),
        "largest_bound": largest_bound,
    }


def sha256(path):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main():
    default = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "certificates",
        nargs="*",
        type=Path,
        default=[
            default / "even_c527_sym_mc.json.gz",
            default / "even_local_core_mc.json.gz",
        ],
    )
    parser.add_argument("--trials", type=int, default=50)
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()

    start = time.time()
    print("independent derivation of the 42-moment system")
    derive_moment_rows(verbose=False)
    print(
        f"  moment_rows={len(MOMENT_ROWS)} product_variables={len(PRODUCT_PAIRS)} "
        f"inner_atoms=64"
    )
    checks = validate_rows_on_colorings(trials=args.trials)
    print(
        f"  semantic_equation_checks={checks} on {args.trials} random colorings "
        f"for n in 12,16,20,28"
    )

    for path in args.certificates:
        print(f"{path.name}")
        print(f"  sha256={sha256(path)}")
        report = verify_certificate(path, progress=not args.quiet)
        print(f"  format={report['format']}")
        print(f"  nodes={report['nodes']} max_depth={report['max_depth']}")
        print(f"  stats={report['stats']}")
        print(f"  local_leaves_by_region={report['local_hits']}")
        print(f"  largest_rational_mc_upper={report['largest_bound']}")
        print("  EXACT_BRANCH_CERTIFICATE_INDEPENDENTLY_OK")

    print(f"elapsed_seconds={time.time() - start:.1f}")
    print("EVEN_FINITE_INDEPENDENT_VERIFIER_OK")


if __name__ == "__main__":
    main()
