#!/usr/bin/env python3
"""Independent exact verifier for the 760 support-dual cuts.

This file intentionally does not import any project verifier.  Its certificate
path uses only the Python standard library, with ``fractions.Fraction`` for
every arithmetic operation that affects a verdict.

The 42 moment rows are generated from the four torus parity blocks and the
R/C/D/A atom incidences.  Missing witnesses for the 76 legacy Benders
polynomials are recovered by a small exact two-phase simplex implementation.
All recovered witnesses are then checked in exactly the same columnwise path
as the 684 delivered witnesses.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import os
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Sequence


SCHEMA = "peaceable-queens-envelope-e1-v1"
RECOVERY_SCHEMA = "peaceable-queens-envelope-e1-recovered-benders-v1"
CHECKER_VERSION = 1

SCRIPT_DIR = Path(__file__).resolve().parent
PEACEABLE_QUEENS_DIR = SCRIPT_DIR.parent
DEFAULT_NEW_CUTS = SCRIPT_DIR / "new_dual_cuts.json"
DEFAULT_BENDERS_CUTS = SCRIPT_DIR / "benders_cuts.json"
DEFAULT_RECOVERED = SCRIPT_DIR / "recovered_benders_duals.json"
DEFAULT_MOMENT_MODEL = SCRIPT_DIR / "moment_model.json"
DEFAULT_OUTPUT = SCRIPT_DIR / "verification.json"

OUTER_NAMES = ("r0", "r1", "c0", "c1", "d0", "d1", "a0", "a1")
LINE_NAMES = ("R", "C", "D", "A")
PARITY_BLOCKS = ((0, 0), (0, 1), (1, 0), (1, 1))
ATOMS = tuple(itertools.product((0, 1), repeat=4))
BLACK_ATOM = (1, 1, 1, 1)
WHITE_ATOM = (0, 0, 0, 0)

# Coordinate covectors on Z_(2q)^2.  The determinants explain why the five
# local pair products have one lift, while D/A has two lifts and must be
# aggregated over both blocks of a square parity.
LINE_COVECTORS = {
    "R": (1, 0),
    "C": (0, 1),
    "D": (1, -1),
    "A": (1, 1),
}
LOCAL_PAIR_LABELS = (("R", "C"), ("R", "D"), ("R", "A"), ("C", "D"), ("C", "A"))
LOCAL_FEATURES = (
    ("1", ()),
    ("R", (0,)),
    ("C", (1,)),
    ("D", (2,)),
    ("A", (3,)),
    ("RC", (0, 1)),
    ("RD", (0, 2)),
    ("RA", (0, 3)),
    ("CD", (1, 2)),
    ("CA", (1, 3)),
)


class InputError(ValueError):
    """Malformed or inconsistent input artifact."""


def _reject_duplicate_object_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise InputError(f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def load_json_strict(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_reject_duplicate_object_keys)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise InputError(f"cannot read strict JSON from {path}: {exc}") from exc


def canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode(
        "ascii"
    )


def atomic_write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    data = canonical_json_bytes(value)
    with temporary.open("wb") as handle:
        handle.write(data)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_sha256(value: Any) -> str:
    return sha256_bytes(canonical_json_bytes(value))


def portable_path(path: Path) -> str:
    """Use an ancillary-directory-relative path when possible."""

    resolved = path.resolve()
    try:
        return str(resolved.relative_to(SCRIPT_DIR))
    except ValueError:
        return str(resolved)


def is_plain_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def parse_rational(value: Any, context: str) -> Fraction:
    if (
        not isinstance(value, list)
        or len(value) != 2
        or not is_plain_int(value[0])
        or not is_plain_int(value[1])
        or value[1] <= 0
    ):
        raise InputError(f"{context}: expected [integer, positive-integer], got {value!r}")
    result = Fraction(value[0], value[1])
    if result.numerator != value[0] or result.denominator != value[1]:
        raise InputError(f"{context}: rational is not in normalized form: {value!r}")
    return result


def rational_json(value: Fraction | int) -> list[int]:
    value = Fraction(value)
    return [value.numerator, value.denominator]


def rational_text(value: Fraction | int) -> str:
    value = Fraction(value)
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def parse_monomial(key: Any, context: str) -> tuple[int, ...]:
    if not isinstance(key, str):
        raise InputError(f"{context}: monomial key is not a string")
    if key == "":
        return ()
    pieces = key.split(",")
    if any(not piece.isdigit() for piece in pieces):
        raise InputError(f"{context}: malformed monomial {key!r}")
    monomial = tuple(int(piece) for piece in pieces)
    if len(monomial) not in (1, 2):
        raise InputError(f"{context}: only degree <= 2 monomials are allowed: {key!r}")
    if monomial != tuple(sorted(monomial)) or len(set(monomial)) != len(monomial):
        raise InputError(f"{context}: monomial is not strictly sorted: {key!r}")
    if any(not 0 <= index < len(OUTER_NAMES) for index in monomial):
        raise InputError(f"{context}: outer index out of range: {key!r}")
    return monomial


def parse_polynomial(value: Any, context: str) -> dict[tuple[int, ...], Fraction]:
    if not isinstance(value, dict):
        raise InputError(f"{context}: polynomial is not an object")
    result: dict[tuple[int, ...], Fraction] = {}
    for key, coefficient in value.items():
        monomial = parse_monomial(key, context)
        parsed = parse_rational(coefficient, f"{context}[{key!r}]")
        if parsed == 0:
            raise InputError(f"{context}[{key!r}]: explicit zero coefficient is not canonical")
        result[monomial] = parsed
    return result


def polynomial_json(polynomial: dict[tuple[int, ...], Fraction]) -> dict[str, list[int]]:
    result: dict[str, list[int]] = {}
    for monomial in sorted(polynomial, key=lambda item: (len(item), item)):
        key = ",".join(str(index) for index in monomial)
        result[key] = rational_json(polynomial[monomial])
    return result


def parse_sparse_dual(value: Any, size: int, context: str) -> list[Fraction]:
    if not isinstance(value, list):
        raise InputError(f"{context}: sparse vector is not a list")
    result = [Fraction(0) for _ in range(size)]
    occupied: set[int] = set()
    previous = -1
    for offset, item in enumerate(value):
        item_context = f"{context}[{offset}]"
        if (
            not isinstance(item, list)
            or len(item) != 3
            or not all(is_plain_int(component) for component in item)
        ):
            raise InputError(f"{item_context}: expected [index, numerator, denominator]")
        index, numerator, denominator = item
        if not 0 <= index < size:
            raise InputError(f"{item_context}: index {index} is out of range")
        if index in occupied:
            raise InputError(f"{item_context}: duplicate sparse index {index}")
        if index <= previous:
            raise InputError(f"{item_context}: sparse indices are not strictly increasing")
        occupied.add(index)
        previous = index
        coefficient = parse_rational([numerator, denominator], item_context)
        if coefficient == 0:
            raise InputError(f"{item_context}: zero entries must be omitted")
        result[index] = coefficient
    return result


def sparse_dual_json(vector: Sequence[Fraction]) -> list[list[int]]:
    return [
        [index, coefficient.numerator, coefficient.denominator]
        for index, coefficient in enumerate(vector)
        if coefficient
    ]


def determinant(left: tuple[int, int], right: tuple[int, int]) -> int:
    return left[0] * right[1] - left[1] * right[0]


@dataclass(frozen=True)
class MomentRow:
    name: str
    columns: tuple[int, ...]
    monomial: tuple[int, ...]
    factor: int
    derivation: str


def derive_moment_rows() -> tuple[MomentRow, ...]:
    """Generate the 42 rows from parity blocks and Boolean atom features."""

    rows: list[MomentRow] = []
    for block_number, (row_parity, column_parity) in enumerate(PARITY_BLOCKS):
        square_parity = row_parity ^ column_parity
        outer_coordinates = (
            row_parity,
            2 + column_parity,
            4 + square_parity,
            6 + square_parity,
        )
        for label, feature_positions in LOCAL_FEATURES:
            coefficients: list[int] = []
            for candidate_block, _ in enumerate(PARITY_BLOCKS):
                for atom in ATOMS:
                    if candidate_block != block_number:
                        coefficients.append(0)
                    else:
                        coefficient = math.prod(atom[position] for position in feature_positions)
                        coefficients.append(coefficient)
            monomial = tuple(sorted(outer_coordinates[position] for position in feature_positions))
            if len(feature_positions) == 0:
                derivation = "parity-block normalization"
            elif len(feature_positions) == 1:
                derivation = f"{LINE_NAMES[feature_positions[0]]} marginal fiber size q"
            else:
                left = LINE_NAMES[feature_positions[0]]
                right = LINE_NAMES[feature_positions[1]]
                det = determinant(LINE_COVECTORS[left], LINE_COVECTORS[right])
                if abs(det) != 1:
                    raise AssertionError(f"unexpected non-unimodular local pair {left}{right}")
                derivation = f"{left}/{right} determinant {det:+d}"
            rows.append(
                MomentRow(
                    name=f"b{row_parity}{column_parity}:{label}",
                    columns=tuple(coefficients),
                    monomial=monomial,
                    factor=1,
                    derivation=derivation,
                )
            )

    # The D/A coordinate determinant is 2.  For every equal-parity (d,a)
    # pair there are exactly two torus lifts in the union of the two blocks
    # r xor c = e, so only the aggregate equation is sound for all q.
    da_det = determinant(LINE_COVECTORS["D"], LINE_COVECTORS["A"])
    if da_det != 2:
        raise AssertionError("D/A determinant derivation failed")
    for square_parity in (0, 1):
        coefficients = []
        for row_parity, column_parity in PARITY_BLOCKS:
            in_aggregate = row_parity ^ column_parity == square_parity
            for atom in ATOMS:
                coefficients.append(int(in_aggregate and atom[2] and atom[3]))
        rows.append(
            MomentRow(
                name=f"aggDA{square_parity}",
                columns=tuple(coefficients),
                monomial=(4 + square_parity, 6 + square_parity),
                factor=2,
                derivation="D/A determinant +2; two-lift aggregate",
            )
        )

    if len(rows) != 42 or any(len(row.columns) != 64 for row in rows):
        raise AssertionError("moment derivation did not yield a 42 by 64 matrix")
    return tuple(rows)


def line_label(line: str, row: int, column: int, modulus: int) -> int:
    if line == "R":
        return row
    if line == "C":
        return column
    if line == "D":
        return (row - column) % modulus
    if line == "A":
        return (row + column) % modulus
    raise AssertionError(f"unknown line family {line}")


def audit_torus_fibers(max_q: int = 12) -> dict[str, Any]:
    """Check the incidence fibers used in the symbolic row derivation."""

    if max_q < 1:
        raise ValueError("max_q must be positive")
    local_determinants = {
        left + right: determinant(LINE_COVECTORS[left], LINE_COVECTORS[right])
        for left, right in LOCAL_PAIR_LABELS
    }
    if any(abs(value) != 1 for value in local_determinants.values()):
        raise AssertionError("a local product pair is not unimodular")
    if determinant(LINE_COVECTORS["D"], LINE_COVECTORS["A"]) != 2:
        raise AssertionError("D/A determinant is not 2")

    checks = 0
    for q in range(1, max_q + 1):
        modulus = 2 * q
        cells_by_block: dict[tuple[int, int], list[tuple[int, int]]] = {
            block: [] for block in PARITY_BLOCKS
        }
        for row in range(modulus):
            for column in range(modulus):
                cells_by_block[(row & 1, column & 1)].append((row, column))

        for row_parity, column_parity in PARITY_BLOCKS:
            block = cells_by_block[(row_parity, column_parity)]
            if len(block) != q * q:
                raise AssertionError("parity block normalization failed")
            checks += 1
            square_parity = row_parity ^ column_parity
            label_parities = {
                "R": row_parity,
                "C": column_parity,
                "D": square_parity,
                "A": square_parity,
            }

            for line in LINE_NAMES:
                counts: dict[int, int] = {}
                for cell in block:
                    label = line_label(line, *cell, modulus)
                    counts[label] = counts.get(label, 0) + 1
                expected_labels = range(label_parities[line], modulus, 2)
                for label in expected_labels:
                    if counts.get(label, 0) != q:
                        raise AssertionError(f"{line} marginal fiber failed at q={q}")
                    checks += 1
                if set(counts) != set(expected_labels):
                    raise AssertionError(f"{line} marginal parity failed at q={q}")

            for left, right in LOCAL_PAIR_LABELS:
                counts: dict[tuple[int, int], int] = {}
                for cell in block:
                    key = (
                        line_label(left, *cell, modulus),
                        line_label(right, *cell, modulus),
                    )
                    counts[key] = counts.get(key, 0) + 1
                expected = {
                    (left_label, right_label)
                    for left_label in range(label_parities[left], modulus, 2)
                    for right_label in range(label_parities[right], modulus, 2)
                }
                if set(counts) != expected or any(counts[key] != 1 for key in expected):
                    raise AssertionError(f"{left}{right} unit fiber failed at q={q}")
                checks += len(expected)

        for square_parity in (0, 1):
            counts: dict[tuple[int, int], int] = {}
            for block, cells in cells_by_block.items():
                if block[0] ^ block[1] != square_parity:
                    continue
                for cell in cells:
                    key = (
                        line_label("D", *cell, modulus),
                        line_label("A", *cell, modulus),
                    )
                    counts[key] = counts.get(key, 0) + 1
            expected = {
                (diagonal, antidiagonal)
                for diagonal in range(square_parity, modulus, 2)
                for antidiagonal in range(square_parity, modulus, 2)
            }
            if set(counts) != expected or any(counts[key] != 2 for key in expected):
                raise AssertionError(f"D/A two-lift aggregate failed at q={q}")
            checks += len(expected)

    return {
        "passed": True,
        "q_range": [1, max_q],
        "orders": [2 * q for q in range(1, max_q + 1)],
        "fiber_checks": checks,
        "local_pair_determinants": local_determinants,
        "aggregate_DA_determinant": 2,
    }


def moment_model_json(rows: Sequence[MomentRow]) -> dict[str, Any]:
    return {
        "outer_order": list(OUTER_NAMES),
        "block_order": [list(block) for block in PARITY_BLOCKS],
        "atom_order": [list(atom) for atom in ATOMS],
        "rows": [
            {
                "index": index,
                "name": row.name,
                "monomial": list(row.monomial),
                "factor": row.factor,
                "columns": list(row.columns),
                "derivation": row.derivation,
            }
            for index, row in enumerate(rows)
        ],
    }


def induced_polynomial(
    rows: Sequence[MomentRow], dual: Sequence[Fraction]
) -> dict[tuple[int, ...], Fraction]:
    if len(dual) != len(rows):
        raise AssertionError("dual length does not match moment rows")
    polynomial: dict[tuple[int, ...], Fraction] = {}
    for row, multiplier in zip(rows, dual):
        if multiplier:
            polynomial[row.monomial] = polynomial.get(row.monomial, Fraction(0)) + row.factor * multiplier
    return {monomial: coefficient for monomial, coefficient in polynomial.items() if coefficient}


def verify_witness(
    rows: Sequence[MomentRow],
    source_polynomial: dict[tuple[int, ...], Fraction],
    alpha: Fraction,
    dual: Sequence[Fraction],
) -> dict[str, Any]:
    alpha_ok = Fraction(0) <= alpha <= Fraction(1)
    induced = induced_polynomial(rows, dual)
    polynomial_ok = induced == source_polynomial
    slacks: list[Fraction] = []
    violating_columns: list[int] = []
    for column in range(64):
        lhs = sum(
            (dual[row_index] * row.columns[column] for row_index, row in enumerate(rows)),
            Fraction(0),
        )
        atom = ATOMS[column % 16]
        target = alpha if atom == BLACK_ATOM else 1 - alpha if atom == WHITE_ATOM else Fraction(0)
        slack = lhs - target
        slacks.append(slack)
        if slack < 0:
            violating_columns.append(column)
    support_ok = not violating_columns
    minimum_slack = min(slacks)
    return {
        "alpha_in_unit_interval": alpha_ok,
        "polynomial_consistency": polynomial_ok,
        "columnwise_support": support_ok,
        "passed": alpha_ok and polynomial_ok and support_ok,
        "minimum_slack": rational_json(minimum_slack),
        "tight_column_count": sum(slack == 0 for slack in slacks),
        "violating_columns": violating_columns,
        "nonzero_dual_entries": sum(bool(value) for value in dual),
        "maximum_dual_denominator": max(value.denominator for value in dual),
        "induced_polynomial_sha256": canonical_sha256(polynomial_json(induced)),
    }


class ExactSimplex:
    """Deterministic exact two-phase simplex for max c*x, A*x <= b, x >= 0."""

    INFEASIBLE = "infeasible"
    OPTIMAL = "optimal"
    UNBOUNDED = "unbounded"

    def __init__(
        self,
        matrix: Sequence[Sequence[Fraction]],
        bounds: Sequence[Fraction],
        objective: Sequence[Fraction],
    ) -> None:
        self.m = len(bounds)
        self.n = len(objective)
        if self.m == 0 or self.n == 0:
            raise ValueError("the exact simplex expects a nonempty LP")
        if len(matrix) != self.m or any(len(row) != self.n for row in matrix):
            raise ValueError("LP matrix dimensions are inconsistent")

        self.basic = [self.n + index for index in range(self.m)]
        self.nonbasic = list(range(self.n)) + [-1]
        self.tableau = [
            [Fraction(0) for _ in range(self.n + 2)] for _ in range(self.m + 2)
        ]
        for row in range(self.m):
            for column in range(self.n):
                self.tableau[row][column] = Fraction(matrix[row][column])
            self.tableau[row][self.n] = Fraction(-1)
            self.tableau[row][self.n + 1] = Fraction(bounds[row])
        for column in range(self.n):
            self.tableau[self.m][column] = -Fraction(objective[column])
        self.tableau[self.m + 1][self.n] = Fraction(1)

    def pivot(self, leaving: int, entering: int) -> None:
        pivot = self.tableau[leaving][entering]
        if pivot == 0:
            raise ArithmeticError("zero simplex pivot")
        inverse = Fraction(1) / pivot
        for row in range(self.m + 2):
            if row == leaving:
                continue
            entering_value = self.tableau[row][entering]
            if entering_value == 0:
                continue
            for column in range(self.n + 2):
                if column == entering:
                    continue
                self.tableau[row][column] -= (
                    self.tableau[leaving][column] * entering_value * inverse
                )
        for column in range(self.n + 2):
            if column != entering:
                self.tableau[leaving][column] *= inverse
        for row in range(self.m + 2):
            if row != leaving:
                self.tableau[row][entering] *= -inverse
        self.tableau[leaving][entering] = inverse
        self.basic[leaving], self.nonbasic[entering] = (
            self.nonbasic[entering],
            self.basic[leaving],
        )

    def run_phase(self, phase: int) -> bool:
        objective_row = self.m + 1 if phase == 1 else self.m
        while True:
            entering: int | None = None
            for column in range(self.n + 1):
                if phase == 2 and self.nonbasic[column] == -1:
                    continue
                if entering is None:
                    entering = column
                    continue
                candidate = (self.tableau[objective_row][column], self.nonbasic[column])
                incumbent = (self.tableau[objective_row][entering], self.nonbasic[entering])
                if candidate < incumbent:
                    entering = column
            if entering is None or self.tableau[objective_row][entering] >= 0:
                return True

            leaving: int | None = None
            for row in range(self.m):
                coefficient = self.tableau[row][entering]
                if coefficient <= 0:
                    continue
                if leaving is None:
                    leaving = row
                    continue
                candidate = (
                    self.tableau[row][self.n + 1] / coefficient,
                    self.basic[row],
                )
                incumbent = (
                    self.tableau[leaving][self.n + 1]
                    / self.tableau[leaving][entering],
                    self.basic[leaving],
                )
                if candidate < incumbent:
                    leaving = row
            if leaving is None:
                return False
            self.pivot(leaving, entering)

    def solve(self) -> tuple[str, Fraction | None, list[Fraction] | None]:
        leaving = min(
            range(self.m),
            key=lambda row: (self.tableau[row][self.n + 1], self.basic[row]),
        )
        if self.tableau[leaving][self.n + 1] < 0:
            self.pivot(leaving, self.n)
            if not self.run_phase(1) or self.tableau[self.m + 1][self.n + 1] != 0:
                return self.INFEASIBLE, None, None
            for row in range(self.m):
                if self.basic[row] != -1:
                    continue
                entering = min(
                    range(self.n + 1),
                    key=lambda column: (self.tableau[row][column], self.nonbasic[column]),
                )
                if self.tableau[row][entering] != 0:
                    self.pivot(row, entering)

        if not self.run_phase(2):
            return self.UNBOUNDED, None, None
        solution = [Fraction(0) for _ in range(self.n)]
        for row in range(self.m):
            if 0 <= self.basic[row] < self.n:
                solution[self.basic[row]] = self.tableau[row][self.n + 1]
        return self.OPTIMAL, self.tableau[self.m][self.n + 1], solution


def exact_simplex_self_test() -> dict[str, Any]:
    tests = 0

    # max x+y subject to x<=2, y<=3, x+y<=4.
    status, value, solution = ExactSimplex(
        [
            [Fraction(1), Fraction(0)],
            [Fraction(0), Fraction(1)],
            [Fraction(1), Fraction(1)],
        ],
        [Fraction(2), Fraction(3), Fraction(4)],
        [Fraction(1), Fraction(1)],
    ).solve()
    if status != ExactSimplex.OPTIMAL or value != 4 or solution is None:
        raise AssertionError("exact simplex bounded self-test failed")
    if solution[0] + solution[1] != 4:
        raise AssertionError("exact simplex solution self-test failed")
    tests += 1

    # x <= 0 and x >= 1 is infeasible.
    status, _, _ = ExactSimplex(
        [[Fraction(1)], [Fraction(-1)]],
        [Fraction(0), Fraction(-1)],
        [Fraction(0)],
    ).solve()
    if status != ExactSimplex.INFEASIBLE:
        raise AssertionError("exact simplex infeasibility self-test failed")
    tests += 1

    # max x with only -x <= 0 is unbounded.
    status, _, _ = ExactSimplex(
        [[Fraction(-1)]],
        [Fraction(0)],
        [Fraction(1)],
    ).solve()
    if status != ExactSimplex.UNBOUNDED:
        raise AssertionError("exact simplex unbounded self-test failed")
    tests += 1
    return {"passed": True, "tests": tests}


@dataclass
class AffineDual:
    base: list[Fraction]
    directions: list[list[Fraction]]

    def evaluate(self, parameters: Sequence[Fraction]) -> list[Fraction]:
        if len(parameters) != len(self.directions):
            raise ValueError("wrong number of affine dual parameters")
        result = list(self.base)
        for parameter, direction in zip(parameters, self.directions):
            if parameter:
                for row, coefficient in enumerate(direction):
                    result[row] += parameter * coefficient
        return result


def dual_parameterization(
    rows: Sequence[MomentRow], polynomial: dict[tuple[int, ...], Fraction]
) -> AffineDual:
    """Solve polynomial consistency, leaving 11 multiplier-split parameters."""

    rows_by_monomial: dict[tuple[int, ...], list[int]] = {}
    for index, row in enumerate(rows):
        rows_by_monomial.setdefault(row.monomial, []).append(index)
    allowed = set(rows_by_monomial)
    unsupported = sorted(set(polynomial) - allowed)
    if unsupported:
        raise InputError(f"polynomial has unsupported monomials: {unsupported}")

    base = [Fraction(0) for _ in rows]
    directions: list[list[Fraction]] = []

    constant_rows = rows_by_monomial[()]
    if len(constant_rows) != 4:
        raise AssertionError("expected four constant moment rows")
    constant = polynomial.get((), Fraction(0))
    base[constant_rows[-1]] = constant
    for row in constant_rows[:-1]:
        direction = [Fraction(0) for _ in rows]
        direction[row] = 1
        direction[constant_rows[-1]] = -1
        directions.append(direction)

    for outer_index in range(8):
        monomial = (outer_index,)
        linear_rows = rows_by_monomial[monomial]
        if len(linear_rows) != 2:
            raise AssertionError(f"expected two rows for linear monomial {monomial}")
        total = polynomial.get(monomial, Fraction(0))
        base[linear_rows[-1]] = total
        direction = [Fraction(0) for _ in rows]
        direction[linear_rows[0]] = 1
        direction[linear_rows[-1]] = -1
        directions.append(direction)

    for monomial, matching_rows in rows_by_monomial.items():
        if len(monomial) != 2:
            continue
        if len(matching_rows) != 1:
            raise AssertionError(f"product monomial {monomial} is not forced")
        row_index = matching_rows[0]
        base[row_index] = polynomial.get(monomial, Fraction(0)) / rows[row_index].factor

    if len(directions) != 11:
        raise AssertionError("polynomial consistency should leave exactly 11 directions")
    if induced_polynomial(rows, base) != polynomial:
        raise AssertionError("affine dual base does not induce the source polynomial")
    for direction in directions:
        if induced_polynomial(rows, direction):
            raise AssertionError("affine dual direction changes the polynomial")
    return AffineDual(base, directions)


def recovery_lp(
    rows: Sequence[MomentRow],
    affine: AffineDual,
    alpha_objective: int,
) -> tuple[Fraction, list[Fraction], dict[str, Any]]:
    """Optimize alpha over all support duals inducing one polynomial."""

    if alpha_objective not in (-1, 1):
        raise ValueError("alpha objective must be -1 or +1")
    parameter_count = len(affine.directions)
    variable_count = 2 * parameter_count + 1
    alpha_index = variable_count - 1
    matrix: list[list[Fraction]] = []
    bounds: list[Fraction] = []

    for column in range(64):
        fixed = sum(
            (affine.base[row_index] * row.columns[column] for row_index, row in enumerate(rows)),
            Fraction(0),
        )
        parameter_coefficients = [
            sum(
                (direction[row_index] * row.columns[column] for row_index, row in enumerate(rows)),
                Fraction(0),
            )
            for direction in affine.directions
        ]
        atom = ATOMS[column % 16]
        black = int(atom == BLACK_ATOM)
        white = int(atom == WHITE_ATOM)
        inequality = [Fraction(0) for _ in range(variable_count)]
        for index, coefficient in enumerate(parameter_coefficients):
            # fixed + c*(positive-negative) >= white + (black-white)*alpha
            inequality[index] = -coefficient
            inequality[parameter_count + index] = coefficient
        inequality[alpha_index] = black - white
        matrix.append(inequality)
        bounds.append(fixed - white)

    alpha_upper = [Fraction(0) for _ in range(variable_count)]
    alpha_upper[alpha_index] = 1
    matrix.append(alpha_upper)
    bounds.append(Fraction(1))

    objective = [Fraction(0) for _ in range(variable_count)]
    objective[alpha_index] = alpha_objective
    status, value, solution = ExactSimplex(matrix, bounds, objective).solve()
    if status != ExactSimplex.OPTIMAL or value is None or solution is None:
        raise AssertionError(f"support-dual recovery LP is {status}")
    alpha = solution[alpha_index]
    if not 0 <= alpha <= 1:
        raise AssertionError("recovery LP returned alpha outside [0,1]")
    parameters = [
        solution[index] - solution[parameter_count + index]
        for index in range(parameter_count)
    ]
    dual = affine.evaluate(parameters)
    objective_alpha = value if alpha_objective == 1 else -value
    if objective_alpha != alpha:
        raise AssertionError("recovery LP objective and solution disagree")
    stats = {
        "constraints": len(matrix),
        "nonnegative_variables": variable_count,
        "free_multiplier_parameters": parameter_count,
    }
    return alpha, dual, stats


def recover_legacy_witness(
    rows: Sequence[MomentRow], polynomial: dict[tuple[int, ...], Fraction]
) -> tuple[Fraction, list[Fraction], tuple[Fraction, Fraction], dict[str, Any]]:
    affine = dual_parameterization(rows, polynomial)
    minimum_alpha, _, stats_min = recovery_lp(rows, affine, -1)
    maximum_alpha, dual, stats_max = recovery_lp(rows, affine, 1)
    if minimum_alpha > maximum_alpha:
        raise AssertionError("recovered alpha interval is reversed")
    witness_check = verify_witness(rows, polynomial, maximum_alpha, dual)
    if not witness_check["passed"]:
        raise AssertionError("newly recovered legacy witness does not verify")
    return maximum_alpha, dual, (minimum_alpha, maximum_alpha), {
        "minimum_alpha_lp": stats_min,
        "maximum_alpha_lp": stats_max,
        "selection_rule": "maximum feasible alpha; deterministic exact simplex",
    }


def parse_new_cut_record(
    value: Any, index: int, row_count: int
) -> tuple[dict[tuple[int, ...], Fraction], Fraction, list[Fraction]]:
    context = f"new_dual_cuts[{index}]"
    if not isinstance(value, dict) or set(value) != {"poly", "alpha", "dual"}:
        raise InputError(f"{context}: expected exactly poly, alpha, dual")
    polynomial = parse_polynomial(value["poly"], f"{context}.poly")
    alpha = parse_rational(value["alpha"], f"{context}.alpha")
    dual = parse_sparse_dual(value["dual"], row_count, f"{context}.dual")
    return polynomial, alpha, dual


def parse_legacy_polynomials(value: Any) -> list[dict[tuple[int, ...], Fraction]]:
    if not isinstance(value, list):
        raise InputError("benders_cuts root must be a list")
    return [
        parse_polynomial(record, f"benders_cuts[{index}]")
        for index, record in enumerate(value)
    ]


def load_recovered_records(
    path: Path,
    benders_sha256: str,
    moment_sha256: str,
    rows: Sequence[MomentRow],
) -> dict[int, dict[str, Any]]:
    if not path.exists():
        return {}
    root = load_json_strict(path)
    if (
        not isinstance(root, dict)
        or root.get("schema") != RECOVERY_SCHEMA
        or root.get("checker_version") != CHECKER_VERSION
        or root.get("benders_cuts_sha256") != benders_sha256
        or root.get("moment_model_sha256") != moment_sha256
        or not isinstance(root.get("cuts"), list)
    ):
        return {}
    result: dict[int, dict[str, Any]] = {}
    for offset, record in enumerate(root["cuts"]):
        context = f"recovered.cuts[{offset}]"
        if not isinstance(record, dict):
            raise InputError(f"{context}: record is not an object")
        index = record.get("source_index")
        if not is_plain_int(index) or index in result:
            raise InputError(f"{context}: invalid or duplicate source_index")
        # Parse eagerly so a malformed cached artifact is never silently reused.
        parse_polynomial(record.get("poly"), f"{context}.poly")
        parse_rational(record.get("alpha"), f"{context}.alpha")
        parse_sparse_dual(record.get("dual"), len(rows), f"{context}.dual")
        interval = record.get("alpha_feasible_interval")
        if not isinstance(interval, list) or len(interval) != 2:
            raise InputError(f"{context}: malformed alpha interval")
        parse_rational(interval[0], f"{context}.alpha_feasible_interval[0]")
        parse_rational(interval[1], f"{context}.alpha_feasible_interval[1]")
        result[index] = record
    return result


def recovered_root(
    benders_sha256: str,
    moment_sha256: str,
    records_by_index: dict[int, dict[str, Any]],
    expected_count: int,
) -> dict[str, Any]:
    return {
        "schema": RECOVERY_SCHEMA,
        "checker_version": CHECKER_VERSION,
        "benders_cuts_sha256": benders_sha256,
        "moment_model_sha256": moment_sha256,
        "complete": len(records_by_index) == expected_count,
        "expected_cut_count": expected_count,
        "cuts": [records_by_index[index] for index in sorted(records_by_index)],
    }


def make_recovered_record(
    index: int,
    polynomial: dict[tuple[int, ...], Fraction],
    alpha: Fraction,
    dual: Sequence[Fraction],
    interval: tuple[Fraction, Fraction],
    recovery_stats: dict[str, Any],
) -> dict[str, Any]:
    poly_json = polynomial_json(polynomial)
    return {
        "source_index": index,
        "source_polynomial_sha256": canonical_sha256(poly_json),
        "poly": poly_json,
        "alpha": rational_json(alpha),
        "dual": sparse_dual_json(dual),
        "alpha_feasible_interval": [rational_json(interval[0]), rational_json(interval[1])],
        "recovery": recovery_stats,
    }


def parse_recovered_record(
    record: dict[str, Any],
    index: int,
    polynomial: dict[tuple[int, ...], Fraction],
    row_count: int,
) -> tuple[Fraction, list[Fraction], tuple[Fraction, Fraction]]:
    context = f"recovered.cuts[source_index={index}]"
    if record.get("source_index") != index:
        raise InputError(f"{context}: source index mismatch")
    stored_polynomial = parse_polynomial(record.get("poly"), f"{context}.poly")
    if stored_polynomial != polynomial:
        raise InputError(f"{context}: source polynomial mismatch")
    expected_poly_sha = canonical_sha256(polynomial_json(polynomial))
    if record.get("source_polynomial_sha256") != expected_poly_sha:
        raise InputError(f"{context}: polynomial SHA-256 mismatch")
    alpha = parse_rational(record.get("alpha"), f"{context}.alpha")
    dual = parse_sparse_dual(record.get("dual"), row_count, f"{context}.dual")
    interval_value = record.get("alpha_feasible_interval")
    if not isinstance(interval_value, list) or len(interval_value) != 2:
        raise InputError(f"{context}: malformed alpha interval")
    interval = (
        parse_rational(interval_value[0], f"{context}.interval[0]"),
        parse_rational(interval_value[1], f"{context}.interval[1]"),
    )
    if not interval[0] <= alpha <= interval[1]:
        raise InputError(f"{context}: selected alpha is outside stored interval")
    return alpha, dual, interval


def per_cut_record(
    library: str,
    index: int,
    raw_record: Any,
    polynomial: dict[tuple[int, ...], Fraction],
    alpha: Fraction,
    dual: Sequence[Fraction],
    check: dict[str, Any],
    alpha_interval: tuple[Fraction, Fraction] | None = None,
    recovery_mode: str | None = None,
) -> dict[str, Any]:
    record: dict[str, Any] = {
        "library": library,
        "source_index": index,
        "source_record_sha256": canonical_sha256(raw_record),
        "polynomial_sha256": canonical_sha256(polynomial_json(polynomial)),
        "alpha": rational_json(alpha),
        **check,
    }
    if alpha_interval is not None:
        record["alpha_feasible_interval"] = [
            rational_json(alpha_interval[0]),
            rational_json(alpha_interval[1]),
        ]
    if recovery_mode is not None:
        record["recovery_mode"] = recovery_mode
    return record


def summarize_records(records: Sequence[dict[str, Any]]) -> dict[str, Any]:
    alpha_histogram: dict[str, int] = {}
    library_counts: dict[str, int] = {}
    passed = 0
    failed_ids: list[str] = []
    max_denominator = 1
    for record in records:
        alpha = parse_rational(record["alpha"], "summary alpha")
        alpha_key = rational_text(alpha)
        alpha_histogram[alpha_key] = alpha_histogram.get(alpha_key, 0) + 1
        library = record["library"]
        library_counts[library] = library_counts.get(library, 0) + 1
        max_denominator = max(max_denominator, int(record["maximum_dual_denominator"]))
        if record["passed"]:
            passed += 1
        else:
            failed_ids.append(f"{library}:{record['source_index']}")
    return {
        "cut_count": len(records),
        "passed": passed,
        "failed": len(records) - passed,
        "failed_cut_ids": failed_ids,
        "library_counts": dict(sorted(library_counts.items())),
        "alpha_histogram": dict(
            sorted(alpha_histogram.items(), key=lambda item: Fraction(item[0]))
        ),
        "maximum_dual_denominator": max_denominator,
    }


def load_resume_records(
    path: Path,
    input_hashes: dict[str, str],
    moment_sha256: str,
) -> dict[tuple[str, int], dict[str, Any]]:
    if not path.exists():
        return {}
    root = load_json_strict(path)
    if (
        not isinstance(root, dict)
        or root.get("schema") != SCHEMA
        or root.get("checker_version") != CHECKER_VERSION
        or root.get("input_sha256") != input_hashes
        or root.get("moment_model", {}).get("sha256") != moment_sha256
        or not isinstance(root.get("cuts"), list)
    ):
        return {}
    result: dict[tuple[str, int], dict[str, Any]] = {}
    for record in root["cuts"]:
        if not isinstance(record, dict):
            continue
        library = record.get("library")
        index = record.get("source_index")
        if library in ("new_dual_cuts", "benders_cuts") and is_plain_int(index):
            result[(library, index)] = record
    return result


def verification_root(
    *,
    input_paths: dict[str, str],
    input_hashes: dict[str, str],
    moment_sha256: str,
    geometry_audit: dict[str, Any],
    simplex_audit: dict[str, Any],
    moment_path: Path,
    recovered_path: Path,
    recovered_sha256: str | None,
    records: Sequence[dict[str, Any]],
    expected_count: int,
) -> dict[str, Any]:
    summary = summarize_records(records)
    complete = len(records) == expected_count
    overall_passed = complete and summary["failed"] == 0
    return {
        "schema": SCHEMA,
        "checker_version": CHECKER_VERSION,
        "implementation": {
            "language": "Python",
            "dependencies": ["standard-library"],
            "arithmetic": "fractions.Fraction exact rational",
            "recovery_algorithm": "deterministic exact two-phase simplex",
            "reference_verifier_imported": False,
        },
        "input_paths": input_paths,
        "input_sha256": input_hashes,
        "expected_cut_count": expected_count,
        "complete": complete,
        "overall_passed": overall_passed,
        "moment_model": {
            "rows": 42,
            "columns": 64,
            "sha256": moment_sha256,
            "path": portable_path(moment_path),
            "geometry_audit": geometry_audit,
        },
        "exact_simplex_self_test": simplex_audit,
        "recovered_benders_artifact": {
            "path": portable_path(recovered_path),
            "sha256": recovered_sha256,
        },
        "summary": summary,
        "cuts": list(records),
    }


def run(args: argparse.Namespace) -> dict[str, Any]:
    new_path = args.new_cuts.resolve()
    benders_path = args.benders_cuts.resolve()
    recovered_path = args.recovered.resolve()
    moment_path = args.moment_output.resolve()
    output_path = args.output.resolve()

    rows = derive_moment_rows()
    model = moment_model_json(rows)
    moment_sha256 = canonical_sha256(model)
    atomic_write_json(moment_path, model)
    if sha256_file(moment_path) != moment_sha256:
        raise AssertionError("written moment-model SHA-256 disagrees with derived model")
    geometry_audit = audit_torus_fibers(args.geometry_max_q)
    simplex_audit = exact_simplex_self_test()

    new_raw = load_json_strict(new_path)
    benders_raw = load_json_strict(benders_path)
    if not isinstance(new_raw, list):
        raise InputError("new_dual_cuts root must be a list")
    legacy_polynomials = parse_legacy_polynomials(benders_raw)
    if len(new_raw) != 684:
        raise InputError(f"expected 684 delivered cuts, got {len(new_raw)}")
    if len(legacy_polynomials) != 76:
        raise InputError(f"expected 76 legacy cuts, got {len(legacy_polynomials)}")
    expected_count = len(new_raw) + len(legacy_polynomials)

    input_paths = {
        "new_dual_cuts": portable_path(new_path),
        "benders_cuts": portable_path(benders_path),
    }
    input_hashes = {
        "new_dual_cuts": sha256_file(new_path),
        "benders_cuts": sha256_file(benders_path),
    }
    resume_records = (
        load_resume_records(output_path, input_hashes, moment_sha256) if args.resume else {}
    )

    recovered_by_index = (
        {}
        if args.rebuild_recovered
        else load_recovered_records(
            recovered_path,
            input_hashes["benders_cuts"],
            moment_sha256,
            rows,
        )
    )
    records: list[dict[str, Any]] = []

    def checkpoint() -> None:
        recovered_sha = sha256_file(recovered_path) if recovered_path.exists() else None
        root = verification_root(
            input_paths=input_paths,
            input_hashes=input_hashes,
            moment_sha256=moment_sha256,
            geometry_audit=geometry_audit,
            simplex_audit=simplex_audit,
            moment_path=moment_path,
            recovered_path=recovered_path,
            recovered_sha256=recovered_sha,
            records=records,
            expected_count=expected_count,
        )
        atomic_write_json(output_path, root)

    for index, raw_record in enumerate(new_raw):
        polynomial, alpha, dual = parse_new_cut_record(raw_record, index, len(rows))
        identity = canonical_sha256(raw_record)
        cached = resume_records.get(("new_dual_cuts", index))
        check = verify_witness(rows, polynomial, alpha, dual)
        expected_record = per_cut_record(
            "new_dual_cuts",
            index,
            raw_record,
            polynomial,
            alpha,
            dual,
            check,
        )
        # Resume data is never trusted merely because it says PASS: reuse it
        # only when it is byte-for-byte equivalent as a JSON value to the
        # result just recomputed from the current source witness.
        if (
            cached is not None
            and cached.get("source_record_sha256") == identity
            and cached == expected_record
        ):
            records.append(cached)
        else:
            records.append(expected_record)
        if args.checkpoint_every and len(records) % args.checkpoint_every == 0:
            checkpoint()

    for index, (raw_polynomial, polynomial) in enumerate(
        zip(benders_raw, legacy_polynomials)
    ):
        recovery_mode: str
        if index in recovered_by_index:
            alpha, dual, interval = parse_recovered_record(
                recovered_by_index[index], index, polynomial, len(rows)
            )
            recovery_mode = "exact_simplex_frozen_witness"
        else:
            alpha, dual, interval, recovery_stats = recover_legacy_witness(rows, polynomial)
            recovered_by_index[index] = make_recovered_record(
                index,
                polynomial,
                alpha,
                dual,
                interval,
                recovery_stats,
            )
            atomic_write_json(
                recovered_path,
                recovered_root(
                    input_hashes["benders_cuts"],
                    moment_sha256,
                    recovered_by_index,
                    len(legacy_polynomials),
                ),
            )
            recovery_mode = "exact_simplex_frozen_witness"

        check = verify_witness(rows, polynomial, alpha, dual)
        records.append(
            per_cut_record(
                "benders_cuts",
                index,
                raw_polynomial,
                polynomial,
                alpha,
                dual,
                check,
                interval,
                recovery_mode,
            )
        )
        if args.checkpoint_every and len(records) % args.checkpoint_every == 0:
            checkpoint()

    # Rewrite the recovery file in canonical complete order even when every
    # witness came from a prior resumable run.
    atomic_write_json(
        recovered_path,
        recovered_root(
            input_hashes["benders_cuts"],
            moment_sha256,
            recovered_by_index,
            len(legacy_polynomials),
        ),
    )
    recovered_sha256 = sha256_file(recovered_path)
    root = verification_root(
        input_paths=input_paths,
        input_hashes=input_hashes,
        moment_sha256=moment_sha256,
        geometry_audit=geometry_audit,
        simplex_audit=simplex_audit,
        moment_path=moment_path,
        recovered_path=recovered_path,
        recovered_sha256=recovered_sha256,
        records=records,
        expected_count=expected_count,
    )
    atomic_write_json(output_path, root)
    return root


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--new-cuts", type=Path, default=DEFAULT_NEW_CUTS)
    result.add_argument("--benders-cuts", type=Path, default=DEFAULT_BENDERS_CUTS)
    result.add_argument("--recovered", type=Path, default=DEFAULT_RECOVERED)
    result.add_argument("--moment-output", type=Path, default=DEFAULT_MOMENT_MODEL)
    result.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    result.add_argument(
        "--rebuild-recovered",
        action="store_true",
        help="ignore any frozen legacy witnesses and recover all 76 again",
    )
    result.add_argument(
        "--resume",
        action="store_true",
        help="reuse matching delivered-cut verdicts from a partial output file",
    )
    result.add_argument(
        "--checkpoint-every",
        type=int,
        default=25,
        help="atomically checkpoint the verification output every N cuts (0 disables)",
    )
    result.add_argument(
        "--geometry-max-q",
        type=int,
        default=12,
        help="audit all torus incidence fibers for q=1..N",
    )
    return result


def main(argv: Sequence[str] | None = None) -> int:
    args = parser().parse_args(argv)
    if args.checkpoint_every < 0:
        raise SystemExit("--checkpoint-every must be nonnegative")
    try:
        root = run(args)
    except (InputError, AssertionError, ArithmeticError, OSError, ValueError) as exc:
        print(f"E1_VERIFIER_ERROR: {exc}", file=sys.stderr)
        return 2
    summary = root["summary"]
    print(
        "E1_DUAL_CUTS_"
        + ("OK" if root["overall_passed"] else "FAIL")
        + f" {summary['passed']}/{summary['cut_count']}"
    )
    print("new_dual_cuts sha256", root["input_sha256"]["new_dual_cuts"])
    print("benders_cuts sha256", root["input_sha256"]["benders_cuts"])
    print("alpha histogram", json.dumps(summary["alpha_histogram"], sort_keys=True))
    print("verification", str(args.output.resolve()))
    print("recovered duals", str(args.recovered.resolve()))
    return 0 if root["overall_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
