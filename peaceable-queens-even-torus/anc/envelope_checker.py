#!/usr/bin/env python3
"""Independent exact branch-and-bound checker for the even cut envelope.

This implementation deliberately does not import either reference verifier.
It proves that every canonical integer profile in a fixed order is covered by
at least one support-dual cut.  The search is over integer boxes, not over an
explicit profile array:

* linear canonical/budget inequalities are propagated on every box;
* a cut first receives a separable McCormick/interval upper bound;
* promising cuts then receive their exact multi-affine corner maximum;
* an entire box is discharged when either upper bound is at most H + 1/2;
* otherwise the box is bisected and both children are checked.

The common denominator is derived as the LCM of all delivered rational
coefficients.  Count-scale evaluation is important: a constant monomial means
q^2 and a linear monomial means q*x_i.  Consequently every comparison below
is integer-only.
"""

from __future__ import annotations

import argparse
import hashlib
import heapq
import itertools
import json
import math
import os
import sys
import time
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
PEACEABLE_QUEENS = HERE.parents[1]
RESULT4 = PEACEABLE_QUEENS / "handoff-mathematician" / "result4"
DEFAULT_RECORDS = HERE / "records"
SCHEMA = "peaceable-queens-e2e3-envelope-box-proof-v2"

# Each row is sum(a_i*x_i) <= rhs.  The coordinate order is
# r0,r1,c0,c1,d0,d1,a0,a1.
DOMAIN_ROWS: tuple[tuple[tuple[int, ...], int | None], ...] = (
    ((1, -1, 0, 0, 0, 0, 0, 0), 0),
    ((0, 0, 1, -1, 0, 0, 0, 0), 0),
    ((1, 1, -1, -1, 0, 0, 0, 0), 0),
    ((0, 0, 0, 0, 1, 1, -1, -1), 0),
    ((1, 1, 1, 1, 1, 1, 1, 1), None),  # rhs = 4*q
)


@dataclass(frozen=True)
class Cut:
    """A polynomial multiplied by the library-wide computed denominator."""

    source: str
    source_index: int
    scale: int
    constant: int
    linear: tuple[int, ...]
    quadratic: tuple[tuple[int, int, int], ...]
    variables: tuple[int, ...]

    @property
    def label(self) -> str:
        return f"{self.source}:{self.source_index}"


@dataclass(frozen=True)
class Box:
    lo: tuple[int, ...]
    hi: tuple[int, ...]
    depth: int
    hint: int


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _poly_entries() -> tuple[list[dict[str, list[int]]], list[dict[str, list[int]]]]:
    with (RESULT4 / "benders_cuts.json").open(encoding="utf-8") as handle:
        old = json.load(handle)
    with (RESULT4 / "new_dual_cuts.json").open(encoding="utf-8") as handle:
        new = [entry["poly"] for entry in json.load(handle)]
    if len(old) != 76 or len(new) != 684:
        raise ValueError(f"unexpected cut counts: {len(old)} and {len(new)}")
    return old, new


def _coefficient_lcm(entries: Iterable[dict[str, list[int]]]) -> int:
    denominator = 1
    for raw in entries:
        for pair in raw.values():
            if not (
                isinstance(pair, list)
                and len(pair) == 2
                and all(isinstance(value, int) for value in pair)
                and pair[1] != 0
            ):
                raise ValueError(f"malformed coefficient {pair!r}")
            denominator = math.lcm(
                denominator, Fraction(pair[0], pair[1]).denominator
            )
    return denominator


def _convert_cut(
    raw: dict[str, list[int]],
    source: str,
    index: int,
    common_denominator: int,
) -> Cut:
    constant = 0
    linear = [0] * 8
    quadratic: dict[tuple[int, int], int] = {}
    for key, pair in raw.items():
        if not (
            isinstance(pair, list)
            and len(pair) == 2
            and all(isinstance(value, int) for value in pair)
            and pair[1] != 0
        ):
            raise ValueError(f"{source}:{index}: malformed coefficient {key!r}")
        coefficient = Fraction(pair[0], pair[1])
        scaled = coefficient * common_denominator
        if scaled.denominator != 1:
            raise ValueError(
                f"{source}:{index}: denominator does not divide "
                f"computed LCM {common_denominator}"
            )
        value = scaled.numerator
        monomial = tuple(sorted(int(part) for part in key.split(","))) if key else ()
        if any(variable < 0 or variable >= 8 for variable in monomial):
            raise ValueError(f"{source}:{index}: variable outside 0..7")
        if len(monomial) == 0:
            constant += value
        elif len(monomial) == 1:
            linear[monomial[0]] += value
        elif len(monomial) == 2 and monomial[0] != monomial[1]:
            quadratic[monomial] = quadratic.get(monomial, 0) + value
        else:
            raise ValueError(f"{source}:{index}: polynomial is not multi-affine")
    terms = tuple(
        (left, right, value)
        for (left, right), value in sorted(quadratic.items())
        if value
    )
    variables = sorted(
        {
            variable
            for variable, value in enumerate(linear)
            if value
        }
        | {left for left, _, _ in terms}
        | {right for _, right, _ in terms}
    )
    return Cut(
        source=source,
        source_index=index,
        scale=common_denominator,
        constant=constant,
        linear=tuple(linear),
        quadratic=terms,
        variables=tuple(variables),
    )


def load_cuts() -> tuple[list[Cut], dict[str, str], int]:
    old, new = _poly_entries()
    common_denominator = _coefficient_lcm([*old, *new])
    arithmetic_scale = math.lcm(common_denominator, 2)
    cuts = [
        _convert_cut(raw, "benders76", index, arithmetic_scale)
        for index, raw in enumerate(old)
    ]
    cuts.extend(
        _convert_cut(raw, "new684", index, arithmetic_scale)
        for index, raw in enumerate(new)
    )
    if len(cuts) != 760:
        raise AssertionError(len(cuts))
    digests = {
        "benders_cuts.json": sha256(RESULT4 / "benders_cuts.json"),
        "new_dual_cuts.json": sha256(RESULT4 / "new_dual_cuts.json"),
    }
    return cuts, digests, common_denominator


def evaluate(cut: Cut, q: int, point: Sequence[int]) -> int:
    """Return cut.scale * poly(point) in count scale."""

    value = cut.constant * q * q
    value += sum(
        coefficient * q * point[index]
        for index, coefficient in enumerate(cut.linear)
        if coefficient
    )
    value += sum(
        coefficient * point[left] * point[right]
        for left, right, coefficient in cut.quadratic
    )
    return value


def interval_upper(cut: Cut, q: int, lo: Sequence[int], hi: Sequence[int]) -> int:
    """Separable exact-integer McCormick upper bound for one cut."""

    value = cut.constant * q * q
    for index, coefficient in enumerate(cut.linear):
        if coefficient:
            endpoint = hi[index] if coefficient > 0 else lo[index]
            value += coefficient * q * endpoint
    for left, right, coefficient in cut.quadratic:
        if coefficient > 0:
            product = hi[left] * hi[right]
        else:
            # All counts are nonnegative, so this is the minimum product.
            product = lo[left] * lo[right]
        value += coefficient * product
    return value


def exact_corner_leq(
    cut: Cut,
    q: int,
    lo: Sequence[int],
    hi: Sequence[int],
    threshold: int,
) -> tuple[bool, int]:
    """Test the exact multi-affine maximum, stopping at a bad corner.

    A multi-affine polynomial on a real box attains its maximum at a corner.
    Integer endpoints make this an exact integer calculation.  The returned
    count is the number of corners actually inspected.
    """

    active = [index for index in cut.variables if lo[index] != hi[index]]
    base = evaluate(cut, q, lo)
    if base > threshold:
        return False, 1
    if not active:
        return True, 1

    # Substitute x_i = lo_i + delta_i*z_i.  The resulting polynomial in
    # binary z is again quadratic.  Gray-code traversal changes one z at a
    # time, avoiding a full polynomial evaluation at each of up to 256
    # corners.
    position = {variable: index for index, variable in enumerate(active)}
    first_order = [0] * len(active)
    interactions = [[0] * len(active) for _ in active]
    for local, variable in enumerate(active):
        derivative = cut.linear[variable] * q
        for left, right, coefficient in cut.quadratic:
            if left == variable:
                derivative += coefficient * lo[right]
            elif right == variable:
                derivative += coefficient * lo[left]
        first_order[local] = (hi[variable] - lo[variable]) * derivative
    for left, right, coefficient in cut.quadratic:
        if left not in position or right not in position:
            continue
        first = position[left]
        second = position[right]
        interaction = (
            coefficient
            * (hi[left] - lo[left])
            * (hi[right] - lo[right])
        )
        interactions[first][second] = interaction
        interactions[second][first] = interaction

    value = base
    selected = [False] * len(active)
    previous_gray = 0
    inspected = 1
    for ordinal in range(1, 1 << len(active)):
        gray = ordinal ^ (ordinal >> 1)
        changed = gray ^ previous_gray
        local = changed.bit_length() - 1
        adjustment = first_order[local] + sum(
            interactions[local][other]
            for other in range(len(active))
            if selected[other] and other != local
        )
        if selected[local]:
            value -= adjustment
            selected[local] = False
        else:
            value += adjustment
            selected[local] = True
        inspected += 1
        if value > threshold:
            return False, inspected
        previous_gray = gray
    return True, inspected


def _ceil_div(numerator: int, denominator: int) -> int:
    return -((-numerator) // denominator)


def propagate_box(q: int, lo_input: Sequence[int], hi_input: Sequence[int]) -> tuple[
    tuple[int, ...], tuple[int, ...]
] | None:
    """Integer bound propagation for all five domain inequalities."""

    lo = list(lo_input)
    hi = list(hi_input)
    rows = [
        (coefficients, 4 * q if rhs is None else rhs)
        for coefficients, rhs in DOMAIN_ROWS
    ]
    changed = True
    while changed:
        changed = False
        for coefficients, rhs in rows:
            minimum = sum(
                coefficient * (lo[index] if coefficient > 0 else hi[index])
                for index, coefficient in enumerate(coefficients)
                if coefficient
            )
            if minimum > rhs:
                return None
            for index, coefficient in enumerate(coefficients):
                if not coefficient:
                    continue
                used = lo[index] if coefficient > 0 else hi[index]
                other_minimum = minimum - coefficient * used
                if coefficient > 0:
                    candidate = (rhs - other_minimum) // coefficient
                    if candidate < hi[index]:
                        hi[index] = candidate
                        changed = True
                else:
                    candidate = _ceil_div(rhs - other_minimum, coefficient)
                    if candidate > lo[index]:
                        lo[index] = candidate
                        changed = True
                if lo[index] > hi[index]:
                    return None
    return tuple(lo), tuple(hi)


def in_domain(q: int, point: Sequence[int]) -> bool:
    if len(point) != 8 or any(value < 0 or value > q for value in point):
        return False
    return (
        point[0] <= point[1]
        and point[2] <= point[3]
        and point[0] + point[1] <= point[2] + point[3]
        and point[4] + point[5] <= point[6] + point[7]
        and sum(point) <= 4 * q
    )


def brute_force_h(q: int) -> tuple[int, tuple[int, int, int, int]]:
    """Independent literal four-loop definition of H(2q)."""

    best = -1
    optimizer = (0, 0, 0, 0)
    for r0 in range(q + 1):
        for r1 in range(q + 1):
            for c0 in range(q + 1):
                for c1 in range(q + 1):
                    black = r0 * c1 + r1 * c0
                    white = (
                        (q - r0) * (q - c0)
                        + (q - r1) * (q - c1)
                    )
                    score = min(black, white)
                    if score > best:
                        best = score
                        optimizer = (r0, r1, c0, c1)
    return best, optimizer


def crossing_h(q: int) -> tuple[int, tuple[int, int, int, int]]:
    """O(q^3) exact H search by optimizing c1 at its affine crossing.

    For fixed (r0,r1,c0), the black count is nondecreasing in c1 and
    the white count is nonincreasing.  Their minimum is therefore maximized
    at an endpoint or at one of the two integers around the crossing.
    """

    best = -1
    optimizer = (0, 0, 0, 0)
    for r0 in range(q + 1):
        for r1 in range(q + 1):
            denominator = q + r0 - r1
            for c0 in range(q + 1):
                candidates = {0, q}
                if denominator:
                    numerator = (
                        (q - r0) * (q - c0)
                        + q * (q - r1)
                        - r1 * c0
                    )
                    floor_crossing = numerator // denominator
                    candidates.update((floor_crossing, floor_crossing + 1))
                for c1 in candidates:
                    if c1 < 0 or c1 > q:
                        continue
                    black = r0 * c1 + r1 * c0
                    white = (
                        (q - r0) * (q - c0)
                        + (q - r1) * (q - c1)
                    )
                    score = min(black, white)
                    if score > best:
                        best = score
                        optimizer = (r0, r1, c0, c1)
    return best, optimizer


def box_h(
    q: int,
) -> tuple[int, tuple[int, int, int, int], dict[str, int]]:
    """Exact best-first box optimization of H in integer arithmetic.

    On a box, the black expression is at most its value at the all-high
    corner, while the white expression is at most its value at the all-low
    corner.  The minimum of those two maxima is therefore a valid upper bound
    on every point in the box.  Best-first bisection stops only once the
    largest remaining upper bound is no better than the incumbent.
    """

    if q < 1:
        raise ValueError("q must be positive")

    def score(point: Sequence[int]) -> int:
        r0, r1, c0, c1 = point
        return min(
            r0 * c1 + r1 * c0,
            (q - r0) * (q - c0) + (q - r1) * (q - c1),
        )

    def upper(lo: Sequence[int], hi: Sequence[int]) -> int:
        black_upper = hi[0] * hi[3] + hi[1] * hi[2]
        white_upper = (
            (q - lo[0]) * (q - lo[2])
            + (q - lo[1]) * (q - lo[3])
        )
        return min(black_upper, white_upper)

    best = -1
    optimizer = (0, 0, 0, 0)
    # Exact-integer heuristic seeds near (sqrt(3)-1)q.  It affects runtime
    # only; the queue exhaustion below is the proof of optimality.
    plaid = math.isqrt(3 * q * q) - q
    for r1 in range(max(0, plaid - 2), min(q, plaid + 2) + 1):
        for c0 in range(max(0, plaid - 2), min(q, plaid + 2) + 1):
            for r0 in range(min(2, q) + 1):
                for c1 in range(min(2, q) + 1):
                    point = (r0, r1, c0, c1)
                    value = score(point)
                    if value > best:
                        best = value
                        optimizer = point

    initial_lo = (0, 0, 0, 0)
    initial_hi = (q, q, q, q)
    queue: list[
        tuple[int, tuple[int, ...], tuple[int, ...]]
    ] = [(-upper(initial_lo, initial_hi), initial_lo, initial_hi)]
    nodes = 0
    pruned_children = 0
    max_queue = 1
    while queue:
        neg_upper, lo, hi = heapq.heappop(queue)
        if -neg_upper <= best:
            break
        nodes += 1
        midpoint = tuple(
            (left + right) // 2 for left, right in zip(lo, hi)
        )
        value = score(midpoint)
        if value > best:
            best = value
            optimizer = midpoint
        if -neg_upper <= best:
            continue
        split_index = max(
            range(4),
            key=lambda index: (hi[index] - lo[index], -index),
        )
        if lo[split_index] == hi[split_index]:
            raise AssertionError("unpruned H point box")
        split = (lo[split_index] + hi[split_index]) // 2
        for upper_child in (False, True):
            child_lo = list(lo)
            child_hi = list(hi)
            if upper_child:
                child_lo[split_index] = split + 1
            else:
                child_hi[split_index] = split
            child_lo_tuple = tuple(child_lo)
            child_hi_tuple = tuple(child_hi)
            child_upper = upper(child_lo_tuple, child_hi_tuple)
            if child_upper <= best:
                pruned_children += 1
                continue
            heapq.heappush(
                queue,
                (-child_upper, child_lo_tuple, child_hi_tuple),
            )
        max_queue = max(max_queue, len(queue))
    return best, optimizer, {
        "nodes": nodes,
        "pruned_children": pruned_children,
        "max_queue": max_queue,
        "unfinished_boxes_with_upper_above_H": 0,
    }


def recount_witness(
    q: int, optimizer: Sequence[int]
) -> dict[str, object]:
    """Build the prescribed plaid witness and recount all 4q^2 cells."""

    n = 2 * q
    r0, r1, c0, c1 = optimizer
    even = list(range(0, n, 2))
    odd = list(range(1, n, 2))
    row_lines = set(even[:r0] + odd[:r1])
    column_lines = set(even[:c0] + odd[:c1])
    diagonal_lines = set(odd)
    antidiagonal_lines = set(odd)
    row_selected = [index in row_lines for index in range(n)]
    column_selected = [index in column_lines for index in range(n)]
    black = 0
    white = 0
    overlap = 0
    for row in range(n):
        for column in range(n):
            # Because n is even, row-column and row+column have the same
            # parity, and both are odd exactly when row/column parity differs.
            # This is still a direct visit to every cell; it merely avoids two
            # modulo/set lookups for the prescribed full odd D/A classes.
            diagonal_and_antidiagonal_selected = bool((row ^ column) & 1)
            is_black = (
                row_selected[row]
                and column_selected[column]
                and diagonal_and_antidiagonal_selected
            )
            is_white = (
                not row_selected[row]
                and not column_selected[column]
                and not diagonal_and_antidiagonal_selected
            )
            black += int(is_black)
            white += int(is_white)
            overlap += int(is_black and is_white)
    return {
        "outer_profile": [
            r0,
            r1,
            c0,
            c1,
            0,
            q,
            0,
            q,
        ],
        "line_counts": {
            "rows": len(row_lines),
            "columns": len(column_lines),
            "diagonals": len(diagonal_lines),
            "antidiagonals": len(antidiagonal_lines),
            "total": (
                len(row_lines)
                + len(column_lines)
                + len(diagonal_lines)
                + len(antidiagonal_lines)
            ),
        },
        "armies": {
            "black": black,
            "white": white,
            "minimum": min(black, white),
            "overlap": overlap,
            "cells_recounted": n * n,
        },
    }


def _split_score(cut: Cut, q: int, lo: Sequence[int], hi: Sequence[int], index: int) -> int:
    if lo[index] == hi[index]:
        return -1
    derivative_low = cut.linear[index] * q
    derivative_high = derivative_low
    for left, right, coefficient in cut.quadratic:
        if left == index:
            other = right
        elif right == index:
            other = left
        else:
            continue
        first = coefficient * lo[other]
        second = coefficient * hi[other]
        derivative_low += min(first, second)
        derivative_high += max(first, second)
    sensitivity = max(abs(derivative_low), abs(derivative_high), 1)
    return (hi[index] - lo[index]) * sensitivity


def _choose_split(cut: Cut, q: int, lo: Sequence[int], hi: Sequence[int]) -> int:
    active = [index for index in range(8) if lo[index] != hi[index]]
    if not active:
        return -1
    return max(
        active,
        key=lambda index: (
            _split_score(cut, q, lo, hi, index),
            hi[index] - lo[index],
            -index,
        ),
    )


def certify_order(
    q: int,
    h_value: int,
    cuts: Sequence[Cut],
    *,
    active_cut_count: int = 76,
    corner_candidates: int = 6,
    timeout_seconds: float = 600.0,
    progress: bool = False,
) -> dict[str, object]:
    """Run the exact box proof for one q and return detailed statistics."""

    if q < 1:
        raise ValueError("q must be positive")
    if not (1 <= active_cut_count <= len(cuts)):
        raise ValueError("invalid active cut count")
    active_cuts = list(cuts[:active_cut_count])
    arithmetic_scale = active_cuts[0].scale
    if any(cut.scale != arithmetic_scale for cut in cuts):
        raise ValueError("cuts do not share one coefficient scale")
    if arithmetic_scale % 2:
        raise AssertionError("arithmetic coefficient scale is not even")
    threshold = arithmetic_scale * h_value + arithmetic_scale // 2
    initial = propagate_box(q, (0,) * 8, (q,) * 8)
    if initial is None:
        raise AssertionError("empty initial domain")
    stack = [Box(initial[0], initial[1], 0, 0)]
    started = time.monotonic()
    stats: dict[str, int] = {
        "nodes": 0,
        "propagation_infeasible": 0,
        "certified_boxes": 0,
        "interval_certified_boxes": 0,
        "corner_certified_boxes": 0,
        "point_boxes": 0,
        "fallback_full_library_points": 0,
        "fallback_cut_point_evaluations": 0,
        "survivor_count": 0,
        "cut_center_evaluations": 0,
        "cut_interval_evaluations": 0,
        "cut_corner_calls": 0,
        "corners_inspected": 0,
        "max_depth": 0,
        "max_stack": 1,
    }
    cut_wins: dict[str, int] = {}
    survivors: list[list[int]] = []
    timed_out = False

    while stack:
        stats["max_stack"] = max(stats["max_stack"], len(stack))
        box = stack.pop()
        stats["nodes"] += 1
        stats["max_depth"] = max(stats["max_depth"], box.depth)
        if stats["nodes"] % 1024 == 0:
            elapsed = time.monotonic() - started
            if elapsed > timeout_seconds:
                timed_out = True
                break
            if progress:
                print(
                    f"q={q} nodes={stats['nodes']} stack={len(stack)} "
                    f"certified={stats['certified_boxes']} elapsed={elapsed:.1f}s",
                    file=sys.stderr,
                    flush=True,
                )

        propagated = propagate_box(q, box.lo, box.hi)
        if propagated is None:
            stats["propagation_infeasible"] += 1
            continue
        lo, hi = propagated
        if lo == hi:
            stats["point_boxes"] += 1
            if not in_domain(q, lo):
                raise AssertionError(f"propagated point outside domain: {lo}")
            covering = None
            for cut_index, cut in enumerate(active_cuts):
                stats["cut_center_evaluations"] += 1
                if evaluate(cut, q, lo) <= threshold:
                    covering = cut_index
                    break
            if covering is None and active_cut_count < len(cuts):
                for cut_index in range(active_cut_count, len(cuts)):
                    stats["fallback_cut_point_evaluations"] += 1
                    if evaluate(cuts[cut_index], q, lo) <= threshold:
                        covering = cut_index
                        stats["fallback_full_library_points"] += 1
                        break
            if covering is None:
                stats["survivor_count"] += 1
                survivors.append(list(lo))
                # One witness is sufficient to establish library insufficiency.
                break
            label = cuts[covering].label
            cut_wins[label] = cut_wins.get(label, 0) + 1
            stats["certified_boxes"] += 1
            continue

        center = tuple((left + right) // 2 for left, right in zip(lo, hi))
        ranked: list[tuple[int, int, int]] = []
        ordered_indices = [box.hint] + [
            index for index in range(len(active_cuts)) if index != box.hint
        ]
        certified_by: tuple[int, str] | None = None
        for cut_index in ordered_indices:
            cut = active_cuts[cut_index]
            center_value = evaluate(cut, q, center)
            stats["cut_center_evaluations"] += 1
            if center_value > threshold:
                continue
            upper = interval_upper(cut, q, lo, hi)
            stats["cut_interval_evaluations"] += 1
            if upper <= threshold:
                certified_by = (cut_index, "interval")
                break
            heapq.heappush(ranked, (upper, center_value, cut_index))

        if certified_by is None:
            for _ in range(min(corner_candidates, len(ranked))):
                _, _, cut_index = heapq.heappop(ranked)
                stats["cut_corner_calls"] += 1
                covered, inspected = exact_corner_leq(
                    active_cuts[cut_index], q, lo, hi, threshold
                )
                stats["corners_inspected"] += inspected
                if covered:
                    certified_by = (cut_index, "corner")
                    break

        if certified_by is not None:
            cut_index, method = certified_by
            stats["certified_boxes"] += 1
            stats[f"{method}_certified_boxes"] += 1
            label = active_cuts[cut_index].label
            cut_wins[label] = cut_wins.get(label, 0) + 1
            continue

        if ranked:
            _, _, hint = heapq.heappop(ranked)
        else:
            # No cut even covers the real-valued center.  It need not be an
            # integer-domain survivor, so continue branching exactly.
            hint = min(
                range(len(active_cuts)),
                key=lambda index: evaluate(active_cuts[index], q, center),
            )
            stats["cut_center_evaluations"] += len(active_cuts)
        split_index = _choose_split(active_cuts[hint], q, lo, hi)
        if split_index < 0:
            raise AssertionError("non-point box has no split dimension")
        midpoint = (lo[split_index] + hi[split_index]) // 2
        low_hi = list(hi)
        low_hi[split_index] = midpoint
        high_lo = list(lo)
        high_lo[split_index] = midpoint + 1
        # Depth-first, with the upper child inspected first.
        stack.append(
            Box(tuple(lo), tuple(low_hi), box.depth + 1, hint)
        )
        stack.append(
            Box(tuple(high_lo), tuple(hi), box.depth + 1, hint)
        )

    elapsed = time.monotonic() - started
    if timed_out:
        verdict = "timeout"
    elif survivors:
        verdict = "envelope_exceeds_threshold"
    else:
        verdict = "envelope_le_h_plus_half"
    return {
        "verdict": verdict,
        "threshold": {
            "expression": "H(2q) + 1/2",
            "integer_comparison_scale": arithmetic_scale,
            "integer_threshold": threshold,
        },
        "active_cut_count": active_cut_count,
        "corner_candidate_limit": corner_candidates,
        "runtime_seconds": elapsed,
        "stats": stats,
        "survivors": survivors,
        "cut_box_wins": dict(
            sorted(cut_wins.items(), key=lambda item: (-item[1], item[0]))
        ),
        "unfinished_stack_boxes": len(stack),
    }


def make_record(
    q: int,
    cuts: Sequence[Cut],
    digests: dict[str, str],
    common_denominator: int,
    *,
    active_cut_count: int,
    corner_candidates: int,
    timeout_seconds: float,
    progress: bool,
    brute_h_limit: int,
) -> dict[str, object]:
    h_started = time.monotonic()
    fast_h, optimizer, h_stats = box_h(q)
    h_method = "exact monotone-box branch-and-bound"
    brute_crosscheck: dict[str, object]
    if q <= brute_h_limit:
        brute_h, brute_optimizer = brute_force_h(q)
        if brute_h != fast_h:
            raise AssertionError(
                f"H implementations disagree at q={q}: {brute_h} != {fast_h}"
            )
        brute_crosscheck = {
            "performed": True,
            "value": brute_h,
            "optimizer": list(brute_optimizer),
            "match": True,
        }
    else:
        brute_crosscheck = {"performed": False, "limit": brute_h_limit}
    h_runtime = time.monotonic() - h_started
    witness = recount_witness(q, optimizer)
    if witness["armies"]["minimum"] < fast_h:  # type: ignore[index]
        raise AssertionError("recounted witness falls below H")

    proof = certify_order(
        q,
        fast_h,
        cuts,
        active_cut_count=active_cut_count,
        corner_candidates=corner_candidates,
        timeout_seconds=timeout_seconds,
        progress=progress,
    )
    return {
        "schema": SCHEMA,
        "q": q,
        "n": 2 * q,
        "H(2q)": fast_h,
        "h_optimizer": list(optimizer),
        "h_computation": {
            "method": h_method,
            "runtime_seconds": h_runtime,
            "search_stats": h_stats,
            "literal_bruteforce_crosscheck": brute_crosscheck,
        },
        "witness": witness,
        "envelope": proof,
        "cut_library": {
            "loaded_count": len(cuts),
            "common_denominator": common_denominator,
            "arithmetic_coefficient_scale": cuts[0].scale,
            "common_denominator_derivation": (
                "LCM of every reduced rational coefficient in both cut files"
            ),
            "file_sha256": digests,
        },
        "algorithm": {
            "name": "canonical-integer-box branch-and-bound",
            "bounds": [
                "integer linear-inequality propagation",
                "separable bilinear McCormick interval upper bound",
                "exact multi-affine corner maximum",
            ],
            "arithmetic": "integer only after coefficient scaling",
            "threads": 1,
        },
    }


def _atomic_json(path: Path, record: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    with temporary.open("w", encoding="utf-8") as handle:
        json.dump(record, handle, indent=2, sort_keys=True)
        handle.write("\n")
    temporary.replace(path)


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("q", nargs="+", type=int)
    parser.add_argument(
        "--records-dir",
        type=Path,
        default=DEFAULT_RECORDS,
        help="one resumable qNNNN.json record is written here",
    )
    parser.add_argument(
        "--active-cuts",
        type=int,
        default=76,
        help="certifying prefix of the verified 760-cut library",
    )
    parser.add_argument("--corner-candidates", type=int, default=6)
    parser.add_argument("--timeout", type=float, default=600.0)
    parser.add_argument(
        "--brute-h-limit",
        type=int,
        default=30,
        help="also run the literal four-loop H search through this q",
    )
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--progress", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    cuts, digests, common_denominator = load_cuts()
    exit_status = 0
    for q in args.q:
        if q < 1:
            raise ValueError("all q values must be positive")
        output = args.records_dir / f"q{q:04d}.json"
        if output.exists() and not args.force:
            with output.open(encoding="utf-8") as handle:
                existing = json.load(handle)
            if (
                existing.get("schema") == SCHEMA
                and existing.get("q") == q
                and existing.get("cut_library", {}).get("file_sha256") == digests
                and existing.get("cut_library", {}).get("common_denominator")
                == common_denominator
                and existing.get("envelope", {}).get("active_cut_count")
                == args.active_cuts
                and existing.get("envelope", {}).get("corner_candidate_limit")
                == args.corner_candidates
                and existing.get("envelope", {}).get("verdict") != "timeout"
            ):
                print(
                    f"q={q}: resume skip ({existing['envelope']['verdict']}) "
                    f"{output}"
                )
                continue
            raise ValueError(f"refusing to overwrite incompatible record {output}")
        record = make_record(
            q,
            cuts,
            digests,
            common_denominator,
            active_cut_count=args.active_cuts,
            corner_candidates=args.corner_candidates,
            timeout_seconds=args.timeout,
            progress=args.progress,
            brute_h_limit=args.brute_h_limit,
        )
        _atomic_json(output, record)
        envelope = record["envelope"]
        print(
            f"q={q} n={2*q} H={record['H(2q)']} "
            f"witness={record['witness']['armies']['black']}/"
            f"{record['witness']['armies']['white']} "
            f"verdict={envelope['verdict']} nodes={envelope['stats']['nodes']} "
            f"survivors={envelope['stats']['survivor_count']} "
            f"runtime={envelope['runtime_seconds']:.3f}s -> {output}",
            flush=True,
        )
        if envelope["verdict"] != "envelope_le_h_plus_half":
            exit_status = 1
            break
    return exit_status


if __name__ == "__main__":
    raise SystemExit(main())
