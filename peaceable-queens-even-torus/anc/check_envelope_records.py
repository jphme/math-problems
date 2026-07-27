#!/usr/bin/env python3
"""Fail-closed audit of the 122 compact finite-envelope run summaries.

This checker validates order coverage, schemas, exact H values, witnesses,
input and engine hashes, thresholds, and aggregate full-binary-tree
accounting.  The summaries contain no individual nodes or terminal boxes, so
this audit does not prove geometric coverage.  Run replay_finite_envelope.py
to re-establish coverage by repeating every exact search from source.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
RECORD_DIRS = (HERE / "records_q003_q020", HERE / "records_q021_q129")
EXPECTED_Q = {3, 5, *range(10, 130)}
EXPECTED_SCHEMA = "peaceable-queens-e2e3-envelope-box-proof-v2"
EXPECTED_CPP_DIGEST = (
    "ea916eb518261a3bbe9558bcb95ec8471d9a765e15667d767eafe35636af9ae2"
)
EXPECTED_CPP_FLAGS = [
    "-std=c++17",
    "-O3",
    "-Wall",
    "-Wextra",
    "-Werror",
    "-pedantic",
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def nonnegative_int(value: Any, label: str) -> int:
    require(
        isinstance(value, int) and not isinstance(value, bool) and value >= 0,
        f"{label}: expected nonnegative integer",
    )
    return value


def crossing_h(q: int) -> int:
    """Evaluate H(2q) exactly in O(q^3), directly from its definition.

    For fixed r0,r1,c0, the black count is nondecreasing and the white count
    nonincreasing in c1.  Their minimum is maximized at one of the two
    integers adjacent to their crossing, clamped to [0,q].
    """

    best = -1
    for r0 in range(q + 1):
        for r1 in range(q + 1):
            denominator = q + r0 - r1
            for c0 in range(q + 1):
                if denominator == 0:
                    candidates = (0,)
                else:
                    numerator = (
                        (q - r0) * (q - c0)
                        + q * (q - r1)
                        - r1 * c0
                    )
                    floor_crossing = numerator // denominator
                    candidates = (
                        min(q, max(0, floor_crossing)),
                        min(q, max(0, floor_crossing + 1)),
                    )
                for c1 in candidates:
                    black = r0 * c1 + r1 * c0
                    white = (
                        (q - r0) * (q - c0)
                        + (q - r1) * (q - c1)
                    )
                    best = max(best, min(black, white))
    return best


def load_records() -> dict[int, tuple[Path, dict[str, Any]]]:
    records: dict[int, tuple[Path, dict[str, Any]]] = {}
    for directory in RECORD_DIRS:
        require(directory.is_dir(), f"missing record directory: {directory}")
        for path in sorted(directory.glob("q????.json")):
            record = json.loads(path.read_text(encoding="utf-8"))
            q = record.get("q")
            require(isinstance(q, int), f"{path}: invalid q")
            require(path.name == f"q{q:04d}.json", f"{path}: filename/q mismatch")
            require(q not in records, f"duplicate q={q}")
            records[q] = (path, record)
    require(
        set(records) == EXPECTED_Q,
        "record-order mismatch: "
        f"missing={sorted(EXPECTED_Q - set(records))}, "
        f"extra={sorted(set(records) - EXPECTED_Q)}",
    )
    return records


def sum_nonnegative_values(mapping: Any, label: str) -> int:
    require(isinstance(mapping, dict), f"{label}: expected object")
    return sum(
        nonnegative_int(value, f"{label}.{key}")
        for key, value in mapping.items()
    )


def check_record(
    q: int,
    path: Path,
    record: dict[str, Any],
    cut_hashes: dict[str, str],
    coefficient_lcm: int,
) -> int:
    prefix = str(path)
    require(record.get("schema") == EXPECTED_SCHEMA, f"{prefix}: schema")
    require(record.get("q") == q and record.get("n") == 2 * q, f"{prefix}: q/n")

    h_value = nonnegative_int(record.get("H(2q)"), f"{prefix}: H(2q)")
    require(crossing_h(q) == h_value, f"{prefix}: exact H recomputation")
    optimizer = record.get("h_optimizer")
    require(
        isinstance(optimizer, list)
        and len(optimizer) == 4
        and all(isinstance(value, int) and 0 <= value <= q for value in optimizer),
        f"{prefix}: h_optimizer",
    )
    r0, r1, c0, c1 = optimizer
    black = r0 * c1 + r1 * c0
    white = (q - r0) * (q - c0) + (q - r1) * (q - c1)
    require(min(black, white) == h_value, f"{prefix}: optimizer score")

    witness = record.get("witness")
    require(isinstance(witness, dict), f"{prefix}: witness")
    armies = witness.get("armies")
    lines = witness.get("line_counts")
    require(isinstance(armies, dict) and isinstance(lines, dict), f"{prefix}: witness fields")
    require(
        witness.get("outer_profile") == [r0, r1, c0, c1, 0, q, 0, q],
        f"{prefix}: witness profile",
    )
    require(
        armies
        == {
            "black": black,
            "white": white,
            "minimum": h_value,
            "overlap": 0,
            "cells_recounted": 4 * q * q,
        },
        f"{prefix}: witness armies",
    )
    require(
        lines
        == {
            "rows": r0 + r1,
            "columns": c0 + c1,
            "diagonals": q,
            "antidiagonals": q,
            "total": r0 + r1 + c0 + c1 + 2 * q,
        },
        f"{prefix}: witness line counts",
    )

    library = record.get("cut_library")
    require(isinstance(library, dict), f"{prefix}: cut_library")
    require(library.get("loaded_count") == 760, f"{prefix}: cut count")
    require(library.get("file_sha256") == cut_hashes, f"{prefix}: cut hashes")
    require(
        library.get("common_denominator") == coefficient_lcm,
        f"{prefix}: coefficient LCM",
    )
    scale = math.lcm(coefficient_lcm, 2)
    require(
        library.get("arithmetic_coefficient_scale") == scale,
        f"{prefix}: arithmetic scale",
    )

    envelope = record.get("envelope")
    require(isinstance(envelope, dict), f"{prefix}: envelope")
    require(
        envelope.get("verdict") == "envelope_le_h_plus_half",
        f"{prefix}: verdict",
    )
    require(envelope.get("unfinished_stack_boxes") == 0, f"{prefix}: unfinished")
    require(envelope.get("survivors") == [], f"{prefix}: survivors")
    require(envelope.get("active_cut_count") == 76, f"{prefix}: active cuts")
    require(
        envelope.get("corner_candidate_limit") == 6,
        f"{prefix}: corner candidate limit",
    )
    threshold = envelope.get("threshold")
    require(isinstance(threshold, dict), f"{prefix}: threshold")
    require(
        threshold.get("integer_comparison_scale") == scale
        and threshold.get("integer_threshold") == scale * h_value + scale // 2,
        f"{prefix}: threshold arithmetic",
    )

    stats = envelope.get("stats")
    require(isinstance(stats, dict), f"{prefix}: stats")
    required_stats = (
        "nodes",
        "propagation_infeasible",
        "certified_boxes",
        "interval_certified_boxes",
        "corner_certified_boxes",
        "point_boxes",
        "survivor_count",
        "max_depth",
        "max_stack",
    )
    values = {
        name: nonnegative_int(stats.get(name), f"{prefix}: stats.{name}")
        for name in required_stats
    }
    require(values["survivor_count"] == 0, f"{prefix}: survivor count")
    nodes = values["nodes"]
    require(nodes > 0 and nodes % 2 == 1, f"{prefix}: node parity")
    require(
        values["certified_boxes"] + values["propagation_infeasible"]
        == (nodes + 1) // 2,
        f"{prefix}: aggregate terminal accounting",
    )
    require(
        values["certified_boxes"]
        == values["interval_certified_boxes"]
        + values["corner_certified_boxes"]
        + values["point_boxes"],
        f"{prefix}: certified-box decomposition",
    )
    require(
        sum_nonnegative_values(envelope.get("cut_box_wins"), f"{prefix}: cut wins")
        == values["certified_boxes"],
        f"{prefix}: cut-win accounting",
    )

    algorithm = record.get("algorithm")
    require(isinstance(algorithm, dict), f"{prefix}: algorithm")
    require(
        algorithm.get("name") == "canonical-integer-box branch-and-bound"
        and algorithm.get("threads") == 1,
        f"{prefix}: algorithm identity",
    )
    if q <= 60:
        require(
            "engine_source" not in algorithm and "engine_source_sha256" not in algorithm,
            f"{prefix}: unexpected historical source metadata",
        )
    else:
        require(
            algorithm.get("backend") == "independent C++17 exact box engine",
            f"{prefix}: C++ backend label",
        )
        require(
            algorithm.get("engine_source")
            == "peaceable_queens/envelope-ladder/e2e3/box_engine.cpp",
            f"{prefix}: recorded C++ source path",
        )
        require(
            algorithm.get("engine_source_sha256") == EXPECTED_CPP_DIGEST,
            f"{prefix}: recorded C++ source hash",
        )
        require(
            algorithm.get("compile_flags") == EXPECTED_CPP_FLAGS,
            f"{prefix}: C++ compile flags",
        )
        preflight = algorithm.get("integer_magnitude_preflight")
        require(
            preflight
            == {
                "absolute_coefficient_sum_max": 360,
                "q_squared_product_bound": 360 * q * q,
                "signed_64_bit_max": 2**63 - 1,
                "pass": True,
            },
            f"{prefix}: integer-width preflight",
        )
    return nodes


def main() -> None:
    cpp_source = HERE / "box_engine.cpp"
    python_source = HERE / "envelope_checker.py"
    require(cpp_source.is_file(), "missing released C++ engine")
    require(python_source.is_file(), "missing released Python engine")
    require(
        sha256(cpp_source) == EXPECTED_CPP_DIGEST,
        "released C++ engine does not match the q=61..129 records",
    )

    cut_hashes = {
        "benders_cuts.json": sha256(HERE / "benders_cuts.json"),
        "new_dual_cuts.json": sha256(HERE / "new_dual_cuts.json"),
    }
    # All rational coefficients in the frozen cut files have denominators
    # dividing 12; the engine uses lcm(12,2)=12 as its integer scale.
    coefficient_lcm = 12
    records = load_records()
    total_nodes = sum(
        check_record(q, path, record, cut_hashes, coefficient_lcm)
        for q, (path, record) in sorted(records.items())
    )
    require(total_nodes == 13_379_092, "aggregate node total mismatch")
    print(
        "ENVELOPE_RECORD_SUMMARIES_OK "
        f"orders={len(records)} q=3,5,10..129 nodes={total_nodes} "
        "aggregate_tree_accounting=checked "
        f"python_source_sha256={sha256(python_source)} "
        f"cpp_source_sha256={sha256(cpp_source)}"
    )
    print(
        "NOTE summaries_have_no_terminal_boxes; "
        "run replay_finite_envelope.py for exhaustive domain coverage"
    )


if __name__ == "__main__":
    main()
