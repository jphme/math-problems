#!/usr/bin/env python3
"""Re-run the complete finite cut-envelope proof with exact C++17 arithmetic.

The archived per-order JSON files are compact run summaries, not serialized
search trees.  This program therefore recompiles the released engine, repeats
all 122 exhaustive integer-box searches, and compares every proof-relevant
envelope field with the frozen summaries.  A successful run re-establishes
domain coverage from source.
"""

from __future__ import annotations

import copy
import json
from pathlib import Path
from typing import Any

import envelope_checker as checker
import run_cpp_ladder as cpp


HERE = Path(__file__).resolve().parent
EXPECTED_Q = (3, 5, *range(10, 130))
MILESTONES = {3, 5, 10, 20, 40, 60, 80, 100, 120, 129}


def record_path(q: int) -> Path:
    directory = "records_q003_q020" if q <= 20 else "records_q021_q129"
    return HERE / directory / f"q{q:04d}.json"


def normalized_envelope(envelope: dict[str, Any]) -> dict[str, Any]:
    """Remove runtime noise and normalize two legacy omitted zero counters."""

    result = copy.deepcopy(envelope)
    result.pop("runtime_seconds", None)
    stats = result.get("stats")
    if not isinstance(stats, dict):
        raise ValueError("envelope has no stats object")
    stats.setdefault("fallback_full_library_points", 0)
    stats.setdefault("fallback_cut_point_evaluations", 0)
    return result


def main() -> None:
    cuts, digests, coefficient_lcm = checker.load_cuts()
    if len(cuts) != 760:
        raise AssertionError(f"unexpected cut count: {len(cuts)}")
    binary, source_digest = cpp.build_engine()

    total_nodes = 0
    for q in EXPECTED_Q:
        path = record_path(q)
        frozen = json.loads(path.read_text(encoding="utf-8"))
        if frozen.get("q") != q or frozen.get("n") != 2 * q:
            raise ValueError(f"{path}: q/n mismatch")
        if frozen.get("cut_library", {}).get("file_sha256") != digests:
            raise ValueError(f"{path}: cut digest mismatch")
        if (
            frozen.get("cut_library", {}).get("common_denominator")
            != coefficient_lcm
        ):
            raise ValueError(f"{path}: coefficient LCM mismatch")

        algorithm = frozen.get("algorithm", {})
        if q >= 61 and (
            algorithm.get("engine_source_sha256") != source_digest
            or algorithm.get("compile_flags") != list(cpp.COMPILE_FLAGS)
        ):
            raise ValueError(f"{path}: released C++ source metadata mismatch")

        h_value, _, _ = checker.box_h(q)
        if frozen.get("H(2q)") != h_value:
            raise ValueError(f"{path}: fresh H mismatch")
        query = cpp.encode_query(
            cuts,
            q,
            h_value,
            active_cut_count=76,
            corner_candidates=6,
            timeout_seconds=600.0,
        )
        fresh = cpp.run_engine(binary, query, timeout_seconds=600.0)
        if fresh.get("verdict") != "envelope_le_h_plus_half":
            raise ValueError(f"q={q}: fresh envelope search did not close")
        if normalized_envelope(fresh) != normalized_envelope(frozen["envelope"]):
            raise ValueError(f"q={q}: fresh/frozen envelope mismatch")

        nodes = fresh.get("stats", {}).get("nodes")
        if not isinstance(nodes, int) or nodes <= 0:
            raise ValueError(f"q={q}: malformed fresh node count")
        total_nodes += nodes
        if q in MILESTONES:
            print(f"q={q}: EXACT_FULL_REPLAY_MATCH nodes={nodes}", flush=True)

    print(
        "FINITE_ENVELOPE_FULL_REPLAY_OK "
        f"orders={len(EXPECTED_Q)} q=3,5,10..129 nodes={total_nodes} "
        f"cpp_source_sha256={source_digest}"
    )


if __name__ == "__main__":
    main()
