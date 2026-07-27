#!/usr/bin/env python3
"""Audit the frozen Python/C++ finite-envelope cross-check ledger.

This validates provenance and exact agreement with the released C++ run
summaries.  It does not rerun the slower Python computation; use
crosscheck_finite_backends.py for that.
"""

from __future__ import annotations

import json
from typing import Any

import crosscheck_finite_backends as crosscheck
import envelope_checker as checker
import replay_finite_envelope as replay
import run_cpp_ladder as cpp


EXPECTED_Q = list(range(61, 130))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def main() -> None:
    path = crosscheck.DEFAULT_OUTPUT
    ledger = json.loads(path.read_text(encoding="utf-8"))
    require(
        ledger.get("schema")
        == "peaceable-queens-finite-envelope-crosscheck-v1",
        "cross-check schema mismatch",
    )
    require(
        ledger.get("scope")
        == {"q_start": 61, "q_end": 129, "orders": len(EXPECTED_Q)},
        "cross-check scope mismatch",
    )

    _, cut_digests, coefficient_lcm = checker.load_cuts()
    require(
        ledger.get("cut_file_sha256") == cut_digests,
        "cross-check cut hashes mismatch",
    )
    require(
        ledger.get("computed_coefficient_lcm") == coefficient_lcm,
        "cross-check coefficient LCM mismatch",
    )
    require(
        ledger.get("python_source") == "envelope_checker.py"
        and ledger.get("python_source_sha256")
        == checker.sha256(checker.HERE / "envelope_checker.py"),
        "cross-check Python source mismatch",
    )
    require(
        ledger.get("cpp_source") == "box_engine.cpp"
        and ledger.get("cpp_source_sha256")
        == checker.sha256(checker.HERE / "box_engine.cpp"),
        "cross-check C++ source mismatch",
    )
    require(
        ledger.get("cpp_compile_flags") == list(cpp.COMPILE_FLAGS),
        "cross-check compile flags mismatch",
    )

    comparisons = ledger.get("comparisons")
    require(isinstance(comparisons, list), "comparisons must be an array")
    require(
        [entry.get("q") for entry in comparisons] == EXPECTED_Q,
        "cross-check order coverage mismatch",
    )
    total_nodes = 0
    for entry in comparisons:
        require(isinstance(entry, dict), "malformed comparison entry")
        q = entry["q"]
        frozen = json.loads(
            replay.record_path(q).read_text(encoding="utf-8")
        )
        normalized = replay.normalized_envelope(frozen["envelope"])
        nodes = normalized["stats"]["nodes"]
        require(entry.get("H(2q)") == frozen.get("H(2q)"), f"q={q}: H")
        require(entry.get("nodes") == nodes, f"q={q}: node count")
        require(
            entry.get("normalized_envelope_sha256")
            == crosscheck.canonical_digest(normalized),
            f"q={q}: normalized envelope digest",
        )
        require(
            entry.get("exact_nonruntime_envelope_match") is True,
            f"q={q}: cross-check verdict",
        )
        total_nodes += nodes

    require(ledger.get("total_nodes") == total_nodes, "total node mismatch")
    require(
        ledger.get("verdict")
        == "exact non-runtime envelope match at every listed order",
        "cross-check ledger verdict mismatch",
    )
    print(
        "FINITE_ENVELOPE_PYTHON_CROSSCHECK_LEDGER_OK "
        f"orders={len(EXPECTED_Q)} q=61..129 nodes={total_nodes}"
    )


if __name__ == "__main__":
    main()
