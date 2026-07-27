#!/usr/bin/env python3
"""Cross-check q=61..129 with the separately written Python engine.

The released frozen records in this range were produced by the C++17 engine.
This script reruns the same exact integer-box algorithm in Python, compares
every proof-relevant envelope field, and writes a deterministic cross-check
ledger.  The two implementations share the mathematical algorithm; this is
an implementation cross-check, not a conceptually independent proof method.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
from typing import Any, Sequence

import envelope_checker as checker
import replay_finite_envelope as replay
import run_cpp_ladder as cpp


HERE = Path(__file__).resolve().parent
DEFAULT_OUTPUT = HERE / "finite_envelope_python_crosscheck_q061_q129.json"
_WORKER_CUTS: Sequence[checker.Cut] | None = None


def canonical_digest(value: Any) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return hashlib.sha256(payload).hexdigest()


def _initialize_worker() -> None:
    global _WORKER_CUTS
    _WORKER_CUTS = checker.load_cuts()[0]


def _crosscheck_one(q: int, timeout_seconds: float) -> dict[str, Any]:
    if _WORKER_CUTS is None:
        _initialize_worker()
    assert _WORKER_CUTS is not None

    h_value, _, _ = checker.box_h(q)
    fresh = checker.certify_order(
        q,
        h_value,
        _WORKER_CUTS,
        active_cut_count=76,
        corner_candidates=6,
        timeout_seconds=timeout_seconds,
    )
    if fresh.get("verdict") != "envelope_le_h_plus_half":
        raise ValueError(f"q={q}: Python search did not close")

    return comparison_from_record(q, h_value, fresh)


def comparison_from_record(
    q: int, h_value: int, fresh: dict[str, Any]
) -> dict[str, Any]:
    """Validate one completed Python envelope result against the C++ summary."""

    frozen_path = replay.record_path(q)
    frozen = json.loads(frozen_path.read_text(encoding="utf-8"))
    if frozen.get("H(2q)") != h_value:
        raise ValueError(f"q={q}: H mismatch")
    normalized = replay.normalized_envelope(fresh)
    if normalized.get("verdict") != "envelope_le_h_plus_half":
        raise ValueError(f"q={q}: Python search did not close")
    if normalized != replay.normalized_envelope(frozen["envelope"]):
        raise ValueError(f"q={q}: Python/C++ envelope mismatch")

    return {
        "q": q,
        "H(2q)": h_value,
        "nodes": normalized["stats"]["nodes"],
        "normalized_envelope_sha256": canonical_digest(normalized),
        "exact_nonruntime_envelope_match": True,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, default=61)
    parser.add_argument("--end", type=int, default=129)
    parser.add_argument(
        "--jobs",
        type=int,
        default=min(4, os.cpu_count() or 1),
        help="parallel Python searches (default: min(4, CPU count))",
    )
    parser.add_argument("--timeout", type=float, default=600.0)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument(
        "--completed-records-dir",
        type=Path,
        help=(
            "reuse q????.json files already produced by envelope_checker.py "
            "instead of rerunning them"
        ),
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if not (61 <= args.start <= args.end <= 129):
        raise ValueError("this cross-check covers a subrange of 61..129")
    if args.jobs < 1:
        raise ValueError("--jobs must be positive")
    qs = list(range(args.start, args.end + 1))

    comparisons: list[dict[str, Any]] = []
    if args.completed_records_dir is not None:
        for q in qs:
            path = args.completed_records_dir / f"q{q:04d}.json"
            record = json.loads(path.read_text(encoding="utf-8"))
            if record.get("q") != q or record.get("n") != 2 * q:
                raise ValueError(f"{path}: q/n mismatch")
            h_value = record.get("H(2q)")
            if not isinstance(h_value, int):
                raise ValueError(f"{path}: malformed H")
            result = comparison_from_record(q, h_value, record["envelope"])
            comparisons.append(result)
            print(
                f"q={q}: IMPORTED_EXACT_PYTHON_CPP_MATCH "
                f"nodes={result['nodes']}",
                flush=True,
            )
    else:
        with concurrent.futures.ProcessPoolExecutor(
            max_workers=args.jobs, initializer=_initialize_worker
        ) as executor:
            futures = {
                executor.submit(_crosscheck_one, q, args.timeout): q for q in qs
            }
            for future in concurrent.futures.as_completed(futures):
                result = future.result()
                comparisons.append(result)
                print(
                    f"q={result['q']}: EXACT_PYTHON_CPP_MATCH "
                    f"nodes={result['nodes']}",
                    flush=True,
                )

    comparisons.sort(key=lambda item: item["q"])
    _, cut_digests, coefficient_lcm = checker.load_cuts()
    ledger = {
        "schema": "peaceable-queens-finite-envelope-crosscheck-v1",
        "scope": {
            "q_start": args.start,
            "q_end": args.end,
            "orders": len(qs),
        },
        "relation": (
            "separately written Python and C++ implementations of the same "
            "exact integer-box algorithm"
        ),
        "cut_file_sha256": cut_digests,
        "computed_coefficient_lcm": coefficient_lcm,
        "python_source": "envelope_checker.py",
        "python_source_sha256": checker.sha256(HERE / "envelope_checker.py"),
        "cpp_source": "box_engine.cpp",
        "cpp_source_sha256": checker.sha256(HERE / "box_engine.cpp"),
        "cpp_compile_flags": list(cpp.COMPILE_FLAGS),
        "comparisons": comparisons,
        "total_nodes": sum(item["nodes"] for item in comparisons),
        "verdict": "exact non-runtime envelope match at every listed order",
    }
    checker._atomic_json(args.output, ledger)
    print(
        "FINITE_ENVELOPE_PYTHON_CROSSCHECK_OK "
        f"orders={len(qs)} nodes={ledger['total_nodes']} -> {args.output}"
    )


if __name__ == "__main__":
    main()
