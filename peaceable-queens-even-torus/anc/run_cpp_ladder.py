#!/usr/bin/env python3
"""Run the finite ladder through the separately implemented C++ box engine.

The C++ and Python engines implement the same exact integer-box algorithm;
agreement between them is an implementation cross-check, not a second
mathematical method.
"""

from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Sequence

import envelope_checker as checker


ENGINE_SOURCE = checker.HERE / "box_engine.cpp"
COMPILE_FLAGS = (
    "-std=c++17",
    "-O3",
    "-Wall",
    "-Wextra",
    "-Werror",
    "-pedantic",
)
_BUILD_DIRECTORIES: list[tempfile.TemporaryDirectory[str]] = []


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("q", nargs="*", type=int)
    parser.add_argument("--start", type=int)
    parser.add_argument("--end", type=int)
    parser.add_argument("--records-dir", type=Path, default=checker.DEFAULT_RECORDS)
    parser.add_argument("--active-cuts", type=int, default=76)
    parser.add_argument("--corner-candidates", type=int, default=6)
    parser.add_argument("--timeout", type=float, default=600.0)
    parser.add_argument("--brute-h-limit", type=int, default=30)
    parser.add_argument("--force", action="store_true")
    return parser.parse_args(argv)


def requested_qs(args: argparse.Namespace) -> list[int]:
    values = list(args.q)
    if (args.start is None) != (args.end is None):
        raise ValueError("--start and --end must be supplied together")
    if args.start is not None:
        if args.start > args.end:
            raise ValueError("--start exceeds --end")
        values.extend(range(args.start, args.end + 1))
    values = sorted(set(values))
    if not values:
        raise ValueError("supply q values or --start/--end")
    if values[0] < 1 or values[-1] > 1000:
        raise ValueError("the E3 engine accepts 1 <= q <= 1000")
    return values


def build_engine() -> tuple[Path, str]:
    source_digest = checker.sha256(ENGINE_SOURCE)
    build_directory = tempfile.TemporaryDirectory(
        prefix="peaceable-queens-finite-engine-"
    )
    _BUILD_DIRECTORIES.append(build_directory)
    binary = Path(build_directory.name) / "box_engine"
    command = [
        "g++",
        *COMPILE_FLAGS,
        str(ENGINE_SOURCE),
        "-o",
        str(binary),
    ]
    completed = subprocess.run(
        command,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode:
        raise RuntimeError(
            "C++ engine compilation failed:\n"
            + completed.stdout
            + completed.stderr
        )
    return binary, source_digest


def encode_query(
    cuts: Sequence[checker.Cut],
    q: int,
    h_value: int,
    active_cut_count: int,
    corner_candidates: int,
    timeout_seconds: float,
) -> str:
    scale = cuts[0].scale
    rows = [
        " ".join(
            map(
                str,
                (
                    scale,
                    len(cuts),
                    active_cut_count,
                    corner_candidates,
                    q,
                    h_value,
                    timeout_seconds,
                ),
            )
        )
    ]
    for cut in cuts:
        fields = [
            cut.constant,
            *cut.linear,
            len(cut.quadratic),
        ]
        for term in cut.quadratic:
            fields.extend(term)
        rows.append(" ".join(map(str, fields)))
    return "\n".join(rows) + "\n"


def run_engine(
    binary: Path,
    query: str,
    timeout_seconds: float,
) -> dict[str, object]:
    completed = subprocess.run(
        [str(binary)],
        input=query,
        text=True,
        capture_output=True,
        timeout=timeout_seconds + 30.0,
        check=False,
    )
    if completed.returncode not in (0, 2):
        raise RuntimeError(
            f"C++ engine exited {completed.returncode}:\n"
            + completed.stdout
            + completed.stderr
        )
    try:
        proof = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(
            "C++ engine emitted malformed JSON:\n" + completed.stdout
        ) from error
    if completed.returncode == 0 and proof.get("verdict") != (
        "envelope_le_h_plus_half"
    ):
        raise RuntimeError("C++ exit status/verdict mismatch")
    if completed.returncode == 2 and proof.get("verdict") == (
        "envelope_le_h_plus_half"
    ):
        raise RuntimeError("C++ exit status/verdict mismatch")
    return proof


def compatible_record(
    record: dict[str, object],
    q: int,
    digests: dict[str, str],
    coefficient_lcm: int,
    active_cut_count: int,
    corner_candidates: int,
) -> bool:
    return (
        record.get("schema") == checker.SCHEMA
        and record.get("q") == q
        and record.get("cut_library", {}).get("file_sha256") == digests
        and record.get("cut_library", {}).get("common_denominator")
        == coefficient_lcm
        and record.get("cut_library", {}).get("arithmetic_coefficient_scale")
        == math.lcm(coefficient_lcm, 2)
        and record.get("envelope", {}).get("active_cut_count")
        == active_cut_count
        and record.get("envelope", {}).get("corner_candidate_limit")
        == corner_candidates
        and record.get("envelope", {}).get("verdict") != "timeout"
    )


def make_cpp_record(
    q: int,
    cuts: Sequence[checker.Cut],
    digests: dict[str, str],
    coefficient_lcm: int,
    binary: Path,
    engine_digest: str,
    *,
    active_cut_count: int,
    corner_candidates: int,
    timeout_seconds: float,
    brute_h_limit: int,
) -> dict[str, object]:
    whole_started = time.monotonic()
    absolute_coefficient_sum = max(
        abs(cut.constant)
        + sum(abs(value) for value in cut.linear)
        + sum(abs(coefficient) for _, _, coefficient in cut.quadratic)
        for cut in cuts
    )
    integer_magnitude_bound = absolute_coefficient_sum * q * q
    if integer_magnitude_bound >= 2**63:
        raise OverflowError("C++ signed 64-bit arithmetic preflight failed")
    h_started = time.monotonic()
    h_value, optimizer, h_stats = checker.box_h(q)
    brute_crosscheck: dict[str, object]
    if q <= brute_h_limit:
        brute_h, brute_optimizer = checker.brute_force_h(q)
        if brute_h != h_value:
            raise AssertionError(f"H searches disagree at q={q}")
        brute_crosscheck = {
            "performed": True,
            "value": brute_h,
            "optimizer": list(brute_optimizer),
            "match": True,
        }
    else:
        brute_crosscheck = {"performed": False, "limit": brute_h_limit}
    h_runtime = time.monotonic() - h_started
    witness = checker.recount_witness(q, optimizer)
    if witness["armies"]["minimum"] < h_value:
        raise AssertionError("recounted witness falls below H")

    query = encode_query(
        cuts,
        q,
        h_value,
        active_cut_count,
        corner_candidates,
        timeout_seconds,
    )
    proof = run_engine(binary, query, timeout_seconds)
    return {
        "schema": checker.SCHEMA,
        "q": q,
        "n": 2 * q,
        "H(2q)": h_value,
        "h_optimizer": list(optimizer),
        "h_computation": {
            "method": "exact monotone-box branch-and-bound",
            "runtime_seconds": h_runtime,
            "search_stats": h_stats,
            "literal_bruteforce_crosscheck": brute_crosscheck,
        },
        "witness": witness,
        "envelope": proof,
        "cut_library": {
            "loaded_count": len(cuts),
            "common_denominator": coefficient_lcm,
            "arithmetic_coefficient_scale": cuts[0].scale,
            "common_denominator_derivation": (
                "LCM of every reduced rational coefficient in both cut files"
            ),
            "file_sha256": digests,
        },
        "algorithm": {
            "name": "canonical-integer-box branch-and-bound",
            "backend": "separately implemented C++17 exact box engine",
            "engine_source": "box_engine.cpp",
            "engine_source_sha256": engine_digest,
            "compile_flags": list(COMPILE_FLAGS),
            "bounds": [
                "integer linear-inequality propagation",
                "separable bilinear McCormick interval upper bound",
                "exact multi-affine corner maximum",
            ],
            "arithmetic": "signed 64-bit integer after checked q<=1000 scaling",
            "integer_magnitude_preflight": {
                "absolute_coefficient_sum_max": absolute_coefficient_sum,
                "q_squared_product_bound": integer_magnitude_bound,
                "signed_64_bit_max": 2**63 - 1,
                "pass": True,
            },
            "threads": 1,
            "whole_record_runtime_seconds": time.monotonic() - whole_started,
        },
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    qs = requested_qs(args)
    cuts, digests, coefficient_lcm = checker.load_cuts()
    if not (1 <= args.active_cuts <= len(cuts)):
        raise ValueError("invalid --active-cuts")
    binary, engine_digest = build_engine()
    for q in qs:
        output = args.records_dir / f"q{q:04d}.json"
        if output.exists() and not args.force:
            with output.open(encoding="utf-8") as handle:
                existing = json.load(handle)
            if compatible_record(
                existing,
                q,
                digests,
                coefficient_lcm,
                args.active_cuts,
                args.corner_candidates,
            ):
                print(
                    f"q={q}: resume skip ({existing['envelope']['verdict']}) "
                    f"{output}",
                    flush=True,
                )
                continue
            raise ValueError(f"refusing to overwrite incompatible record {output}")
        record = make_cpp_record(
            q,
            cuts,
            digests,
            coefficient_lcm,
            binary,
            engine_digest,
            active_cut_count=args.active_cuts,
            corner_candidates=args.corner_candidates,
            timeout_seconds=args.timeout,
            brute_h_limit=args.brute_h_limit,
        )
        checker._atomic_json(output, record)
        envelope = record["envelope"]
        print(
            f"q={q} n={2*q} H={record['H(2q)']} "
            f"witness={record['witness']['armies']['black']}/"
            f"{record['witness']['armies']['white']} "
            f"verdict={envelope['verdict']} nodes={envelope['stats']['nodes']} "
            f"survivors={envelope['stats']['survivor_count']} "
            f"runtime={envelope['runtime_seconds']:.6f}s -> {output}",
            flush=True,
        )
        if (
            envelope["verdict"] != "envelope_le_h_plus_half"
            or envelope["runtime_seconds"] > args.timeout
        ):
            return 1
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except subprocess.TimeoutExpired as error:
        print(f"C++ engine process timeout: {error}", file=sys.stderr)
        raise SystemExit(1)
