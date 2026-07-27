#!/usr/bin/env python3
"""Run the portable, non-enumerative checks for the released proof bundle.

Invoke this script with a Python environment containing SymPy.  The long
exhaustive C++ searches and a full recomputation of the finite ladder are not
rerun here; their frozen outputs are audited.  See README.txt for commands
that rerun those computations.
"""

from __future__ import annotations

import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent


def verify_manifest() -> None:
    manifest = HERE / "SHA256SUMS"
    expected: dict[str, str] = {}
    for line_number, raw in enumerate(
        manifest.read_text(encoding="utf-8").splitlines(), start=1
    ):
        digest, separator, relative = raw.partition("  ")
        if (
            separator != "  "
            or len(digest) != 64
            or any(character not in "0123456789abcdef" for character in digest)
            or not relative
            or relative in expected
        ):
            raise RuntimeError(f"malformed SHA256SUMS line {line_number}")
        expected[relative] = digest

    actual = {
        path.relative_to(HERE).as_posix()
        for path in HERE.rglob("*")
        if path.is_file() and path != manifest
    }
    missing = sorted(set(expected) - actual)
    unlisted = sorted(actual - set(expected))
    if missing or unlisted:
        raise RuntimeError(
            f"manifest/file-set mismatch: missing={missing}, unlisted={unlisted}"
        )

    for relative in sorted(expected):
        digest = hashlib.sha256((HERE / relative).read_bytes()).hexdigest()
        if digest != expected[relative]:
            raise RuntimeError(
                f"SHA-256 mismatch for {relative}: {digest} != {expected[relative]}"
            )
    print(f"SHA256SUMS_OK files={len(expected)}", flush=True)


def run(*arguments: str, cwd: Path = HERE) -> None:
    command = [sys.executable, *arguments]
    print("+", " ".join(command), flush=True)
    subprocess.run(command, cwd=cwd, check=True)


def main() -> None:
    verify_manifest()
    run("verify_even_q_ge_130_bundle.py")
    run("verify_even_finite_independent.py")
    run("verify_even_finite_prose.py")
    with tempfile.TemporaryDirectory(prefix="peaceable-cuts-") as temporary:
        target = Path(temporary)
        run(
            "verify_support_duals.py",
            "--output",
            str(target / "verification.json"),
            "--moment-output",
            str(target / "moment_model.json"),
        )
    run("check_envelope_records.py")
    run("peace15_audit.py")
    run("check_peace15_independent_results.py")
    run("check_witness15.py")
    run("peace16_union_audit.py")
    run("check_witness16.py")
    run("check_witness17.py")

    sweep = HERE / "general_sweep"
    campaigns = ((8, 9), (12, 19), (14, 26), (17, 29), (18, 43))
    for n, target in campaigns:
        run(
            "audit_b.py",
            "--n",
            str(n),
            "--target",
            str(target),
            "--records",
            str(sweep / "results" / f"n{n}_t{target}_unsat.jsonl"),
            cwd=sweep,
        )

    print("PEACEABLE_QUEENS_RELEASE_BUNDLE_OK")


if __name__ == "__main__":
    main()
