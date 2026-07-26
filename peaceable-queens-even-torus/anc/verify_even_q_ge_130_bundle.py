#!/usr/bin/env python3
"""Run every exact machine check used by the q>=130 even-order proof.

This bundle does not contain the project's independent exact ladder for
q<=1000.  It verifies the two infinite-range branch certificates and the
exact support-dual/algebra layer.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
commands = [
    [sys.executable, str(ROOT / "verify_even_branch_certificate.py"),
     str(ROOT / "even_c527_sym_mc.json.gz"),
     str(ROOT / "even_local_core_mc.json.gz")],
    [sys.executable, str(ROOT / "verify_even_finite_algebra.py"),
     str(ROOT / "even_finite_support_cuts.json")],
]
for command in commands:
    subprocess.run(command, check=True)
print("EVEN_Q_GE_130_BUNDLE_OK")
