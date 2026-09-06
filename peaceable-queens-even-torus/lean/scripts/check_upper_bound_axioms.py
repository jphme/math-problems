#!/usr/bin/env python3
"""Audit the output of AuditUpperBound.lean against the documented trusted base.

This checks a Lean-produced report, not a proof or a certificate. Run the Lean
audit successfully first, and separately verify generated-source reproducibility.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re


ENDPOINTS = ("PeaceableQueens.upperBoundStatement", "PeaceableQueens.evenTorusTheorem")
NATIVE = "._native.native_decide.ax_1_1"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def expected_axioms(project: Path) -> set[str]:
    branch: set[str] = set()
    generated = project / "PeaceableQueens/UpperBound/Generated/Even"
    for stem, split_count, terminal_count in [("C527", 139, 39), ("Core", 89, 89)]:
        names = []
        for path in sorted(generated.glob(f"{stem}LeafRange*.lean")):
            names.extend(re.findall(
                r"^theorem ((?:split|terminal)_batch_[0-9]+_ok) : [^\n]* := by\n  native_decide$",
                path.read_text(), re.MULTILINE))
        if (len(names) != len(set(names)) or
                sum(n.startswith("split_") for n in names) != split_count or
                sum(n.startswith("terminal_") for n in names) != terminal_count):
            raise ValueError(f"unexpected generated native-batch declarations for {stem}")
        branch.update(f"PeaceableQueens.UpperBound.Generated.Even.{stem}.{n}{NATIVE}" for n in names)
    finite = {f"PeaceableQueens.UpperBound.Generated.Finite.Q{q:03d}.certificate_accepted{NATIVE}"
              for q in range(3, 130)}
    # SmallBoards now uses kernel decisions and an explicit translation argument.
    return STANDARD | branch | finite


def check_report(report: str, expected: set[str]) -> dict[str, set[str]]:
    results = {}
    for name in ENDPOINTS:
        blocks = re.findall(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", report)
        if len(blocks) != 1:
            raise ValueError(f"{name}: expected exactly one complete report, found {len(blocks)}")
        items = [value.strip() for value in blocks[0].split(",")]
        actual = set(items)
        if len(items) != len(actual):
            raise ValueError(f"{name}: duplicate axiom entries")
        if actual != expected:
            missing = sorted(expected - actual)
            extra = sorted(actual - expected)
            raise ValueError(f"{name}: missing={missing}, unexpected={extra}")
        results[name] = actual
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path, help="successful output of scripts/AuditUpperBound.lean")
    args = parser.parse_args()
    project = Path(__file__).resolve().parents[1]
    try:
        results = check_report(args.log.read_text(), expected_axioms(project))
    except (OSError, ValueError) as error:
        parser.error(str(error))
    for name, axioms in results.items():
        print(f"AXIOM_AUDIT_OK theorem={name} standard={len(STANDARD)} "
              f"native={len(axioms - STANDARD)} unexpected=0")


if __name__ == "__main__":
    main()
