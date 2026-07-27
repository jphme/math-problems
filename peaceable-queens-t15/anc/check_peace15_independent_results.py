#!/usr/bin/env python3
"""Check structural integrity and completeness of profile-enumerator JSONL."""
from __future__ import annotations

import argparse
import json
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXPECTED_SOUND_COMPLETIONS = 6_241_793_402


def load_worklist(path: Path) -> set[tuple[int, int, int, int]]:
    profiles = set()
    for line in path.read_text().splitlines():
        if line and not line.startswith("#"):
            profiles.add(tuple(map(int, line.split("\t")[0].split(","))))
    return profiles


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--worklist",
        type=Path,
        default=ROOT / "WORKLIST-2026-07-25.tsv",
    )
    parser.add_argument(
        "--results",
        type=Path,
        default=ROOT / "peace15_independent_results.jsonl",
    )
    args = parser.parse_args()

    worklist = load_worklist(args.worklist)
    records = [
        json.loads(line)
        for line in args.results.read_text().splitlines()
        if line.strip()
    ]
    by_profile = {tuple(record["profile"]): record for record in records}
    assert len(records) == len(by_profile), "duplicate profile records"
    assert set(by_profile) == worklist, "results do not exactly cover the worklist"

    total = 0
    for profile, record in by_profile.items():
        assert record["S"] == sum(profile)
        assert record["result"] == "UNSAT"
        assert record["witness"] is None
        assert record["thresholds"] == [21, 21]
        assert record["reps_enumerated"] == record["orbit_reps_total"]
        assert record["orbit_reps_total"] >= record.get(
            "brief_orbit_lower_bound", 0
        )

        if record["fixed"] == "RC":
            completion_size = profile[3]
            epsilon_is_sound = profile[2] == profile[3]
            transpose_is_sound = profile[0] == profile[1]
        else:
            assert record["fixed"] == "DA"
            completion_size = profile[0]
            epsilon_is_sound = profile[0] == profile[1]
            transpose_is_sound = profile[2] == profile[3]
        assert record["symmetry"]["epsilon"] == epsilon_is_sound
        assert record["symmetry"]["transpose"] == transpose_is_sound
        assert record["completions"] == (
            record["orbit_reps_total"] * comb(15, completion_size)
        )
        total += record["completions"]

    assert len(records) == 247
    assert total == EXPECTED_SOUND_COMPLETIONS
    print(
        f"PASS: {len(records)} unique profiles, all UNSAT, "
        f"{total:,} sound completions"
    )


if __name__ == "__main__":
    main()
