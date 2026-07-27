#!/usr/bin/env python3
"""Check the frozen finite-ladder records and their bound inputs."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
RECORD_DIRS = (HERE / "records_q003_q020", HERE / "records_q021_q129")
EXPECTED_Q = {3, 5, *range(10, 130)}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> None:
    expected_hashes = {
        "benders_cuts.json": sha256(HERE / "benders_cuts.json"),
        "new_dual_cuts.json": sha256(HERE / "new_dual_cuts.json"),
    }
    records: dict[int, dict[str, object]] = {}
    for directory in RECORD_DIRS:
        for path in sorted(directory.glob("q????.json")):
            record = json.loads(path.read_text(encoding="utf-8"))
            q = record.get("q")
            assert isinstance(q, int), f"{path}: invalid q"
            assert q not in records, f"duplicate q={q}"
            records[q] = record

    assert set(records) == EXPECTED_Q, (
        f"record coverage mismatch: missing={sorted(EXPECTED_Q - set(records))}, "
        f"extra={sorted(set(records) - EXPECTED_Q)}"
    )
    total_nodes = 0
    for q, record in records.items():
        assert record.get("n") == 2 * q
        envelope = record.get("envelope")
        witness = record.get("witness")
        cuts = record.get("cut_library")
        assert isinstance(envelope, dict)
        assert isinstance(witness, dict)
        assert isinstance(cuts, dict)
        assert envelope.get("verdict") == "envelope_le_h_plus_half"
        assert envelope.get("unfinished_stack_boxes") == 0
        stats = envelope.get("stats")
        armies = witness.get("armies")
        assert isinstance(stats, dict)
        assert isinstance(armies, dict)
        assert stats.get("survivor_count") == 0
        assert armies.get("minimum") == record.get("H(2q)")
        assert armies.get("overlap") == 0
        assert cuts.get("file_sha256") == expected_hashes
        nodes = stats.get("nodes")
        assert isinstance(nodes, int) and nodes > 0
        total_nodes += nodes

    print(
        "ENVELOPE_RECORDS_OK "
        f"orders={len(records)} q=3,5,10..129 nodes={total_nodes}"
    )


if __name__ == "__main__":
    main()
