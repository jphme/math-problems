#!/usr/bin/env python3
"""Independent bookkeeping/audit for impl_b.

This script intentionally regenerates profiles, oriented jobs, affine pair
orbit counts (by Burnside), even-board incidence, and SAT witness counts.  It
does not import or execute the C++ solver.
"""

from __future__ import annotations

import argparse
import collections
import csv
import functools
import json
import math
import pathlib
import sys
from typing import Iterable, Sequence


def profile_passes(n: int, tau: int, p: tuple[int, ...]) -> bool:
    if n % 2:
        if sum(p) > 2 * n:
            return False
        for i in range(4):
            for j in range(i + 1, 4):
                if p[i] * p[j] < tau:
                    return False
                if (n - p[i]) * (n - p[j]) < tau:
                    return False
        for omitted in range(4):
            x, y, z = (p[i] for i in range(4) if i != omitted)
            if n * n - n * (x + y + z) + x * y + x * z + y * z < 2 * tau:
                return False
        return True

    r, c, d0, d1, a0, a1 = p
    h = n // 2
    d, a = d0 + d1, a0 + a1
    if r + c + d + a > 2 * n:
        return False
    for x, y in ((r, c), (r, d), (r, a), (c, d), (c, a)):
        if x * y < tau or (n - x) * (n - y) < tau:
            return False
    if 2 * (d0 * a0 + d1 * a1) < tau:
        return False
    if 2 * ((h - d0) * (h - a0) + (h - d1) * (h - a1)) < tau:
        return False
    if n * n - n * (r + c + d) + r * c + r * d + c * d < 2 * tau:
        return False
    if n * n - n * (r + c + a) + r * c + r * a + c * a < 2 * tau:
        return False
    pair_term = 2 * (d0 * a0 + d1 * a1)
    for x in (r, c):
        if n * n - n * (x + d + a) + x * d + x * a + pair_term < 2 * tau:
            return False
    return True


def profile_neighbors(n: int, p: tuple[int, ...]) -> Iterable[tuple[int, ...]]:
    if n % 2:
        r, c, d, a = p
        yield (c, r, d, a)
        yield (r, c, a, d)
        yield (a, d, c, r)
        if sum(p) == 2 * n:
            yield tuple(n - x for x in p)
    else:
        r, c, d0, d1, a0, a1 = p
        yield (c, r, d0, d1, a0, a1)
        yield (r, c, a0, a1, d0, d1)
        yield (r, c, d1, d0, a1, a0)
        if sum(p) == 2 * n:
            h = n // 2
            yield (n - r, n - c, h - d0, h - d1, h - a0, h - a1)


def canonical_profile(n: int, p: tuple[int, ...]) -> tuple[int, ...]:
    seen = {p}
    queue = [p]
    for current in queue:
        for other in profile_neighbors(n, current):
            if other not in seen:
                seen.add(other)
                queue.append(other)
    return min(seen)


def regenerate_profiles(
    n: int, tau: int
) -> tuple[int, list[tuple[int, ...]], list[tuple[tuple[int, ...], tuple[int, ...]]]]:
    canonical: set[tuple[int, ...]] = set()
    ordered = 0
    if n % 2:
        for r in range(n + 1):
            for c in range(n + 1):
                for d in range(n + 1):
                    for a in range(n + 1):
                        p = (r, c, d, a)
                        if profile_passes(n, tau, p):
                            ordered += 1
                            canonical.add(canonical_profile(n, p))
    else:
        h = n // 2
        for r in range(n + 1):
            for c in range(n + 1):
                for d0 in range(h + 1):
                    for d1 in range(h + 1):
                        if r + c + d0 + d1 > 2 * n:
                            continue
                        for a0 in range(h + 1):
                            for a1 in range(h + 1):
                                p = (r, c, d0, d1, a0, a1)
                                if profile_passes(n, tau, p):
                                    ordered += 1
                                    canonical.add(canonical_profile(n, p))
    profiles = sorted(canonical)
    jobs: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
    for p in profiles:
        if n % 2:
            seen = {p}
            queue = [p]
            for current in queue:
                r, c, d, a = current
                for candidate in (
                    (c, r, d, a),
                    (r, c, a, d),
                    (a, d, c, r),
                ):
                    if candidate not in seen:
                        seen.add(candidate)
                        queue.append(candidate)

            def odd_cost(candidate: tuple[int, ...]) -> int:
                r, c, d, a = candidate
                return burnside_pair_count(
                    n, r, c, r == c, d == a
                ) * math.comb(n, a)

            base = min(seen, key=lambda candidate: (odd_cost(candidate), candidate))
        else:
            r, c, d0, d1, a0, a1 = p
            candidates = (
                p,
                (c, r, d0, d1, a0, a1),
                (r, c, a0, a1, d0, d1),
                (c, r, a0, a1, d0, d1),
            )

            def even_cost(candidate: tuple[int, ...]) -> int:
                return math.comb(n // 2, candidate[4]) * math.comb(
                    n // 2, candidate[5]
                )

            base = min(
                candidates, key=lambda candidate: (even_cost(candidate), candidate)
            )
        jobs.append((p, base))
        if not n % 2:
            flipped = (base[0], base[1], base[3], base[2], base[5], base[4])
            if flipped != base:
                jobs.append((p, flipped))
    jobs.sort()
    return ordered, profiles, jobs


def affine_cycles(n: int, multiplier: int, shift: int) -> list[int]:
    seen = [False] * n
    cycles: list[int] = []
    for start in range(n):
        if seen[start]:
            continue
        at = start
        length = 0
        while not seen[at]:
            seen[at] = True
            length += 1
            at = (multiplier * at + shift) % n
        if at != start:
            raise AssertionError("non-bijection in affine cycle audit")
        cycles.append(length)
    return cycles


@functools.lru_cache(maxsize=None)
def invariant_k_subsets(n: int, k: int, multiplier: int, shift: int) -> int:
    dp = [0] * (k + 1)
    dp[0] = 1
    for length in affine_cycles(n, multiplier, shift):
        for size in range(k, length - 1, -1):
            dp[size] += dp[size - length]
    return dp[k]


@functools.lru_cache(maxsize=None)
def burnside_pair_count(
    n: int, r: int, c: int, transpose: bool, relative_sign: bool
) -> int:
    if transpose and r != c:
        raise AssertionError("transpose requested for unequal sizes")
    units = [u for u in range(1, n) if math.gcd(u, n) == 1]
    fixed_sum = 0
    for swapped in range(2 if transpose else 1):
        for sign in range(2 if relative_sign else 1):
            for u in units:
                v = (-u) % n if sign else u
                for alpha in range(n):
                    for beta in range(n):
                        if not swapped:
                            fixed_sum += invariant_k_subsets(
                                n, r, u, alpha
                            ) * invariant_k_subsets(n, c, v, beta)
                        else:
                            fixed_sum += invariant_k_subsets(
                                n,
                                r,
                                (u * v) % n,
                                (u * beta + alpha) % n,
                            )
    order = len(units) * n * n
    if transpose:
        order *= 2
    if relative_sign:
        order *= 2
    quotient, remainder = divmod(fixed_sum, order)
    if remainder:
        raise AssertionError("nonintegral Burnside average")
    return quotient


def verify_two_lifts(n: int) -> None:
    if n % 2:
        return
    counts = [[0] * n for _ in range(n)]
    for r in range(n):
        for c in range(n):
            counts[(r - c) % n][(r + c) % n] += 1
    for d in range(n):
        for a in range(n):
            expected = 2 if d % 2 == a % 2 else 0
            if counts[d][a] != expected:
                raise AssertionError(f"two-lift failure d={d}, a={a}")


def parse_mask(value: str) -> int:
    return int(value, 0)


def verify_witness(n: int, witness: dict[str, object]) -> tuple[int, int]:
    rows = parse_mask(str(witness["R"]))
    columns = parse_mask(str(witness["C"]))
    diagonals = parse_mask(str(witness["D"]))
    antidiagonals = parse_mask(str(witness["A"]))
    black = white = 0
    for r in range(n):
        for c in range(n):
            memberships = (
                bool(rows >> r & 1),
                bool(columns >> c & 1),
                bool(diagonals >> ((r - c) % n) & 1),
                bool(antidiagonals >> ((r + c) % n) & 1),
            )
            black += all(memberships)
            white += not any(memberships)
    return black, white


TSV_SCHEMA_LINE = "# peaceable-queens impl_b deterministic job certificate"
TSV_COLUMNS = [
    "job_id",
    "canonical_profile",
    "oriented_profile",
    "S",
    "r",
    "c",
    "d0",
    "d1",
    "a0",
    "a1",
    "relative_sign_quotient",
    "orbit_count",
    "orbit_list_sha256",
    "a_count_per_orbit",
    "a_space",
    "a_checked",
    "prefilter_survivors",
    "exact_calls",
    "mitm_queries",
    "verdict",
    "seconds",
]


def write_tsv(path: pathlib.Path, records: Sequence[dict[str, object]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        handle.write(TSV_SCHEMA_LINE + "\n")
        handle.write("# " + "\t".join(TSV_COLUMNS) + "\n")
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        for record in sorted(records, key=lambda item: int(item["job_id"])):
            row = []
            for column in TSV_COLUMNS:
                value = record[column]
                if isinstance(value, (list, dict)):
                    value = json.dumps(value, separators=(",", ":"), sort_keys=True)
                row.append(value)
            writer.writerow(row)
        totals = {
            key: sum(int(record[key]) for record in records)
            for key in ("a_space", "a_checked", "prefilter_survivors", "exact_calls")
        }
        handle.write(
            "# totals "
            + " ".join(f"{key}={value}" for key, value in totals.items())
            + "\n"
        )


def audit(args: argparse.Namespace) -> None:
    ordered, profiles, jobs = regenerate_profiles(args.n, args.target)
    strata = collections.Counter(map(sum, profiles))
    verify_two_lifts(args.n)
    print(
        "WORKLIST_AUDIT_OK",
        f"ordered={ordered}",
        f"canonical={len(profiles)}",
        f"oriented_jobs={len(jobs)}",
        f"strata={dict(sorted(strata.items()))}",
    )

    records: list[dict[str, object]] = []
    with args.records.open(encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.strip() or line.startswith("#"):
                continue
            record = json.loads(line)
            if int(record["n"]) != args.n or int(record["target"]) != args.target:
                continue
            if not record["complete"]:
                raise AssertionError(f"incomplete record at line {line_number}")
            records.append(record)

    by_id: dict[int, dict[str, object]] = {}
    for record in records:
        job_id = int(record["job_id"])
        if job_id in by_id:
            raise AssertionError(f"duplicate completed job id {job_id}")
        by_id[job_id] = record
        if not (0 <= job_id < len(jobs)):
            raise AssertionError(f"out-of-range job id {job_id}")
        canonical, oriented = jobs[job_id]
        if tuple(record["canonical_profile"]) != canonical:
            raise AssertionError(f"canonical profile mismatch at job {job_id}")
        if tuple(record["oriented_profile"]) != oriented:
            raise AssertionError(f"oriented profile mismatch at job {job_id}")
        if args.n % 2:
            r, c, d, a = oriented
            transpose = r == c
            sign = d == a
            a_count = math.comb(args.n, a)
        else:
            r, c, d0, d1, a0, a1 = oriented
            transpose = r == c
            sign = (d0, d1) == (a0, a1)
            a_count = math.comb(args.n // 2, a0) * math.comb(args.n // 2, a1)
        if bool(record["transpose_quotient"]) != transpose:
            raise AssertionError(f"transpose flag mismatch at job {job_id}")
        if bool(record["relative_sign_quotient"]) != sign:
            raise AssertionError(f"relative sign flag mismatch at job {job_id}")
        orbit_count = burnside_pair_count(args.n, r, c, transpose, sign)
        if int(record["orbit_count"]) != orbit_count:
            raise AssertionError(
                f"Burnside mismatch at job {job_id}: "
                f"{record['orbit_count']} != {orbit_count}"
            )
        if int(record["a_count_per_orbit"]) != a_count:
            raise AssertionError(f"A count mismatch at job {job_id}")
        if int(record["a_space"]) != orbit_count * a_count:
            raise AssertionError(f"A space mismatch at job {job_id}")
        if record["verdict"] == "UNSAT":
            if int(record["a_checked"]) != int(record["a_space"]):
                raise AssertionError(f"incomplete UNSAT coverage at job {job_id}")
            if record["witness"] is not None:
                raise AssertionError(f"UNSAT job {job_id} has witness")
        elif record["verdict"] == "SAT":
            if record["witness"] is None:
                raise AssertionError(f"SAT job {job_id} lacks witness")
            black, white = verify_witness(args.n, record["witness"])
            if (black, white) != (
                int(record["witness"]["B"]),
                int(record["witness"]["W"]),
            ):
                raise AssertionError(f"witness count mismatch at job {job_id}")
            if min(black, white) < args.target:
                raise AssertionError(f"invalid SAT witness at job {job_id}")
        else:
            raise AssertionError(f"unknown verdict at job {job_id}")

    if not args.allow_partial and len(by_id) != len(jobs):
        missing = sorted(set(range(len(jobs))) - set(by_id))
        raise AssertionError(
            f"certificate has {len(by_id)}/{len(jobs)} jobs; "
            f"first missing={missing[:10]}"
        )

    totals = {
        key: sum(int(record[key]) for record in records)
        for key in ("a_space", "a_checked", "prefilter_survivors", "exact_calls")
    }
    if args.expect_n16_c1:
        expected = {
            "canonical": 342,
            "jobs": 677,
            "a_space": 13_163_028_768,
            "prefilter_survivors": 17_834,
        }
        if args.n != 16 or args.target != 33:
            raise AssertionError("--expect-n16-c1 requires n=16,target=33")
        if len(profiles) != expected["canonical"] or len(jobs) != expected["jobs"]:
            raise AssertionError("n=16 worklist reference mismatch")
        if totals["a_space"] != expected["a_space"]:
            raise AssertionError(f"n=16 A-space mismatch: {totals['a_space']}")
        if totals["prefilter_survivors"] != expected["prefilter_survivors"]:
            raise AssertionError(
                "n=16 survivor mismatch: "
                f"{totals['prefilter_survivors']}"
            )
        if any(record["verdict"] != "UNSAT" for record in records):
            raise AssertionError("n=16 C1 certificate contains SAT")
        print("N16_C1_REFERENCE_OK")

    if args.tsv_out:
        write_tsv(args.tsv_out, records)
        print(f"TSV_WRITTEN {args.tsv_out}")
    print(
        "RECORD_AUDIT_OK",
        f"records={len(records)}",
        *(f"{key}={value}" for key, value in totals.items()),
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--target", type=int, required=True)
    parser.add_argument("--records", type=pathlib.Path, required=True)
    parser.add_argument("--allow-partial", action="store_true")
    parser.add_argument("--expect-n16-c1", action="store_true")
    parser.add_argument("--tsv-out", type=pathlib.Path)
    args = parser.parse_args()
    audit(args)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:  # audit failures should be prominent in logs
        print(f"AUDIT_ERROR: {exc}", file=sys.stderr)
        raise
