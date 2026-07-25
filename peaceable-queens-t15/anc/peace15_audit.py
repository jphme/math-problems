#!/usr/bin/env python3
"""Independent audit of the peaceable-queens exhaustive run.

This script does not repeat the 6.07-billion-case completion sweep. It
independently regenerates the profile worklist, verifies every recorded orbit
count by Burnside's lemma, checks the row totals, and verifies the 20+20 lower
bound witness. Re-run peace15_solver.cpp for the exhaustive completion step.
"""
from __future__ import annotations

import csv
import hashlib
import itertools
import math
from collections import Counter
from pathlib import Path

N = 15
TARGET = 21
UNITS = (1, 2, 4, 7, 8, 11, 13, 14)
D4 = (
    (0, 1, 2, 3), (0, 1, 3, 2), (1, 0, 2, 3), (1, 0, 3, 2),
    (2, 3, 0, 1), (2, 3, 1, 0), (3, 2, 0, 1), (3, 2, 1, 0),
)


def triple_total(x: int, y: int, z: int) -> int:
    return 225 - 15 * (x + y + z) + x * y + x * z + y * z


def valid_profile(s: tuple[int, int, int, int]) -> bool:
    if sum(s) > 30:
        return False
    for i in range(4):
        for j in range(i + 1, 4):
            if s[i] * s[j] < TARGET:
                return False
            if (15 - s[i]) * (15 - s[j]) < TARGET:
                return False
    for omitted in range(4):
        t = [s[i] for i in range(4) if i != omitted]
        if triple_total(*t) < 2 * TARGET:
            return False
    return True


def canonical_profile(s: tuple[int, int, int, int]) -> tuple[int, int, int, int]:
    orbit = [tuple(s[i] for i in p) for p in D4]
    if sum(s) == 30:
        comp = tuple(15 - x for x in s)
        orbit += [tuple(comp[i] for i in p) for p in D4]
    return min(orbit)


def regenerate_profiles() -> set[tuple[int, int, int, int]]:
    return {
        canonical_profile(s)
        for s in itertools.product(range(16), repeat=4)
        if valid_profile(s)
    }


def affine_cycles(a: int, b: int) -> list[int]:
    perm = [(a * x + b) % N for x in range(N)]
    seen = [False] * N
    lengths: list[int] = []
    for x in range(N):
        if seen[x]:
            continue
        y, length = x, 0
        while not seen[y]:
            seen[y] = True
            length += 1
            y = perm[y]
        lengths.append(length)
    return lengths


def invariant_subsets(k: int, a: int, b: int) -> int:
    coeff = [0] * (N + 1)
    coeff[0] = 1
    for length in affine_cycles(a, b):
        for j in range(N - length, -1, -1):
            coeff[j + length] += coeff[j]
    return coeff[k]


INV = {
    (k, a, b): invariant_subsets(k, a, b)
    for k in range(16)
    for a in UNITS
    for b in range(N)
}


def burnside_pair_orbits(r: int, c: int, relative_sign: bool) -> int:
    epsilons = (1, -1) if relative_sign else (1,)
    direct_sum = 0
    swap_sum = 0
    for u in UNITS:
        for eps in epsilons:
            v = (eps * u) % N
            for alpha in range(N):
                fixed_r = INV[(r, u, alpha)]
                for beta in range(N):
                    direct_sum += fixed_r * INV[(c, v, beta)]
                    if r == c:
                        # For the swap coset: R = g(C), C = f(R), so R is
                        # invariant under g∘f(x)=v(ux+alpha)+beta.
                        aa = (v * u) % N
                        bb = (v * alpha + beta) % N
                        swap_sum += invariant_subsets(r, aa, bb)
    group_order = N * N * len(UNITS) * len(epsilons) * (2 if r == c else 1)
    numerator = direct_sum + swap_sum
    assert numerator % group_order == 0
    return numerator // group_order


def read_certificate(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as f:
        rows = [line for line in f if not line.startswith("#")]
    return list(csv.DictReader(rows, delimiter="\t"))


def cells_for_lines(R: set[int], C: set[int], D: set[int], A: set[int]):
    black, white = [], []
    for r in range(N):
        for c in range(N):
            d, a = (r - c) % N, (r + c) % N
            if r in R and c in C and d in D and a in A:
                black.append((r, c))
            if r not in R and c not in C and d not in D and a not in A:
                white.append((r, c))
    return black, white


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def main() -> None:
    root = Path(__file__).resolve().parent
    cert_path = root / "peace15_certificate.tsv"
    source_path = root / "peace15_solver.cpp"
    rows = read_certificate(cert_path)
    assert len(rows) == 247
    assert all(row["result"] == "UNSAT" for row in rows)

    generated = regenerate_profiles()
    recorded = {
        tuple(map(int, row["profile"].split(",")))
        for row in rows
    }
    assert generated == recorded
    assert Counter(map(sum, generated)) == {
        20: 1, 21: 1, 22: 4, 23: 6, 24: 13, 25: 18,
        26: 29, 27: 37, 28: 47, 29: 52, 30: 39,
    }

    checked_total = 0
    orbit_keys: dict[tuple[int, int, bool], int] = {}
    for row in rows:
        r, c = int(row["r"]), int(row["c"])
        sign = bool(int(row["relative_sign"]))
        orbit_count = int(row["pair_orbits"])
        a = int(row["a"])
        checked = int(row["A_checked"])
        assert checked == orbit_count * math.comb(N, a)
        checked_total += checked
        key = (r, c, sign)
        if key in orbit_keys:
            assert orbit_keys[key] == orbit_count
        orbit_keys[key] = orbit_count

    assert checked_total == 6_074_753_568
    for (r, c, sign), recorded_count in orbit_keys.items():
        assert burnside_pair_orbits(r, c, sign) == recorded_count

    R = {5, 7, 8, 11, 12, 14}
    C = {0, 3, 4, 7, 9, 10, 12, 13}
    D = {0, 1, 4, 8, 12, 13, 14}
    A = {1, 2, 3, 9, 10, 12, 14}
    black, white = cells_for_lines(R, C, D, A)
    assert len(black) == 20 and len(white) == 22

    print("AUDIT_OK")
    print(f"profiles={len(rows)}")
    print(f"orbit_keys_burnside_checked={len(orbit_keys)}")
    print(f"A_checked={checked_total}")
    print(f"lower_bound_cells=black:{len(black)},white:{len(white)}")
    print(f"solver_sha256={sha256(source_path)}")
    print(f"certificate_sha256={sha256(cert_path)}")


if __name__ == "__main__":
    main()
