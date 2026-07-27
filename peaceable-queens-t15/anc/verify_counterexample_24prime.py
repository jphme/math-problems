#!/usr/bin/env python3
"""Integer-only verification that the proposed local envelope (24') is false.

The right side is enlarged beyond the proposed 288 profiles: all 4-tuples
whose coordinates are chosen from the eight local counts and all eight
complements are checked (16^4 tuples).  Even this larger envelope is too small.
"""
from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path

PATH = Path(sys.argv[1] if len(sys.argv) > 1 else "/mnt/data/counterexample_24prime.json")
data = json.loads(PATH.read_text())
q = int(data["q"])
z = {k: int(v) for k, v in data["local_coordinates"].items()}
u, R, v, C, g, e, h, f = (z[k] for k in ("u", "R", "v", "C", "g", "e", "h", "f"))

# Rational plaid box N, canonical chamber, and line budget.
assert 0 <= u <= q // 10 and 0 <= v <= q // 10
assert 0 <= e <= q // 10 and 0 <= f <= q // 10
assert 0 <= g <= q // 20 and 0 <= h <= q // 20
assert 5 * R >= 3 * q and 8 * R <= 7 * q
assert 5 * C >= 3 * q and 8 * C <= 7 * q
assert u + R <= v + C
assert e + h <= f + g                 # d0+d1 <= a0+a1
assert u + v + R + C + e + f - g - h <= 2 * q

X = u * v + R * C
Y = (q - u) * (q - C) + (q - R) * (q - v)
alpha = 2 * q - R - C - u - v
beta = R + C - q
Q = 2 * e * f + 2 * g * h
FB1 = X - beta * (g + h) + 2 * g * h + e * (u + v)
FB2 = X - beta * (g + h) + Q
FW = Y - alpha * (e + f) + Q
T = min(FB1, FB2, FW)
threshold = 527 * q * q // 1000
assert 1000 * T > 527 * q * q

pool = []
for name in ("u", "R", "v", "C", "g", "e", "h", "f"):
    value = z[name]
    pool.append((name, value))
    pool.append((f"q-{name}", q - value))

best = -1
best_data = None
for a, b, c, d in itertools.product(pool, repeat=4):
    black = a[1] * d[1] + b[1] * c[1]
    white = (q - a[1]) * (q - c[1]) + (q - b[1]) * (q - d[1])
    value = min(black, white)
    if value > best:
        best = value
        best_data = ([a[0], b[0], c[0], d[0]], [black, white])

claimed = data["claimed_values"]
assert FB1 == claimed["F_B1"]
assert FB2 == claimed["F_B2"]
assert FW == claimed["F_W"]
assert T == claimed["cut_minimum"]
assert threshold == claimed["threshold_527_over_1000"]
assert best == claimed["best_value_over_all_16_power_4_literal_profiles"]
assert best_data[0] == claimed["best_profile"]
assert best_data[1] == claimed["best_profile_capacities"]
assert T - best == claimed["violation_margin"] > 0

print("q", q)
print("cuts", FB1, FB2, FW, "minimum", T)
print("527/1000 threshold", threshold)
print("best enlarged literal profile", best_data[0], best_data[1], "value", best)
print("violation margin", T - best)
print("COUNTEREXAMPLE_24PRIME_OK")
