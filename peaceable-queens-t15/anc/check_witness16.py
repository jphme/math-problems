"""Independent re-check of the 32+32 lower-bound witness for the 16x16 torus.

Checks, from scratch (no shared code with the solvers or the audit script):
  1. the black line sets R=C={5,7,9,11,13,15}, D=A={0,2,...,14} give exactly
     36 black-homogeneous and 32 white-homogeneous cells;
  2. direct pairwise queen check over ALL 36x32 black/white-homogeneous cell
     pairs (a fortiori over any 32+32 placement drawn from them): no pair
     shares a row, column, wraparound diagonal, or wraparound antidiagonal.
"""
N = 16
R = C = {5, 7, 9, 11, 13, 15}
D = A = {0, 2, 4, 6, 8, 10, 12, 14}

bh = {(r, c) for r in range(N) for c in range(N)
      if r in R and c in C and (r - c) % N in D and (r + c) % N in A}
wh = {(r, c) for r in range(N) for c in range(N)
      if r not in R and c not in C and (r - c) % N not in D and (r + c) % N not in A}

assert len(bh) == 36, len(bh)
assert len(wh) == 32, len(wh)

for (r1, c1) in bh:
    for (r2, c2) in wh:
        assert r1 != r2 and c1 != c2
        assert (r1 - c1) % N != (r2 - c2) % N
        assert (r1 + c1) % N != (r2 + c2) % N

print("WITNESS16_OK: B=36 W=32, no black-white attack across all "
      f"{len(bh) * len(wh)} pairs; any 32 of the 36 black cells give a 32+32 placement")
