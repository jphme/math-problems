"""Independent re-check of the 20+20 lower-bound witness in PEACE15_PROOF.md.

Checks, from scratch (no shared code with solver or audit script):
  1. the black line sets give exactly 20 black-homogeneous and 22
     white-homogeneous cells;
  2. the 20 listed black cells are exactly the black-homogeneous set;
  3. the 20 listed white cells are white-homogeneous;
  4. direct pairwise queen check: no black-white pair shares a row, column,
     wraparound diagonal, or wraparound antidiagonal.
"""
N = 15
R = {5, 7, 8, 11, 12, 14}
C = {0, 3, 4, 7, 9, 10, 12, 13}
D = {0, 1, 4, 8, 12, 13, 14}
A = {1, 2, 3, 9, 10, 12, 14}

black_listed = [(5,4),(5,7),(5,12),(7,3),(7,7),(7,9),(7,10),(8,4),(8,9),(8,10),
                (11,3),(11,7),(11,13),(12,0),(12,4),(12,12),(12,13),(14,0),(14,10),(14,13)]
white_listed = [(0,5),(0,6),(0,8),(1,5),(1,6),(1,14),(2,6),(2,11),(3,1),(3,8),
                (4,1),(4,2),(6,1),(6,14),(9,2),(9,6),(9,14),(10,1),(10,5),(13,2)]

bh = {(r,c) for r in range(N) for c in range(N)
      if r in R and c in C and (r-c) % N in D and (r+c) % N in A}
wh = {(r,c) for r in range(N) for c in range(N)
      if r not in R and c not in C and (r-c) % N not in D and (r+c) % N not in A}

assert len(bh) == 20, len(bh)
assert len(wh) == 22, len(wh)
assert set(black_listed) == bh
assert set(white_listed) <= wh and len(set(white_listed)) == 20

for (r1,c1) in black_listed:
    for (r2,c2) in white_listed:
        assert r1 != r2 and c1 != c2
        assert (r1-c1) % N != (r2-c2) % N
        assert (r1+c1) % N != (r2+c2) % N

print("WITNESS_OK: B=20 W=22, listed armies exact, no black-white attack (400 pairs)")
