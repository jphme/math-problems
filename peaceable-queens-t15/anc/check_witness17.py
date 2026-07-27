#!/usr/bin/env python3
"""Directly verify the displayed 28+28 line-set witness at n=17."""

N = 17
R = {0, 1, 2, 4, 5, 7, 8, 9}
C = {0, 1, 2, 4, 5, 7, 8, 9, 13}
D = {2, 3, 4, 7, 10, 13, 14, 15}
A = {2, 5, 6, 7, 9, 11, 12, 13, 16}


def main() -> None:
    black = []
    white = []
    for r in range(N):
        for c in range(N):
            membership = (r in R, c in C, (r - c) % N in D, (r + c) % N in A)
            if all(membership):
                black.append((r, c))
            elif not any(membership):
                white.append((r, c))
    assert len(black) == len(white) == 28
    for r, c in black:
        for u, v in white:
            assert r != u and c != v
            assert (r - c) % N != (u - v) % N
            assert (r + c) % N != (u + v) % N
    print("WITNESS17_OK black=28 white=28 pairs=784")


if __name__ == "__main__":
    main()
