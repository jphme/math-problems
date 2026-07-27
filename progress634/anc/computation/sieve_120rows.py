#!/usr/bin/env python3
"""Arithmetic sieve for the five non-equilateral 120-degree rows of the
triangle-tiling classification (Erdos Problem 634 investigation).

For each N <= NMAX, find all arithmetic candidates (a,b,c,k) in each row:

  Tile: primitive (a,b,c), c^2 = a^2+ab+b^2, gcd(a,b)=1  (Eisenstein triple)
  U = a+2b, V = 2a+b, W = a+b, Delta = a+c-b.

  Row I   (ABC isosceles (alpha,alpha,pi-2alpha)):  N*b = k^2*U  (U | N)
  Row II  (alpha,2alpha,3beta):                     N = 3*k^2*U*W
  Row III (alpha,2beta,2alpha+beta):                N = k^2*V*W
  Row IV  (alpha,alpha+beta,alpha+2beta):           N*b = k^2*W  (W | N)
  Row V   (2alpha,2beta,alpha+beta):                N = k^2*U*V

Additionally applies the Phi-invariant filter to Row I:
  k*(U-2c) = M*Delta  with  M in Z, |M| <= N, M == N (mod 2).

Also flags N realizable by classical families:
  squares, sums of two squares, 2n^2, 3n^2, 6n^2.

Necessity-only: a surviving candidate is NOT a tiling, just not yet excluded.
"""

import sys
from math import gcd, isqrt

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200


def is_square(n: int) -> bool:
    if n < 0:
        return False
    r = isqrt(n)
    return r * r == n


def eisenstein_c(a: int, b: int):
    c2 = a * a + a * b + b * b
    r = isqrt(c2)
    return r if r * r == c2 else None


def divisors(n: int):
    ds = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            ds.append(d)
            if d != n // d:
                ds.append(n // d)
    return sorted(ds)


def square_divisor_roots(n: int):
    """all k >= 1 with k^2 | n"""
    return [k for k in range(1, isqrt(n) + 1) if n % (k * k) == 0]


def row_I(N):
    out = []
    for U in divisors(N):
        if U < 3:
            continue
        for b in range(1, (U - 1) // 2 + 1):
            a = U - 2 * b
            if a <= 0 or gcd(a, b) != 1:
                continue
            k2, rem = divmod(N * b, U)
            if rem or not is_square(k2):
                continue
            c = eisenstein_c(a, b)
            if c is None:
                continue
            out.append((a, b, c, isqrt(k2)))
    return out


def row_IV(N):
    out = []
    for W in divisors(N):
        if W < 2:
            continue
        for b in range(1, W):
            a = W - b
            if a <= 0 or gcd(a, b) != 1:
                continue
            k2, rem = divmod(N * b, W)
            if rem or not is_square(k2):
                continue
            c = eisenstein_c(a, b)
            if c is None:
                continue
            out.append((a, b, c, isqrt(k2)))
    return out


def row_II(N):
    out = []
    if N % 3:
        return out
    M = N // 3
    for k in square_divisor_roots(M):
        UW = M // (k * k)
        for W in divisors(UW):
            U = UW // W
            if U <= W:  # U - W = b > 0
                continue
            b = U - W
            a = 2 * W - U
            if a <= 0 or gcd(a, b) != 1:
                continue
            c = eisenstein_c(a, b)
            if c is None:
                continue
            out.append((a, b, c, k))
    return out


def row_III(N):
    out = []
    for k in square_divisor_roots(N):
        VW = N // (k * k)
        for W in divisors(VW):
            V = VW // W
            if not (W < V < 2 * W):  # V-W=a>0, 2W-V=b>0
                continue
            a = V - W
            b = 2 * W - V
            if gcd(a, b) != 1:
                continue
            c = eisenstein_c(a, b)
            if c is None:
                continue
            out.append((a, b, c, k))
    return out


def row_E(N):
    """Equilateral ABC, 120-degree tile (a,b,c): N = L^2/(ab), L integer side.

    Pure area+boundary-integrality arithmetic only; Beeson's equilateral
    papers (1812.07014, 1811.09723 Lemma 14/Table 5) impose further
    conditions not encoded here.  Tags Zhang-threshold realizability:
    N = n^2*ab achievable if n >= 3*ceil((a^2+ab+b^2-a-b)/(ab)).

    CAVEAT: unlike rows I-V there is no divisor condition bounding (a,b)
    for fixed N; only the ratio a/b is bounded (a^2+ab+b^2 <= N*ab).  The
    enumeration window below is heuristic, NOT provably exhaustive.
    """
    out = []
    # L^2 = N*ab; enumerate tile (a,b) with ab | L^2 via a,b up to bound
    for a in range(1, 4 * isqrt(N) + 2):
        for b in range(1, a + 1):
            if gcd(a, b) != 1:
                continue
            c = eisenstein_c(a, b)
            if c is None:
                continue
            if not is_square(N * a * b):
                continue
            L = isqrt(N * a * b)
            # Zhang realizability: N = n^2 * ab with n above threshold?
            n2, rem = divmod(N, a * b)
            zhang = ""
            if rem == 0 and is_square(n2):
                n = isqrt(n2)
                thr = 3 * (-((-(a * a + a * b + b * b - a - b)) // (a * b)))
                zhang = " ZHANG-REALIZED" if n >= thr else f" (Zhang form n={n} < threshold {thr})"
            out.append((a, b, c, L, zhang))
    return out


def row_V(N):
    out = []
    for k in square_divisor_roots(N):
        UV = N // (k * k)
        for U in divisors(UV):
            V = UV // U
            if (2 * V - U) <= 0 or (2 * U - V) <= 0:
                continue
            if (2 * V - U) % 3 or (2 * U - V) % 3:
                continue
            a = (2 * V - U) // 3
            b = (2 * U - V) // 3
            if gcd(a, b) != 1:
                continue
            c = eisenstein_c(a, b)
            if c is None:
                continue
            out.append((a, b, c, k))
    return out


def phi_filter_row_I(N, cand):
    """Return (M, verdict) for the Phi boundary equation k(U-2c) = M*Delta."""
    a, b, c, k = cand
    U, Delta = a + 2 * b, a + c - b
    num = k * (U - 2 * c)
    if num % Delta:
        return None, "impossible (M not integral)"
    M = num // Delta
    if abs(M) > N:
        return M, "impossible (|M| > N)"
    if (M - N) % 2:
        return M, "impossible (wrong parity)"
    return M, "survives"


def classical(N):
    tags = []
    if is_square(N):
        tags.append("n^2")
    if any(is_square(N - i * i) for i in range(1, isqrt(N) + 1)):
        tags.append("e^2+f^2")
    for m, tag in ((2, "2n^2"), (3, "3n^2"), (6, "6n^2")):
        if N % m == 0 and is_square(N // m):
            tags.append(tag)
    return tags


def main():
    rows = {"I": row_I, "II": row_II, "III": row_III, "IV": row_IV, "V": row_V}
    print("Equilateral-row (row E) arithmetic candidates, N <= %d," % NMAX)
    print("restricted to N NOT in classical families {n^2,e^2+f^2,2n^2,3n^2,6n^2}:")
    for N in range(2, NMAX + 1):
        if classical(N):
            continue
        cands = row_E(N)
        if cands:
            for a, b, c, L, zhang in cands:
                print(f"  N = {N}: tile ({a},{b},{c}), equilateral side L={L}{zhang}")
    print()
    print(f"Arithmetic survivors in 120-degree rows, N <= {NMAX}")
    print("=" * 78)
    open_candidates = []
    for N in range(2, NMAX + 1):
        found = {name: fn(N) for name, fn in rows.items()}
        if not any(found.values()):
            continue
        tags = classical(N)
        lines = []
        row_I_alive = False
        for name in rows:
            for cand in found[name]:
                a, b, c, k = cand
                extra = ""
                if name == "I":
                    M, verdict = phi_filter_row_I(N, cand)
                    extra = f"  Phi: M={M} -> {verdict}"
                    if verdict == "survives":
                        row_I_alive = True
                lines.append(
                    f"    row {name:>3}: (a,b,c)=({a},{b},{c}), k={k}{extra}"
                )
        status = f"[classical: {','.join(tags)}]" if tags else ""
        if not tags and (row_I_alive or any(found[r] for r in "II III V IV".split())):
            status += " [NOT in classical families]"
            open_candidates.append((N, found, row_I_alive))
        print(f"N = {N} {status}")
        print("\n".join(lines))
    print("=" * 78)
    print("\nSummary: N <= %d with 120-row arithmetic candidates but NOT in" % NMAX)
    print("classical families {n^2, e^2+f^2, 2n^2, 3n^2, 6n^2}:")
    for N, found, row_I_alive in open_candidates:
        rows_hit = [r for r in rows if found[r]]
        note = " (row I survives Phi)" if row_I_alive else ""
        print(f"  N = {N}: rows {','.join(rows_hit)}{note}")


if __name__ == "__main__":
    main()
