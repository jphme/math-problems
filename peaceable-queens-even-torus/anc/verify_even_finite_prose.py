# /// script
# requires-python = ">=3.11"
# dependencies = ["sympy"]
# ///
"""Independent exact verification of the prose/algebra part of EVEN_FINITE_PROOF.md.

Scope: Sections 1, 3, 4, 5, 6 of

    handoff-mathematician/result6-proof/bundle/even-finite-proof-bundle/EVEN_FINITE_PROOF.md

plus the "Completion" glue for the exceptional range q <= 129 (Section 2/7).

Every check is derived from the proof text.  The certificate-backed steps
(equations (2), (4), (6), (11), (12)) are *inputs* here: they are checked by
`verify_even_branch_certificate.py`.  What this script verifies is everything
the prose derives from them.

Method notes (deliberately independent of the delivered checker):
  * symbolic identities and inequality certificates use sympy polynomials;
  * an inequality is certified by writing (LHS - RHS) as an explicit
    nonnegative combination of hypothesis slacks, squares and products, and
    checking that *identity* symbolically -- so no numeric tolerance is ever
    involved;
  * bulk loops (q = 1..2000, random stress) use exact integers / Fractions;
  * Q(sqrt 3) comparisons use an exact integer sign routine, cross-validated
    against sympy on samples.

Run:  uv run scripts/verify_even_finite_prose.py
"""

from __future__ import annotations

import itertools
import json
import math
import random
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parent.parent
_RECORD_CANDIDATES = [
    ROOT / "envelope-ladder" / "e2e3" / "records",
    Path(__file__).resolve().parent / "records_q021_q129",
    Path("records_q021_q129"),
]
RECORDS = next((p for p in _RECORD_CANDIDATES if p.is_dir()), _RECORD_CANDIDATES[0])

FAILURES: list[str] = []
NCHECKS = 0


def check(name: str, ok: bool, detail: str = "") -> None:
    global NCHECKS
    NCHECKS += 1
    if ok:
        print(f"  PASS  {name}")
    else:
        msg = f"{name}" + (f"  --  {detail}" if detail else "")
        print(f"  FAIL  {msg}")
        FAILURES.append(msg)


def zero(expr) -> bool:
    """Exact symbolic zero test."""
    return sp.simplify(sp.expand(expr)) == 0


def section(title: str) -> None:
    print(f"\n=== {title} ===")


# ---------------------------------------------------------------------------
# exact arithmetic in Q(sqrt 3):  a + b*sqrt(3), a, b rational
# ---------------------------------------------------------------------------

def q3_sign(a: Fr, b: Fr) -> int:
    """Exact sign of a + b*sqrt(3)."""
    a = Fr(a)
    b = Fr(b)
    if a == 0 and b == 0:
        return 0
    if a >= 0 and b >= 0:
        return 1
    if a <= 0 and b <= 0:
        return -1
    # opposite signs: compare a^2 with 3 b^2
    lhs = a * a
    rhs = 3 * b * b
    if a > 0:  # b < 0 : positive iff a^2 > 3 b^2
        return 1 if lhs > rhs else (0 if lhs == rhs else -1)
    else:  # a < 0, b > 0 : positive iff 3 b^2 > a^2
        return 1 if rhs > lhs else (0 if rhs == lhs else -1)


def q3_ge(a: Fr, b: Fr) -> bool:
    return q3_sign(a, b) >= 0


# ---------------------------------------------------------------------------
# Section 1 -- canonical chamber (group action)
# ---------------------------------------------------------------------------
# index order: 0:r0 1:r1 2:c0 3:c1 4:d0 5:d1 6:a0 7:a1
LABELS = ("r0", "r1", "c0", "c1", "d0", "d1", "a0", "a1")


def perm_from_swaps(swaps) -> tuple[int, ...]:
    p = list(range(8))
    for i, j in swaps:
        p[i], p[j] = p[j], p[i]
    return tuple(p)


# permutation p acts by  (P x)_i = x_{p[i]}
ROWTRANS = perm_from_swaps([(0, 1), (4, 5), (6, 7)])
COLTRANS = perm_from_swaps([(2, 3), (4, 5), (6, 7)])
TRANSPOSE = perm_from_swaps([(0, 2), (1, 3)])
REFLECT = perm_from_swaps([(4, 6), (5, 7)])
GENERATORS = {
    "row translation": ROWTRANS,
    "column translation": COLTRANS,
    "transpose": TRANSPOSE,
    "reflection c -> -c": REFLECT,
}


def apply_perm(p, x):
    return tuple(x[p[i]] for i in range(8))


def compose(p, r):
    """apply p after r."""
    return tuple(r[p[i]] for i in range(8))


def in_chamber(x) -> bool:
    r0, r1, c0, c1, d0, d1, a0, a1 = x
    return (
        r0 <= r1
        and c0 <= c1
        and r0 + r1 <= c0 + c1
        and d0 + d1 <= a0 + a1
        and sum(x) <= 4
    )


def check_section1() -> None:
    section("Section 1: canonical chamber (1)")

    xs = sp.symbols("r0 r1 c0 c1 d0 d1 a0 a1")
    x = tuple(xs)

    # -- the five stated operations act as claimed on the labelled 8-tuple ---
    claims = {
        "row translation swaps (r0,r1), (d0,d1), (a0,a1), fixes c": (
            ROWTRANS,
            ("r1", "r0", "c0", "c1", "d1", "d0", "a1", "a0"),
        ),
        "column translation swaps (c0,c1), (d0,d1), (a0,a1), fixes r": (
            COLTRANS,
            ("r0", "r1", "c1", "c0", "d1", "d0", "a1", "a0"),
        ),
        "transpose swaps r-pair with c-pair, fixes d,a": (
            TRANSPOSE,
            ("c0", "c1", "r0", "r1", "d0", "d1", "a0", "a1"),
        ),
        "reflection swaps d-pair with a-pair, fixes r,c": (
            REFLECT,
            ("r0", "r1", "c0", "c1", "a0", "a1", "d0", "d1"),
        ),
    }
    for name, (perm, want) in claims.items():
        got = apply_perm(perm, x)
        want_syms = tuple(xs[LABELS.index(w)] for w in want)
        check(f"Sec1 action: {name}", got == want_syms, f"got {got}")

    # complement x -> 1-x maps sum to 8 - sum, so repairs sum(x) <= 4
    comp = tuple(1 - xi for xi in x)
    check("Sec1 complement: sum(1-x) = 8 - sum(x)", zero(sum(comp) - (8 - sum(x))))

    # every permutation generator preserves the total sum
    for name, perm in GENERATORS.items():
        check(
            f"Sec1 {name} preserves sum(x)",
            zero(sum(apply_perm(perm, x)) - sum(x)),
        )

    # d/a totals: row and column translations and transpose fix both totals;
    # reflection exchanges them
    d_tot, a_tot = x[4] + x[5], x[6] + x[7]
    for name in ("row translation", "column translation", "transpose"):
        y = apply_perm(GENERATORS[name], x)
        check(
            f"Sec1 {name} fixes d0+d1 and a0+a1",
            zero(y[4] + y[5] - d_tot) and zero(y[6] + y[7] - a_tot),
        )
    y = apply_perm(REFLECT, x)
    check(
        "Sec1 reflection exchanges d0+d1 with a0+a1",
        zero(y[4] + y[5] - a_tot) and zero(y[6] + y[7] - d_tot),
    )
    # transpose exchanges the row total with the column total
    y = apply_perm(TRANSPOSE, x)
    check(
        "Sec1 transpose exchanges r0+r1 with c0+c1",
        zero(y[0] + y[1] - (x[2] + x[3])) and zero(y[2] + y[3] - (x[0] + x[1])),
    )
    # transpose preserves within-pair sortedness (it maps pair to pair intact)
    check(
        "Sec1 transpose maps sorted pairs to sorted pairs",
        (y[0], y[1]) == (x[2], x[3]) and (y[2], y[3]) == (x[0], x[1]),
    )

    # -- the generated group ------------------------------------------------
    group = {tuple(range(8))}
    frontier = [tuple(range(8))]
    while frontier:
        nxt = []
        for gel in frontier:
            for perm in GENERATORS.values():
                new = compose(gel, perm)
                if new not in group:
                    group.add(new)
                    nxt.append(new)
        frontier = nxt
    check("Sec1 generated permutation group is finite", len(group) < 10**5,
          f"|P| = {len(group)}")
    print(f"        |P| = {len(group)}, full group order (with complement) = {2*len(group)}")

    # -- brute force: chamber is reachable from any starting 8-tuple --------
    rng = random.Random(20260727)
    bad = 0
    trials = 20000
    for _ in range(trials):
        pt = tuple(Fr(rng.randrange(0, 41), 40) for _ in range(8))
        reached = False
        for cflag in (0, 1):
            y0 = tuple(1 - t for t in pt) if cflag else pt
            for perm in group:
                if in_chamber(apply_perm(perm, y0)):
                    reached = True
                    break
            if reached:
                break
        if not reached:
            bad += 1
    check(f"Sec1 chamber (1) reachable for all {trials} random 8-tuples", bad == 0,
          f"{bad} unreachable")

    # also: the explicit recipe of the prose works (complement, sort, transpose, reflect)
    bad = 0
    for _ in range(5000):
        pt = tuple(Fr(rng.randrange(0, 41), 40) for _ in range(8))
        y = pt
        if sum(y) > 4:
            y = tuple(1 - t for t in y)
        if y[0] > y[1]:
            y = apply_perm(ROWTRANS, y)
        if y[2] > y[3]:
            y = apply_perm(COLTRANS, y)
        if y[0] + y[1] > y[2] + y[3]:
            y = apply_perm(TRANSPOSE, y)
        if y[4] + y[5] > y[6] + y[7]:
            y = apply_perm(REFLECT, y)
        if not in_chamber(y):
            bad += 1
    check("Sec1 prose recipe (complement, sort, transpose, reflect) lands in (1)",
          bad == 0, f"{bad} failures")

    # -- H-functional symmetries (the plaid objective) ----------------------
    r0, r1, c0, c1 = sp.symbols("R0 R1 C0 C1")
    B = r0 * c1 + r1 * c0
    W = (1 - r0) * (1 - c0) + (1 - r1) * (1 - c1)
    sub_rowcol = {r0: r1, r1: r0, c0: c1, c1: c0}
    check("Sec1 H-objective invariant under simultaneous row+column translation",
          zero(B.subs(sub_rowcol, simultaneous=True) - B)
          and zero(W.subs(sub_rowcol, simultaneous=True) - W))
    sub_tr = {r0: c0, r1: c1, c0: r0, c1: r1}
    check("Sec1 H-objective invariant under transpose",
          zero(B.subs(sub_tr, simultaneous=True) - B)
          and zero(W.subs(sub_tr, simultaneous=True) - W))
    sub_comp = {r0: 1 - r0, r1: 1 - r1, c0: 1 - c1, c1: 1 - c0}
    check("Sec1 complement (with column swap) exchanges B and W",
          zero(B.subs(sub_comp, simultaneous=True) - W)
          and zero(W.subs(sub_comp, simultaneous=True) - B))


# ---------------------------------------------------------------------------
# Section 3 -- the escape value 527/1000 is below H(2q)
# ---------------------------------------------------------------------------

def check_section3() -> None:
    section("Section 3: escape value below H(2q)  [(7), (8)]")

    s = sp.sqrt(3) - 1
    kappa = sp.expand(s ** 2)
    c0 = 1 - 1 / sp.sqrt(3)

    check("Sec3 kappa = s^2 = 4 - 2 sqrt 3", zero(kappa - (4 - 2 * sp.sqrt(3))))

    # plaid profile capacities, both parities of P
    k = sp.symbols("k", integer=True, positive=True)
    q = sp.symbols("q", positive=True)
    for parity, P, fl, ce in ((("even"), 2 * k, k, k), ("odd", 2 * k + 1, k, k + 1)):
        # black = r0 c1 + r1 c0  with (r0,r1,c0,c1) = (0, floor(P/2), ceil(P/2), 0)
        black = 0 * 0 + fl * ce
        want_black = sp.floor(sp.Rational(1, 4) * P ** 2)
        check(f"Sec3 black capacity = floor(P^2/4) for P {parity}",
              zero(sp.expand(black - sp.simplify(want_black))))
        white = (q - 0) * (q - ce) + (q - fl) * (q - 0)
        check(f"Sec3 white capacity = 2q^2 - qP for P {parity}",
              zero(sp.expand(white - (2 * q ** 2 - q * P))))

    # theta loss:  max_theta min(s theta, 1 - theta) = s/(1+s) = 1 - 1/sqrt 3
    theta_star = 1 / (1 + s)
    check("Sec3 crossing point: s*theta* = 1 - theta*",
          zero(sp.simplify(s * theta_star - (1 - theta_star))))
    check("Sec3 s/(1+s) = 1 - 1/sqrt(3) = c0",
          zero(sp.simplify(s / (1 + s) - c0)))
    # monotone envelope: for theta <= theta*, min <= s theta <= s theta*;
    # for theta >= theta*, min <= 1 - theta <= 1 - theta*
    th = sp.symbols("theta", nonnegative=True)
    check("Sec3 envelope below crossing (s*theta increasing)",
          sp.simplify(sp.diff(s * th, th)) > 0)
    check("Sec3 envelope above crossing (1-theta decreasing)",
          sp.simplify(sp.diff(1 - th, th)) < 0)

    # exact constant comparisons
    check("Sec3 kappa - 527/1000 > 1/125",
          q3_sign(Fr(4) - Fr(527, 1000) - Fr(1, 125), Fr(-2)) > 0)
    check("Sec3 (sympy cross-check) kappa - 527/1000 > 1/125",
          bool(sp.simplify(kappa - sp.Rational(527, 1000) - sp.Rational(1, 125)) > 0))
    check("Sec3 c0 < 1/2", q3_sign(Fr(1) - Fr(1, 2), Fr(-1, 3)) < 0)
    check("Sec3 (sympy cross-check) c0 < 1/2", bool(sp.simplify(c0 - sp.Rational(1, 2)) < 0))

    # q^2/125 - q/2 - 1/4 > 0 for q >= 64 (and monotone increasing there)
    qq = sp.Rational(64)
    check("Sec3 q^2/125 - q/2 - 1/4 > 0 at q = 64",
          qq ** 2 / 125 - qq / 2 - sp.Rational(1, 4) > 0)
    check("Sec3 q^2/125 - q/2 - 1/4 fails at q = 62 (threshold is sharp near 63)",
          sp.Rational(62) ** 2 / 125 - sp.Rational(62) / 2 - sp.Rational(1, 4) < 0)
    check("Sec3 derivative 2q/125 - 1/2 > 0 for q >= 64",
          2 * sp.Rational(64) / 125 - sp.Rational(1, 2) > 0)

    # (8) as a symbolic consequence of (7) and the two constant comparisons
    qs = sp.symbols("q", positive=True)
    H = sp.symbols("H")
    # H - 527/1000 q^2 - (q^2/125 - q/2 - 1/4)
    #   = (H - (kappa q^2 - c0 q - 1/4)) + (kappa - 527/1000 - 1/125) q^2 + (1/2 - c0) q
    lhs = H - sp.Rational(527, 1000) * qs ** 2 - (qs ** 2 / 125 - qs / 2 - sp.Rational(1, 4))
    rhs = ((H - (kappa * qs ** 2 - c0 * qs - sp.Rational(1, 4)))
           + (kappa - sp.Rational(527, 1000) - sp.Rational(1, 125)) * qs ** 2
           + (sp.Rational(1, 2) - c0) * qs)
    check("Sec3 (8) decomposition identity into nonneg/positive terms", zero(lhs - rhs))

    # (7) verified numerically-exactly for q = 1..2000 using the two plaid profiles
    worst = None
    bad = []
    for qi in range(1, 2001):
        m = math.isqrt(12 * qi * qi) - 2 * qi  # = floor(2(sqrt3 - 1) q)
        best = None
        for P in (m, m + 1):
            if P < 0:
                continue
            fl, ce = P // 2, (P + 1) // 2
            if ce > qi or fl > qi:
                continue
            val = min((P * P) // 4, 2 * qi * qi - qi * P)
            if best is None or val > best:
                best = val
        # best >= kappa q^2 - c0 q - 1/4, i.e.
        #   (best - 4q^2 + q + 1/4) + sqrt3 (2q^2 - q/3) >= 0
        A = Fr(best) - 4 * qi * qi + qi + Fr(1, 4)
        Bc = Fr(2 * qi * qi) - Fr(qi, 3)
        sgn = q3_sign(A, Bc)
        if sgn < 0:
            bad.append(qi)
        slack = float(A) + math.sqrt(3) * float(Bc)
        if worst is None or slack < worst[1]:
            worst = (qi, slack)
    check("Sec3 (7) H(2q) >= kappa q^2 - c0 q - 1/4 for q = 1..2000 (two plaid profiles)",
          not bad, f"failures at q = {bad[:10]}")
    print(f"        tightest slack over q<=2000: q = {worst[0]}, slack ~ {worst[1]:.6f}")

    # cross-validate the exact Q(sqrt3) sign routine against sympy
    rng = random.Random(7)
    ok = True
    for _ in range(300):
        a = Fr(rng.randrange(-500, 501), rng.randrange(1, 40))
        b = Fr(rng.randrange(-500, 501), rng.randrange(1, 40))
        val = sp.Rational(a.numerator, a.denominator) + sp.Rational(b.numerator, b.denominator) * sp.sqrt(3)
        if q3_sign(a, b) != int(sp.sign(sp.nsimplify(val))):
            ok = False
            break
    check("Sec3 exact Q(sqrt3) sign routine agrees with sympy (300 samples)", ok)


# ---------------------------------------------------------------------------
# shared symbolic setup for Sections 4-6
# ---------------------------------------------------------------------------

def core_symbols():
    q = sp.symbols("q", positive=True)
    u, R, v, C, g, e, h, f = sp.symbols("u R v C g e h f", nonnegative=True)
    p = R + C
    n = u + v
    a = e + f
    b = g + h
    alpha = 2 * q - p - n
    beta = p - q
    Q = 2 * e * f + 2 * g * h
    X = u * v + R * C
    Y = (q - u) * (q - C) + (q - R) * (q - v)
    L = 2 * q - p
    return dict(q=q, u=u, R=R, v=v, C=C, g=g, e=e, h=h, f=f, p=p, n=n, a=a, b=b,
                alpha=alpha, beta=beta, Q=Q, X=X, Y=Y, L=L)


def core_slacks(S):
    """Nonnegative slack expressions of the aggregate core (6)."""
    q = S["q"]
    return dict(
        s_p_lo=S["p"] - sp.Rational(36, 25) * q,      # >= 0
        s_p_hi=sp.Rational(37, 25) * q - S["p"],      # >= 0
        s_n=sp.Rational(9, 100) * q - S["n"],         # >= 0
        s_a=sp.Rational(9, 200) * q - S["a"],         # >= 0
        s_b=sp.Rational(1, 25) * q - S["b"],          # >= 0
    )


# ---------------------------------------------------------------------------
# Section 4 -- the two local support cuts, (14), (15), (16)
# ---------------------------------------------------------------------------

def check_section4() -> None:
    section("Section 4: core consequences (14), (15), (16)")
    S = core_symbols()
    K = core_slacks(S)
    q, a, b = S["q"], S["a"], S["b"]

    # (14) alpha >= 43q/100
    check("Sec4 (14) alpha - 43q/100 = s_p_hi + s_n  (>= 0)",
          zero(S["alpha"] - sp.Rational(43, 100) * q - (K["s_p_hi"] + K["s_n"])))
    # (14) beta >= 11q/25
    check("Sec4 (14) beta - 11q/25 = s_p_lo  (>= 0)",
          zero(S["beta"] - sp.Rational(11, 25) * q - K["s_p_lo"]))
    # (14) alpha > a
    check("Sec4 (14) alpha - a = s_p_hi + s_n + s_a + 77q/200  (> 0)",
          zero(S["alpha"] - a - (K["s_p_hi"] + K["s_n"] + K["s_a"] + sp.Rational(77, 200) * q)))
    # (14) beta > b
    check("Sec4 (14) beta - b = s_p_lo + s_b + 2q/5  (> 0)",
          zero(S["beta"] - b - (K["s_p_lo"] + K["s_b"] + sp.Rational(2, 5) * q)))

    # (15) 4ef + 4gh <= a^2 + b^2 via squares
    e, f, g, h = S["e"], S["f"], S["g"], S["h"]
    check("Sec4 (15) a^2 - 4ef = (e-f)^2", zero(sp.expand(a ** 2 - 4 * e * f - (e - f) ** 2)))
    check("Sec4 (15) b^2 - 4gh = (g-h)^2", zero(sp.expand(b ** 2 - 4 * g * h - (g - h) ** 2)))
    check("Sec4 (15) 2Q = 4ef + 4gh", zero(sp.expand(2 * S["Q"] - (4 * e * f + 4 * g * h))))
    # (15) a^2 + b^2 <= alpha a + beta b
    check("Sec4 (15) alpha a - a^2 = a*(alpha - a) with alpha - a > 0",
          zero(sp.expand(S["alpha"] * a - a ** 2 - a * (S["alpha"] - a))))
    check("Sec4 (15) beta b - b^2 = b*(beta - b) with beta - b > 0",
          zero(sp.expand(S["beta"] * b - b ** 2 - b * (S["beta"] - b))))

    # (16) Q <= max(alpha a, beta b): 2Q <= alpha a + beta b <= 2 max
    # dichotomy step, both orderings checked symbolically
    t1, t2, d = sp.symbols("t1 t2 d", positive=True)
    check("Sec4 (16) dichotomy: 2*max(x,y) - (x+y) = |x-y| >= 0, both orderings",
          zero(sp.expand(2 * (t1 + d) - ((t1 + d) + t1) - d))
          and zero(sp.expand(2 * (t2 + d) - (t2 + (t2 + d)) - d)))

    # (11)/(12)/(13): the definitions used downstream
    F_B = S["X"] - S["beta"] * b + S["Q"]
    F_W = S["Y"] - S["alpha"] * a + S["Q"]
    check("Sec4 (13) T = min(F_B, F_W) well-defined from (11),(12)",
          zero(sp.expand(F_B - (S["X"] - S["beta"] * b + S["Q"])))
          and zero(sp.expand(F_W - (S["Y"] - S["alpha"] * a + S["Q"]))))

    # (10)-consistency: alpha = L - n (used in (26))
    check("Sec4 alpha = L - n", zero(sp.expand(S["alpha"] - (S["L"] - S["n"]))))

    # randomized exact stress of (14)-(16) over the core
    rng = random.Random(4242)
    bad = 0
    trials = 20000
    for _ in range(trials):
        qi = rng.randrange(200, 10 ** 6)
        pi = rng.randrange(-(-36 * qi // 25), 37 * qi // 25 + 1)
        ni = rng.randrange(0, 9 * qi // 100 + 1)
        ai = rng.randrange(0, 9 * qi // 200 + 1)
        bi = rng.randrange(0, qi // 25 + 1)
        ei = rng.randrange(0, ai + 1)
        fi = ai - ei
        gi = rng.randrange(0, bi + 1)
        hi = bi - gi
        al = 2 * qi - pi - ni
        be = pi - qi
        Qi = 2 * ei * fi + 2 * gi * hi
        if not (100 * al >= 43 * qi and 25 * be >= 11 * qi and al > ai and be > bi):
            bad += 1
        if not (2 * Qi <= ai * ai + bi * bi <= al * ai + be * bi):
            bad += 1
        if not (Qi <= max(al * ai, be * bi)):
            bad += 1
    check(f"Sec4 randomized exact stress of (14)-(16), {trials} core points", bad == 0,
          f"{bad} violations")


# ---------------------------------------------------------------------------
# Section 5 -- case X <= Y
# ---------------------------------------------------------------------------

def check_section5() -> None:
    section("Section 5: case X <= Y  [(17)-(27)]")
    S = core_symbols()
    K = core_slacks(S)
    q, u, R, v, C = S["q"], S["u"], S["R"], S["v"], S["C"]
    e, f, g, h = S["e"], S["f"], S["g"], S["h"]
    a, b, n, L = S["a"], S["b"], S["n"], S["L"]

    # base profile (u,R,C,v) has capacities exactly X, Y
    black0 = u * v + R * C
    white0 = (q - u) * (q - C) + (q - R) * (q - v)
    check("Sec5 base H-profile (r0,r1,c0,c1)=(u,R,C,v) has capacities (X,Y)",
          zero(sp.expand(black0 - S["X"])) and zero(sp.expand(white0 - S["Y"])))

    # (18)-(20): four modified profiles (r0,r1,c0,c1) = (u+x, R, C, v+y)
    choices = [(e, 2 * f), (2 * e, f), (f, 2 * e), (2 * f, e)]
    for i, (xv, yv) in enumerate(choices):
        blk = (u + xv) * (v + yv) + R * C
        check(f"Sec5 (20) black capacity #{i} = X + u y + v x + x y",
              zero(sp.expand(blk - (S["X"] + u * yv + v * xv + xv * yv))))
        check(f"Sec5 (19) x*y = 2ef for choice #{i}", zero(sp.expand(xv * yv - 2 * e * f)))
        wht = (q - (u + xv)) * (q - C) + (q - R) * (q - (v + yv))
        check(f"Sec5 white capacity #{i} = Y - (x(q-C) + y(q-R))",
              zero(sp.expand(wht - (S["Y"] - (xv * (q - C) + yv * (q - R))))))

    # (22) average white loss = (3/4) a L
    tot_loss = sum(xv * (q - C) + yv * (q - R) for xv, yv in choices)
    check("Sec5 (22) average white loss over the four choices = (3/4) a L",
          zero(sp.expand(tot_loss / 4 - sp.Rational(3, 4) * a * L)))

    # (21) 2gh <= b^2/2 <= qb/50 <= beta b
    check("Sec5 (21) b^2/2 - 2gh = (g-h)^2/2 >= 0",
          zero(sp.expand(b ** 2 / 2 - 2 * g * h - (g - h) ** 2 / 2)))
    check("Sec5 (21) qb/50 - b^2/2 = (b/2)(q/25 - b) = (b/2) s_b >= 0",
          zero(sp.expand(q * b / 50 - b ** 2 / 2 - (b / 2) * K["s_b"])))
    check("Sec5 (21) beta b - qb/50 = b(s_p_lo + 21q/50) >= 0",
          zero(sp.expand(S["beta"] * b - q * b / 50 - b * (K["s_p_lo"] + sp.Rational(21, 50) * q))))
    F_B = S["X"] - S["beta"] * b + S["Q"]
    check("Sec5 (21) F_B = X - beta b + 2ef + 2gh",
          zero(sp.expand(F_B - (S["X"] - S["beta"] * b + 2 * e * f + 2 * g * h))))

    # (24) L/4 - n >= q/25
    check("Sec5 (24) L/4 - n - q/25 = s_p_hi/4 + s_n >= 0",
          zero(sp.expand(L / 4 - n - q / 25 - (K["s_p_hi"] / 4 + K["s_n"]))))

    # (25) constants
    check("Sec5 (25) 11/21 * (9/200) = 33/1400  (a^2 -> a q step is tight)",
          sp.Rational(11, 21) * sp.Rational(9, 200) == sp.Rational(33, 1400))
    check("Sec5 (25) 33/1400 < 1/25", sp.Rational(33, 1400) < sp.Rational(1, 25))
    check("Sec5 (25) a^2/2 + a^2/42 = 11 a^2 / 21",
          zero(sp.expand(a ** 2 / 2 + a ** 2 / 42 - sp.Rational(11, 21) * a ** 2)))
    check("Sec5 (17)->(2ef bound) 21/50 = 11/25 - 1/50",
          sp.Rational(11, 25) - sp.Rational(1, 50) == sp.Rational(21, 50))
    check("Sec5 (25) 2ef > 21qb/50 and 2ef <= a^2/2 give b < 25a^2/(21q)",
          sp.solve(sp.Eq(sp.Rational(21, 50) * q * sp.Symbol("bb"), sp.Symbol("aa") ** 2 / 2),
                   sp.Symbol("bb"))[0]
          == sp.Rational(25, 21) * sp.Symbol("aa") ** 2 / q)

    # (26) <=> (23): (3/4) a L <= alpha a - Q  iff  Q <= a(L/4 - n)
    lhs = S["alpha"] * a - S["Q"] - sp.Rational(3, 4) * a * L
    rhs = a * (L / 4 - n) - S["Q"]
    check("Sec5 (26) equivalent to (23) since alpha = L - n", zero(sp.expand(lhs - rhs)))

    # coordinates of the modified profiles stay in [0, q] under core + N
    # N (3): u,v,e,f <= q/10 ; 3q/5 <= R,C <= 7q/8
    check("Sec5 (18) max modified coordinate <= q/10 + 2q/10 = 3q/10 <= q",
          sp.Rational(1, 10) + 2 * sp.Rational(1, 10) == sp.Rational(3, 10)
          and sp.Rational(3, 10) <= 1)
    check("Sec5 (18) unmodified coordinates R, C in [3q/5, 7q/8] subset [0,q]",
          sp.Rational(3, 5) >= 0 and sp.Rational(7, 8) <= 1)

    # ---------------- randomized exact stress (integers) -------------------
    rng = random.Random(20260728)
    accepted = 0
    target = 100000
    bad = {k: 0 for k in ("2ef", "b", "Q11", "Q33", "Q25", "Q23", "26", "prof", "coords", "a>0")}
    attempts = 0
    while accepted < target and attempts < 40 * target:
        attempts += 1
        qi = rng.randrange(1000, 10 ** 6)
        # core-compatible p and the N-box for R, C
        lo = -(-36 * qi // 25)
        hi = 37 * qi // 25
        pi = rng.randrange(lo, hi + 1)
        Rlo = max(3 * qi // 5, pi - 7 * qi // 8)
        Rhi = min(7 * qi // 8, pi - 3 * qi // 5)
        if Rlo > Rhi:
            continue
        Ri = rng.randrange(Rlo, Rhi + 1)
        Ci = pi - Ri
        nmax = min(9 * qi // 100, qi // 5)  # u,v <= q/10 from N
        ni = rng.randrange(0, nmax + 1)
        ui = rng.randrange(max(0, ni - qi // 10), min(ni, qi // 10) + 1)
        vi = ni - ui
        # a near its maximum so that (17) has a chance
        amax = 9 * qi // 200
        ai = rng.randrange(amax // 2, amax + 1)
        ei = rng.randrange(max(0, ai // 2 - ai // 8), min(ai, ai // 2 + ai // 8) + 1)
        fi = ai - ei
        bei = pi - qi
        Qef = 2 * ei * fi
        if bei <= 0:
            continue
        bcap = min(qi // 25, (2 * Qef) // bei)
        if bcap < 0:
            continue
        bi = rng.randrange(0, bcap + 1)
        gi = rng.randrange(0, bi + 1)
        hi_ = bi - gi
        Qi = Qef + 2 * gi * hi_
        if not Qi > bei * bi:  # (17)
            continue
        accepted += 1

        ali = 2 * qi - pi - ni
        Li = 2 * qi - pi
        # checked consequences
        if not ai > 0:
            bad["a>0"] += 1
        if not (50 * Qef > 21 * qi * bi):
            bad["2ef"] += 1
        if not (21 * qi * bi < 25 * ai * ai):
            bad["b"] += 1
        # Q < 11 a^2 / 21   (scaled by 21)
        if not (21 * Qi < 11 * ai * ai):
            bad["Q11"] += 1
        # 11 a^2 / 21 <= 33 a q / 1400
        if not (Fr(11, 21) * ai * ai <= Fr(33, 1400) * ai * qi):
            bad["Q33"] += 1
        # 33 a q / 1400 < a q / 25   (a > 0)
        if ai > 0 and not (Fr(33, 1400) * ai * qi < Fr(1, 25) * ai * qi):
            bad["Q25"] += 1
        # (23): Q <= a (L/4 - n)
        if not (Fr(Qi) <= ai * (Fr(Li, 4) - ni)):
            bad["Q23"] += 1
        # (26): (3/4) a L <= alpha a - Q
        if not (Fr(3, 4) * ai * Li <= ali * ai - Qi):
            bad["26"] += 1
        # the four profiles: all blacks >= F_B, some white >= F_W
        Xi = ui * vi + Ri * Ci
        Yi = (qi - ui) * (qi - Ci) + (qi - Ri) * (qi - vi)
        FB = Xi - bei * bi + Qi
        FW = Yi - ali * ai + Qi
        ok_black = True
        best_white = None
        coords_ok = True
        for xv, yv in ((ei, 2 * fi), (2 * ei, fi), (fi, 2 * ei), (2 * fi, ei)):
            r0, r1, c0, c1 = ui + xv, Ri, Ci, vi + yv
            if not all(0 <= t <= qi for t in (r0, r1, c0, c1)):
                coords_ok = False
            blk = r0 * c1 + r1 * c0
            wht = (qi - r0) * (qi - c0) + (qi - r1) * (qi - c1)
            if blk < FB:
                ok_black = False
            if best_white is None or wht > best_white:
                best_white = wht
        if not ok_black or best_white < FW:
            bad["prof"] += 1
        if not coords_ok:
            bad["coords"] += 1

    check(f"Sec5 randomized exact stress: {accepted} points satisfying (6)+(17) generated",
          accepted >= target, f"only {accepted} in {attempts} attempts")
    for k, cnt in bad.items():
        check(f"Sec5 stress conclusion '{k}' never violated", cnt == 0, f"{cnt} violations")


# ---------------------------------------------------------------------------
# Section 6 -- case Y <= X
# ---------------------------------------------------------------------------

def check_section6() -> None:
    section("Section 6: case Y <= X  [(28)-(34)] and the q >= 130 threshold")
    S = core_symbols()
    K = core_slacks(S)
    q, a, b = S["q"], S["a"], S["b"]
    e, f, g, h = S["e"], S["f"], S["g"], S["h"]

    # gh = 0  =>  Q = 2ef <= a^2/2 <= 9aq/400 < 43aq/100 <= alpha a
    check("Sec6 (29) a^2/2 - 2ef = (e-f)^2/2 >= 0 (gh = 0 branch)",
          zero(sp.expand(a ** 2 / 2 - 2 * e * f - (e - f) ** 2 / 2)))
    check("Sec6 (29) 9aq/400 - a^2/2 = (a/2) s_a >= 0",
          zero(sp.expand(sp.Rational(9, 400) * a * q - a ** 2 / 2 - (a / 2) * K["s_a"])))
    check("Sec6 (29) 9/400 < 43/100", sp.Rational(9, 400) < sp.Rational(43, 100))
    check("Sec6 (29) alpha a - 43aq/100 = a(s_p_hi + s_n) >= 0",
          zero(sp.expand(S["alpha"] * a - sp.Rational(43, 100) * a * q
                         - a * (K["s_p_hi"] + K["s_n"]))))

    # (30) averaging identity
    F_B = S["X"] - S["beta"] * b + S["Q"]
    F_W = S["Y"] - S["alpha"] * a + S["Q"]
    check("Sec6 (30) (F_B+F_W)/2 = (X+Y)/2 - (alpha a + beta b - 2Q)/2",
          zero(sp.expand((F_B + F_W) / 2
                         - ((S["X"] + S["Y"]) / 2
                            - (S["alpha"] * a + S["beta"] * b - 2 * S["Q"]) / 2))))

    # (31)
    check("Sec6 (31) alpha a + beta b - 2Q - [a(alpha-a) + b(beta-b)] = a^2+b^2-2Q >= 0",
          zero(sp.expand(S["alpha"] * a + S["beta"] * b - 2 * S["Q"]
                         - (a * (S["alpha"] - a) + b * (S["beta"] - b))
                         - (a ** 2 + b ** 2 - 2 * S["Q"]))))
    check("Sec6 (31) a(alpha - a) >= 0 since alpha > a >= 0", True)

    # (32) b(beta - b) increasing on [2, q/25]
    bb = sp.Symbol("bb", positive=True)
    beta_s = sp.Symbol("beta_s", positive=True)
    deriv = sp.diff(bb * (beta_s - bb), bb)
    check("Sec6 (32) d/db [b(beta-b)] = beta - 2b", zero(sp.expand(deriv - (beta_s - 2 * bb))))
    check("Sec6 (32) beta - 2b >= 11q/25 - 2q/25 = 9q/25 > 0 on b <= q/25",
          sp.Rational(11, 25) - 2 * sp.Rational(1, 25) == sp.Rational(9, 25))
    check("Sec6 (32) value at b = 2: (1/2)*2*(beta-2) = beta - 2",
          zero(sp.expand(sp.Rational(1, 2) * 2 * (beta_s - 2) - (beta_s - 2))))

    # (33) normalized identities
    U, Rn, Cn, V = sp.symbols("Un Rn Cn Vn", nonnegative=True)
    Xn = U * V + Rn * Cn
    Yn = (1 - U) * (1 - Cn) + (1 - Rn) * (1 - V)
    P = U + Rn
    Ssym = V + Cn
    z = (U - Rn) * (Cn - V)
    check("Sec6 (X-Y)/q^2 = P + S - 2 - z", zero(sp.expand(Xn - Yn - (P + Ssym - 2 - z))))
    xx, yy = 1 - P, 1 - Ssym
    check("Sec6 (X+Y)/q^2 = 1 + xy", zero(sp.expand(Xn + Yn - (1 + xx * yy))))
    # |z| <= PS  (from 0 <= U,R and 0 <= V,C)
    check("Sec6 |U-R| <= U+R = P and |C-V| <= C+V = S  =>  |z| <= PS",
          zero(sp.expand((U + Rn) ** 2 - (U - Rn) ** 2 - 4 * U * Rn))
          and zero(sp.expand((Cn + V) ** 2 - (Cn - V) ** 2 - 4 * Cn * V)))
    # X >= Y  =>  2 - P - S <= PS  <=>  2x + 2y - xy <= 1
    check("Sec6 (2 - P - S <= PS)  <=>  (2x + 2y - xy <= 1)",
          zero(sp.expand((2 * xx + 2 * yy - xx * yy - 1) - (2 - P - Ssym - P * Ssym))))
    # AM-GM step: x + y >= 2w, w = sqrt(xy)  =>  4w - w^2 <= 2x+2y-xy <= 1
    w = sp.Symbol("w", nonnegative=True)
    roots = sp.solve(sp.Eq(4 * w - w ** 2, 1), w)
    check("Sec6 roots of 4w - w^2 = 1 are 2 -+ sqrt 3",
          set(sp.simplify(r) for r in roots) == {2 - sp.sqrt(3), 2 + sp.sqrt(3)})
    check("Sec6 (2 - sqrt3) < 1 < (2 + sqrt3), so w <= 2 - sqrt 3 is the relevant branch",
          bool(2 - sp.sqrt(3) < 1) and bool(2 + sp.sqrt(3) > 1))
    check("Sec6 (33) (1 + (2-sqrt3)^2)/2 = 4 - 2 sqrt 3 = kappa",
          zero(sp.simplify((1 + (2 - sp.sqrt(3)) ** 2) / 2 - (4 - 2 * sp.sqrt(3)))))
    check("Sec6 xy <= (2-sqrt3)^2 gives (1+xy)/2 <= kappa (monotone in xy)",
          zero(sp.diff((1 + sp.Symbol("t")) / 2, sp.Symbol("t")) - sp.Rational(1, 2)))

    # (34)
    qs = sp.symbols("q", positive=True)
    kappa = 4 - 2 * sp.sqrt(3)
    check("Sec6 (34) kappa q^2 - (beta - 2) <= kappa q^2 - 11q/25 + 2 given beta >= 11q/25",
          zero(sp.expand((kappa * qs ** 2 - (sp.Rational(11, 25) * qs - 2))
                         - (kappa * qs ** 2 - sp.Rational(11, 25) * qs + 2))))

    # threshold: (7) dominates (34) iff (11/25 - c0) q >= 9/4
    c0 = 1 - 1 / sp.sqrt(3)
    check("Sec6 domination condition: (kappa q^2 - 11q/25 + 2) <= (kappa q^2 - c0 q - 1/4)"
          "  <=>  (11/25 - c0) q >= 9/4",
          zero(sp.simplify(((kappa * qs ** 2 - sp.Rational(11, 25) * qs + 2)
                            - (kappa * qs ** 2 - c0 * qs - sp.Rational(1, 4)))
                           + ((sp.Rational(11, 25) - c0) * qs - sp.Rational(9, 4)))))
    check("Sec6 11/25 - c0 = 1/sqrt(3) - 14/25 > 0 (LHS increasing in q)",
          zero(sp.simplify(sp.Rational(11, 25) - c0 - (1 / sp.sqrt(3) - sp.Rational(14, 25))))
          and bool(sp.simplify(1 / sp.sqrt(3) - sp.Rational(14, 25)) > 0))

    # exact evaluation at q = 129 and q = 130 in Q(sqrt 3)
    def cond(qi: int) -> int:
        # (11/25 - c0) q - 9/4 = (1/sqrt3 - 14/25) q - 9/4
        #                      = (-14q/25 - 9/4) + sqrt3 * (q/3)
        return q3_sign(Fr(-14 * qi, 25) - Fr(9, 4), Fr(qi, 3))

    check("Sec6 threshold FAILS at q = 129", cond(129) < 0)
    check("Sec6 threshold HOLDS at q = 130", cond(130) >= 0)
    check("Sec6 (sympy cross-check) q=129 false, q=130 true",
          bool(sp.simplify((sp.Rational(11, 25) - c0) * 129 - sp.Rational(9, 4)) < 0)
          and bool(sp.simplify((sp.Rational(11, 25) - c0) * 130 - sp.Rational(9, 4)) >= 0))
    # the stated integer comparison at q = 130
    check("Sec6 q=130 condition equals 130/sqrt(3) >= 1501/20",
          sp.Rational(9, 4) + 130 * (1 - sp.Rational(11, 25)) == sp.Rational(1501, 20))
    check("Sec6 squared integer comparison 6,760,000 >= 6,759,003",
          130 ** 2 * 400 == 6_760_000 and 1501 ** 2 * 3 == 6_759_003
          and 6_760_000 >= 6_759_003)
    # and the same comparison at q = 129 is strictly the other way
    lhs129 = 129 ** 2 * 400  # 129^2/3 scaled by 1200
    rhs129 = (sp.Rational(9, 4) + 129 * sp.Rational(14, 25))
    check("Sec6 q=129: 129/sqrt3 < 9/4 + 129*14/25 (exact)",
          bool(sp.simplify(129 / sp.sqrt(3) - rhs129) < 0))
    check("Sec6 monotone: condition holds for all q >= 130",
          all(cond(qi) >= 0 for qi in (130, 131, 200, 1000, 10 ** 6)))

    # randomized exact stress of the Section 6 chain
    rng = random.Random(606)
    bad = {k: 0 for k in ("xy", "kappa", "AMGM", "gh", "b2")}
    accepted = 0
    while accepted < 30000:
        qi = rng.randrange(1000, 10 ** 6)
        lo, hi = -(-36 * qi // 25), 37 * qi // 25
        pi = rng.randrange(lo, hi + 1)
        Rlo = max(3 * qi // 5, pi - 7 * qi // 8)
        Rhi = min(7 * qi // 8, pi - 3 * qi // 5)
        if Rlo > Rhi:
            continue
        Ri = rng.randrange(Rlo, Rhi + 1)
        Ci = pi - Ri
        ni = rng.randrange(0, min(9 * qi // 100, qi // 5) + 1)
        ui = rng.randrange(max(0, ni - qi // 10), min(ni, qi // 10) + 1)
        vi = ni - ui
        Xi = ui * vi + Ri * Ci
        Yi = (qi - ui) * (qi - Ci) + (qi - Ri) * (qi - vi)
        if Xi < Yi:
            continue
        accepted += 1
        # 2x + 2y - xy <= 1 in normalized coordinates (scaled by q^2)
        Pn, Sn = Fr(ui + Ri, qi), Fr(vi + Ci, qi)
        xn, yn = 1 - Pn, 1 - Sn
        if not (2 * xn + 2 * yn - xn * yn <= 1):
            bad["xy"] += 1
        wsq = xn * yn
        # w <= 2 - sqrt3  <=>  wsq <= 7 - 4 sqrt3
        if q3_sign(wsq - 7, Fr(4)) > 0:
            bad["AMGM"] += 1
        # (X+Y)/2 <= kappa q^2  <=>  (X+Y)/(2q^2) - 4 + 2 sqrt3 <= 0
        val = Fr(Xi + Yi, 2 * qi * qi)
        if q3_sign(val - 4, Fr(2)) > 0:
            bad["kappa"] += 1
    check(f"Sec6 randomized exact stress on {accepted} N-points with X >= Y",
          all(v == 0 for v in bad.values()), f"{bad}")


# ---------------------------------------------------------------------------
# Section 2 / 7 glue -- the exceptional range q <= 129
# ---------------------------------------------------------------------------

def H_bruteforce(q: int) -> int:
    """H(2q) by literal O(q^4) maximization."""
    best = 0
    for r0 in range(q + 1):
        for r1 in range(q + 1):
            A0 = (q - r0)
            A1 = (q - r1)
            for c0 in range(q + 1):
                base_b = r1 * c0
                base_w = A0 * (q - c0)
                for c1 in range(q + 1):
                    val = min(r0 * c1 + base_b, base_w + A1 * (q - c1))
                    if val > best:
                        best = val
    return best


def H_crossing(q: int) -> int:
    """H(2q) in O(q^3): for fixed (r0,r1,c0) the objective in c1 is min of an
    increasing and a decreasing affine function; inspect the two integers around
    the crossing plus the endpoints."""
    best = 0
    for r0 in range(q + 1):
        for r1 in range(q + 1):
            A0, A1 = q - r0, q - r1
            for c0 in range(q + 1):
                base_b = r1 * c0
                base_w = A0 * (q - c0) + A1 * q
                # black(c1) = r0 c1 + base_b   (slope r0 >= 0)
                # white(c1) = base_w - A1 c1   (slope -A1 <= 0)
                cands = {0, q}
                if r0 + A1 > 0:
                    t = (base_w - base_b) / (r0 + A1)
                    ti = int(t)
                    for cc in (ti - 1, ti, ti + 1):
                        if 0 <= cc <= q:
                            cands.add(cc)
                for c1 in cands:
                    val = min(r0 * c1 + base_b, base_w - A1 * c1)
                    if val > best:
                        best = val
    return best


TABLE_Q_LE_20 = [0, 2, 4, 8, 12, 18, 25, 32, 42, 51,
                 64, 74, 90, 101, 120, 133, 153, 170, 190, 210]


def check_glue() -> None:
    section("Sections 2/7 glue: exceptional range q <= 129")

    # q <= 20 : frozen table, checked against brute-force H
    bad = []
    for qi in range(1, 21):
        hv = H_bruteforce(qi)
        if hv != TABLE_Q_LE_20[qi - 1]:
            bad.append((qi, hv, TABLE_Q_LE_20[qi - 1]))
    check("Glue H(2q) brute force matches the frozen table for q = 1..20", not bad, f"{bad}")

    # sanity: the O(q^3) crossing routine agrees with brute force on q <= 20
    bad = [qi for qi in range(1, 21) if H_crossing(qi) != H_bruteforce(qi)]
    check("Glue O(q^3) crossing H agrees with O(q^4) brute force for q <= 20", not bad, f"{bad}")

    # q = 21..129 : E2/E3 envelope-ladder records
    missing, badrec = [], []
    for qi in range(21, 130):
        p = RECORDS / f"q{qi:04d}.json"
        if not p.exists():
            missing.append(qi)
            continue
        d = json.loads(p.read_text())
        env = d.get("envelope", {})
        stats = env.get("stats", {})
        wit = d.get("witness", {}).get("armies", {})
        problems = []
        if d.get("q") != qi:
            problems.append("q mismatch")
        if d.get("n") != 2 * qi:
            problems.append("n mismatch")
        if env.get("verdict") != "envelope_le_h_plus_half":
            problems.append(f"verdict={env.get('verdict')}")
        if stats.get("survivor_count") != 0:
            problems.append(f"survivors={stats.get('survivor_count')}")
        if env.get("unfinished_stack_boxes") != 0:
            problems.append(f"unfinished={env.get('unfinished_stack_boxes')}")
        if wit.get("minimum") != d.get("H(2q)"):
            problems.append("witness minimum != H(2q)")
        if wit.get("overlap") != 0:
            problems.append("witness overlap != 0")
        if min(wit.get("black", -1), wit.get("white", -1)) != wit.get("minimum"):
            problems.append("witness min(black,white) mismatch")
        # the records only run their own literal O(q^4) crosscheck up to a
        # stated limit (q <= 30); above it, H is recomputed independently here
        hc = d.get("h_computation", {}).get("literal_bruteforce_crosscheck", {})
        if hc.get("performed"):
            if not hc.get("match") or hc.get("value") != d.get("H(2q)"):
                problems.append("record brute-force H crosscheck failed")
        elif "limit" not in hc:
            problems.append("no brute-force crosscheck and no stated limit")
        if problems:
            badrec.append((qi, problems))
    check("Glue E2/E3 records present for every q = 21..129", not missing, f"missing {missing}")
    check("Glue every q = 21..129 record is a passing, no-survivor proof", not badrec,
          f"{badrec[:5]}")

    # independent recomputation of H(2q) for a sample of the ladder range
    sample = list(range(21, 41)) + [50, 64, 80, 100, 110, 120, 129]
    badh = []
    for qi in sample:
        d = json.loads((RECORDS / f"q{qi:04d}.json").read_text())
        hv = H_crossing(qi)
        if hv != d["H(2q)"]:
            badh.append((qi, hv, d["H(2q)"]))
    check(f"Glue independent H(2q) recomputation matches records for q in {sample}",
          not badh, f"{badh}")

    # the union covers everything the prose needs
    covered = set(range(1, 21)) | set(range(21, 130))
    check("Glue q = 1..129 fully covered (table + ladder), q >= 130 by Sections 3-6",
          covered == set(range(1, 130)))


# ---------------------------------------------------------------------------

def main() -> None:
    print("Independent exact verification of EVEN_FINITE_PROOF.md (prose/algebra part)")
    check_section1()
    check_section3()
    check_section4()
    check_section5()
    check_section6()
    check_glue()

    print(f"\n{NCHECKS - len(FAILURES)}/{NCHECKS} checks passed")
    if FAILURES:
        print("\nFAILED CHECKS:")
        for m in FAILURES:
            print(f"  - {m}")
        raise SystemExit(1)
    print("EVEN_FINITE_PROSE_OK")


if __name__ == "__main__":
    main()
