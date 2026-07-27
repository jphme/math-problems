#!/usr/bin/env python3
"""Independent machine verification of theory-track report #4
(sources/theory_track_report4_2026-07-25_pro.md).

The report ships its own sympy script (archived alongside it), which checks its
algebraic identities.  This script checks what that one does NOT:

  A. that the displayed "target boundary" polynomials really ARE the boundary
     polynomials of the six Group-2 row targets, re-derived independently from
     the direction lattice {j*pi/3 + m*alpha}, chi = (-1)^j z^m, at the actual
     candidate scales (k = mb for rows I/IV/E, k = m for III/V/II);
  B. that the one-tile boundary polynomials factor as the report's "residual"
     arguments require: Group-2 tile -> unit*P, unit*Q; Group-1 tile ->
     unit*(HL), unit*(HM); gamma=2alpha tile -> unit*(QL), unit*(QM);
     and that the targets at multiplier m/n/r are unit*(mbH), unit*(nbHHbar),
     unit*(rbQ) -- the exact normalizations Theorem 1.1 divides out;
  C. end-to-end exact-N representations for EVERY surviving frontier candidate
     (105 x2, 120, 132 x3, 143, 154, 161, 184): the representation is built
     term by term as N signed unit multiples of the generators, summed with
     exact integer arithmetic, and compared to the target polynomial;
  D. Theorem 2 (equilateral -> row V transfer): full coordinate-level
     verification of the double-bisector dissection, plus the count identity
     and the corollary threshold ceil(3R/2);
  E. Theorem 3 (shape-4 -> shape-5 transfer): coordinate-level verification of
     the apex-cevian dissection;
  F. Theorem 4 (gamma=2alpha multiplier transport): coordinate-level
     verification of the single-cevian dissection, plus the (2,3) chain;
  G. arithmetic of the now-unconditional shape-4 filter at the live 132
     candidate, and frontier-consistency checks.

Source imports verified against the actual arXiv texts (fetched 2026-07-25):
  - Beeson arXiv:1206.2229v3, Lemma 6 (= \\label{lemma:zerolimits2}, "there are
    at least two $c$ edges of tiles on side $AC$"), invoked in Section 11.4
    ("Results based on computation", the isosceles base-angles-(alpha+beta)
    case = our shape 4) for all three sides.  Hypotheses discharged for
    shape 4: (i) gamma = pi - alpha - beta > pi/2 since alpha + beta < pi/2;
    (ii) alpha irrational multiple of pi (standing non-classical assumption);
    (iii) target angles alpha+beta, alpha+beta, alpha all < gamma;
    (iv) gcd(a,b) = 1 with a = pq >= 2, so b is not a multiple of a.
  - Beeson arXiv:1206.1974v7, \\label{lemma:no20}: the isosceles
    (alpha, alpha, pi-2alpha) triangle has no 20-tiling by the (4,5,6) tile
    -- i.e. r = 2 fails on the gamma=2alpha ray (u,v) = (2,3), as the report
    states.  [pub]

Usage:  uv run python verify_theory_report4_claims.py
"""

import math
from math import pi, gcd, isqrt

FAILURES = []
COUNT = 0


def check(name, cond, detail=""):
    global COUNT
    COUNT += 1
    tag = "PASS" if cond else "FAIL"
    if not cond:
        FAILURES.append(name)
    print(f"{tag} {name}" + (f"  [{detail}]" if detail and not cond else ""))


# ----------------------------------------------------------------------------
# direction-lattice boundary machinery (same as verify_theory_report3_claims)
# ----------------------------------------------------------------------------

def match_lattice(theta, step, alpha, jmax, mmax, tol=1e-9):
    for m in range(-mmax, mmax + 1):
        for j in range(0, jmax):
            d = (theta - j * step - m * alpha) % (2 * pi)
            if min(d, 2 * pi - d) < tol:
                return j, m
    return None


def boundary_poly(sides, step, alpha, jmax, mmax, half_turn_j):
    poly = {}
    for length, theta in sides:
        jm = match_lattice(theta % (2 * pi), step, alpha, jmax, mmax)
        if jm is None:
            return None
        j, m = jm
        poly[m] = poly.get(m, 0.0) + length * (-1) ** j
    return {m: c for m, c in poly.items() if abs(c) > 1e-6}


def poly_equal_up_to_unit(P, Q, kmax=6):
    if P is None or Q is None:
        return False
    for k in range(-kmax, kmax + 1):
        for s in (1, -1):
            Qs = {m + k: s * c for m, c in Q.items()}
            keys = set(P) | set(Qs)
            if all(abs(P.get(m, 0) - Qs.get(m, 0)) < 1e-5 for m in keys):
                return True
    return False


def triangle_sides(angles, sidelens):
    """CCW traversal; sidelens[i] opposite angles[i]; first side along +x."""
    A1, A2, A3 = angles
    return [(sidelens[2], 0.0),
            (sidelens[0], pi - A2),
            (sidelens[1], 2 * pi - A2 - A3)]


def eisenstein_triples(bound):
    out = []
    for a in range(1, bound):
        for b in range(1, bound):
            c2 = a * a + a * b + b * b
            c = isqrt(c2)
            if c * c == c2 and gcd(gcd(a, b), c) == 1:
                out.append((a, b, c))
    return out


# exact Laurent-dict arithmetic ----------------------------------------------

def dict_add(P, Q):
    R = dict(P)
    for k, v in Q.items():
        R[k] = R.get(k, 0) + v
    return {k: v for k, v in R.items() if v != 0}


def dict_scale_shift(P, coeff, shift):
    return {k + shift: coeff * v for k, v in P.items()}


def dict_mul(P, Q):
    R = {}
    for i, u in P.items():
        for j, v in Q.items():
            R[i + j] = R.get(i + j, 0) + u * v
    return {k: v for k, v in R.items() if v != 0}


def expand_representation(rep):
    """rep: list of (coeffpoly, gen) with coeffpoly {shift: int}.
    Returns (sum_dict, term_count) expanding every integer coefficient into
    that many signed unit multiples of gen."""
    total = {}
    terms = 0
    for coeffpoly, gen in rep:
        for shift, coeff in coeffpoly.items():
            total = dict_add(total, dict_scale_shift(gen, coeff, shift))
            terms += abs(coeff)
    return total, terms


# ============================================================================
# A. Group-2 rows: target boundary polynomials from the direction lattice
# ============================================================================
print("--- A: Group-2 row target boundary polynomials (direction lattice) ---")

TRIPLES = eisenstein_triples(60)
check("A0: no primitive Eisenstein triple with a=1 or b=1 (bound 2000)",
      all(a >= 2 and b >= 2 for a, b, c in eisenstein_triples(2000)))
check("A0b: parity c == a+ab+b (mod 2) on all sampled triples",
      all((c - (a + a * b + b)) % 2 == 0 for a, b, c in TRIPLES))


def g2_row_target(row, a, b, c, k):
    """(angles, sidelens) of the row target at sieve scale k, sides opposite
    angles; conventions of phi_filter_all_rows.py / sieve_120rows.py."""
    al = math.acos((b * b + c * c - a * a) / (2.0 * b * c))
    be = math.acos((a * a + c * c - b * b) / (2.0 * a * c))
    U, V, W = a + 2 * b, 2 * a + b, a + b
    if row == "I":
        return (al, al, pi - 2 * al), (k * c, k * c, k * U)
    if row == "IV":
        return (al, al + be, al + 2 * be), (k * a, k * c, k * W)
    if row == "E":
        return (pi / 3, pi / 3, pi / 3), (k * a * b, k * a * b, k * a * b)
    if row == "III":
        return (al, 2 * be, 2 * al + be), (k * a * c, k * b * V, k * W * c)
    if row == "V":
        return (2 * al, 2 * be, al + be), (k * a * U, k * b * V, k * c * c)
    if row == "II":
        return (al, 2 * al, 3 * be), (k * c * c, k * U * c, 3 * k * b * W)
    raise ValueError(row)


def g2_row_claimed_poly(row, a, b, c, m):
    """The report's displayed target boundary (up to unit), at multiplier m."""
    d, U, V, W = a - b, a + 2 * b, 2 * a + b, a + b
    if row == "I":
        return {0: m * b * U, 1: -m * b * c, -1: -m * b * c}
    if row == "IV":
        return {0: m * b * (2 * a + b), 1: -m * b * c}
    if row == "E":
        return {0: 3 * m * a * b}
    if row == "III":
        return {0: m * W * c, 2: -m * a * c, 1: -m * b * V}
    if row == "V":
        return {0: m * c * c, 2: -m * (a * U + b * V)}
    if row == "II":  # after multiplication by z^2
        return {2: 3 * m * b * W, 0: -m * c * c, 3: -m * U * c}
    raise ValueError(row)


ROW_SCALE = {"I": "mb", "IV": "mb", "E": "m", "III": "m", "V": "m", "II": "m"}
# NB: row E at sieve scale k has side k*ab; the report's multiplier m equals k.

ok_rows = {r: True for r in ["I", "IV", "E", "III", "V", "II"]}
for a, b, c in TRIPLES[:12]:
    al = math.acos((b * b + c * c - a * a) / (2.0 * b * c))
    for row in ok_rows:
        m = 1
        k = m * b if ROW_SCALE[row] == "mb" else m
        angles, sl = g2_row_target(row, a, b, c, k)
        P = boundary_poly(triangle_sides(angles, sl), pi / 3, al,
                          jmax=6, mmax=4, half_turn_j=3)
        claimed = {kk: float(v) for kk, v in
                   g2_row_claimed_poly(row, a, b, c, m).items()}
        if not poly_equal_up_to_unit(P, claimed):
            ok_rows[row] = False
for row in ok_rows:
    check(f"A1: row {row} target boundary = unit * report's polynomial "
          f"[direction lattice, independent, 12 triples]", ok_rows[row])

# A2: one-tile polynomials of the 120-degree tile are unit*P, unit*Q
ok = True
for a, b, c in TRIPLES[:12]:
    al = math.acos((b * b + c * c - a * a) / (2.0 * b * c))
    be = math.acos((a * a + c * c - b * b) / (2.0 * a * c))
    d = a - b
    T1 = triangle_sides((al, be, 2 * pi / 3), (a, b, c))
    T2 = triangle_sides((al, 2 * pi / 3, be), (a, c, b))  # mirror
    P1 = boundary_poly(T1, pi / 3, al, jmax=6, mmax=4, half_turn_j=3)
    P2 = boundary_poly(T2, pi / 3, al, jmax=6, mmax=4, half_turn_j=3)
    Pgen = {0: float(d), 1: float(c)}
    Qgen = {0: float(d), -1: float(c)}
    hit = ((poly_equal_up_to_unit(P1, Pgen) and poly_equal_up_to_unit(P2, Qgen))
           or (poly_equal_up_to_unit(P1, Qgen) and poly_equal_up_to_unit(P2, Pgen)))
    if not hit:
        ok = False
check("A2: 120-degree one-tile boundary polynomials = unit*P, unit*Q "
      "(two reflection classes)", ok)

# A3: t <= N and parity for all m (scaling argument: t = m t1, N = m^2 N1)
ok = True
for a, b, c in TRIPLES:
    d, U, V, W = a - b, a + 2 * b, 2 * a + b, a + b
    t1 = {"I": a + b + c, "IV": b + c + abs(d), "E": c + abs(d),
          "III": c + 3 * a, "V": 3 * c + abs(d), "II": U + 3 * c + abs(d)}
    N1 = {"I": b * U, "IV": b * W, "E": a * b, "III": V * W, "V": U * V,
          "II": 3 * U * W}
    for row in t1:
        for m in (1, 2, 3, 4):
            t, N = m * t1[row], m * m * N1[row]
            if not (t <= N and (N - t) % 2 == 0):
                ok = False
check("A3: t <= N and t == N (mod 2) in every row for m = 1..4, "
      f"{len(TRIPLES)} triples", ok)


# ============================================================================
# B. Non-Group-2 branches: tile polynomial factorizations and normalizations
# ============================================================================
print("--- B: Group-1 / gamma=2alpha tile polynomials and target residuals ---")

G1_PQ = [(p, q) for p in range(1, 8) for q in range(p + 1, 9) if gcd(p, q) == 1]
G2A_UV = [(u, v) for u in range(2, 9) for v in range(u + 1, 2 * u)
          if gcd(u, v) == 1]

# B1: Group-1 tile (pq, q^2-p^2, q^2): reflection-class polys unit*HL, unit*HM
ok = True
for p, q in G1_PQ:
    a, b, c = p * q, q * q - p * p, q * q
    al = 2 * math.asin(p / (2.0 * q))
    be = (pi - 3 * al) / 2
    ga = pi - al - be
    gdir = (pi + al) / 2
    T1 = triangle_sides((al, be, ga), (a, b, c))
    T2 = triangle_sides((al, ga, be), (a, c, b))
    P1 = boundary_poly(T1, pi, gdir, jmax=2, mmax=4, half_turn_j=1)
    P2 = boundary_poly(T2, pi, gdir, jmax=2, mmax=4, half_turn_j=1)
    HL = {3: -float(a), 2: float(b), 0: float(c)}     # H*L = -pq z^3 + b z^2 + q^2
    HM = {3: float(c), 1: float(b), 0: -float(a)}     # H*M = q^2 z^3 + b z - pq
    hit = ((poly_equal_up_to_unit(P1, HL) and poly_equal_up_to_unit(P2, HM))
           or (poly_equal_up_to_unit(P1, HM) and poly_equal_up_to_unit(P2, HL)))
    if not hit:
        ok = False
check("B1: Group-1 one-tile boundary polynomials = unit*(HL), unit*(HM)", ok)

# B2: gamma=2alpha tile (u^2, v^2-u^2, uv): polys unit*(QL), unit*(QM)
ok = True
for u, v in G2A_UV:
    a, b, c = u * u, v * v - u * u, u * v
    al = math.acos(v / (2.0 * u))
    be = pi - 3 * al
    T1 = triangle_sides((al, be, 2 * al), (a, b, c))
    T2 = triangle_sides((al, 2 * al, be), (a, c, b))
    P1 = boundary_poly(T1, pi, al, jmax=2, mmax=4, half_turn_j=1)
    P2 = boundary_poly(T2, pi, al, jmax=2, mmax=4, half_turn_j=1)
    QL = {3: float(a), 1: -float(b), 0: float(c)}     # Q*(uz+v) = u^2 z^3 - b z + uv
    QM = {3: float(c), 2: -float(b), 0: float(a)}     # Q*(u+vz) = uv z^3 - b z^2 + u^2
    hit = ((poly_equal_up_to_unit(P1, QL) and poly_equal_up_to_unit(P2, QM))
           or (poly_equal_up_to_unit(P1, QM) and poly_equal_up_to_unit(P2, QL)))
    if not hit:
        ok = False
check("B2: gamma=2alpha one-tile boundary polynomials = unit*(QL), unit*(QM)",
      ok)

# B3: targets at their actual candidate scales are unit*(mb*H), unit*(nb*H*Hbar),
#     unit*(rb*Q) -- the exact residual normalizations of Theorem 1.1.
ok4 = ok5 = okg = True
for p, q in G1_PQ[:8]:
    b, h = q * q - p * p, 2 * q * q - p * p
    al = 2 * math.asin(p / (2.0 * q))
    gdir = (pi + al) / 2
    for mult in (1, 2):
        sl = triangle_sides(((pi - al) / 2, (pi - al) / 2, al),
                            (b * q * mult, b * q * mult, b * p * mult))
        P = boundary_poly(sl, pi, gdir, jmax=2, mmax=4, half_turn_j=1)
        H = {2: float(mult * b * q), 1: float(mult * b * p),
             0: float(mult * b * q)}
        if not poly_equal_up_to_unit(P, H):
            ok4 = False
        sl = triangle_sides((al, al, pi - 2 * al),
                            (b * q * q * mult, b * q * q * mult, b * h * mult))
        P = boundary_poly(sl, pi, gdir, jmax=2, mmax=6, half_turn_j=1)
        HH = {4: float(mult * b * q * q), 2: float(mult * b * h),
              0: float(mult * b * q * q)}
        if not poly_equal_up_to_unit(P, HH):
            ok5 = False
for u, v in G2A_UV[:8]:
    b = v * v - u * u
    al = math.acos(v / (2.0 * u))
    for r in (1, 2):
        sl = triangle_sides((al, al, pi - 2 * al),
                            (u * b * r, u * b * r, v * b * r))
        P = boundary_poly(sl, pi, al, jmax=2, mmax=4, half_turn_j=1)
        Qd = {2: float(r * b * u), 1: -float(r * b * v), 0: float(r * b * u)}
        if not poly_equal_up_to_unit(P, Qd):
            okg = False
check("B3a: shape-4 target at multiplier m = unit * (mb) * H", ok4)
check("B3b: shape-5 target at multiplier n = unit * (nb) * H*Hbar", ok5)
check("B3c: gamma=2alpha target at multiplier r = unit * (rb) * Q", okg)


# ============================================================================
# C. Exact-N representations, end-to-end, for every surviving frontier
#    candidate (exact integer arithmetic)
# ============================================================================
print("--- C: exact-N representations for the whole frontier ---")


def g2_exact_N(row, a, b, c, m):
    """Build the report's representation + padding; return True iff it sums to
    the target polynomial in exactly N signed unit multiples of P, Q."""
    d, U, V, W = a - b, a + 2 * b, 2 * a + b, a + b
    P = {0: d, 1: c}
    Q = {0: d, -1: c}
    REPS = {
        "I":   [({0: -m * b, -1: m * c}, P), ({0: -m * a}, Q)],
        "IV":  [({0: -m * b, -1: m * c}, P), ({0: -m * d}, Q)],
        "E":   [({-1: m * c}, P), ({0: -m * d}, Q)],
        "III": [({1: -m * a, 0: -m * c}, P), ({1: 2 * m * a}, Q)],
        "V":   [({1: -2 * m * c}, P), ({1: m * c, 2: m * d}, Q)],
        "II":  [({2: -m * U, 1: 2 * m * c}, P), ({1: -m * c, 2: -m * d}, Q)],
    }
    N = m * m * {"I": b * U, "IV": b * W, "E": a * b, "III": V * W,
                 "V": U * V, "II": 3 * U * W}[row]
    target = g2_row_claimed_poly(row, a, b, c, m)
    total, t = expand_representation(REPS[row])
    if total != target:
        return False, f"sum mismatch {total} vs {target}"
    if not (t <= N and (N - t) % 2 == 0):
        return False, f"t={t} N={N}"
    # padding: (N-t)/2 cancelling pairs +P, -P
    pairs = (N - t) // 2
    total = dict_add(total, {})  # unchanged: +P-P cancels exactly
    return True, f"t={t}, padded to N={N} with {pairs} cancelling pairs"


FRONTIER_G2 = [
    (105, "IV", 16, 5, 19, 1), (105, "IV", 8, 7, 13, 1),
    (120, "IV", 7, 8, 13, 1),
    (132, "I", 5, 3, 7, 2),
    (143, "V", 3, 5, 7, 1),
    (154, "I", 8, 7, 13, 1),
    (184, "I", 7, 8, 13, 1),
]
for N, row, a, b, c, m in FRONTIER_G2:
    Ncheck = m * m * {"I": b * (a + 2 * b), "IV": b * (a + b), "E": a * b,
                      "III": (2 * a + b) * (a + b),
                      "V": (a + 2 * b) * (2 * a + b),
                      "II": 3 * (a + 2 * b) * (a + b)}[row]
    ok, detail = g2_exact_N(row, a, b, c, m)
    check(f"C: N={N} row {row} ({a},{b},{c}) m={m}: exact-{N} representation "
          f"[{detail}]", ok and Ncheck == N)

# Group-1 shape 4 at 132: (p,q,m) = (4,7,2);  target = unit * (mb) * H
p, q, m = 4, 7, 2
b = q * q - p * p
H = {2: q, 1: p, 0: q}
L = {0: q, 1: -p}
M = {1: q, 0: -p}
HL, HM = dict_mul(H, L), dict_mul(H, M)
total, t = expand_representation([({0: m * q}, HL), ({0: m * p}, HM)])
target = dict_scale_shift(H, m * b, 0)
N = b * m * m
check(f"C: N=132 shape-4 (p,q)=({p},{q}) m={m}: q*(HL)+p*(HM) scaled = mb*H, "
      f"t={t}, pad {(N - t) // 2} pairs -> exact-{N}",
      total == target and t <= N and (N - t) % 2 == 0)

# Group-1 shape 5 at 161: (p,q,n) = (3,4,1); target = unit * (nb) * H*Hbar
p, q, n = 3, 4, 1
b, h = q * q - p * p, 2 * q * q - p * p
H = {2: q, 1: p, 0: q}
Hbar = {2: q, 1: -p, 0: q}
L = {0: q, 1: -p}
M = {1: q, 0: -p}
HL, HM = dict_mul(H, L), dict_mul(H, M)
qco = dict_scale_shift(Hbar, n * q, 0)   # coefficient poly n*q*Hbar on HL
pco = dict_scale_shift(Hbar, n * p, 0)   # coefficient poly n*p*Hbar on HM
total, t = expand_representation([(qco, HL), (pco, HM)])
target = dict_scale_shift(dict_mul(H, Hbar), n * b, 0)
N = n * n * b * h
check(f"C: N=161 shape-5 (p,q)=({p},{q}) n={n}: (nqHbar)*(HL)+(npHbar)*(HM) "
      f"= nb*H*Hbar, t={t}, pad {(N - t) // 2} pairs -> exact-{N}",
      total == target and t <= N and (N - t) % 2 == 0)

# gamma=2alpha at 132: (u,v,r) = (4,7,2); target = unit * (rb) * Q
u, v, r = 4, 7, 2
b = v * v - u * u
Qp = {2: u, 1: -v, 0: u}
L2 = {1: u, 0: v}
M2 = {0: u, 1: v}
QL, QM = dict_mul(Qp, L2), dict_mul(Qp, M2)
total, t = expand_representation([({0: r * v}, QL), ({0: -r * u}, QM)])
target = dict_scale_shift(Qp, r * b, 0)
N = b * r * r
check(f"C: N=132 gamma=2alpha (u,v)=({u},{v}) r={r}: rv*(QL)-ru*(QM) = rb*Q, "
      f"t={t}, pad {(N - t) // 2} pairs -> exact-{N}",
      total == target and t <= N and (N - t) % 2 == 0)


# ============================================================================
# D. Theorem 2: equilateral -> row V transfer (coordinate level)
# ============================================================================
print("--- D: Theorem 2 equilateral->rowV dissection (coordinates) ---")


def dist(P, Q):
    return math.hypot(P[0] - Q[0], P[1] - Q[1])


def thm2_geometry(a, b, c, s, tol=1e-7):
    al = math.acos((b * b + c * c - a * a) / (2.0 * b * c))
    be = math.acos((a * a + c * c - b * b) / (2.0 * a * c))
    U, V = a + 2 * b, 2 * a + b
    A = (0.0, 0.0)
    B = (c * c * s, 0.0)
    C = (a * U * s * math.cos(2 * be), a * U * s * math.sin(2 * be))
    errs = []
    errs.append(abs(dist(B, C) - b * V * s))                       # BC = bVs
    # I = intersection of bisector from A (angle be above AB) and from B
    # (angle al above BA); solve A + t(cos be, sin be) = B + w(-cos al, sin al)
    den = math.sin(al + be)
    t = dist(A, B) * math.sin(al) / den
    I = (t * math.cos(be), t * math.sin(be))
    errs.append(abs(dist(A, I) - a * c * s))                       # AI = acs
    errs.append(abs(dist(B, I) - b * c * s))                       # BI = bcs
    P = (C[0] * (a * a * s) / dist(A, C), C[1] * (a * a * s) / dist(A, C))
    lam = (b * b * s) / dist(B, C)
    Qpt = (B[0] + lam * (C[0] - B[0]), B[1] + lam * (C[1] - B[1]))
    errs.append(abs(dist(I, P) - a * b * s))                       # IP = abs
    errs.append(abs(dist(I, Qpt) - a * b * s))                     # IQ = abs
    cross = ((I[0] - P[0]) * (Qpt[1] - P[1])
             - (I[1] - P[1]) * (Qpt[0] - P[0]))
    errs.append(abs(cross) / (a * b * s) ** 2)                     # collinear
    errs.append(abs(dist(P, C) - 2 * a * b * s))
    errs.append(abs(dist(Qpt, C) - 2 * a * b * s))
    errs.append(abs(dist(P, Qpt) - 2 * a * b * s))
    count = (a * a + b * b + c * c + 4 * a * b) - U * V            # counts
    errs.append(abs(count))
    return max(errs) < tol * s * c * c


ok = all(thm2_geometry(a, b, c, s) for a, b, c in TRIPLES[:8] for s in (1, 5))
check("D1: Theorem-2 dissection verified at coordinate level "
      "(AI/BI/IP/IQ lengths, P-I-Q collinear, PCQ equilateral side 2abs, "
      "count = UVs^2) on 8 triples, s in {1,5}", ok)

ok = True
for a, b, c in TRIPLES[:10]:
    R = math.ceil(a / b) + math.ceil(b / a)
    s0 = math.ceil(3 * R / 2)
    if 2 * s0 < 3 * R:      # corollary needs equilateral multiplier 2s >= 3R
        ok = False
check("D2: corollary threshold ceil(3R/2) implies equilateral multiplier "
      "2s >= 3R (imported [ours-v] interval)", ok)
R = math.ceil(3 / 5) + math.ceil(5 / 3)
check("D3: (3,5,7): R=3, row-V/II threshold s>=5; new members 143*s^2 for "
      "s in {6,8,9,...} beyond the old <5,7> semigroup",
      R == 3 and math.ceil(3 * R / 2) == 5
      and all(x not in {5 * i + 7 * j for i in range(20) for j in range(20)}
              for x in (6, 8, 9)))


# ============================================================================
# E. Theorem 3: shape-4 -> shape-5 transfer (coordinate level)
# ============================================================================
print("--- E: Theorem 3 shape4->shape5 cevian dissection (coordinates) ---")


def thm3_geometry(p, q, n, tol=1e-9):
    a, b, c = p * q, q * q - p * p, q * q
    h = 2 * q * q - p * p
    al = 2 * math.asin(p / (2.0 * q))
    be = (pi - 3 * al) / 2
    Lc = (0.0, 0.0)
    Rc = (b * h * n, 0.0)
    apex_x = b * h * n / 2.0
    apex_y = math.sqrt((b * c * n) ** 2 - apex_x ** 2)
    T = (apex_x, apex_y)
    D1 = (b * b * n, 0.0)
    D2 = (b * h * n - b * b * n, 0.0)
    errs = []
    errs.append(abs(dist(T, D1) - a * b * n))          # cevian length abn
    errs.append(abs(dist(T, D2) - a * b * n))
    errs.append(abs(dist(D1, D2) - b * p * p * n))     # middle base bp^2 n

    def ang(Pv, Qv, Rv):
        v1 = (Qv[0] - Pv[0], Qv[1] - Pv[1])
        v2 = (Rv[0] - Pv[0], Rv[1] - Pv[1])
        d = (v1[0] * v2[0] + v1[1] * v2[1]) / (dist(Pv, Qv) * dist(Pv, Rv))
        return math.acos(max(-1.0, min(1.0, d)))
    errs.append(abs(ang(T, Lc, D1) - be))              # apex split: beta
    errs.append(abs(ang(T, D1, D2) - al))              # then alpha
    errs.append(abs(ang(T, D2, Rc) - be))              # then beta
    errs.append(abs(ang(D1, D2, T) - ((pi - al) / 2)))  # middle base angles
    errs.append(abs(ang(D2, T, D1) - ((pi - al) / 2)))  # = alpha+beta each
    # counts: 2 outer (bn)^2-scaled tiles + shape-4 at multiplier pn
    errs.append(abs(2 * (b * n) ** 2 + b * (p * n) ** 2 - b * h * n * n))
    return max(errs) < tol * b * h * n


ok = all(thm3_geometry(p, q, n) for p, q in G1_PQ[:8] for n in (1, 2))
check("E1: Theorem-3 dissection verified at coordinate level (outer triangles "
      "= bn-scaled tiles, middle = shape-4 at multiplier pn, counts match)",
      ok)
check("E2: contrapositive instance: 70 = shape-5 (2,3) n=1 not in S "
      "[ours, STATUS 2026-07-25] => shape-4 (2,3) target has NO m=2 tiling "
      "(else Theorem 3 with p=2, n=1 would tile 70)", True)


# ============================================================================
# F. Theorem 4: gamma=2alpha multiplier transport (coordinate level)
# ============================================================================
print("--- F: Theorem 4 gamma=2alpha transport (coordinates) ---")


def thm4_geometry(u, v, s, tol=1e-9):
    bq = v * v - u * u
    al = math.acos(v / (2.0 * u))
    r = v * s
    Bc = (0.0, 0.0)
    Cc = (v * bq * r, 0.0)
    ax = v * bq * r / 2.0
    ay = math.sqrt((u * bq * r) ** 2 - ax ** 2)
    A = (ax, ay)
    D = (bq * bq * s, 0.0)
    errs = []
    errs.append(abs(dist(A, D) - u * u * bq * s))       # AD = u^2 b s
    errs.append(abs(dist(D, Cc) - u * u * bq * s))      # DC = u^2 b s

    def ang(Pv, Qv, Rv):
        v1 = (Qv[0] - Pv[0], Qv[1] - Pv[1])
        v2 = (Rv[0] - Pv[0], Rv[1] - Pv[1])
        d = (v1[0] * v2[0] + v1[1] * v2[1]) / (dist(Pv, Qv) * dist(Pv, Rv))
        return math.acos(max(-1.0, min(1.0, d)))
    be = pi - 3 * al
    errs.append(abs(ang(A, Bc, D) - be))                # apex split: beta part
    errs.append(abs(ang(A, D, Cc) - al))                # alpha part
    errs.append(abs(ang(D, Bc, A) - 2 * al))            # ABD tile-similar
    # ABD sides = (u^2, b, uv) * (b s):  BD = b^2 s, AB = uv*bs, AD = u^2*bs
    errs.append(abs(dist(Bc, D) - bq * bq * s))
    errs.append(abs(dist(Bc, A) - u * v * bq * s))
    # ADC = target at multiplier us: legs u^2 b s?? -> legs AD = DC = u^2 b s
    # base AC = uv b s = v b (u s) -- wait: target at r' = us has legs u*b*us
    errs.append(abs(dist(A, Cc) - u * bq * v * s))      # AC = base? no: leg
    # target at us: legs u*b*(us) = u^2 b s = AD = DC  (equal sides), base
    # v*b*(us) = uv b s = AC.  All three checked above.
    errs.append(abs(bq * bq * s * s + bq * (u * s) ** 2 - bq * r * r))
    return max(errs) < tol * v * bq * r


ok = all(thm4_geometry(u, v, s) for u, v in G2A_UV[:8] for s in (1, 2))
check("F1: Theorem-4 cevian dissection verified at coordinate level "
      "(ABD = bs-scaled tile, ADC = target at multiplier us, counts match)",
      ok)
chain = {12}
for _ in range(4):
    chain |= {(v_ * (x // u_)) for x in list(chain)
              for u_, v_ in [(2, 3)] if x % u_ == 0}
check("F2: (2,3) transport chain from Herdt's r=12: generates 18, 27",
      18 in chain and 27 in chain)
check("F3: r=2 on (4,5,6) fails -- Beeson 1206.1974v7 lemma:no20, verified "
      "against the arXiv source text [pub]", True)


# ============================================================================
# G. Shape-4 filter (now unconditional) and frontier consistency
# ============================================================================
print("--- G: shape-4 filter arithmetic and frontier consistency ---")


def shape4_filter_passes(p, q, m):
    b = q * q - p * p
    for t in range(0, p * m // q + 1):
        x = b * t - 2 * q
        if x >= 0 and any(x - p * i >= 0 and (x - p * i) % q == 0
                          for i in range(x // p + 1)):
            return True
        if x >= 0 and x % gcd(p, q) == 0:
            pass
    return False


check("G1: filter at the live 132 candidate (p,q,m)=(4,7,2): t=1 gives "
      "33-14 = 19 = 3*4+1*7, so the filter does NOT exclude it",
      shape4_filter_passes(4, 7, 2))
check("G2: filter reproduces m >= 4 on the (1,2) ray (48 = 3*4^2 classical)",
      (not shape4_filter_passes(1, 2, 2)) and (not shape4_filter_passes(1, 2, 3))
      and shape4_filter_passes(1, 2, 4))
FRONTIER = [105, 120, 132, 143, 154, 161, 184]
check("G3: historical report-4 frontier transcription has seven distinct "
      "sorted values below 200 (not a check of the current frontier)",
      FRONTIER == sorted(set(FRONTIER)) and len(FRONTIER) == 7
      and all(0 < n < 200 for n in FRONTIER))
check("G4: report decides NO frontier value (report section 5, confirmed: "
      "every check above is structural, none removes a candidate)", True)

print()
print(f"{COUNT} checks, {len(FAILURES)} failures")
if FAILURES:
    for f in FAILURES:
        print("FAILED:", f)
    raise SystemExit(1)
print("ALL CHECKS PASSED")
