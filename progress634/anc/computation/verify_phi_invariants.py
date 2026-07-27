#!/usr/bin/env python3
"""
Exact / high-precision numeric verification of the boundary invariants Phi
and Phi' for tilings of a triangle by congruent copies of a tile (a,b,c)
opposite angles (alpha,beta,gamma), gamma = 2*pi/3, c^2 = a^2+ab+b^2,
alpha+beta = pi/3.

Every directed edge direction in such a tiling is theta = j*(pi/3) + m*alpha,
j in Z (mod 6), m in Z.  Two candidate boundary characters:
    chi(j,m)       = (-1)^j        -> Phi   (Beeson-Zhang, Sec 4.2 of the source)
    chi'(j,m)      = (-1)^(j+m)    -> Phi'  (candidate invariant, to be checked)

Run with:
    uv run --with sympy python verify_phi_invariants.py
"""

from fractions import Fraction
import mpmath as mp

mp.mp.dps = 60                     # working precision (>= 50 significant digits)
PRINT_DPS = 50                     # digits used when printing coordinates
CLOSURE_TOL = mp.mpf('1e-45')      # tolerance for "vector sum == 0" checks
MATCH_TOL = mp.mpf('1e-30')        # tolerance for numeric (j,m) direction matching

results = {}                       # item number -> bool (PASS/FAIL)


def hr(title):
    print("\n" + "=" * 78)
    print(title)
    print("=" * 78)


# ----------------------------------------------------------------------
# (j,m) lattice arithmetic.  A direction is theta = j*(pi/3) + m*alpha.
# ----------------------------------------------------------------------

def jm_add(t1, t2):
    return (t1[0] + t2[0], t1[1] + t2[1])


def jm_scale(t, k):
    return (t[0] * k, t[1] * k)


def jm_value(t, alpha):
    j, m = t
    return j * mp.pi / 3 + m * alpha


def chi(j, m):
    """(-1)^j -- the Beeson-Zhang character (Phi)."""
    return 1 if j % 2 == 0 else -1


def chi_prime(j, m):
    """(-1)^(j+m) -- the candidate character (Phi')."""
    return 1 if (j + m) % 2 == 0 else -1


def chi_m_only(j, m):
    """(-1)^m -- the candidate that must FAIL the reversal test."""
    return 1 if m % 2 == 0 else -1


ALPHA = (0, 1)
BETA = (1, -1)      # beta = pi/3 - alpha  =  (1,0) - (0,1)
PI = (3, 0)


def ang_diff(a, b):
    """a - b wrapped into (-pi, pi]."""
    twopi = 2 * mp.pi
    d = a - b
    d = d - twopi * mp.floor(d / twopi + mp.mpf('0.5'))
    return d


def match_jm(theta, alpha, jrange=range(0, 6), mrange=range(-5, 6), tol=MATCH_TOL):
    """Find integer (j,m) with j*pi/3+m*alpha == theta (mod 2*pi), within tol."""
    best = None
    for j in jrange:
        for m in mrange:
            cand = j * mp.pi / 3 + m * alpha
            d = abs(ang_diff(theta, cand))
            if best is None or d < best[0]:
                best = (d, j, m)
    if best[0] > tol:
        raise RuntimeError(f"no (j,m) match within tol={tol}: best residual {best[0]} "
                            f"at (j,m)=({best[1]},{best[2]})")
    return best[1], best[2], best[0]


def make_tile(a, b, c):
    """Return (alpha, beta) at working precision, after checking the Eisenstein relation."""
    amp, bmp, cmp_ = mp.mpf(a), mp.mpf(b), mp.mpf(c)
    assert abs(cmp_ ** 2 - (amp ** 2 + amp * bmp + bmp ** 2)) < mp.mpf('1e-50'), \
        f"tile ({a},{b},{c}) does not satisfy c^2 = a^2+ab+b^2"
    alpha = mp.acos((amp + 2 * bmp) / (2 * cmp_))
    beta = mp.pi / 3 - alpha
    return alpha, beta


# ========================================================================
# ITEM 1 -- cancellation character check (symbolic / trivial)
# ========================================================================

def verify_item1():
    hr("ITEM 1: Cancellation character check   [chi(theta+pi) = -chi(theta)]")
    print("theta -> theta+pi corresponds to (j,m) -> (j+3,m) in the (j,m) lattice")
    print("(since pi = 3*(pi/3) + 0*alpha = (3,0)).")
    print("Requirement for a valid cancellation character: chi(j+3,m) == -chi(j,m).\n")

    ok_phi = True
    ok_phi2 = True
    m_only_ever_flips = False
    for j in range(-10, 11):
        for m in range(-10, 11):
            if chi(j + 3, m) != -chi(j, m):
                ok_phi = False
            if chi_prime(j + 3, m) != -chi_prime(j, m):
                ok_phi2 = False
            if chi_m_only(j + 3, m) == -chi_m_only(j, m):
                m_only_ever_flips = True   # this should NEVER happen

    print(f"  (-1)^j       : chi(j+3,m) = -chi(j,m)  for all tested (j,m)? {ok_phi}"
          f"   -> {'PASS' if ok_phi else 'FAIL'}")
    print(f"  (-1)^(j+m)   : chi(j+3,m) = -chi(j,m)  for all tested (j,m)? {ok_phi2}"
          f"   -> {'PASS' if ok_phi2 else 'FAIL'}")
    print(f"  (-1)^m       : chi(j+3,m) = -chi(j,m)  for ANY tested (j,m)? {m_only_ever_flips}"
          f"  (expected False: since (-1)^m does not depend on j, chi(j+3,m)==chi(j,m) always)")
    m_only_correctly_fails = not m_only_ever_flips
    print(f"                 -> candidate correctly REJECTED: "
          f"{'PASS' if m_only_correctly_fails else 'FAIL (unexpectedly satisfies reversal)'}")

    item1_pass = ok_phi and ok_phi2 and m_only_correctly_fails
    print(f"\nITEM 1 RESULT: {'PASS' if item1_pass else 'FAIL'}")
    results[1] = item1_pass
    return item1_pass


# ========================================================================
# ITEM 2 -- one-tile formula, numeric, high precision, 4 tiles
# ========================================================================

TILES = [(3, 5, 7), (7, 8, 13), (5, 16, 19), (16, 39, 49)]


def verify_item2():
    hr("ITEM 2: One-tile formula  (grid of (j0,m0) in 0..5 x -2..2, both orientations, 4 tiles)")
    overall_pass = True

    for (a, b, c) in TILES:
        alpha, beta = make_tile(a, b, c)
        Delta = a + c - b
        ambc = a - b - c

        n_checked = 0
        formula_ok = True
        sign_relation_ok = True
        closure_ok = True
        sample = None

        for j0 in range(6):
            for m0 in range(-2, 3):
                for orient in ("CCW", "reflected"):
                    if orient == "CCW":
                        # a at (j0,m0); b at +(1,0); c at +(1,0)+(3,-1)=(4,-1)
                        edges_jm = [(a, j0, m0), (b, j0 + 1, m0), (c, j0 + 4, m0 - 1)]
                    else:
                        # a at (j0,m0); c at +(2,1); b at +(2,1)+(3,-1)=(5,0)
                        edges_jm = [(a, j0, m0), (c, j0 + 2, m0 + 1), (b, j0 + 5, m0)]

                    Phi = sum(length * chi(j, m) for length, j, m in edges_jm)
                    Phi2 = sum(length * chi_prime(j, m) for length, j, m in edges_jm)
                    n_checked += 1

                    sign_phi = 1 if Phi == Delta else (-1 if Phi == -Delta else 0)
                    sign_phi2 = 1 if Phi2 == ambc else (-1 if Phi2 == -ambc else 0)
                    if sign_phi == 0 or sign_phi2 == 0:
                        formula_ok = False
                    else:
                        expected_sign_phi2 = sign_phi * (1 if m0 % 2 == 0 else -1)
                        if sign_phi2 != expected_sign_phi2:
                            sign_relation_ok = False

                    # numeric vector-closure check (high precision)
                    thetas = [jm_value((j, m), alpha) for _, j, m in edges_jm]
                    lengths = [length for length, _, _ in edges_jm]
                    vx = sum(L * mp.cos(t) for L, t in zip(lengths, thetas))
                    vy = sum(L * mp.sin(t) for L, t in zip(lengths, thetas))
                    if mp.sqrt(vx ** 2 + vy ** 2) > CLOSURE_TOL:
                        closure_ok = False

                    if j0 == 0 and m0 == 0:
                        sample = sample or {}
                        sample[orient] = (Phi, sign_phi, Phi2, sign_phi2)

        tile_pass = formula_ok and sign_relation_ok and closure_ok
        print(f"\ntile (a,b,c)=({a},{b},{c}):  Delta=a+c-b={Delta},  a-b-c={ambc}")
        print(f"  combos checked (j0 in 0..5, m0 in -2..2, 2 orientations): {n_checked}")
        for orient, (Phi, sp, Phi2, sp2) in sample.items():
            print(f"    sample j0=0,m0=0,{orient:9s}: Phi={Phi:>4} (sign {sp:+d}),  "
                  f"Phi'={Phi2:>4} (sign {sp2:+d})")
        print(f"  Phi=+-Delta and Phi'=+-(a-b-c) for ALL combos:      "
              f"{'PASS' if formula_ok else 'FAIL'}")
        print(f"  sign relation  sign_Phi' = sign_Phi*(-1)^m0 for ALL combos: "
              f"{'PASS' if sign_relation_ok else 'FAIL'}")
        print(f"  vector closure |sum of directed edge vectors| < {CLOSURE_TOL} "
              f"for ALL combos: {'PASS' if closure_ok else 'FAIL'}")
        print(f"  -> tile result: {'PASS' if tile_pass else 'FAIL'}")
        overall_pass = overall_pass and tile_pass

    results[2] = overall_pass
    print(f"\nITEM 2 RESULT: {'PASS' if overall_pass else 'FAIL'}")
    return overall_pass


# ========================================================================
# ITEM 3 -- boundary evaluation, row I
# ========================================================================

def verify_item3():
    hr("ITEM 3: Boundary evaluation, ROW I  (isosceles T = k(c,c,U), U=a+2b)")
    a, b, c = 5, 3, 7
    k = 3
    alpha, beta = make_tile(a, b, c)
    U = a + 2 * b
    kU, kc = k * U, k * c

    edges_jm = [(kU, 0, 0), (kc, 3, -1), (kc, 3, 1)]
    Phi = sum(length * chi(j, m) for length, j, m in edges_jm)
    Phi2 = sum(length * chi_prime(j, m) for length, j, m in edges_jm)

    thetas = [jm_value((j, m), alpha) for _, j, m in edges_jm]
    lengths = [length for length, _, _ in edges_jm]
    vx = sum(L * mp.cos(t) for L, t in zip(lengths, thetas))
    vy = sum(L * mp.sin(t) for L, t in zip(lengths, thetas))
    closure_err = mp.sqrt(vx ** 2 + vy ** 2)
    closure_ok = closure_err < CLOSURE_TOL

    Delta = a + c - b
    ambc = a - b - c
    N = k * U
    M = Fraction(Phi, Delta)
    M2 = Fraction(Phi2, ambc)

    print(f"tile (a,b,c)=({a},{b},{c}),  k={k}   ->  U=a+2b={U},  T=(kc,kc,kU)=({kc},{kc},{kU})")
    print(f"Phi(dT)  = k(U-2c) = {Phi}    (expected -9)")
    print(f"Phi'(dT) = k(U+2c) = {Phi2}   (expected 75)")
    print(f"Delta = a+c-b = {Delta}   (expected 9);   a-b-c = {ambc}   (expected -5)")
    print(f"M  = Phi/Delta     = {M}    (expected -1)")
    print(f"M2 = Phi'/(a-b-c)  = {M2}   (expected -15)")
    print(f"N = kU = {N}   (expected 33)")
    print(f"vector closure |sum| = {mp.nstr(closure_err, 5)}  "
          f"(< {CLOSURE_TOL}: {'PASS' if closure_ok else 'FAIL'})")

    Mi, M2i = int(M), int(M2)
    parities = {"M": Mi % 2, "N": N % 2, "M2": M2i % 2}
    parity_ok = parities["M"] == parities["N"] == parities["M2"]
    print(f"M mod 2 = {parities['M']}, N mod 2 = {parities['N']}, M2 mod 2 = {parities['M2']}  "
          f"-> all congruent: {'PASS' if parity_ok else 'FAIL'}")

    expected_ok = (Phi == -9 and Phi2 == 75 and Delta == 9 and ambc == -5
                   and Mi == -1 and M2i == -15 and N == 33)

    item3_pass = closure_ok and parity_ok and expected_ok
    print(f"\nITEM 3 RESULT: {'PASS' if item3_pass else 'FAIL'}")
    results[3] = item3_pass
    return item3_pass


# ========================================================================
# ITEM 4 -- known-tiling consistency: 4-reptiling of (7,8,13) x2
# ========================================================================

def verify_item4():
    hr("ITEM 4: Known-tiling consistency -- 4-reptiling of tile (7,8,13) scaled x2")
    a, b, c = 7, 8, 13
    alpha, beta = make_tile(a, b, c)
    Delta = a + c - b
    ambc = a - b - c
    a2, b2, c2 = 2 * a, 2 * b, 2 * c

    # T's own CCW boundary, directly, starting a-edge at (j0,m0)=(0,0)
    T_edges_jm = [(a2, 0, 0), (b2, 1, 0), (c2, 4, -1)]
    Phi_T = sum(L * chi(j, m) for L, j, m in T_edges_jm)
    Phi2_T = sum(L * chi_prime(j, m) for L, j, m in T_edges_jm)

    # explicit coordinates (mpmath, printed at 50 digits)
    P0 = (mp.mpf(0), mp.mpf(0))
    th_a = jm_value((0, 0), alpha)
    P1 = (P0[0] + a2 * mp.cos(th_a), P0[1] + a2 * mp.sin(th_a))
    th_b = jm_value((1, 0), alpha)
    P2 = (P1[0] + b2 * mp.cos(th_b), P1[1] + b2 * mp.sin(th_b))
    th_c = jm_value((4, -1), alpha)
    Pclose = (P2[0] + c2 * mp.cos(th_c), P2[1] + c2 * mp.sin(th_c))
    closure_T = mp.sqrt((Pclose[0] - P0[0]) ** 2 + (Pclose[1] - P0[1]) ** 2)
    closure_T_ok = closure_T < CLOSURE_TOL

    print(f"tile (a,b,c)=({a},{b},{c}),  T = tile x2 = ({a2},{b2},{c2}),  alpha = "
          f"{mp.nstr(alpha, PRINT_DPS)}")
    print("T vertices (CCW, 50 digits):")
    print(f"  P0 = ({mp.nstr(P0[0], PRINT_DPS)}, {mp.nstr(P0[1], PRINT_DPS)})")
    print(f"  P1 = ({mp.nstr(P1[0], PRINT_DPS)}, {mp.nstr(P1[1], PRINT_DPS)})")
    print(f"  P2 = ({mp.nstr(P2[0], PRINT_DPS)}, {mp.nstr(P2[1], PRINT_DPS)})")
    print(f"  boundary closure |Pclose-P0| = {mp.nstr(closure_T, 5)}  "
          f"(< {CLOSURE_TOL}: {'PASS' if closure_T_ok else 'FAIL'})")

    def midpoint(P, Q):
        return ((P[0] + Q[0]) / 2, (P[1] + Q[1]) / 2)

    Ma, Mb, Mc = midpoint(P0, P1), midpoint(P1, P2), midpoint(P2, P0)
    print("Midpoints (50 digits):")
    print(f"  Ma = ({mp.nstr(Ma[0], PRINT_DPS)}, {mp.nstr(Ma[1], PRINT_DPS)})")
    print(f"  Mb = ({mp.nstr(Mb[0], PRINT_DPS)}, {mp.nstr(Mb[1], PRINT_DPS)})")
    print(f"  Mc = ({mp.nstr(Mc[0], PRINT_DPS)}, {mp.nstr(Mc[1], PRINT_DPS)})")

    def signed_area2(pts):
        (x0, y0), (x1, y1), (x2, y2) = pts
        return (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)

    def ensure_ccw(pts):
        return list(pts) if signed_area2(pts) > 0 else [pts[0], pts[2], pts[1]]

    subtiles_raw = {
        "corner@P0": [P0, Ma, Mc],
        "corner@P1": [P1, Mb, Ma],
        "corner@P2": [P2, Mc, Mb],
        "middle": [Ma, Mb, Mc],
    }

    # analytic prediction, derived by hand from the midpoint/medial-triangle theorem
    # (see report): corner tiles are translates (same (j,m) set as the unit tile),
    # the middle tile is the unit tile rotated by pi (each direction shifted by (3,0),
    # i.e. j -> j+3). j is only meaningful mod 6, so (7,-1) is reduced to (1,-1) here
    # to match match_jm's canonical j-range of 0..5 (chi/chi' depend only on j's parity,
    # so this reduction changes nothing about the Phi/Phi' values).
    analytic_jm = {
        "corner@P0": {(0, 0), (1, 0), (4, -1)},
        "corner@P1": {(1, 0), (4, -1), (0, 0)},
        "corner@P2": {(4, -1), (0, 0), (1, 0)},
        "middle": {(1, -1), (3, 0), (4, 0)},
    }

    total_Phi = 0
    total_Phi2 = 0
    all_ok = True
    print("\nSub-tile boundary matching (numeric direction -> (j,m), tol=1e-30):")
    for name, raw_pts in subtiles_raw.items():
        pts = ensure_ccw(raw_pts)
        edges = []
        for i in range(3):
            P, Q = pts[i], pts[(i + 1) % 3]
            dx, dy = Q[0] - P[0], Q[1] - P[1]
            length = mp.sqrt(dx ** 2 + dy ** 2)
            theta = mp.atan2(dy, dx)
            edges.append((length, theta))

        matched = []
        for length, theta in edges:
            j, m, resid = match_jm(theta, alpha, mrange=range(-3, 4))
            matched.append((length, j, m, resid))

        matched_set = {(j, m) for _, j, m, _ in matched}
        analytic_match = (matched_set == analytic_jm[name])

        int_lengths = [int(mp.nint(length)) for length, _, _, _ in matched]
        len_ok = all(abs(length - round_len) < mp.mpf('1e-40')
                     for (length, _, _, _), round_len in zip(matched, int_lengths))

        Phi_i = sum(L * chi(j, m) for L, (_, j, m, _) in zip(int_lengths, matched))
        Phi2_i = sum(L * chi_prime(j, m) for L, (_, j, m, _) in zip(int_lengths, matched))
        max_resid = max(r for _, _, _, r in matched)

        ok = (abs(Phi_i) == Delta) and (abs(Phi2_i) == abs(ambc)) and analytic_match and len_ok
        all_ok = all_ok and ok
        total_Phi += Phi_i
        total_Phi2 += Phi2_i

        edge_desc = ", ".join(f"len={L},(j,m)=({j},{m})"
                               for L, (_, j, m, _) in zip(int_lengths, matched))
        print(f"  [{name:10s}] {edge_desc}   max_resid={mp.nstr(max_resid, 3)}   "
              f"Phi={Phi_i:>4}  Phi'={Phi2_i:>4}   analytic-match={analytic_match}   "
              f"{'OK' if ok else 'MISMATCH'}")

    print(f"\nSum over 4 sub-tiles:  Phi_sum  = {total_Phi:>4}   (T direct: {Phi_T})")
    print(f"                       Phi'_sum = {total_Phi2:>4}   (T direct: {Phi2_T})")
    sums_ok = (total_Phi == Phi_T) and (total_Phi2 == Phi2_T)
    print(f"interior-edge cancellation (sum of sub-tiles == T boundary): "
          f"{'PASS' if sums_ok else 'FAIL'}")

    item4_pass = closure_T_ok and all_ok and sums_ok
    print(f"\nITEM 4 RESULT: {'PASS' if item4_pass else 'FAIL'}")
    results[4] = item4_pass
    return item4_pass


# ========================================================================
# ITEM 5 -- rows II-V boundary evaluations (new data)
# ========================================================================

def build_row_directions(angle_tuples):
    """Exact (j,m) directions for sides s1,s2,s3 (CCW), given the (j,m)-tuples
    of the three angles theta1,theta2,theta3 opposite s1,s2,s3 respectively.
    Turn between s_i and s_{i+1} = pi - theta_{other index}. See report for the
    (i -> i+1 turn uses the angle opposite the third side) rule derivation."""
    th1, th2, th3 = angle_tuples
    d1 = (0, 0)
    turn1 = (PI[0] - th3[0], PI[1] - th3[1])       # vertex between s1,s2: angle opposite s3
    d2 = jm_add(d1, turn1)
    turn2 = (PI[0] - th1[0], PI[1] - th1[1])       # vertex between s2,s3: angle opposite s1
    d3 = jm_add(d2, turn2)
    turn3 = (PI[0] - th2[0], PI[1] - th2[1])       # closing vertex: angle opposite s2
    dclose = jm_add(d3, turn3)
    assert dclose[1] == 0 and dclose[0] % 6 == 0, f"row closure failed: {dclose}"
    return [d1, d2, d3]


ROWS = {
    "II": dict(
        angles=[ALPHA, jm_scale(ALPHA, 2), jm_scale(BETA, 3)],
        sides=lambda a, b, c, U, V, W: [c ** 2, U * c, 3 * b * W],
        N=lambda a, b, c, U, V, W, k: Fraction(3 * k ** 2 * U * W),
    ),
    "III": dict(
        angles=[ALPHA, jm_scale(BETA, 2), jm_add(jm_scale(ALPHA, 2), BETA)],
        sides=lambda a, b, c, U, V, W: [a * c, b * V, W * c],
        N=lambda a, b, c, U, V, W, k: Fraction(k ** 2 * V * W),
    ),
    "IV": dict(
        angles=[ALPHA, jm_add(ALPHA, BETA), jm_add(ALPHA, jm_scale(BETA, 2))],
        sides=lambda a, b, c, U, V, W: [a, c, W],
        N=lambda a, b, c, U, V, W, k: Fraction(k ** 2 * W, b),
    ),
    "V": dict(
        angles=[jm_scale(ALPHA, 2), jm_scale(BETA, 2), jm_add(ALPHA, BETA)],
        sides=lambda a, b, c, U, V, W: [a * U, b * V, c ** 2],
        N=lambda a, b, c, U, V, W, k: Fraction(k ** 2 * U * V),
    ),
}


def verify_item5():
    hr("ITEM 5: Rows II-V boundary evaluations (new data, k=1)")
    table_rows = []
    for tile in [(3, 5, 7), (7, 8, 13)]:
        a, b, c = tile
        alpha, beta = make_tile(a, b, c)
        U, V, W = a + 2 * b, 2 * a + b, a + b
        Delta = a + c - b
        ambc = a - b - c

        for row_name, spec in ROWS.items():
            angle_tuples = spec["angles"]
            side_lengths = spec["sides"](a, b, c, U, V, W)   # exact ints
            dirs_jm = build_row_directions(angle_tuples)

            # --- independent numeric construction (real coordinates) ---
            angle_vals = [jm_value(t, alpha) for t in angle_tuples]
            dir_vals = [mp.mpf(0)]
            dir_vals.append(dir_vals[0] + (mp.pi - angle_vals[2]))
            dir_vals.append(dir_vals[1] + (mp.pi - angle_vals[0]))

            pts = [(mp.mpf(0), mp.mpf(0))]
            for i in range(3):
                L, d, prev = side_lengths[i], dir_vals[i], pts[-1]
                pts.append((prev[0] + L * mp.cos(d), prev[1] + L * mp.sin(d)))
            closure_err = mp.sqrt((pts[3][0] - pts[0][0]) ** 2 + (pts[3][1] - pts[0][1]) ** 2)
            closure_ok = closure_err < CLOSURE_TOL

            los_ratios = [mp.mpf(side_lengths[i]) / mp.sin(angle_vals[i]) for i in range(3)]
            los_ok = (max(los_ratios) - min(los_ratios)) < mp.mpf('1e-40')

            matched_jm = []
            for dv in dir_vals:
                j, m, resid = match_jm(dv, alpha, mrange=range(-8, 9))
                matched_jm.append((j, m))
            jm_cross_check = (matched_jm == list(dirs_jm))

            # --- Phi / Phi' from the exact lattice bookkeeping ---
            Phi = sum(L * chi(j, m) for L, (j, m) in zip(side_lengths, dirs_jm))
            Phi2 = sum(L * chi_prime(j, m) for L, (j, m) in zip(side_lengths, dirs_jm))

            M = Fraction(Phi, Delta)
            M2 = Fraction(Phi2, ambc)
            N = spec["N"](a, b, c, U, V, W, 1)

            row_ok = closure_ok and los_ok and jm_cross_check
            table_rows.append(dict(tile=tile, row=row_name, Phi=Phi, Phi2=Phi2,
                                    Delta=Delta, ambc=ambc, M=M, M2=M2, N=N,
                                    dirs_jm=dirs_jm, geom_ok=row_ok))

    def parity(fr):
        return (fr.numerator % 2) if fr.denominator == 1 else None

    def pstr(p):
        return "n/a" if p is None else ("odd" if p else "even")

    hdr = (f"{'tile':>11} {'row':>4} {'sides(j,m)':>26} {'Phi':>6} {'Phi/D=M':>9} "
           f"{'Phi2':>7} {'Phi2/amb=M2':>12} {'N':>10} {'M par':>5} {'N par':>5} "
           f"{'M2 par':>6} {'geom':>5}")
    print(hdr)
    print("-" * len(hdr))
    for r in table_rows:
        dirs_str = ",".join(f"({j},{m})" for j, m in r["dirs_jm"])
        Mp, Np, M2p = parity(r["M"]), parity(r["N"]), parity(r["M2"])
        print(f"{str(r['tile']):>11} {r['row']:>4} {dirs_str:>26} {r['Phi']:>6} "
              f"{str(r['M']):>9} {r['Phi2']:>7} {str(r['M2']):>12} {str(r['N']):>10} "
              f"{pstr(Mp):>5} {pstr(Np):>5} {pstr(M2p):>6} "
              f"{'OK' if r['geom_ok'] else 'FAIL':>5}")

    item5_geom_ok = all(r["geom_ok"] for r in table_rows)
    print(f"\n(geometry: closure + law-of-sines + numeric-(j,m)-match all consistent: "
          f"{'PASS' if item5_geom_ok else 'FAIL'})")
    print("Per the task spec, rows II-V integrality/parity are reported as NEW data points "
          "(no pass/fail judgement is made on them).")
    results[5] = item5_geom_ok
    return table_rows, item5_geom_ok


# ========================================================================
# MAIN
# ========================================================================

def main():
    print("Verification of Phi / Phi' boundary invariants")
    print(f"mpmath working precision: {mp.mp.dps} decimal digits")

    r1 = verify_item1()
    r2 = verify_item2()
    r3 = verify_item3()
    r4 = verify_item4()
    row_table, r5 = verify_item5()

    hr("FINAL SUMMARY")
    print(f"{'Item':<6}{'Description':<62}{'Result'}")
    print(f"{'1':<6}{'Cancellation character check (symbolic)':<62}"
          f"{'PASS' if r1 else 'FAIL'}")
    print(f"{'2':<6}{'One-tile formula, 4 tiles, full (j0,m0) grid, both orient.':<62}"
          f"{'PASS' if r2 else 'FAIL'}")
    print(f"{'3':<6}{'Row I boundary evaluation, (5,3,7) k=3 (N=33)':<62}"
          f"{'PASS' if r3 else 'FAIL'}")
    print(f"{'4':<6}{'4-reptiling consistency, tile (7,8,13) x2':<62}"
          f"{'PASS' if r4 else 'FAIL'}")
    print(f"{'5':<6}{'Rows II-V geometry/bookkeeping consistency (data reported)':<62}"
          f"{'PASS' if r5 else 'FAIL'}")

    print("\nRows II-V data table (tile, row, Phi, M=Phi/Delta, Phi', M'=Phi'/(a-b-c), N, parities):")
    for r in row_table:
        Mp = (r["M"].numerator % 2) if r["M"].denominator == 1 else "n/a"
        Np = (r["N"].numerator % 2) if r["N"].denominator == 1 else "n/a"
        M2p = (r["M2"].numerator % 2) if r["M2"].denominator == 1 else "n/a"
        print(f"  tile={r['tile']}  row={r['row']:3s}  Phi={r['Phi']:>5}  M={str(r['M']):>6}  "
              f"Phi'={r['Phi2']:>5}  M'={str(r['M2']):>6}  N={str(r['N']):>7}  "
              f"M%2={Mp} N%2={Np} M'%2={M2p}")

    all_pass = r1 and r2 and r3 and r4
    print(f"\nOverall (items 1-4, the strict correctness checks): {'ALL PASS' if all_pass else 'SOME FAILED'}")
    print("(Item 5 has no external ground truth to check against -- it is new data; "
          "'geom' PASS just means the construction/bookkeeping is self-consistent.)")

    return 0 if (all_pass and r5) else 1


if __name__ == "__main__":
    raise SystemExit(main())
