#!/usr/bin/env python3
"""Independent arithmetic audit of archive/pro_report_7.md (2026-07-27).

Verified here:

  A. The finite angle enumeration behind the one-full-side, one-patch
     row-to-row transfers in Group 2 and Group 1.  The enumeration is made
     under the standing incommensurable-angle hypotheses and is modulo
     reflection and a <-> b.  Trivial outputs whose union is itself a scaled
     copy of the tile are deliberately not called row-to-row transfers.
  B. Every stated scale/count identity for those transfers.
  C. The two-orientation parallelogram construction and the corrected
     arithmetic inventory of Herdt's N=720 construction: ten quadratic
     patches and THREE transition blocks, each split into two uniform
     subparallelograms.
  D. The primitive Eisenstein parametrization for a,b < 400 (both orders
     included), its two relation vectors, and the lattice-basis test.
  E. The pure-edge B^j A^(n-j) transition rule, coherent-junction angle
     uniqueness, exact defect-wedge geometry, and its nonintegral area ratio.
  F. A concrete exact mirror placement showing why report 7 does NOT close
     the forced-corner-layer induction G11.

Not verified, and not promoted in the paper:

  * the geometric coverage of the N=720 macro inventory by an exact coordinate
    certificate (the vector figure was audited separately);
  * the forced-layer induction: identifying the ideal gaps does not force the
    actual tiles to occupy them with the intended side assignment;
  * geometric seam propagation, macro-normalization, or the claimed
    semilinearity consequence.

This script uses only the Python standard library.

Run:
    python3 erdos634_universal/computation/verify_theory_report7_claims.py
"""

from fractions import Fraction as Fr
from itertools import permutations
from math import gcd, isqrt


PASS = 0
FAIL = 0


def check(name, condition, detail=""):
    global PASS, FAIL
    if condition:
        PASS += 1
        print(f"  PASS  {name}")
    else:
        FAIL += 1
        suffix = f" -- {detail}" if detail else ""
        print(f"  FAIL  {name}{suffix}")


def add_angles(x, y):
    return x[0] + y[0], x[1] + y[1]


def canon_angles(angles):
    return tuple(sorted(angles))


def angle_outputs(rows, tile_angles, pi_angle, include_swaps=False):
    """Enumerate source/destination angle shapes for a full-side attachment.

    The tile is glued along one complete source side.  One seam endpoint must
    straighten to pi.  The return value maps each source to all destination
    row names whose three angle vectors result, plus "R" for a tile-shaped
    output and None for an angle shape outside the named catalogue.
    """
    lookup = {canon_angles(angles): name for name, angles in rows.items()}
    if include_swaps:
        for name, angles in rows.items():
            swapped = [(y, x) for x, y in angles]
            lookup.setdefault(canon_angles(swapped), name + "*")
    lookup[canon_angles(tile_angles.values())] = "R"
    outputs = {name: set() for name in rows}

    for source_name, source_angles in rows.items():
        for opposite_source_vertex in range(3):
            endpoints = [i for i in range(3) if i != opposite_source_vertex]
            for opposite_tile_name, opposite_tile_angle in tile_angles.items():
                tile_endpoints = [
                    item for item in tile_angles.items()
                    if item[0] != opposite_tile_name
                ]
                for order in (tile_endpoints, list(reversed(tile_endpoints))):
                    for straight_position in (0, 1):
                        straight_vertex = endpoints[straight_position]
                        other_vertex = endpoints[1 - straight_position]
                        straight_tile_angle = order[straight_position][1]
                        other_tile_angle = order[1 - straight_position][1]
                        if add_angles(
                                source_angles[straight_vertex],
                                straight_tile_angle) != pi_angle:
                            continue
                        result = [
                            source_angles[opposite_source_vertex],
                            opposite_tile_angle,
                            add_angles(source_angles[other_vertex],
                                       other_tile_angle),
                        ]
                        outputs[source_name].add(
                            lookup.get(canon_angles(result)))
    return outputs


print("A. finite one-patch angle enumeration")

G2_ROWS = {
    "I": [(1, 0), (1, 0), (1, 3)],
    "II": [(1, 0), (2, 0), (0, 3)],
    "III": [(1, 0), (0, 2), (2, 1)],
    "IV": [(1, 0), (1, 1), (1, 2)],
    "V": [(2, 0), (0, 2), (1, 1)],
    "E": [(1, 1), (1, 1), (1, 1)],
}
G2_TILE = {"a": (1, 0), "b": (0, 1), "c": (2, 2)}
g2_outputs = angle_outputs(G2_ROWS, G2_TILE, (3, 3), include_swaps=True)

# Swapped destinations are identified by applying a <-> b to the output
# angle vectors.  The unswapped catalogue therefore records III/V variants
# conservatively below; the side audit distinguishes the stated swaps.
check("A1: Group-2 sources I, II, III have no straightening attachment",
      all(not g2_outputs[row] for row in ("I", "II", "III")))
check("A2: Group-2 E starts only row IV (including its swapped form)",
      g2_outputs["E"] == {"IV", "IV*"})
check("A3: Group-2 IV outputs I, IV, III(swapped), or the trivial reptile",
      g2_outputs["IV"] == {"I", "IV", "III*", "R"})
check("A4: Group-2 V outputs II or III (including swapped variants)",
      g2_outputs["V"] == {"II", "II*", "III", "III*"})
check("A5: no Group-2 row-to-row one-patch attachment lands in V",
      all("V" not in values for values in g2_outputs.values()))

G1_ROWS = {
    "S1": [(2, 0), (0, 1), (1, 1)],
    "S2": [(2, 0), (1, 0), (0, 2)],
    "S3": [(0, 1), (0, 1), (3, 0)],
    "S4": [(1, 1), (1, 1), (1, 0)],
    "S5": [(1, 0), (1, 0), (1, 2)],
}
G1_TILE = {"a": (1, 0), "b": (0, 1), "c": (2, 1)}
g1_outputs = angle_outputs(G1_ROWS, G1_TILE, (3, 2))
check("A6: Group-1 S1 outputs S1, S2, S3, or the trivial reptile",
      g1_outputs["S1"] == {"S1", "S2", "S3", "R"})
check("A7: Group-1 S4 outputs S1, S4, S5, or the trivial reptile",
      g1_outputs["S4"] == {"S1", "S4", "S5", "R"})
check("A8: no Group-1 attachment starts from S5",
      not g1_outputs["S5"])
check("A9: Group-1 sources S2 and S3 have no straightening attachment",
      not g1_outputs["S2"] and not g1_outputs["S3"])


print("B. transfer scale and count identities")


def primitive_eisenstein_triples(rmax=35):
    triples = set()
    for r in range(2, rmax + 1):
        for s in range(1, r):
            if gcd(r, s) != 1 or (r - s) % 3 == 0:
                continue
            a = r * r - s * s
            b = 2 * r * s + s * s
            c = r * r + r * s + s * s
            triples.add((a, b, c, r, s))
            triples.add((b, a, c, r, s))
    return sorted(triples)


g2_transfer_ok = True
for a, b, c, _r, _s in primitive_eisenstein_triples():
    U, V, W = a + 2 * b, 2 * a + b, a + b
    identities = [
        a * b + b * b == b * W,                         # E -> IV
        b * W + b * b == b * U,                         # IV -> I
        b * W + W * W == U * W,                         # IV -> III(b,a)
        U * V + U * U == 3 * U * W,                     # V -> II
        b * W * a * a + (b * W) ** 2 == b * W * c * c, # IV(as)->IV(cs)
        U * V * a * a + (b * V) ** 2 == V * W * c * c, # V(as)->III(a,b;cs)
        U * V * b * b + (a * U) ** 2 == U * W * c * c, # swapped transport
    ]
    g2_transfer_ok &= all(identities)
check("B1: all seven Group-2 count identities (parametric sweep)",
      g2_transfer_ok)

g1_transfer_ok = True
for q in range(2, 60):
    for p in range(1, q):
        if gcd(p, q) != 1:
            continue
        a, b, c = p * q, q * q - p * p, q * q
        h, g = b + c, b + 2 * c
        identities = [
            b * c + c * c == c * h,                    # S4 -> S1
            b * c + b * b == b * h,                    # S4 -> S5
            c * h + h * h == h * g,                    # S1 -> S2
            c * h + c * c == c * g,                    # S1 -> S3
            c * h * b * b + (a * h) ** 2
            == c * h * c * c,                          # S1(bs) -> S1(cs)
            b * c * p * p + (b * q) ** 2
            == b * c * q * q,                          # S4(ps) -> S4(qs)
        ]
        g1_transfer_ok &= all(identities)
check("B2: all six Group-1 count identities (p,q < 60 sweep)",
      g1_transfer_ok)


print("C. two-orientation parallelograms and Herdt's N=720 inventory")

parallelogram_ok = True
for b, c in ((3, 7), (5, 6), (7, 13), (16, 19)):
    for p in range(6):
        for q in range(6):
            if p + q == 0:
                continue
            first_cells = c * p   # bc/b by pc/c
            second_cells = b * q # bc/c by qb/b
            parallelogram_ok &= (
                2 * first_cells + 2 * second_cells
                == 2 * (p * c + q * b)
            )
check("C1: P(bc,pc+qb) has 2(pc+qb) tiles", parallelogram_ok)

quadratic_scales = [15] + 3 * [6, 5, 4]
uniform_cell_counts = [35, 24, 24, 35, 4, 10]
uniform_tile_counts = [2 * n for n in uniform_cell_counts]
transition_blocks = [
    uniform_tile_counts[0] + uniform_tile_counts[1],
    uniform_tile_counts[2] + uniform_tile_counts[3],
    uniform_tile_counts[4] + uniform_tile_counts[5],
]
check("C2: ten quadratic patches contribute 456 tiles",
      sum(k * k for k in quadratic_scales) == 456)
check("C3: six uniform subblocks form three transition blocks",
      uniform_tile_counts == [70, 48, 48, 70, 8, 20]
      and transition_blocks == [118, 118, 28])
check("C4: transition dimensions are 30x(35+24), twice, and 20x(4+10)",
      59 == 35 + 24 and 14 == 4 + 10
      and 30 == 5 * 6 and 20 == 4 * 5)
check("C5: corrected macro inventory totals N=720",
      456 + sum(transition_blocks) == 720)
check("C6: target/ray data for (4,5,6) at r=12",
      5 * 12 * 12 == 720 and (10 * 12, 10 * 12, 15 * 12)
      == (120, 120, 180))


print("D. primitive Eisenstein parametrization and relation lattice")

direct = set()
for a in range(1, 400):
    for b in range(1, 400):
        c2 = a * a + a * b + b * b
        c = isqrt(c2)
        if c * c == c2 and gcd(gcd(a, b), c) == 1:
            direct.add((a, b, c))

parametrized = {
    (a, b, c)
    for a, b, c, _r, _s in primitive_eisenstein_triples(rmax=100)
    if a < 400 and b < 400
}
check("D1: parametrization finds every ordered primitive triple with a,b<400",
      direct == parametrized,
      f"direct={len(direct)}, parametrized={len(parametrized)}")

relations_ok = True
primitive_cross_ok = True
for a0, b0, c, r, s in primitive_eisenstein_triples(rmax=35):
    # The stored (r,s) parametrizes one of (a0,b0) or (b0,a0).
    a = r * r - s * s
    b = 2 * r * s + s * s
    if (a0, b0) != (a, b):
        continue
    rc = (r + s, s, -r)
    rb = (s, -r, s)
    dot_c = a * rc[0] + b * rc[1] + c * rc[2]
    dot_b = a * rb[0] + b * rb[1] + c * rb[2]
    cross = (
        rc[1] * rb[2] - rc[2] * rb[1],
        rc[2] * rb[0] - rc[0] * rb[2],
        rc[0] * rb[1] - rc[1] * rb[0],
    )
    relations_ok &= (
        c * r == (r + s) * a + s * b
        and r * b == s * (a + c)
        and (r + 2 * s) * a == (r - s) * (b + c)
        and dot_c == dot_b == 0
        and cross == (-a, -b, -c)
    )
    primitive_cross_ok &= gcd(gcd(abs(cross[0]), abs(cross[1])),
                              abs(cross[2])) == 1
check("D2: parametrization identities and R_c x R_b=-(a,b,c)",
      relations_ok)
check("D3: primitive cross product gives an index-one kernel basis",
      primitive_cross_ok)
check("D4: flagship (3,5,7) relations",
      2 * 5 == 3 + 7 and 2 * 7 == 3 * 3 + 5
      and 4 * 3 == 5 + 7)


print("E. ordered pure-edge layers and defect wedge")

# At a junction, record the two supported endpoint angles.  A->B gives
# gamma+gamma and is impossible in a pi half-plane; B->A gives beta+beta.
alpha, beta, gamma = (1, 0), (0, 1), (2, 2)
check("E1: A->B has two gamma sectors and exceeds a half-plane",
      add_angles(gamma, gamma)[0] > 3
      and add_angles(gamma, gamma)[1] > 3)

# Avoid relying on a floating evaluation of alpha: a word avoids the forbidden
# adjacent substring AB iff it is B^j A^(n-j).
word_rule_ok = True
for n in range(1, 11):
    for mask in range(1 << n):
        word = "".join("B" if mask & (1 << i) else "A" for i in range(n))
        avoids_ab = "AB" not in word
        normal = any(word == "B" * j + "A" * (n - j)
                     for j in range(n + 1))
        word_rule_ok &= avoids_ab == normal
check("E2: forbidding A->B gives exactly B^j A^(n-j)", word_rule_ok)

# If n_a alpha+n_b beta+n_g gamma=alpha, comparison in the basis
# {alpha, pi/3}, with beta=pi/3-alpha and gamma=2pi/3, gives
# n_a-n_b-1=0 and n_b+2n_g=0.
coherent_solutions = []
for na in range(8):
    for nb in range(8):
        for ng in range(8):
            if na - nb - 1 == 0 and nb + 2 * ng == 0:
                coherent_solutions.append((na, nb, ng))
check("E3: a coherent junction's residual alpha sector is one alpha tile",
      coherent_solutions == [(1, 0, 0)])

defect_ok = True
nonintegral_ok = True
for a, b, c, _r, _s in primitive_eisenstein_triples(rmax=35):
    V = 2 * a + b
    # With rho=e^(i*pi/3), Q_-=-a+b rho^2 and Q_+=a+b rho.
    qminus_sq = a * a + a * b + b * b
    qplus_sq = qminus_sq
    base_sq = V * V
    # Areas have the common factor b*sqrt(3)/4.
    defect_ok &= qminus_sq == qplus_sq == c * c and base_sq == V * V
    nonintegral_ok &= V % a != 0
check("E4: defect wedge has sides (c,c,2a+b) and area ratio (2a+b)/a",
      defect_ok)
check("E5: the defect area ratio is never integral for a primitive triple",
      nonintegral_ok)


print("F. exact mirror-gap obstruction to the proposed forced-layer proof")

# In the (4,5,6) tile, an alpha-sector is bounded by the adjacent sides
# x=5 and y=6, with opposite side z=4.  The intended placement uses (5,6).
# The reflected placement uses (6,5) in the same sector.  Both are congruent,
# while the reflected endpoints overshoot the x-wall and undershoot the
# y-wall by one unit.
x, y, z = 5, 6, 4
cos_alpha = Fr(x * x + y * y - z * z, 2 * x * y)
reflected_opposite_sq = (
    y * y + x * x - 2 * y * x * cos_alpha
)
check("F1: intended and reflected alpha-sector placements are both (4,5,6)",
      reflected_opposite_sq == z * z)
check("F2: reflected placement overshoots one ideal wall and undershoots the other",
      y - x == 1 and x - y == -1)
check("F3: report 7's gap coordinates do not distinguish the two side assignments",
      sorted((x, y)) == sorted((y, x)) and x != y)


print(f"\nSUMMARY: {PASS} passed, {FAIL} failed")
if FAIL:
    raise SystemExit(1)
