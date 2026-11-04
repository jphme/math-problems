Ancillary files for:

  "No triangle can be cut into nineteen congruent triangles:
   the prime case of Erdos Problem 634"
  Jan Philipp Harries, version 2 (October 2026)

The proofs in the paper are self-contained. The scripts below are supplementary
checks of the algebra and arithmetic used there; they are error detection, not
proofs, and they do not check any geometry (see "What is not established").

Files
-----
verify_triangle19.py   Checks of Lemma "lem:group2" (the lemma on tiles with an
                       angle of 2pi/3; Group 2 in the paper). Carried over from
                       version 1; its checks are unchanged, only its attribution
                       of the parametrization and its final output line were
                       corrected.
verify_lemmas_v2.py    Checks of the lemmas that are new in version 2: Group-1
                       tiles and counts, residues, the two shapes of the
                       Group-1 case, isosceles and equilateral targets, and the
                       boundary characters.
README.txt             This file.
../lean/               Lean 4 formalization of the integer arithmetic (see
                       ../lean/README.md); not part of this folder's scripts.

Requirements
------------
Python >= 3.10 and SymPy. Tested with Python 3.14.7 and SymPy 1.14.0. No other
packages are needed. Everything is exact arithmetic (SymPy expressions, Python
integers and Fractions); there is no floating point.

Run
---
    python3 verify_triangle19.py
    python3 verify_lemmas_v2.py

or, with uv (no installation needed):

    uv run --with sympy python verify_triangle19.py
    uv run --with sympy python verify_lemmas_v2.py

Each script exits with status 0 if and only if all its checks pass.
Runtime: verify_triangle19.py about 0.3 seconds, verify_lemmas_v2.py about
2 to 3 seconds (on a laptop, single core).

verify_lemmas_v2.py takes one optional argument, --tilings DIR. Section [8] of
its output checks the boundary-character identity on exact tilings (N = 63,
99, 189 in Group 1; N = 88, 143, 77 in Group 2) stored as JSON files, which
are not included in this folder. Without the option that section is skipped
with one line, as in the output below.

Expected output of verify_triangle19.py
---------------------------------------
    symbolic trigonometric identities: PASS
    symbolic area-ratio formulas:       PASS
    symbolic prime-obstruction factor:  PASS
    primitive gcd sanity check (41,112 triples): PASS
    finite N=19 cross-check:
      m=1: (a,b)=(18,1), c^2=343, 324 < c^2 < 361
      m=2: (a,b)=(15,4), c^2=301, 289 < c^2 < 324
      m=3: (a,b)=(10,9), c^2=271, 256 < c^2 < 289
      m=4: (a,b)=(3,16), c^2=313, 289 < c^2 < 324
    finite N=19 cross-check:            PASS

    ALL CHECKS PASSED: the identities and area-ratio formulas of the lemma on 2pi/3 tiles hold symbolically, the primitivity claims hold on the tested triples, and the N=19 instance of case C is excluded.

Expected output of verify_lemmas_v2.py (without --tilings)
----------------------------------------------------------

    [1] Group-1 side vectors and counts (Lemmas lem:g1tile, lem:g1counts, lem:shape4, lem:shape5)
      ok    law of sines ratios a/c = 2 sin(alpha/2), b/c = 1 - (a/c)^2
      ok    cosine table of all Group-1 angles as polynomials in sin(alpha/2)
      ok    tile (mk, k^2-m^2, k^2) has angles (alpha, beta, gamma) with sin(alpha/2) = m/(2k)
      ok    triquadratic (2a,b,a+b): sides j*(m*(2*k**2 - m**2), k*(k**2 - m**2), k**3), N = j**2*(2*k**2 - m**2)
      ok    isosceles-beta (b,b,3a): sides j*(k**3, k**3, m*(3*k**2 - m**2)), N = j**2*(3*k**2 - m**2)
      ok    (a,2a,2b): sides j*(k**4, k**2*(2*k**2 - m**2), (k**2 - m**2)*(3*k**2 - m**2)), N = j**2*(2*k**2 - m**2)*(3*k**2 - m**2)
      ok    shape 4 (a+b,a+b,a): sides t*(k, k, m), N = t**2/((k - m)*(k + m))
      ok    shape 5 (a,a,a+2b): sides t*(k**2, k**2, 2*k**2 - m**2), N = t**2*(2*k**2 - m**2)/((k - m)*(k + m))

    [2] Group-2 side vectors and counts (Lemma lem:rowI and the four cases of lem:group2)
      ok    row I (a,a,pi-2a): side vector and count N = scale^2 * (s**2 + 4*s*t + t**2)/(t*(2*s + t))
      ok    row I swapped (b,b,pi-2b): side vector and count N = scale^2 * (2*s**2 + 2*s*t - t**2)/((s - t)*(s + t))
      ok    lem:group2 case A (a,2a,3b): side vector and count N = scale^2 * 3*s*(s + 2*t)*(s**2 + 4*s*t + t**2)
      ok    lem:group2 case B (a,2b,2a+b): side vector and count N = scale^2 * s*(s + 2*t)*(2*s**2 + 2*s*t - t**2)
      ok    lem:group2 case C (a,a+b,a+2b): side vector and count N = scale^2 * s*(s + 2*t)/(t*(2*s + t))
      ok    lem:group2 case D (2a,2b,a+b): side vector and count N = scale^2 * (s**2 + 4*s*t + t**2)*(2*s**2 + 2*s*t - t**2)
      ok    lem:group2 scale ratios K_T/K = mc^2/a, mc, m, mc

    [3] gcd (primitivity) claims
      ok    Group 1: all six vectors primitive and gcd(h,b)=gcd(m,b)=gcd(k,b)=1 for all 48677 coprime 0<m<k<=400
      ok    Group 2: 418 primitive triples with a,b <= 1200: pairwise coprime, 3 !| c, d = a-b unit mod 3ab, a,b >= 2, gcd(c,a+2b)=gcd(c,2a+b)=1, lem:group2 vectors A-D primitive

    [4] Residues (Lemma lem:g1residues)
      ok    complete residue enumeration: odd 2k^2-m^2 mod 8 in [1, 7]; 3k^2-m^2 mod 3 in [0, 2]
      ok    primes p = 3 mod 4, 5 <= p < 5000: 338; represented by 2k^2-m^2 (coprime 0<m<k): 171, all = 7 mod 8, missing p = 7 mod 8: []
      ok    represented by 3k^2-m^2: 167, all = 11 mod 12, missing p = 11 mod 12: []
      ok    83 primes p = 19 mod 24 below 5000 (19, 43, 67, ...): represented by neither form

    [5] Lemma lem:shape4: base decompositions in the prime case
      ok    274 prime instances with k <= 80: the base t*m = N*s*m has no decomposition with a c-edge (only (A,B,C) = (0, m/s, 0) when s | m, none otherwise); e.g. (m,k)=(1,2) N=3 t=3 base=3; (m,k)=(1,3) N=2 t=4 base=4; (m,k)=(2,3) N=5 t=5 base=10; (m,k)=(3,4) N=7 t=7 base=21; (m,k)=(5,6) N=11 t=11 base=55; (m,k)=(1,7) N=3 t=12 base=12

    [6] Lemma lem:shape5, elementary part
      ok    36 pairs with k <= 400 where t^2 = b and h prime; all have N = h = k^2 + t^2 = 1 mod 4 and b !| t (excluded by the boundary-character part); first: [(3, 5, 4, 41), (5, 13, 12, 313), (15, 17, 8, 353), (7, 25, 24, 1201)]

    [7] Boundary characters (Lemmas lem:character, lem:rowI, lem:shape5)
      ok    Group-2 tile values: direct chi(a-edge)(d + c z^-1), reflected chi(a-edge)(d + c z)
      ok    row I target polynomial B(dT) = k(U - c z^-1 - c z) (base direction anchored)
      ok    evaluation z -> -d c^-1: kills d+cz and d+cz^-1 (mod 3ab); d*eps(B(dT)) = 3a^2 k
      ok    row I: eps(B(dT)) = 0 mod 3ab exactly when b | k (22874 cases, 104 triples a,b <= 300)
      ok    Group-1 tile values: direct -chi(a-edge) z^-3 (k-mz)Q, reflected -chi(a-edge)(kz-m)Q, Q = kz^2+mz+k
      ok    shape 5 target polynomial B(dT) = t(h + k^2 z^-2 + k^2 z^2) = t z^-2 Q Qbar
      ok    Qbar(k m^-1) = k^3 m^-2 (a unit mod b)
      ok    shape 5: psi_b(t Qbar) = 0 mod b exactly when b | t (2664318 cases, k <= 60)

    [8] Boundary-character identity on exact tilings (optional)
      skipped: no --tilings DIR given (this section needs the tiling JSON files)

    [9] Examples quoted in the remarks (count formula allows a prime; the geometric step excludes it)
      ok    lem:shape4: tile (90,19,100), T = 19*(10,10,9), N = 19; base 171 decompositions [(0, 9, 0)] (nine b-edges, no c-edge)
      ok    lem:shape5: tile (15,16,25), T = 4*(25,25,41), N = 41 prime = 1 mod 4; excluded only by b | t (16 !| 4)
      ok    lem:rowI: tile (39,16,49), T = 4*(49,49,71), N = 71 prime = 3 mod 4; eps(B(dT)) = 468 != 0 mod 1872, so excluded

    ALL CHECKS PASSED (exact symbolic identities and finite arithmetic tests; tilings section skipped)

What is checked
---------------
verify_triangle19.py (Lemma "lem:group2", tiles with an angle of 2pi/3):
 1. The six trigonometric identities and the four area-ratio formulas of the
    lemma, symbolically with SymPy modulo c^2 = a^2 + ab + b^2, in both
    labelings of the acute angles.
 2. The primitivity (gcd) claims for the four side vectors on 41,112 primitive
    solutions of c^2 = a^2 + ab + b^2, generated by the standard
    parametrization of primitive Eisenstein triples
        a = s^2 - t^2, b = t(2s + t), c = s^2 + st + t^2
    and the same with a and b exchanged (2 <= s <= 300, 1 <= t < s,
    gcd(s,t) = 1, s != t mod 3). Every generated triple is checked directly,
    so the checks do not depend on the parametrization being complete.
 3. The N = 19 instance of case C: for the four candidates
    (a,b) = (19 - m^2, m^2), 1 <= m <= 4, a^2 + ab + b^2 is not a square.
 4. a + b = s(s + 2t) on the parametrization, which makes a + b composite.

verify_lemmas_v2.py (lemma names as in the paper; LaTeX labels in brackets):
 [1] Group-1 tiles and counts ["Group-1 tiles", "Group-1 count equations",
     lem:shape4, lem:shape5]: side vectors against the law of cosines with
     the exact cosines as polynomials in sin(alpha/2) = m/(2k), and tile
     counts against Heron's formula; polynomial identities in m, k.
 [2] Group-2 targets ["Isosceles and equilateral targets", lem:group2]: the
     same two checks for the isosceles targets and the four cases of
     lem:group2, on the rational parametrization of c^2 = a^2 + ab + b^2.
 [3] Primitivity of the side vectors for all coprime 0 < m < k <= 400
     (Group 1) and all primitive triples with a, b <= 1200 (Group 2).
 [4] ["Residues"] complete residue enumeration mod 8 and mod 3, and the primes
     p = 3 mod 4 below 5000 represented by the two Group-1 forms (shows the
     congruences are sharp; p = 19 mod 24 is represented by neither).
 [5] [lem:shape4] all base decompositions in the prime case for k <= 80 have
     no c-edge.
 [6] [lem:shape5] elementary part: a prime count forces N = k^2 + t^2.
 [7] ["Boundary character", lem:rowI, lem:shape5] tile and target boundary
     polynomials recomputed from the turning-angle rule, the evaluation maps
     checked symbolically, and the criterion "eps(B(dT)) = 0 iff b | k" and
     its shape-5 analogue tested on finite ranges.
 [8] Optional, with --tilings: sum over tiles of the boundary polynomial
     equals that of the target, and the tile values are as predicted, on the
     exact tilings named above.
 [9] The three numerical examples quoted in the remarks of the paper.

What is not established
-----------------------
 * Finite ranges (sections [3] to [7]) test universal statements that the paper
   proves; a pass is error detection, not a proof. The complete enumerations
   mod 8 and mod 3 in [4] are exhaustive.
 * The geometry is not checked: the boundary decomposition, the angle counts,
   the derivation of the count equations from a tiling, and the imported
   classification and rationality theorems.
 * verify_triangle19.py checks only the arithmetic of the lemma on tiles with
   an angle of 2pi/3. It does not show that N = 19 is impossible; that
   follows only from the full argument of the paper.
 * Section [8] needs tilings that are not in this folder; the default run does
   not include it.

Related material
----------------
 * Lean 4 formalization of the integer arithmetic and of the case analysis
   (hypotheses named explicitly): ../lean/, described in ../lean/README.md.
 * Version 1 of the paper (July 24, 2026) is in the history of the public
   repository https://github.com/jphme/math-problems, folder no19tiling, at the
   git tag no19tiling-v1. Its proof is incomplete for the reasons listed in
   Section "Changes from version 1" of version 2.
