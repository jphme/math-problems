Ancillary files for:

  "Peaceable queens on even toroidal boards:
   the exact formula t(2q) = H(2q)"
  Jan Philipp Harries, July 2026

The paper proves t(2q) = H(2q) for every positive integer q, where

  H(2q) = max over 0 <= r0,r1,c0,c1 <= q of
          min( r0*c1 + r1*c0 , (q-r0)*(q-c0) + (q-r1)*(q-c1) ).

The upper bound has three machine-checked components: two exact rational
branch certificates over a 42-equation moment relaxation (valid for all q,
used for q >= 130), an exact library of 760 certified support-dual cuts of
which two are used in the closed-form finish, and an exact integer
cut-envelope ladder covering q <= 129. The odd values t(15) = 20 and
t(17) = 28 come from exhaustive board sweeps; the n = 15 and n = 16 sweep
programs are shipped here as well.

Every verifier here runs on the Python standard library alone, with one
exception: verify_even_finite_prose.py uses sympy for its symbolic
identities. Every verifier uses exact arithmetic only: Python fractions.Fraction, or exact arithmetic
in Q(sqrt 3). No floating-point value enters any decision anywhere.
Python >= 3.10 suffices for all Python files; NumPy/SciPy are needed only
to *rebuild* the branch certificates, never to verify them. The C++ files
need a C++17 (n=15) or C++20 (n=16) compiler with OpenMP.


Even torus: the proof for q >= 130
----------------------------------
even_c527_sym_mc.json.gz      Global branch certificate: in the canonical
                              symmetry chamber, every normalized outer
                              profile outside the rational plaid
                              neighbourhood N has 42-moment relaxation
                              value at most 527/1000. Format tag
                              peaceable-even-c527-sym-mc-v1. 6,929 nodes,
                              3,368 McCormick-dual leaves, 4 plaid leaves,
                              93 exact empty leaves, depth 22.
even_local_core_mc.json.gz    Local branch certificate: inside N, either
                              the same 527/1000 bound holds or the integer
                              profile lies in the aggregate core. Format
                              tag peaceable-even-local-core-mc-v1. 4,423
                              nodes, 1,639 McCormick-dual leaves, 563 core
                              leaves, 10 exact empty leaves, depth 29.
verify_even_branch_certificate.py
                              Delivered exact checker for both trees.
                              Rebuilds the moment system, every McCormick
                              row, every rational dual, every split and
                              every empty-leaf obstruction.
verify_even_finite_independent.py
                              Second, from-scratch verifier for the same
                              two trees. Imports nothing from the checker
                              above or from the builders. It *discovers*
                              the 42 moment rows by counting torus
                              incidence fibres at n = 8,12,16,20, revalidates
                              them on 200 random colourings (8,400 exact
                              equation checks), re-derives the McCormick
                              rows, recomputes every leaf bound from its own
                              partial Lagrangian, and re-proves every
                              emptiness claim by its own interval reasoning.
                              Also self-tests against eight tampered copies.
even_finite_support_cuts.json Compact exact duals for support cuts 547,
                              609 and 559. The proof uses only 609
                              (B <= X - beta*b + Q) and 559
                              (W <= Y - alpha*a + Q).
verify_even_finite_algebra.py Exact check of the two support duals (their
                              columnwise support property and polynomial
                              identities) and of the paper's exact
                              constants.
verify_even_finite_prose.py   Independently written exact check of the
                              prose of Sections 3-5: the chamber argument,
                              every displayed inequality as a symbolic
                              identity or slack decomposition, an exact
                              Q(sqrt 3) sign routine, a 150,000-point exact
                              integer stress test of both cases, and the
                              q-coverage bookkeeping. 126 checks.
verify_even_q_ge_130_bundle.py
                              One-command driver: runs the certificate
                              checker, the algebra checker and the constant
                              checks in sequence.
counterexample_24prime.json   Exact integer lattice counterexample at
                              q = 10^6 to the proposed switching envelope
                              (24'), which the final proof bypasses.
verify_counterexample_24prime.py
                              Integer-arithmetic verification of it.


Even torus: the cut library and the finite ladder
-------------------------------------------------
new_dual_cuts.json            The certified library of 760 support-dual
                              cuts for the 42-moment system, with exact
                              rational duals. Cuts 609 and 559 used by the
                              closed-form proof are entries of this file.
envelope_checker.py           Exact single-threaded cut-envelope engine for
                              one even order. Searches canonical integer
                              boxes, propagates the chamber inequalities and
                              the budget exactly, uses separable McCormick
                              bounds and exact multi-affine corner maxima,
                              and bisects otherwise. All arithmetic is
                              integer after scaling by the coefficient LCM,
                              which it computes itself from the cut files.
                              It recomputes H(2q) independently and recounts
                              the parity-plaid witness cell by cell.
records_q021_q129/            109 JSON result/provenance records, one per
                              order q = 21..129: cut hashes, coefficient
                              LCM, exact H optimizer and witness recount,
                              complete terminal-tree accounting, empty
                              survivor list, runtime.


Odd torus and the legacy sweeps (n = 15, n = 16)
------------------------------------------------
peace15_solver.cpp            Proof solver for n = 15: exhaustively decides
                              all 247 canonical size profiles at target 21.
                              C++17 + OpenMP.
profile_enum.cpp              Second, independently written exact enumerator
                              for n = 15 (different symmetry quotient,
                              exact 7+8 meet-in-the-middle instead of DFS
                              with dynamic-programming bounds). C++20.
peace15_audit.py              Independent audit: regenerates the 247-profile
                              worklist, verifies all 43 fixed-pair orbit
                              counts by Burnside's lemma, checks the
                              certificate arithmetic, recounts the 20+20
                              witness.
WORKLIST-2026-07-25.tsv       The 247 canonical size profiles.
peace15_certificate.tsv       Per-profile certificate, five-thread run.
peace15_certificate_run2.tsv  Per-profile certificate, three-thread run.
peace16_solver.cpp            Proof solver for n = 16: all 677 oriented
                              parity-refined profiles at target 33.
                              C++20 + OpenMP.
peace16_solver_bruteforce.cpp The same with the completion kernel replaced
                              by direct enumeration of every admissible
                              diagonal mask.
peace16_audit.py              Independent audit for n = 16: profiles, 14
                              Burnside orbit counts, the two-lift (d,a)
                              reconstruction on all 256 label pairs, the
                              witness, and column-by-column agreement of the
                              two certificates.
peace16_certificate.tsv       Per-job certificate, optimized kernel.
peace16_certificate_bruteforce.tsv
                              Per-job certificate, brute-force kernel.
check_witness15.py            From-scratch pairwise check of the 20+20
                              witness (all 400 black-white pairs, all four
                              attack relations).
check_witness16.py            The same for the 32+32 witness.

The certificate column schemas for the two TSV families are unchanged from
the companion note on t(15) and t(16); see its ancillary README, or the
header comment lines of each TSV.


Integrity
---------
SHA256SUMS                    SHA-256 digests of every other file in this
                              directory. Verify with
                                shasum -a 256 -c SHA256SUMS
                              (or sha256sum -c).
README.txt                    This file.


Run: the even theorem for q >= 130
----------------------------------
    python3 verify_even_q_ge_130_bundle.py

Expected final line:

    EVEN_Q_GE_130_BUNDLE_OK

(about 3.3 seconds). The components can also be run individually:

    python3 verify_even_branch_certificate.py even_c527_sym_mc.json.gz \
                                              even_local_core_mc.json.gz
    python3 verify_even_finite_algebra.py

printing, respectively, EXACT_BRANCH_CERTIFICATE_OK for each tree followed
by ALL_EVEN_BRANCH_CERTIFICATES_OK, and EVEN_FINITE_ALGEBRA_OK.


Run: the independent verifications
----------------------------------
    python3 verify_even_finite_independent.py
    python3 verify_even_finite_prose.py

Expected output of the first (about 2.1 seconds):

    independent derivation of the 42-moment system
      moment_rows=42 product_variables=22 inner_atoms=64
      semantic_equation_checks=8400 on 50 random colorings for n in 12,16,20,28
    even_c527_sym_mc.json.gz
      ...
      nodes=6929 max_depth=22
      stats={'split': 3464, 'mc': 3368, 'empty_csort': 9, 'empty_rsort': 1,
             'empty_dasum': 21, 'empty_rcsum': 19, 'empty_budget': 43,
             'local': 4}
      EXACT_BRANCH_CERTIFICATE_INDEPENDENTLY_OK
    even_local_core_mc.json.gz
      ...
      nodes=4423 max_depth=29
      stats={'split': 2211, 'mc': 1639, 'local': 563, 'empty_rcsum': 10}
      EXACT_BRANCH_CERTIFICATE_INDEPENDENTLY_OK
    EVEN_FINITE_INDEPENDENT_VERIFIER_OK

and of the second:

    126/126 checks passed
    EVEN_FINITE_PROSE_OK


Run: the counterexample to the abandoned envelope (24')
-------------------------------------------------------
    python3 verify_counterexample_24prime.py

Expected final line:

    COUNTEREXAMPLE_24PRIME_OK


Run: the finite ladder
----------------------
    python3 envelope_checker.py 21 22 23 --progress

writes one JSON record per order to records/. Each record must carry an
empty survivor list, a complete terminal-tree accounting, a recomputed
H(2q) with its optimizer, and a cell-by-cell witness recount. The shipped
records for q = 21..129 are in records_q021_q129/. Per-order runtime is
well under the engine's 600-second stop; the slowest order of the full
project ladder (q = 1..1000) was q = 53 at 40.9 seconds.


Run: the upper bound for n = 15
-------------------------------
    g++ -O3 -fopenmp -std=c++17 peace15_solver.cpp -o peace15_solver
    OMP_NUM_THREADS=5 ./peace15_solver \
        --worklist WORKLIST-2026-07-25.tsv \
        --output peace15_certificate.tsv
    python3 peace15_audit.py

The solver prints SELFTEST_OK after its startup gates and ALL_UNSAT on
completion (A_checked=6074753568); the audit script prints AUDIT_OK. The
recorded five-thread run took about 60 seconds. The independent enumerator:

    clang++ -O3 -std=c++20 profile_enum.cpp -o profile_enum
    ./profile_enum --self-test --random 100000
    ./profile_enum --batch --worklist WORKLIST-2026-07-25.tsv \
        --results results.jsonl --log logs

reports 6,241,793,402 completions (a different case count, because the two
programs use different symmetry quotients) and UNSAT for all 247 profiles,
in about 200 seconds single-threaded.


Run: the upper bound for n = 16
-------------------------------
    g++ -O3 -fopenmp -std=c++20 peace16_solver.cpp -o peace16_solver
    OMP_NUM_THREADS=5 ./peace16_solver --output peace16_certificate.tsv

    g++ -O3 -fopenmp -std=c++20 \
        peace16_solver_bruteforce.cpp -o peace16_solver_bruteforce
    OMP_NUM_THREADS=5 ./peace16_solver_bruteforce \
        --output peace16_certificate_bruteforce.tsv

    python3 peace16_audit.py

Each solver prints SELFTEST_OK and then ALL_UNSAT (A=13163028768,
triple=17834); the audit script prints AUDIT_OK and compares the two
certificates column by column. Both audit scripts read the certificates
from their own directory, so run them after the solvers have written those
files, or against the shipped copies.

-march=native and -DNDEBUG may be added for speed and were used in the
recorded runs; they are omitted above because neither affects any
verification step. No proof-relevant check in any program is implemented
via assert; all gates are explicit runtime tests that abort in every build.
The randomized self-tests are deterministic (std::mt19937_64 with fixed
seeds).


What is checked, and what that means
------------------------------------
1. The two branch certificates and the support-dual cuts ARE
   machine-checkable proof objects. Each carries exact rational multipliers
   that a reader's own program can re-verify without solving any linear
   programme. Both are checked here by two programs sharing no code, and
   the independent verifier does not even take the moment system on trust:
   it rediscovers it from torus incidences.

2. The ladder records and the sweep certificates are audit logs, not
   standalone proof objects. They record what was searched and bind their
   inputs by hash. The refutations are the engines together with the
   reductions proved in the paper; re-running them is what re-establishes
   them.

3. Every pruning rule in every exhaustive search is a necessary condition
   for feasibility, so no candidate is discarded unexamined. This is what
   makes the searches exhaustive rather than heuristic.

4. Evidence tiers, stated plainly. The range q >= 130 and the range
   q <= 20 each have two genuinely independent verifications. The ladder
   segment q = 21..129 currently rests on one exact certified method: a
   strict C++17 accelerator reproduces the Python engine counter for
   counter, but it is a second-language port of the same algorithm, not a
   conceptually different method. Writing a second, different exact engine
   for those 109 orders is the most valuable check that remains open, and
   it is a cheap computation.

5. For n = 16 the two shipped sweep programs differ only in the completion
   kernel; their agreement tests the kernel, not the chassis. That debt was
   closed separately by two independent general-n implementations that
   reproduced all 677 oriented jobs, the 13,163,028,768 cases and the
   17,834 prefilter survivors exactly; those programs are not shipped here.
