Ancillary files for:

  "Peaceable queens on the 15x15 and 16x16 tori:
   the exact values t(15)=20 and t(16)=32"
  Jan Philipp Harries, July 2026

The two cases are independent computations that share a common reduction
(Section 2 of the paper). Files are grouped by case.


Files for n = 15
----------------
peace15_solver.cpp            The proof solver. Exhaustively decides all 247
                              canonical size profiles (Sections 4-6 of the
                              paper). C++17 + OpenMP.
profile_enum.cpp              The second, independently written exact
                              enumerator (different symmetry quotient,
                              different completion algorithm: exact 7+8
                              meet-in-the-middle instead of DFS with
                              dynamic-programming bounds). C++20.
peace15_audit.py              Independent audit: regenerates the 247-profile
                              worklist, verifies all 43 fixed-pair orbit
                              counts by Burnside's lemma, checks the row
                              arithmetic and column total of the certificate,
                              and re-counts the 20+20 witness. Python 3, no
                              third-party dependencies.
WORKLIST-2026-07-25.tsv       The 247 canonical size profiles. The solver
                              regenerates this set from scratch and refuses
                              to run if it differs.
peace15_certificate.tsv       Per-profile certificate of the recorded
                              five-thread run.
peace15_certificate_run2.tsv  Per-profile certificate of the recorded
                              three-thread run. All columns except the
                              per-profile timing agree with the file above.

Files for n = 16
----------------
peace16_solver.cpp            The proof solver. Exhaustively decides all 677
                              oriented parity-refined profiles (Sections
                              8-10 of the paper). C++20 + OpenMP.
peace16_solver_bruteforce.cpp The same program with the completion kernel
                              replaced by direct enumeration of every
                              admissible diagonal mask (at most
                              C(8,d0)*C(8,d1) <= 4900 per case). It differs
                              from peace16_solver.cpp in ten lines; see the
                              caveat below.
peace16_audit.py              Independent audit: regenerates the 1,898
                              ordered / 342 canonical profiles and their
                              strata, verifies all 14 row-column pair-orbit
                              counts by Burnside's lemma, checks the two-lift
                              (d,a) reconstruction against brute force for
                              all 256 label pairs, re-counts the 36/32
                              lower-bound line colouring, and compares all
                              non-timing columns of the two certificates.
peace16_certificate.tsv       Per-job certificate, optimized kernel.
peace16_certificate_bruteforce.tsv
                              Per-job certificate, brute-force kernel.

README.txt                    This file.


Requirements
------------
A C++17 compiler with OpenMP for peace15_solver.cpp, a C++20 compiler for
profile_enum.cpp and for both n=16 solvers (g++ recommended; the n=16
solvers need OpenMP), and Python >= 3.10 for the audit scripts. No
third-party libraries.


Run: the upper bound for n = 15
-------------------------------
    g++ -O3 -march=native -fopenmp -DNDEBUG -std=c++17 \
        peace15_solver.cpp -o peace15_solver
    OMP_NUM_THREADS=5 ./peace15_solver \
        --worklist WORKLIST-2026-07-25.tsv \
        --output peace15_certificate.tsv
    python3 peace15_audit.py

Expected output: the solver prints

    SELFTEST_OK profiles=247 estimated_A=6074753568 threads=...
    [  1/247] 5,5,5,5 S=20 ... result=UNSAT ...
    ...
    ALL_UNSAT A_checked=6074753568 triple_pass=2329772941
              dfs_calls=26948453 dfs_nodes=246476279 elapsed=...

and the audit script prints

    AUDIT_OK
    profiles=247
    orbit_keys_burnside_checked=43
    A_checked=6074753568
    lower_bound_cells=black:20,white:22
    solver_sha256=...
    certificate_sha256=...

The recorded five-thread run took about 60 seconds.


Run: the independent enumerator for n = 15
------------------------------------------
    clang++ -O3 -std=c++20 -DNDEBUG -Wall -Wextra -Wpedantic \
        profile_enum.cpp -o profile_enum
    ./profile_enum --self-test --random 100000
    ./profile_enum --batch --worklist WORKLIST-2026-07-25.tsv \
        --results results.jsonl --log logs

This writes one JSON record per profile to results.jsonl and is resumable.
It reports 6,241,793,402 completions in total (a different case count from
the solver's 6,074,753,568, because the two programs use different symmetry
quotients) and result "UNSAT" for every one of the 247 profiles. It takes
about 200 seconds single-threaded.


Run: the upper bound for n = 16
-------------------------------
    g++ -O3 -march=native -fopenmp -std=c++20 \
        peace16_solver.cpp -o peace16_solver
    OMP_NUM_THREADS=5 ./peace16_solver --output peace16_certificate.tsv

    g++ -O3 -march=native -fopenmp -std=c++20 \
        peace16_solver_bruteforce.cpp -o peace16_solver_bruteforce
    OMP_NUM_THREADS=5 ./peace16_solver_bruteforce \
        --output peace16_certificate_bruteforce.tsv

    python3 peace16_audit.py

Expected output: each solver prints

    SELFTEST_OK profiles=342 jobs=677 estimated_A=13163028768 threads=...
    [  1/677] 6,6,0,6,0,6 -> 6,6,0,6,0,6 orb=10132 A=283696 UNSAT sec=...
    ...
    ALL_UNSAT A=13163028768 triple=17834 calls=0 nodes=0 elapsed=...

and the audit script prints

    profiles (1898, 342, {24: 13, 25: 41, 26: 101, 27: 120, 28: 57, 29: 10})
    orbits {...14 entries...}
    plaid_masks (43680, 43680, 21845, 21845)
    lift_map OK
    certificates (677, 13163028768, 17834)
    <sha256> peace16_solver.cpp
    <sha256> peace16_solver_bruteforce.cpp
    <sha256> peace16_certificate.tsv
    <sha256> peace16_certificate_bruteforce.tsv
    AUDIT_OK

The recorded five-thread runs took about 78 seconds each. Runtime is not
part of either proof. Both audit scripts read the certificates from their
own directory, so run them after the solvers have written those files (or
against the shipped copies).


What is checked, and what that means
------------------------------------
The reductions of Sections 2, 4-6 and 8-10 of the paper are proved in the
text; the programs carry out the finite search those reductions leave open.

1. Every solver begins with gates that abort on failure. peace15_solver.cpp
   compares its exact subset decision against direct enumeration of all
   C(15,k) subsets on 20,000 pseudorandom instances (profile_enum.cpp:
   100,000), checks three known pair-orbit counts (11,793 / 6,892 / 13,654),
   and regenerates the 247-profile set and compares it with the supplied
   worklist. Both n=16 solvers compare the optimized and brute-force
   completion kernels on 20,000 pseudorandom instances with randomized
   parity cardinalities, check that Z/16Z has 810 necklaces of size 8 and
   that the pair-orbit counts 73,663 (r,c = 7,8) and 42,062 (8,8, no
   relative sign) come out right, and regenerate the 1,898 / 342 profile
   counts.

2. Every pruning rule inside the exact completion decisions is a necessary
   condition for feasibility, so no candidate is discarded unexamined; this
   is what makes the searches exhaustive rather than heuristic.

3. The certificate TSVs are audit logs, not standalone machine-checkable
   proof objects. They record what was searched. The refutations are the
   programs together with the reductions in the paper; re-running the
   programs is what re-establishes them.

4. The audit scripts do not repeat the multi-billion-case sweeps. They check
   the finite bookkeeping around them: the profile lists, the orbit counts
   (by independent Burnside computations), the per-row and total case
   arithmetic, the lower-bound witnesses, and (for n=16) the two-lift
   incidence map and the agreement of the two certificates.

5. CAVEAT for n = 16. peace16_solver.cpp and peace16_solver_bruteforce.cpp
   are the same program apart from the completion kernel; they share profile
   generation, the symmetry quotient, the pair-representative construction,
   the parity-orientation logic and the antidiagonal loop. Their agreement
   therefore tests the kernel, not the chassis. Unlike n=15, there is as yet
   no fully independent second enumerator for n=16. Writing one from
   Sections 8-9 of the paper is the most valuable check that remains open.
