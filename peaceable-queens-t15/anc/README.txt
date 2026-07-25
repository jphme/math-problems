Ancillary files for:

  "Peaceable queens on the 15x15 torus: the exact value t(15)=20"
  Jan Philipp Harries, July 2026

Files
-----
peace15_solver.cpp            The proof solver. Exhaustively decides all 247
                              canonical size profiles (Sections 5-6 of the
                              paper). C++17 + OpenMP.
peace15_audit.py              Independent audit: regenerates the 247-profile
                              worklist, verifies all 43 fixed-pair orbit
                              counts by Burnside's lemma, checks the row
                              arithmetic and column total of the certificate,
                              and re-counts the 20+20 witness. Python 3, no
                              third-party dependencies.
profile_enum.cpp              The second, independently written exact
                              enumerator (different symmetry quotient,
                              different completion algorithm: exact 7+8
                              meet-in-the-middle instead of DFS with
                              dynamic-programming bounds). C++20.
WORKLIST-2026-07-25.tsv       The 247 canonical size profiles. The solver
                              regenerates this set from scratch and refuses
                              to run if it differs.
peace15_certificate.tsv       Per-profile certificate of the recorded
                              five-thread run.
peace15_certificate_run2.tsv  Per-profile certificate of the recorded
                              three-thread run. All columns except the
                              per-profile timing agree with the file above.
README.txt                    This file.

Requirements
------------
A C++17 compiler with OpenMP for the solver (g++ recommended), a C++20
compiler for the enumerator (clang++ or g++), and Python >= 3.10 for the
audit script. No third-party libraries.

Run: the upper bound
--------------------
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

The recorded five-thread run took about 60 seconds. Runtime is not part of
the proof. Note that peace15_audit.py reads peace15_certificate.tsv from its
own directory, so run it after the solver has written that file (or against
the shipped copy).

Run: the independent enumerator
-------------------------------
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

What is checked, and what that means
------------------------------------
The reductions of Sections 4-6 of the paper are proved in the text; the
programs carry out the finite search those reductions leave open.

1. Both programs begin with gates that abort on failure: the solver compares
   its exact subset decision against direct enumeration of all C(15,k)
   subsets on 20,000 pseudorandom instances (the enumerator: 100,000),
   checks three known pair-orbit counts (11,793 / 6,892 / 13,654), and
   regenerates the 247-profile set and compares it with the supplied
   worklist.

2. Every pruning rule inside the exact subset decision is a necessary
   condition for feasibility, so no candidate is discarded unexamined; this
   is what makes the search exhaustive rather than heuristic.

3. The certificate TSVs are audit logs, not standalone machine-checkable
   proof objects. They record what was searched. The refutation is the
   program together with the reductions in the paper; re-running the program
   is what re-establishes it.

4. peace15_audit.py does not repeat the multi-billion-case sweep. It checks
   the finite bookkeeping around it: the profile list, the orbit counts (by
   an independent Burnside computation), the per-row and total case
   arithmetic, and the lower-bound witness.
