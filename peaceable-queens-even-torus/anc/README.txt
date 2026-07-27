Ancillary files for

  "Peaceable queens on even tori: an exact parity formula"
  Jan Philipp Harries, July 2026

The paper proves

  t(2q) = max over (r0,r1,c0,c1) in {0,...,q}^4 of
          min(r0*c1 + r1*c0,
              (q-r0)*(q-c0) + (q-r1)*(q-c1))

for every positive integer q, and also proves t(15)=20 and t(17)=28.

The paper records the exact commit of an immutable public snapshot.  The
canonical repository path is:

  https://github.com/jphme/math-problems/tree/main/
  peaceable-queens-even-torus/anc

SHA256SUMS binds every other released file.  Verify it with:

  shasum -a 256 -c SHA256SUMS


One-command portable audit
--------------------------

From this directory, run:

  uv run --isolated --python 3.14.6 \
    --with sympy==1.14.0 --with mpmath==1.3.0 \
    python verify_bundle.py

The final line is:

  PEACEABLE_QUEENS_RELEASE_BUNDLE_OK

The recorded environment is CPython 3.14.6 and SymPy 1.14.0.  The other
Python verifiers use only the standard library.  The C++ sources require
C++20 unless their header comments state C++17.  Recorded rebuilds used
Apple Clang 21.0.0; the n=16 union enumerator was also reproduced under
GCC 14 with OpenMP and Clang 17 in serial mode.

The one-command audit does not rerun the multi-billion-case C++ enumerations
or recompute all finite-ladder trees.  It verifies their frozen outputs,
coverage, input hashes, orbit counts, representative hashes, and witness
counts.  The commands below rerun individual proof computations.


Even theorem for q >= 130
-------------------------

even_c527_sym_mc.json.gz
  Exact global branch certificate over the 42-equation moment relaxation.

even_local_core_mc.json.gz
  Exact local-core branch certificate.

verify_even_branch_certificate.py
  Delivered exact rational checker for both trees.

verify_even_finite_independent.py
  Separately written checker.  It derives the 42 moment rows from torus
  incidence fibres, rechecks the trees, and tests tampered certificates.

even_finite_support_cuts.json
verify_even_finite_algebra.py
  Compact duals and exact checks for the support cuts used in the local
  algebraic finish.

verify_even_finite_prose.py
  Independent symbolic and exact-integer audit of the displayed local proof.
  This is the only verifier requiring SymPy.

verify_even_q_ge_130_bundle.py
  Driver for the delivered branch and local-algebra checks.

Run:

  python verify_even_q_ge_130_bundle.py
  python verify_even_finite_independent.py
  python verify_even_finite_prose.py


Finite cut envelope
-------------------

benders_cuts.json
  The 76 legacy support-cut polynomials.

new_dual_cuts.json
  The 684 delivered support cuts with rational duals.

verify_support_duals.py
recovered_benders_duals.json
moment_model.json
  A standalone exact verifier for all 760 cuts, together with frozen
  recovered witnesses and the derived moment model.

envelope_checker.py
  Portable exact integer-box engine.  Both cut inputs are resolved relative
  to this directory; no research-tree path is required.

records_q003_q020/
records_q021_q129/
  Complete records for q=3,5 and q=10,...,129.

check_envelope_records.py
  Checks the exact coverage, terminal accounting, witnesses, and input
  hashes of all 122 records.

Recompute selected orders into a fresh directory:

  python envelope_checker.py 21 22 23 --records-dir fresh-records


The n=15 search
---------------

peace15_solver.cpp
peace15_certificate.tsv
peace15_certificate_run2.tsv
  The C++17 proof enumerator and two complete outputs.

profile_enum.cpp
peace15_independent_results.jsonl
check_peace15_independent_results.py
  Separately written C++20 meet-in-the-middle enumerator, its complete
  247-profile output, and a strict coverage checker.

WORKLIST-2026-07-25.tsv
peace15_audit.py
check_witness15.py
  Profile worklist, independent profile/orbit/certificate audit, and direct
  black-white pair witness check.

Typical builds:

  g++ -O3 -fopenmp -std=c++17 peace15_solver.cpp -o peace15_solver
  ./peace15_solver --worklist WORKLIST-2026-07-25.tsv \
    --output fresh_peace15_certificate.tsv

  c++ -O3 -std=c++20 profile_enum.cpp -o profile_enum
  ./profile_enum --batch --worklist WORKLIST-2026-07-25.tsv \
    --results fresh_peace15_results.jsonl --log fresh_peace15_logs


The n=16 union-domain search
----------------------------

peace16_union_enum.cpp
peace16_union_certificate.tsv
peace16_union_audit.py
  The primary direct n=16 proof search.  It searches the union of all 1,898
  ordered completion profiles, tests 3,226,530,570 antidiagonal masks and
  then 38,830,322 diagonal masks literally, and finds no 33+33 placement.
  The Python audit independently regenerates all representative lists,
  hashes, Burnside counts, and certificate totals.

Build and rerun serially:

  c++ -O3 -std=c++20 peace16_union_enum.cpp -o peace16_union_enum
  ./peace16_union_enum --output fresh_peace16_union_certificate.tsv
  python peace16_union_audit.py \
    --certificate fresh_peace16_union_certificate.tsv \
    --source peace16_union_enum.cpp

peace16_solver.cpp
peace16_solver_bruteforce.cpp
peace16_certificate.tsv
peace16_certificate_bruteforce.tsv
peace16_audit.py
check_witness16.py
  The earlier 677-job search and two completion-kernel outputs, retained as
  secondary cross-checks.


General-n finite searches
-------------------------

general_sweep/solver_b.cpp
general_sweep/audit_b.py
general_sweep/results/
  A C++20 general-n exact enumerator, its independent standard-library
  audit, and complete UNSAT records for the upper targets:

    n=8, target=9
    n=12, target=19
    n=14, target=26
    n=17, target=29
    n=18, target=43

Audit one result, for example:

  cd general_sweep
  python audit_b.py --n 17 --target 29 \
    --records results/n17_t29_unsat.jsonl

general_sweep/impl_a/
  Source and frozen n=17 target-29 output from the second implementation.

check_witness17.py
  Direct cell-by-cell and pairwise check of the displayed 28+28 witness.


Proof-object boundary
---------------------

The branch trees and support duals are standalone exact proof objects: their
rational multipliers can be checked without solving an optimization problem.
The finite-ladder records and exhaustive-search outputs are audit records.
Their proofs are the short released source programs together with the
reductions in the paper; rerunning those sources re-establishes the finite
computations.
