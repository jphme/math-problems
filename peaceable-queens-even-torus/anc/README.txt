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

LICENSE.txt states the MIT license for the released Python and C++ source.
The article and machine-readable proof/data objects retain their stated
copyright status.


One-command release verification
--------------------------------

From this directory, run:

  uv run --isolated --python 3.14.6 \
    --with sympy==1.14.0 --with mpmath==1.3.0 \
    python verify_bundle.py

The final line is:

  PEACEABLE_QUEENS_RELEASE_BUNDLE_OK

The recorded environment is CPython 3.14.6 and SymPy 1.14.0.  The other
Python verifiers use only the standard library.  A C++17 compiler available
as g++ is also required.  The released C++ sources use C++17 or C++20 as
specified in the build commands below.  Recorded rebuilds used Apple
Clang 21.0.0; the n=16 union enumerator was also reproduced under GCC 14
with OpenMP and Clang 17 in serial mode.

The driver labels its actions explicitly:

  EXACT CERTIFICATE REPLAY
    rechecks the rational branch trees, support duals, and displayed algebra;

  FULL EXACT COMPUTATION RERUN
    compiles box_engine.cpp and repeats all 122 finite-envelope searches;

  FROZEN-OUTPUT AND PROVENANCE AUDIT
    checks the compact envelope summaries, the Python/C++ cross-check ledger,
    and the outputs of the multi-billion-case board enumerations.

The one-command verification therefore re-establishes finite-envelope domain
coverage from source.  It does not rerun the much larger n=15--18 board
enumerations; their audits check domains, orbit representatives, hashes,
totals, and witnesses.  The commands below rerun individual computations.


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
  Portable Python exact integer-box engine.  Both cut inputs are resolved
  relative to this directory; no research-tree path is required.

box_engine.cpp
run_cpp_ladder.py
  Separately implemented C++17 engine and its Python driver.  The C++ source
  has SHA-256

    ea916eb518261a3bbe9558bcb95ec8471d9a765e15667d767eafe35636af9ae2

  exactly as recorded by every q=61,...,129 summary.  The C++ and Python
  programs implement the same exact box algorithm; agreement is an
  implementation cross-check, not a conceptually different proof method.

records_q003_q020/
records_q021_q129/
  Compact run summaries for q=3,5 and q=10,...,129.  They contain status,
  witnesses, input hashes, and aggregate search statistics, but not the
  split nodes or terminal boxes.  The historical q<=60 summaries omit an
  engine-source field; q=61,...,129 bind box_engine.cpp by SHA-256.

check_envelope_records.py
  Recomputes H exactly for every q and checks the order set, schemas, source
  and input hashes, thresholds, witnesses, and aggregate node/leaf accounting
  of all 122 summaries.  It does not reconstruct geometric coverage.

replay_finite_envelope.py
  Canonical full proof rerun.  It builds box_engine.cpp with

    -std=c++17 -O3 -Wall -Wextra -Werror -pedantic

  repeats every q=3,5,10,...,129 search, and compares all proof-relevant
  non-runtime fields with the frozen summaries.  Run:

    python replay_finite_envelope.py

Recompute selected full records into a fresh directory:

  python envelope_checker.py 21 22 23 --records-dir fresh-records

or with the C++ implementation:

  python run_cpp_ladder.py 3 5 --start 10 --end 129 \
    --records-dir fresh-cpp-records

finite_envelope_python_crosscheck_q061_q129.json
check_finite_backend_crosscheck.py
  Frozen ledger of a complete q=61,...,129 rerun with the separately written
  Python implementation, matching every proof-relevant C++ envelope field.
  The checker audits the ledger, source and cut hashes, order coverage, and
  normalized per-order digests; it does not rerun the Python searches.

crosscheck_finite_backends.py
  Recreates that slower second-language ledger.  Four parallel workers were
  used for the released run:

    python crosscheck_finite_backends.py --start 61 --end 129 --jobs 4 \
      --output fresh-python-crosscheck.json


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
The finite-ladder JSON files and the exhaustive-search outputs are audit
records, not serialized coverage certificates.  Their proofs are the short
released source programs together with the reductions in the paper.  The
one-command driver reruns the complete finite ladder; the larger board
enumerations can be rerun with the commands in their sections above.
