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


Packaging and manifest
----------------------

SHA256SUMS lists every delivered file except itself: one line per file, a
64-character lowercase hexadecimal digest, two spaces, then the path relative
to this directory, sorted by that path.  The archive is built without macOS
metadata (COPYFILE_DISABLE=1) and contains no ._* AppleDouble entries, no
.DS_Store and no __pycache__.

verify_bundle.py calls verify_manifest() before anything else, and that check
is two-sided.  It fails on any missing file, any altered file, and any file
that is present but not listed.  The only paths it ignores are SHA256SUMS
itself, anything below a directory component named __pycache__, and any file
whose suffix is .pyc; empty directories are ignored because only regular
files are compared.  A stray AppleDouble (._name) or .DS_Store file added
while copying the archive through a macOS tool is therefore reported as an
unlisted file and stops the run before any mathematics is checked.  Deleting
the stray files, or re-extracting the original tarball, restores a clean
check.  The shasum command above is one-sided: it verifies the listed files
but does not detect extra ones.


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

Build.  The solver is single-threaded by design and links no OpenMP:

  cd general_sweep
  c++ -std=c++20 -O3 -DNDEBUG -Wall -Wextra -Wpedantic \
    solver_b.cpp -o solver_b
  ./solver_b self-test

Every solve run repeats that self-test, regenerates the oriented job list for
(n, target), and appends one JSON record per finished job.  An interrupted
job is deliberately not recorded, so rerunning the same command resumes.
Rerun a campaign with:

  ./solver_b solve --n 8  --target 9 \
    --records fresh_n8_t9_unsat.jsonl   --log-dir logs-n8-t9
  ./solver_b solve --n 12 --target 19 \
    --records fresh_n12_t19_unsat.jsonl --log-dir logs-n12-t19
  ./solver_b solve --n 14 --target 26 \
    --records fresh_n14_t26_unsat.jsonl --log-dir logs-n14-t26
  ./solver_b solve --n 17 --target 29 \
    --records fresh_n17_t29_unsat.jsonl --log-dir logs-n17-t29
  ./solver_b solve --n 18 --target 43 \
    --records fresh_n18_t43_unsat.jsonl --log-dir logs-n18-t43

A long campaign may be split over disjoint deterministic workers by
congruence class of the job identifier.  Worker r of M runs

  ./solver_b solve --n 17 --target 29 \
    --job-modulus M --job-remainder r \
    --records worker-r.jsonl --log-dir logs-worker-r

and the per-worker record files concatenate to the full record set.  The
remaining options, including the profiles and orbits subcommands, are listed
by ./solver_b --help.

Audit any record file, frozen or fresh:

  cd general_sweep
  python audit_b.py --n 17 --target 29 \
    --records results/n17_t29_unsat.jsonl

The audit regenerates the profiles, oriented jobs, affine pair-orbit counts
(by Burnside) and incidence bounds from scratch; it neither imports nor runs
the solver.  Only the per-job seconds field is expected to differ between
runs of the same campaign.

general_sweep/impl_a/
  Source, its SHA-256 header, and the frozen n=17 target-29 output of the
  second, independently written implementation.  Its completion kernel is a
  suffix DFS; solver_b uses meet-in-the-middle with Pareto queries.  Build
  and rerun with:

    cd general_sweep/impl_a
    c++ -O3 -march=native -std=c++20 -Wall -Wextra -Wpedantic \
      solver.cpp -o impl_a_solver
    ./impl_a_solver --n 17 --tau 29 --output fresh_n17_tau29.tsv

  Per-job logs are written to <output>.job-logs/, and --resume continues an
  interrupted run of the same command from them.  The recorded run split the
  316 jobs into three shards selected with --only-canonical PROFILE and
  merged them; n17_tau29_unsat.tsv is that merge, n17_tau29_unsat.jsonl its
  per-job projection, and n17_tau29_partition_audit.json the closing audit
  record.  The adapter named in that record belongs to the research tree and
  is not released; audit_b.py audits the released solver_b records.

check_witness17.py
  Direct cell-by-cell and pairwise check of the displayed 28+28 witness.


Recorded runs
-------------

Every campaign was run on one shared arm64 macOS machine, recorded platform
string macOS-26.5.2-arm64-arm-64bit-Mach-O, with 48 GB of RAM.  No CPU model
was recorded.  The recorded compiler is Apple clang version 21.0.0
(clang-2100.1.1.101), target arm64-apple-darwin25.5.0.  Timings below are
properties of those runs only; every determinism and audit comparison
excludes them.

Recorded build flags:

  box_engine.cpp
    -std=c++17 -O3 -Wall -Wextra -Werror -pedantic
  peace15_solver.cpp
    -O3 -march=native -fopenmp -DNDEBUG -std=c++17
  profile_enum.cpp
    -O3 -std=c++20 -DNDEBUG
  general_sweep/solver_b.cpp
    -std=c++20 -O3 -DNDEBUG -Wall -Wextra -Wpedantic
  general_sweep/impl_a/solver.cpp
    -O3 -march=native -std=c++20 -Wall -Wextra -Wpedantic

No separate flag record was kept for peace16_union_enum.cpp beyond the
command in its section above and the GCC 14 and Clang 17 rebuilds.  The n=15
and n=16 enumerators were additionally rebuilt under AddressSanitizer and
UndefinedBehaviorSanitizer and rerun over their complete sweeps, 232 s and
244 s, with no diagnostics and identical non-timing certificates.  For the
two general-n solvers the sanitizer builds were exercised on their built-in
self-tests, not on a full campaign.

The frozen outputs and their recorded totals.  SHA256SUMS binds these files
as well; the digests are repeated here so that a single campaign can be
pinned without reading the manifest.

  Finite cut envelope, q=3,5,10,...,129
    records_q003_q020/ and records_q021_q129/, 122 summaries, each recording
    threads=1; 35.390436 s of summed whole-record runtime.  The 69 summaries
    for q=61,...,129 also record the compile flags and the box_engine.cpp
    SHA-256; the 53 earlier ones predate that field.

  n=15, target 21 (peace15_certificate.tsv)
    247 profiles, 6,074,753,568 A-cases, 60.392420 s with 5 threads
    f9d2c858cc6e3a144a10da509a744114080de801df6d216b8cd2783cb2f410b0

  n=15, target 21, repeat run (peace15_certificate_run2.tsv)
    identical non-timing totals, 73.986599 s with 3 threads
    0bbd042d210ec96300d6b4626f08f036a932a0d896f2fa7a06938ff0f5861a6f

  n=15, independent enumerator (peace15_independent_results.jsonl)
    247 profiles, 205.234348 s of summed per-profile search time
    37682b9acb682adbe3a651d8c448a8deaf5046a8c2bd6e40b47f33d149cfbd55

  n=16 union domain (peace16_union_certificate.tsv)
    1,898 profiles in 7 (r,c) blocks, 3,226,530,570 antidiagonal and
    38,830,322 diagonal masks, 2.126498 s
    68e74911c5d1a2851a789dc2b838b1535d6238e1a6a236aebbd6fe002a858865

  n=16 completion kernel (peace16_certificate.tsv)
    13,163,028,768 A-cases, 77.895125 s
    850fc499127193539c06216aa57e91fd6373b3ea2773f4c642654e95def0c086

  n=16 brute-force kernel (peace16_certificate_bruteforce.tsv)
    identical non-timing totals, 78.012232 s
    8f606eac6e0b3bcc31f07b21bcfabf1fddd5d6abd350c9b557765f01dc2948d2

  general_sweep/results/, summed job seconds and A-cases as counted by
  solver_b:

    n=8,  target 9    6 jobs                720 cases  0.000056 s
      2370b1f05fb1281c6c10c360ce1950da5ea717579b3fb3fb0d218fb0c8117ed1
    n=12, target 19   100 jobs        5,111,848 cases  0.033002 s
      bf3025211631d19a68fbb2e2ca0460ce43c668d6e2125c8d8ed7cff611695c09
    n=14, target 26   76 jobs        70,259,455 cases  0.150754 s
      b01d0055b7254f6b46b0b72d2c778eb5d7412c7a0440be254cc7830c4be2b836
    n=17, target 29   316 jobs  157,158,165,660 cases  4520.929574 s
      b815c9966d78cfd12903ee4cd82ef37c8ba379bc39dd6600b7ce3771adf24ed4
    n=18, target 43   259 jobs  228,644,005,008 cases  117.400642 s
      8d2b626ce538a3fd4dc3cf6d6196dd590999c70f6553c8bd60ed051d9684a8d5

  n=17, target 29, second implementation
    (general_sweep/impl_a/n17_tau29_unsat.tsv)
    316 jobs, 158,802,287,408 A-cases as counted by impl_a, 54,743.390673 s
    summed over its three shards
    c5c7d428f333aebc2f9ee4eec5b071e9a775404d7ae58f115a768e9178b1c019
    Its per-job projection general_sweep/impl_a/n17_tau29_unsat.jsonl has
    708c735359f1232e66e775ca4ea9d3ec3fe67c335897752b1777ae1603b21866

The two n=17 case counts differ because the implementations decompose the
search domain differently; each counter is internal to its own enumerator.
peace15_solver.cpp and the three n=16 enumerators use OpenMP, so their wall
times depend on the thread count; profile_enum.cpp, box_engine.cpp and both
general-n solvers are serial.


Proof-object boundary
---------------------

The branch trees and support duals are standalone exact proof objects: their
rational multipliers can be checked without solving an optimization problem.
The finite-ladder JSON files and the exhaustive-search outputs are audit
records, not serialized coverage certificates.  Their proofs are the short
released source programs together with the reductions in the paper.  The
one-command driver reruns the complete finite ladder; the larger board
enumerations can be rerun with the commands in their sections above.
