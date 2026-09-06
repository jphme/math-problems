# Verification record

This document records how the Lean development in this directory was checked,
what the result was, and which part of it the repository's continuous
integration repeats. It is the evidence referred to by the paper's
Appendix A.0 and by [`README.md`](README.md). The statements being verified
are

```
PeaceableQueens.upperBoundStatement : ∀ q : ℕ, 0 < q → t (2 * q) ≤ H q
PeaceableQueens.evenTorusTheorem    : ∀ q : ℕ, 0 < q → t (2 * q) = H q
```

in `PeaceableQueens/Main.lean`, together with the exported corollaries in
`PeaceableQueens/Corollaries.lean`.

## Environment

| item | value |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.32.2` (`lean-toolchain`) |
| Mathlib | `v4.32.2` (`lake-manifest.json`; all nine external packages at their pinned revisions) |
| Lake | 5.0.0 |
| machine | Apple Silicon Mac, macOS (Darwin 25.5.0), 48 GB RAM |
| memory guard | `scripts/run_with_memory_limit.sh`, 12 GiB aggregate descendant-RSS cutoff, one Lean compiler at a time |
| sources | the closure of `PeaceableQueens.Corollaries`: 895 Lean modules plus the three project files (`COROLLARIES_FILES.txt`); `PeaceableQueens.Main` needs 892 of them (`VERIFICATION_FILES.txt`) |

## Complete build, 2026-09-06

The sources of this release (revision of 2026-09-06) were built from scratch for all local modules with the serial driver:

```sh
lake exe cache get
python3 scripts/build_project_serial.py --target PeaceableQueens.Corollaries
scripts/run_with_memory_limit.sh lake --rehash build
scripts/run_with_memory_limit.sh lake env lean scripts/AuditUpperBound.lean > .lake/final-upper-bound-audit.log 2>&1
python3 scripts/check_upper_bound_axioms.py .lake/final-upper-bound-audit.log
```

Result:

| step | outcome |
|---|---|
| serial build (`build_project_serial.py`, target `PeaceableQueens.Corollaries` plus the umbrella) | 896 of 896 modules `SERIAL_BUILD OK`, exit 0; 11:27 to 17:10 CEST (5 h 43 min); peak sampled RSS over all module builds 7,743,984 KiB (7.39 GiB), reached by a scaled dual-leaf module of the global tree; no `sorry` warning in any module log |
| `lake --rehash build` (default target, i.e. the umbrella `PeaceableQueens`) | `Build completed successfully (3893 jobs)`; peak 4,177,104 KiB |
| `scripts/AuditUpperBound.lean` | both endpoint statements type-check against the printed propositions; axiom reports written |
| `scripts/check_upper_bound_axioms.py` | `AXIOM_AUDIT_OK` for both endpoints: `standard=3 native=483 unexpected=0` |

The axiom report is kept in
[`verification/final-upper-bound-audit-2026-09-06.log`](verification/final-upper-bound-audit-2026-09-06.log)
(the complete `#print axioms` output for both endpoints), with the gate
transcript in `verification/final-gate-2026-09-06.log` and the serial-build
summary in `verification/serial-build-summary-2026-09-06.txt`.

Both endpoints depend on exactly:

* `propext`, `Classical.choice`, `Quot.sound`;
* 356 native computations `PeaceableQueens.UpperBound.Generated.Even.{C527,Core}.{split,terminal}_batch_NN_ok._native.native_decide.ax_1_1`
  (139 + 39 for the global tree, 89 + 89 for the local tree), each deciding a
  list of `splitNodeOK`, `checkEmpty`, `checkPlaid` or `checkCore` Booleans on
  concrete boxes and consumed by the kernel theorems
  `splitNodeOK_coverTree`, `checkEmpty_sound`, `c527_local_semantics`,
  `checkCore_sound`;
* 127 native computations `PeaceableQueens.UpperBound.Generated.Finite.Qnnn.certificate_accepted._native.native_decide.ax_1_1`
  for `q = 3 … 129`, each deciding the fail-closed validator on one embedded
  action tree and consumed by `acceptedCached_sound`/`acceptedFast_sound` and
  `finite_order_bound_of_tree_at`.

`check_upper_bound_axioms.py` derives this allowlist from the generated
sources (it counts the batch theorems and the 127 orders) and fails on any
missing or additional axiom. The 5,007 scaled-integer dual leaves, the 76
finite support-cut witnesses, the two large-order support cuts, all checker
soundness theorems, the small boards and the analytic estimates carry only the
three standard axioms (their own `#print axioms` lines are in the module
logs of the serial build).

`native_decide` additionally trusts Lean's compiler, runtime and the evaluated
library implementations; it is not kernel-only computation. Everything else in
the proof is checked by the Lean kernel.

After the build, the six diagnostic scripts under `scripts/` were rerun with
`lake env lean`: `CheckEncodedFinite.lean` (`ONE_CORNER_CHECK result=true`),
`CheckFastFinite.lean` (`FAST_FINITE_REGRESSIONS_OK`),
`C527PlaidSemantics.lean` (standard axioms only) and the three benchmark
entry points (`BenchmarkFinite`, `BenchmarkFastFinite`,
`BenchmarkFiniteTables`, type-checked), all exit 0 with no error line. The
2026-09-06 revision differs from the build of 2026-09-05 only in docstrings
and in removed unused declarations; no generated module or checker definition
changed, and that earlier build had the same axiom counts, a rehash build of
3,893 jobs and a peak of 7.35 GiB.

## What continuous integration checks

The complete closure takes hours and about 7.4 GiB, which exceeds the budget
of GitHub-hosted runners. The workflow `.github/workflows/lean.yml` of the
public repository `jphme/math-problems` therefore builds, on every change to
a Lean file:

1. every hand-written module, through the targets
   `PeaceableQueens.UpperBound.LargeOrderFinish`,
   `PeaceableQueens.UpperBound.FiniteCertificateConsequences`,
   `PeaceableQueens.UpperBound.EncodedFiniteCertificate`,
   `PeaceableQueens.UpperBound.FastFiniteChecker`,
   `PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Aggregate`,
   `PeaceableQueens.UpperBound.BranchCertificate`,
   `PeaceableQueens.UpperBound.Asymptotics`, `PeaceableQueens.SmallBoards`
   and `PeaceableQueens.Values` — this covers all soundness proofs, the
   moment model and its compatibility checks, the chamber normalization, the
   two support cuts with their kernel-checked columnwise inequalities, the 76
   finite cut witnesses, the large-order algebra and finish, the
   finite-lattice checker with its fast/cached equivalence, the lower bound,
   the small boards and the analytic corollaries;
2. a sample of generated certificate modules:
   `PeaceableQueens.UpperBound.Generated.Finite.Q003`, `…Q004` (the two
   smallest finite action trees) and
   `PeaceableQueens.UpperBound.Generated.Even.C527Scaled00Check` (one
   kernel-`decide` batch of dual leaves of the global tree);
3. `scripts/verification_manifest.py --check` for both source manifests; and
4. a `grep` asserting that no source contains `sorry`.

What CI does **not** rebuild: the other 813 generated certificate modules,
`Main.lean`, `Corollaries.lean` and the two endpoint theorems. Their
verification is the offline record above. Anyone can repeat it with the
commands in the *Complete build* section; on a machine without the macOS
memory guard, use `build_project_serial.py --plan` to obtain the module order
and build the modules one at a time.

## Reproducing the record

From this directory with the pinned toolchain installed and internet access
for the Mathlib cache:

```sh
lake exe cache get
python3 scripts/build_project_serial.py --target PeaceableQueens.Corollaries
scripts/run_with_memory_limit.sh lake --rehash build
scripts/run_with_memory_limit.sh lake env lean scripts/AuditUpperBound.lean > .lake/final-upper-bound-audit.log 2>&1
python3 scripts/check_upper_bound_axioms.py .lake/final-upper-bound-audit.log
```

The last command must print `AXIOM_AUDIT_OK … standard=3 native=483
unexpected=0` for both endpoints. Expect several hours for the serial build;
the memory guard is a sampled watchdog, not a hard limit.
