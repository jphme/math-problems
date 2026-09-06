# Lean 4 formalization — peaceable queens on even toroidal boards

Companion formalization for *Peaceable queens on even tori: an exact parity
formula* (`peace_even_torus.tex`, published together with this directory in
[`jphme/math-problems/peaceable-queens-even-torus`](https://github.com/jphme/math-problems/tree/main/peaceable-queens-even-torus)),
written at the request of an OEIS editor reviewing the A279405 contribution.
It proves the paper's main theorem (`thm:main`, printed Theorem 2):

```
PeaceableQueens.evenTorusTheorem : ∀ q : ℕ, 0 < q → t (2 * q) = H q
```

with `t n` the toroidal peaceable-queens number defined from actual queen
placements on `ZMod n × ZMod n`, and Lean's `H q` the paper's `H(2q)`.
The development builds with **zero `sorry`** and no upper-bound or
certificate hypothesis.

## Documents

1. **[`FORMAL_PROOF.md`](FORMAL_PROOF.md)** — the proof of `thm:main` rewritten
   as a dependency-ordered sequence of formal statements S1–S66, each tagged by
   formalization status, with exact specifications of the finite certified
   objects the upper bound rests on.
2. **[`PAPER_CORRESPONDENCE.md`](PAPER_CORRESPONDENCE.md)** — every numbered
   result of the paper and every obligation S1–S66 mapped to its exact Lean
   statement, with the coverage limits.
3. **[`FORMAL_PROOF_GUIDE.pdf`](FORMAL_PROOF_GUIDE.pdf)** ([LaTeX source](FORMAL_PROOF_GUIDE.tex)) —
   a four-page guide: the argument in reading order, paper/Lean
   cross-references, the source manifests and the trusted base.
4. **[`VERIFICATION.md`](VERIFICATION.md)** — the recorded complete build,
   the endpoint axiom audit, and what the repository's continuous integration
   checks.

The formalization is complete for the even theorem. It does not assert that
every statement in the paper has a literal Lean counterpart: the real-valued
LP optimum, the odd-order results, divisor lifting and the plaid comparisons
are outside the exported statements. The finite range `3 ≤ q ≤ 129` is proved
by a different route from the paper's cut-envelope engine (see below).

## What is formalized

| Result | Lean name | File |
|---|---|---|
| Board, attacks, peaceability, `t n` (A279405), `H q` (= paper's `H(2q)`) | `Cell`, `SharesLine`, `IsPeaceable`, `HasPeaceable`, `t`, `H` | `Defs.lean` |
| `m ≤ t n ↔ HasPeaceable n m` | `le_t_iff` | `Defs.lean` |
| Line-colouring equivalence (paper `lem:lines`): queens are eliminated | `hasPeaceable_iff_lineSets` | `LineColouring.lean` |
| `t n = lineMax n` — `t` becomes finitely computable | `t_eq_lineMax` | `LineColouring.lean` |
| Parity labels, fibres and counts on `ZMod (2q)` | `Parity.parityClass`, `card_parityClass`, `card_parity_filter_compl` | `Parity.lean` |
| Parity-separated construction (paper `prop:lower`; arbitrary sets and explicit label choices) | `paritySeparated_counts`, `parityBlackCells_eq_lineCells`, `parityWhiteCells_eq_lineCells`, `H_le_t` | `LowerBound.lean` |
| **Lower bound, all q: `H q ≤ t (2*q)`** | `H_le_t` | `LowerBound.lean` |
| **Upper bound, every `q ≥ 130`** (paper `thm:q130`) | `LargeOrderCertified.large_order_bound` | `UpperBound/LargeOrderCertified.lean` |
| **Upper bound, every `3 ≤ q ≤ 129`** | `Generated.Finite.finite_range_bound` | `UpperBound/Generated/FiniteRange.lean` |
| **Upper bound and equality, every positive q** | `upperBoundStatement`, `evenTorusTheorem` | `Main.lean` |
| `H` values of paper Table `tab:Hvals` (`H(2)…H(40)`) | `H_one` … `H_twenty` | `SmallBoards.lean`, `Values.lean` |
| Complete base cases: `t 2 = H 1`, `t 4 = H 2`, using kernel decisions | `t_two`, `t_four` | `SmallBoards.lean` |
| Explicit asymptotic corollaries and displayed `t` values (paper `cor:asym`, `cor:values`) | `even_bounds`, `even_asymptotic`, `even_density_limit`, `t_sixteen`, `t_eighteen`, `t_twenty`, `t_forty` | `UpperBound/Asymptotics.lean`, `Corollaries.lean` |
| Reduction of `thm:main` to the upper-bound statement | `evenTorusTheorem_of_upperBound` | `TheoremStatement.lean` |
| McCormick, exact dual (`lem:dualleaf`), support-cut (`lem:cutsound`) and branch-coverage (`lem:branchsound`) soundness | `mccormick_*`, `linear_dual_upper_bound`, `support_weighted_dual_sound_indicator`, `CoverTree.locate` | `UpperBound/CertificateCore.lean` |
| Semantic 42-row/64-atom moment system (`lem:moments`) and flat certificate-order 42/95/22/64 model | `MomentModel`, `LPModel` definitions | `UpperBound/MomentModel.lean`, `UpperBound/LPModel.lean` |
| Closed semantic/flat compatibility checks (42 × 64 atom and 42 × 30 RHS coefficients) | `moment_coefficients_compatible`, `moment_rhs_*_compatible` | `UpperBound/ModelCompatibility.lean` |
| Sound concrete dual-leaf, empty-chamber, plaid and core checks | `DualLeaf.check_sound`, `ScaledIntDualLeaf.Sound`, `checkEmpty_sound`, `checkPlaid_contains`, `checkCore_sound` | `UpperBound/DualLeaf.lean`, `UpperBound/ScaledIntDualLeaf/`, `UpperBound/LeafChecks.lean` |
| Checked split nodes of the branch trees | `splitNodeOK_coverTree` | `UpperBound/BranchCertificate.lean` |
| Profile identities, continuous upper bound (`lem:Hupper`), lower bound (`lem:Hlower`) and escape comparison (`lem:escape`) | `profile_identities`, `profile_min_le_kappa_s17`, `H_le_floor_s18`, `H_lower_s19`, `H_escape_s20` | `UpperBound/ProfileAlgebra.lean` |
| Even-torus configurations, eight counts and normalized profile | `Configuration`, `outerCount`, `normalizedProfile_range` | `UpperBound/Configuration.lean` |
| Non-D/A line-pair bijections and exact two-point D/A fibres (`lem:inc`) | `*_bijective`, `card_diagonalAntidiagonalFibre_of_image` | `UpperBound/Incidence.lean` |
| Configuration-to-moment bridge: block frequencies, all 42 equations, nonnegativity, objectives | `aggregateDAAtomCount_eq`, `configurationWeights_satisfiesMoments`, `configurationWeights_blackTotal`, `configurationWeights_whiteTotal` | `UpperBound/BlockMoments.lean`, `UpperBound/ConfigurationMoments.lean` |
| Budget/complement (`lem:budget`) and canonical chamber (`lem:chamber`) under all board symmetries | `budget_or_complement`, `outerCount_*Config`, `exists_chamber` | `UpperBound/Symmetry.lean` |
| Configuration-to-relaxation feasibility (`def:OPT` in configuration form) | `configurationLPVector_leafFeasible` | `UpperBound/ConfigurationBridge.lean` |
| Support cuts 609 and 559 (`lem:cuts`): kernel-checked columnwise support and the polynomials `F_B`, `F_W` | `cut609_black_bound`, `cut559_white_bound`, `cut609_configuration_black`, `cut559_configuration_white` | `UpperBound/SupportCuts.lean`, `UpperBound/LargeOrderFinish.lean` |
| Local algebra (`lem:basic`, `lem:dichotomy`) and the integrality step | `Local.basic`, `Local.defect_dichotomy`, `zeta_ge_two_of_natural_defects` | `UpperBound/LargeOrderAlgebra.lean` |
| Local finish on configurations (`prop:caseA`, `prop:caseB`, `thm:q130`) | `configuration_local_finish`, `configuration_finish` | `UpperBound/LargeOrderFinish.lean` |
| Integer-box soundness (`lem:boxops`, `lem:boxsound`): splitting, pruning, tightening, interval and corner discharge, tree inference | `split_covers_integer`, `endpoint_prune_sound`, `validTighten_sound`, `interval_discharge_sound`, `corner_check_discharge`, `integer_box_inference` | `UpperBound/FiniteLattice.lean` |
| Finite acceptance to `t(2q) ≤ H q` | `finite_order_bound_of_tree_at` | `UpperBound/FiniteCertificateConsequences.lean` |

## How the upper bound is proved

* `q = 1, 2`: `SmallBoards.lean`, kernel decisions after translating one queen to
  the origin.
* `3 ≤ q ≤ 129`: one complete action tree per order, embedded in
  `UpperBound/Generated/Finite/Q003.lean` … `Q129.lean` (13,403,719 nodes in
  total). Each tree is decoded and checked node by node by the fail-closed
  validator of `FiniteLattice.lean`; every discharge uses one of the 76 legacy
  support cuts of the paper's library, each with a kernel-checked support
  witness in `UpperBound/RecoveredFiniteCutSupport/`. The threshold `12b + 6`
  with an explicit profile witness `b ≤ H q` gives `min(B,W) ≤ H q` by
  integrality. This route is self-contained: it uses neither the paper's C++
  cut-envelope engine nor its separate exhaustive sweeps for `q = 4, 6, 7, 8, 9`.
  Orders `q = 3..9` use the cached checker, `q = 10..129` the fast checker;
  `FastFiniteChecker.acceptedFast_eq` proves the two equal for every input.
* `q ≥ 130`: the 42-equation moment relaxation, the two rational branch trees
  (`UpperBound/Generated/Even/`, 6,929 and 4,423 nodes, all 5,007 dual leaves
  checked by kernel `decide`), and the algebraic local finish, exactly as in
  the paper's Sections 3–5.

`Main.lean` assembles the three ranges; `Assembly.lean` shows they cover every
positive `q`.

## Building

```
elan self update            # or install elan first
cd lean                     # this directory
lake exe cache get          # fetch Mathlib build cache
python3 scripts/build_project_serial.py --plan  # inspect local dependency order
python3 scripts/build_project_serial.py         # one watched module at a time
scripts/run_with_memory_limit.sh lake --rehash build  # final acceptance gate
```

Pinned toolchain: `leanprover/lean4:v4.32.2`, Mathlib `v4.32.2`.

Do not start a full build with missing generated modules: Lake may run large
compilations concurrently. The Python serial driver orders all local modules
dependency-first, stops on any failure, and forwards interrupts to the memory
watchdog for descendant cleanup. Fetch the external dependency cache first.
Use `--target PeaceableQueens.Main` for the complete theorem's dependency
closure and `--target PeaceableQueens.Corollaries` for the closure including
the exported paper corollaries. `PeaceableQueens.TheoremStatement` alone
contains only the proposition and a conditional assembly lemma; building it
does not verify the general upper bound. Per-module output is kept in
`.lake/serial-project-logs/`. A cold build of the local certificate modules
takes hours even after fetching the Mathlib cache; the serial driver keeps
this work within the resource guard. Heavy commands use
`run_with_memory_limit.sh`, normally with a 12 GiB aggregate descendant-RSS
cutoff and a system free-memory check; this sampled watchdog is not a hard
global memory limit. It uses macOS process and memory tools (`zsh`,
`memory_pressure`); on other platforms use an equivalent resource guard.
`build_project_serial.py --plan` itself is portable and prints the module
order for sequential `lake build +MODULE` calls. Running plain `lake build`
with default parallelism on the hand-written modules alone already needs
several gigabytes per Lean process; use `-j3` or fewer on a 16–32 GB machine.

The generated `Finite/Q*.lean` files contain multi-megabyte encoded-string
lines. The repository's `.gitattributes` disables their text diffs and marks
them as generated. Their raw Lean source remains available for inspection;
`scripts/generate_encoded_finite.py --check` (in the working repository)
validates the payloads against the pinned cut inputs.

## Trusted base

The mathematical proof terms are checked by the Lean kernel. Generic
soundness, the individual support bounds, the analytic estimates and the small
boards use only `propext`, `Classical.choice` and `Quot.sound`. Scaled-integer
dual-leaf checks use kernel `decide`.

The main endpoints depend on **3 standard axioms and 483 native computation
axioms**: 356 branch batches (`split_batch_*_ok`, `terminal_batch_*_ok` in
`Generated/Even/`) and 127 finite certificate acceptances
(`certificate_accepted` in `Generated/Finite/`). Each `native_decide` decides a
Boolean checker on concrete certificate data and is consumed by a kernel-checked
soundness theorem; `native_decide` additionally trusts Lean's compiler/runtime
and the evaluated library implementations, so it is not kernel-only
computation. `scripts/check_upper_bound_axioms.py` compares Lean's axiom report
for both endpoints against this exact allowlist, which it computes from the
generated sources rather than hard-coding it.

`Values.lean` is an optional module with 18 additional native evaluations
(`H 3` through `H 20`); `H 1` and `H 2` are kernel proofs in `SmallBoards`.
The optional values are outside the main theorem's import closure and proof
terms. The four named numerical corollaries in `Corollaries.lean` depend on
their individual value computations.

To reproduce the endpoint statement and axiom audit after building:

```sh
scripts/run_with_memory_limit.sh lake env lean scripts/AuditUpperBound.lean > .lake/final-upper-bound-audit.log 2>&1
python3 scripts/check_upper_bound_axioms.py .lake/final-upper-bound-audit.log
```

The Python step only validates Lean's report against the documented allowlist;
it does not replace running Lean or constitute a proof checker.

## Minimal verification source set

[`VERIFICATION_FILES.txt`](VERIFICATION_FILES.txt) lists the exact transitive
source closure of `PeaceableQueens.Main`: **892 Lean modules plus
`lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` (895 files)**.
Paths are relative to this directory. This is minimal at the file level for
the current imports, not a claim that every imported declaration is used by
the final proof term. The project also needs the external packages pinned in
`lake-manifest.json` and the pinned Lean toolchain. `.lake/` is fetched/built.

All generated Lean files in that list are proof inputs and must be retained.
Logs, compiled objects, benchmarks, C++/Python search tools and the paper's
ancillary bundle are not inputs to Lean's endpoint proof. The root
`PeaceableQueens.lean` is an optional convenience import; retain it too if
using the default `lake build` target instead of the explicit `Main` target.

For all exported paper corollaries, [`REVIEWER_FILES.txt`](REVIEWER_FILES.txt)
adds three modules (`Values`, `UpperBound/Asymptotics`, `Corollaries`):
**895 Lean sources plus the three project files, 898 files total**.

Both lists can be refreshed or checked without running Lean:

```sh
python3 scripts/verification_manifest.py --check
python3 scripts/verification_manifest.py --check --target PeaceableQueens.Corollaries --output REVIEWER_FILES.txt
```

For the documented serial verification workflow, additionally retain
`scripts/build_project_serial.py`, `scripts/run_with_memory_limit.sh`,
`scripts/AuditUpperBound.lean`, and `scripts/check_upper_bound_axioms.py`.
From this directory, with the pinned toolchain installed:

```sh
lake exe cache get
python3 scripts/build_project_serial.py --target PeaceableQueens.Corollaries
scripts/run_with_memory_limit.sh lake --rehash build +PeaceableQueens.Corollaries
scripts/run_with_memory_limit.sh lake env lean scripts/AuditUpperBound.lean > .lake/final-upper-bound-audit.log 2>&1
python3 scripts/check_upper_bound_axioms.py .lake/final-upper-bound-audit.log
```

## What continuous integration checks

The complete closure takes hours to build with a 7.35 GiB peak under the
serial driver, which exceeds hosted-runner budgets. The repository's GitHub
Actions workflow (`.github/workflows/lean.yml` in `jphme/math-problems`)
therefore builds a defined subset on every change to a Lean file:

* every hand-written module — all soundness proofs, the moment model and its
  compatibility checks, the chamber normalization, the two support cuts with
  their kernel-checked columnwise inequalities, the 76 finite cut witnesses,
  the large-order algebra and finish, the finite-lattice checker with its
  fast/cached equivalence, the lower bound, the small boards and the analytic
  corollaries (targets `UpperBound.LargeOrderFinish`,
  `UpperBound.FiniteCertificateConsequences`,
  `UpperBound.EncodedFiniteCertificate`, `UpperBound.FastFiniteChecker`,
  `UpperBound.RecoveredFiniteCutSupport.Aggregate`,
  `UpperBound.BranchCertificate`, `UpperBound.Asymptotics`, `SmallBoards`,
  `Values`); and
* a sample of generated certificate modules: the two smallest finite action
  trees `Generated.Finite.Q003` and `Q004`, and the scaled-integer dual-leaf
  batch `Generated.Even.C527Scaled00Check`.

It also checks both source manifests against the import closure and asserts
that no source contains `sorry`. The complete closure, the final rehash build
and the endpoint axiom audit for `Main.evenTorusTheorem` are verified
offline; [`VERIFICATION.md`](VERIFICATION.md) records the environment, the
module counts, the peak memory and the exact axiom report of that run.

## Companion programs

`scripts/check_paper_values.cpp` reproduces the paper's Table `tab:Hvals`, the
plaid comparisons and witnesses of Remark `rem:plaid16`, and the 200-order
difference histogram with exact integers, cross-checked against direct
enumeration for `q = 0..12`:

```sh
c++ -std=c++17 -O2 -Wall -Wextra -Werror -pedantic scripts/check_paper_values.cpp -o check-paper-values
./check-paper-values     # ends with PAPER_VALUE_CHECKS_OK
```

To regenerate the PDF guide (Tectonic):

```sh
tectonic FORMAL_PROOF_GUIDE.tex
```
