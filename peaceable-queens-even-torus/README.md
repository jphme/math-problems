# Peaceable queens on even tori: an exact parity formula

This is the canonical publication directory for the unified paper, its
verification bundle and the Lean 4 formalization of its main theorem.

For the toroidal peaceable queens number \(t(n)\), the paper proves, for every
positive integer \(q\),

\[
t(2q)=
\max_{(r_0,r_1,c_0,c_1)\in\{0,\ldots,q\}^4}
\min\!\left\{
r_0c_1+r_1c_0,\,
(q-r_0)(q-c_0)+(q-r_1)(q-c_1)
\right\}.
\]

Thus every even value is determined and
\[
\lim_{\substack{n\to\infty\\2\mid n}}\frac{t(n)}{n^2}
=\frac{2-\sqrt3}{2}.
\]
The same paper also proves \(t(15)=20\) and \(t(17)=28\).

The four-parameter construction refines the plaid idea of Clinch, Drescher,
Huynh and Saffidine by separating row and column parity classes. The
classical two-parameter plaid family is a subfamily and already gives the
sharp even-order asymptotic density; the parity refinement is exact at each
even order.

Clinch, Drescher, Huynh and Saffidine conjectured (arXiv:2406.06974,
Conjecture 5.1) that on even tori the optimum exceeds the best plaid by at
most two. The theorem confirms this for every even \(n\le400\) (the
difference between the formula and the best plaid takes only the values 0, 1
and 2 there) and replaces the inequality by an exact formula.

## Contents

- [`peace_even_torus.pdf`](peace_even_torus.pdf): the 24-page paper
  (September 6, 2026).
- [`peace_even_torus.tex`](peace_even_torus.tex): self-contained LaTeX source.
- [`peace_even_torus-arxiv.tar.gz`](peace_even_torus-arxiv.tar.gz): source and
  ancillary files for submission or fresh extraction.
- [`lean/`](lean/): the complete Lean 4 / Mathlib proof of the main even
  theorem, `∀ q > 0, t (2*q) = H q` (Lean's `H q` is the paper's `H(2q)`),
  with zero `sorry` and no upper-bound or certificate hypothesis. It covers
  the line-colouring reduction, the parity construction, the 42-equation
  moment relaxation, both rational branch trees, the integer local finish for
  `q ≥ 130`, and complete node-by-node checked action trees for every
  `3 ≤ q ≤ 129`; the two base boards use kernel decisions. Start with
  [`lean/README.md`](lean/README.md); the four-page
  [`lean/FORMAL_PROOF_GUIDE.pdf`](lean/FORMAL_PROOF_GUIDE.pdf) explains the
  argument, [`lean/FORMAL_PROOF.md`](lean/FORMAL_PROOF.md) states it as
  obligations S1–S66, [`lean/PAPER_CORRESPONDENCE.md`](lean/PAPER_CORRESPONDENCE.md)
  maps every numbered result of the paper to its Lean statement (and lists
  what is outside Lean: the real LP optimum, the odd-order theorems, divisor
  lifting, the plaid comparisons), and [`lean/VERIFICATION.md`](lean/VERIFICATION.md)
  records the complete offline build and the endpoint axiom audit.
- [`anc/README.txt`](anc/README.txt): proof-object inventory, exact
  environments, and full rerun commands for the paper's original
  computational verification route.
- [`anc/SHA256SUMS`](anc/SHA256SUMS): integrity manifest.
- [`anc/LICENSE.txt`](anc/LICENSE.txt): MIT license for the released source.

The ancillary bundle contains two exact rational branch trees and independent
checkers, the complete 760-cut library, 122 compact finite-envelope run
summaries, the exact C++17 finite engine and a separately written Python
same-algorithm cross-check, two independently written \(n=15\) enumerators, a
union-domain \(n=16\) search, the \(n=17\) and small-even sweep sources and
frozen outputs, and direct witness checks.

## Lean trusted base and continuous integration

[![Lean](https://github.com/jphme/math-problems/actions/workflows/lean.yml/badge.svg)](https://github.com/jphme/math-problems/actions/workflows/lean.yml)

The two Lean endpoints depend on the three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) and 483 native-computation axioms: 356
branch-tree batches and 127 finite-tree acceptances decided by
`native_decide` on concrete certificate data, each consumed by a
kernel-checked soundness theorem. All generic soundness proofs, the support
inequalities, the small boards and the analytic estimates use the standard
axioms only. `native_decide` additionally trusts Lean's compiler, runtime and
evaluated library implementations.

The complete Lean closure has 895 modules, 816 of them generated certificate
modules, and takes hours to build with a 7.35 GiB peak under the project's
serial driver. That exceeds hosted-runner budgets, so **the CI workflow
[`lean.yml`](../.github/workflows/lean.yml) checks a defined subset on every
change to a Lean file**: every hand-written module (all soundness proofs, the
moment model and its compatibility checks, the chamber normalization, the
support cuts with their kernel-checked columnwise inequalities, the 76 finite
cut witnesses, the large-order algebra and finish, the finite-lattice checker
with its fast/cached equivalence, the lower bound, the small boards and the
analytic corollaries) plus a sample of generated certificate modules (the two
smallest finite action trees `Q003`, `Q004` and one scaled-integer dual-leaf
batch of the global branch tree). It also checks both source manifests
against the import closure and asserts that no source contains `sorry`. The
complete closure, the final rehash build and the endpoint axiom audit are
verified offline; [`lean/VERIFICATION.md`](lean/VERIFICATION.md) records the
environment, the module counts, the peak memory and the exact axiom report,
and [`lean/README.md`](lean/README.md) gives the commands to repeat that
verification.

## Quick audit of the paper's computational route

```bash
cd anc
shasum -a 256 -c SHA256SUMS
uv run --isolated --python 3.14.6 \
  --with sympy==1.14.0 --with mpmath==1.3.0 \
  python verify_bundle.py
```

The last command must end with
`PEACEABLE_QUEENS_RELEASE_BUNDLE_OK`. It checks all portable exact proof
objects, recompiles the C++17 finite engine and reruns all 122
finite-envelope searches, verifies the separately implemented Python
same-algorithm cross-check ledger, and audits the frozen outputs of the
larger enumerations. Full rebuild commands for those larger computations are
in `anc/README.txt`. `lean/scripts/check_paper_values.cpp` reproduces the
displayed `H` values, the plaid comparisons and the 200-order histogram of
Remark 11 with exact integers.

An immutable snapshot of the released ancillary data is commit
[`459046273420a61d51bac18f3a260b4317ec2e62`](https://github.com/jphme/math-problems/tree/459046273420a61d51bac18f3a260b4317ec2e62/peaceable-queens-even-torus/anc);
the bundle is unchanged since.

The paper contains a concise disclosure of the AI tools used in discovery,
drafting, code generation, and verification. The author takes responsibility
for the final mathematical claims and presentation.

## Changelog

Each entry names the paper revision it accompanies; the Git history of this
directory gives the exact files.

- **2026-09-06 — paper dated September 6, 2026; complete Lean proof of the
  theorem.**
  - *Formal proof.* `lean/` now contains the complete Lean 4 proof of the
    upper bound and hence of the theorem for every positive `q` (previously:
    definitional layer, line-colouring reduction, lower bound and small
    instances only). New in the paper: Appendix A.0 describing the
    formalization, its scope and its trusted base, and pointing to this
    directory; a sentence after Proposition 36 noting the independent
    machine-checked finite range. New documents:
    `lean/PAPER_CORRESPONDENCE.md`, `lean/VERIFICATION.md`,
    `lean/FORMAL_PROOF_GUIDE.pdf`; `lean/FORMAL_PROOF.md` updated to the
    completed state; `lean/scripts/check_paper_values.cpp` added. The two
    source manifests are `lean/VERIFICATION_FILES.txt` (closure of `Main`)
    and `lean/COROLLARIES_FILES.txt` (closure of `Corollaries`).
  - *Corrections relative to the September 2 version.* Display (16) typeset
    the definition of `Y` in text mode, fixed. The sentence claiming that
    integrality is used "only" at one point of the local finish was
    corrected (integrality also enters the construction of `H` and the
    finite range). Lemma 26 is stated for every configuration (the chamber
    hypothesis was never needed); the second case of Lemma 12 uses the
    direct nonnegativity bound instead of the bilinear-vertex argument; the
    paragraph after Lemma 17 gives the correct non-interference argument for
    the chamber normalization; the plaid maximum in Remark 11 is written
    over `u,v ∈ {0,…,q}`; the proof of Lemma 35 was reworded.
  - *Presentation.* Appendix A.1 prints the two sparse dual vectors of cuts
    609 and 559, so that Lemma 26 can be checked by hand. File-level
    verification detail (checker names, test parameters, the storage of the
    cut library and of the two support duals) moved from Sections 4–6 into
    Appendix A.1; the acknowledgements were shortened. In `lean/`: the
    docstrings of the load-bearing theorems cite the paper's stable labels,
    unused declarations were removed, and the provenance of the two
    transcribed support duals is documented.
  - *Continuous integration* builds the hand-written modules and a
    certificate sample (see above); the previous workflow built the small
    August development in full.
- **2026-09-02 — paper dated September 2, 2026.** Attribution: the
  introduction and Remark 11 cite Conjecture 5.1 and the swapped plaids of
  Clinch, Drescher, Huynh and Saffidine (arXiv:2406.06974, Section 5) and
  state the numerical relation between the formula and the best plaid for
  `n ≤ 400`. README sentence on the conjecture added.
- **2026-08-02 — no paper change.** Lean 4 formalization of the definitional
  layer, the line-colouring reduction, the full lower bound, the Table 1
  values and the complete small instances `t(2)`, `t(4)`; formalization-ready
  proof rewrite `lean/FORMAL_PROOF.md`; CI workflow building that
  development.
- **2026-07-27 — paper dated July 27, 2026 (initial release).** The unified
  paper with the theorem `t(2q) = H(2q)`, the odd values `t(15) = 20`,
  `t(17) = 28`, and the ancillary verification bundle (snapshot
  `4590462734…`).
