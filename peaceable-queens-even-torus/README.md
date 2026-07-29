# Peaceable queens on even tori: an exact parity formula

This is the canonical publication directory for the unified paper and its
verification bundle.

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

## Contents

- [`lean/`](lean/): a formalization-ready rewrite of the proof
  ([`lean/FORMAL_PROOF.md`](lean/FORMAL_PROOF.md)) and a Lean 4 / Mathlib
  formalization (zero `sorry`) of its definitional layer, the line-colouring
  reduction, the full lower bound \(t(2q)\ge H(2q)\), the Table-1 values of
  \(H\), and complete small instances of the theorem; written at the request
  of an OEIS editor. See [`lean/README.md`](lean/README.md) for exact scope.
- [`peace_even_torus.pdf`](peace_even_torus.pdf): the 21-page paper.
- [`peace_even_torus.tex`](peace_even_torus.tex): self-contained LaTeX source.
- [`peace_even_torus-arxiv.tar.gz`](peace_even_torus-arxiv.tar.gz): source and
  ancillary files for submission or fresh extraction.
- [`anc/README.txt`](anc/README.txt): proof-object inventory, exact
  environments, and full rerun commands.
- [`anc/SHA256SUMS`](anc/SHA256SUMS): integrity manifest.
- [`anc/LICENSE.txt`](anc/LICENSE.txt): MIT license for the released source.

The ancillary bundle contains two exact rational branch trees and independent
checkers, the complete 760-cut library, 122 compact finite-envelope run
summaries, the exact C++17 finite engine and a separately written Python
same-algorithm cross-check, two independently written \(n=15\) enumerators, a
union-domain \(n=16\) search, the \(n=17\) and small-even sweep sources and
frozen outputs, and direct witness checks.

## Quick audit

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
larger enumerations. Full rebuild
commands for those larger computations are in `anc/README.txt`.

An immutable snapshot of the released ancillary data is commit
[`459046273420a61d51bac18f3a260b4317ec2e62`](https://github.com/jphme/math-problems/tree/459046273420a61d51bac18f3a260b4317ec2e62/peaceable-queens-even-torus/anc).

The paper contains a concise disclosure of the AI tools used in discovery,
drafting, code generation, and verification. The author takes responsibility
for the final mathematical claims and presentation.
