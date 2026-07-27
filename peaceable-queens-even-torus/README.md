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

The four-parameter construction separates square parities and extends the
plaid idea of Clinch, Drescher, Huynh and Saffidine. It is strictly larger
than the classical two-parameter plaid family.

## Contents

- [`peace_even_torus.pdf`](peace_even_torus.pdf): the 20-page paper.
- [`peace_even_torus.tex`](peace_even_torus.tex): self-contained LaTeX source.
- [`peace_even_torus-arxiv.tar.gz`](peace_even_torus-arxiv.tar.gz): source and
  ancillary files for submission or fresh extraction.
- [`anc/README.txt`](anc/README.txt): proof-object inventory, exact
  environments, and full rerun commands.
- [`anc/SHA256SUMS`](anc/SHA256SUMS): integrity manifest.

The ancillary bundle contains two exact rational branch trees and independent
checkers, the complete 760-cut library and 122 finite-envelope records, two
independently written \(n=15\) enumerators, a union-domain \(n=16\) search,
the \(n=17\) and small-even sweep sources and frozen outputs, and direct
witness checks.

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
objects and audits the frozen outputs of the multi-billion-case enumerations;
the full recomputation commands are in `anc/README.txt`.

An immutable snapshot of the released ancillary data is commit
[`c55eb4858c15df01af6ffde5985aa4681244bbd3`](https://github.com/jphme/math-problems/tree/c55eb4858c15df01af6ffde5985aa4681244bbd3/peaceable-queens-even-torus/anc).

The paper contains a concise disclosure of the AI tools used in discovery,
drafting, code generation, and verification. The author takes responsibility
for the final mathematical claims and presentation.
