# Peaceable queens on even toroidal boards: the exact formula $t(2q)=H(2q)$

Paper + certificates + verifiers for the complete solution of the even case of the toroidal
peaceable queens problem.

**Theorem.** For every positive integer $q$,

$$t(2q) \;=\; H(2q) \;:=\; \max_{0\le r_0,r_1,c_0,c_1\le q}\ \min\bigl(r_0c_1+r_1c_0,\ (q-r_0)(q-c_0)+(q-r_1)(q-c_1)\bigr),$$

where $t(n)$ is the largest $m$ such that $m$ black and $m$ white queens coexist on the
$n\times n$ toroidal board with no black queen attacking a white one
([OEIS A279405](https://oeis.org/A279405), previously known only through $n=14$).

Consequences: every even value is determined forever ($t(16)=32$, $t(18)=42$, $t(20)=51$, ...,
$t(2000)=535824$), and the even-torus density is exactly $(2-\sqrt3)/2 = 0.13397\ldots$ — the
bottom end of the interval $[0.1340,\,0.1402]$ of Clinch, Drescher, Huynh and Saffidine
([arXiv:2406.06974](https://arxiv.org/abs/2406.06974)), whose plaid constructions are thereby
exactly optimal at every even order. The paper also records the new odd values $t(15)=20$ and
$t(17)=28$ (odd orders remain open; there is no odd formula candidate).

The upper bound has four parts: a sound 42-equation moment relaxation of a line-colouring
reformulation; **two exact rational branch certificates** (11,352 nodes in total, every leaf a
rational LP dual or an exact emptiness argument, no floating point anywhere) that localize any
hypothetical counterexample into a narrow core around the plaid profiles; a **four-page
hand-checkable algebraic finish** valid for $q\ge130$ (two certified support-dual cuts, a
four-profile switching average, one AM–GM step, one integrality step — the threshold is the
integer comparison $6{,}760{,}000\ge6{,}759{,}003$); and an **exact integer cut-envelope ladder**
covering $q\le129$.

**Verification tiers, stated plainly** (Section 6.3 of the paper): the ranges $q\ge130$ and
$q\le20$ each have two genuinely independent verifications — in particular both branch
certificates are checked by two programs sharing no code, one of which re-derives the entire
moment system from torus incidence counting. The ladder segment $21\le q\le129$ currently rests
on one exact certified method; the 109 per-order records are shipped so that segment can be
independently redone.

**Provenance**: the mathematics was produced by AI systems (OpenAI GPT-5.6 Pro as mathematician,
Anthropic Claude for orchestration, auditing, refutation and independent verification) over seven
rounds of exchange, 25–27 July 2026; three intermediate lemmas proposed along the way were false
and are recorded in the paper with their exact counterexamples. See Section 8 of the paper for
the full disclosure.

## Contents

| File | Description |
|------|-------------|
| [`peace_even_torus.pdf`](peace_even_torus.pdf) | The paper (23 pages) |
| [`peace_even_torus.tex`](peace_even_torus.tex) | LaTeX source (amsart) |
| [`peace_even_torus-arxiv.tar.gz`](peace_even_torus-arxiv.tar.gz) | arXiv submission bundle (source + `anc/`) |
| `anc/even_c527_sym_mc.json.gz` | Global branch certificate (6,929 nodes) |
| `anc/even_local_core_mc.json.gz` | Local aggregate-core branch certificate (4,423 nodes) |
| `anc/verify_even_branch_certificate.py` | Exact checker for both certificates (stdlib, rational only) |
| `anc/verify_even_finite_independent.py` | Independent from-scratch verifier (derives the moment system itself) |
| `anc/even_finite_support_cuts.json` + `anc/verify_even_finite_algebra.py` | The two support duals + exact algebra checks |
| `anc/verify_even_finite_prose.py` | Independent symbolic check of the paper's algebra (126 checks; needs sympy) |
| `anc/verify_even_q_ge_130_bundle.py` | One-command driver for the whole $q\ge130$ proof |
| `anc/new_dual_cuts.json` | The certified 760-cut support-dual library |
| `anc/envelope_checker.py` + `anc/records_q021_q129/` | Exact ladder engine + the 109 proof-load-bearing records |
| `anc/counterexample_24prime.json` + verifier | Exact refutation of the bypassed switching envelope |
| `anc/peace15_*`, `anc/peace16_*`, `anc/profile_enum.cpp`, ... | The legacy $n=15$/$n=16$ sweep programs (companion note) |
| `anc/SHA256SUMS`, `anc/README.txt` | Integrity manifest + full run instructions |

## Quick check

```bash
cd anc
python3 verify_even_q_ge_130_bundle.py          # EVEN_Q_GE_130_BUNDLE_OK   (~3 s)
python3 verify_even_finite_independent.py even_c527_sym_mc.json.gz even_local_core_mc.json.gz
                                                # EVEN_FINITE_INDEPENDENT_VERIFIER_OK  (~2 s)
python3 verify_counterexample_24prime.py counterexample_24prime.json
shasum -a 256 -c SHA256SUMS
```

`anc/README.txt` documents every file and every command, including the ladder engine
(`python3 envelope_checker.py 3 5 10` reproduces small orders in seconds).

## Companion

The detailed treatment of the $n=15$ and $n=16$ exhaustive sweeps is the companion note in
[`../peaceable-queens-t15/`](../peaceable-queens-t15/).
