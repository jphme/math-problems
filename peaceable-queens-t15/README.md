# Peaceable queens on the 15×15 and 16×16 tori: $t(15)=20$ and $t(16)=32$

Paper + the programs that decide the upper bounds.

**Theorem 1.** On the $15\times15$ toroidal chessboard, 20 black and 20 white queens can be placed
with no black queen attacking a white queen, and 21 black and 21 white queens cannot. That is,
$t(15)=20$.

**Theorem 2.** On the $16\times16$ toroidal chessboard, 32 black and 32 white queens can be placed
with no black queen attacking a white queen, and 33 black and 33 white queens cannot. That is,
$t(16)=32$.

These are the first two previously unknown terms of [OEIS A279405](https://oeis.org/A279405), whose
exact values were known only through $n=14$. Clinch, Drescher, Huynh and Saffidine
([arXiv:2406.06974](https://arxiv.org/abs/2406.06974)) had bracketed them to $[20,28]$ and
$[32,35]$; both lower bounds are theirs (for $n=16$, the $(4,4)$-plaid construction).

Both upper bounds are computer-assisted on a common plan: a queen placement is replaced by a
colouring of the $4n$ toroidal lines, elementary counting identities restrict the line-set
cardinalities to finitely many size profiles up to symmetry, and each profile is decided exactly by
a finite search in which every pruning step is a necessary condition — exhaustive, not heuristic.
For $n=15$: 247 canonical profiles, 6,074,753,568 cases. For $n=16$ the diagonal and antidiagonal
sizes must be refined by parity (on an even torus a diagonal and an antidiagonal meet in two cells
or in none): 342 canonical profiles, 677 oriented jobs, 13,163,028,768 cases. No larger placement
exists in either search.

**Verification is not equally strong on the two sides**, and the paper says so: for $n=15$ two
independently written enumerators with different symmetry quotients and different completion
algorithms agree on all 247 profiles; for $n=16$ the two recorded programs share everything outside
the completion kernel, and a genuinely independent second enumerator is the main open hardening
item. See Section 11 of the paper.

## Contents

| File | Description |
|------|-------------|
| [`peace1516.pdf`](peace1516.pdf) | The paper (20 pages) |
| [`peace1516.tex`](peace1516.tex) | LaTeX source (amsart) |
| [`peace1516-arxiv.tar.gz`](peace1516-arxiv.tar.gz) | arXiv submission bundle |
| [`anc/peace15_solver.cpp`](anc/peace15_solver.cpp) | $n=15$ proof solver: decides all 247 canonical profiles (C++17 + OpenMP) |
| [`anc/profile_enum.cpp`](anc/profile_enum.cpp) | $n=15$ second, independently written enumerator — different quotient, different completion algorithm (C++20) |
| [`anc/peace15_audit.py`](anc/peace15_audit.py) | $n=15$ independent audit: worklist regeneration, Burnside check of all 43 orbit counts, certificate arithmetic, witness re-count |
| [`anc/WORKLIST-2026-07-25.tsv`](anc/WORKLIST-2026-07-25.tsv) | The 247 canonical $n=15$ profiles |
| [`anc/peace15_certificate.tsv`](anc/peace15_certificate.tsv), [`anc/peace15_certificate_run2.tsv`](anc/peace15_certificate_run2.tsv) | $n=15$ per-profile certificates, two recorded runs |
| [`anc/peace16_solver.cpp`](anc/peace16_solver.cpp) | $n=16$ solver, optimized completion kernel (C++20 + OpenMP) |
| [`anc/peace16_solver_bruteforce.cpp`](anc/peace16_solver_bruteforce.cpp) | $n=16$ solver, brute-force completion kernel (differs only in the kernel — see the verification caveat) |
| [`anc/peace16_audit.py`](anc/peace16_audit.py) | $n=16$ independent audit: profile regeneration, 14 Burnside orbit counts, two-lift incidence map, witness, certificate cross-check |
| [`anc/peace16_certificate.tsv`](anc/peace16_certificate.tsv), [`anc/peace16_certificate_bruteforce.tsv`](anc/peace16_certificate_bruteforce.tsv) | $n=16$ per-job certificates of both kernels |
| [`anc/README.txt`](anc/README.txt) | Full build/run instructions and what each check does and does not establish |

## Reproduce

```bash
cd anc
# n = 15
g++ -O3 -march=native -fopenmp -DNDEBUG -std=c++17 peace15_solver.cpp -o peace15_solver
OMP_NUM_THREADS=5 ./peace15_solver --worklist WORKLIST-2026-07-25.tsv --output peace15_certificate_new.tsv
python3 peace15_audit.py
# n = 16
g++ -O3 -march=native -fopenmp -std=c++20 peace16_solver.cpp -o peace16_solver
OMP_NUM_THREADS=5 ./peace16_solver --output peace16_certificate_new.tsv
g++ -O3 -march=native -fopenmp -std=c++20 peace16_solver_bruteforce.cpp -o peace16_bf
OMP_NUM_THREADS=5 ./peace16_bf --output peace16_certificate_bf_new.tsv
python3 peace16_audit.py
```

Expected: `ALL_UNSAT` from each solver, `AUDIT_OK` from each audit. Each full sweep takes about a
minute on five threads (the $n=16$ sweeps run in well under a minute on Apple Silicon even
single-threaded).

## Provenance

Produced with substantial use of AI systems; the paper's final section discloses the roles
precisely (reduction programme and verification by Anthropic Claude agents; final proof documents,
solvers and audits by OpenAI GPT-5.6 Pro). The author reviewed the manuscript and takes full
responsibility for its content.
