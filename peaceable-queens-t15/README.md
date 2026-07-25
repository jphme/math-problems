# Peaceable queens on the 15×15 torus: $t(15)=20$

Paper + the programs that decide the upper bound.

**Theorem.** On the $15\times15$ toroidal chessboard, 20 black and 20 white queens can be placed
with no black queen attacking a white queen, and 21 black and 21 white queens cannot. That is,
$t(15)=20$.

This is the first previously unknown term of [OEIS A279405](https://oeis.org/A279405), whose exact
values were known only through $n=14$. Clinch, Drescher, Huynh and Saffidine
([arXiv:2406.06974](https://arxiv.org/abs/2406.06974)) had bracketed it to $[20,28]$.

The lower bound is an explicit placement. The upper bound is computer-assisted: a queen placement is
replaced by a colouring of the 60 toroidal lines, elementary counting identities restrict the four
line-set cardinalities to 247 profiles up to a symmetry group of order 14,400, and each profile is
decided exactly by a finite search in which every pruning step is a necessary condition — so the
search is exhaustive, not heuristic. It examined 6,074,753,568 cases and found no $21+21$ placement.

## Contents

| File | Description |
|------|-------------|
| [`peace15.pdf`](peace15.pdf) | The paper (11 pages) |
| [`peace15.tex`](peace15.tex) | LaTeX source (amsart) |
| [`peace15-arxiv.tar.gz`](peace15-arxiv.tar.gz) | arXiv submission bundle |
| [`anc/peace15_solver.cpp`](anc/peace15_solver.cpp) | The proof solver: decides all 247 canonical profiles (C++17 + OpenMP) |
| [`anc/profile_enum.cpp`](anc/profile_enum.cpp) | A second, independently written enumerator — different symmetry quotient, different completion algorithm (C++20) |
| [`anc/peace15_audit.py`](anc/peace15_audit.py) | Independent audit: worklist regeneration, Burnside check of all 43 orbit counts, certificate arithmetic, witness re-count |
| [`anc/WORKLIST-2026-07-25.tsv`](anc/WORKLIST-2026-07-25.tsv) | The 247 canonical size profiles |
| [`anc/peace15_certificate.tsv`](anc/peace15_certificate.tsv), [`anc/peace15_certificate_run2.tsv`](anc/peace15_certificate_run2.tsv) | Per-profile certificates of two recorded runs |
| [`anc/README.txt`](anc/README.txt) | Full build/run instructions and what each check does and does not establish |

## Reproduce

```bash
cd anc
g++ -O3 -march=native -fopenmp -DNDEBUG -std=c++17 peace15_solver.cpp -o peace15_solver
OMP_NUM_THREADS=5 ./peace15_solver --worklist WORKLIST-2026-07-25.tsv --output peace15_certificate.tsv
python3 peace15_audit.py
```

The solver ends in `ALL_UNSAT A_checked=6074753568`, the audit script in `AUDIT_OK`. The recorded
five-thread run took about 60 seconds; runtime is not part of the proof. The second enumerator:

```bash
clang++ -O3 -std=c++20 -DNDEBUG -Wall -Wextra -Wpedantic profile_enum.cpp -o profile_enum
./profile_enum --self-test --random 100000
./profile_enum --batch --worklist WORKLIST-2026-07-25.tsv --results results.jsonl --log logs
```

It reports UNSAT for all 247 profiles over 6,241,793,402 completions — a different case count,
because it uses a different symmetry quotient. About 200 seconds single-threaded.

Both programs begin with gates that abort on failure (brute-force comparison of the subset kernel
against direct enumeration on 20,000 resp. 100,000 pseudorandom instances, known pair-orbit counts,
regeneration of the profile list). The certificate TSVs are audit logs, not standalone
machine-checkable proof objects: the refutation is the program together with the reductions proved
in the paper, and re-running the program is what re-establishes it.

## AI disclosure

The reduction programme was developed inside an AI-assisted research repository in which Anthropic
Claude agents ran the computations; the exact completion algorithm originates in a consultation with
a large-language-model collaborator acting as a mathematician (one error in that reply was found and
corrected). The final proof document, `peace15_solver.cpp` and `peace15_audit.py` were produced by
OpenAI GPT-5.6 Pro on 2026-07-25. The verification — the second enumerator, the line-by-line solver
audit, the rebuild and rerun on a different toolchain, the sanitizer builds, the re-derivation of
every identity, the witness checks — was carried out by Claude agents.

Agreement between two AI-written implementations is a deliberately engineered error filter, but it
is not independent verification in the scholarly sense. Readers who wish to check the theorem should
re-run the ancillary programs or, better, write a third implementation from Sections 4–6 of the
paper. See the "Use of AI tools" section for the full disclosure. The author reviewed the manuscript
and takes full responsibility for its content.

## Citation

arXiv link will be added once the submission is announced. Until then:

```bibtex
@misc{harries2026peace15,
  author = {Harries, Jan Philipp},
  title  = {Peaceable queens on the $15\times15$ torus: the exact value $t(15)=20$},
  year   = {2026},
  url    = {https://github.com/jphme/math-problems/tree/main/peaceable-queens-t15}
}
```
