# math-problems

Solutions to open mathematical problems, produced by [Jan Philipp Harries](https://www.jph.me)
with substantial help from AI systems. Each directory holds one finished result: the paper,
its LaTeX source, and the ancillary programs needed to check it independently.

Every paper discloses exactly which AI systems did what — see the "Use of AI tools" section of
each manuscript. The AI involvement is not incidental, and agreement between two AI-written
implementations is not independent verification in the scholarly sense; the papers say so
themselves and tell you what to re-run if you want to check the claims yourself. That is the
point of shipping the ancillary code.

## Results

| directory | result | status |
|---|---|---|
| [`no19tiling/`](no19tiling/) | **No triangle can be cut into nineteen congruent triangles** — and more generally none can be cut into $p$ congruent triangles for any prime $p>3$ with $p\equiv 3\pmod 4$. The prime case of [Erdős Problem 634](https://www.erdosproblems.com/634). | paper + exact-arithmetic verification script |
| [`peaceable-queens-even-torus/`](peaceable-queens-even-torus/) | **$t(2q)=H(2q)$ for every $q$** — an exact formula for the peaceable queens number of every even toroidal board; even-torus density exactly $(2-\sqrt3)/2$. Plus the odd values $t(15)=20$, $t(17)=28$. Extends and closes the even side of [OEIS A279405](https://oeis.org/A279405). | paper + two exact rational branch certificates, 760-cut certified library, ladder records, two independently written verifiers |
| [`peaceable-queens-t15/`](peaceable-queens-t15/) | **$t(15)=20$ and $t(16)=32$** — the first two previously unknown terms of [OEIS A279405](https://oeis.org/A279405); companion note with the detailed exhaustive-sweep treatment. | paper + two independent exact enumerators per order, audit scripts, certificates |

## Checking the results

Each directory has an `anc/README.txt` with the exact build and run commands, what each program
checks, and — importantly — what it does *not* establish. Nothing needs third-party libraries
beyond SymPy for the tiling script and one symbolic queens verifier; the queens programs are plain C++ and Python.

## Related

Working notes, failed routes, and problems still in progress live in a separate repository and
are not part of this one. What appears here is finished work.
