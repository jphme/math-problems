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
| [`peaceable-queens-t15/`](peaceable-queens-t15/) | **$t(15)=20$** — the largest peaceable pair of queen armies on the $15\times15$ toroidal board. First previously unknown term of [OEIS A279405](https://oeis.org/A279405). | paper + two independent exact enumerators, audit script, certificates |

## Checking the results

Each directory has an `anc/README.txt` with the exact build and run commands, what each program
checks, and — importantly — what it does *not* establish. Nothing needs third-party libraries
beyond SymPy for the tiling script; the queens programs are plain C++ and Python.

## Related

Working notes, failed routes, and problems still in progress live in a separate repository and
are not part of this one. What appears here is finished work.
