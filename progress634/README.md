# Progress toward Erdős Problem 634

Publication package for:

> Jan Philipp Harries, *New constructions, obstructions, and multiplier
> structure for Erdős Problem 634* (2026).

The full problem asks which positive integers \(N\) occur as the number of
congruent triangles in a tiling of some triangle. It remains open.

## Main results

- Exact-coordinate certificates prove \(88,189\in\mathcal S\).
- The \(189\)-tiling, together with known constructions, settles the Group-1
  ray \(21n^2\): precisely the multipliers \(n\ge2\) occur.
- An exact exhaustive search proves \(33\notin\mathcal S\).
- A Laurent-polynomial boundary quotient gives the exact arithmetic
  obstruction on all six \(120^\circ\)-tile target families.
- Every multiplier set on those six rays is a numerical semigroup with an
  explicit finite generator window.

The \(N=33\) result is deliberately scoped as a **one-implementation
computer-assisted theorem**. The primary run exhausts 6,479 states; a replay
of the same implementation with its general segment-semigroup table and
boundary-invariant pruning disabled exhausts 22,850 states. A separately
written diagnostic searcher had an incomplete historical placement rule. Its
corrected regression is included for transparency, but it supplies no
independent verdict and is not part of the proof.

The paper's provisional programme below \(200\) is clearly separated into an
appendix and is not a theorem.

## Contents

| path | description |
|---|---|
| [`progress634.pdf`](progress634.pdf) | paper |
| [`progress634.tex`](progress634.tex) | LaTeX source |
| [`progress634-arxiv.tar.gz`](progress634-arxiv.tar.gz) | clean arXiv source bundle |
| [`verification_manifest.md`](verification_manifest.md) | commands, environments, results, qualifications, and hashes |
| [`figures/`](figures/) | exact-certificate renderings used in the paper |
| [`anc/`](anc/) | search sources, exact certificates, stored records, and arithmetic audits |

## Build and quick checks

```bash
tectonic progress634.tex
```

From `anc/`:

```bash
python3 computation/tiling_search/searcher2.py --selftest
python3 computation/tiling_search/searcher2.py \
  --instance N33 \
  --json /tmp/progress634-N33-primary-replay.jsonl \
  --tag N33_primary_replay
python3 computation/tiling_search/searcher2.py \
  --instance N33 \
  --no-prune-segment --no-prune-invariant \
  --json /tmp/progress634-N33-reduced-pruning-replay.jsonl \
  --tag N33_reduced_pruning_replay
```

See [`anc/README.txt`](anc/README.txt) and
[`verification_manifest.md`](verification_manifest.md) before interpreting a
run. The exact positive certificates have a separate coordinate checker;
agreement between configurations of one searcher is not external scholarly
replication.

## AI disclosure

OpenAI and Anthropic systems contributed substantially to mathematical
exploration, exact-search code, checking, adversarial review, and drafting.
The paper identifies their role and the limits of model agreement. The author
reviewed the circulated version and is responsible for it.

## Citation

```bibtex
@misc{harries2026progress634,
  author = {Harries, Jan Philipp},
  title  = {New constructions, obstructions, and multiplier structure
            for Erd\H{o}s Problem 634},
  year   = {2026},
  url    = {https://github.com/jphme/math-problems/tree/main/progress634}
}
```
