# Separately written diagnostic searcher

`erdos634_exact_search.py` was written independently of
`../searcher.py` and `../searcher2.py`. It uses a different affine coordinate
system, corner rule, placement enumeration, subtraction algorithm, and
state-level memoization. It is useful as a diagnostic implementation, but it
does not currently supply an independent exhaustion for \(N=33\).

## Completeness correction

The source used for the historical 47,750-state `N=33` run rejected a flush
tile edge whenever its length exceeded that of the first boundary segment on
the selected ray:

```python
if s > rayL:
    continue
```

That restriction is invalid when the next boundary vertex is reflex. A legal
tile edge may pass that vertex and continue inside the residual component.
The current source removes the cap and lets the exact containment predicate
decide.

`long_edge_reflex_witness.json` records an exact state reached after two legal
placements. At its selected corner, the first boundary segment has length 5,
while a contained flush tile edge has length 7.
`test_long_edge_reflex_regression.py` reconstructs the state from the two
placements and checks that the corrected generator enumerates the length-7
placement.

Run the regression with:

```sh
uv run --python 3.14.6 python test_long_edge_reflex_regression.py
```

It must end with `LONG_EDGE_REFLEX_REGRESSION_OK`.

## Status of the historical runs

The records under `logs/` were produced by the pre-correction source. Their
restricted search trees contain no tiling, but those records are not
exhaustive proofs and are retained only to document the defect. In
particular, `logs/n33.json` must not be cited as a second proof of
\(33\notin\mathcal S\).

A reviewer run of the minimally corrected program reached 100,000 states and
1,749,582 tested placements without completing. No verdict is claimed for
that partial run. The paper's \(N=33\) theorem instead uses the primary exact
searcher and a 22,850-state replay with its segment-semigroup and boundary
invariant pruning disabled.

## Diagnostic replay

The corrected program can be run with:

```sh
uv run --python 3.14.6 python erdos634_exact_search.py \
  --tile 5 3 7 --target 21 21 33 -N 33 \
  --out /tmp/progress634-N33-independent-diagnostic.json
```

Do not attach a proof status to this command unless it completes without a
resource limit and the resulting search is audited again.
