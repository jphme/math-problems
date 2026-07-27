Reproducibility files for "New constructions, obstructions, and multiplier
structure for Erdős Problem 634" (July 27, 2026).

Start with paper/verification_manifest.md. It records the exact commands,
environments, qualifications, results, and SHA-256 digests for every
load-bearing artifact. The machine-readable environment record is
paper/replay_environment.toml.

Quick checks from this directory:

  python3 computation/tiling_search/searcher2.py --selftest

  python3 computation/tiling_search/searcher2.py --instance N33 \
    --json /tmp/progress634-N33-primary-replay.jsonl \
    --tag N33_primary_replay

  python3 computation/tiling_search/searcher2.py --instance N33 \
    --no-prune-segment --no-prune-invariant \
    --json /tmp/progress634-N33-reduced-pruning-replay.jsonl \
    --tag N33_reduced_pruning_replay

  (cd computation/tiling_search/independent && \
    uv run --python 3.14.6 python test_long_edge_reflex_regression.py)

The separately written diagnostic searcher is not an independent proof. A
review found an incomplete historical edge-length cap; the included source
contains the correction and regression, but its corrected N=33 search has not
been exhausted. The proof of 33 ∉ S uses searcher2.py only, with the
reduced-pruning replay serving as a same-implementation audit.
