# Verification manifest

This manifest records the exact computations used for the positive tiling
certificates, the \(N=33\) exhaustion, the refutation certificates and their
independent checker, and the arithmetic audit suite in the
manuscript.  It was prepared on 2026-07-27 (CEST) from repository state based
on commit `0c44c70d9ba2b31c96e6fcadbc369cb6150c0faf` and extended on
2026-07-28 for the major revision (refutation certificates, independent
checker, explicit branch-reduction proposition, imported-statement pins);
the SHA-256 inventory below,
rather than the commit alone, identifies every load-bearing artifact.

Commands and paths beginning with `erdos634_universal/` or
`triangle19_refutation/` are relative to the project repository root.  In the
arXiv package, the reproducibility files are under `anc/`, with the directory
tree below that point preserving the shorter paths used here.  For readability
in the audit inventories,
`computation/...` is relative to `erdos634_universal/`, while a bare
`results/...` certificate path is relative to
`erdos634_universal/computation/tiling_search/`.  SHA-256 values were computed
with `shasum -a 256`.

After extracting the arXiv package, the corresponding replay root is the
ancillary directory:

```sh
cd anc
python3 computation/tiling_search/searcher2.py --selftest
python3 computation/tiling_search/searcher2.py --group1 --shape 5 --pq 1 2 --N 21 --json /tmp/progress634-N21-replay.jsonl --tag N21_shape5_replay
python3 computation/tiling_search/searcher2.py --instance N33 --json /tmp/progress634-N33-primary-replay.jsonl --tag N33_primary_replay
python3 computation/tiling_search/searcher2.py --instance N33 --no-prune-segment --no-prune-invariant --json /tmp/progress634-N33-reduced-pruning-replay.jsonl --tag N33_reduced_pruning_replay
(cd computation/tiling_search/independent && uv run --python 3.14.6 python test_long_edge_reflex_regression.py)
```

For the other repository-root commands below, remove the literal
`erdos634_universal/` prefix after changing to `anc`.  Replay commands use new
files under `/tmp`; they do not append to or overwrite the hash-inventoried
records.

The circulation artifacts built after the report-7 audit, the 2026-07-27
referee pass, and the 2026-07-28 major revision (version 0.4: refutation
certificates with independent checker, explicit $N=33$ branch-reduction
proposition and disposition tables, imported statements pinned and collected
in a dependency ledger, rotation-system subtraction proof, fit-test and
pruning necessity lemmas, run-status and memoization semantics, trapezoid
theorem split, explicit Laurent isomorphism with universal-property
corollary, $60^\circ$ unit lemma, Eisenstein-square lemma, and
$\gamma=2\alpha$ angle-representation lemma) are:

| artifact | SHA-256 |
|---|---|
| `erdos634_universal/paper/progress634.tex` | `63ddd07adfa22f4a10660d302e31c62528bb49a9facfc0b674965e6f6559692c` |
| `erdos634_universal/paper/progress634.pdf` | `0136a3b70cb430959ddd2ee1320a2a02864a60fddf8f3f0af70fa7ada9d7dea7` |

The current artifacts additionally expand Appendix B.2/B.3 with the
per-branch direction lattices, the explicit ideal memberships
$B(\partial T)\in(F,G)=Q\cdot J$ over $\mathbb Z[z,z^{-1}]$, and the
integer-scale derivations ($t\in J\cap\mathbb Z=(b)$, and $C\in\mathbb Z$ by
boundary integrality plus B\'ezout), in response to a referee query on the
$\gamma=2\alpha$ ray (theorem numbering unchanged).  The 2026-07-28 v0.4
artifacts (tex
`ba3b615677be07e561f471a1eab034d9972171526a2a700f5cf99a6abcec8128`, pdf
`2df8f4a85a8d1905b44213c2d9425adb86cb97a5799e08a174aae601310ba08d`) and the
2026-07-27 referee-pass artifacts (tex
`9b2cb91faafdae090ebed008499f18d7398d2dcda9b4a2ed34bc8aff9835bde5`, pdf
`737a46e12aaab3c218a8f7ec6fe2159be781850d04794ca43704f5a5dbd62a71`) are
superseded by the above.

## Environment for the 2026-07-27 reruns

- OS: macOS 26.5.2 (build 25F84), arm64; Darwin kernel 25.5.0.
- Python: CPython 3.9.6,
  `/Library/Developer/CommandLineTools/usr/bin/python3`, built with
  Clang 21.0.0.
- The primary and diagnostic searchers, the certificate verifier, and the
  seven non-Laurent audit scripts use only the Python standard library.  The
  Laurent/character audit was run separately under CPython 3.14.6 with
  SymPy 1.14.0 and mpmath 1.3.0.
- The machine-readable environment record is
  `paper/replay_environment.toml`.
- Primary search self-test:

  ```sh
  python3 erdos634_universal/computation/tiling_search/searcher2.py --selftest
  ```

  Result: `ALL SELF-TESTS PASSED`.  Its six positive controls were found and
  internally verified; every control reported `warns=0`.

## Positive-certificate verification

`verify_tiling.py` is a separate exact verifier, not a second search.  It reads
the tile coordinates in a found certificate and independently checks:

1. the exact squared side-length multiset of every tile;
2. containment in the reconstructed convex hull;
3. zero intersection area for every pair of tile interiors, by exact rational
   clipping; and
4. exact equality of the summed tile area and hull area.

For the two triangular targets below, the verifier additionally required the
reconstructed hull to have three corners and its exact squared side-length
multiset to equal the squares of `--expect-sides`.  For each trapezoid it used
`--expect-ideal-trapezoid X L`, which requires four corners, the cyclic squared
side lengths \((X+L)^2,L^2,X^2,L^2\) up to reversal and rotation, parallel
unequal bases, and both diagonal squares \(X^2+XL+L^2\).  This distinguishes
the intended ideal trapezoid from other quadrilaterals with the same side
multiset.  The legacy one-argument command remains valid and was also
smoke-tested on `N88_tiling.json`.

Exact commands:

```sh
python3 erdos634_universal/computation/tiling_search/verify_tiling.py erdos634_universal/computation/tiling_search/results/N88_tiling.json --expect-corners 3 --expect-sides 21 55 56
python3 erdos634_universal/computation/tiling_search/verify_tiling.py erdos634_universal/computation/tiling_search/results/N189_tiling.json --expect-corners 3 --expect-sides 36 36 63
python3 erdos634_universal/computation/tiling_search/verify_tiling.py erdos634_universal/computation/tiling_search/results/x29_N73_trapezoid_tiling.json --expect-ideal-trapezoid 29 15
python3 erdos634_universal/computation/tiling_search/verify_tiling.py erdos634_universal/computation/tiling_search/results/x31_N77_trapezoid_tiling.json --expect-ideal-trapezoid 31 15
python3 erdos634_universal/computation/tiling_search/verify_tiling.py erdos634_universal/computation/tiling_search/results/x32_N79_trapezoid_tiling.json --expect-ideal-trapezoid 32 15
python3 erdos634_universal/computation/tiling_search/verify_tiling.py erdos634_universal/computation/tiling_search/results/x35_N85_trapezoid_tiling.json --expect-ideal-trapezoid 35 15
python3 erdos634_universal/computation/tiling_search/verify_tiling.py erdos634_universal/computation/tiling_search/results/x36_N87_trapezoid_tiling.json --expect-ideal-trapezoid 36 15
python3 erdos634_universal/computation/tiling_search/verify_tiling.py erdos634_universal/computation/tiling_search/results/x38_N91_trapezoid_tiling.json --expect-ideal-trapezoid 38 15
python3 erdos634_universal/computation/tiling_search/verify_tiling.py erdos634_universal/computation/tiling_search/results/x41_N97_trapezoid_tiling.json --expect-ideal-trapezoid 41 15
```

Every command exited with status 0.  The detailed results were:

| certificate | asserted target sides | tiles | pairs clipped | result |
|---|---:|---:|---:|---|
| `N88_tiling.json` | \(21,55,56\) | 88 | 3,828 | verified |
| `N189_tiling.json` | \(36,36,63\) | 189 | 17,766 | verified |
| `x29_N73_trapezoid_tiling.json` | \(15,15,29,44\) | 73 | 2,628 | verified |
| `x31_N77_trapezoid_tiling.json` | \(15,15,31,46\) | 77 | 2,926 | verified |
| `x32_N79_trapezoid_tiling.json` | \(15,15,32,47\) | 79 | 3,081 | verified |
| `x35_N85_trapezoid_tiling.json` | \(15,15,35,50\) | 85 | 3,570 | verified |
| `x36_N87_trapezoid_tiling.json` | \(15,15,36,51\) | 87 | 3,741 | verified |
| `x38_N91_trapezoid_tiling.json` | \(15,15,38,53\) | 91 | 4,095 | verified |
| `x41_N97_trapezoid_tiling.json` | \(15,15,41,56\) | 97 | 4,656 | verified |

The verifier has no warning-suppression path: any failed assertion terminates
with nonzero status.  Thus the positive-certificate reruns had zero warnings and
zero failed checks.  As a negative control, rerunning the \(N=88\) certificate
with `--expect-sides 21 55 57` exited with status 1 and reported the exact
mismatch between squared side multisets
\(\{441,3025,3136\}\) and \(\{441,3025,3249\}\).  A second negative control
checked the \(x=29\) certificate with `--expect-ideal-trapezoid 30 15`; it
exited with status 1 and reported the unequal cyclic squared-side sequences.

The full trapezoid campaign record
`results/trapezoid_357.jsonl` contains 34 jobs: 27 exact exhaustions and seven
found certificates, totaling 5,699,235 search nodes.  Every job records
`warns=0`.  The human-readable `.summary` was reconciled with the JSONL record
on 2026-07-27: its seven successful jobs are now labeled `FOUND`.

## Group-1 shape-5 \(N=21\) exhaustion

The computer-assisted input to Corollary 2 was freshly rerun.  The safe replay
command is:

```sh
python3 erdos634_universal/computation/tiling_search/searcher2.py --group1 --shape 5 --pq 1 2 --N 21 --json /tmp/progress634-N21-replay.jsonl --tag N21_shape5_replay
```

The archived record in
`computation/tiling_search/results/verification_N21_20260727.jsonl` embeds the
original argument vector.  It reports `EXHAUSTED`, 415 nodes, maximum depth 14, 60
segment-semigroup cuts, and `warns=0`.  A larger unpruned `--paranoid`
cross-check is stored in `results/followup.jsonl` under tag `xchk_g1_N21`; it
also reports `EXHAUSTED`, with 674 nodes and zero warnings.  These are two
search trees from the same implementation, not two independent programs.

## Exact \(N=33\) exhaustion and reduced-pruning replay

Safe replay command:

```sh
python3 erdos634_universal/computation/tiling_search/searcher2.py --instance N33 --json /tmp/progress634-N33-primary-replay.jsonl --tag N33_primary_replay
```

The archived record embeds the original argument vector and was written to a
then-new path.  Because `--json` has append semantics, replay against a new
path as above.  Wall time and peak RSS are machine-dependent fields.

The stable one-line JSON record is
`computation/tiling_search/results/verification_20260727.jsonl`.  It reports:

- verdict `EXHAUSTED`;
- 6,479 nodes and maximum depth 22;
- 6,479 failed states and zero solved states;
- 1,575 wedge cuts and 1,394 segment-semigroup cuts;
- `warns=0`, invariant misses 0, peak RSS 37 MB; and
- wall time 16.90 seconds.

This is the project's primary search implementation.  The same implementation
was also rerun with its segment-semigroup and
boundary-invariant pruning disabled:

```sh
python3 erdos634_universal/computation/tiling_search/searcher2.py --instance N33 --no-prune-segment --no-prune-invariant --json /tmp/progress634-N33-reduced-pruning-replay.jsonl --tag N33_reduced_pruning_replay
```

The archived record
`computation/tiling_search/results/verification_N33_no_seg_inv_20260727.jsonl`
reports `EXHAUSTED`, 22,850 nodes, maximum depth 22, 22,850 failed states,
5,561 wedge cuts, 773 corner cuts, zero segment or invariant cuts, and
`warns=0`.  This is a broader replay tree from the same implementation, not
an independent program.

### Corrected diagnostic searcher

A separately written diagnostic searcher formerly reported an exhaustion of
this instance.  Review found that its placement generator rejected any flush
tile edge longer than the first boundary segment on its ray.  This is invalid
when the next boundary vertex is reflex.  The exact regression witness reaches
a legal state after two placements with first-segment length 5 and a contained
tile-edge length 7; the historical generator omits the placement.

The cap has been removed from
`computation/tiling_search/independent/erdos634_exact_search.py`.
The regression is:

```sh
cd erdos634_universal/computation/tiling_search/independent
uv run --python 3.14.6 python test_long_edge_reflex_regression.py
```

It reports `LONG_EDGE_REFLEX_REGRESSION_OK` and enumerates 22 placements at
the witness corner.  The corrected diagnostic search has not been exhausted,
so it supplies no independent verdict and is not used in the proof.  The
historical output is omitted from the public ancillary package; the internal
review archive preserves it with its matching historical source for
provenance.

## Other exhaustive inputs to the detailed ledger

The detailed ledger also reports the following archived primary-search
exhaustions.  Each JSON record embeds its full argument vector:

| value and branch | record/tag | nodes | warnings |
|---|---|---:|---:|
| \(N=56\), Group-2 row E, tile \((7,8,13)\) | `group2_frontier.jsonl`, `N56_rowE` | 1,236,044 | 0 |
| \(N=56\), Group-1 shape 4, \((p,q)=(13,15)\) | `group1.jsonl`, `g1_s4_p13q15_N56` | 61,739 | 0 |
| \(N=56\), Group-1 shape 4, \((p,q)=(5,9)\) | `group1.jsonl`, `g1_s4_p5q9_N56` | 1,016,672 | 0 |
| \(N=70\), Group-1 shape 5, \((p,q)=(2,3)\) | `group1.jsonl`, `g1_s5_p2q3_N70` | 253,206 | 0 |

All four report `EXHAUSTED`.  They have not been reproduced with a separately
implemented searcher, which is why the paper keeps them in the more qualified
“further audited exclusions” row.

## Refutation certificates and the independent checker (2026-07-28)

The negative results for \(N=33\) and for the 21-ray at \(n=1\) are now
carried by exported refutation certificates validated by an independently
written checker; the format is fixed normatively in
`computation/tiling_search/CERT_SPEC.md`, and the paper's
Appendix on refutation certificates states the soundness theorem.  The
export runs use the reduced pruning configuration with memoization and
canonicalization disabled (tree mode).  All commands below were run from
`erdos634_universal/computation/tiling_search/` under CPython 3.14.6
(`uv run python`), standard library only.

Reduced-configuration baselines (memoized, no export):

```sh
uv run python searcher2.py --instance N33 --no-prune-segment --no-prune-invariant --json results/certificates/certruns.jsonl --tag N33_reduced_memo_baseline
uv run python searcher2.py --group1 --shape 5 --pq 1 2 --N 21 --no-prune-segment --no-prune-invariant --json results/certificates/certruns.jsonl --tag N21_reduced_memo_baseline
```

Both report `EXHAUSTED` with zero warnings: 22,850 and 674 nodes.

Certificate exports:

```sh
uv run python searcher2.py --instance N33 --no-prune-segment --no-prune-invariant --export-cert results/certificates/N33_refutation.jsonl.gz --cert-instance N33 --max-rss-mb 12000 --json results/certificates/certruns.jsonl --tag N33_cert_export
uv run python searcher2.py --group1 --shape 5 --pq 1 2 --N 21 --no-prune-segment --no-prune-invariant --export-cert results/certificates/N21_refutation.jsonl.gz --cert-instance N21 --max-rss-mb 12000 --json results/certificates/certruns.jsonl --tag N21_cert_export
```

Both report `EXHAUSTED` with zero warnings and zero rollbacks:

- `N33_refutation.jsonl.gz`: 23,157 nodes (16,516 branched; prunes
  307 budget, 5,561 wedge, 773 short-edge), 1,217,374 bytes, export wall
  time 27.3 s.  The tree node count equals the memoized baseline plus the
  307 budget-pruned children materialized per the specification (zero
  memoization sharing occurred in this search).
- `N21_refutation.jsonl.gz`: 887 nodes (625 branched; prunes 111 budget,
  104 wedge, 47 short-edge), 50,323 bytes, export wall time 0.7 s.  The
  tree node count equals 674 baseline nodes plus 111 budget children plus
  102 states the memo cache had shared.

The gzip containers are written with `mtime=0` and no stored filename, so
the digests are byte-reproducible.

Independent checker runs:

```sh
uv run python check_refutation.py results/certificates/N21_refutation.jsonl.gz
uv run python check_refutation.py results/certificates/N33_refutation.jsonl.gz
```

Verdicts: `ACCEPT N21 nodes=887` in 1.11 s and `ACCEPT N33 nodes=23157` in
58.5 s (wall times machine-dependent).  On \(N=33\) the checker made
198,192 candidate containment decisions by exact intersection area and
verified 418 multi-child coverage decompositions, including the
boundary-support (union-coverage) obligation; on \(N=21\), 6,614 rejected
and 886 expanded candidates.  The checker was written from
`CERT_SPEC.md` alone, shares no code with the searcher or the
positive-certificate verifier, and imports only the Python standard
library; its test suite
(`tests_check_refutation.py`, 1,410 checks) accepts three synthetic valid
certificates and rejects 44 synthetic mutants and 7 mutants of the real
\(N=21\) certificate, including an artificial-chord subdivision caught
only by the boundary-support check.

SHA-256 digests:

| artifact | SHA-256 |
|---|---|
| `results/certificates/N33_refutation.jsonl.gz` | `613c52ddf436aea2abffe0a1d62e7cb40f65f9ab5b792dcdd7bf4c099cc21919` |
| `results/certificates/N21_refutation.jsonl.gz` | `7063333609b6075fc677b8cee4a130c2db301e4339809344bbb83607829eaf76` |
| `computation/tiling_search/check_refutation.py` | `52d74ab383892ce53c10d14d9daa541263589abd8d4b0f7eabf10851ea7fd99c` |
| `computation/tiling_search/tests_check_refutation.py` | `de71dbba20e7b2156fd12d8e014bbc8d33cc1377836c162939a4f6ccd384e81c` |
| `computation/tiling_search/CERT_SPEC.md` | `ffaa8396c0bb0f83ea64567786e1755c067a9d4c29226a1656840b5412883bc7` |
| `computation/tiling_search/RELAUNCH_certificates.md` | `95ee1abfcbe5aa65805166c2fd3e21bb8693cdfb6d52a611b0c53ccfe783f9dd` |

The deferred certificate campaigns for the \(N=56\), \(N=70\), and
trapezoid exhaustions, with commands, size estimates, and prerequisites,
are recorded in `computation/tiling_search/RELAUNCH_certificates.md`.

## Arithmetic and invariant audit suite

The complete suite was rerun on 2026-07-27 with these commands:

```sh
uv run --python 3.14.6 --with sympy==1.14.0 --with mpmath==1.3.0 python erdos634_universal/computation/verify_phi_invariants.py
python3 erdos634_universal/computation/verify_parallel_track_claims.py
python3 erdos634_universal/computation/verify_theory_report3_claims.py
python3 erdos634_universal/computation/verify_theory_report4_claims.py
python3 erdos634_universal/computation/verify_theory_report5_claims.py
python3 erdos634_universal/computation/verify_theory_report5_2_claims.py
python3 erdos634_universal/computation/verify_theory_report6_claims.py
python3 erdos634_universal/computation/verify_theory_report7_claims.py
python3 erdos634_universal/computation/sieve_120rows.py 200
```

The Laurent/character script ran under CPython 3.14.6 with SymPy 1.14.0 and
mpmath 1.3.0.  The other seven scripts use only the standard library and ran
under the CPython 3.9.6 environment identified above.  The results were,
respectively: all strict invariant checks passed; 23/23, 90/90, 37/37, 18/18,
53/53, 27/27, and 29/29 checks passed.  The report-3 total is 90 rather than
the earlier 76 because, in addition to the fixed-\(N\) branch reductions for
\(21,30,33,55,\) and \(66\) added earlier, the script now carries
section~H (2026-07-28, rerun under CPython 3.14.6): the equation-only sweep
of Beeson's five Table-6 tiling equations at \(N=33\) over \(q\le400\),
validated against all 53 printed rows of that paper's Tables~1--5, ending
with the branch-empty verdicts quoted in the paper's disposition table.
The script now exits nonzero on any failure.  The report-6
script checks only the arithmetic consequences of the proposed forced-layer
induction; it does not verify the missing geometric induction and is not used
to promote any forced-layer-dependent statement.  The report-7 script performs bounded
regression checks: Group-2 parametrizations and defect tests use \(r\le35\);
Group-1 identities use \(p,q<60\); the parallelogram identity uses four
selected side pairs with \(p,q<6\); relation comparisons use \(r\le35\)
together with a separate \(a,b<400\) parametrization comparison; and pure-edge
words have length at most 10 with the coefficient bounds stated in the
script.  The universal identities are proved in the manuscript; these finite
tests are regression checks, not their proofs.  The same script verifies only
that the manually transcribed Herdt inventory sums arithmetically to 720, and
supplies an exact mirror-placement counterexample to the proposed forced-layer
inference.  It does not certify that figure's coordinate coverage,
forced-layer induction, seam propagation, macro-normalization, or
semilinearity.

The final `sieve_120rows.py 200` command is a deterministic candidate-ledger
generator rather than a pass/fail audit.  It completed without error; its
program hash is included below so that the provisional below-\(200\) output
can be regenerated exactly.

The captured outputs are:

| audit | output |
|---|---|
| Laurent/character checks | `computation/results/phi_verification_20260727.txt` |
| parallel track | `computation/results/parallel_track_verification.txt` |
| report 3 | `computation/results/theory_report3_verification.txt` |
| report 4 | `computation/results/theory_report4_verification.txt` |
| report 5 | `computation/results/theory_report5_verification_20260727.txt` |
| report 5.2 | `computation/results/theory_report5_2_verification_20260727.txt` |
| report 6 arithmetic | `computation/results/theory_report6_verification_20260727.txt` |
| report 7 algebra and finite enumeration | `computation/results/theory_report7_verification_20260727.txt` |
| searcher self-tests | `computation/results/searcher_selftest_20260727.txt` |

## SHA-256 inventory

### Programs and search records

| file | SHA-256 |
|---|---|
| `computation/tiling_search/verify_tiling.py` | `6561003dad004da2539fe3dd1c068ca2876976594f13f0772295a15af3ca008a` |
| `computation/tiling_search/searcher2.py` (with certificate exporter, 2026-07-28) | `3eceb14e432f918a84f32c5fc3723ce1a03bfb4de477a13e48ec6cc4317dd1a8` |
| `computation/tiling_search/searcher2.py` (pre-exporter edition used for the 2026-07-27 records) | `b33ae49032f15ec851e45ebce03d02eafdec271cabc60552e1d0558aa482bc94` |
| `computation/tiling_search/check_refutation.py` | `52d74ab383892ce53c10d14d9daa541263589abd8d4b0f7eabf10851ea7fd99c` |
| `computation/tiling_search/tests_check_refutation.py` | `de71dbba20e7b2156fd12d8e014bbc8d33cc1377836c162939a4f6ccd384e81c` |
| `computation/tiling_search/CERT_SPEC.md` | `ffaa8396c0bb0f83ea64567786e1755c067a9d4c29226a1656840b5412883bc7` |
| `computation/tiling_search/results/certificates/N33_refutation.jsonl.gz` | `613c52ddf436aea2abffe0a1d62e7cb40f65f9ab5b792dcdd7bf4c099cc21919` |
| `computation/tiling_search/results/certificates/N21_refutation.jsonl.gz` | `7063333609b6075fc677b8cee4a130c2db301e4339809344bbb83607829eaf76` |
| `computation/tiling_search/independent/erdos634_exact_search.py` | `298f0a49d1fa1b09584d085365e9726ea4addca6e9b569633a5515f712d49d3f` |
| `computation/tiling_search/independent/README.md` | `e1b9cc3c23852f2a18453aef06d8dc981cb25d6ae4e7aa9b6c2d58741d34b421` |
| `computation/tiling_search/independent/long_edge_reflex_witness.json` | `3da7e405917ede37958f3f7d588ce451f2858676dbd03a0cb9931096d4817dcb` |
| `computation/tiling_search/independent/test_long_edge_reflex_regression.py` | `6f9af1e79a7bb55d1a2e3d0856a3a7a2345924ac90ae7cb6e29b48a80077a204` |
| `computation/tiling_search/results/verification_N21_20260727.jsonl` | `2dcbb37a25f3a98691af3abeba77369fa2c74795a47bcad69f6a34b43566b7fb` |
| `computation/tiling_search/results/followup.jsonl` | `303ab9abe831f732ef31b1b993b552994b4f817ec44e8c7bef49dcf63a19f3c4` |
| `computation/tiling_search/results/verification_20260727.jsonl` | `a03046c4c7ce7287577e553686dd4aa3d76c944bbe0bb824e623ab3799eb5ea0` |
| `computation/tiling_search/results/verification_N33_no_seg_inv_20260727.jsonl` | `b014c99894f9b758de32a69453f2e1684e414c7172ce7840e1137e1e43e4e19d` |
| `paper/replay_environment.toml` | `834688acfa4c1f5b59156d9ea080490eec27ac5296f7e57bbaade13134f1b157` |
| `computation/tiling_search/results/group1.jsonl` | `7077e2c6443ef20aae8b5c7992a52e29d3c3a08b1a5ff59fda09df952f72de74` |
| `computation/tiling_search/results/group2_frontier.jsonl` | `18c4f3d04e271ef6ea099bd96363565d8be01d8f4918103890dd7c1a93af6a77` |
| `computation/tiling_search/jobs/trapezoid_357.tsv` | `28a6f5a9ef1880da1d2c66568cf3785704080024c19adf03f9ba2d84c618ebb2` |
| `computation/tiling_search/results/trapezoid_357.jsonl` | `1b128d56fbc860ff6c4686ae168900248dbe6333287bcfc886e160e981873459` |
| `computation/tiling_search/logs/trapezoid_357.summary` | `4d3f21807b0843d5c078b0b4ad43fc16c5f7b0628dd5e0a0b63a474477399c3a` |

### Arithmetic audit programs and outputs

| file | SHA-256 |
|---|---|
| `computation/verify_phi_invariants.py` | `816f0a235e1a04598c791a5902a78e6944f766d255911b187018c0ed4be22ade` |
| `computation/verify_parallel_track_claims.py` | `709ccd536766ed42d2269c636d6f89381bcd785371b4884a67d5c28055fbf092` |
| `computation/verify_theory_report3_claims.py` (with section H, 2026-07-28) | `45a062eddccb6efbc588b6c3e6fae5b781e5fb9178898c7ac018085272bec897` |
| `computation/verify_theory_report4_claims.py` | `46a4bf6f5b451d5d6867c26e3a9c577df21daa3cf87c28ccb492ab80b058ebe7` |
| `computation/verify_theory_report5_claims.py` | `3721d52f631559b35bb30d4ead80c4524004a0c9b326167dd747ff222b389f1e` |
| `computation/verify_theory_report5_2_claims.py` | `6a1267416067b6040f49ce16d56658f762045bf70fc808463661d0671fa308a3` |
| `computation/verify_theory_report6_claims.py` | `acb72396e7a573216d5a7ff3f79aef1f223cdadfbce752db5abf9cb45643f8ee` |
| `computation/verify_theory_report7_claims.py` | `b3017ca9ef4eca22cb6d127f95998bae84238f05e7ec335ca101405c7d894e07` |
| `computation/sieve_120rows.py` | `f2ca7700ce9737dc714b4b3dea933e866dccda520eb238dfb6b7022003639847` |
| `computation/results/phi_verification_20260727.txt` | `8ce49f06e1569c3621ba54d0f200c35ea8730ec60a3e447f1d70e6e7ec9416b4` |
| `computation/results/parallel_track_verification.txt` | `3fe2efcecb224f71b911d68ba3b17ef893f726ac160828be2eb317a6c27c4d4f` |
| `computation/results/theory_report3_verification.txt` | `3ee9b97090b9e0ade4f75b7d1e188bc985f7192c48129827a844f95eb837e2e8` |
| `computation/results/theory_report4_verification.txt` | `7b1e89dfd24dc6242eb072397f28baa112b1d984b037af97b480ce560bfb5c01` |
| `computation/results/theory_report5_verification_20260727.txt` | `0938f3600cecfca160ca59d48671bb3a69c625b7f3e496b09b4be25eec482390` |
| `computation/results/theory_report5_2_verification_20260727.txt` | `ce8d7a8ff0fe472ead74f7cf3865f61675df9937db89ddc06208c4c42d94a5d1` |
| `computation/results/theory_report6_verification_20260727.txt` | `87b5823239cb2ce22ca0818fcb254bf5b76af0479bedbe696de253132fbd12af` |
| `computation/results/theory_report7_verification_20260727.txt` | `997a7d41e3de0262d15bdc2ae33e9c8f5646577afe209780184df1481ed038e8` |
| `computation/results/searcher_selftest_20260727.txt` | `9c92b3b58271332cf09472349d1ab489a249cf1ba13e2e297e96bb7d73c01646` |

### Positive certificates

| file | SHA-256 |
|---|---|
| `results/N88_tiling.json` | `163327fc06cf8f98639b38743e8d796c9fdcd86d722485229a8f047e94aefbbd` |
| `results/N189_tiling.json` | `28f33084443ba303e6758511e616c3f9bbf3de1657e3422eee6680118a0d5096` |
| `results/x29_N73_trapezoid_tiling.json` | `8895cd158aeae79d3a0151a003b58a022446d89941ed50cd680b1e03a52e7931` |
| `results/x31_N77_trapezoid_tiling.json` | `184949796da1e3fff07143d7414e772762041ef27e538e5a0fed28a89c0e428e` |
| `results/x32_N79_trapezoid_tiling.json` | `7b4f3373a05cdae099d685ac461e8bd24c5cba3793dbb880c4fe26d8468e6b41` |
| `results/x35_N85_trapezoid_tiling.json` | `0fd8e6c292a94b064fe4b702ee9bc2724d3fe4bf598ba26f9cce1d315ec624d6` |
| `results/x36_N87_trapezoid_tiling.json` | `1f552ee87279e4919227d8bc2493054751e277180ac3df18f510c66dd9f67374` |
| `results/x38_N91_trapezoid_tiling.json` | `ac879b202c60b62160bda2f9e2b3e9b4f9be37d5fe86ae91ab0ca4539812d65b` |
| `results/x41_N97_trapezoid_tiling.json` | `a6094c63002df033193b624bf638ed58e47e92ea95ba55001496c18544769fe7` |

In the last table, every path is under
`erdos634_universal/computation/tiling_search/results/`.

### Source-version audit inventory

These hashes identify the exact manuscripts inspected.  They are not
computational proof artifacts and are not redistributed in the arXiv
ancillary package.  Public items are recoverable through the manuscript's
citations.  Beeson's *No Prime Tiling of an Isosceles Triangle* is public as
arXiv:2607.19572v1.  His separate July 26 manuscript, *Tiling a Triangle into
a Prime Number of Congruent Triangles*, was supplied privately and has no
public identifier as of this manifest date.

| source | SHA-256 |
|---|---|
| `triangle19_refutation/triangle19_refutation.pdf` | `8c4463ae74b5a8e4ea8b75f76dbf8431b274b6ab63e781eea73064d8bc87b46f` |
| `erdos634_universal/sources/PrimeTilings[34].pdf` | `7229facc5cd346617778cd5eed26ea2721e21108bc3f764b15fd06e434c1d8f5` |
| `erdos634_universal/sources/george_gpt56pro_candidate_partial_solution_2026-07-16.pdf` | `34231b402a3ab8c302d3370cdee57cecc638824f278a5bed46eef46bc048388e` |
| `erdos634_universal/sources/adjacent_methods_2026-07-25/pdfs/Beeson_2026_No_Prime_Tiling_Isosceles_arXiv2607.19572v1.pdf` | `62a0afe7716b98cab7df2f0fda33f535dd3c3b8063e255a8a1a8082721b86b9a` |
| `erdos634_universal/sources/adjacent_methods_2026-07-25/pdfs/Beeson_2019_Triangle_Tiling_3alpha_2beta_arXiv1206.2229v3.pdf` | `3511913efd16c4deebd6659f7db8f0b00c18546ca539cd3616de2442eafaebae` |
| `erdos634_universal/sources/beeson_IsoscelesTilings_michaelbeeson.com_edition.pdf` | `95d41234e23aff2d4607a73484187778f7bb81c0b7a69ac6488996bf649daec7` |
| `https://arxiv.org/pdf/1206.1974v7` (61-page arXiv PDF fetched 2026-07-27) | `e0a1059554bf1c9f51e7bbf33ffe7243e58e4994793462765636e30183958b4b` |
| `erdos634_universal/sources/blz_2604.03609v2_solution_erdos633.pdf` (fetched 2026-07-28; Theorem~9 verified verbatim for the dependency ledger) | `8e9657b4557ca1e68159583f04e21c9cbd5637e98c0c3ad8905f81a250f1a145` |
| `erdos634_universal/sources/zhang_2512.22696v4_tiling_triangles_2pi3.pdf` | `fcfeb2b70737ae6ff15fd3ff3eacde794438f2128a7b1d76231769f6ebac2d56` |
