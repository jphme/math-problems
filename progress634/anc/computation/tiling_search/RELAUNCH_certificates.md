# Relaunching the deferred refutation-certificate campaigns

**Run this in its own terminal / dedicated session — not from inside a working agent session.**
Each job is a single-core exact search that runs for minutes to hours and writes a large
uncompressed scratch file; agent sessions get killed or time out long before the batch finishes.

Why this file exists: the first certificate campaign (2026-07-27) covered only the two small
instances `N33` and `N21`. The 31 remaining exhaustion results in the paper still rest on a single
implementation with no independently checkable proof object — the referee's objection. This file is
the recipe for closing that gap for the rest of them.

Format and semantics are fixed by [`CERT_SPEC.md`](CERT_SPEC.md) (normative). The exporter is
`searcher2.py --export-cert`; the independent checker is `check_refutation.py`.

## Before you launch: three blocking prerequisites

1. **The instance name must be known to both sides.** A certificate header carries
   `"instance": "<NAME>"`, and checker obligation 1 makes the checker *reconstruct* that instance's
   target from published side lengths and compare exactly. So for every new instance:
   - add it to `CERT_INSTANCES` in `searcher2.py` (name -> builder call), and
   - add it to `CERT_SPEC.md` §1, and
   - add it to `check_refutation.py`'s own registry.

   Names used below (proposed; agree them with the checker author before running the batch):

   | name | searcher2 arguments | target |
   |---|---|---|
   | `N56_rowE` | `--instance N56` | equilateral side 56, tile (7,8,13), D=3 |
   | `N70_g1s5_p2q3` | `--group1 --shape 5 --pq 2 3 --N 70` | (70,45,45), tile (6,5,9), D=32 |
   | `N56_g1s4_p13q15` | `--group1 --shape 4 --pq 13 15 --N 56` | (840,840,728), tile (195,56,225), D=731 |
   | `N56_g1s4_p5q9` | `--group1 --shape 4 --pq 5 9 --N 56` | (504,504,280), tile (45,56,81), D=299 |
   | `trapz357_L15_x<NN>` | `--trapezoid --tile 3 5 7 --L 15 --x <NN>` | ideal trapezoid, tile (3,5,7), D=3 |

   `<NN>` is the two-digit `x` of the 27 exhausted trapezoids:
   03 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 30 33.

2. **`CERT_SPEC.md` §3.1 must be extended to non-triangles.** "Longest side from (0,0) to (base,0),
   apex strictly above" is written for triangles. The 27 trapezoid targets are quadrilaterals. All
   31 targets have been pre-checked: `N56_rowE`, `N70_g1s5_p2q3` and all 27 trapezoids are already in
   standard position as built, and the two Group-1 shape-4 N56 targets are rebuilt by an exact rigid
   motion (their longest side is a leg, not the base edge) to

   ```
   N56_g1s4_p13q15 -> (0,0) (840,0) (4732/15, (364/15)*sqrt731)
   N56_g1s4_p5q9   -> (0,0) (504,0) (700/9,  (140/9)*sqrt299)
   ```

   The checker must reconstruct exactly these vertex lists.

3. **Disk.** The exporter buffers node lines in `<PATH>.nodes.tmp` — *uncompressed* JSONL, about
   **1.8 kB per node** — and deletes it after writing the gzip. Certificates themselves compress to
   about **52 bytes per node**. Budget for the largest jobs: see the table below. Keep ~60 GB free.

## Launch

Three jobs at a time, one memory cap per job, `nohup` so the batch survives the terminal:

```bash
cd ~/dev2/proof/erdos634_universal/computation/tiling_search
mkdir -p results/certificates logs

export_one () {          # $1 = instance name, $2.. = searcher2 target arguments
  local name="$1"; shift
  nohup uv run python searcher2.py "$@" \
      --no-prune-segment --no-prune-invariant \
      --export-cert "results/certificates/${name}_refutation.jsonl.gz" \
      --cert-instance "$name" \
      --max-rss-mb 8000 --max-seconds 86400 \
      --json results/certificates/certruns.jsonl --tag "${name}_cert_export" \
      > "logs/cert_export_${name}.log" 2>&1 &
}
```

Wave 1 — the four non-trapezoid instances (the two big ones first, so they overlap the small ones):

```bash
export_one N56_rowE        --instance N56
export_one N56_g1s4_p5q9   --group1 --shape 4 --pq 5 9 --N 56
export_one N56_g1s4_p13q15 --group1 --shape 4 --pq 13 15 --N 56
wait
export_one N70_g1s5_p2q3   --group1 --shape 5 --pq 2 3 --N 70
wait
```

Wave 2 — the 27 trapezoids, three at a time, smallest first:

```bash
for x in 03 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 30 33; do
  while [ "$(jobs -rp | wc -l)" -ge 3 ]; do sleep 30; done
  export_one "trapz357_L15_x${x}" --trapezoid --tile 3 5 7 --L 15 --x "$((10#$x))"
done
wait
```

Optional on a laptop: prefix the whole script with `caffeinate -i`.

## Monitor

```bash
tail -f logs/cert_export_N56_rowE.log        # [export] visited=… kept=… rolled=… n/s rss=…
grep -c '"mode": "export-cert"' results/certificates/certruns.jsonl
ls -l results/certificates/*.jsonl.gz
du -sh results/certificates                  # watch the .nodes.tmp scratch files
```

Every finished job prints `EXHAUSTED: NO TILING EXISTS`, the node count, the byte size, the
SHA-256, and then a `[internal-ok]` line from the exporter's own structural pass. **Three things
must hold for a job to count:** verdict `EXHAUSTED`, `warns=0`, and `rolled_back` consistent with
`cert_nodes = visited - rolled_back`. A nonzero `warns` is a completeness hole — re-run that job
with `--warn-detail` and stop the campaign until it is understood.

## Expected sizes

Node counts scale from the measured runs. The certificate tree is the memoization-free unfolding of
the **reduced-pruning** search, so start from the reduced-config node count, not the
full-pruning one: measured reduced/full ratios are 3.4x (`x03`), 5.0x (`x06`), 6.5x (`x09`),
7.2x (`x12`), 6.3x (`x28`) — take **~6x** for anything large. Tree mode then adds the
budget-pruned children the search rejects inline plus the states memoization used to share:
+1.3 % on `N33`, +32 % on `N21`; assume **+35 %**. Throughput of the exporter is essentially the
throughput of the reduced search, ~850 nodes/s on `N33`-sized regions and ~200-400 nodes/s on the
larger trapezoids.

| job | full-prune nodes | est. certificate nodes | est. .jsonl.gz | est. scratch | est. wall |
|---|---|---|---|---|---|
| `N33` (done) | 6,479 | 23,157 | 1.2 MB | 42 MB | 27 s |
| `N21` (done) | 415 | 887 | 50 kB | 1.3 MB | 0.7 s |
| `trapz357_L15_x03` | 2,605 | ~12,000 | ~0.6 MB | ~22 MB | ~1 min |
| `trapz357_L15_x12` | 24,952 | ~240,000 | ~13 MB | ~430 MB | ~20 min |
| `N56_g1s4_p13q15` | 61,739 | ~500,000 | ~26 MB | ~0.9 GB | ~30 min |
| `N70_g1s5_p2q3` | 253,206 | ~2,000,000 | ~105 MB | ~3.6 GB | ~2 h |
| `trapz357_L15_x28` | 336,267 | ~2,900,000 | ~150 MB | ~5.2 GB | ~4 h |
| `trapz357_L15_x33` | 560,097 | ~4,500,000 | ~235 MB | ~8 GB | ~6 h |
| `N56_g1s4_p5q9` | 1,016,672 | ~8,000,000 | ~420 MB | ~14 GB | ~8 h |
| `N56_rowE` | 1,236,044 | ~10,000,000 | ~520 MB | ~18 GB | ~10 h |

Whole campaign: order 40 M certificate nodes, ~2 GB of certificates, roughly 40 core-hours
(~15 h wall at parallelism 3). The two `N56`s and `x33` dominate; if a job overruns, run it alone
with `--max-seconds 172800`.

**There is no checkpointing.** An interrupted export writes nothing and restarts from zero — the
same limitation as `RELAUNCH.md`'s searches. A job that hits `--max-nodes`, `--max-seconds` or
`--max-rss-mb` prints `UNDECIDED (limit reached: …) -- no certificate written`, deletes its scratch
file, and leaves no partial certificate behind.

## Follow-up: the independent check (this is the point of the exercise)

A certificate nobody checked proves nothing. For every finished job:

```bash
uv run python check_refutation.py results/certificates/<name>_refutation.jsonl.gz
```

It must print `ACCEPT` with the instance name, node count and SHA-256. Per `CERT_SPEC.md` §5.10
there is no inconclusive state: any warning is a `REJECT` and must be chased down before the result
can be cited.

Budget for it: obligation 7 makes the checker decide containment for all 12 candidates of every
branched node by exact polygon intersection, which is the expensive part. Measured on the
equivalent cross-check of `N21`: ~130 branched nodes/s, i.e. **the check is roughly 6x slower than
the export**. Plan on ~250 core-hours for the whole campaign, and run the checks three at a time as
well:

```bash
for f in results/certificates/*_refutation.jsonl.gz; do
  while [ "$(jobs -rp | wc -l)" -ge 3 ]; do sleep 30; done
  nohup uv run python check_refutation.py "$f" > "logs/check_$(basename "$f" .jsonl.gz).log" 2>&1 &
done
wait
grep -L ACCEPT logs/check_*.log        # must be empty
```

Then record, per `CERT_SPEC.md` §8, in `paper/verification_manifest.md`: the exact command,
`uv run python --version`, node count, wall time, and the SHA-256 of both the certificate and
`check_refutation.py`. Certificates are bulk machine output and stay untracked; only their hashes
are published. The gzip container is written with `mtime=0` and no stored filename, so a re-export
of the same instance reproduces the same SHA-256 byte for byte — a hash mismatch means the
certificate content changed, not that the file was merely rebuilt.
