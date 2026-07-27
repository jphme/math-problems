# math-problems

Solutions to open mathematical problems by
[Jan Philipp Harries](https://www.jph.me), produced with substantial use of
AI systems. Each result directory contains the paper, its LaTeX source, and
the ancillary material needed to check the computer-assisted claims.

## Results

| directory | result | release |
|---|---|---|
| [`no19tiling/`](no19tiling/) | No triangle can be tiled by nineteen congruent triangles; more generally, not by \(p\) congruent triangles for any prime \(p>3\) with \(p\equiv3\pmod4\). | paper and exact-arithmetic verifier |
| [`peaceable-queens-even-torus/`](peaceable-queens-even-torus/) | Exact formula for the peaceable queens number of every even toroidal board; even density \((2-\sqrt3)/2\); also \(t(15)=20\) and \(t(17)=28\). | unified paper, exact certificates, exhaustive-search sources, audits, and frozen outputs |
| [`peaceable-queens-t15/`](peaceable-queens-t15/) | Stable compatibility path for the former \(15\times15\)/\(16\times16\) companion paper. | mirror of the unified peaceable-queens release |

## Checking the results

Each publication directory includes an `anc/README.txt` that distinguishes
standalone proof objects from audited exhaustive-search outputs and gives the
exact commands and recorded environments. The peaceable-queens bundle has a
single portable audit entry point and ships the source needed to rerun the
long searches.

Every paper discloses how AI systems contributed. Agreement between
AI-generated implementations is treated as error detection, not as external
scholarly replication.

Working notes, reviews, failed routes, and unfinished problems remain in a
separate repository and are not published here.
