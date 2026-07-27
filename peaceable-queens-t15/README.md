# Unified peaceable-queens paper

This former \(15\times15\)/\(16\times16\) companion directory is retained as
a stable compatibility path. It now contains the same finished paper and
complete ancillary bundle as
[`../peaceable-queens-even-torus/`](../peaceable-queens-even-torus/).

The unified paper proves the exact parity formula for every even toroidal
board, together with \(t(15)=20\) and \(t(17)=28\). In particular it subsumes
both results of the older partial paper.

## Contents

- [`peace1516.pdf`](peace1516.pdf): compatibility copy of the 20-page unified
  paper.
- [`peace1516.tex`](peace1516.tex): identical source under the historical
  filename.
- [`peace1516-arxiv.tar.gz`](peace1516-arxiv.tar.gz): source and ancillary
  files for fresh extraction.
- [`anc/README.txt`](anc/README.txt): full inventory and reproduction guide.
- [`anc/SHA256SUMS`](anc/SHA256SUMS): integrity manifest.

Quick audit:

```bash
cd anc
shasum -a 256 -c SHA256SUMS
uv run --isolated --python 3.14.6 \
  --with sympy==1.14.0 --with mpmath==1.3.0 \
  python verify_bundle.py
```

The canonical publication and immutable artifact link are maintained in
[`../peaceable-queens-even-torus/`](../peaceable-queens-even-torus/).
