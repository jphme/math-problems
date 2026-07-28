# Erdős 634 manuscript

The current manuscript is:

- `progress634.tex` — source of record
- `progress634.pdf` — compiled manuscript PDF
- `verification_manifest.md` — commands, environments, results, and hashes
- `figures/N88_tiling.png` and `figures/N189_tiling.png` — clean renders derived from the exact SVG certificates
- `progress634-arxiv.tar.gz` — clean arXiv upload package: source and figures
  at the root, with the curated reproducibility record under `anc/`

Version 0.4 is dated 2026-07-28. It is the major revision responding to the
independent referee report of 2026-07-27: the `N=33` and 21-ray negative
results are now carried by exported refutation certificates validated by an
independently written checker (`computation/tiling_search/check_refutation.py`,
written from `CERT_SPEC.md` alone); the branch reduction for `N=33` is a
formal proposition with a per-branch disposition table; every imported
classification, rationality, and construction statement is stated with a
pinned version and collected in a dependency ledger; the exact-subtraction
lemma has a full rotation-system proof; the fit-test, pruning, memoization,
and run-status semantics are proved as lemmas; the trapezoid classification
is split into its constructive and exclusion halves; and the Laurent theorem
carries an explicit isomorphism plus universal-property corollary, the 60°
unit lemma, the expanded Eisenstein-square lemma, and the γ=2α
angle-representation lemma. Version 0.3 (2026-07-27) integrated the audited
portion of theory report #7 and the first independent manuscript review. The
paper is deliberately
structured so that new results can be added without rewriting the status
logic:

1. Unconditional mathematical results belong in the main theorem sections.
2. Exact exhaustive results must be labelled **computer-assisted** and documented in Appendix A and `verification_manifest.md`.
3. Positive tilings must cite an exact coordinate certificate and its digest.
4. Any result depending on the unfinished forced-layer induction G11 stays in the red conditional appendix and is not used downstream.
5. The conservative result ledger is separate from the provisional below-200 table.
6. A macro inventory read from a vector figure is labelled as a figure audit,
   not an exact coordinate certificate.

## Update checklist

Before each numbered draft:

1. Treat this paper and `verification_manifest.md` as the vetted source of
   record. Consult `../STATUS.md` and `../invariants.md` for project history,
   but independently re-audit any G11-dependent statement; do not rely on the
   stale summaries in `../README.md`, `../theory_brief.md`, or
   `../OPERATIONS.md`.
2. Re-run the arithmetic verification scripts and `searcher2.py --selftest`.
3. Re-run every certificate verifier affected by the change.
4. For a new negative result, record the complete candidate reduction, exact search scope, node count, warning count, limits, and whether a separately implemented search agrees.
5. Update the evidence level in both the main text and the result-ledger appendix.
6. Re-audit the conditional-value set before changing the below-200 narrative.
7. Check whether Michael Beeson's new all-primes preprint has acquired an arXiv identifier.
8. Compile twice, render every PDF page, and inspect the title page, tables, figures, warning boxes, bibliography, and final page.
9. Send the changed draft to Michael Beeson and other directly affected authors before public posting.
10. Increment the version and date only after the verification pass succeeds.

## Build

From this directory:

```bash
tectonic progress634.tex
pdfinfo progress634.pdf
pdftoppm -png -r 150 progress634.pdf /tmp/progress634-page
```

The exact tiling sources remain under:

```text
../computation/tiling_search/results/
```

The paper figures omit only the diagnostic text labels from the SVG renders; no geometry was changed.

## arXiv package

The upload archive deliberately excludes the compiled PDF and all `.aux`,
`.log`, and `.out` files.  It contains `progress634.tex`, the two used
PNG figures, and the ancillary verification manifest, programs, exact
certificates, search records, and captured audit outputs — now including the
refutation-certificate specification (`CERT_SPEC.md`), the exporter-capable
searcher, the independent checker and its test suite, the two refutation
certificates (`N33_refutation.jsonl.gz`, `N21_refutation.jsonl.gz`), and the
deferred-campaign instructions (`RELAUNCH_certificates.md`).  The main source
compiles from the archive root with PDFLaTeX-compatible TeX.
