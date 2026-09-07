# Paper C — V3PREL manuscript sources

This directory preserves the author-supplied article (53 pages), technical
companion (25 pages), and all 34 source-archive files, byte for byte.
The two PDFs must stay together for their cross-document links.

- [Article](paper_C_version_3PREL_en.pdf)
- [Technical companion](paper_C_version_3PREL_technical_companion_en.pdf)
- [LaTeX sources and original build instructions](source/README.md)
- [Exact file identities](manifest.json)
- [V3PREL source-to-Lean correspondence](../../docs/FORMALIZATION_COVERAGE_V3PREL.md)

The `PaperC.V282` namespace is retained for stable proof names. The new
correspondence records the changed numbering and stronger statements;
the historical v2.8.2 manifest identifies the original formalization inputs.
In particular, V3PREL C.3 requires the corrected directional Stein input,
not the false unweighted Euclidean quadratic bound used before this revision.

Check the delivered sources from the repository root:

```sh
python3 scripts/check_v3prel_sources.py
```

The source archive's own `SHA256SUMS` is also preserved. Build generated
documents in a disposable copy of `source/`, so the delivered pair and
source inventory stay unchanged. The author's build report covers TeX/PDF
checks and finite diagnostics; it is not Lean or Palomar verification.
No new Palomar identifier is asserted for this manuscript version.
