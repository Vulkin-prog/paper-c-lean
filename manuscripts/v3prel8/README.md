# Paper C — 3PREL8 manuscript sources

This directory contains the author-supplied article (66 pages), technical
companion (42 pages), and the **26 autonomous compilation inputs**, preserved
byte for byte from `paper_c_version_3PREL8_release.zip` (16 September 2026).
The two PDF filenames stay unchanged and together so their cross-document links
remain usable. [manifest.json](manifest.json) records the archive identity and
all 28 retained files.

- [Article](paper_c_version_3PREL8_en.pdf)
- [Technical companion](paper_c_version_3PREL8_technical_companion_en.pdf)
- [Current source-to-Lean comparison](../../docs/FORMALIZATION_COVERAGE_V3PREL8.md)

The public payload excludes nested predecessor releases, internal editorial
reviews, development inputs, diagnostic scripts and their outputs, compilation
logs, auxiliary files, contact sheets, duplicate bibliography exports and
revision working files. None is a compilation dependency. The original archive
is not republished. The earlier manuscript snapshot in `../v3prel/` is retained
because existing coverage and validation records identify it.

Verify the curated payload from the repository root:

```sh
python3 scripts/check_v3prel8_sources.py
```

To rebuild, copy this directory to a disposable working directory and run
`bash build.sh` there. The delivered script deletes and regenerates its PDFs
and auxiliary files, so do not build over the frozen delivered pair. It needs
pdfLaTeX, Biber, Python 3, and the TeX packages named in `preamble.tex`, including
BibLaTeX, Latin Modern, TikZ and cleveref. Both documents must be built together
because they share references. No prior PDF, prior release or other paper is
needed. The author's reported toolchain is pdfTeX 1.40.26 and Biber 2.20; that
report is not an independent rebuild or Lean certification.

Archiving this edition does not extend the earlier formalization's coverage.
The correspondence distinguishes preserved statements, new proved components,
and open proof obligations. No new Palomar qualification or version-specific
publication DOI is asserted for 3PREL8.
