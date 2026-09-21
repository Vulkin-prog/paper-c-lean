# Paper C — published article, companion and sources

*Long runs and rare patterns of a random completely multiplicative function*,
by Brice Pouly. **Version 3, published 21 September 2026.**

- [Published record and version DOI](https://doi.org/10.5281/zenodo.22872154)
- [Article](paper_c_version_3_en.pdf)
- [Technical companion](paper_c_version_3_technical_companion_en.pdf)
- [Correspondence with Lean](../../docs/MANUSCRIPT_ALIGNMENT.md)
- [Explicit literature inputs](../../PaperCV282/LITERATURE_INPUTS.md)

The two PDFs and all 27 compilation inputs are copied byte for byte from the
Zenodo record and its source archive. [manifest.json](manifest.json) records
SHA-256 values, the source-archive identity, and the original PDF download
names and checksums. The Zenodo PDF names contain `(1)`; their local names
omit this suffix to match the published source build and cross-document links.
The PDF contents are unchanged. Source-archive documentation and checksum lists
are represented by this README and the manifest; no build products or working
notes are included.

The article's [formalization section](formalization_v3_en.tex) lists the seven
Palomar version 1 registrations and the formalization's explicit limitations.
The manuscript uses the CC-BY-4.0 licence stated by the Zenodo record.

Verify the delivered bytes, source dependencies and mathematical correspondence
from the repository root:

```sh
python3 scripts/check_current_manuscript.py
```

To rebuild both PDFs, copy this directory to a disposable working directory and
run `bash build.sh` there. The script regenerates the PDFs, so do not run it over
the published pair. It requires pdfLaTeX, Biber, Python 3 and the TeX packages
listed in `preamble.tex`. Both documents must be built together for cross
references. No previous PDF or external article is a compilation dependency.

Integration verified the Zenodo checksums, source correspondence, and the
published formalization pages. It did not regenerate the PDF pair; Biber was
not available locally. The seven literature propositions remain explicit formal
premises, including the analytic Stein solution used for F.2.
