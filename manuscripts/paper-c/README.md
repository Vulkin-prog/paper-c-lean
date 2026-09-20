# Paper C — article, companion and editable sources

*Long runs and rare patterns of a random completely multiplicative function*,
by Brice Pouly.

- [Article](paper_c_version_3PREL9_en.pdf)
- [Technical companion](paper_c_version_3PREL9_technical_companion_en.pdf)
- [Correspondence with the Lean development](../../docs/MANUSCRIPT_ALIGNMENT.md)
- [Explicit literature inputs](../../PaperCV282/LITERATURE_INPUTS.md)

This is the author-supplied manuscript of 20 September 2026, labelled 3PREL9.
The two PDFs and 26 compilation inputs are preserved byte for byte.
[manifest.json](manifest.json) identifies their exact contents and the supplied
archive. This directory is the public manuscript entry point; the final
published files and version-specific DOI will be incorporated after publication.

The two PDF filenames are kept together and unchanged to preserve their mutual
links. Nested archives, other papers, internal revision notes, duplicate exports,
diagnostic programs, build products and contact sheets are excluded. This is the
minimal source package, not a mirror of the author's complete working release.

From the repository root, verify the package and its formal correspondence with:

```sh
python3 scripts/check_current_manuscript.py
```

To rebuild the PDFs, copy this directory to a disposable working directory and
run `bash build.sh` there. The script regenerates both PDFs, so do not run it over
the delivered pair. It requires pdfLaTeX, Biber, Python 3 and the TeX packages
listed in `preamble.tex`. Both documents must be built together for their cross
references. No other paper or earlier PDF is a compilation dependency.

The integration checks establish file identity, local source completeness and
the recorded statement correspondence. They are not a fresh PDF rebuild or a
Palomar qualification. The seven literature propositions remain explicit theorem
arguments, including the analytic Stein input used for F.2.
