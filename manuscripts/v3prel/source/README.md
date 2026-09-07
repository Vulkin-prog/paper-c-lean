# Paper C — Version 3PREL

**Long runs and rare patterns of a random completely multiplicative function**  
Brice Pouly — 7 September 2026.

The article and its technical companion form one proof package. Keep both PDF files in the same directory to use their local cross-document links. Links are encoded as PDF file destinations; support can vary between PDF readers. Both documents have second-level bookmarks, while their printed contents remain compact.

## Rebuild

Requirements: a LaTeX installation with pdfLaTeX and the packages listed in `preamble.tex`, plus Python 3. The finite diagnostic programs use the Python standard library. PyMuPDF is optional for the PDF structural audit and for locating printed statement headings. The sources and diagnostics do not require internet access.

```sh
sha256sum -c SHA256SUMS
bash build.sh
```

The script removes generated files for this document pair, compiles both documents until their cross-references stabilize, checks the final logs, and runs the finite diagnostics. It fixes `SOURCE_DATE_EPOCH`, locale and timezone for reproducible PDF metadata. The exact PDF bytes can depend on the installed TeX engine and packages; the delivered pair was reconstructed on the environment listed in `BUILD_ENVIRONMENT.json`.

Output files:

- `paper_C_version_3PREL_en.pdf`
- `paper_C_version_3PREL_technical_companion_en.pdf`

The source archive contains no precompiled PDFs or auxiliary files. Each bibliography is generated from `bibliography/entries.json`; run `python3 tools/bibliography.py --write` after editing that shared data. The build checks that the generated bibliography files match it.

## Scope of the checks

The tests check finite algebraic identities and inequalities, manuscript references, bibliography consistency, PDF fonts and link destinations. They do not establish the asymptotic theorems, validate every external theorem or perform a Lean build. The written proofs and their cited literature inputs are the mathematical basis of the article.

The PDFs declare their language and embed fonts but are not structurally tagged; no PDF/UA conformance is asserted. The AI-assistance disclosure is on the first page of each PDF, with the full declaration in the article.
