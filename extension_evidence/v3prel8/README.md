# Initial 3PREL8 component validation

This is the initial snapshot at commit `6656221b244925bd56b2bb02b53b303d4b396567`.
Its source hashes are historical and are not a receipt for later modifications.
The [prime-forcing batch](prime-forcing/README.md) records the second validation;
the [microscopic-field batch](microscopic-field/README.md) is retained as historical evidence;
the [reciprocal-pivot batch](reciprocal-pivots/README.md) is also retained as historical evidence.

The [receipt](validation.json) identifies the exact new Lean sources, the
successful 24-library build, the 33-name axiom audit, the curated manuscript
payload and the PDF structural checks. Compressed logs preserve their exact
bytes; both compressed and uncompressed hashes are recorded.

This is **component validation while full paper alignment remains incomplete**.
It does not extend the previous Palomar scope or qualify the new numbered
results. See the [coverage ledger](../../docs/FORMALIZATION_COVERAGE_V3PREL8.md).

The 1,171 baseline Lean files and historical evidence are unchanged. New source
hashes are independent of the later packaging commit. The supplied PDFs and
26 compilation inputs are preserved byte for byte; the TeX build was not rerun
locally because Biber/BibLaTeX are absent.

The current receipt is the [prime obstruction checkpoint](prime-obstruction/README.md),
with 1,005 audited theorems across 202 modules. Earlier receipts retain their
original source hashes and historical scope.
