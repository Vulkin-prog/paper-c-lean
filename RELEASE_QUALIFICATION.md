# Release qualification for Paper C / paper-c-lean v0.48.1

## Current status

`v0.48.1` is a **candidate**, not a qualified release. A merge of PR #5 alone
does not create a tag, an archive, a version DOI or hardened evidence binding
the final manuscript bytes. The internal modulo-two discharge of the
Halter--Koch interface changes the Lean core and the main Comparator theorem,
which now has three open literature premises rather than four. Consequently no
v0.48.0 core digest, Comparator result, or hardened archive qualifies this
candidate.

The final candidate pair currently present is bound to these exact bytes:
English, 77 pages and 935831 bytes, SHA-256
`c99ac22eaa0bb59032fc2d683c03d19826f9e9bf27920433df4fae9b49e14cb1`;
French, 79 pages and 946847 bytes, SHA-256
`11d67677fbf9ba52a462b6df2d03a9affed71c670a27a2d525519af66358af44`.

## Required gates

A qualified release uses two exact, consecutive commits.  The final source
commit **Q** contains the PDFs and all code.  A fresh hardened run is bound to
Q.  Its privacy-minimized result records and binding are then added by a
single-parent packaging commit **R** whose complete `Q..R` diff is restricted
to `release_evidence/v0.48.1/**`.

- [ ] The English and French v09 PDFs are the final rebuilt artifacts, and the
  manifest records their byte sizes, page counts and SHA-256 values.
- [ ] `scripts/qa_pdfs.sh` passes with `qpdf --check` or its explicit
  `mutool info` plus `mutool clean -gggg` fallback: every font is embedded and subset,
  no Type 3 font is present, all four Poppler URL/metadata/custom/destination
  inventories are produced, and no private/local path leaks.
- [ ] The standard reproducibility workflow is green for source commit Q: PDF
  bytes, the new source digest, bridge and literature-certificate mapping, root
  guards, project build, four isolated Challenge/Solution builds and exhaustive
  kernel audit.
- [ ] The regenerated bridge inventory records exactly six `external/open`
  interfaces globally, records `HK13-QO-conductor-fibres` as
  `external/discharged`, and identifies
  `PaperC.PellInput.quadraticOrderConductorFiberBound` as its internal
  discharge theorem.
- [ ] The documentary fileset contains three active source certificates for
  the open premises of Theorem 1.1 plus one historical Halter--Koch closure
  note; all four files are included in its digest, but only three are reported
  as active Theorem 1.1 certificates.
- [ ] The main finite-cylinder Challenge/Solution theorem has exactly the three
  open premises AGG, Evertse--Silverman, and Nicolas--Robin; the independent
  infinite-to-finite transfer target remains unconditional.
- [ ] Both agent counter-reviews are published with date, scope, original
  hashes and the explicit absence of human-review status.
- [ ] The Halter--Koch status follows
  `docs/HK_INTERFACE_ADJUDICATION.md`: the historical external provenance, the
  internal kernel discharge, and the fact that the cited text itself has not
  been formalized or human-reviewed are not conflated.
- [ ] A fresh **hardened, non-root, no-fallback** Comparator run is produced
  locally with `scripts/run_hardened_comparator.sh`, for both targets, while
  `HEAD` is source commit Q.
- [ ] The privacy-minimized result records and `release-binding.json` bind the
  source commit Q, its Comparator fileset, both final PDF hashes and the
  hardened archive SHA-256.
- [ ] Packaging commit R has Q as its unique parent and adds exactly the two
  result records and `release-binding.json` under
  `release_evidence/v0.48.1/`; it changes no source, PDF or metadata file.
- [ ] `.github/workflows/release-qualification.yml` passes against R.  It
  derives Q from R, verifies the restricted `Q..R` diff, recomputes the PDF and
  Comparator identities from both Git trees, and requires every binding and
  result record to carry Q.
- [ ] The tag `v0.48.1`, GitHub release, `paper_c_lean_v0481.zip`, checksums,
  QA report, hardened public evidence archive, its detached checksum, and its
  informational `.verified.json` report are published together.
- [ ] A Zenodo **version DOI** is minted for those exact bytes; the concept DOI
  remains the series-level identifier.

## Hardened evidence binding

After the final PDFs and code are committed, record source commit Q and run the
hardened procedure while `HEAD=Q`.  Copy only its two privacy-minimized result
records into the packaging directory before creating the binding. The raw
runner output is never a publication asset. Derivation and independent
verification of the omission-only public archive are mandatory gates; see
`scripts/PUBLIC_COMPARATOR_ARCHIVE.md` for prerequisites and the full
fail-closed contract:

```bash
SOURCE_Q=$(git rev-parse HEAD)
test -z "$(git status --porcelain=v1 --untracked-files=all)"
RAW_DIR=/absolute/path/to/paper-c-hardened-evidence-Q
PUBLIC_PARENT=/absolute/path/to/new-public-output
python3 scripts/derive_public_comparator_archive.py \
  --source "$RAW_DIR" \
  --output-dir "$PUBLIC_PARENT"
PUBLIC_ARCHIVE="$PUBLIC_PARENT/paper-c-hardened-public-$SOURCE_Q.tar.zst"
python3 scripts/verify_public_comparator_archive.py \
  --source "$RAW_DIR" \
  --archive "$PUBLIC_ARCHIVE" \
  --repository "$PWD"
PUBLIC_TREE=$(mktemp -d /tmp/paper-c-public-extract.XXXXXX)
tar --zstd -xf "$PUBLIC_ARCHIVE" -C "$PUBLIC_TREE"
PUBLIC_ROOT="$PUBLIC_TREE/paper-c-hardened-public-$SOURCE_Q"
mkdir -p release_evidence/v0.48.1
cp "$PUBLIC_ROOT/evidence/theorem-one-one/result-theorem-one-one.json" \
  release_evidence/v0.48.1/
cp "$PUBLIC_ROOT/evidence/infinite-finite-transfer/result-infinite-finite-transfer.json" \
  release_evidence/v0.48.1/
node scripts/create_release_binding.mjs \
  --evidence-dir release_evidence/v0.48.1 \
  --archive "$PUBLIC_ARCHIVE" \
  --raw-source "$RAW_DIR" \
  --output release_evidence/v0.48.1/release-binding.json
test "$(git rev-parse HEAD)" = "$SOURCE_Q"
git add release_evidence/v0.48.1
git diff --cached --name-only --diff-filter=ACMRTUXB
git commit -m "release: package v0.48.1 hardened evidence"
PACKAGING_R=$(git rev-parse HEAD)
test "$(git rev-parse HEAD^)" = "$SOURCE_Q"
```

Before committing R, the staged-path listing must contain only the three files
under `release_evidence/v0.48.1/`.  Run the manual release-qualification
workflow with `packaging_commit=PACKAGING_R` and the hardened archive SHA-256.
Tag R, not Q, only after this workflow succeeds.  The raw host transcript must
remain private when it contains usernames, hostnames, groups or local paths.

## Repository short description

The GitHub short description is repository metadata and cannot be changed by
the file-only remediation. The safe replacement is:

> Lean 4 formalization accompanying Paper C — zero sorry in the audited core and Solution files; six external literature bridges remain open; the Halter--Koch conductor interface is discharged internally; byte-hashed manuscripts and reproducible kernel audit.

The DOI displayed beside the repository should label the formalization concept
DOI separately from the exact version DOI.
