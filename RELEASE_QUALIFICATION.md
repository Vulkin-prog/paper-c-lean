# Release qualification for Paper C / paper-c-lean v0.48.1

## Current status

`v0.48.1` is a **candidate**, not a qualified release. A merge of PR #5 alone
does not create a tag, an archive, a version DOI or hardened evidence binding
the final manuscript bytes.

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
  bytes, source digest, literature-certificate mapping, root guards, project
  build, four isolated Challenge/Solution builds and exhaustive kernel audit.
- [ ] Both agent counter-reviews are published with date, scope, original
  hashes and the explicit absence of human-review status.
- [ ] The Halter--Koch status follows
  `docs/HK_INTERFACE_ADJUDICATION.md`: the mathematical proof route and the
  conditional Lean route are not conflated.
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
  QA report and hardened public evidence archive are published together.
- [ ] A Zenodo **version DOI** is minted for those exact bytes; the concept DOI
  remains the series-level identifier.

## Hardened evidence binding

After the final PDFs and code are committed, record source commit Q and run the
hardened procedure while `HEAD=Q`.  Copy only its two privacy-minimized result
records into the packaging directory before creating the binding:

```bash
SOURCE_Q=$(git rev-parse HEAD)
test -z "$(git status --porcelain=v1 --untracked-files=all)"
mkdir -p release_evidence/v0.48.1
cp /absolute/path/to/privacy-minimized-evidence/result-theorem-one-one.json \
  release_evidence/v0.48.1/
cp /absolute/path/to/privacy-minimized-evidence/result-infinite-finite-transfer.json \
  release_evidence/v0.48.1/
node scripts/create_release_binding.mjs \
  --evidence-dir release_evidence/v0.48.1 \
  --archive /absolute/path/to/paper-c-hardened-public-<commit>.tar.zst \
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

> Lean 4 formalization accompanying Paper C — 4,070 audited public declarations; zero sorry in the frozen core and Solution files; seven explicit external literature bridges; byte-hashed manuscripts and reproducible kernel audit.

The DOI displayed beside the repository should label the formalization concept
DOI separately from the exact version DOI.
