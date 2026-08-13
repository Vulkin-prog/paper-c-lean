# Release qualification for Paper C / paper-c-lean v0.48.1

## Current status

`v0.48.1` is a **candidate**, not a qualified release. A merge of PR #5 alone
does not create a tag, an archive, a version DOI or hardened evidence binding
the final manuscript bytes.

## Required gates

A qualified release must satisfy all of the following on one exact commit.

- [ ] The English and French v09 PDFs are the final rebuilt artifacts, and the
  manifest records their byte sizes, page counts and SHA-256 values.
- [ ] `scripts/qa_pdfs.sh` passes: `qpdf`, embedded-font inventory, no Type 3
  fonts, URL/metadata extraction and no private/local path leakage.
- [ ] The standard reproducibility workflow is green for the exact commit: PDF
  bytes, source digest, literature-certificate mapping, root guards, project
  build, four isolated Challenge/Solution builds and exhaustive kernel audit.
- [ ] Both agent counter-reviews are published with date, scope, original
  hashes and the explicit absence of human-review status.
- [ ] The Halter--Koch status follows
  `docs/HK_INTERFACE_ADJUDICATION.md`: the mathematical proof route and the
  conditional Lean route are not conflated.
- [ ] A fresh **hardened, non-root, no-fallback** Comparator run is produced
  locally with `scripts/run_hardened_comparator.sh`, for both targets.
- [ ] The privacy-minimized result records and `release-binding.json` bind the
  final commit, the unchanged Comparator fileset, both final PDF hashes and the
  hardened archive SHA-256.
- [ ] `.github/workflows/release-qualification.yml` passes against that exact
  commit and binding.
- [ ] The tag `v0.48.1`, GitHub release, `paper_c_lean_v0481.zip`, checksums,
  QA report and hardened public evidence archive are published together.
- [ ] A Zenodo **version DOI** is minted for those exact bytes; the concept DOI
  remains the series-level identifier.

## Hardened evidence binding

After a successful local hardened run:

```bash
node scripts/create_release_binding.mjs \
  --evidence-dir /absolute/path/to/privacy-minimized-evidence \
  --archive /absolute/path/to/paper-c-hardened-public-<commit>.tar.zst \
  --output release_evidence/v0.48.1/release-binding.json
```

Copy the two privacy-minimized `result-*.json` files beside the binding, commit
those small records, and run the manual release-qualification workflow with
the exact commit SHA and hardened archive SHA-256. The raw host transcript must
remain private when it contains usernames, hostnames, groups or local paths.

## Repository short description

The GitHub short description is repository metadata and cannot be changed by
the file-only remediation. The safe replacement is:

> Lean 4 formalization accompanying Paper C — 4,070 audited public declarations; zero sorry in the frozen core and Solution files; seven explicit external literature bridges; byte-hashed manuscripts and reproducible kernel audit.

The DOI displayed beside the repository should label the formalization concept
DOI separately from the exact version DOI.
