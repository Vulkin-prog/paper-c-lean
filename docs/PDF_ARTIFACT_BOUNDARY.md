# PDF artifact boundary

## Repository roles

`paper-c-lean` is the formalization and release-evidence companion. The two
PDF files at its root are **external manuscript artifacts frozen as exact
bytes**. Their presence lets the audit and Comparator evidence bind a Lean
source snapshot to the manuscript versions it accompanies.

This repository is intentionally not the manuscript-authoring repository. It
does not contain the v09 TeX sources or promise to reconstruct the PDFs from
TeX. Therefore:

- a successful Lean build says nothing about TeX reconstruction;
- PDF QA in this repository validates the checked-in artifacts, not the
  authoring environment;
- absence of `.tex` files here is an explicit repository boundary, not an
  omitted Lean dependency.

## Frozen v09 artifacts

| Artifact | Language | Pages | Bytes | SHA-256 |
|---|---:|---:|---:|---|
| `paper_C_complete_v09.pdf` | French | 79 | 946,847 | `11d67677fbf9ba52a462b6df2d03a9affed71c670a27a2d525519af66358af44` |
| `paper_C_complete_v09_en.pdf` | English | 77 | 935,831 | `c99ac22eaa0bb59032fc2d683c03d19826f9e9bf27920433df4fae9b49e14cb1` |

These identities are consumed by the audit and release-binding machinery.
Changing either PDF creates a new source candidate and invalidates evidence
bound to the former bytes.

## Authoring source and TeX chain

The editorial sources and their TeX/QA chain live under `paperC/` in the
companion manuscript repository
[`Vulkin-prog/vdw-gpu-starter`](https://github.com/Vulkin-prog/vdw-gpu-starter):

- `paperC/paper_C_complete_v09.tex`;
- `paperC/paper_C_complete_v09_en.tex`;
- `paperC/build_paper_C_v09.sh`;
- `paperC/build_paper_C_v09_en.sh`;
- `paperC/qa_paper_C_v09.sh`;
- `paperC/QA_v09_audit_remediation.md` and `paperC/REVISION_v09.md`;
- the language-specific build JSON records, `ARTIFACT_INDEX_v09.json` and
  `MANIFEST_v09.sha256`.

For the PDF bytes frozen above, the TeX source hashes are:

| Source | SHA-256 |
|---|---|
| French v09 TeX | `ee3f9d4983fb3744150ed4b8c044d48285eef479a2e41b3a704e5d5080f0a203` |
| English v09 TeX | `524a5d1120a1d920b03a051c6aaf9f30b006ea0574fe0dc606e515ec26116201` |

The manuscript release must freeze an exact companion-repository commit and
its manifest. A branch name or pull-request number alone is not a permanent
reconstruction identity.

## What is and is not certified here

The repository-side PDF QA checks structural validity, embedded and subsetted
fonts, absence of Type 3 fonts, links and destinations, metadata, text
extraction, private-path leakage and the exact hashes above. Release evidence
may bind those hashes to an exact Lean source candidate and Comparator run.

Those checks do not by themselves constitute:

- a rebuild from the TeX sources;
- a page-by-page independent typographical review;
- a visual equivalence proof between the French and English editions;
- proof that the prose of the manuscript follows from the cited literature.

Reconstruction and visual QA records belong to the companion manuscript
repository. Scientific claims about Lean remain limited by the explicit open
literature bridges, irrespective of the PDF hash checks.

## Release hand-off

A qualified publication should record both sides of the boundary:

1. the exact `paper-c-lean` source/evidence commits and PDF hashes;
2. the exact companion-manuscript commit, TeX hashes, build records and
   manifest;
3. the hash of each uploaded asset, recalculated after downloading it from the
   release service.

This makes the separation of repositories explicit while preserving an exact,
auditable connection between formalization and manuscript artifacts.
