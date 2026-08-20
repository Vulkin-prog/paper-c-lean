# Palomar qualification candidate

This directory prepares one deliberately narrow Palomar Registry entry for the
quantitative finite-cylinder form of Paper C, Theorem 1.1.

Submission fields after this pull request is merged:

- project path: leave blank (the Lean project is the repository root);
- Comparator configuration: `comparator/theorem_one_one.json`;
- formalization metadata: `palomar/formalization.yaml`;
- commit: the full 40-character SHA of the final merged snapshot.

The selected declaration is
`paper_c_theorem_one_one_finite_cylinder`. The auxiliary exact
infinite-product/finite-cylinder transfer is important evidence for the paper,
but it is not submitted as a second Palomar entry because this candidate is
scoped to the research-level quantitative theorem itself.

`Challenge.lean` is 30,480 bytes and 721 lines. It is below Palomar's hard
limits of 100 KiB and 1,000 lines and below the preferred 32 KiB byte surface,
but it exceeds the preferred 300-line surface and will therefore receive a
mechanical warning. The existing statement boundary is retained because its
line count comes largely from explicit mathematical definitions, literature
premises, and their audit docstrings; reformatting it solely to suppress a
warning would make it less auditable and would perturb a previously reviewed
interface.

The compared Lean modules intentionally retain their historical v08
manuscript anchor. The Palomar metadata identifies both those exact frozen
bytes and the current v09 registration source: the paper's Theorem 1.1
statement is unchanged, while Corollary 13.10 moved from printed/PDF p. 41 to
p. 43.

The metadata records the principal limitation directly: the compared theorem
is conditional on three fully stated ordinary literature propositions. Those
propositions are theorem arguments rather than Lean axioms. Their
source-to-statement certificates are agent-reviewed documentary evidence, not
Lean proofs or independent human certification.

## Reproduce the candidate checks

The submitted Comparator file preserves the historical release record with
`enable_nanoda: false`. Palomar intentionally ignores that author-controlled
field and writes a protected copy with NanoDa enabled. The qualification replay
mirrors that behavior without changing the certified historical configuration.

`palomar/verify-comparator.sh` uses the trusted-tool revisions pinned by
`PalomarRegistry/PalomarSubmission` at commit
`0a2c287a924d2a7cb22e2b12f12b27321bb485a3` (2026-08-20). It builds and runs
Comparator against a protected copy of `comparator/theorem_one_one.json`, with
the toolchain-matched lean4export release, real Landrun, and the independent
NanoDa kernel:

```bash
PALOMAR_COMPARATOR_CACHE=/path/to/disposable/cache \
  ./palomar/verify-comparator.sh
```

The GitHub workflow `.github/workflows/palomar-qualification.yml` runs both
the current Palomar metadata contract and this NanoDa-enabled replay. A pass is
a pre-submission compatibility result. Palomar's own public mechanical
verification at the submitted immutable commit remains authoritative.
