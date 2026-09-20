# Lean 4.34.0 migration

The migration starts from the validated Lean 4.33.1 source commit
`8b6e838f90632631575d37fafada95950d0a9051`. It retains the mathematical
arguments and the seven explicit literature premises of the V3PREL development.
The complete build and all three axiom audits pass. The official core-notation
printing component also accepts all 69 V3 Challenge signatures. All 80 selected
declarations pass the ten local Comparator/NanoDa replays and the separate
strict interface comparison. The [validation evidence](../migration_evidence/lean-4.34.0/README.md)
binds these results to exact source hashes.

## Exact versions

| Component | Version or role | Commit |
|---|---|---|
| Lean | v4.34.0 | `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| Mathlib | v4.34.0 | `5ed2965256430c3649e86755f9576b54eca72435` |
| lean4export | v4.34.0, built with the same project compiler | `076e8e57707e813375e8f9da8bf989799ace9680` |
| Comparator | official pinned source, its own Lean v4.34.0-rc1 | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| NanoDa | independent kernel | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | sandbox | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |
| PalomarSubmission | current metadata contract, adapter and printing component | `3561d237dcc4b28482558ad28a64d767d7cc8615` |

The exporter source and effective compiler are checked independently. Comparator
is built using its declared compiler, rather than the project compiler. The
complete nine-package dependency lock is in [lake-manifest.json](../lake-manifest.json).

## Mathematical compatibility review

Most edits follow Mathlib API changes: 159 probability-measure map proofs in
84 files, 18 uses of `Finset.prod_le_prod` renamed to `prod_le_prod₀`, three uses
of `prod_le_one` renamed to `prod_le_one₀`, the implicit function argument of
`Measurable.of_eval`, and `Finsupp.mapDomain_apply_of_injective`. Several proofs
also drop a tactic after the preceding tactic now closes its goal.

The proof adaptations affect 115 Lean files relative to the 4.33.1 snapshot:
11 in `PaperC`, 98 in `PaperCV282`, three Challenge files and their three matching
Solution files. `AuditCheck.lean` additionally changes its generated digest
comment. No selected theorem is added or removed. Existing deprecation warnings
are not suppressed by new global compatibility options.

### Measures and conditional distributions

Mathlib changed the total definition of `Measure.map`: outside the almost
everywhere measurable case, a nonzero measure now maps to an arbitrary Dirac
mass. Previously that exceptional case was zero. This is a semantic library
change, not merely a theorem rename.

Every migrated call to `Measure.isProbabilityMeasure_map` retains its original
measurability proof through `Measure.isProbabilityMeasure_map_iff`. The proofs
of `map_smul` and the conditional-distribution identities supply the newly
required measurable-map premises from hypotheses already present in the
original statements, or from countability. No measurability assumption is
silently dropped or added to a selected theorem.

`ProbabilityMeasure.map` now takes the function explicitly. The independent
Gaussian-increment and Poisson-threshold identities use `thresholdSum J` in
their statements; its continuity and measurability are already established in
the same development. The represented probability laws are the measurable
pushforwards in both versions. The helper signatures do change syntactically,
so source hashes and old qualification receipts are not interchangeable.

### Cancellation classes

Mathlib removed the deprecated `CancelCommMonoidWithZero` structure. Its old
compatibility layer in `QuadraticIdealDivisors` is replaced by the current
`CommMonoidWithZero` data and `IsCancelMulZero` proposition-valued mixin in
`factorCountProduct`. The removed layer had constructed the old structure from
these same fields and recovered these same instances from it. The factor-count
product remains the product over normalized factors; its public Lean helper
interface uses the split classes. The downstream ideal-divisor and Pell proofs
are rebuilt and included in the axiom audit.

The derivation-local option already documented in the
[4.33.1 review](LEAN_4_33_1_MIGRATION.md#one-local-derivation-exception) is retained.
No additional compatibility option, axiom, proof placeholder or literature
premise was introduced for 4.34.

## Validation

| Check | Result |
|---|---|
| Complete build | PASS, all 23 libraries; 10,113 Lake tasks including dependencies and replays |
| Core axiom audit | PASS, exact 4,074-name inventory |
| V1.1 axiom audit | PASS, exact seven-name inventory |
| V3 development axiom audit | PASS, exact 6,094-name inventory |
| Canonical Mathlib provenance | PASS against canonical master; release-tag fallback also regression-tested |
| Official V3 metadata/import preflight | PASS, five families, 69 declarations, 8,908 imported source modules |
| Official core-notation audit | PASS, all 69 V3 Challenge signatures |
| Strict Challenge/Solution comparison | PASS, all 80 declarations across ten configurations |
| Comparator and NanoDa | PASS locally, all ten configurations and 80 declarations |
| Tooling regression tests | PASS, 48 Python tests and the root audit guards |
| External Palomar registration | Not performed by this migration |

Audit counts are separate scopes, not a deduplicated total. The only permitted
foundational axioms are `propext`, `Classical.choice` and `Quot.sound`. The seven
explicit literature premises remain hypotheses; axiom checking does not prove
them. Intentional holes remain exclusively in the Challenge skeletons.

The printing probe uses the exact official script with imported environment
extensions disabled. It exercises the component previously blocked by issue
134. It does not run the complete server-side rendering or editorial pipeline.

## Reproducing local validation

Use exact Lean 4.34.0 and its matching Mathlib lock. Do not reuse compiled
objects from 4.32 or 4.33.1. The default `lake build` covers only `PaperC`.

```sh
lake build PaperC PaperCV11 PaperCV282 \
  Challenge Solution ChallengeTransfer SolutionTransfer \
  ChallengeTheoremOneTwo SolutionTheoremOneTwo \
  ChallengeTheoremOneFour SolutionTheoremOneFour \
  ChallengeTheoremSixteenTwo SolutionTheoremSixteenTwo \
  ChallengeV3CriticalField SolutionV3CriticalField \
  ChallengeV3Patterns SolutionV3Patterns \
  ChallengeV3Limits SolutionV3Limits \
  ChallengeV3Boundary SolutionV3Boundary \
  ChallengeV3Crossover SolutionV3Crossover
lake env lean AuditCheck.lean > core-audit.log 2>&1
lake env lean PaperCV11/Audit.lean > v11-audit.log 2>&1
lake env lean PaperCV282/Audit.lean > v282-audit.log 2>&1
node scripts/verify_audit.mjs --input core-audit.log
python3 scripts/check_v282_audit.py --log v282-audit.log
node scripts/generate_audit.mjs --check-source-digest
node scripts/generate_audit.mjs --check-pdfs
node scripts/generate_audit.mjs --check-literature-certificates
node scripts/generate_audit.mjs --check
python3 -m unittest discover -s scripts -p 'test_*.py'
node scripts/test_audit_root_guards.mjs
```

Check the V1.1 transcript against the seven names in `PaperCV11/Audit.lean`
and the same foundational allowlist. For the ten separate Comparator runs,
use the five historical configurations with `palomar/verify-comparator.sh`
and the five V3 configurations with `palomar/v3prel/verify-comparator.sh`.
Both runners force NanoDa on a protected configuration copy. A hardened local
run additionally uses the official `systemd-run` address-family restriction;
its successful replay still does not register a Palomar entry.

## Provenance and preserved evidence

The current 382-file core digest is
`545b5dfe5f972614c0e682065640c1c34a03c8819255436f2adf6032a9d0f056`.
The 4.32 baseline digest
`3505665c32c33ddc5508994964f8623911ae83720b814f2fe4b7573bccba4137`
and the [4.33.1 evidence](../migration_evidence/lean-4.33.1/README.md) remain
unchanged. Historical release records, original manuscript files and published
identifiers are preserved. Their qualification does not transfer automatically
to this source snapshot.

Upstream [PR 128](https://github.com/PalomarRegistry/PalomarSubmission/pull/128)
and [PR 137](https://github.com/PalomarRegistry/PalomarSubmission/pull/137) were
merged on 14 September 2026. The former accepts exact canonical Mathlib release
tags when a release is outside master ancestry; the latter fixes the type-proxy
printing failure reported in
[issue 134](https://github.com/PalomarRegistry/PalomarSubmission/issues/134).
The local provenance guard now supports the canonical release fallback without
trusting repository-local tags, arbitrary tags or alternate submitted remotes.

All local work stays on the Ubuntu partition. Builds and kernel replays are
serialized, with a disk guard requiring 10 GiB before starting and stopping
below a 5 GiB reserve. Existing 4.32 and 4.33.1 runtimes and worktrees are
preserved. These machine-specific precautions are not new theorem hypotheses.
