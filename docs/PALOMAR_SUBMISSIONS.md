# Palomar submission guide

The current selection contains **89 declarations in seven configurations**,
using **Lean 4.34.0 and Mathlib v4.34.0**. The [README](../README.md) links the
article, companion, editable sources and publication records. All seven
metadata files identify the current manuscript by immutable source URL and
SHA-256, and include the author's structured ORCID.

## Fields for the submissions

For each submission use repository **`https://github.com/Vulkin-prog/paper-c-lean`**,
a validated **full 40-character commit SHA**, and the configuration below.
For the remaining Palm submission, use the merged prose-correction commit after
its qualification jobs succeed. Existing registered snapshots stay immutable.

| Entry | Comparator configuration | Selected results |
|---|---|---:|
| Critical Poisson fields and information-adapted conditioning | `comparator/v3prel_critical_field.json` | 16 |
| Typical dictionaries, exact marks and compound Poisson clusters | `comparator/v3prel_patterns.json` | 11 |
| Threshold staircases and the Poisson–Gaussian bridge | `comparator/v3prel_limits.json` | 29 |
| Microscopic boundary, prefixes and longest runs | `comparator/v3prel_boundary.json` | 7 |
| Microscopic–bulk crossover and conditional affine laws | `comparator/v3prel_crossover.json` | 11 |
| Microscopic signed fields and empirical Poisson laws | `comparator/v3prel_microscopic.json` | 6 |
| Regular configurations, Palm deficits and the cumulant obstruction | `comparator/v3prel_palm.json` | 9 |

Leave **Project path** empty: the Lean project is at the repository root.
Set **Formalization metadata path** explicitly for each entry; leaving it empty
would select the generated root audit file, which describes a different scope.

| Configuration suffix | Formalization metadata path |
|---|---|
| `critical_field` | `palomar/v3prel/critical_field/formalization.yaml` |
| `patterns` | `palomar/v3prel/patterns/formalization.yaml` |
| `limits` | `palomar/v3prel/limits/formalization.yaml` |
| `boundary` | `palomar/v3prel/boundary/formalization.yaml` |
| `crossover` | `palomar/v3prel/crossover/formalization.yaml` |
| `microscopic` | `palomar/v3prel/microscopic/formalization.yaml` |
| `palm` | `palomar/v3prel/palm/formalization.yaml` |

The source licence for the Lean project is **Apache-2.0**; the manuscript's
licence is recorded separately. The repository owner is **Vulkin-prog**.

Use `project.name` and `project.description` there for a title or description
field if the submission form requests them. Bibliographic references belong in
`sources`; author identity and ORCID belong in `project.authors`. They need not
be repeated in the mathematical description. These metadata files are specific
to the selected configuration; the generated root audit metadata is not the
metadata for these submissions.

For a family that already has an **issued registry identifier**, choose the
next version of that identifier where appropriate. A queued or failed attempt
without an issued identifier is not an existing registration. The two additional
families are prepared as new registrations. Record the identifiers actually
issued by Palomar; none is inferred or invented here.

## Current registration status

The author confirmed the following issued identifiers on 20–21 September 2026,
in submission order. This table records the author's confirmations; it does not
assert an independent public-registry check.

| Family | Issued identifier | Version |
|---|---|---:|
| Critical field | `PALOMAR-2026-09-20-000003` | 1 |
| Patterns | `PALOMAR-2026-09-20-000004` | 1 |
| Limits | `PALOMAR-2026-09-20-000007` | 1 |
| Boundary | `PALOMAR-2026-09-20-000011` | 1 |
| Crossover | `PALOMAR-2026-09-20-000012` | 1 |
| Microscopic | `PALOMAR-2026-09-21-000002` | 1 |

Keep these registrations. Their future publication updates should use these
identifiers and the next version, rather than creating duplicates.

The corrected Limits dossier passed review and was registered as listed above.
The [Limits review follow-up](PALOMAR_REVIEW_FOLLOWUP.md) records its earlier
probability-law correction and the separate Mathlib-cache warning. The subsequent
[audit of the four remaining dossiers](PALOMAR_REMAINING_DOSSIERS_AUDIT.md) records
the corresponding probability and measurability guarantees.

### Palm: complete mathematical narrative

The Palm attempt passed mechanical verification but automated review on
21 September 2026 at 05:14:57 UTC requested an assessable informal account of
`PaperCV3Audit.Palm.ordinary_deletion`. No identifier has been reported for this
attempt. The review explicitly said that the Lean statement need not change.

The selected declaration now has a mathematical docstring in both
[ChallengeV3Palm.lean](../ChallengeV3Palm.lean) and
[SolutionV3Palm.lean](../SolutionV3Palm.lean). It defines the retained field,
the deleted-site interpretation, the weighted equality, the precise regularity
restriction, the arbitrary measurable outside event, and the positive small-prime
conditioning assumption. The metadata locates the companion's exact equation.
No Lean statement, proof, definition, dependency pin or manuscript is changed.

The next attempt, at commit `3ecbfb8122b15f40ffd01a51736b1e56dccb0ff8`,
also passed mechanical verification and rendering. Its automated review on
21 September 2026 at 07:05:14 UTC requested concrete accounts of four further
selected results: `full_deficit_comparison`, `full_retained_normalized_comparison`,
`normalized_deficit_eventually`, and `stronger_retention_counts`. This was another
narrative finding; the review stated that their Lean statements need not change.

The follow-up supplies shared notation in the module documentation and exact
accounts for **all nine selected declarations**, in both Challenge and Solution.
The existing ordinary-deletion account is retained. The scope check covers:

| Declaration (under `PaperCV3Audit.Palm`) | Concrete account and domain checked |
|---|---|
| `source_target_palm_mass` | Exact mass identity and all coefficient, measurability, probability and positivity conclusions; positive small-prime event and regular plant. |
| `full_deficit_comparison` | Both masses sum to one; TV minus the full deficit lies between zero and target irregularity; no extra cardinality cutoff or literature premise. |
| `ordinary_deletion` | Exact weighted identity for any measurable outside event; deleted-site interpretation and conditioning assumptions. |
| `full_retained_normalized_comparison` | Absolute TV-minus-normalized-deficit bound and all four errors; arbitrary nested finite sets and cardinality cutoff, with positive normalizers. |
| `normalized_deficit_eventually` | Exact constants and exponents; threshold before the event, sites and excess cutoff; four arithmetic literature inputs and the actual finite-carrier Stein premise. |
| `original_cumulant_obstruction` | Exact prime scales, positive constant, centered moments, all cumulant orders and PNT premise. |
| `retained_cumulant_obstruction` | Same obstruction for fixed theta >= 0; no theta < c restriction in this theorem. |
| `stronger_retention_counts` | Both cardinality estimates, floors and ceilings, logarithmic regime, theta range and PNT-only premise. |
| `regular_target_probability` | Diverging intensity, eventual regime, positive theta, mark and population cutoffs, and left-boundary labeling. |

The full and Bernoulli-normalized deficits are explicitly distinguished. The
bound with exponent `-1/3 + epsilon` is stated for every positive epsilon;
its power error tends to zero when epsilon is below one third. The target
regularity result alone is not presented as a source approximation theorem.
No manuscript revision or further formal hypothesis is introduced.

The [statement-alignment policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/prompts/02-statement-alignment.md)
explicitly includes selected declaration docstrings among eligible narrative
sources. The detailed account is placed there, leaving the project abstract
concise. The other abstracts' publication refresh remains deferred to the V2
update after the final paper is supplied.

Local validation on 21 September 2026: the Palm Challenge and Solution build
successfully; after removing comments, both files have exactly the same Lean
tokens as commit `3ecbfb8122b15f40ffd01a51736b1e56dccb0ff8`. The manuscript
identity check, full seven-family source preflight with the pinned official
metadata contract, and all 25 candidate/source regression tests pass.
The Comparator source guard also passes, and all nine selected declaration
docstrings match between Challenge and Solution. These are local checks, not
a new dual-kernel receipt or a Palomar review.

After merging and qualification, submit Palm using the new full commit SHA,
`comparator/v3prel_palm.json`, and
`palomar/v3prel/palm/formalization.yaml`. Leave Project path and the existing
Palomar ID field empty: this is still a first registration, not a V2 update.
The rejected attempt can be withdrawn. A fresh automated review remains required;
the prose correction does not itself constitute editorial acceptance.

## Exact mathematical selection

Each Challenge imports Mathlib only, constructs the source and target objects,
and contains placeholders only for its selected declarations. Each Solution
proves those same statements using explicit bridges to the development.
Every configuration enables NanoDa and permits only `propext`, `Quot.sound`
and `Classical.choice`.

- **Critical field:** critical lattice and diffuse laws, scalar and spatial
  conditional means, hard and soft conditioning, arbitrary statistics and masks,
  stable recorded variables and uniform quenched convergence. Three declarations
  additionally establish the information-cutoff equation, its constrained maximum
  and the actual field comparison of article 6.2 with a prescribed conditioning floor.
- **Patterns:** word overlaps, dictionary Poisson law, exact signs and excesses,
  aggregation and compound clusters. Two declarations add uniform mean bounds for
  fixed-size and affine dictionaries (5.3–5.4 / 1.3). The dictionary is fixed inside
  each conditional distance before the dictionary-selection average is taken.
- **Limits:** staircase joint limits, Gaussian covariance and AR(1) structure,
  local/central/moderate bounds and conditional transfers; companion D.1 and D.4
  through the actual whole integer process, restrictions and compact-test Laplace
  functional. Both upper-point-law assertions include proved measurability and
  probability normalization; every finite conditioning count has positive mass.
  A separate vague-topology convergence declaration is not selected.
- **Boundary:** exact border probability, microscopic relative error, localization,
  mesoscopic exclusion, contained-prefix law, almost-sure envelopes and longest runs.
- **Crossover:** the moving two-source marked mixture, locations and signs in the
  boundary, intermediate and bulk phases, and the final conditioned affine law.
- **Microscopic:** exact all-excess signed source coefficients, quantitative full-field
  comparison in the moving-depth regime, same-grid dyadic comparison, arbitrary common
  measurable deterministic readouts, the almost-sure empirical Poisson count law, and
  the positive full-vector empirical obstruction. Count convergence and vector
  non-convergence are distinct selected results (7.7–7.8b and Appendix F).
- **Palm:** exact arithmetic source–target mass identity; full-target deficit comparison;
  ordinary deletion identity; full-to-retained normalized comparison and its eventual
  bound; stronger retention counts; vanishing target irregularity; and original/stronger
  retained absolute-cumulant obstructions along prime scales. This selects endpoints
  of G.1, G.3–G.5 and G.9. G.2, G.6–G.8 and supporting lemmas remain in the substantive
  development and are not separately registered declarations in this configuration.

This selection does not replace the [full correspondence](MANUSCRIPT_ALIGNMENT.md).
The seven literature inputs remain theorem-level premises. In particular, F.2's
analytic directional Stein solution bounds are required for the actual finite
carrier. Neither a successful build nor an axiom audit proves those inputs.
The metadata's fidelity fields state further interface qualifications.

## Reproducible checks

```sh
python3 scripts/check_current_manuscript.py
python3 -m unittest discover -s scripts -p 'test_check_v3prel_candidates.py' -v
python3 scripts/check_v3prel_candidates.py
lake build ChallengeV3CriticalField SolutionV3CriticalField \
  ChallengeV3Patterns SolutionV3Patterns ChallengeV3Limits SolutionV3Limits \
  ChallengeV3Boundary SolutionV3Boundary ChallengeV3Crossover SolutionV3Crossover \
  ChallengeV3Microscopic SolutionV3Microscopic ChallengeV3Palm SolutionV3Palm
```

Replay each configuration separately with the checked-in runner, for example:

```sh
./palomar/v3prel/verify-comparator.sh comparator/v3prel_palm.json
```

The candidate workflow repeats the source and official metadata checks and runs
all seven Comparator jobs. The runner pins Comparator, the Lean exporter,
NanoDa, landrun, the Palomar submission contract, Lean and Mathlib. The static
check additionally follows the canonical package import closure and rejects
local Challenge imports or shadowed dependency modules.

Source identity checks, compilation, exact statement comparison and the two
kernel checks establish different properties. Local receipts apply only to
their recorded source hashes and commit. They do not assert success of Palomar's
renderer, editorial review or registration. A changed statement, solution or
configuration requires a new qualification; an existing receipt must not be
silently relabelled with the new commit.

The [local qualification record](../palomar/v3prel/qualification/2026-09-20/README.md)
contains the initial seven-family receipt, file identities and transcript excerpts.
It predates the strengthened Limits interface and is not evidence for the changed
statements. The [Limits correction record](../palomar/v3prel/qualification/2026-09-20-limits-probability/README.md)
records its separate replay. The [remaining-dossier qualification](../palomar/v3prel/qualification/2026-09-20-remaining-probability/README.md)
records the 33 declarations in Boundary, Crossover, Microscopic and Palm after
their interface audit. After merging, the candidate workflow automatically
repeats qualification on `main`; use the full SHA of that successful merged commit
for the remaining submissions.

## Relation to earlier registrations

| Issued identifier | Relationship |
|---|---|
| `PALOMAR-2026-08-20-000007` | Scalar antecedent of CriticalField; the selected field and conditioning package is broader. |
| `PALOMAR-2026-08-26-000010` | Earlier transfer result, with its own immutable statement boundary. |
| `PALOMAR-2026-08-26-000012` | Earlier conditioning results, with their own immutable statement boundary. |
| `PALOMAR-2026-08-27-000008` | Partial antecedent of Boundary; the selected relative precision and prefix/envelope package is broader. |

These identifiers retain their original scope and do not automatically identify
any of the seven prepared submissions. Palomar determines novelty and editorial
acceptance. Current-family identifiers confirmed by the author are recorded above.

## Publication sequence

The author submits the prepared entries, adds the issued references to the
paper, and publishes the paper on Zenodo. After receiving the published files
and the exact V3 DOI, update the manuscript package, README and all seven
metadata files, verify the new snapshot, and prepare the planned Palomar version
updates. The [publication plan](V3_PUBLICATION_PLAN.md) records this sequence.
