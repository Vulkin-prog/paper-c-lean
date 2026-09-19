# Paper C — Lean formalization

*Long runs and rare patterns of a random completely multiplicative function*
and its technical companion, by **Brice Pouly**.

The current manuscript is the author-supplied **3PREL8 of 16 September 2026**.
Its [minimal source package](manuscripts/v3prel8/README.md) is archived here.
**Alignment of the formalization with its new results is in progress:**
71 prior numbered statements are preserved, one introductory statement is
extended, and 24 numbered blocks are new. The
[current coverage ledger](docs/FORMALIZATION_COVERAGE_V3PREL8.md) identifies
proved components and remaining obligations. The [new library](PaperCPrel8/README.md)
currently contains 546 audited theorems across 115 modules; all 24
libraries build. The final V3 has not yet been
deposited on the publication platforms.

The toolchain remains **Lean 4.34.0 and Mathlib v4.34.0**. At the validated
pre-extension snapshot, all 23 libraries build, the three axiom audits pass,
and all 80 selected declarations pass local Lean and NanoDa checks across
ten configurations. Those checks do not certify the newly added 3PREL8 results. The
[validation evidence](migration_evidence/lean-4.34.0/README.md) and
[migration review](docs/LEAN_4_34_0_MIGRATION.md) describe the checks and limits.
Earlier qualification records remain tied to their recorded source snapshots.

| Paper and source material | Link |
|---|---|
| Current article | [3PREL8 PDF](manuscripts/v3prel8/paper_c_version_3PREL8_en.pdf) |
| Current technical companion | [3PREL8 PDF](manuscripts/v3prel8/paper_c_version_3PREL8_technical_companion_en.pdf) |
| Editable sources and exact file identities | [Minimal manuscript archive](manuscripts/v3prel8/README.md) |
| Zenodo paper record, all versions | [Concept DOI 10.5281/zenodo.21736676](https://doi.org/10.5281/zenodo.21736676) |
| Cambridge Open Engage, published version 2 | [DOI 10.33774/coe-2026-z3l74-v2](https://doi.org/10.33774/coe-2026-z3l74-v2) |

The publication records above concern earlier published versions. They do
not identify the 3PREL8 snapshot archived here, for which no version-specific
DOI is asserted. The Lean formalization has its own
[Zenodo concept DOI 10.5281/zenodo.21735481](https://doi.org/10.5281/zenodo.21735481),
distinct from the paper record.

## Abstract of the 3PREL8 article

The following is the abstract of the [current manuscript](manuscripts/v3prel8/paper_c_version_3PREL8_en.tex); it describes the paper, not the completed Lean coverage.

Let $f$ be a random completely multiplicative function with independent
symmetric signs at the primes. We study rare constant runs and prescribed
words at logarithmic lengths, despite long-range multiplicative identities.
A uniform weighted two-window square-relation estimate, with critical
bound $O_\varepsilon(N^{5/3+\varepsilon})$, separates exact rational
relations from residual components.

At critical intensity, this estimate gives Poisson comparisons retaining
positions, exact excess lengths and signs. For dictionaries, uniform
bounds under size and overlap conditions are complemented by typical
bounds obtained by averaging the distance after fixing the dictionary.
In a quantitatively controlled regime of diverging intensity, an exact
one-word coupling by largest-odd-prime pivots compares the full signed
run field under prescribed small-prime conditioning. For fixed
admissible window parameters and almost every fixed realization of $f$,
run-start counts in prescribed near-macroscopic windows satisfy an
empirical Poisson law along dyadic scales.

In the exceptionally rare regime, a relative marked comparison separates
the boundary event from bulk occurrences. Conditional on existence, the
first location, sign and overshoot have a two-source lattice law with
scale-dependent weights. The two overshoots use different clocks: prime
rank at the boundary and integer distance in the bulk.

## Formalization scope

The completed baseline below concerns **V3PREL of 7 September 2026**. The
[3PREL8 extension](docs/FORMALIZATION_COVERAGE_V3PREL8.md) is tracked separately.

The [source-to-Lean correspondence](docs/FORMALIZATION_COVERAGE_V3PREL.md)
maps all **59 numbered article results** and, separately, **8 companion
results**, together with the unnumbered conclusions. The development retains
753 mathematical modules and 6,094 named declarations from the audited
Lean 4.32.0 baseline; the migrated audit covers the same 6,094 declarations.
The separate Palomar interfaces select the results listed below.

The proofs remain relative to **seven explicit literature propositions**,
used as ordinary theorem arguments. These propositions are not themselves
proved in Lean, and an axiom audit does not discharge them. The
[literature ledger](PaperCV282/LITERATURE_INPUTS.md) states their content and
use, including the corrected directional Stein input. The Solution files
contain no proof holes; the kernel axiom audit permits only `propext`,
`Classical.choice` and `Quot.sound`.

The [mathematical development guide](PaperCV282/README.md),
[endpoint inventory](PaperCV282/ENDPOINTS.md) and
[revision log](docs/PAPER_V3_REVISION_LOG.md) give the detailed coverage,
limitations and corrections.

## Five Palomar submission families

The five existing configurations retain their first-V3PREL scope and select
**69 declarations** in total. They do not cover all 3PREL8 additions. This selection
is distinct from the full paper-to-Lean coverage ledger. Each family has its
own statement boundary, sources and metadata.

| Family | Selected declarations | Comparator configuration | Metadata |
|---|---:|---|---|
| Critical Poisson field and small-prime conditioning | 13 | [critical_field](comparator/v3prel_critical_field.json) | [formalization.yaml](palomar/v3prel/critical_field/formalization.yaml) |
| Word dictionaries, exact marks and compound clusters | 9 | [patterns](comparator/v3prel_patterns.json) | [formalization.yaml](palomar/v3prel/patterns/formalization.yaml) |
| Threshold staircase and Poisson–Gaussian limits | 29 | [limits](comparator/v3prel_limits.json) | [formalization.yaml](palomar/v3prel/limits/formalization.yaml) |
| Microscopic boundary, prefixes and longest runs | 7 | [boundary](comparator/v3prel_boundary.json) | [formalization.yaml](palomar/v3prel/boundary/formalization.yaml) |
| Microscopic–bulk crossover | 11 | [crossover](comparator/v3prel_crossover.json) | [formalization.yaml](palomar/v3prel/crossover/formalization.yaml) |

The [submission guide](docs/PALOMAR_V3PREL.md) explains the exact selection
and its relationship to the four historical registrations. Links to issued
V3PREL registry records will be added when available.

[Candidate-side replays](https://github.com/Vulkin-prog/paper-c-lean/actions/runs/34157635210)
accepted all 69 selected declarations with Comparator, Lean and NanoDa for
source commit [`32ecdbc0`](https://github.com/Vulkin-prog/paper-c-lean/commit/32ecdbc0eace9cd1d47dccbbd7ccaaaf8f6d459e),
preserved by the merge into `main`. Those results concern that source
snapshot. Palomar performs its own verification and editorial review for
each submitted commit; a repository replay is not a registry entry.

The [V3 publication plan](docs/V3_PUBLICATION_PLAN.md) records the remaining
source, bibliography and registration updates for the final paper and the
next versions of these five entries.

## Build and check

The pins are **Lean 4.34.0 and Mathlib v4.34.0**. The complete local build
and audits have passed. With these exact dependencies installed, the
following commands check the mathematical overlays from the repository root:

```sh
lake build PaperCV11 PaperCV282
python3 scripts/check_v3prel_sources.py
python3 scripts/check_v282_audit.py --check-source
```

The [migration guide](docs/LEAN_4_34_0_MIGRATION.md#reproducing-local-validation) lists
all 23 library targets and the three kernel audits: a default `lake build`
covers only `PaperC`. The
[Palomar guide](docs/PALOMAR_V3PREL.md#reproducible-qualification) describes
the separate candidate replay. Source identity checks, proof builds,
axiom audits and registry verification have distinct roles.

## Citation, licence and credits

Cite the exact published paper version used, together with the formalization
commit or registered Palomar version where relevant. The concept DOIs above
identify the respective paper and software version series.

The Lean project is released under the [Apache-2.0 licence](LICENSE).
The manuscript sources retain their [own licence and production declarations](manuscripts/v3prel/source/declarations.tex).
Human authorship and responsibility, agent-assisted development and the
completed review are recorded in the formalization metadata. Agent review
is not human peer review.

## Historical development

The [archived README](docs/history/README_before_v3_refresh.md) preserves the
v0.9 development, earlier qualification procedures and their dated claims.
The [historical Palomar table](palomar/README.md) and
[current relationship table](docs/PALOMAR_V3PREL.md#relation-to-the-historical-registrations)
retain the four earlier identifiers and their relation to the new families.
