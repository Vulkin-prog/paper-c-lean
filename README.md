# Paper C — Lean formalization

*Long runs and rare patterns of a random completely multiplicative function*
and its technical companion, by **Brice Pouly**.

The current development follows the author-supplied **V3PREL of 7 September
2026**. The final V3 has not yet been deposited on the publication platforms.

Local validation has passed with **Lean 4.33.1 and Mathlib v4.33.1**:
all 23 libraries build, the three kernel audits pass, and all 80 selected
interfaces pass the strict local comparison. Official Comparator/NanoDa
qualification for this migrated snapshot is not established. See the
[migration results and limits](docs/LEAN_4_33_1_MIGRATION.md) and the
[validation receipt](migration_evidence/lean-4.33.1/validation.json).
Earlier qualification records remain tied to their Lean 4.32.0 snapshots.

| Paper and source material | Link |
|---|---|
| Article used for the formalization | [V3PREL PDF](manuscripts/v3prel/paper_C_version_3PREL_en.pdf) |
| Technical companion used for the formalization | [V3PREL PDF](manuscripts/v3prel/paper_C_version_3PREL_technical_companion_en.pdf) |
| Editable sources and exact file identities | [Manuscript archive](manuscripts/v3prel/README.md) |
| Zenodo paper record, all versions | [Concept DOI 10.5281/zenodo.21736676](https://doi.org/10.5281/zenodo.21736676) |
| Cambridge Open Engage, published version 2 | [DOI 10.33774/coe-2026-z3l74-v2](https://doi.org/10.33774/coe-2026-z3l74-v2) |

The publication records above concern earlier published versions. They do
not identify the V3PREL snapshot archived here, for which no version-specific
DOI is asserted. The Lean formalization has its own
[Zenodo concept DOI 10.5281/zenodo.21735481](https://doi.org/10.5281/zenodo.21735481),
distinct from the paper record.

## Abstract of the V3PREL article

The following is the abstract of the [supplied manuscript](manuscripts/v3prel/source/paper_C_version_3PREL_en.tex).
The formalization scope is described separately below.

Let $f$ be a random completely multiplicative function with independent
symmetric signs at the primes. At logarithmic run lengths, we approximate
the full field of positions, excess lengths and signs by independent
Poisson coordinates, despite exact long-range multiplicative identities.
More generally, a deterministic dictionary of $m\le N^{1/2-\eta}$
prescribed words at length $B=\log_2(Nm)+O(1)$ is asymptotically equivalent in total variation to the rare-word
field of independent fair signs, when its weighted
overlap tends to zero. Most dictionaries satisfy this condition; explicit
marker families have no overlaps.

The arithmetic input is a uniform two-window square-relation estimate
with critical bound $O_\varepsilon(N^{5/3+\varepsilon})$. A capped form exploits the mutual exclusivity of distinct words at one site
and allows the dictionary to grow.
The proof uses rational relations, private prime coordinates and
bounded-height Runge--Pell arguments. Conditioning on small primes then
supplies an exact dependency graph.

For the longest run in $[1,M]$, we obtain the lattice extreme law and
asymmetric almost-sure envelopes. Exceptionally long runs arise either
from a boundary event of exact mass $2^{-\pi(L)}$ or from a bulk field
of intensity $M2^{-L}$. A relative marked comparison gives, conditional
on existence, a lattice mixture for the first location, sign and
overshoot with moving source weights. The two source branches have geometric overshoots
in different clocks: prime rank at the boundary and integer distance
in the bulk.

## Formalization scope

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

The five configurations select **69 declarations** in total. This selection
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

The pins are **Lean 4.33.1 and Mathlib v4.33.1**. The complete local build
and audits have passed. With these exact dependencies installed, the
following commands check the mathematical overlays from the repository root:

```sh
lake build PaperCV11 PaperCV282
python3 scripts/check_v3prel_sources.py
python3 scripts/check_v282_audit.py --check-source
```

The [migration guide](docs/LEAN_4_33_1_MIGRATION.md#reproducing-local-validation) lists
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
