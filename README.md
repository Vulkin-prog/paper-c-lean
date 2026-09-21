# Paper C — Lean formalization

*Long runs and rare patterns of a random completely multiplicative function*
and its technical companion, by [Brice Pouly](https://orcid.org/0009-0008-8491-2467).

This repository contains the mathematical development, the article and companion
with their editable sources, and seven Palomar submission interfaces. The
[source-to-Lean correspondence](docs/MANUSCRIPT_ALIGNMENT.md) records the current
manuscript's results and the precise scope of their formalization.

| Paper and source material | Link |
|---|---|
| Article | [PDF](manuscripts/paper-c/paper_c_version_3PREL9_en.pdf) |
| Technical companion | [PDF](manuscripts/paper-c/paper_c_version_3PREL9_technical_companion_en.pdf) |
| Editable sources and file identities | [Manuscript package](manuscripts/paper-c/README.md) |
| Zenodo paper record, all versions | [10.5281/zenodo.21736676](https://doi.org/10.5281/zenodo.21736676) |
| Cambridge Open Engage paper record | [10.33774/coe-2026-z3l74-v2](https://doi.org/10.33774/coe-2026-z3l74-v2) |
| Formalization record, all versions | [10.5281/zenodo.21735481](https://doi.org/10.5281/zenodo.21735481) |

The repository currently includes the author's manuscript of 20 September 2026.
The publication links identify the available paper records; they do not identify
this manuscript as the published V3. The published files, version-specific paper
DOI will be added when available. The first six Palomar identifiers, confirmed by
the author, are recorded in the
[submission guide](docs/PALOMAR_SUBMISSIONS.md#current-registration-status).

## Abstract

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


## Mathematical scope

The development covers critical Poisson fields and conditional transfers;
word dictionaries, exact marks and compound clusters; threshold staircases
and Gaussian limits; boundary and prefix laws; the microscopic–bulk crossover;
and the microscopic, empirical and Palm refinements. The
[coverage correspondence](docs/MANUSCRIPT_ALIGNMENT.md) links the numbered
statements to Lean and records proof substitutions and qualifications.

The proofs are relative to **seven explicit literature propositions**: scalar
and multivariate Poisson Stein bounds, the finite AGG process bound, the prime
number theorem remainder, and the arithmetic inputs of Laishram–Shorey,
Shorey, and Nicolas–Robin. They are ordinary theorem arguments, not proved
literature results. In particular, the analytic solution premise of **F.2**
remains explicit. The [input ledger](PaperCV282/LITERATURE_INPUTS.md) gives the
statements and references. Kernel axiom checks do not discharge these hypotheses.

Solution proofs contain no placeholders. The permitted kernel axioms are
`propext`, `Classical.choice` and `Quot.sound`. Intentional placeholders in the
standalone Challenges specify the obligations checked by Comparator.

## Palomar submission families

The seven configurations select **89 declarations**. This is the registration
selection, not a count of all results proved in the repository.

| Family | Declarations | Configuration | Metadata |
|---|---:|---|---|
| Critical fields and information-adapted conditioning | 16 | [critical_field](comparator/v3prel_critical_field.json) | [metadata](palomar/v3prel/critical_field/formalization.yaml) |
| Typical dictionaries, exact marks and compound clusters | 11 | [patterns](comparator/v3prel_patterns.json) | [metadata](palomar/v3prel/patterns/formalization.yaml) |
| Threshold staircase and Poisson–Gaussian bridge | 29 | [limits](comparator/v3prel_limits.json) | [metadata](palomar/v3prel/limits/formalization.yaml) |
| Boundary, prefixes and longest runs | 7 | [boundary](comparator/v3prel_boundary.json) | [metadata](palomar/v3prel/boundary/formalization.yaml) |
| Microscopic–bulk crossover | 11 | [crossover](comparator/v3prel_crossover.json) | [metadata](palomar/v3prel/crossover/formalization.yaml) |
| Microscopic signed fields and empirical laws | 6 | [microscopic](comparator/v3prel_microscopic.json) | [metadata](palomar/v3prel/microscopic/formalization.yaml) |
| Regular configurations, Palm deficits and cumulants | 9 | [palm](comparator/v3prel_palm.json) | [metadata](palomar/v3prel/palm/formalization.yaml) |

The [submission guide](docs/PALOMAR_SUBMISSIONS.md) records the exact scope,
submission fields and validation procedure. Each selected configuration has its
own metadata, including structured author and ORCID fields. Local verification
is distinct from Palomar's verification, rendering and editorial decision.

## Build and verification

Use the pinned **Lean 4.34.0 and Mathlib v4.34.0** dependencies:

```sh
lake build PaperCV11 PaperCV282 PaperCPrel8
python3 scripts/check_current_manuscript.py
python3 scripts/check_v3prel_candidates.py
```

A default `lake build` builds only `PaperC`. To validate a submission, build its
Challenge and Solution and replay the selected declarations through both kernels:

```sh
lake build ChallengeV3Microscopic SolutionV3Microscopic
./palomar/v3prel/verify-comparator.sh comparator/v3prel_microscopic.json
```

Repeat the replay for each configuration in the table. The
[submission guide](docs/PALOMAR_SUBMISSIONS.md) distinguishes source checks,
compilation, statement comparison and the Lean/NanoDa checks.

## Citation, licence and credits

Cite the published paper version together with the exact formalization commit
or Palomar record used. Paper and software DOIs are distinct. The
[publication plan](docs/V3_PUBLICATION_PLAN.md) describes the pending updates.

The Lean project uses the [Apache-2.0 licence](LICENSE). The manuscript retains
its [own licence and declarations](manuscripts/paper-c/declarations.tex).
The submission metadata records human authorship and responsibility and
agent-assisted development. Agent review is not human peer review.
