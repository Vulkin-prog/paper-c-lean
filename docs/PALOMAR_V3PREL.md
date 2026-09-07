# Five new Palomar candidates for V3PREL

The maintainer selected **five new registrations**. No existing Palomar
identifier is reused or assigned to these files. The candidates select
groups of declarations from the broader
[V3PREL source mapping](FORMALIZATION_COVERAGE_V3PREL.md).

| New candidate | Selected results | Configuration | Metadata |
|---|---|---|---|
| Critical Poisson field and conditional transfers | 13: actual coefficients, lattice/source count, masked conditional kernel, conditional means, hard/soft transfers, spatial and uniform quenched limits, stable small-prime record, diffuse limit | [critical_field](../comparator/v3prel_critical_field.json) | [formalization](../palomar/v3prel/critical_field/formalization.yaml) |
| Dictionaries, exact marks and compound clusters | 9: word overlap, growing dictionaries, exact signed/unsigned fields, category partition, whole aggregate path, geometric Poisson configuration, compound weight and generating function, actual constant windows | [patterns](../comparator/v3prel_patterns.json) | [formalization](../palomar/v3prel/patterns/formalization.yaml) |
| Threshold staircase and Poisson–Gaussian bridge | 29: actual joint limit, covariance and AR(1), central/local/moderate estimates and transfers, D.1 and D.4 including the whole integer process and conditioned upper-half point laws | [limits](../comparator/v3prel_limits.json) | [formalization](../palomar/v3prel/limits/formalization.yaml) |
| Microscopic boundary, prefixes and longest runs | 7: exact boundary model, the quantitative relative error with exponent 1/256, boundary uniqueness, mesoscopic exclusion, contained-prefix control, critical prefix law and almost-sure envelopes | [boundary](../comparator/v3prel_boundary.json) | [formalization](../palomar/v3prel/boundary/formalization.yaml) |
| Microscopic–bulk crossover | 11: affine boundary mass, complete moving marked mixture, first contained exceedance locations and signs in the three phases, and the final conditioned affine clock and projections | [crossover](../comparator/v3prel_crossover.json) | [formalization](../palomar/v3prel/crossover/formalization.yaml) |

The 69 selected declarations do not replace the full coverage ledger. Each
metadata file states its precise fidelity boundary, including clauses proved
in the development but not separately selected for Comparator. In particular,
the Patterns entry does not independently select the literal finite C.1
ledger or every conditional signed refinement. The Limits entry presents
D.4 through its actual whole process, restrictions and complete compact-test
Laplace functional; a separate vague-topology convergence declaration is
not selected. Its constant auxiliary sign coordinate has no probabilistic
sign claim.

## Relation to the historical registrations

The historical files, metadata and qualification workflow remain intact.

| Historical identifier | Earlier content | Relation to the new candidates |
|---|---|---|
| `PALOMAR-2026-08-20-000007` | v0.9 Theorem 1.1 | Scalar antecedent of CriticalField; the new entry additionally selects the conditional field, process and uniform results above. |
| `PALOMAR-2026-08-26-000010` | v0.9 Theorem 1.2 | Historical transfer antecedent; not represented as a new identifier or copied qualification. |
| `PALOMAR-2026-08-26-000012` | v0.9 Theorem 1.4 and Corollary 11.3 | Historical conditioning results; the new five entries have their own statement boundaries. |
| `PALOMAR-2026-08-27-000008` | v0.9 Theorem 16.2 and Corollary 16.4 | Partial antecedent of Boundary; the new entry selects the stronger microscopic precision and prefix/envelope package. |

Patterns, Limits and Crossover add distinct mathematical families. This
explains the proposed grouping and overlap; Palomar retains authority over
its novelty and source-fidelity decisions.

## Statement and proof boundaries

Every candidate has one autonomous `ChallengeV3*.lean`, one separately proved
`SolutionV3*.lean`, and one configuration selecting multiple declarations.
Challenges import Mathlib only, with no local repository module. Their
intentional proof placeholders are exactly the selected results. Solutions
identify the independently defined objects with the actual source model by
proved bridges and use the substantive repository proofs.

All five retain Lean **4.32.0** and mathlib **v4.32.0**, revision
`81a5d257c8e410db227a6665ed08f64fea08e997`. Literature propositions are
ordinary visible theorem arguments, never new Lean axioms. The
[literature ledger](../PaperCV282/LITERATURE_INPUTS.md) documents seven such
propositions across the development; an individual candidate uses only its
required subset. The old directional Euclidean premise was false and is
replaced by the constant entrywise and weighted quadratic estimates of
V3PREL C.3. A Lean counterexample documents why the replacement matters.

Original V3PREL PDFs and editable sources are preserved byte for byte in
[the manuscript archive](../manuscripts/v3prel/README.md). Baseline theorem
names remain in `PaperCV282`; the current source mapping records the changed
numbering. No old Palomar evidence is presented as evidence for these files.

## Reproducible qualification

The dedicated [V3PREL workflow](../.github/workflows/v3prel-qualification.yml)
checks the source archive and each metadata/configuration pair, then replays
the selected declarations through pinned Comparator and NanoDa tools. The
[candidate guard](../scripts/check_v3prel_candidates.py) and
[replay script](../palomar/v3prel/verify-comparator.sh) record the exact
configuration and tool identities. Source guards, a Lean build and a local
axiom audit are useful separate checks; none alone establishes Comparator
agreement or an external Palomar registration.

Submission must reference the immutable commit actually checked and its
corresponding configuration. Results for an earlier commit, the historical
v0.9 matrix, or a smaller selection do not qualify a changed V3PREL candidate.
The workflow's outcome is separate evidence: this document makes no claim
that a particular run has passed or that a new record has been issued.
