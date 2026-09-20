# Pre-submission audit of the four remaining dossiers

This review follows the automated rejection of the Limits upper-point laws.
It examines the 33 selected declarations in Boundary, Crossover, Microscopic
and Palm, their reachable standalone definitions, metadata, source bridges and
corresponding current article/companion passages. It identifies interface
risks and strengthens their public guarantees; it does not predict Palomar's
editorial decision or replace human mathematical peer review.

## Findings and changes

| Dossier | Exposed risk | Proved guarantee in the corrected comparison interface |
|---|---|---|
| Boundary (7) | Mesoscopic `Measure.map` expressions and conditioned measures lacked exposed normalization; prefix TV uses a countable real series. | `v3_boundary_exact` now includes `Boundary.ProbabilityLaws`: measurable positive-mass border/microscopic events, probability conditional laws, measurable positive-mass enlarged events, measurable records and probability pushforwards for every cutoff, and measurable prefix counts whose masses have sum one. |
| Crossover (11) | Marked mixtures and both spatial laws used raw pushforwards under a non-vacancy conditioning; `Weakly` previously stated test-integral convergence only. | All ten asymptotic endpoints include eventual `Crossover.ProbabilityLaws`: measurable positive-mass conditioning, measurable actual record/first-start maps, and probability normalization of source, target and both location laws. `Weakly` additionally includes eventual source and target normalization. |
| Microscopic (6) | Complete-field flattening and arbitrary readouts needed explicit probability guarantees; the source uses an epsilon selection. | The Challenge proves countable flattening measurability and a target probability instance. The selected coefficient theorem proves source measurability and normalization alongside the exact coefficients. The selected common-readout assertion proves composite measurability and probability normalization of both transported laws. |
| Palm (9) | Nested Palm conditioning could appear to condition on a null event; standalone source selection and countable deficit formulas needed explicit guarantees. | The selected mass identity proves exact source coefficients, measurable source/presence event, target and conditional probability laws, and strictly positive presence mass on regular configurations. The full-deficit comparison proves `HasSum ... 1` for both mass functions. |

All guarantees are **proved conclusions**, or proved instances in the standalone
Challenge, not new premises. Declaration names and counts remain unchanged:
89 selected declarations overall. The first two registered family interfaces,
the already corrected Limits interface, the mathematical development, paper files,
Lean 4.34.0 and Mathlib pin are unchanged by this follow-up.

## Checks beyond normalization

- **Actual source objects:** finite-prefix counts include the border and contained
  starts; microscopic coefficients retain exact excesses and both signs. Palm
  now exposes the same coefficient identity independently of the microscopic
  dossier. The epsilon choice cannot silently supply unrelated coefficients.
- **Correct conditioning:** Boundary events contain the positive border event.
  Crossover positivity holds eventually because lengths are eventually contained;
  affine compatibility supplies positive border-intersection mass. The Palm
  regular-plant argument proves positive presence under the already positive
  small-prime trace. No null-event normalization is assumed.
- **Nontrivial variation distances:** countable sources are measurable on genuine
  probability spaces, and their countable targets are probability measures.
  The resulting singleton masses are summable, excluding the nonsummable-series
  fallback of a real `tsum`. Boundary prefix laws and Palm source/target masses
  now explicitly expose `HasSum ... 1`. Bounded probability masses also bound the
  sets used in the measurable-set supremum definition of total variation.
- **Phase limits:** limiting delta, uniform and mixture laws have total mass one.
  Finite and infinite phase claims concern actual normalized position laws at
  sufficiently large indices. Initial values with a run longer than the prefix
  are not incorrectly asserted to have positive non-vacancy probability.
- **Quantifiers and clocks:** empirical Poisson convergence fixes alpha and tau
  before choosing the almost-sure set, uses the literal dyadic scales and counts
  starts, not a whole-vector empirical Poisson limit. The vector obstruction is
  retained. Crossover border overshoot uses prime rank, bulk overshoot uses
  integer excess, and future neutrality is required only for the full affine
  clock. The added guards do not add neutrality to location or sign claims.
- **Palm scope:** positive normalizers use `L >= 1`; regular configurations
  retain multiplicities and the empty configuration. The normalized deficit
  bound does not assert that target regularity alone proves source approximation.
  The G.9 cumulant obstruction uses finite centered moments and all distinct-site
  category transversals, and asserts an eventual lower bound on prime scales.
- **Literature inputs:** the displayed Stein, PNT and arithmetic propositions
  remain explicit. In particular, F.2's analytic Stein solution is still a premise.
  The manuscript correspondence and metadata disclose this boundary; none of
  these edits purports to formalize those external inputs.

No additional mismatch requiring a paper correction was identified in this
focused review. The changes address how existing results are presented for
comparison. The source comparisons use the current Section 7, the empirical
and dyadic subsections, and companion Appendices E–G; the existing
[manuscript correspondence](MANUSCRIPT_ALIGNMENT.md) gives the detailed mapping.

## Validation and remaining decision

The [qualification record](../palomar/v3prel/qualification/2026-09-20-remaining-probability/README.md)
binds the strengthened interfaces to exact file hashes and Comparator/Lean/NanoDa
results. The earlier receipts remain unchanged and are not relabelled as checks
of the new source. CI repeats all seven configurations on the PR and after merge.

Submit the corrected, successfully qualified merged commit for the remaining
families. The normal automated review is still required and may raise another
issue; there is no blanket assurance of acceptance. The independently observed
partial Mathlib-cache warning is described in the [Limits follow-up](PALOMAR_REVIEW_FOLLOWUP.md).
