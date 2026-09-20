# Palomar review follow-up: D.4 upper-point laws

## Correction

The Limits automated review dated 20 September 2026, 13:34:48 UTC, accepted
mechanical verification but requested explicit guarantees that the complete
and conditional upper-point-law expressions are genuine probability laws.
The previous compared assertions exposed only equalities of measures.

The correction strengthens the same two selected declarations, in both
`ChallengeV3Limits.lean` and `SolutionV3Limits.lean`:

- `paper_c_v3_limits_d4_entire_upper_point_law` proves measurability of the
  source configuration and Poisson target map, probability normalization of
  both measures, and their equality.
- `paper_c_v3_limits_d4_conditional_upper_point_law` proves strictly positive
  probability of every finite conditioning count, measurability of the target
  map, almost-everywhere measurability of the source map under conditioning,
  probability normalization of both measures, and their equality.

`IsProbabilityMeasure` includes the assertion that the measure of the whole
space is one. These properties are conclusions proved from the existing
construction, not additional assumptions. The count positivity follows from
the proved Poisson count law and strictly positive intensity. The two auxiliary
measurability bridges use the Borel space of finite point measures already
specified by the public interface.

The selection remains 29 Limits declarations and 89 declarations overall.
No manuscript statement, literature premise, source construction, dependency
pin or other family interface changes. This repairs the submission interface;
it does not require a mathematical correction to the paper.

Technical detail: at the pinned Mathlib commit, `Measure.map` falls back to an
arbitrary Dirac mass for a nonzero measure and a map that is not almost everywhere
measurable (and to zero for a zero source). Its introductory file comment still
mentions zero. Thus total mass one alone would not rule out the actual fallback;
explicit measurability is essential and is now part of the compared conclusions.
See the pinned [definition](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/MeasureTheory/Measure/Map.lean).

## Qualification and submission

The [correction qualification record](../palomar/v3prel/qualification/2026-09-20-limits-probability/README.md)
identifies the exact corrected sources, Comparator replay and Lean/NanoDa checks.
The earlier seven-family receipt is preserved and applies only to its recorded
sources. Mechanical qualification does not predict the new automated review.

The rejected Limits attempt is not a registration. Resubmit the qualified
merged correction as a new submission, leaving the existing identifier blank.
The first two issued registrations are recorded separately in the
[submission guide](PALOMAR_SUBMISSIONS.md#current-registration-status).

## Mathlib-cache warning

The warning is separate from the D.4 review objection. The repository pins
Lean 4.34.0 and Mathlib v4.34.0 (commit
`5ed2965256430c3649e86755f9576b54eca72435`). The
[successful seven-family main workflow](https://github.com/Vulkin-prog/paper-c-lean/actions/runs/35497081247)
shows **8,906 of 8,908 cache archives downloaded**, followed by two misses in
the fallback cache. The local cache transcript gives the same counts.

Using the pinned cache client's hash computation against the local archive
store identified the missing archives:

| Module | Archive |
|---|---|
| `Mathlib` (umbrella import) | `d72c1206c21e9732.ltar` |
| `Mathlib.Probability.Kernel.Invariance` | `6a37890db73db848.ltar` |

Palomar's pinned [cache availability check](https://github.com/PalomarRegistry/PalomarSubmission/blob/3561d237dcc4b28482558ad28a64d767d7cc8615/scripts/verify_submission.py)
returns false whenever the transcript says some files were missing, even if
almost all archives downloaded successfully. This explains the broad warning
in the observed run; it does not establish that users must rebuild all Mathlib.
Missing modules can require local compilation if imported. No Lean or Mathlib
migration is needed to fix the D.4 statements. Cache availability can change
upstream, so these counts describe the checked runs, not a permanent guarantee.
