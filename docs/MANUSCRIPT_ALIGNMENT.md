# Current manuscript and Lean correspondence

The [article and companion](../manuscripts/paper-c/README.md) are aligned with the
existing Lean development, **relative to its explicit literature inputs and
documented proof substitutions**. This is the published Version 3 of
21 September 2026, DOI [10.5281/zenodo.22872154](https://doi.org/10.5281/zenodo.22872154).
No Lean theorem, proof or hypothesis has changed for the publication update.

Compared with the manuscript at the latest registered commit,
`409779f46c0599edcd9ae1f973dd931b1d0a1cea`, all **96 numbered statements are
unchanged** after whitespace/comment normalization. Of 90 proof blocks, 89
are textually unchanged; the remaining edit replaces “whose proof above is
unchanged” with “proved independently above” without changing the argument.
The other edits concern publication metadata, cross-document references and
the new formalization section, including all seven Palomar identifiers.

The correspondence also preserves the earlier mathematical review against its
fixed baseline: 95 of 96 statements were unchanged, G.2 made three ambient
hypotheses explicit, and 14 of 90 proof blocks had been revised. The table below
records that review. These baseline counts must not be mistaken for changes
introduced by the published edition. Prose outside numbered blocks is included
in the review; the counts alone do not establish mathematical correspondence.

[MANUSCRIPT_ALIGNMENT.json](MANUSCRIPT_ALIGNMENT.json) binds every current TeX
file and statement to its exact bytes and to the existing
[numbered correspondence](FORMALIZATION_COVERAGE_V3PREL8.md) and
[unnumbered review](UNNUMBERED_REVIEW_V3PREL8.md). Statement labels are the joining
keys; old page numbers must not be used as current locators. The 337 existing
label keys are preserved; the publication adds `sec:formalization`.

## Review of mathematical changes

| Passage | Current manuscript and existing Lean proof |
|---|---|
| 5.4, affine dictionaries | Inclusion probabilities transfer nonnegative error bounds; they do not equate the average total-variation distances of different dictionary ensembles. The matrix/offset averaging route is already represented by `AffineDictionaryMatrix`, `AffineDictionaryConsequences` and the numbered correspondence. |
| 6.2 and companion C.5 | Monotonicity proves the crossing, strict improvement and constrained optimum. The common larger truncation controls both tails. `InformationSaddle`, `InformationSaddleBudget`, `InformationSaddleLimit` and `PrescribedInformationPaper` already use these routes. |
| 7.7 and F.1 | Ambient and retained intensities are distinguished; constant changes are absorbed by the information margin. The cutoff rounding and conditional costs match `MicroscopicNormalization`, `MicroscopicInformationCutoff` and the finite comparison ledger. |
| F.2 | The coordinatewise minimum gives the full lattice-distance bound for arbitrary configurations. `PalmStein` proves the finite comparison from the existing analytic Stein input. The printed semigroup construction remains outside the formal proof. |
| F.3–F.6 | Positive-integer counting, odd-valuation pivots, the tangent inequality in the saddle parameter, the next-slice factor and translated congruence counts agree with the existing Rankin, saddle, reciprocal-pivot and footprint components. No broader asymptotic domain is introduced. |
| F.7 | Only the prescribed word's pivots are forced, unused maximal-support pivots remain fixed, and the cylinder includes the conditioning information. The directed baseline is retained before enlarging the nonnegative excess. These are the existing full-law forcing and directed-cost conventions. |
| 7.7a | The manuscript now uses monotonicity and the height-ratio bound, matching `SaddleScaleMonotonicity` and `DyadicRestriction`; an inverse-function derivative estimate is no longer needed. |
| 7.8a | An upper covariance bound suffices. The count of origins and eventual comparison of its denominator with the ambient number of starts match the existing empirical proof. |
| G.2 | The added assumptions are `n ≥ 1`, `Q ≤ n`, `Y > Q`. They already occur as `hn`, `hQn`, `hQY` in `RoughKernelCloudBound.regularity_probability_le` and `strong_good_probability_le`. `RoughKernelCRT` charges a factor three only for nonempty CRT blocks. The weaker vertex-bound interface remains sufficient for the individual allocation estimate. |
| G.3–G.6 | Multiplicities and the empty configuration are retained. The no-atom/no-start equivalence is almost sure. Zero void probabilities use the extended logarithmic convention; reference-centered singleton cumulants remain `EX-p`. These agree with the recorded regular-cloud, Palm, `TiltedVoidIntegral` and `CumulantConventions` proofs. |
| G.9 | The witness uses the cylinder up to `M+Q`, with terminal-index omissions counted. This matches the existing arithmetic witness and retained higher-cumulant divergence proof. |

The seven propositions in the [literature register](../PaperCV282/LITERATURE_INPUTS.md)
remain assumptions. No stronger claim about them follows from an axiom audit.
Optional stronger bounds from the working notes have not become new manuscript
claims. The written scalar-tail argument remains independent of the microscopic
comparison; the Palm consequences are not used to prove that comparison.

## Validation and registration boundary

`python3 scripts/check_current_manuscript.py` verifies all 29 delivered files,
the local TeX inputs, the complete numbered comparison, the changed proof blocks,
and the source identities recorded in the existing final Lean receipt. It also
checks the published version DOI, fixed PDF identities and seven Palomar
identifiers. This is a source-alignment check, not a new Lean build or a replay
of Comparator/NanoDa. Prior build and axiom-audit evidence remains tied to its
original snapshot.

The published PDFs and source archive were downloaded from the Zenodo record
and checked against its checksums. The PDFs have not been regenerated during
integration: Biber is not available in the current environment. Their byte
identity is checked; no independent PDF reproducibility claim is made.

All seven Palomar version 1 registrations are recorded in the
[submission guide](PALOMAR_SUBMISSIONS.md#current-registration-status) and the
published article. The version 2 metadata now identifies the published edition
and retains the same 89 selected Lean declarations. The publication commit
must pass its own qualification before submission under the existing identifiers;
preparing metadata does not constitute a version 2 registration.
