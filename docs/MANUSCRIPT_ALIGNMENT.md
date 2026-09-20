# Current manuscript and Lean correspondence

The [article and companion](../manuscripts/paper-c/README.md) are aligned with the
existing Lean development, **relative to its explicit literature inputs and
documented proof substitutions**. The supplied manuscript is dated 20 September
2026 (3PREL9). No Lean theorem or hypothesis has been changed for this integration.

The independent source comparison finds 96 numbered statement blocks: 95 are
unchanged after whitespace/comment normalization, and G.2 makes three ambient
hypotheses explicit. Of 90 proof blocks, 14 have changed. The source comparison
also covers prose outside these blocks; the count alone is not a proof review.

[MANUSCRIPT_ALIGNMENT.json](MANUSCRIPT_ALIGNMENT.json) binds every current TeX
file and statement to its exact bytes and to the existing
[numbered correspondence](FORMALIZATION_COVERAGE_V3PREL8.md) and
[unnumbered review](UNNUMBERED_REVIEW_V3PREL8.md). Statement labels are the joining
keys; old page numbers must not be used as current locators. The 337 numerical
labels retain their keys in the source comparison.

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

## Validation and publication boundary

`python3 scripts/check_current_manuscript.py` verifies all 28 delivered files,
the local TeX inputs, the complete numbered comparison, the changed proof blocks,
and the source identities recorded in the existing final Lean receipt. This is
a source-alignment check, not a new Lean build or a replay of Comparator/NanoDa.
The prior build and axiom-audit evidence remains tied to its original snapshot.

The supplied PDFs have not been regenerated during integration: Biber is not
available in the current environment. Their byte identity with the author's
archive is checked; no independent PDF reproducibility claim is made.

The Palomar dossiers still need their expanded statement selections and fresh
qualification. After the author's first submissions, the manuscript will receive
the Palomar references. The published PDFs, sources and Zenodo version DOI will
then replace this manuscript package, and the submission metadata can reference
that published edition. No future DOI or Palomar identifier is preassigned here.
