# 3PREL8 — review of unnumbered passages and proof substitutions

The numbered ledger has 96 entries. This review additionally checks changed
proofs, examples and unnumbered consequences, without treating unchanged
statement text as a certificate for all surrounding prose.

The [source-bound inventory](UNNUMBERED_REVIEW_V3PREL8.json) retains all 32
previous unnumbered groups (including D.1/D.4), records every TeX file hash and
changed span, and gives the following current dispositions. The formalization
uses the same explicit literature inputs as the baseline. In particular,
**the analytic Stein solution in F.2 remains an input**. No claim of a wholly
self-contained proof of all cited analysis, or new Palomar qualification, is made.

## R01 — arithmetic exposition and cofactor counting

The added cofactor decomposition and lattice-step count expose the existing proof of the two-thirds energy bound. The partition and terminal-container paragraphs explain existing branches; they do not strengthen the numbered conclusions.

Proof references: [card_kernelQuotients_le_sqrt_ratio](../PaperCV282/ShiftedKernelQuotients.lean), [card_dyadic_boxSolutions_le](../PaperCV282/ShiftedKernelBoxCount.lean), [card_shiftedKernelValues_le_two_thirds_eventually](../PaperCV282/ShiftedKernelPairCount.lean).

## R02 — typical and affine dictionaries

Dictionary selection remains independent of prime signs. Local collisions, full-value separated rank, both deletion costs, the order of supremum and averaging, deterministic masks, mean and in-selection-probability limits are represented in the linked numbered components. No almost-sure selection across scales is claimed.

Proof references: [mean_rate_eventually](../PaperCPrel8/TypicalDictionaryTheorem.lean), [iid_in_selection_probability](../PaperCPrel8/TypicalDictionaryConvergence.lean), [averaged_statistic_le](../PaperCPrel8/TypicalDictionaryConsequences.lean), [matrix_average_eq](../PaperCPrel8/AffineDictionaryMatrix.lean), [description_bits_le](../PaperCPrel8/AffineDictionaryMatrix.lean).

## R03 — information crossing and prescribed floor

Strict monotonicity proves the unique crossing, strict improvement and constrained maximum. The displayed implicit derivative of w_N(I) is not separately formalized and is not used by the Lean argument. A larger certified auxiliary truncation is used where appropriate; source and target tails are both controlled. The final source-facing field, measurability condition and exponent are preserved.

Proof references: [existsUnique_crossing](../PaperCPrel8/InformationSaddle.lean), [budget_strict_improvement](../PaperCPrel8/InformationSaddleBudget.lean), [constrained_maximum](../PaperCPrel8/InformationSaddleBudget.lean), [information_budget_limit](../PaperCPrel8/InformationSaddleLimit.lean), [optimized_floor_field](../PaperCPrel8/PrescribedInformationPaper.lean).

## R04 — microscopic source and independent inputs

The actual signed field and full small-prime event are retained. The shifted scalar tail is independent of this comparison. F.2 uses the baseline DirectionalSolutionBounds premise; the semigroup construction printed in the companion has not been reconstructed. This is a declared literature boundary, not an unconditional Lean proof of that analytic input.

Proof references: [paper_comparison_eventually](../PaperCPrel8/MicroscopicNormalization.lean), [actual_geometry_eventually](../PaperCPrel8/MicroscopicActualGeometry.lean), [cutoff_tail_bound](../PaperCPrel8/MicroscopicInformationCutoff.lean), [tail_probability_eventually](../PaperCPrel8/MicroscopicDiscardTheorem.lean), [palm_stein_bound](../PaperCPrel8/PalmStein.lean).

## R05 — dyadic and empirical readouts

The stronger intermediate derivative estimate in the dyadic proof is replaced by monotonicity and a height-ratio bound. Same-grid field contraction, literal empirical scales, common-kernel readouts and the support obstruction are covered by the numbered ledger. Neither process limits nor arbitrary changes of conditioning follow from contraction alone.

Proof references: [shifted_information_margin](../PaperCPrel8/SaddleScaleMonotonicity.lean), [prime_sigma_mono](../PaperCPrel8/DyadicRestriction.lean), [rounded_intensity_bounds](../PaperCPrel8/EmpiricalPaperScales.lean).

## R06 — ordinary deletion and actual Palm laws

The costs d_A and delta_G are the actual original-conditioning outside-start probability and Poisson intensity. Additional deletions are bounded by a constant-word union, with harmless factor two, and vanish without exponential Palm amplification.

Proof references: [outside_union](../PaperCPrel8/OutsideDeletion.lean), [source_tendsto](../PaperCPrel8/OutsideDeletionLimits.lean), [target_tendsto](../PaperCPrel8/OutsideDeletionLimits.lean), [ordinary_full_deletion](../PaperCPrel8/ArithmeticPalmOutside.lean).

## R07 — tilted void and cumulant conventions

Higher cumulants are unchanged by deterministic translations and therefore agree with the raw convention. Reference-centered singletons remain EX-p. The improper logarithmic integral tends to +infinity at zero void probability; Real.log(0) is not an endpoint value.

Proof references: [integral_limit_positive](../PaperCPrel8/TiltedVoidIntegral.lean), [integral_limit_zero](../PaperCPrel8/TiltedVoidIntegral.lean), [jointCumulant_eq_raw](../PaperCPrel8/CumulantConventions.lean), [reference_singleton](../PaperCPrel8/CumulantConventions.lean), [reference_higher](../PaperCPrel8/CumulantConventions.lean).

## R08 — two-rank numerical example

The factorization and odd-valuation matrix of 91..95 and 113..117 are certified. The original arithmetic values agree with that matrix. The active independent prime coordinates give ranks 5,5,7,10, masses 2^-5,2^-7,2^-10, compatibility fraction 1/8, and mean absolute covariance 7/4096. The unused small prime 11 is a zero column.

Proof references: [individual_ranks](../PaperCPrel8/PairRankExample.lean), [rough_rank](../PaperCPrel8/PairRankExample.lean), [full_rank](../PaperCPrel8/PairRankExample.lean), [actual_values](../PaperCPrel8/PairRankExampleSource.lean), [compatibility_probability](../PaperCPrel8/PairRankExampleLaw.lean), [mean_absolute_covariance](../PaperCPrel8/PairRankExampleLaw.lean).

## R09 — fixed-weight prime obstruction

The same explicit witness works at every fixed t>exp(1)-1. This is a sufficient witness threshold, not a proved optimal phase boundary. Both original and stronger retained fields have a vanishing pair layer and divergent higher activity.

Proof references: [retained_log_diverges](../PaperCPrel8/PrimeWeightedLimit.lean), [original_log_diverges](../PaperCPrel8/PrimeWeightedLimit.lean), [retained_higher_diverges](../PaperCPrel8/PrimeHigherDivergence.lean).

## R10 — inherited unnumbered results including D.1/D.4

All 32 prior unnumbered groups and their precise proof references are retained below. D.1/D.4 assertions are unchanged; the added final paragraph clarifies the existing split proving joint Gaussian/Poisson independence. The prior declared fidelity and literature limits are retained.

## R11 — reading routes, introduction and discussion

The extended introduction is linked to the actual typical/affine dictionary theorem. Other changes explain proof routes, existing arithmetic inputs, scope and non-optimality; they are not additional independent probabilistic claims. Runge/Diophantine premises retain their baseline status. Bibliographic, layout and author-declaration edits are outside theorem coverage.

## Exact boundary of completion

The mathematical realignment is complete **relative to the explicit baseline
inputs and the alternative proofs recorded here**. The derivative formulas
replaced by monotonicity are not advertised as separately proved Lean lemmas.
F.2's semigroup construction remains outside the proved library boundary.
Statements inherited from earlier versions retain their earlier fidelity limits.
Publication metadata, revised manuscript prose, and new Comparator/NanoDa/Palomar
qualification are subsequent release work, not certified by this review.
