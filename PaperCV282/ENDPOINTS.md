# Paper C v2.8.2 endpoint ledger

The 115 mathematical modules contain **830 named declarations: 707 theorems, 111 definitions and 12 named local instances**. Batch 9 adds 182 theorems in 26 new modules.

This ledger records the mathematical scope of the supplied proof terms.
Build and qualification outcomes belong in separate evidence. No entry is
a new Palomar record. Declaration names below have prefix `PaperC.V282.`.

## Corollary 2.6: pointwise, conditional and dyadic summed clauses

Source: article page 9, equation (2.6), its conditional clause and the
following summed first-moment statement.

| Declaration | Established result |
|---|---|
| `PrescribedValues.probability_eq_eta_weight` | Exact finite affine probability `η 2^ρ / 2^B`. |
| `PrescribedValues.probability_error_le_defect_weight` | Error at most `(2^m - 1) / 2^B` under private-coordinate witnesses outside an `m`-element defect set. |
| `PrescribedValues.probability_eq_uniform_event` | Exact identification of the affine probability with the finite event of prescribed value bits. |
| `PrescribedValues.assemble_solves_values_iff` | Fixing small-prime coordinates translates the right-hand side by their actual contribution. |
| `WindowValues.corollary_two_six_pointwise` | Equation (2.6) in a finite cylinder, using the actual defective-vertex count. |
| `WindowValues.corollary_two_six_conditioned` | Exact word probability `2^(-B)` for each fixed small-prime assignment, when all vertices are nondefective above the threshold. |
| `InfiniteWordTransfer.infiniteWordEvent_eq_preimage` | The infinite word event is the preimage of its event on any adequate finite cylinder. |
| `InfiniteWordTransfer.measurableSet_infiniteWordEvent` | Measurability in the actual infinite product model. |
| `InfiniteWordTransfer.infiniteWordEvent_measure_eq_uniformSolutionProbability` | Exact equality of source measure with `ENNReal.ofReal` of the rational affine probability. |
| `InfiniteWordTransfer.infiniteWordProbability_eq_uniformSolutionProbability` | Exact real-valued finite/infinite probability identity. |
| `InfiniteWordTransfer.corollary_two_six_pointwise_infinite` | The real pointwise bound (2.6) for the infinite-product word probability. |
| `InfiniteConditionalWords.infiniteSmallPrimeAtom_measure` | Exact atom mass as the finite completion-count ratio under the source law. |
| `InfiniteConditionalWords.infiniteSmallPrimeAtom_measure_pos` | Every assignment atom has strictly positive measure. |
| `InfiniteConditionalWords.smallPrimeSigmaAlgebra_eq_primeCylinder` | For `Y ≤ M`, the represented small-prime sigma-algebra equals that of all prime coordinates at most `Y`, namely `F_Y`. |
| `InfiniteConditionalWords.corollary_two_six_joint_infinite` | Exact identity `measure(word ∩ atom) = measure(atom) * (1 / 2^B)` in the infinite model. |
| `InfiniteConditionalWords.corollary_two_six_conditioned_infinite` | The ratio `measure(word ∩ atom) / measure(atom)` is exactly `1 / 2^B` on every assignment atom. |
| `InfiniteWordFirstMoment.wordOccurrenceCount` | Finite sum of indicators of the actual infinite word events over positions and distinct dictionary words. |
| `InfiniteWordFirstMoment.integrable_wordOccurrenceCount` | Integrability under `infiniteRademacherMeasure`. |
| `InfiniteWordFirstMoment.integral_wordOccurrenceCount` | Exact identity between the occurrence-count integral and `wordProbabilitySum`. |
| `InfiniteWordFirstMoment.abs_wordProbabilitySum_sub_baseline_le` | Finite summed error bounded by `(|W| / 2^B)` times the mask's total word defect weight. |
| `WordDefectCounting.wordDefectMass_le` | The shifted word mass is at most twice the historical mass plus the global count of possible defective roots. |
| `WordDefectAsymptotics.wordDefectMass_uniformHalfPower_on_window` | Uniform `N^(1/2+o(1))` word defect mass on a fixed logarithmic band, with finite technical thresholds eliminated. |
| `WordFirstMomentAsymptotics.corollary_two_six_summed_probability` | Summed word-probability error, with one threshold valid for every length, dyadic mask and dictionary. |
| `WordFirstMomentAsymptotics.corollary_two_six_summed_expectation` | The same uniform estimate for the actual integral of the occurrence count under the infinite source law. |

The infinite pointwise endpoint is, for `x ≥ 2` and every `b : Fin B → F₂`,

```text
|infiniteWordProbability x B b - 1 / 2^B|
  ≤ (2^(defectIndices B x B).card - 1) / 2^B.
```

It has no exposed cutoff parameter: it chooses an adequate cylinder
internally and uses the exact source-law identity. Vertices are
`j ↦ x - 1 + j`, with `j < B`; distinct indices give distinct vertices.
The law is the retained `infiniteRademacherMeasure`, not a new model of
independent signs on integers.

The finite window endpoints require `x ≥ 2` and
`x - 1 + B ≤ M + 1`, so the cutoff contains every vertex. The conditional
endpoint further assumes `B ≤ Y` and
`∀ i : Fin B, ¬HDefective Y (vertex x B i)`. It proves uniformity for each
fixed assignment of represented primes at most `Y`. Using `B ≤ Y` slightly
extends the sufficient range `Y > B` printed in the article. The empty
window is also covered; the article's positive lengths are included without
relying on values at integer zero. The infinite conditional endpoints add
`Y ≤ M`, so the atom contains precisely all prime signs at most `Y`.
The atom definition, measurability, positive finite mass, and equality of
the generated sigma-algebra with `F_Y` are proved independently of the
good-window probability conclusion.

The summed first moment uses `s : Finset ℕ` and
`W : Finset (Fin B → F₂)`. Thus words are distinct, but their number and
values can vary with `N` and `B`. The random variable is the finite sum
of word-event indicators; linearity of its integral needs no independence
between positions or words. Its baseline is `|s| |W| / 2^B`.

The finite arithmetic bridge explicitly handles the root `x - 1`, rather
than identifying the word window with the historical interval `[x, x+B]`.
The resulting word defect mass is bounded by `sqrt N` times three times
the retained subpolynomial residual factor. Uniform admissibility removes
all finite technical thresholds in the logarithmic band.

For fixed real numbers `0 < c₁ < c₂`, the terminal expectation theorem
has the exact quantifier order

```text
∀ k : ℕ, 0 < k → ∃ N₀, ∀ N ≥ N₀, ∀ B : ℕ,
  (c₁ log N ≤ B ∧ B ≤ c₂ log N) →
  ∀ s : Finset ℕ, s ⊆ [N, 2N) →
  ∀ W : Finset (Fin B → F₂),
  |∫ wordOccurrenceCount B s W dμ - |s| |W| / 2^B|^(2k)
    ≤ (|W| / 2^B)^(2k) N^(k+1),
  where μ = infiniteRademacherMeasure.
```

The threshold depends only on `c₁`, `c₂` and `k`. In particular, it is
independent of `B`, `s` and `W`. The scale `|W| / 2^B` is never divided
out, so empty dictionaries and masks are covered. No balance bound on
`N / 2^B` is assumed. This proves the dyadic
`O(m p_B N^(1/2+o(1)))` clause with its uniformity over masks and dictionaries.

The three clauses of Corollary 2.6 are therefore covered in their stated
representations: infinite pointwise probability, exact conditional law on
positive `F_Y` atoms, and the actual dyadic summed expectation. An abstract
conditional-expectation API remains optional presentation work. These
dyadic endpoints are complemented by the batch 9 macroscopic extension in
`MacroscopicWordFirstMoment`, with arbitrary masks in `[ceil(M^δ), M)`.

The intended hypothesis is an odd **valuation** at a prime above `Y`.
[`MANUSCRIPT_NOTES.md`](MANUSCRIPT_NOTES.md) proposes clearer wording for a
future revision. The current source identity remains v2.8.2.
See also the [v3 revision log](../docs/PAPER_V3_REVISION_LOG.md).

## Proposition 3.7: global and macroscopic host inequalities

Source: article pages 14–15, Proposition 3.7 and its proof. Here `B = L + 1`.

| Declaration | Established result |
|---|---|
| `FullIntervalPrimeAssignment.right_mem_boundedAssignment_of_selected_left` and `left_mem_boundedAssignment_of_selected_right` | A selected full-value coefficient places the opposite start in the retained interval assignment classes for `[A, Z)`, without block parity. |
| `FullIntervalHostCounting.squareProductHosts_subset_certificateCover` | Every unrestricted square-product host in a pair mask inside `[A, Z)²`, with `A ≥ 2`, belongs to the retained congruence cover. |
| `FullIntervalHostCounting.card_squareProductHosts_Icc_cast_le_kernelSumQ` | For every mask in `[2, M]²`, finite bound `card ≤ 8 (L + 1) M ∑_{1≤n≤3M} largeKernelWeightQ (L + 1) n`, with `M ≥ 2` and `L ≤ M`. |
| `FullIntervalHostAsymptotics.card_squareProductHosts_cast_le_exp_bound` | Explicit bound `card ≤ 8 (L + 1) M sqrt(3M) exp(4 sqrt(L + 1))` on the same global square. |
| `FullIntervalHostAsymptotics.card_squareProductHosts_uniformThreeHalves_logarithmic` | Uniform `M^(3/2+o(1))` bound for every global pair mask, with finite technical thresholds absorbed and only the logarithmic length ceiling exposed. |
| `MacroscopicGeometry.macroscopicStarts` and `mem_macroscopicStarts_iff_real` | Exact positive-integer start domain `[ceil(M^δ), M)`, equivalently `M^δ ≤ x < M`. |
| `MacroscopicGeometry.separatedPairs_macroscopicStarts_subset_Icc_product` | For `M ≥ 2` and `δ > 0`, its separated pairs lie in `[2, M]²`. |
| `FullHostComparison.startRelationHosts_subset_squareProductHosts` and `card_startRelationHosts_le_squareProductHosts` | Actual nonzero start-relation hosts form a subset of the unrestricted square-product hosts, under positivity and cylinder adequacy. |
| `FullIntervalHostAsymptotics.proposition_three_seven_full_hosts` | Uniform full-host power bound on the exact macroscopic domain, with threshold independent of `L` and `δ`. |
| `FullIntervalHostAsymptotics.proposition_three_seven` | Both Proposition 3.7 host inequalities together, using cutoff `M + L` for the actual start-relation count. |
| `BoundedRatioFullHosts.card_squareProductHosts_uniformThreeHalves_boundedRatio` | Host bound normalized by `N` for `N ≤ M ≤ κ N`, uniformly over all masks in `[2, M]²`. |
| `BoundedRatioFullHosts.proposition_three_seven_boundedRatio` | The same lower-scale bound conjoined with the start-host comparison on separated starts in `[N, M)`. |

The finite assignment cover works on `[A, Z)` without a bounded-ratio or
pair-separation hypothesis. For the global counting bound, `[2, M]` is
`[2, M + 1)`, whose width is `M - 1`. With `L ≤ M`, the selected vertex
and its large-prime kernel are at most `M + 1 + L ≤ 3M`. The congruence
count's additive constant is absorbed using
`(M - 1) + K ≤ 4M`; nonnegative kernel weights allow extension of the
sum to `1 ≤ n ≤ 3M`. No block-parity constraint is added to the host set.

For each fixed `C ≥ 0`, the final global bound has quantifier order

```text
∀ k : ℕ, 0 < k → ∃ M₀, ∀ M ≥ M₀, ∀ L : ℕ,
  L + 1 ≤ C log M → ∀ s : Finset (ℕ × ℕ), s ⊆ [2, M]² →
  card(squareProductHosts L s)^(2k) ≤ M^(3k+1).
```

The threshold absorbs `M ≥ 2` and `L ≤ M`; these are not additional
hypotheses of this terminal theorem. There is no lower logarithmic bound
and no restriction on the ratio or separation of the starts in `s`.

For the macroscopic specialization, put
`U = Finset.Ico ⌈(M : ℝ)^δ⌉₊ M` and `S = separatedPairs U L`.
Under `δ > 0`, the same threshold, chosen before `L` and `δ`, gives

```text
card(startRelationHosts (M + L) L S) ≤ card(squareProductHosts L S)
  ∧ card(squareProductHosts L S)^(2k) ≤ M^(3k+1).
```

The natural ceiling matches the positive-integer lower endpoint under
`M ≥ 2` and `δ > 0`. No assumption `δ < 1` is required; the domain may
be empty. The cutoff `M + L` contains all vertices of both windows, so
the first count uses their actual start relations. This proves the host
inequalities of Proposition 3.7 in an explicit uniform power formulation.
The separate bounded-ratio endpoints preserve normalization by the lower
scale `N`. For fixed `C ≥ 0` and `κ : ℕ`, they give

```text
∀ k : ℕ, 0 < k → ∃ N₀, ∀ N ≥ N₀, ∀ M : ℕ,
  N ≤ M → M ≤ κ N → ∀ L : ℕ, L + 1 ≤ C log N →
  ∀ s : Finset (ℕ × ℕ), s ⊆ [2, M]² →
  card(squareProductHosts L s)^(2k) ≤ N^(3k+1).
```

The proof applies the global theorem with `2k` and chooses the threshold
at least `κ^(6k+1)`. Then `H^(4k) ≤ M^(6k+1) ≤ N^(6k+2)` gives the
displayed bound by comparison of nonnegative squares. The threshold
depends on `C`, `κ` and `k`, and precedes `M`, `L` and the pair mask.
No hypothesis `κ ≥ 1` is required: impossible endpoint
ranges cause no exception. A second endpoint specializes to
`S = separatedPairs (Finset.Ico N M) L`, adjoining
`card(startRelationHosts (M + L) L S) ≤ card(squareProductHosts L S)`.
This proves the bounded-ratio host estimate at scale `N`, including the
actual start-system comparison. Neither endpoint asserts a weighted
relation-profile bound.

## Lemma 3.3 and Proposition 3.8: canonical channels and rational profiles

Source: article page 11, Lemma 3.3; page 15, Proposition 3.8,
equations (3.12) and (3.13).
Here `B = L + 1`, `Q_B = 2^B` and the manuscript's coding parameter is `A = 3`.

| Declaration | Established result |
|---|---|
| `IntervalRationalMass.boundedRationalMass_le_interval_profile` | Finite total rational mass at most `6 M (L+1) 2^(L/2) + 4 M (L+1)^4 2^(L/3)` on `[N, M)`, with `1 ≤ M`, `N ≤ M` and `1 ≤ A`. |
| `IntervalRationalMass.systematicMass_le_interval_profile` | Real-valued transfer to the retained systematic mass. |
| `MacroscopicCanonicalCode.determinant_threshold_macroscopic_eventually` | For fixed `C ≥ 0` and `δ > 0`, eventually `4 B^7 < M^δ ≤ x` for every macroscopic start and every `B ≤ C log M`. |
| `MacroscopicCanonicalCode.card_reduced_candidates_le_one_eventually` | At most one reduced candidate of height at most `B^3`, uniformly in the length, macroscopic first start and arbitrary natural second start. |
| `MacroscopicCanonicalCode.canonical_candidate_eq_some_eventually` | Every candidate witness equals the bundled canonical choice beyond the same kind of threshold. |
| `MacroscopicCanonicalCode.canonical_rational_code_eq_of_nonzero_eventually` | Every nonzero primitive rational code is the canonical code for `A = 3`, with both starts macroscopically positive and arbitrary prime cutoff. |
| `RationalHeightMass.rationalHeightTwoMass` and `rationalHeightAtLeastThreeMass` | Exact sums of `2^sigma-1` filtered by the selected canonical height `q = 2` and `q ≥ 3`. |
| `RationalHeightMass.canonicalPairSigma_eq_zero_of_height_lt_two` | No positive rational weight is omitted at heights zero or one on separated pairs. |
| `RationalHeightMass.boundedRationalMass_eq_height_masses` | Exact decomposition of the full rational mass into the two filtered masses. |
| `RationalHeightMass.rationalHeightTwoMass_le_interval_profile` | Separate finite height-two bound `6 M (L+1) 2^(L/2)`. |
| `RationalHeightMass.rationalHeightAtLeastThreeMass_le_interval_profile` | Separate finite large-height bound `4 M (L+1)^4 2^(L/3)`. |
| `RationalGeometryMass.geometryMass` and `geometry_mem_sum_iff` | Exact binary geometry-only sum and equivalence of its finite support with all positive primitive geometries of height at least two and multiplicity at least two. |
| `RationalGeometryMass.geometryMass_le_poly_two_pow_half` | Explicit finite bound `G ≤ 6 (L+1)^4 2^(L/2)`. |
| `LogarithmicWordPowers.two_pow_div_le_word_rpow` and `polynomial_factor_le_rpow_eventually` | Replace quotient exponents by actual roots of `Q_B`, and absorb fixed polynomial length factors into every prescribed `M^ε`. |
| `RationalMassAsymptotics.systematicMass_uniform_profile` | Total real rational profile with both roots of `Q_B`, uniformly over arbitrary lower endpoints and `A ≥ 1`. |
| `RationalMassAsymptotics.macroscopic_systematicMass_uniform_profile` | Total profile on `[ceil(M^δ), M)` with `A = 3`, with numerical threshold before `δ`. |
| `RationalProfile.height_masses_uniform_profiles` | The two distinct real bounds of (3.12), uniformly over all lower endpoints and `A ≥ 1`. |
| `RationalProfile.geometryMass_uniform_profile` | The real geometry-only bound (3.13), retaining the binary weight and no translation factor. |
| `RationalProfile.proposition_three_eight` | All three bounds on the exact macroscopic domain with `A = 3`, together with uniqueness of any candidate channel beyond a fixed-`δ` threshold. |

The height filters refer to `canonicalPairHeight`, not merely to the
existence of some channel of that height. Each nonzero weight is supported
on the appropriate retained cover; those covers are used only for upper
bounds and need not be disjoint. The exact decomposition instead uses the
disjoint filters `q = 2` and `q ≥ 3`. A positive weight at a lower height
would force a unit channel with `Nat.dist x y ≤ L`, contradicting separation.

The geometry-only sum is literally

```text
G(L) = ∑ q∈[2,L] ∑ (a,b)∈reducedRatiosAtHeight q
         ∑ h∈nontrivialChannelHeights L a b 2^channelSigma(L,a,b,h).
```

The support condition means `a,b > 0`, `gcd(a,b) = 1`, `max(a,b) ≥ 2`
and `m(a,b,h) ≥ 2`; the latter implies the displayed upper bound `q ≤ L`.
The weight is `2^(m-1)`, without subtracting one from that weight and
without translation parameters. The retained historical weighted mass
uses base four and is a different quantity. The new base-two proof uses
at most `2q` reduced pairs, at most `2qL+1` affine heights per pair and
weight at most `2^(L/q)`.

For fixed `C ≥ 0`, `δ > 0` and `ε > 0`, the final endpoint chooses `M₀`
before the length and both starts. With `N = ceil(M^δ)`, it states

```text
∀ M ≥ M₀, ∀ L : ℕ, L + 1 ≤ C log M →
  Rtwo(N,M,3,L)   ≤ M^ε M Q_B^(1/2) ∧
  Rthree(N,M,3,L) ≤ M^ε M Q_B^(1/3) ∧
  G(L)            ≤ M^ε   Q_B^(1/2) ∧
  ∀ x∈[ceil(M^δ),M), ∀ y : ℕ,
    card(reducedChannelCandidates x y B (B^3)) ≤ 1,
  where B = L + 1 and Q_B = 2^B.
```

These are real inequalities with the actual `Q_B`, and no critical-balance
condition is used. Only the polynomial length factors are absorbed into
`M^ε`. The numerical mass bounds are uniform in arbitrary lower interval
endpoints, including empty or reversed intervals. In contrast, identifying
the unique macroscopic canonical channel requires `δ > 0` fixed before
its threshold, exactly as in Lemma 3.3. Existence is supplied by a channel
witness; uniqueness does not assert that every pair is aligned.

This covers the three inequalities of Proposition 3.8. It does not bound
the residual mass, identify the eight residual sectors, or establish the
full raw profile of Theorem 3.1.

## Proposition 3.26: finite comparison and uniform positive correction

Source: article page 25, Proposition 3.26 and equations (3.24)–(3.25).
In these modules `B = L + 1`.

| Declaration | Established result |
|---|---|
| `ValueRelations.relationRho_le_parityNullity_add_two` | Abstract nullity loss at most two under two binary linear constraints. |
| `TwoWindowParity.twoValueSystem` and `TwoWindowParity.blockParity` | Actual valuation rows of both windows and separate sums of coefficients in the two blocks. |
| `TwoWindowParity.startRelationEquivParityKernel` | Linear equivalence from actual two-start relations to the kernel of both parities inside the full-value relation space. |
| `TwoWindowParity.parityNullity_eq_start_relationRho` | Exact equality of constrained full-value nullity and start-system nullity. |
| `TwoWindowParity.twoValueSystem_eq_consecutive` | Historical complete-vertex labels equal the displayed consecutive windows under positive-start hypotheses. |
| `TwoWindowParity.value_weight_le_four_start_weight_add_host` | Pointwise factor-four comparison for actual matrices, with correction only at a nonzero full-value kernel. |
| `ValueSquareRelations.mem_value_relation_iff_square_product` | A full-value relation is exactly a square product over its support, for positive values covered by the cutoff. |
| `ValueSquareRelations.relationRho_ne_zero_iff_exists_nonempty_square_product` | Nonzero full-value nullity is equivalent to a nonempty indexed square-product subset. |
| `TwoWindowSquareHosts.valueRelationalHosts_eq_squareProductHosts` | Full-value nullity hosts equal the unrestricted arithmetic square-product hosts under positivity and cylinder adequacy. |
| `TwoWindowSquareHosts.finite_equation_three_twenty_four_square_hosts` | Finite (3.24) on ordered separated pairs, with actual start relations and unrestricted square-product hosts. |
| `FullPrimeAssignment.right_mem_startsForSomeAssignment_of_selected_left` and `left_mem_startsForSomeAssignment_of_selected_right` | A selected full-value coefficient places the opposite start in the retained congruence assignment classes, without block parity. |
| `FullHostCounting.squareProductHosts_subset_certificateCover` | All unrestricted square-product hosts in a dyadic pair mask lie in the retained certificate cover. |
| `FullHostCounting.card_squareProductHosts_cast_le_kernelSumQ` | Finite bound `card ≤ 8 (L + 1) N ∑_{1≤n≤3N} largeKernelWeightQ (L + 1) n`. |
| `FullHostAsymptotics.card_squareProductHosts_cast_le_exp_bound` | Explicit real bound `card ≤ 8 (L + 1) N sqrt(3N) exp(4 sqrt(L + 1))`. |
| `FullHostAsymptotics.card_squareProductHosts_uniformThreeHalves` | Uniform dyadic `N^(3/2+o(1))` estimate for every pair mask, with the threshold independent of the mask. |
| `FullHostAsymptotics.card_separated_squareProductHosts_uniformThreeHalves` | Specialization to actual separated ordered pairs in the dyadic block. |
| `MacroscopicRelationProfile.macroscopicStartMassNat` and `macroscopicValueMassNat` | Exact natural weighted masses of actual start and full-value relations on the same macroscopic separated pairs and cutoff `M + L`. |
| `MacroscopicRelationProfile.macroscopicSeparatedPairs_eq_boundedRatioPairs` | Exact equality with the retained interval pair population at lower endpoint `ceil(M^δ)`. |
| `MacroscopicRelationProfile.macroscopicStartMassNat_cast_eq_R2kappa` | The start mass's real cast equals the historical interval mass `R2κ`, without ratio, length or positivity hypotheses for this definitional equality. |
| `MacroscopicRelationProfile.macroscopicStartMassNat_cast_eq_systematic_add_residual` | Exact transfer of the historical canonical systematic/residual decomposition for every natural coding parameter `A`, with `M ≥ 2` and `δ > 0`. |
| `MacroscopicRelationProfile.macroscopicValueMassNat_le_four_start_add_hosts` | Finite (3.24) for the literal macroscopic masses, with `M ≥ 2` and `δ > 0`. |
| `MacroscopicValueCorrection.macroscopicValueExcess` and `macroscopicValueExcess_cast_eq_max` | Natural positive excess and its exact real representation `max(0, Rval - 4 Rstart)`. |
| `MacroscopicValueCorrection.macroscopicValueExcess_le_three_hosts` | The positive excess is at most three times the unrestricted macroscopic host count. |
| `MacroscopicValueCorrection.macroscopicValueExcess_uniformThreeHalves` | Uniform power bound for the natural excess, with threshold before length and macroscopic exponent. |
| `MacroscopicValueCorrection.prescribed_value_correction_uniform` | The same unconditional bound for the actual real positive part `max(0, Rval - 4 Rstart)`. |

The finite (3.24) endpoint accepts `M L : ℕ` and `I : Finset ℕ`, with

```text
∀ x ∈ I, 2 ≤ x
∀ x ∈ I, x + L ≤ M + 1.
```

Writing `S = separatedPairs I L`, its conclusion is

```text
∑ (x,y) ∈ S, (2^ρval(M,x,y,L) - 1)
  ≤ 4 * ∑ (x,y) ∈ S, (2^ρstart(M,x,y,L) - 1)
      + 3 * (squareProductHosts L S).card.
```

Here `S` is exactly the ordered pairs from `I × I` with
`L < Nat.dist x y`. The set `I` may be an interval or deterministic mask.
The cutoff contains the rightmost vertex `x + L - 1` of each window.

`squareProductHosts` is defined without a prime-cylinder parameter: a pair
belongs when a **nonempty indexed subset** of its full vertex occurrences
has square product. There is no even-cardinality restriction in either
block. It includes pairs with nonzero full-value nullity but zero start
nullity; the historical start-relation host set cannot replace it.

The real block parities, tree-boundary identification, ordered-pair sum and
arithmetic meaning of the host correction are now proved. The abstract
`ValueRelations` bounds remain reusable components, rather than the limit
of the current implementation.

The dyadic host bound holds for every `s ⊆ dyadicBlock N × dyadicBlock N`
with `N ≥ 2` and `L ≤ N`. It requires no separation or block parity. The
uniform endpoint has the exact quantifier order

```text
∀ C ≥ 0, ∀ k : ℕ, 0 < k → ∃ N₀, ∀ N ≥ N₀, ∀ L,
  (N ≥ 2 ∧ L ≤ N ∧ L + 1 ≤ C log N) →
  ∀ s ⊆ dyadicBlock N × dyadicBlock N,
  card(squareProductHosts L s)^(2k) ≤ N^(3k+1).
```

Thus `N₀` is independent of both the length and the pair mask. This is the
power-form assertion of `N^(3/2+o(1))` uniformly in the logarithmic band.
It also covers the actual separated mask.

The global and macroscopic extension of this host count is established
by the Proposition 3.7 endpoints above. The exact macroscopic masses use
`U = Finset.Ico ⌈(M : ℝ)^δ⌉₊ M`, `S = separatedPairs U L` and cutoff
`M + L`:

```text
Rstart = ∑ (x,y) ∈ S, (2^ρstart(M+L,x,y,L) - 1)
Rval   = ∑ (x,y) ∈ S, (2^ρval(M+L,x,y,L) - 1).
```

Their Lean definitions are natural-valued; `Rstart` and `Rval` in the
following display denote their real casts. The start mass is exactly
`PropositionSixteenOne.R2κ ⌈M^δ⌉₊ M L`, including empty populations.
For `M ≥ 2`, `δ > 0` and every `A : ℕ`, the retained canonical code gives

```text
Rstart = systematicMass A ⌈M^δ⌉₊ M L
           + residualMass A ⌈M^δ⌉₊ M L.
```

This is an exact finite decomposition, without a ratio or logarithmic
assumption. It includes `A = 3`. The new `ResidualSectorPartition` and
`ResidualSectorMass` modules further identify the eight successive sectors
and prove their exact weighted decomposition, as detailed below. Estimates
of their masses are separate theorems.

Finite (3.24) now also appears directly as
`Rval ≤ 4 Rstart + 3 Hval` on `U`, with `M ≥ 2` and `δ > 0`.
Natural subtraction defines the positive excess; its real cast is proved
equal to `max(0, Rval - 4 Rstart)`. For fixed `C ≥ 0`, the terminal
correction theorem states

```text
∀ k : ℕ, 0 < k → ∃ M₀, ∀ M ≥ M₀, ∀ L : ℕ,
  L + 1 ≤ C log M → ∀ δ : ℝ, 0 < δ →
  max(0, Rval - 4 Rstart)^(2k) ≤ M^(3k+1).
```

The threshold precedes both `L` and `δ`. The proof bounds the excess by
`3 Hval`, applies the host theorem at exponent `2k`, and takes
`M ≥ 3^(4k)` to absorb the fixed factor. This is an unconditional
`M^(3/2+o(1))` upper bound for the positive part, not an absolute-difference
bound or an asymptotic equality. It assumes no raw weighted profile.

The complete profiles are now supplied by `WholeRelationProfile` and
`BoundedRatioRelationProfiles`, detailed below. The intermediate finite
comparison and positive-correction theorems retain their own narrower
statements; the new global endpoints discharge every residual sector.

## Exact eight-sector partition and nonterminal profiles

Sources: article pages 16–24, successive partition, Proposition 3.12 and
the sector estimates in the assembly table. Set `B=L+1`, `Q=2^B`,
`N=ceil(M^delta)`. Lean's `Fin 8` indices `0,…,7` denote manuscript
sectors `1,…,8`. The classifier tests actual canonical quantities, in the
printed order: `P#≤M`, a positive small-height rational channel,
`6c#≤B`, alignment, `3c#≤2B`, `D#≥3`, and the actual rank/slack threshold
`floor((L−1)/3)`. Its disjoint cover and membership equivalences do not
accept an external classification or rank function.

| Declaration or module | Established result |
|---|---|
| `ResidualSectorPartition` | Eight literal complementary populations; late-sector zero systematic dimension, nonalignment and actual rank identities. |
| `ResidualSectorMass.residualMass_eq_sum_sectorMass` | Exact sum of the eight actual residual masses, with weight `2^sigma*(2^tau−1)`. |
| `ResidualSectorMass.macroscopicStartMass_eq_systematic_add_sectors` | Exact macroscopic start mass = rational contribution + all eight sectors. |
| `HostRankMass`, `HostRealPowers` | General masked homogeneous weight and real host bounds; corrected rank budget and exact `Q^(1/6)` factor. |
| `MacroscopicSmallProductProfile.sector_one_mass_le_profile_eventually` | Sector 1 at most `M^epsilon*(M^(3/2)+M*Q^(1/2))`. |
| `MacroscopicSmallHeightSector.sector_two_mass_le_rational_profile_eventually` | Sector 2 at most `M^epsilon*(M*Q^(1/2)+M*Q^(1/3))`. |
| `MacroscopicShallowSectors.sector_three_mass_le_profile_eventually` | Sector 3 at most `M^epsilon*M^(3/2)*Q^(1/6)`. |
| `MacroscopicShallowSectors.sector_four_mass_eq_zero_eventually` | Actual sector 4 is empty beyond the uniform threshold. |
| `MacroscopicEarlyProfile.proposition_three_twelve` | Joint form of the first three profiles, plus empty sector 4, with one threshold for `A=3`. |
| `MacroscopicBoundedHosts.card_boundedHosts_le_linear_profile_eventually` | For each fixed component-size bound `K`, at most `M^(1+epsilon)` hosts, uniformly in every lower endpoint `N≥2` and `A`. |
| `SectorFiveProfile.macroscopic_sector_five_le_profile_eventually` | Actual sector 5 at most `M^epsilon*M*Q^(2/3)`. |
| `MacroscopicTwoDefectStarts.card_twoDefectBaseCover_le_rpow_eventually` | Actual two-defect base cover has at most `M^epsilon` members on the macroscopic domain. |
| `SectorSixProfile.card_sector_six_le_half_profile_eventually` | Actual sector-6 host count at most `M^epsilon*sqrt(M)`. |
| `SectorSixProfile.macroscopic_sector_six_le_profile_eventually` | Actual sector 6 at most `M^epsilon*sqrt(M)*Q`. |
| `SizeTwoHostAsymptotics.macroscopic_sector_seven_le_profile_eventually` | Actual sector 7 at most `M^epsilon*M*Q^(2/3)`. |

For the combined sector statements, fix `0<betaMin<betaMax`, `delta>0`
and `epsilon>0`. The threshold precedes all `M≥M0` and `L` in
`betaMin*log M ≤ L+1 ≤ betaMax*log M`. The joint manuscript choice is
`A=3`. Several individual statements are uniform in every natural `A`
or every `A≥1`; their declarations retain this stronger quantifier order.
No bound on the ratio of the two starts or balance `Q≈M` is used.

The small-product proof shows `(B+1)^c#≤P#≤M`, obtains a uniform
pointwise `2^tau≤M^epsilon`, and pays its two systematic branches by hosts
and rational mass. It does not claim the growing-moment inequality itself.
For sector 2, the strict positive-dimensional channel convention omits the
harmless additional `M^(3/2)` term printed in Proposition 3.12.

The alignment argument proves the density specialization needed by the
actual fourth sector, namely eventual `6c#≤B`. The fully general fixed
`alpha>0` statement of Proposition 3.19 is not asserted. Defect estimates
are transported separately to both shifted starts `x−1` and `y−1`;
comparability of the endpoints is not hidden in this step.

Sector 5's strict average forces a component of size at most **11**.
Sector 6's density forces size two, and three corrected defects force two
true defective occurrences in one block. Its partner fibre then has degree
one. Sector 7 uses the exact integer rank budget to obtain
`3*tau≤2B+7`, hence a pointwise factor `8*Q^(2/3)`, followed by the finite
size-two harmonic/Euler host count.

`RemainingDeepProfile` records an earlier valid grouping isolating sectors
5,6,8. It remains a finite reduction; `NonterminalProfile` gives the final
stronger reduction after the individual fifth and sixth sectors are closed.

## Internal divisor, Pell and split-product counts

Sources: article pages 17–20, Lemmas 3.13–3.16 and the companion's
polynomial-height arguments. The newly established rate is the uniform
`M^epsilon` consequence, **not** the more precise displayed
`exp(O(log M/loglog M))` rate.

| Declaration | Established result |
|---|---|
| `DivisorSubpolynomial.card_divisors_pow_le_log_power_mul_self` | Elementary factorization bound `tau(n)^k≤(log_2(n)+1)^(k*2^k)*n` for positive `n`. |
| `DivisorSubpolynomial.card_divisors_le_rpow_eventually` | For fixed natural `K` and `epsilon>0`, every `n≤M^K` has at most `M^epsilon` divisors beyond one threshold. Zero is included through the finite-divisor convention. |
| `PolynomialPellCount.pellBox_atMost_rpow_eventually` | Internal uniform count of the actual polynomial-height generalized Pell box, for positive coefficients, nonsquare rational ratio and nonzero right-hand side. |
| `SplitProductLocalization.squarefreeKernel_shift_dvd` | Each positive factor's squarefree part divides the coefficient times the nonzero shift-difference product. |
| `PositiveSquareclassPairs.positiveSquareclassBox_atMost_rpow_eventually` | Positive-root count including equal squareclasses by signed factorization, and unequal squareclasses by the internal Pell bound. |
| `PolynomialSplitProducts.splitProductStart_atMost_rpow_eventually` | Uniform count of integer starts in a fixed-degree positive split product, after localizing two squareclasses. |
| `PolynomialSplitSolutions.splitProductSolution_atMost_rpow_eventually` | Uniform count of all integer pairs `(X,Y)`, accounting for both signs of `Y`; no extra height bound on `Y`. |
| `MacroscopicOneSidedFibers.offsetProductNatFiber_atMost_rpow_eventually` | True natural `(start,root)` fibres of all degrees from 2 through a fixed bound, at most `M^epsilon`. |

The threshold is selected after the fixed height exponent and degree, and
before coefficients, distinct shift tuples and finite solution families.
All shifted factors are positive. The split coefficient is positive; it
need not be squarefree in the new bound. Fixing a positive factor determines
its canonical nonnegative root, so the natural fibre injection is exact.

`MacroscopicComponentNormalization`, `MacroscopicComponentFibers` and
`MacroscopicBaseFibers` establish the actual component equation and the
coefficient `sf(d*P)` before the mobile start is counted. Height bounds are
polynomial in the upper scale, and the smooth squareclass population is
uniformly subpolynomial. `MacroscopicSmoothKernels` even places its threshold
before the auxiliary height cutoff, by bounding the entire squarefree
smooth population by `2^pi(B)`.

No Evertse–Silverman, Nicolas–Robin or unproved Pell proposition is a premise
of these new endpoints. The proof uses the retained, internally proved
conductor descent and unit-orbit counting, then the new elementary divisor
bound. A historical namespace named after an external interface can still
supply definitions; that name does not establish a dependency on an
external premise. The exact exported theorem types and kernel transcript
are authoritative. No height-free integral-point count is asserted.

## Lemma 3.24: full shifted small-kernel energy

Source: article pages 23–24, equation (3.21). Define

```text
A_T(x) = #{i in range(L+1) : K_(L+1)(x−1+i) ≤ T}
windowEnergy = sum_{x in Ico X (2X)} choose(A_T(x),2).
```

`MacroscopicKernelEnergy.lemma_three_twenty_four` proves, for every fixed
`C,D≥0` and `epsilon>0`, a threshold before all `X≥X0`, lengths `L` and
**natural** caps `T`, under

```text
L+1 ≤ C*log X,     T ≤ D*sqrt(X*(L+1)),
```

the bound

```text
windowEnergy ≤ X^(2/3+epsilon)*(L+1)^2.
```

The natural cap is applied to integer kernels; the displayed endpoint does
not define a separate real-cap energy. It needs no lower logarithmic
bound. Its proof includes every following step, without an energy or
population estimate supplied as a premise:

- `ShiftedKernelBoxCount`: the integer equation `q*r+h=q'*s`, its gcd
  obstruction, spacing and dyadic affine-fibre bound.
- `ShiftedKernelQuotients` and `ShiftedKernelRangeCount`: actual canonical
  quotients have kernel one; their square/smooth representations give the
  finite joint box count.
- `SmallKernelAnchors`: either kernel below `floor(X^(1/3))` supplies a
  low-kernel anchor counted up to `3X`.
- `ShiftedKernelDyadicCover`: exhaustive dyadic ranges based at
  `ceil(X^(1/3))`, with the number of range pairs absorbed uniformly.
- `ShiftedKernelPairCount`: complete two-kernel pair count on `[X,2X)`.
- `KernelWindowEnergy`: exact binomial double counting of actual window
  incidences and at most `L+1` placements per shifted pair.
- `MacroscopicKernelEnergy`: three adjacent value slices cover
  `[X−1,2X+L)`, including all boundary occurrences, before summing shifts.

The batch 9 terminal modules now connect the actual graph components,
determinants, partner fibres and rank strata to this energy estimate.
`SectorEightProfile` completes Proposition 3.25 and its same-cap version;
see the complete terminal and global profiles above.

## Explicit rational lower bounds (3.22)–(3.23)

Source: article page 24. `RationalLowerBounds` embeds an actual even exact-
unit code into the relation space without assuming that the canonical code
selected this particular rational channel. `RationalFamilyMass` keeps both
orientations and proves they are distinct. `IntervalRationalLowerBounds`
checks actual interval membership and separation before taking the mass.

For every fixed upper logarithmic band, the eventual bounds are

```text
R2(N,L) ≥ (N/3−1) * (2^(floor((B+1)/3)−1)−1),
R2_delta(M,L) ≥ (M−2*M^delta−2) * (2^(floor(B/2)−1)−1).
```

The endpoints are respectively
`equation_three_twenty_two_eventually` and
`equation_three_twenty_three_eventually` in that module. All exponents and
subtractions inside the natural weight are natural arithmetic, as declared.
The macroscopic `delta>0` is fixed before its threshold. Both bounds remain
valid when their coefficient is negative or the finite population is empty.
The particular positive lower exponents at critical balance are not exported
as separate asymptotic lower-bound declarations in this batch.

## Capped masses and the retained nonterminal reduction

`CappedRelationMass` defines the literal start and full-value sums
`sum min(T,2^rho−1)` with a real cap and proves monotonicity, elementary
bounds and the same-cap finite inequality `Rval[T]≤4*Rstart[T]+3*Hval`.
`CappedSectorMass` provides the exact capped residual partition, and
`min(T,a+b)≤a+min(T,b)` leaves the systematic part uncapped. Its finite
`min(T,E*Q)≤E*min(T,Q)` step explicitly requires `E≥1` and `T≥0`.

`CappedSectorSixProfile.capped_sector_six_le_profile_eventually` proves the
actual sector-6 bound `M^epsilon*sqrt(M)*min(T,Q)` with a common threshold
before every natural `A` and every real `T≥0`.

`NonterminalProfile` combines the completed sectors and leaves precisely
sector 8 explicit. Its capped start reduction uses

```text
cappedProfile(M,Q,T) = M^(3/2)*Q^(1/6) + M*Q^(2/3)
                      + M^(2/3)*min(T,Q).
```

The bound is `Rstart[T]≤M^epsilon*cappedProfile+capSector8`, uniform in the
cap. The uncapped reduction analogously gives
`Rstart≤M^epsilon*rawProfile+sector8`, where

```text
rawProfile(M,Q) = M^(3/2)*Q^(1/6) + M*Q^(2/3) + M^(2/3)*Q.
```

These intermediate reductions are now discharged by `SectorEightProfile`
and `WholeRelationProfile`, which prove Theorem 3.1 and Proposition 3.27.
`ProfileMonomials` proves the numerical weighted arithmetic–geometric mean
step `rawProfile≤2*(M^(5/3)+M^(2/3)*Q)` and the domination of every row of
the assembly table. `ProfileAssembly` keeps the necessary sector bounds as
explicit hypotheses. Its premises are explicit; the unconditional endpoints are assembled
separately from the actual proved sectors.

## Complete terminal sector and global relation profiles (batch 9)

`SectorEightGeometry` extracts the actual isolated components, distinct
coprime nontrivial kernels, and nonzero cross-determinants. `TerminalSliceGeometry`
transfers the small-kernel lower bound to both original windows. The
`TerminalPartnerCount` and `TerminalSliceContainer` populations are genuine
finite sets with internal counts, uniformly before their moving parameters.
`OrderedPairCounting` counts both orientations with a factor two without
assuming that `sectorOf` is symmetric.

`TerminalSliceGeometry.lemma_three_twenty_two` additionally exposes the
exact ambient package `0<abs(Delta)<=4*M*B`, with coprime common kernels
and their product dividing the determinant. The slice cap retains 6*X*B.

`SectorEightProfile.proposition_three_twenty_five` proves exactly
`M^epsilon*(M^(2/3)*Q+M^(3/4)*Q^(2/3))` for sector 8. Its `_capped`
analogue replaces the first Q by `min(T,Q)`, with the same threshold before
T>=0. Coding A>=1 is explicit; the global assembly uses A=3.
`MacroscopicDyadicSlices` proves exact fibrewise summation by the logarithm
of the larger start and transports the logarithmic band from M to each
nonempty slice. No bounded endpoint ratio is used on the macroscopic domain.

| Module and declaration | Actual conclusion |
|---|---|
| `WholeRelationProfile.theorem_three_one_raw_macroscopic` | Complete start raw profile on `[ceil(M^delta),M)`. |
| `WholeRelationProfile.theorem_three_one_coarse_macroscopic` | Coarse start profile after weighted arithmetic–geometric mean. |
| `WholeRelationProfile.proposition_three_twenty_six_raw_macroscopic` | Raw full-value profile, including the true host correction. |
| `WholeRelationProfile.proposition_three_twenty_six_coarse_macroscopic` | Coarse full-value profile. |
| `WholeRelationProfile.proposition_three_twenty_seven_start_macroscopic` | Same-cap start profile, all real T>=0 after the threshold. |
| `WholeRelationProfile.proposition_three_twenty_seven_value_macroscopic` | Same-cap full-value profile. |
| `DyadicRelationProfile.jointDefectMass_separated_le_coarse_eventually` | Actual separated defect sum used in the finite factorial-moment identity. |
| `RelationProfileRestriction.value_relationRho_cutoff_eq` | Full-value nullity independent of any adequate prime cylinder. |
| `BoundedRatioRelationProfiles.raw_masses_le_profile_boundedRatio_eventually` | Joint start/full raw profile for arbitrary masks in `[N,M)`, M<=kappa*N. |
| `BoundedRatioRelationProfiles.coarse_masses_le_profile_boundedRatio_eventually` | The corresponding coarse profile, normalized at N. |
| `BoundedRatioRelationProfiles.capped_masses_le_profile_boundedRatio_eventually` | Joint start/full capped profile, with threshold before M,L,mask,cylinder,T. |
| `BoundedRatioRelationProfiles.*_dyadic_eventually` | Three explicit specializations to `[N,2N)`. |

The ratio parameter kappa is a fixed natural number. This includes any
fixed real upper ratio by taking an integer majorant. No ratio is assumed
between the two individual coordinates within a macroscopic pair.

## Corollaries 2.5, 2.6 and local pairs (batch 9)

`PointwiseStartBounds` proves both displayed pointwise inequalities of 2.5
for every affine right-hand side in the true infinite model. The boundary
of a relation is supported on actual defective vertices and has even total
parity, giving the rank improvement `max(m-1,0)`.
`MacroscopicFirstMoment.corollary_two_five_macroscopic_expectation` gives
the real masked start-count integral with error `M^(1/2+epsilon)/2^L`.
Its affine version allows the right-hand side to depend on the position.
The dyadic endpoint retains the historical reciprocal-power convention.
The uniform threshold precedes the length and every mask; no critical
balance condition is used.

`MacroscopicFirstMoment.sum_fullDefectWeight_le_half_power_eventually`
also proves the summed macroscopic defect weight needed in (2.4).
`MacroscopicWordFirstMoment.corollary_two_six_macroscopic_expectation`
extends the dictionary first moment to the full macroscopic interval, with
error `(|W|/2^B)*M^(1/2+epsilon)`. The actual dictionary size and all words
are chosen after the threshold. Empty masks and dictionaries are allowed.

`TouchingPairMass.lemma_two_eight_overlap` is deterministic exclusion for
`0<dist(x,y)<L`. The `_dyadic` and `_macroscopic` endpoints prove the
actual ordered touching sum `sum 2^rho <= N^(1+epsilon)` or `M^(1+epsilon)`.
The cylinder may be any adequate cutoff. The transfer to the retained
`TouchingMass.touchingMass` is explicit, preserving the offset minus one
and both orientations.

## Corollary 4.4: genuine infinite-model moments (batch 9)

`CriticalVarianceMoments.corollary_four_four` states, for each C>=0 and
epsilon>0, a common N0 before every N>=N0 and natural L with
`abs(L-log(N)/log(2))<=C`:

```text
|infiniteCountMean - lambda|             <= N^(-1/2+epsilon)
|infiniteCountFactorialMoment-lambda^2|  <= N^(-1/3+epsilon)
|infiniteCountVariance-lambda|           <= N^(-1/3+epsilon)
lambda = N/2^L.
```

All three quantities are the actual integrals defined in
`InfiniteCountMoments`, which proves integrability and exact finite-cylinder
transfer. The finite second factorial baseline is exactly
`N*(N-1)/2^(2L)`, and its correction to lambda squared is `-N/2^(2L)`.
`CriticalProfileNormalization` retains `Q=2^(L+1)=2*2^L` when dividing the
coarse profile by the joint baseline denominator. Variance follows from the
exact centered-square identity and the two moment errors. No unbounded
moment is inferred from total variation convergence.

## Dependencies, audit and historical boundary

`PaperCV282/Audit.lean` covers all 830 named declarations in the 115 mathematical modules, including all 12 named local instances. Batch 9 adds 182 theorems and 29 definitions/instances; the complete per-module counts are in the source manifest.

The source inventory and kernel-axiom transcript are checked separately by
`scripts/check_v282_audit.py`. Failure-path tests exercise missing entries,
duplicate entries, forbidden dependencies and unsupported declaration forms.
The complete module list and every named local instance are in the source
manifest. Coverage alone is not a replacement for Lean's kernel check.

The original PDF hashes and Lean/mathlib versions are listed in
[`source_manifest.json`](source_manifest.json). The historical `PaperC`
core, earlier `PaperCV11` overlay and prior Palomar records keep their
original identities and scope. No new Palomar or Comparator qualification,
or certification of the complete v2.8.2 PDFs, is claimed by this ledger.
