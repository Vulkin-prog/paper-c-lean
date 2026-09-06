# Paper C v2.8.2 endpoint ledger

The 365 mathematical modules contain **3201 named declarations: 2467 theorems, 555 definitions and 179 named instances**. Batch 16 adds 292 theorems in 46 new modules.

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

`PaperCV282/Audit.lean` covers all 3,201 named declarations in 365 mathematical modules, including 179 named instances. Batch 16 adds 292 theorems, 89 definitions and 19 named instances.

The source inventory and kernel-axiom transcript are checked separately by
`scripts/check_v282_audit.py`. Failure-path tests exercise missing entries,
duplicate entries, forbidden dependencies and unsupported declaration forms.
The complete module list and every named instance are in the source
manifest. Coverage alone is not a replacement for Lean's kernel check.

The original PDF hashes and Lean/mathlib versions are listed in
[`source_manifest.json`](source_manifest.json). The historical `PaperC`
core, earlier `PaperCV11` overlay and prior Palomar records keep their
original identities and scope. No new Palomar or Comparator qualification,
or certification of the complete v2.8.2 PDFs, is claimed by this ledger.

## Batch 10: scalar and field Poisson transfer, soft retention and cutoff analysis

The literature boundary of this batch is explicit in
[LITERATURE_INPUTS.md](LITERATURE_INPUTS.md). `ScalarSteinFactorsStatement`
asserts only the positive-rate Stein solutions and their two norm bounds.
`ProcessAGGStatement` is the published finite process theorem, distinct
from the historical coarse scalar interface. `PrimeNumberTheoremRemainder`
asserts the ordinary prime-counting remainder relative to `Ei(log t)`.
They are theorem arguments, not new Lean axioms. The deductions described
below do not constitute proofs of those three external propositions.

### Genuine masked scalar transfer (article 4.1)

For `p=2^(-L)`, `G=A\D_Y`, `mu=|G|p`, the proved bound is

```text
p*(M_B(A) + 2*|A intersect D_Y|)
 + 2*min(1,1/mu)*p^2*(|A| + E_Y(A) + R2(A)),
```

with the factor interpreted as one at zero. `M_B(A)` retains the actual
mask's complete-vertex defect mass. `D_Y` includes the root `x-1`.
`E_Y(A)` counts the ordered support edges of the whole mask, and `R2(A)`
uses the genuine separated-pair nullity. The resulting stronger local
budget implies the full-block presentation in the article. No replacement
of `mu` by the ambient mean is made.

| Declaration | Established result |
|---|---|
| `MaskedArithmeticGeometry.fullBadStarts` | The whole-support deletion rule, including `x-1`. |
| `GoodTouchingProbability` | Exact `p^2` for touching good starts under the common cutoff. |
| `MaskedArithmeticCosts.average_stein_terms_le_twice` | Actual `b1` and mean `b2` controlled by the mask's cardinality, edges and full relation mass. |
| `MaskedScalarTransfer.theorem_four_one_scalar_conditional` | Mean half-L1 distance of the complete conditional count to `Pois(|A|p)`. |
| `MaskedScalarTransfer.theorem_four_one_scalar` | The same bound after unconditional mixing. |
| `InfiniteMaskedScalarTransfer.theorem_four_one_scalar_infinite` | The law of the actual masked count under the infinite Rademacher model. |
| `MaskedScalarFullConditioning.theorem_four_one_scalar_full_FY` | Actual conditional source-atom ratios and equality of the represented sigma-algebra with all primes at most `Y`, for every admissible `Y`. |

The final atom cylinder is `max(Y,dyadicCutoff N L)`. Thus no small-prime
coordinate is silently missing when `Y` exceeds the event cylinder. In
that case every masked site is bad, and a direct whole-count deletion
proves the bound. The atoms have exactly uniform positive source mass.
The finite conditions `N>=2`, `L>0`, `2L<=Y` include the manuscript's
`Y>2(L+1)` range without restricting the ambient intensity or mask size.

### Soft retention (companion B.2)

`SteinLocalTelescoping.local_stein_error_le` proves the outside-neighbourhood
factorization and each good-site telescoping estimate. The exceptional
sum is bounded by the zeroth Stein factor. `SteinTestTotalVariation`
identifies the supremum over test sets with the exact half-L1 metric.
Zero target rate has its own explicit Stein solution proved internally.

`ScalarPoissonBounds.lemma_b_two_finite` and
`SoftConditionalPoisson.lemma_b_two_average` prove (B.4) for finite laws and
finite conditioning environments. `SoftMeasureAverage.lemma_b_two_integral`
extends the averaging to any probability environment with measurable
finite conditional joint laws. It proves total-variation measurability
and integrability before integrating; dependency and good-marginal
conditions are required only almost everywhere. The representation takes
these conditional joint laws as input; it does not automatically build a
conditional-expectation object or kernel from an arbitrary presentation.

`AllStartSoftPoisson.average_full_count_soft_poisson_le` instantiates the
lemma on the actual conditional family of all dyadic sites.
`SoftGraphDegree.actual_neighbour_marginal_sum_le_defects` controls the
neighbour term through the true all-site degree and first moment. Bad
neighbours keep their actual marginal and joint probabilities throughout.
This established the soft lemma and its finite model application in batch 10.
Batch 11 below completes the optimized full-band rates of Theorem 4.3.

### Actual exponential integral and implicit saddles

The eight `Saddle*` / `ExponentialIntegral*` modules define the upper branch
`u>=1` of `exp(u)/u=nu`, the standard normalized exponential integral and
`D(nu)=nu*u(nu)-Ei(u(nu))`. Existence and uniqueness of the positive
solutions `V_a=a D(H/V_a)` within the upper-branch domain `H/V_a>=exp(1)` are proved for every fixed `a>0` and all
sufficiently large `H`. No asymptotic formula for `Ei` or saddle existence
is an external premise.

`SaddleExpansion.saddle_cutoff_second_order` proves

```text
V_a(H)^2/H - (a/2)*(log H + log log H - log(2a) - 2) -> 0.
```

The cases `a=1` and `a=2` are exactly (4.6)–(4.7).
`SaddleScales.tendsto_soft_div_hard_saddle` proves the ratio `sqrt(2)`;
`tendsto_log_div_saddleNu` proves `log H=o(H/V_a)`.
The corollaries on `H=log N` use the actual natural-to-real logarithmic
scale. The parameter `a` is fixed before the limit, as required for the
two manuscript saddles.

### Rankin, PNT and a genuinely free cutoff (article 4.2 / companion B.1)

`DefectiveRankinCount` counts the actual positive defective integers by
their canonical square/squarefree-smooth factorization. `PrimeEulerRankin`
identifies the finite Euler product and bounds its logarithmic correction.
`PrimeEulerAbel` proves the exact identity with the actual prime-counting
step function. `PrimeEulerPNT` introduces only the source-shaped PNT
remainder and proves its weighted integral estimate, retaining both
endpoints. `PrimeEulerLowerSplit` controls `Ei` near zero, including the
logarithmic lower endpoint that moves with the Rankin exponent.

`PrimeEulerUniform` deduces the normalized error of the genuine weighted
prime sum and of the genuine log Euler product. `PrimeEulerFreeScales`
proves the required scalar hypotheses uniformly on a broad power band.
Consequently `PrimeEulerFreeCutoff.euler_errors_sqrt_log_band_of_pnt`
chooses a threshold before every `w` in each fixed positive band
`c*sqrt(H log H) <= w <= C*sqrt(H log H)`. The cutoff is exactly
`floor(exp w)`; no floor error is omitted.

`BadStartRankinFreeCutoff.normalized_fullBadMask_free_cutoff_le_eventually`
then proves

```text
|A intersect D_floor(exp w)|/N <= exp(-D(log N/w) + epsilon*(log N/w)),
```

with one threshold before `w`, `L` and the deterministic mask, on every
fixed logarithmic upper band for `L+1`. The full-block case is included.
The analogous `normalized_defectiveValues_free_cutoff_le_eventually`
is the actual integer count in B.1. Separate saddle-specialized endpoints
are retained for later probability-rate assembly.

The graph bounds use the literal all-site graph, including defective
starts. `CutoffGraphCompatibility` identifies its open and closed degrees
with the arithmetic neighbour sets; the closed degree adds exactly one.
The finite bound is proved without PNT and is uniform before the mask.


### Joint field on the same site lattice (article 4.1)

`FiniteFieldTotalVariation` works on the actual natural-valued finite-site
vector space. Finite pushforwards and product-Poisson masses have proved
mass one; no finite instance is imposed on the infinite vector state space.
`FiniteFieldPoissonCoupling` proves rate perturbation by the sum of absolute
rate differences and both actual-site and target-site deletions with
coefficient one.

`AllStartFieldCosts.bOne_fullGood_allStart_eq` and
`bTwo_fullGood_allStart_eq` identify the costs on the all-site carrier with
the previously bounded retained carrier. This is an exact transport of
indicators that are zero outside the retained mask, not an assumed
arithmetic budget. `AllStartFieldTransfer.average_allStart_field_le_arithmetic`
then bounds the complete conditional field by

```text
p*(M_B(A) + 2*|A intersect D_Y|)
 + 2*p^2*(|A| + 2*E_Y(A) + R2(A)).
```

This is the joint-field form of (4.3), with an absolute constant and no
intensity factor. Its target has rate `p` on the mask and zero elsewhere
on the same finite dyadic lattice.
`InfiniteFieldTransfer.theorem_four_one_field_full_FY` proves the bound
for true source-atom conditional vector laws and identifies the entire
`F_Y`, using the adequate cylinder `max(Y,dyadicCutoff)`. The large-cutoff
case uses actual whole-field deletion. Every conditional ratio is a
normalized law. `theorem_four_one_field_unconditional` gives the same
budget for the actual infinite vector law after mixing.

### All-site degree and edge closure (article 4.2)

`CutoffGraphFreeCutoff.normalized_degree_and_edges_free_cutoff_le_eventually`
proves, without PNT, both the actual maximum-degree bound after division
by `N` and the ordered masked-edge bound after division by `N^2`, with a
threshold before all cutoffs in the free square-root band, all admissible
lengths and all dyadic masks. The resulting bound is
`exp(-w + epsilon*(log N/w))`. In that band `w<=log N` eventually, so the
finite `1/N` contribution is absorbed into this larger envelope. This
implies the degree and edge presentation of (4.5) and completes the
cutoff conclusions together with the Rankin and saddle results above.

## Batch 11: full-band hard/soft rates and arithmetic-event conditioning

Source: article Theorem 4.3 and equations (4.8)–(4.10), printed page 29;
companion B.3, pages 8–9; scalar information formulas in article section
6.1, pages 38–39. The only literature arguments of the new asymptotic
endpoints are `ScalarSteinFactorsStatement` and
`PrimeNumberTheoremRemainder`. The process AGG premise used by earlier
field theorems is not required here.

Write `lambda=N/2^L`, `H=log N`, `w_h=V_1(H)`, `w_s=V_2(H)` and
`nu_a=H/V_a(H)`. For every fixed logarithmic band, epsilon>0 and eta>0,
one threshold is chosen before the natural run length. The cutoffs are
exactly `floor(exp(w_h))` and `floor(exp(w_s))`. Their admissibility, their
inclusion in the count's prime cylinder and equality with the entire
conditioning field `F_Y` are proved, rather than assumed.

| Declaration | Established result |
|---|---|
| `FullBandArithmetic.fullDefectMass_div_block_le_eventually` | Actual complete-vertex mass `M/N <= N^(-1/2+epsilon)`. |
| `FullBandArithmetic.normalized_relation_mass_le_eventually` | Actual separated relation mass `R/2^(2L) <= N^(-1/3+epsilon)*(lambda^2+2lambda)` without bounded intensity. |
| `FullBandArithmetic.touching_mass_le_eventually` | The actual homogeneous touching mass in the same dyadic cylinder. |
| `SaddleCutoffAdmissibility.saddleCutoff_nat_admissible_eventually` | Integer cutoffs contain the required short supports and lie inside the cylinder, uniformly before L. |
| `SaddleArithmeticBounds.normalized_fullBadMask_saddle_cost_le_eventually` | Actual full-support bad mass at either saddle, with arbitrary deterministic submask. |
| `SaddleArithmeticBounds.normalized_degree_and_edges_saddle_le_eventually` | Actual all-site degree and ordered edges, with no PNT premise for these two bounds. |
| `HardPoissonBounds.half_rate_le_retainedRate` | Actual retained mean is at least half the full mean once the bad fraction is at most one half. |
| `SoftArithmeticCosts`, `SoftArithmeticTransfer` | Full good-to-all neighbour ledger: bad neighbours keep their actual marginal and joint probabilities; overlaps, touching and separated pairs have distinct proved bounds. |
| `DyadicPoissonDistance.conditionalDistance_eq_source_atom_average` | The mean distance is exactly the average of the positive source-atom measure-ratio laws. |
| `HardPoissonRates.theorem_four_three_hard` | Equation (4.8) for both the true source count and the mean conditional distance, with constant 20 and the entire expression multiplied by lambda. |
| `SoftRateAssembly.theorem_four_three_soft` | Equation (4.9) for both laws, at the soft cutoff, with constant 6, all intensities and a minimum with one. |
| `FreeCutoffSoftRates.free_soft_ledger_eventually` | Free-cutoff ledger with the two independent costs `exp(-D(H/w)+eta*H/w)` and `exp(-w+eta*H/w)`, retaining `max(1,lambda)`. |
| `FreeCutoffSoftRates.equation_four_ten` | The three printed terms with coefficients 2, 3, 6 under `lambda>=1` and `log lambda<=A*w`, uniformly for each fixed square-root cutoff band. |

Explicitly, the two optimized upper bounds are

```text
20 min(1, lambda*(exp(-w_h+eta*nu_h) + N^(-1/3+epsilon))),
 6 min(1, exp(-(w_s-max(0,log lambda))/2+eta*nu_s) + N^(-1/3+epsilon)).
```

The quantification over every positive eta represents the little-o
exponential error; no computable threshold or optimality assertion is
made. The normalized costs are the actual `M/N`, `D/N`, `E/N^2`,
`Delta/N`, `R/2^(2L)` and `T/N^2`. In particular the proof does not replace
a bad neighbour's probability by the good marginal.

The soft proof also covers lambda<1 directly by the same soft calculation.
In the nontrivial branch `ell=max(0,log lambda)<=w_s`, so the intensity
envelope can be absorbed in a small power of N. This preserves the exact
soft `F_Y`; it is the demonstrated simplification recorded as V3-S009.

### Genuine convergence regimes

`PoissonRateConvergence.hard_convergence_of_bounded_intensity` proves
convergence to zero of the hard conditional mean distance and the actual
count distance for every bounded-intensity sequence in the fixed band.
`soft_convergence_of_margin` proves the two soft conclusions under
`log^+ lambda <= w_s-c*nu_s`, for fixed c>0.
`soft_convergence_at_hard_endpoint` includes
`log^+ lambda <= w_h+K`, for any fixed K. The numerical saddle limits
are separately established in `SaddleRateConvergence`. These conclusions
are limits of total-variation distances and conditional averages, not
almost-sure convergence of conditioning kernels. No convergence at the
exact soft boundary `log lambda=w_s` is asserted.

### Positive events in the chosen prime field

`PrimeFieldEventConditioning` represents every event of the finite prime
sigma-algebra as a union of its source atoms and proves the true event
probability. `RestrictedPoissonTransfer.restrictedCountLaw` is literally
`P(Z=k and E)/P(E)`. Its normalization and the exact selected-atom mixture
are proved. For E measurable in the chosen `F_Y` with P(E)>0,
`event_tv_le_conditionalDistance` bounds its distance by the averaged
conditional distance divided by P(E).

`RareConditioningRates` defines `I=-log P(E)`, proves I>=0 and
`exp(I)=1/P(E)`, and obtains the hard and soft restricted rates at their
respective cutoffs. `hard_event_rate_min_eventually` and
`soft_event_information_min_eventually` put the minimum with one after
the inverse-probability cost, yielding the scalar formulas (6.1)–(6.2).
The soft information ledger has leading term
`exp(-(w_s-(2I+log^+lambda))/2+eta*nu_s)` and polynomial term
`exp(I)*N^(-1/3+epsilon)`.
`soft_event_margin_bound_eventually` chooses a threshold before both L
and E. Under `2I+log^+lambda<=w_s-c*nu_s`, it gives the vanishing bound
`6*(exp(-c*nu_s/4)+N^(-1/6))`.
`soft_event_convergence_of_information_margin` applies this to moving
positive events and run lengths in the true source model.

This is the scalar finite-prime-event specialization of the conditioning
argument and its actual rate consequences. It does not yet prove the
standard-Borel product lift with an extra recorded random variable in
Lemma 6.1, conditioning on a run statistic, resolved states, a labelled
or aggregated marked path, or the remaining results of sections 5–7.
B.3 is an application subsection, not an additional numbered companion
result.

## Theorem 5.1: complete site-and-word dictionary field

Source: article pages 30–31, equations (5.1)–(5.7). Write `B=L+1`,
`m=card W`, `a=m/2^B`, and `Lambda=N*a`. `W` is a nonempty finite set
of prescribed binary words. Every bit, including the bit at `x-1`, is
prescribed. The field carrier is the product of the actual dyadic sites
and the actual dictionary words; no labels are discarded.

| Declaration | Established result |
|---|---|
| `WordOverlap.Compatible` | Literal directed suffix/prefix equality at a proper shift. |
| `WordOverlapProbability.equation_five_five_finite` | True local conditional joint probability, `2^(-(B+d))` for compatible words and zero otherwise, when the union is good. |
| `WordOverlapSum.overlapWeight` | Exact normalized directed sum, including self- and cross-overlaps. |
| `WordOverlapSum.orderedLocalMass_le` | Actual ordered local joint mass at most `2*card(mask)*a*Omega`. |
| `DictionaryFieldModel.DictionaryIndex` | Entire site-and-word carrier. |
| `DictionaryFieldDependency.hasExactDependencyGraph_maskedWordIndicator` | Exact dependency graph after fixing small-prime coordinates, including independence from the whole outside pattern. |
| `DictionaryMarginalCap.dictionary_joint_cap` | Actual grouped joint probability at most `min(a,a^2*2^rhoValue)`, then at most `a^2*(1+min(1/a,2^rhoValue-1))`. |
| `DictionaryFieldDeletion.average_bad_word_mass_le` | Genuine removed source mass at most `a*(Mval(mask)+card(bad mask))`. |
| `DictionaryFieldFirstCost.bOne_dictionary_le` | True first process cost at most `a^2*(2*N*B+E_Y(mask))`. |
| `DictionaryFieldSecondCost.average_bTwo_dictionary_le` | Mean second cost at most `2*Lambda*Omega+a^2*(E_Y(mask)+Rcap(mask))`. |
| `DictionaryFieldBounds.equation_five_seven` | True conditional full-field distance bounded by `a*(Mval+2*Dval)+4*a^2*(N*B+E_Y+Rcap)+4*Lambda*Omega`. |
| `DictionaryProfileNormalization.normalized_cappedProfile_le` | Exact normalization of the capped profile to the three dictionary monomials. |
| `DictionaryErrorLedger.dictionary_ledger_hard_rate_eventually` | Actual arithmetic ledger bounded by eight times the printed three-term error, uniformly before cardinality and overlap. |
| `DictionaryFieldInfinite.conditionalDictionaryLaw_eq_infinite_atom_ratio` | Every conditional field mass equals the actual infinite-source ratio on its positive prime atom. |
| `DictionaryFieldInfinite.infiniteDictionaryLaw_eq_finiteFieldLaw` | Exact infinite-source law on an adequate finite cylinder. |
| `DictionaryFieldRates.allWordRates_full_eq` | Every target coordinate has rate `2^(-B)`. |
| `DictionaryFieldRates.theorem_five_one_full_band` | Equation (5.2) for the true mean full-F_Yhard conditional distance and unconditional distance, with absolute multiplier 8. |
| `DictionaryFieldCritical.equation_five_four` | Equation (5.4) from the literal window and cardinal bound, for both true distances. |
| `DictionaryFieldCritical.dictionary_field_critical_convergence` | Both distances tend to zero for growing dictionaries satisfying (5.3). |

The cutoff is exactly `floor(exp(Vhard))`. Its upper bound by the cylinder
and lower bound by `2*B` are proved from saddle admissibility. Consequently
the represented sigma-algebra is all `F_Yhard`, rather than an incomplete
subset of its primes. Each fixed positive `eta` gives the remainder
`exp(-Vhard+eta*nuhard)`; its threshold is uniform before `L`, `W`, and `m`.
No upper bound on `m` is needed for the full-band result.

For the critical result, `m<=N^(1/2-delta)` and
`abs(B-log2(N*m))<=C` imply bounded intensity and a fixed logarithmic band.
Taking `epsilon=delta/6` bounds the polynomial contribution by `N^(-delta/2)`.
The constant is `8*criticalDictionaryConstant(exp(C*log 2))`, independent
of the words and their number. The convergence is unconditional and in
mean conditional total variation; no almost-sure kernel limit is asserted.

The only literature arguments are `ProcessAGGInput.ProcessAGGStatement`
and `PrimeEulerPNT.PrimeNumberTheoremRemainder`. Marginals, deletion costs,
local compatibility, the grouped marginal cap, complete-value ranks and
arithmetic profiles are actual proved quantities. Scalar Stein factors
are not required by these dictionary endpoints.

## Deterministic restrictions and statistics of the dictionary field

The discrete state space of the Poisson field is infinite; it is never
given a fictitious finite-type instance. The following results apply to
an arbitrary function from that field into any type, so in particular to
every deterministic restriction of the site-and-word carrier.

| Declaration | Established result |
|---|---|
| `MassPushforward.hasSum_pushforwardMass` | Exact mass preservation under fibre summation. |
| `MassPushforward.massTotalVariation_pushforward_le` | Contraction of half-L1 total variation for normalized nonnegative masses. |
| `DictionaryFieldStatistics.pushforward_infiniteDictionaryLaw_eq` | The image mass is exactly the true source law of the composed statistic. |
| `DictionaryFieldStatistics.pushforward_conditionalDictionaryLaw_eq_atom_ratio` | Exact source-atom ratio for every composed statistic. |
| `DictionaryFieldStatistics.full_FY_statistic_representation` | Full prime-sigma-algebra representation when the adequate cylinder also contains the cutoff. |
| `DictionaryFieldStatistics.infinite_statistic_distance_le` | True statistic distance bounded by the full field distance. |
| `DictionaryFieldStatistics.average_source_statistic_distance_le` | Mean true conditional statistic distance bounded by the full conditional distance. |

Composing these inequalities with the full-band and critical endpoints
preserves their constants and thresholds, and gives convergence for every
chosen sequence of deterministic restrictions or statistics. The target
is always the image of the same independent Poisson field. This does not
prove the general stable product lift of Lemma 6.1 with a recorded random
environment. Batch13 separately proves the Poisson target identities
particular to Corollaries5.2 and5.5, as recorded below.

## Corollary 5.4: explicit dictionaries without proper overlaps

Source: article page 32. The family is the actual finite filter of words
`0^k 1 u 1` whose middle contains no block of `k` zeros. Here
`k=floor(log2(2*B))+1`. At exact powers of two this is one larger than the
printed ceiling, and the same conclusion follows from `2*B<2^k<=4*B`.

| Declaration | Established result |
|---|---|
| `MarkerDictionary.wordOfMiddle_not_compatible` | All proper directed overlaps are excluded, including a word with itself. |
| `MarkerDictionaryCount.eraseBlock_injective_on_zeroBlockWords` | The actual fixed-zero-block family injects into its remaining coordinates. |
| `MarkerDictionaryCount.two_pow_le_two_mul_card_admissibleMiddles` | The union bound leaves at least half the possible middle words. |
| `MarkerDictionaryAsymptotics.corollary_five_four` | Explicit family of size at least `2^B/(32*B)` for every `B>=8`, with no proper overlaps and zero overlap weight for all subsets. |
| `MarkerDictionaryCritical.marker_capacity_critical_eventually` | The true critical window eventually implies `B>=8` and enough capacity for the requested cardinality. |
| `MarkerDictionaryCritical.critical_subdictionary_exists_eventually` | Actual selection of any requested critical cardinality with `Omega=0`, uniformly before length and size. |

No external coding theorem is assumed. The marker construction's elementary
injection, union bound and logarithmic capacity estimate are internal.
The remaining dictionary consequences5.2,5.3 and5.5 are now completed below.

## Corollary 5.2: replacement by the actual iid sequence

Source: article pages31–32. IidWordField constructs real independent fair bits
on integer coordinates and proves exact word and compatible-joint probabilities.
IidWordDependency.hasExactDependencyGraph_iidWordField proves independence
from the entire outside pattern for the graph of overlapping windows.
IidWordCosts derives b1≤2NBa² and b2≤2ΛΩ. The explicit process AGG argument
gives IidWordPoisson.infinite_iid_poisson_distance_le with rate
4(ΛΩ+Λ²B/N). No arithmetic assumption is used in these iid costs.

IidWordInfinite.infiniteIidFieldLaw_eq_iidFieldLaw identifies this law with
the field of the actual infinite independent coordinates omega n.
IidWordComparison.corollary_five_two compares both genuine fields with the
same site-word Poisson product and proves TV→0 under(5.3).
Its corollary_five_two_word_counts gives convergence of the actual vector
of word counts to independent Poisson variables of meanN2^(-B), allowing
the number of words to grow.

PoissonFieldMeasure constructs the genuine product measure on count vectors.
PoissonFieldAggregation.hasLaw_columnField and hasLaw_column_sums prove
rearrangement and mutually independent column sums. DictionaryCountTargets
proves the exact pushforward targets for dictionaryWordCounts and
maskedDictionaryCount, then contracts the actual unconditional and averaged
conditional source laws. These are full-law identities, not just marginal
mean calculations or pairwise independence assertions.

## Corollary 5.3: uniform dictionaries without replacement

Source: article page32, equation(5.8). RandomDictionary.uniformDictionaryPMF
is the equal probability law on the actual m-subsets of the2^B words;
its expectation and event probabilities are exactly dictionaryAverage and
dictionaryFraction. RandomDictionaryIndependence constructs its product with
any finite multiplicative source cylinder and proves factorization against
any observation of that source. No extra randomness is needed to apply the
field theorem to a chosen dictionary.

RandomDictionaryWordCount proves the real self-overlap and completion counts.
At each positive proper shift the weighted diagonal sum is1 and the weighted
distinct-pair sum is2^B−1. Exact without-replacement inclusion counts yield
RandomDictionaryOverlap.average_overlapWeight_eq:

    E_W Ω(W) = m(B−1)/2^B,  1≤m≤2^B.

This strengthens the printed inequality, which is also proved in
equation_five_eight. dictionaryFraction_overlapWeight_gt_le is Markov for
the true sampled event. RandomDictionaryCritical.corollary_five_three_exceptional_fraction
bounds the fractionΩ>N^(-1/2) by a constant timeslogN/√N, uniformly beforeB,m
in the literal critical window. nonexceptional_dictionary_field_rate gives
every remaining dictionary the conditional and unconditional bound(5.4),
withΩ replaced byN^(-1/2). Only this arithmetic application uses AGG/PNT.

## Corollary 5.5: low-overlap words up to a common sign

Source: article page33, equations(5.9)–(5.10). SignDictionary.oppositeWord
is the complement1+a inF₂; additive negation inF₂ would be incorrect.
The two words are distinct for positive length and their actual occurrence
events are disjoint. SignOverlap.overlapWeight_signDictionary provesΩ=Θ.
The module provesΘ≤2^(1−d*) and its convergence when the least compatible
shift diverges; runStartWord_compatible_iff and theta_runStartWord prove
that the word(-,+,…,+) has only shiftL and weight2^(-L).

SignPatternRates.sign_field_rate_eventually uses the exact window
|L−log₂N|≤C and preserves theN^(-1/3+ε) error with fixedm=2.
SignPatternCounts.maskedDictionaryCount_sign_eq identifies the field sum
with the genuine count of the disjoint union of the two source events.
corollary_five_five proves the rate for every deterministic maskA⊆[N,2N),
with exact targetPois(|A|2^(-L)), for the unconditional distance and mean
conditional distance. signPatternRate_dyadic specializes the mean toN2^(-L).
masked_sign_count_convergence derives the masked convergence from divergence
of the least compatible shift, for arbitrary sequences of deterministic masks.

All thresholds precedeL, the word and the mask. Each positiveeta quantifies
the exponential remainder. AGG of processes and PNT remain explicit theorem
arguments; no new literature premise, stable-product lift or almost-sure
conditional convergence is claimed by this batch.


## Theorem 5.6: finite exact marks, signed and unsigned

Source: article pages 33–34, (5.11)–(5.15). `L≥1`, `0≤e≤E`,
`Q=L+E+1`. The actual signed word has `L+e+2` values, including
both changes, with the sign read at x. Its marginal is `2^(-L-e-2)`;
summing signs gives `2^(-L-e-1)`. Maximal support vertices are
`x−1,…,x+Q−1`, with Q+1 actual values.

| Declaration | Established result |
|---|---|
| `SignedExactMarks.conditioned_signedMark_probability` | Actual exact marginal, uniform in the represented small-prime assignment. |
| `ExactMarkedLocalProbability.conditioned_signed_pair_le_four` | True short-union joint probabilities, with all four compatibility cases proved. |
| `LabelledSupportGraph.hasExactDependencyGraph_of_labelled_locality` | Complete outside-pattern independence, arbitrary finite labels and free cylinder C. |
| `ExactMarkedDependency.hasExactDependencyGraph_signed` | Instantiation on actual signed exact events and maximal supports. |
| `ExactMarkedAggregation.sum_signed_joint_probability_le_base` | Sum both labels before bounding by the base two-start probability. |
| `ExactMarkedDeletion.average_bad_signed_mass_le` | Actual deletion dominated by base-L defects, even when the bad vertex occurs later. |
| `ExactMarkedPairCosts.average_bTwo_signed_le` | Bound `[8N(Q+1)+edges_Q+R2_L]/2^(2L)`, without a mark-cardinality factor. |
| `ExactMarkedInfinite.signed_fullFY_identification` | True source atom ratios and full F_Y when C covers both the observation and Y. |
| `ExactMarkedSignProjection.pushforward_signed_target` | Sum only the two signs at each site/excess, obtaining the exact unsigned Poisson product. |
| `ExactMarkedFiniteComparison.equation_five_thirteen` | Explicit constant40 times the five printed terms, both conditional and unconditional fields, and explicit full-F_Y identity. |
| `ExactMarkedFiniteComparison.theorem_five_six` | Both fields with bound32λ(1+λ)[exp(−V+ην)+N^(−1/3+ε)], threshold before L,E in the full logarithmic band. |

The finite process estimate assumes only ProcessAGGStatement. The rate adds
PrimeNumberTheoremRemainder. Its free C can be chosen as max(Y,dyadicCutoff(N,Q));
no partial prime cylinder is silently identified with full F_Y. Defect mass and
R2 always use the base L, while deletion and support edges use Q.

## Corollary 5.7: the actual compound-Poisson cluster law

Source: article pages 34–35. `ConstantWindowClusters` defines the genuine
constant-window count without a left-maximality requirement. Outside the
windows beginning at N and2N−1 it equals the full weighted sum of exact
marks. `ConstantWindowRates` proves that the probability of the two actual
boundary events vanishes in the literal window `|L−log₂N|≤C`.

`CompoundPoissonTarget` constructs a true product of a Poisson count and
an infinite iid mark sequence, proves independence, and takes the finite
initial random sum. `GeometricClusterTarget` shifts the geometric law to
positive integers, proves mass2^(-h) for h≥1, and proves
`geometricCompound_pgf = exp(λ*(z/(2−z)−1))`, for0≤z≤1.

`GeometricClusterTruncation.weightedGeometricPoisson_eq_compound` identifies
the weighted finite Poisson field with the actual compound construction
whose large marks are suppressed. `ExactMarkedClusterTarget` aggregates
all positions and signs with exact intensity λ=N/2^L. The source counterpart
is `ExactMarkedClusterTransfer.truncated_source_to_compound_tv_le`.

`ExactMarkedSourceTail.source_mark_tail_le_eventually` gives the true tail
bound λ2^(-E−1)(1+N^(-1/2+ε)) with a threshold before both lengths.
`ExactMarkedTailTarget.compound_target_truncation_tv_le` gives the independent
target tail λ2^(-E−1). `ConstantWindowCompoundConvergence.corollary_five_seven`
combines boundary, finite-field and both tail comparisons: the true window
count law is o(1) in TV from the stated compound law, with its exact varying λ_N.
No moment convergence is inferred from the unbounded weighted sum.

`CompoundPoissonMarking` additionally proves the joint product law of all
finite categories. `GeometricMarkedConfiguration` constructs the aggregated
countable excess configuration on ℕ→₀ℕ with its finite projection laws and
compound total weight. At the end of batch14, the complete spatial field
and weak diffuse limit of introductory1.1 were not yet claimed. Batch15
closes these and the labelled part of5.9 below; batch16 proves the signed comparison below; printed C.1 remains partial.


## Batch 15: complete spatial field and Theorem 1.1

Source: article page3, Theorem1.1/(1.3), and pages33–35, (5.11)–(5.16).
`SpatialMarkedConfig N` is the countable space `(Fin N × (ℕ × F₂)) →₀ ℕ`.
The site i represents x=N+i, and F₂ encodes the two signs.
`SpatialMarkedSource` constructs the actual full field on the infinite prime
probability space. Its projection at every finite excess cutoff equals the
previous actual signed field. Finite support and measurability are proved,
and almost-sure run termination identifies its full total with the start count.

| Declaration | Established result |
|---|---|
| `SpatialMarkedTargetProjection.hasLaw_projectConfiguration` | Every finite projection of the actual countable target is the independent product with atom rate2^(-L-e-2). |
| `SpatialMarkedLawExt` | Equality of complete configuration laws from all finite projections; no assumed tail convergence. |
| `SpatialMarkedFieldComparison.spatial_signed_full_band` | Complete spatial TV bounded by32 times the finite arithmetic rate and explicit geometric tails, uniformly before L,E. |
| `SpatialMarkedCritical.theorem_one_one_lattice` | For every a<1/√2, eventually TV≤exp(−a√(logN·loglogN)), uniformly before L in the critical window. |
| `SpatialMarkedStatistics.theorem_one_one_start_count` | Same coefficient and uniformity for the actual scalar start count and Pois(N/2^L). |
| `SpatialMarkedStatistics.spatial_statistic_tv_le` | Every deterministic statistic contracts the full comparison. |
| `SpatialMarkedTargetAggregation.hasLaw_totalSpatialCount` | Actual target total has exactly the Poisson law of rateN/2^L. |
| `SpatialMarkedTargetCompound` | Actual target weighted total has the geometric compound-Poisson law. |
| `SpatialMarkedTargetLaplace` | Genuine Laplace integral for the full spatial target. |
| `GeneralPoissonMarking` and `SpatialMarkedPoissonIdentification` | Actual Poisson count and independent iid marks have the complete countable product law; proved through joint category laws and finite-projection uniqueness. |
| `SpatialPointConvergence.spatialPointTargetLaw_tendsto` | True target point-measure laws converge weakly along sizes→∞ and rates→rate. |
| `SpatialMarkedDiffuse.theorem_one_one_diffuse` | The actual arithmetic source has the same genuine weak diffuse limit in the critical window along these subsequences. |

The common weak-limit space is `PointMeasure (ℝ × (ℕ × F₂))`, represented
by finite measures with the Borel structure of the weak topology. Every
actual configuration is a finite sum of natural multiples of Dirac measures
at `1+i/N`; `SpatialPointSupport` proves zero mass outside[1,2] both for
these configurations and for every sample constructing the diffuse target.
The latter is a genuine Poisson count with independent uniform positions,
geometric excesses and equiprobable signs. Uniform grid cells identify the
entire prelimit target; no fixed-truncation or Laplace-only conclusion is
substituted for weak convergence. `CountableWeakTransfer` transfers actual
integrals of bounded continuous tests using the countable lattice TV error.
No TV convergence to the diffuse law or moment convergence is claimed.

## Batch 15: labelled growing fields, 5.8(i) and labelled 5.9

Source: article pages35–36, (5.17)–(5.20). Depth d is natural and
`d/logN→0`, base b=floor(log₂N), length L=b−d. Actual full-F_Y events A
have positive probability, I=−logP(A), and Λ=N/2^L. The proof establishes
eventually L≥1 and Λ≥1; these are not extra asymptotic restrictions.

| Declaration | Established result |
|---|---|
| `SpatialMarkedEventComparison.spatial_event_tv_le_finite_and_tails` | Actual normalized restriction given A; finite error and source tail divided by P(A), independent target tail paid separately. |
| `SpatialMarkedHardBudget.theorem_five_eight_labelled_hard` | (5.18): I+logΛ+log(1+Λ)≤V−cν gives full signed spatial TV→0. |
| `SpatialMarkedMovableBudget.spatial_event_movable_rate` | (5.20): constant64 times exp(I)[Λexp(−Vsoft/2+ηνsoft)+Λ²exp(−Vsoft+ηνsoft)+Λ(1+Λ)N^(-1/3+ε)], for each 0<ε<1/3 and η>0, with threshold before L,A and no remaining tail. |
| `SpatialMarkedMovableBudget.theorem_five_eight_labelled_movable` | (5.19): I+logΛ≤Vsoft/2−cνsoft gives full signed spatial TV→0 at full F_Ysoft. |
| `GrowingLevelParameters` | Actual dyadic phase, intensities and growing-depth logarithmic band. |
| `MovingMarkedComparison.conditional_moving_source_tv_eq` | Literal signed reindexing r=e−d preserves the true conditional-field distance exactly. |
| `MovingMarkedComparison.moving_labelled_hard_tendsto_zero` and `moving_labelled_movable_tendsto_zero` | Both conclusions in the integer moving coordinates, retaining every position and sign. |
| `ThresholdPathEquivalence` | Measurable bijection between finite-mass exact levels and their full antitone threshold sequence, with finite-difference inverse. |
| `MovingMarkedComparison.conditional_start_path_totalVariation_eq` | Exact distance equality for the entire path of actual conditioned threshold counts and the aggregated exact levels. |

The rate uses a moving excess cutoff3ceil(V/log2), or its soft analogue;
its cost is o(logN), and both actual tails are absorbed. All arithmetic
comparisons assume only the already declared process AGG and ordinary PNT.
The independently proved target and reindexing results add no premise.

Batch 15 closed the labelled clauses. Batch 16 supplies the distinct aggregate
estimate and joint weak limit below. Introductory 1.1 is not counted twice.


## Batch 16: directional finite comparison related to companion C.1

The new literature argument supplies the multivariate Stein solution and
its two quadratic bounds, as specified in [LITERATURE_INPUTS.md](LITERATURE_INPUTS.md).
The comparison itself is proved. Signed categories already have dimension
two when E=0. The full target intensity is used even if no good sites remain.

| Declaration | Established result |
|---|---|
| `DirectionalHessian` | Polarization of quadratic bounds to the true entrywise minimum factor. |
| `DirectionalPoissonComparison.directional_product_poisson_comparison` | Actual independent filling and category-valued indicator counts have TV at most their weighted dependency-graph cost. |
| `PoissonFillingIdentity` and `PoissonPolynomialIntegrability` | Exact filling identities and all polynomial moments, including zero rates; legitimate integral linearity in the generator. |
| `SignedMarkedSeparatedRelations` | Mixed signed kernels embed by zero into the largest full value-relation space; true separated joint probabilities are averaged over F_Y. |
| `SignedAggregateComparison.average_finite_aggregate_le_ledger` | The genuine mean conditional aggregate TV is bounded by the actual signed comparison ledger. |
| `SignedAggregateComparison.conditional_finite_signed_aggregate_le_ledger` | Every positive event in the whole F_Y has actual aggregate distance at most that ledger/P(A). |
| `SignedAggregateRates.signed_aggregate_ledger_rate_eventually` | Full-band ledger ≤32[λ(1+log⁺(2λ)) exp(-V+ην)+2^(2E+2)λ²N^(-1/3+ε)], uniformly before L,E. |

The ledger is p(M_L+2D_Q)+p²s(λ)[10N(Q+1)+2E_Y(Q)+R_values(Q+1)],
with p=2^(-L), Q=L+E+1 and s=min(1,12(1+log⁺(2λ))/λ).
The relation profile includes all Q+1 values. Its cutoff conversion is
proved; it is never replaced by the smaller base-start profile. The support
condition is 2(Q+1)≤Y. The printed C.1 instead uses an unsigned start-relation
profile at Q and 2Q<Y: that exact finite statement remains partial, although
the enlarged signed estimate proves all aggregate consequences below.

## Batch 16: aggregate 5.8(ii), signed 5.9 and all threshold paths

| Declaration | Established result |
|---|---|
| `SignedAggregateTruncation.conditional_signedAggregate_tv_le_finite_and_tails` | True complete signed aggregate versus its independent countable Poisson target; source tail/P(A), actual finite count distance, and separate target tail. |
| `UnsignedAggregateTarget.hasLaw_aggregateExcess` | Summing positions and signs of the full spatial target gives exactly the geometric Poisson configuration at rate λ. |
| `AggregateBudgetRates.aggregate_ledger_under_budget` | Under I+logλ≤V−cν, the conditional finite ledger at E=3ceil(V/log2) is ≤exp(-c'ν)+N^(-1/3+ε), for every 0<c'<c and ε>0. |
| `SignedAggregateHardBudget.hard_aggregate_event_bound` | Both actual infinite aggregate distances are ≤2exp(-c'ν)+N^(-1/3+ε), with the threshold before L and the full-F_Y event A. |
| `SignedAggregateHardBudget.theorem_five_eight_aggregate_hard_sequences` | Both signed and unsigned aggregate distances tend to zero for arbitrary sizes→∞ and d/log(sizes)→0 under the actual hard information budget. |
| `AggregateMovingCoordinates.corollary_five_nine_aggregate_sequences` | Exact signed/unsigned reindexing on r≥−d, actual phase means2^(θ_N−r−2) and2^(θ_N−r−1), and convergence of both laws. |
| `UnsignedAggregateComparison.conditional_path_distance_eq` | Exact equality with the total variation distance of the entire actual conditioned path of threshold start counts. |

The proof uses the larger cutoff E=3ceil(V/log2). Under the one-factor
budget, the actual conditional first-moment tail is sufficient; the combined
tails are ≤3exp(-2V), hence smaller than each fixed ν-scale remainder.
This is a proof choice, not a correction to the manuscript's shorter-cutoff
argument. The enlarged profile is absorbed only after keeping its explicit
2^(2E+2) cost. No comparison retaining positions in the stronger one-factor
range is asserted.

## Batch 16: actual joint Poisson–Gaussian Theorem 5.10

| Declaration | Established result |
|---|---|
| `PoissonCLT` and `FinitePoissonCLT` | Genuine centered normalized Poisson weak limits, with arbitrary diverging real rates and finite product limits. |
| `PoissonThresholdTarget.normalizedThresholdLaw_tendsto` | True vector of all displayed tail counts; the last finite category keeps the entire infinite upper tail. |
| `PoissonGaussianLimit.jointThresholdLaw_tendsto` | Same geometric configuration supplies thresholds and critical levels. Their finite interaction is computed, then vanishes to give the independent Gaussian/Poisson limit. |
| `GaussianThresholdCovariance` and `GaussianThresholdIncrements` | Actual centered Gaussian law with covariance2^(-max(j,k)), identified with sums of independent increments. |
| `GaussianThresholdAR` | Each finite normalized Gaussian segment is stationary AR(1), with independent standard-normal innovations and coefficient2^(-1/2). |
| `PoissonGaussianCritical.theorem_five_ten_target` | Exact moving lengths, dyadic phase, arbitrary size subsequences and integer critical levels; target means2^(θ−r−1). |
| `PoissonGaussianSource.ae_actualJointVector_eq` | The normalized coordinates are literally the actual start counts; the critical coordinates count exact lengths on the same conditioned sample. |
| `PoissonGaussianTheorem.criticalExactCount_eq_eventually` | Natural excess(d+r).toNat equals the literal critical level b_N+r eventually, with no silent truncation of negative lengths. |
| `PoissonGaussianTheorem.theorem_five_ten` | Actual conditional joint weak limit under the hypotheses of5.8(ii), d→∞ and phase→θ. Vanishing source TV is derived, not assumed. |

The limit is in the topology of probability measures on the finite Euclidean
product, for every fixed J and finite R⊂ℤ. The two explicit literature inputs
are the directional Stein solution theorem and PNT. Positive conditioning
probabilities define each member of the sequence. No Berry–Esseen/local
rate, moderate-deviation estimate, or general result from D.1/D.4 is claimed.
