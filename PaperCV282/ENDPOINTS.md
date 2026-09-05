# Paper C v2.8.2 endpoint ledger

This ledger describes the current thirty-module development: 178 theorems,
36 definitions and five named local instances, totaling 219 named
declarations. It records the mathematical scope of the supplied proof terms;
build and qualification outcomes belong in separate evidence. No entry is a
new Palomar record. Names below have prefix `PaperC.V282.`.

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
endpoints do not assert a macroscopic extension beyond `[N, 2N)`.

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
assumption. It includes `A = 3` but does not identify this canonical code
with the eight sectors of the v2.8.2 manuscript, nor prove their raw
asymptotic estimates.

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

To complete Proposition 3.26, the raw relation profile of Theorem 3.1 must
still be completed through the eight residual sectors and combined with
the finite comparison and correction bound to obtain (3.25), with all
stated uniformity. The rational contribution is now covered by Proposition
3.8 above. Neither it, the host count nor the positive-correction bound
alone establishes the complete raw profile.

Finite (3.24) and the uniform dyadic, global and macroscopic unrestricted
host counts, exact macroscopic decomposition and uniform positive
correction are covered; the full asymptotic proposition is not yet
complete. The bounded-ratio host extension also uses the correct lower
scale `N`. Proposition 3.27's capped profile remains separate work.

## Dependencies, audit and historical boundary

The current endpoints add no external literature premise. They reuse the
historical affine Fourier normalization, tree-boundary maps, finite and
infinite Rademacher measures, cylinder transfer, private-prime arithmetic
and square-product parity identities, together with mathlib.

`PaperCV282/Audit.lean` covers every named declaration in the thirty modules,
including all five named local instances. Batch 7 adds 35 theorems:
5 in `IntervalRationalMass`, 5 in `MacroscopicCanonicalCode`,
4 in `RationalGeometryMass`, 7 in `RationalHeightMass`,
4 in `LogarithmicWordPowers`, 4 in `RationalMassAsymptotics` and
6 in `RationalProfile`. It also adds three definitions: the binary
geometry mass and the two canonical-height masses.
The full inventory and instance names are recorded in the source manifest.
The source inventory and kernel-axiom transcript are checked separately by
`scripts/check_v282_audit.py`; coverage alone is not proof verification.

The original PDF hashes and Lean/mathlib versions are listed in
[`source_manifest.json`](source_manifest.json). The historical `PaperC`
core, earlier `PaperCV11` overlay and prior Palomar records keep their
original identities and scope. No new Palomar or Comparator qualification,
or certification of the complete v2.8.2 PDFs, is claimed by this ledger.
