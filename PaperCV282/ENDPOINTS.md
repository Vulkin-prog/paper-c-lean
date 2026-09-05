# Paper C v2.8.2 endpoint ledger

This ledger describes the current fifteen-module development: 111 theorems,
28 definitions and five named local instances, totaling 144 named
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

## Proposition 3.26: finite arithmetic inequality and dyadic host bound

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

Remaining for the full Proposition 3.26:

1. Extend the proved dyadic host estimate to the remaining macroscopic and
   geometric regimes required by the article.
2. Complete Theorem 3.1's raw relation profile and combine it with the finite
   inequality to obtain (3.25), with all stated uniformity. The host count
   alone does not establish the weighted relation profile.

Finite (3.24) and the uniform dyadic unrestricted host count are covered;
the full asymptotic proposition is not yet complete. Proposition 3.27's
capped profile remains separate work.

## Dependencies, audit and historical boundary

The current endpoints add no external literature premise. They reuse the
historical affine Fourier normalization, tree-boundary maps, finite and
infinite Rademacher measures, cylinder transfer, private-prime arithmetic
and square-product parity identities, together with mathlib.

`PaperCV282/Audit.lean` covers every named declaration in the fifteen modules,
including all five named local instances. Batch 4 adds 22 theorems:
6 in `InfiniteWordFirstMoment`, 6 in `WordDefectCounting`, 5 in
`WordDefectAsymptotics` and 5 in `WordFirstMomentAsymptotics`. It also adds
three definitions and three named local instances. The full inventory and
instance names are recorded in the source manifest.
The source inventory and kernel-axiom transcript are checked separately by
`scripts/check_v282_audit.py`; coverage alone is not proof verification.

The original PDF hashes and Lean/mathlib versions are listed in
[`source_manifest.json`](source_manifest.json). The historical `PaperC`
core, earlier `PaperCV11` overlay and prior Palomar records keep their
original identities and scope. No new Palomar or Comparator qualification,
or certification of the complete v2.8.2 PDFs, is claimed by this ledger.
