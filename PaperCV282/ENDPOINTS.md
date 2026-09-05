# Paper C v2.8.2 endpoint ledger

This ledger describes the current eleven-module development: 89 theorems,
25 definitions and two named local instances, totaling 116 named
declarations. It records the mathematical scope of the supplied proof terms;
build and qualification outcomes belong in separate evidence. No entry is a
new Palomar record. Names below have prefix `PaperC.V282.`.

## Corollary 2.6: infinite pointwise bound and conditional atom law

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

Remaining for the full Corollary 2.6:

1. Expose the general conditional-probability/expectation kernel API, if
   required by downstream results. The infinite atom law and identification
   with `F_Y` are already established.
2. Sum over deterministic masks and distinct words, connect to uniform
   defect-weight estimates in the logarithmic band, and conclude
   `O(m p_B N^(1/2+o(1)))` with explicit uniformity quantifiers.

The unconditional word-event transfer, infinite pointwise estimate and
exact conditional law on all positive `F_Y` atoms are complete.

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

`PaperCV282/Audit.lean` covers every named declaration in the eleven modules,
including `instMeasurableSpaceF2Discrete` in both `InfiniteWordTransfer` and
`InfiniteConditionalWords`. Batch 3 adds 8 theorems in `FullPrimeAssignment`,
5 in `FullHostCounting`, 4 in `FullHostAsymptotics`, and 22 declarations
(15 theorems, 6 definitions, 1 instance) in `InfiniteConditionalWords`.
The source inventory and kernel-axiom transcript are checked separately by
`scripts/check_v282_audit.py`; coverage alone is not proof verification.

The original PDF hashes and Lean/mathlib versions are listed in
[`source_manifest.json`](source_manifest.json). The historical `PaperC`
core, earlier `PaperCV11` overlay and prior Palomar records keep their
original identities and scope. No new Palomar or Comparator qualification,
or certification of the complete v2.8.2 PDFs, is claimed by this ledger.
