# Paper C v2.8.2 finite endpoint ledger

This ledger describes the first three mathematical modules of `PaperCV282`.
“Proved in the finite representation” refers to the supplied Lean proof
terms and their stated mathematical scope; build and qualification outcomes
belong in separate validation evidence. No row is a new Palomar record.

## Corollary 2.6: prescribed words

Source: article page 9, equation (2.6) and the following conditional and
first-moment clauses. Words are encoded by binary bits in the existing
completely multiplicative Rademacher model.

All names in this table have prefix `PaperC.V282.`.

| Declaration | Content | Boundary |
|---|---|---|
| `PrescribedValues.probability_eq_eta_weight` | The exact affine probability is `η 2^ρ / 2^B`. | Arbitrary finite uniform vector space and finite system of rows. |
| `PrescribedValues.abs_probability_sub_baseline_le` | A supplied bound `ρ ≤ m` implies error at most `(2^m - 1) / 2^B`. | Finite algebraic estimate, uniform in the right-hand side. |
| `PrescribedValues.relationRho_le_card_of_private_coordinates` | The full-value nullity is at most the number of rows without private-coordinate witnesses. | No even-cardinality constraint is imposed on full-value relations. |
| `PrescribedValues.probability_eq_uniform_event` | The affine probability equals the finite-cylinder event probability for the displayed value bits. | An arbitrary family of integer arguments; cylinder adequacy is supplied by the window endpoints. |
| `PrescribedValues.assemble_solves_values_iff` | Fixing small prime coordinates translates the right-hand side by their contribution. | Exact equations for the finite small/large coordinate split. |
| `PrescribedValues.conditioned_value_probability_eq_baseline` | Every right-hand side has probability `2^(-B)` after any small-prime assignment is fixed. | Requires private-coordinate witnesses in the remaining large-coordinate system. |
| `WindowValues.private_prime_of_not_defective` | An actual nondefective vertex has an odd-valuation prime coordinate private within the window and represented in the cylinder. | Requires `x ≥ 2`, `x - 1 + B ≤ M + 1`, and `B ≤ H`. |
| `WindowValues.corollary_two_six_pointwise` | `abs(P(word) - 2^(-B)) ≤ 2^(-B) (2^(m_B(x)) - 1)`. | Proved in the finite cylinder, with `m_B(x)` the cardinality of the actual defect-index set. |
| `WindowValues.corollary_two_six_conditioned` | The exact word probability is `2^(-B)` for each fixed small-prime assignment. | Requires every vertex to be nondefective above `Y`, `B ≤ Y`, and the same positivity/cylinder bounds. |

For the last two declarations, the vertex function is exactly
`j ↦ x - 1 + j`, with `j < B`. Distinct indices have distinct vertices, so
the defect-index count is the article's defective-vertex count. The bound
`B ≤ Y` slightly extends the article's sufficient range `Y > B`: primes
used as pivots are strictly above `Y`, and the window diameter is at most
`B - 1`.

The pointwise statement permits any `B`, including the empty-window case;
the article's intended positive word lengths are covered. Positivity of the
arguments is required explicitly through `x ≥ 2`; no use of a truncated
valuation at integer zero is hidden in the paper-facing endpoints.

Remaining for the full Corollary 2.6:

1. State and prove the equality with the corresponding infinite-product word
   event and the conditional kernel, using the retained cylinder transfers.
   The finite fixed-assignment representation itself is already supplied.
2. Sum the bound over deterministic masks and `m` distinct words, identifying
   the defect sum with the applicable retained arithmetic bounds in the
   required uniform logarithmic band.
3. Close the quantified asymptotic first-moment error
   `O(m p_B N^(1/2+o(1)))`. No such summed asymptotic endpoint is claimed yet.

## Proposition 3.26: removing two block parities

Source: article page 25, proof of Proposition 3.26 and equations
(3.24)–(3.25).

All names below have prefix `PaperC.V282.ValueRelations.`. For an arbitrary
full-value system `A` and linear map `P` into `Fin 2 → F₂`, write `ρ_full`
for `relationRho A` and `ρ_par` for `parityNullity A P`.

| Declaration | Proved finite statement |
|---|---|
| `mem_parity_kernel_iff` | A relation is in the constrained kernel exactly when `P u = 0`. |
| `parityNullity_le` | `ρ_par ≤ ρ_full`. |
| `relationRho_le_parityNullity_add_two` | `ρ_full ≤ ρ_par + 2`. |
| `relation_weight_le_four_parity_weight_add_host` | `2^ρ_full - 1 ≤ 4 (2^ρ_par - 1) + 3 · 1_{ρ_full ≠ 0}`. |
| `sum_relation_weight_le_four_parity_weight_add_hosts` | The same comparison summed over any finite index set, with the extra term equal to three times its number of nonzero full-relation hosts. |

These are natural-number weights; subtraction is harmless because every
power of two is at least one. The host correction vanishes at a zero full
kernel. No assumption that the two parity equations are independent is
needed: their rank is at most two.

This is the **abstract finite kernel of Proposition 3.26**, not the completed
proposition. The following identifications and estimates remain open in
this overlay:

1. Instantiate `A` with all `2B` valuation rows of two separated windows and
   instantiate `P` with the sums of coefficients in the two actual blocks.
2. Use the retained tree-boundary bijection to identify the constrained
   relation space with the two-start relative-sign relation space at length
   `B - 1`. The current `parityNullity` is not yet identified with the
   article's `ρ_(B-1)(x,y)`.
3. Instantiate the finite index set with the article's ordered separated
   pairs, and identify the correction count with the relevant unrestricted
   square-relation host count. This yields the paper-specific finite
   inequality (3.24).
4. Supply the uniform host estimate of Proposition 3.7, the raw profile of
   Theorem 3.1, and their compatibility with the macroscopic, dyadic and
   bounded-ratio geometries. These give the asymptotic profile (3.25).

The cap in Proposition 3.27 is not implemented here. A bound for an arbitrary
two-equation map, or an uninstantiated finite sum, is not a substitute for
that capped arithmetic estimate.

## Dependencies and evidence

The finite endpoints above add no literature assumptions. They reuse the
retained affine Fourier normalization, finite Rademacher model,
small/large-prime split and private-pivot arithmetic, together with mathlib
linear algebra and finite sums. The broader historical development still
has its own explicit literature interfaces; the full v2.8.2 dependency
boundary has not yet been assembled.

The exact PDF inputs and Lean/mathlib versions are listed in
[`source_manifest.json`](source_manifest.json). The historical proof core
and prior Palomar records are preserved. Neither their evidence nor the
earlier `PaperCV11` ledger qualifies these new endpoints or certifies all
claims in the two v2.8.2 PDFs.
