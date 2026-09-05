# Manuscript clarification for the next revision

## Corollary 2.6: odd valuation, not merely an odd prime

In the v2.8.2 article, page 9, the conditional clause of Corollary 2.6 says
that every vertex has an “odd prime divisor above `Y > B`”. Read literally,
this describes the prime rather than its exponent. The condition needed for
the private-coordinate argument is that every vertex has a prime above `Y`
whose **valuation is odd**.

The intended convention is already explicit on page 8: the large-prime
kernel includes only primes with odd valuation, and the text distinguishes
this from merely having a large prime divisor. The proof of Corollary 2.6
and the Lean implementation follow that convention. This is a clarification
of the conditional clause, not a change to equation (2.6).

For example, take `B = 2`, `Y = 3`, and `x = 26`. The window is `{25, 26}`.
Both integers have odd prime divisors above 3: respectively 5 and 13.
However, `25 = 5²`, so complete multiplicativity forces `f(25) = +1`.
A prescribed word beginning with `-1` therefore has conditional probability
zero for every assignment of the primes at most 3, rather than `2⁻² = 1/4`.
This shows why the literal weaker reading cannot be used. It does not satisfy
the intended odd-valuation hypothesis, since 25 is defective above 3.

Suggested replacement in the next manuscript revision:

> If, for every vertex `n ∈ V_x`, there is a prime `p > Y`, with `Y > B`
> and `v_p(n)` odd, then `P(I_{x,w} = 1 | F_Y) = p_B` for every realization
> of `F_Y`.

Equivalently, require `K_Y(n) ≠ 1` at every vertex. This is the condition
expressed by `¬HDefective Y n` in
`WindowValues.corollary_two_six_conditioned` and the infinite-model endpoints
`InfiniteConditionalWords.corollary_two_six_joint_infinite` and
`InfiniteConditionalWords.corollary_two_six_conditioned_infinite`.

The latter results now prove the exact conditional ratio on every
small-prime assignment atom. Each atom is measurable and has strictly
positive finite measure. With `Y ≤ M`,
`InfiniteConditionalWords.smallPrimeSigmaAlgebra_eq_primeCylinder` proves
that their generated sigma-algebra is precisely `F_Y`, the sigma-algebra
of all prime signs at most `Y`. The finite cylinder also contains every
word vertex. These results establish the concrete atom law. An abstract
conditional-expectation API could repackage it if needed for presentation;
it is not required by the summed first-moment proof.

Batch 4 additionally proves the dyadic summed clause of Corollary 2.6 as
an inequality for the actual unconditional integral of the occurrence count.
The pointwise, conditional-atom and dyadic summed clauses are now covered
through these explicit representations. For a fixed logarithmic band and
every positive integer `k`, the threshold precedes the length, position
mask and distinct-word dictionary. The error has scale
`|W| 2^(-B) N^(1/2+o(1))`; the proof uses linearity of expectation and does
not assume independence of occurrences. Empty dictionaries are included.
This result is dyadic and does not claim a macroscopic extension.

The [v3 revision log](../docs/PAPER_V3_REVISION_LOG.md) tracks this proposed
wording change and related exposition suggestions. The host count is now
bounded uniformly for every pair mask in the global square `[2, M]²`.
Batch 5 specializes this result to the exact macroscopic domain
`[ceil(M^δ), M)`, proves that the start-host count is at most the full-host
count, and establishes the latter's `M^(3/2+o(1))` bound. For fixed `C ≥ 0`
and positive integer `k`, the threshold precedes both `L` and `δ`; the
exposed hypotheses are `L + 1 ≤ C log M` and `δ > 0`. The actual
start-relation cylinder has cutoff `M + L`. No new manuscript correction
is inferred from this extension; the elementary host-bound simplification
remains an exposition suggestion in the log.

These results close the macroscopic host inequalities of Proposition 3.7.
They do not establish Theorem 3.1's raw weighted relation profile,
conclusion (3.25), or Proposition 3.27's capped profile. The bounded-ratio
host extension also preserves the lower scale `N`: for fixed natural `κ`,
it bounds every pair mask in `[2, M]²` by `N^(3/2+o(1))` when
`N ≤ M ≤ κ N` and `L + 1 ≤ C log N`. The threshold precedes the upper
endpoint, length and mask. Its specialization to separated starts in
`[N, M)` includes the actual start-host comparison with cutoff `M + L`.
The summed word result above remains dyadic.

Batch 6 defines the exact weighted start and value masses on this
macroscopic domain with the same cutoff `M + L`. The start mass is
identified with historical `R2κ`; its canonical systematic/residual
decomposition transfers for every natural coding parameter `A`. This
finite identity does not identify the manuscript's eight sectors or
establish their raw profile. The macroscopic finite comparison further
gives a uniform upper bound for `max(0, Rval - 4 Rstart)`: for every
positive integer `k`, eventually its `2k`-th power is at most
`M^(3k+1)`, uniformly in `L + 1 ≤ C log M` and `δ > 0`, with the
threshold chosen before `L` and `δ`. This bounds the positive correction;
it is not an absolute-error estimate or an asymptotic equality. No raw
profile is assumed, and (3.25) remains open. This progress adds no new
manuscript correction; V3-S001 records its bearing on the host correction.

The exact formal scope and hypotheses are recorded in
[`ENDPOINTS.md`](ENDPOINTS.md).

The source PDF identity is recorded in
[`source_manifest.json`](source_manifest.json). This note records a proposed
wording correction; it does not modify the supplied PDFs or the Lean proofs.
