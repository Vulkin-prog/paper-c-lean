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
`WindowValues.corollary_two_six_conditioned`.

The source PDF identity is recorded in
[`source_manifest.json`](source_manifest.json). This note records a proposed
wording correction; it does not modify the supplied PDFs or the Lean proofs.
