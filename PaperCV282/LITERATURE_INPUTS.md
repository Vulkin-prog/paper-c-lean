# Literature inputs for the v2.8.2 transfer and cutoff proofs

The results from batches 10 and 11 separate published probability/prime-distribution inputs
from the arithmetic and analytic deductions proved in this repository. Each
input below is a named proposition passed as an explicit theorem argument.
There is no new Lean `axiom`, and no proof of these three propositions is
claimed. An axiom audit does not discharge a theorem's hypotheses.

| Explicit proposition | Mathematical content | What the overlay proves from it |
|---|---|---|
| `ScalarSteinInput.ScalarSteinFactorsStatement` | Existence, for every positive Poisson rate and every test set, of a solution of the actual Poisson Stein equation with supremum bound `min(1,lambda^(-1/2))` and first-difference bound `min(1,lambda^(-1))`. | Finite scalar dependency-graph estimates, the soft-exception lemma and their actual conditional arithmetic instances. |
| `ProcessAGGInput.ProcessAGGStatement` | Finite indicator-to-independent-Poisson field comparison for an exact dependency graph, in half-L1 convention, bounded by `2(b1+b2)`. | Actual masked field transfer, including arithmetic costs, deletion of actual sites and of target coordinates. |
| `PrimeEulerPNT.PrimeNumberTheoremRemainder` | For every `eta>0`, eventually `abs(pi(t)-Ei(log t)) <= eta*t/log t`, with the actual prime-counting function. | Weighted partial summation, its lower endpoint, the finite Rankin estimate and subsequent cutoff estimates to the extent recorded in the endpoint ledger. |

The scalar input is taken from the standard Stein solution estimates in
[Krokowski, arXiv:1505.01417v3, Section 2.5, equations (2.14)–(2.15)](https://arxiv.org/pdf/1505.01417).
The zeroth factor used here is a weaker bound than the published
`min(1,sqrt(2/(e*lambda)))`. The zero-rate solution is proved directly in
`ScalarSteinInput.steinSolutionBounds_zero`; it is outside the literature
premise. The telescoping argument, exact dependency factorization and the
identification with total variation are also proved internally.

For the process input, see
[Arratia, Goldstein and Gordon (1989), Theorem 2, printed page 11](https://dornsife.usc.edu/larry-goldstein/wp-content/uploads/sites/221/2023/06/AGG-1.pdf).
The source's norm is twice our total variation. For an exact dependency
graph its third error term vanishes, giving the stated constant after
normalization. The finite specialization includes deterministic zero
coordinates and the empty family. This process premise is independent of
the historical coarse scalar AGG interface; a scalar count bound alone
would not justify a field comparison. The product-Poisson laws and their
rate-perturbation/deletion inequalities are constructed and proved in Lean.

The PNT premise is a source-shaped reformulation of the classical prime
number theorem, using the standard normalization `Li(t)=Ei(log t)`.
A primary mathematical presentation is
[Zagier, *Newman's Short Proof of the Prime Number Theorem* (1997), pages 705–708](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.2307/2975232/fulltext.pdf).
The interpretation as a remainder of size `o(t/log t)` uses the elementary
asymptotic `Li(t) ~ t/log t`; no effective zero-free-region error is assumed.
The overlay does not assume the desired moving-exponent weighted prime
sum as an input. Its Abel identity uses `pi(floor t)` and retains both
endpoints. The definition, derivative, normalization and large-argument
expansion of `Ei`, as well as the two implicit saddle expansions, have
internal proofs independent of the PNT premise.

These inputs extend the explicit literature boundary used by the retained
historical development. Full mathematical coverage under that boundary is
different from an entirely internal formalization of the bibliography.
Any future Palomar submission must state the selected hypotheses and its
exact checked commit separately.

The batch-11 full-band rates, free-cutoff ledger and scalar arithmetic-event
conditioning consequences use only the scalar Stein and PNT propositions.
They add no literature premise. The process AGG argument also supplies the batch-12 dictionary field
comparison together with PNT. The local overlap formulas, marginal cap,
marker construction and mass pushforward contraction are proved internally.
No new coding-theory premise is introduced.
