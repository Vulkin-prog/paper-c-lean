# Literature inputs for the v2.8.2 transfer and cutoff proofs

The results through batch 21 separate published probability/prime-distribution inputs
from the arithmetic and analytic deductions proved in this repository. Each
input below is a named proposition passed as an explicit theorem argument.
There is no new Lean `axiom`, and no proof of these seven propositions is
claimed. An axiom audit does not discharge a theorem's hypotheses.

| Explicit proposition | Mathematical content | What the overlay proves from it |
|---|---|---|
| `ScalarSteinInput.ScalarSteinFactorsStatement` | Existence, for every positive Poisson rate and every test set, of a solution of the actual Poisson Stein equation with supremum bound `min(1,lambda^(-1/2))` and first-difference bound `min(1,lambda^(-1))`. | Finite scalar dependency-graph estimates, the soft-exception lemma and their actual conditional arithmetic instances. |
| `ProcessAGGInput.ProcessAGGStatement` | Finite indicator-to-independent-Poisson field comparison for an exact dependency graph, in half-L1 convention, bounded by `2(b1+b2)`. | Actual masked field transfer, including arithmetic costs, deletion of actual sites and of target coordinates. |
| `PrimeEulerPNT.PrimeNumberTheoremRemainder` | For every `eta>0`, eventually `abs(pi(t)-Ei(log t)) <= eta*t/log t`, with the actual prime-counting function. | Weighted partial summation, its lower endpoint, the finite Rankin estimate and subsequent cutoff estimates to the extent recorded in the endpoint ledger. |
| `DirectionalSteinInput.DirectionalSteinFactorsStatement` | Existence of a solution of the finite multivariate Poisson immigration–death equation, with the two published quadratic Hessian bounds; dimension at least two and positive target coordinates. | Entrywise bounds by polarization, typed dependency graph, true independent Poisson filling, the exact unsigned C.1 and its signed analogue, aggregate5.8–5.9, the proved target limit5.10, resolved paths and the mean bound for6.4. |
| `LaishramUniformInput.UniformPrimeDivisorStatement` | For every epsilon>0, eventually in k uniformly for every n>k, omega(Delta(n,k)) >= (2-epsilon)*pi(k). | Actual large-prime species, private rows, quadratic rank surplus, microscopic first moment and localization. |
| `PostQuadraticLiterature.ShoreySquareProductStatement` | Square-product specialization of Shorey equation (15), with arbitrary positive k-smooth coefficient and the stated height/density conditions; threshold uniform in all later data. | The k^2 threshold, shifts, true post-quadratic defects, gap/prime-count divergence, probabilities and sums. |
| `PellInput.NicolasRobinDivisorLogBoundStatement` | Historical divisor bound log(tau(n))*log(log(n)) <= 2*log(2)*log(n), n>=64. | Historical ideals/orbits/divisor envelope and actual uniform intermediate two-defect counts exp(O(logM/loglogM)). |

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

## Batch 13: dictionary consequences

Corollaries5.2 and5.5 and the arithmetic conclusion for each nonexceptional
dictionary in5.3 use the same explicit process AGG and PNT arguments.
The iid probability computations and dependency graph, finite sampling
without replacement, exact mean overlap, Markov fraction, common-sign
identities and exact Poisson aggregation are proved internally. No additional
probabilistic or coding premise is introduced. The product Poisson target
is proved from mathlib's Poisson measure, including full independence of
column sums. The kernel audit does not discharge theorem arguments.


## Batch 14: exact marks and compound clusters

Theorem5.6 uses the same ProcessAGGStatement for the finite field comparison;
its uniform arithmetic rate and Corollary5.7 add only the existing PNT argument.
The actual signed/unsigned words, local probabilities, maximal-support graph,
label aggregation, free-cylinder source transfer and sign projection are proved.
The Poisson count and iid geometric marks are constructed independently on a
product probability space; the weighted target identity, joint category laws,
PGF, source boundaries and tail couplings add no external premise. Neither
scalar Stein factors nor a compound-Poisson approximation theorem is assumed
in the new process/cluster endpoints. Kernel auditing does not discharge the
explicit process AGG and PNT theorem arguments.


## Batch 15: complete spatial fields, weak limits and growing conditioning

The uniform critical lattice comparison, scalar consequence, actual-source
diffuse limit and both labelled growing information budgets use only the
existing process AGG and ordinary PNT propositions. These are explicit
arguments, not new axioms. The actual full F_Y conditioning, separate source
and target tails, integer reindexing and whole threshold-path identities are
proved. Countable product targets, joint marking, their identification with
Poisson iid samples, the weak topology, actual integral transfer and the
uniform spatial-grid limit add no literature premise. Neither a Poisson
process convergence theorem nor a desired joint law is assumed.

At the end of batch 15, companion C.1 and the aggregate range remained
open. The aggregate consequences are proved by the chain below; the exact
printed unsigned C.1 bound remained a separate obligation until batch17. The kernel audit
does not discharge the explicit literature hypotheses of any batch.


## Batch 16: directional aggregation and the actual joint Gaussian limit

The new input is exactly the analytic solution theorem and quadratic bounds in
[A. Röllin, *On the Optimality of Stein Factors*, arXiv:0706.0879v3,
printed page 5, equation (3.1)](https://arxiv.org/pdf/0706.0879v3), reproducing
Barbour (1988), Lemma 3. The dimension condition d≥2 was checked visually
against the primary PDF. Its SHA-256 is
`cca9b417622e06ab0cf759f838fc75664d2d766b6032d8c4664685ec8090f440`.
Writing the target coordinates as t_i=λμ_i gives the coefficient
(1+2 log⁺(2Σt_i))/2 multiplying Σα_i²/t_i. The proposition states this
bound and the unweighted bound at every natural configuration, together
with the actual immigration–death Stein equation for every test set.

The signed analogue of C.1 is a deduction, never an input. In batch16, C.1
remained partial because the unsigned cost and support condition were not
yet reproduced. The exact unsigned proof in batch17 closes that obligation.
The entrywise min bound is derived by
polarization. The proof retains an arbitrary outside offset when telescoping
local dependence. An actual independent Poisson field fills missing target
means, including when every retained indicator is zero. Every gradient
integral and coordinate-times-gradient integral used for linearity is
justified by proved polynomial moments and the Hessian growth bound.
Zero filling rates and natural-coordinate boundaries are included.

The signed arithmetic comparison uses mixed value kernels extended by zero
into the complete value-relation space at L+E+2 vertices. Its separated
joint bound is averaged over the actual full F_Y assignments. The geometric
square-root sums are bounded uniformly before the mark cutoff; the full
profile cost 2^(2E+2) is retained before absorption. All this is internal.
PNT enters only the subsequent hard-cutoff arithmetic asymptotics.

The proof of Theorem 5.10 derives the vanishing source distance from the signed comparison and
the one-factor information budget. Its joint target is built from one real
geometric Poisson configuration; the interaction of threshold and exact
counts is computed before passing to the limit. The scalar CLT, finite
joint characteristic functions, Gaussian covariance 2^(-max(j,k)), limiting
independence, and stationary AR(1) innovations are proved using mathlib.
No CLT, Gaussian independence, or desired source convergence is an added
premise. Berry–Esseen, local Gaussian and moderate-deviation rates in D.1
are not consequences claimed by this weak-limit proof.


## Batch 17: exact C.1, conditional kernels and local resolution

No new literature proposition is added. The exact unsigned finite C.1
uses the existing directional Stein input; the full arithmetic rates6.5,
the sufficient resolved budget6.7 and almost-sure6.4 add ordinary PNT.
The dimension condition includes E=0 because two signs are retained during
the comparison. This does not require a fifth scalar input for that case.

The general stable lift6.1, sharp conditioning6.2, the geometric and reverse
Poisson target identities, and Markov/Borel–Cantelli are proved internally.
The effective local Poisson estimate is derived from mathlib's proved
Stirling limit and Robbins stepwise inequality, with remainder1/(12n).
Neither a local-limit theorem nor the desired resolved comparison is
supplied as a literature hypothesis. The four earlier propositions remain
explicit, unproved theorem arguments under the same qualification boundary.

Batch 18 adds no literature input. Its relative hard scalar comparison and
equation (6.3) use only the existing `ScalarSteinFactorsStatement` and
`PrimeNumberTheoremRemainder`. The Poisson non-vacancy and singleton estimates,
the conditional source pushforward, and the ratio limits are proved internally.

Batch 19 adds no literature input. The entropy remainder, its central
asymptotics with bounded rounding, and absorption of the logarithmic Stein
cost are proved internally from the pinned library. The actual resolved
future endpoint uses the same `DirectionalSteinFactorsStatement` and
`PrimeNumberTheoremRemainder` as the previously proved budget (6.7).

## Batch 20: microscopic and mesoscopic arithmetic

The active boundary expands from four to seven propositions. These three
arguments are not new Lean axioms, and no desired rank, defect count, Pell
solution count, or start-probability conclusion is postulated.

The uniform Laishram–Shorey input is [equation(14), printed p.331, in
Acta Arithmetica113.4(2004)](https://www.impan.pl/shop/en/publication/transaction/download/product/83314).
The threshold depends on epsilon, uniformly for every n>k. The historical
Corollary1 input has a weaker coefficient and does not supply this near2π(k)
bound. Its deduction to actual large-prime species is proved in the overlay.

The square-product input is [Shorey, RIMS Kokyuroku886(1994), pp.55–56,
equation(15)](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/0886-05.pdf).
The smooth coefficient is positive, with all prime factors at most k; its
size is unrestricted. From this square-case input, the k² threshold and shifts to
the actual windows are derived. The cited source-shaped proposition contains
neither a rank bound nor a probability estimate.

The retained `PellInput.NicolasRobinDivisorLogBoundStatement` uses
[Nicolas–Robin, Theorem1, p.485(1983)](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/D424A2915C0A748C93CF4962D0120B94/S0008439500065188a.pdf/majorations_explicites_pour_le_nombre_de_diviseurs_de_n.pdf).
It uses the safe constant2 for n>=64, not an equality to a rounded decimal.
The historical conductor, ideal, orbit and divisor-envelope proofs connect
this divisor bound to the precise Pell rate. The new global count then gives
Lemma7.2 with exp(O(logM/loglogM)) uniformly before the height slice.
The earlier polynomial/subpolynomial sector results remain independent of it.

Theorem7.1 and the actual microscopic prime-clock limit use uniform LS,
Shorey and PNT. Lemma7.2 uses PNT and Nicolas–Robin. Proposition7.3 uses all
four arithmetic arguments; its deep/cutoff branches need only Shorey, PNT
and Nicolas–Robin, while the prefix starting at2 adds LS. Exact border and
affine identities and the unconditioned border prime clock are internal.

## Batch21: prefix and relative bulk applications

No new literature proposition is introduced. The seven active inputs from
batch20 remain unchanged and explicit. The final prefix7.4 and almost-sure
7.5 endpoints take scalar Stein solution/factors, uniform Laishram–Shorey,
Shorey square-product, PNT and Nicolas–Robin as arguments. Actual dependency
graphs, deletion, Poisson-mean restoration, contained-prefix coupling,
summable dyadic errors, Borel–Cantelli and all-prefix interpolation are
proved internally. No desired probability bound or summability result is
postulated in the final almost-sure theorem.

The signed bulk7.7 comparison and its full-FY stable factorization use only
the existing process AGG and PNT arguments. The source and target with all
excesses/signs, exact Poisson rates, tail bounds, arbitrary macroscopic masks,
base-length relation estimate and actual microscopic-record measurability
are proved. The lower logarithmic band follows from rare intensity itself.
The spatial point processes at x/M are actual pushforwards of these laws.
Neither their Poisson approximation nor their asymptotic independence is an
additional literature premise. Kernel auditing still does not prove any
of the seven explicit input propositions.
