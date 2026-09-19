# Paper C 3PREL8 — formalization correspondence

**Status: extension in progress. The complete 3PREL8 paper is not yet formalized.**

The curated [manuscripts](../manuscripts/v3prel8/README.md) contain 96 numbered statement blocks. Relative to the first V3PREL, 71 retain the same statement text (ignoring comments and whitespace), one introductory statement is extended, and 24 are new. These counts include introductory restatements and remarks and are not a percentage of the mathematical work.

Preserved statements retain the [earlier correspondence](FORMALIZATION_COVERAGE_V3PREL.md), including its explicit literature premises and fidelity limits. Textual preservation does not independently certify every proof or unnumbered assertion in the new paper. The old Lean 4.34 validation receipt remains bound to its original source snapshot.

New finite and asymptotic components are proved in `PaperCPrel8`; they are not substitutes for the missing arithmetic/asymptotic conclusions. No additional literature premise, axiom, `sorry`, or assumption of a final comparison theorem is used to close those gaps.

The five existing Palomar configurations still describe their recorded V3PREL scope. They must not be presented as qualification of all 3PREL8 additions.

## Numbered correspondence

| Document | Result | Label | Status |
|---|---|---|---|
| article | [1.1](../manuscripts/v3prel8/sections/01_introduction.tex#L62) | `thm:poisson-main` | preserved statement |
| article | [1.2](../manuscripts/v3prel8/sections/01_introduction.tex#L122) | `thm:global-summary` | preserved statement |
| article | [1.3](../manuscripts/v3prel8/sections/01_introduction.tex#L171) | `thm:patterns-summary` | extended statement proved |
| article | [2.1](../manuscripts/v3prel8/sections/02_affine.tex#L38) | `lem:fourier` | preserved statement |
| article | [2.2](../manuscripts/v3prel8/sections/02_affine.tex#L74) | `lem:even-subsets` | preserved statement |
| article | [2.3](../manuscripts/v3prel8/sections/02_affine.tex#L101) | `lem:runge` | preserved statement |
| article | [2.4](../manuscripts/v3prel8/sections/02_affine.tex#L125) | `prop:defects` | preserved statement |
| article | [2.5](../manuscripts/v3prel8/sections/02_affine.tex#L176) | `cor:first-moment` | preserved statement |
| article | [2.6](../manuscripts/v3prel8/sections/02_affine.tex#L204) | `cor:absolute-marginal` | preserved statement |
| article | [2.7](../manuscripts/v3prel8/sections/02_affine.tex#L248) | `lem:private-tree` | preserved statement |
| article | [2.8](../manuscripts/v3prel8/sections/02_affine.tex#L263) | `lem:local-pairs` | preserved statement |
| article | [3.1](../manuscripts/v3prel8/sections/03_arithmetic.tex#L23) | `thm:master-profile` | preserved statement |
| article | [3.2](../manuscripts/v3prel8/sections/03_arithmetic.tex#L96) | `macro:lem:rational-code` | preserved statement |
| article | [3.3](../manuscripts/v3prel8/sections/03_arithmetic.tex#L125) | `macro:lem:channel-unique` | preserved statement |
| article | [3.4](../manuscripts/v3prel8/sections/03_arithmetic.tex#L155) | `macro:rem:disparate` | preserved statement |
| article | [3.5](../manuscripts/v3prel8/sections/03_arithmetic.tex#L177) | `macro:lem:graph-resolution` | preserved statement |
| article | [3.6](../manuscripts/v3prel8/sections/03_arithmetic.tex#L224) | `macro:lem:quotient-core` | preserved statement |
| article | [3.7](../manuscripts/v3prel8/sections/03_arithmetic.tex#L301) | `macro:prop:host` | preserved statement |
| article | [3.8](../manuscripts/v3prel8/sections/03_arithmetic.tex#L355) | `macro:prop:systematic` | preserved statement |
| article | [3.9](../manuscripts/v3prel8/sections/03_arithmetic.tex#L376) | `rem:dyadic-edge` | preserved statement |
| article | [3.10](../manuscripts/v3prel8/sections/03_arithmetic.tex#L424) | `prop:shallow-final` | preserved statement |
| article | [3.11](../manuscripts/v3prel8/sections/03_arithmetic.tex#L487) | `macro:lem:pell` | preserved statement |
| article | [3.12](../manuscripts/v3prel8/sections/03_arithmetic.tex#L503) | `lem:split-bounded` | preserved statement |
| article | [3.13](../manuscripts/v3prel8/sections/03_arithmetic.tex#L539) | `lem:component-normalization` | preserved statement |
| article | [3.14](../manuscripts/v3prel8/sections/03_arithmetic.tex#L562) | `lem:one-sided-component` | preserved statement |
| article | [3.15](../manuscripts/v3prel8/sections/03_arithmetic.tex#L583) | `lem:singleton-pair` | preserved statement |
| article | [3.16](../manuscripts/v3prel8/sections/03_arithmetic.tex#L631) | `lem:bounded-component` | preserved statement |
| article | [3.17](../manuscripts/v3prel8/sections/03_arithmetic.tex#L676) | `macro:prop:aligned` | preserved statement |
| article | [3.18](../manuscripts/v3prel8/sections/03_arithmetic.tex#L765) | `macro:lem:two-defects` | preserved statement |
| article | [3.19](../manuscripts/v3prel8/sections/03_arithmetic.tex#L786) | `macro:prop:sector6` | preserved statement |
| article | [3.20](../manuscripts/v3prel8/sections/03_arithmetic.tex#L834) | `macro:lem:determinant` | preserved statement |
| article | [3.21](../manuscripts/v3prel8/sections/03_arithmetic.tex#L884) | `lem:terminal-partners` | preserved statement |
| article | [3.22](../manuscripts/v3prel8/sections/03_arithmetic.tex#L922) | `lem:kernel-energy` | preserved statement |
| article | [3.23](../manuscripts/v3prel8/sections/03_arithmetic.tex#L986) | `prop:terminal-final` | preserved statement |
| article | [3.24](../manuscripts/v3prel8/sections/03_arithmetic.tex#L1089) | `prop:absolute-profile` | preserved statement |
| article | [3.25](../manuscripts/v3prel8/sections/03_arithmetic.tex#L1145) | `prop:capped-profile` | preserved statement |
| article | [4.1](../manuscripts/v3prel8/sections/04_poisson.tex#L58) | `thm:transfer` | preserved statement |
| article | [4.2](../manuscripts/v3prel8/sections/04_poisson.tex#L118) | `prop:cutoffs` | preserved statement |
| article | [4.3](../manuscripts/v3prel8/sections/04_poisson.tex#L158) | `thm:scalar-rates` | preserved statement |
| article | [4.4](../manuscripts/v3prel8/sections/04_poisson.tex#L225) | `cor:moments` | preserved statement |
| article | [5.1](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L38) | `thm:word-field` | preserved statement |
| article | [5.2](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L156) | `cor:iid-word-replacement` | preserved statement |
| article | [5.3](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L196) | `thm:typical-dictionaries` | proved |
| article | [5.4](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L294) | `cor:affine-dictionaries` | proved |
| article | [5.5](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L332) | `cor:generic-dictionaries` | preserved statement |
| article | [5.6](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L365) | `cor:marker-dictionaries` | preserved statement |
| article | [5.7](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L411) | `thm:patterns` | preserved statement |
| article | [5.8](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L458) | `thm:marked-field` | preserved statement |
| article | [5.9](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L533) | `cor:window-clusters` | preserved statement |
| article | [5.10](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L586) | `thm:moving-comparison` | preserved statement |
| article | [5.11](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L675) | `cor:signed-growing` | preserved statement |
| article | [5.12](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L730) | `thm:bridge` | preserved statement |
| article | [6.1](../manuscripts/v3prel8/sections/06_conditioning.tex#L62) | `lem:stable-lift` | preserved statement |
| article | [6.2](../manuscripts/v3prel8/sections/06_conditioning.tex#L149) | `prop:information-labelled` | proved |
| article | [6.3](../manuscripts/v3prel8/sections/06_conditioning.tex#L221) | `lem:conditioning-floor` | preserved statement |
| article | [6.4](../manuscripts/v3prel8/sections/06_conditioning.tex#L262) | `thm:resolved-kernel` | preserved statement |
| article | [6.5](../manuscripts/v3prel8/sections/06_conditioning.tex#L311) | `cor:quenched` | preserved statement |
| article | [7.1](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L37) | `thm:boundary` | preserved statement |
| article | [7.2](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L124) | `lem:meso-defects` | preserved statement |
| article | [7.3](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L142) | `prop:deep-starts` | preserved statement |
| article | [7.4](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L189) | `thm:prefix-poisson` | preserved statement |
| article | [7.5](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L230) | `cor:as-longest` | preserved statement |
| article | [7.6](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L262) | `thm:macro-field` | preserved statement |
| article | [7.7](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L387) | `thm:micro-run-tv` | proved with explicit inputs |
| article | [7.8](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L458) | `cor:micro-readout` | new statement proved |
| article | [7.9](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L507) | `thm:relative-bulk` | preserved statement |
| article | [7.10](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L562) | `thm:crossover` | preserved statement |
| article | [7.11](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L640) | `thm:two-clock` | preserved statement |
| article | [7.12](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L725) | `thm:affine-crossover` | preserved statement |
| article | [7.7a](../manuscripts/v3prel8/sections/07b_dyadic_restriction.tex#L6) | `cor:dyadic-micro` | proved with explicit inputs |
| article | [7.8a](../manuscripts/v3prel8/sections/07a_empirical_poisson.tex#L12) | `cor:empirical-poisson` | proved with explicit inputs |
| article | [7.8b](../manuscripts/v3prel8/sections/07a_empirical_poisson.tex#L154) | `rem:empirical-field-obstruction` | proved |
| companion | [A.1](../manuscripts/v3prel8/companion/A_runge_diophantine.tex#L9) | `supp:lem:runge-calculation` | preserved statement |
| companion | [A.2](../manuscripts/v3prel8/companion/A_runge_diophantine.tex#L112) | `supp:lem:pell` | preserved statement |
| companion | [B.1](../manuscripts/v3prel8/companion/B_cutoffs.tex#L8) | `supp:prop:cutoff-calculation` | preserved statement |
| companion | [B.2](../manuscripts/v3prel8/companion/B_cutoffs.tex#L95) | `supp:lem:soft-retention` | preserved statement |
| companion | [C.1](../manuscripts/v3prel8/companion/C_fields.tex#L250) | `supp:thm:aggregated` | preserved statement |
| companion | [E.1](../manuscripts/v3prel8/companion/E_boundary.tex#L23) | `supp:lem:transition` | preserved statement |
| companion | [E.2](../manuscripts/v3prel8/companion/E_boundary.tex#L97) | `supp:lem:simple-incidence` | preserved statement |
| companion | [E.3](../manuscripts/v3prel8/companion/E_boundary.tex#L165) | `supp:lem:pointwise-maximum` | preserved statement |
| companion | [F.1](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L36) | `supp:pivot:lem:inputs` | new statement partial |
| companion | [F.2](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L113) | `supp:pivot:lem:palm` | new statement partial |
| companion | [F.3](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L174) | `supp:pivot:lem:rankin` | new statement proved |
| companion | [F.4](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L206) | `supp:pivot:lem:saddle` | new statement proved |
| companion | [F.5](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L231) | `supp:pivot:prop:reciprocal` | new statement proved |
| companion | [F.6](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L316) | `supp:pivot:prop:footprint` | new statement proved |
| companion | [F.7](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L333) | `supp:pivot:prop:forcing` | new statement proved |
| companion | [G.1](../manuscripts/v3prel8/companion/G_palm_complements.tex#L44) | `supp:palm:prop:deletion` | new statement proved with explicit inputs |
| companion | [G.2](../manuscripts/v3prel8/companion/G_palm_complements.tex#L67) | `supp:palm:lem:crt` | new statement proved |
| companion | [G.3](../manuscripts/v3prel8/companion/G_palm_complements.tex#L83) | `supp:palm:thm:regular` | new statement partial |
| companion | [G.4](../manuscripts/v3prel8/companion/G_palm_complements.tex#L137) | `supp:palm:prop:palm` | new statement partial |
| companion | [G.5](../manuscripts/v3prel8/companion/G_palm_complements.tex#L183) | `supp:palm:cor:palm-completion` | new statement partial |
| companion | [G.6](../manuscripts/v3prel8/companion/G_palm_complements.tex#L219) | `supp:palm:prop:signed-void` | new statement partial |
| companion | [G.7](../manuscripts/v3prel8/companion/G_palm_complements.tex#L311) | `supp:palm:prop:pair-activity` | new statement open |
| companion | [G.8](../manuscripts/v3prel8/companion/G_palm_complements.tex#L338) | `supp:palm:lem:cumulant` | new statement open |
| companion | [G.9](../manuscripts/v3prel8/companion/G_palm_complements.tex#L371) | `supp:palm:thm:cumulant-obstruction` | new statement open |

The machine-readable [inventory](FORMALIZATION_COVERAGE_V3PREL8.json) contains titles, page/source locators, comment-stripped statement hashes, prior proof references and the limits of new components.

## Arithmetic forcing and finite footprint

The checkpoints below describe the scope and open obligations at each historical snapshot. The current state is in the twentieth checkpoint and the remaining dependency chains below.

The second component batch proved 35 additional theorems (68 at that snapshot). Actual largest-odd-prime pivots are identified in the existing cylinder; deterministic forcing preserves nonpivot and small-prime coordinates and raw windows outside its directed footprint. Its law is the complete conditional arithmetic-sample law under any positive-mass event of the small-prime trace. The signed-run specialization retains both boundary equations, the exact excess and the sign, with mass `2^(-L-e-2)`. A weighted version also covers small-prime tilts.

The third batch added 30 theorems (98 total) proving the saddle envelope,
reciprocal-pivot sum and full directed-footprint estimates in F.4–F.6. Its
source-bound receipt is preserved as historical evidence.

The fourth batch added **55 theorems (153 total, 29 modules)**. F.3 now has the
literal expanded-band endpoint. F.7 has the actual maximal-support field,
complete mark-conditioned law, fixed small trace and directed preservation;
the infinite-source conditional mass function is exactly the finite source
law. The categorical Palm ledger, local and full-value-rank pair estimates,
and the actual product-of-means footprint bound are also proved. The
[fourth-batch receipt](../extension_evidence/v3prel8/microscopic-field/README.md)
records validation. F.2 still uses the explicit analytic Stein solution input.

The new infinite-field comparison has the explicit finite cost
`p^2*(#G + edgeCount + weightedEdges)`. It is not yet theorem 7.7: relation-excess summation, completion of the
discard estimates in the information regime and final uniform limits remain open. The progress counts are an inventory, not a completion percentage.

The fifth batch added **21 theorems (174 total, 32 modules)**. An independent
scalar hit estimate is available, together with a stronger first-moment bound
for arbitrary masks that needs no scalar Stein input. This yields the actual
excess-tail probability and the probability of a hit in the literal complement
of G0, under any positive conditioning event. The latter is bounded using the
integer square-root cutoff and the number of sites with a bad pivot. The
[fifth-batch receipt](../extension_evidence/v3prel8/discard-bounds/README.md) records
the full build and exact axiom audit. The information-dependent excess cutoff
still needs to be placed in the shifted logarithmic band, and the remaining
arithmetic cardinality and error terms must be controlled asymptotically.

The sixth batch added **13 theorems (187 total, 34 modules)**. Actual bad
supports satisfy `card <= n*exp(-V+epsilon*nu)`, uniformly under the stated
population and logarithmic-support conditions. This estimate is substituted
in the conditional deletion probability. The actual infinite-field comparison
now separates a linear local-pair count, the sparse directed baseline and the
nonnegative full-value excess sum over all separated retained sites. Only the
excess is enlarged to all pairs. The [sixth-batch receipt](../extension_evidence/v3prel8/arithmetic-ledger/README.md)
records the validation. The arithmetic profile of the remaining excess sum
and the final cutoff/asymptotic assembly are still open.

The seventh batch adds **17 theorems (204 total, 37 modules)**. The actual
separated full-value excess equals the established arithmetic mass on the
shifted retained-start mask. Its coarse and normalized profiles are proved,
and substituted in the actual infinite-field comparison. The literal cutoff
`ceil((I+V+log(2+lambda))/log 2)` has its exact tail budget, shifted-band
admissibility and subpolynomial inflation proved uniformly under the ambient
budget. The full conditioned relation contribution is at most
`M^(-1/3+epsilon)`. The paper's budget uses `(M-L)*2^-L`, while the cutoff uses
`M*2^-L`; the conversion and remaining error assembly are still explicit open
obligations. See the [seventh-batch receipt](../extension_evidence/v3prel8/value-profile/README.md).

The eighth batch adds **41 theorems (245 total, 51 modules)**. The paper-to-ambient
budget conversion and every geometry condition are now derived. The retained
field, actual conditional deletion, actual excess tail and independent target
costs assemble into the **full interior spatial field**, retaining all signs
and all excesses. For every positive event of the full small-prime sigma-algebra,
the bound is `10*exp(-c′*nu)+4*M^(-1/3+epsilon)`, uniformly in lengths in a
fixed logarithmic band and events satisfying the literal paper budget.
The old analytic and arithmetic inputs remain explicit. Convergence follows
for varying fields satisfying this eventual source regime; no final convergence
premise is used. Arbitrary measurable readouts contract the actual distance.
The [eighth-batch receipt](../extension_evidence/v3prel8/full-microscopic/README.md)
records the validation. The literal moving-depth normalization of 7.7 is now instantiated, including
validity of natural subtraction. The dyadic restriction and general Markov-kernel
readout clause still need their endpoints. F.2 retains its analytic solution input.

The ninth batch adds **20 theorems (265 total, 56 modules)** and completes the
common Markov-kernel clause of 7.8 and the dyadic endpoint 7.7a (with the same
explicit baseline inputs as 7.7). The kernel proof uses the sharp constant-one
bound for [0,1]-valued tests on the actual countable configuration space.
Auxiliary marking followed by any measurable readout is included.

The dyadic proof uses `nu(H)<=nu(K)<=(K/H)*nu(H)` and cutoff monotonicity.
This absorbs the bounded intensity factor when passing from N to 4N and
embeds the original prime sigma-algebra in the larger one. Restriction retains
literal integer coordinates, signs and all excesses. The final theorem still
conditions only on F_{Y_N}, at the one-factor budget, and uses the exact
moving-depth normalization. No implicit derivative or final comparison premise
is assumed. The stronger unnumbered derivative estimate in the paper is not
newly proved. See the [ninth-batch receipt](../extension_evidence/v3prel8/dyadic-readouts/README.md).

The tenth batch adds **31 theorems (296 total, 61 modules)** for the empirical
count law. The actual product-Poisson windows have exact Poisson(h*p) laws
and their empirical frequencies have variance at most `(2h-1)/(4N)`, with
no independence assumption for overlapping origins. The covariance proof
counts at most `2h-1` overlapping origins and uses the sharp `1/4` bound.

A whole-frequency deviation event transfers with **one** full-field TV error,
not N errors. The actual arithmetic starts are reindexed in their original
order (`i+2`), and summing all signs/excesses agrees almost surely by run
finiteness. The normalized empirical masses then converge almost surely in TV
under explicit summable field errors and overlap ratios and convergence of
the target means. The dyadic full-field error is now proved summable; window
rounding changes the mean by less than one site rate.

**7.8a remains partial:** its literal length/window sequence still needs the
eventual microscopic regime and information budget, summability of h/N and
vanishing site rate instantiated. The full-field support obstruction 7.8b is
not yet proved. See the [tenth-batch receipt](../extension_evidence/v3prel8/empirical-windows/README.md).

The eleventh batch adds **25 theorems (321 total, 65 modules)** and proves
**corollary 7.8a at its literal scales**, with the baseline microscopic inputs.
For M_k=2^k and L_k=k-floor(alpha*V_M/log 2), the actual intensity satisfies
`exp(alpha*V_M)/4 <= Lambda_k <= exp(alpha*V_M)`. Thus it diverges and the
strict alpha<1 margin supplies every fixed microscopic information budget.
The h/n ratio is bounded by `4*tau*exp(-alpha*V_M)` and is summable. Windows
are eventually positive and fit within half the sites, so h/N is summable too.

The final theorem proves almost-sure TV convergence of the genuine arithmetic
empirical count law to Poisson(tau), for each fixed alpha and tau, with no
numerical asymptotic premise left to assume. It uses the actual field bound
`10*exp(-nu_M)+4*M^(-1/6)`. Exact mean normalization and the additional
window-size clauses are included: h lies between `(tau/2)*M*exp(-alpha*V_M)`
and `2*tau*M*exp(-alpha*V_M)`, and log h/log M tends to one.

The same explicit directional Stein, PNT, Laishram-Shorey and Nicolas-Robin
inputs remain. The support obstruction 7.8b is distinct and still open.
See the [eleventh-batch receipt](../extension_evidence/v3prel8/empirical-paper/README.md).

The twelfth batch adds **25 theorems (346 total, 70 modules)** and proves
**remark 7.8b for every fixed realization**, without analytic or arithmetic
literature premises. The actual empirical measure is the uniform-origin
pushforward, with event mass equal to the exact observed frequency. Its
support has at most N configurations. Each product-Poisson atom with total
count at least two has mass at most p^2, while this event has mass
`1-exp(-h*p)*(1+h*p)`. Testing outside the empirical support proves the
literal finite lower bound.

At the exact paper scales, N*p^2 tends to zero and
`log(N*p^2)/log(M)->-1`, proving the displayed M^(-1+o(1)) assertion.
Together with h*p->tau, this gives the liminf bound
`1-exp(-tau)*(1+tau)>0`. Relative coordinates are identified with the
existing arithmetic start field, including the u+i+2 integer offset.
The count convergence of 7.8a and the full-vector obstruction of 7.8b
are therefore both proved, with the different premise sets stated above.
See the [twelfth-batch receipt](../extension_evidence/v3prel8/empirical-support/README.md).

The thirteenth batch adds **90 theorems (436 total, 92 modules)** and proves
**theorem 5.3 and proposition 6.2**, under the baseline process AGG and PNT
inputs. Dictionary selection is averaged only after bounding each fixed
conditional field distance. The actual deletion cost averages to exactly
`a*#bad` on every prime fibre. A relation-space injection controls actual
word collisions. The finite local cost uses `#mask*B`, even for sparse masks.
A supremum of the admissible actual means yields one deterministic rate,
and a logarithmic envelope constructs its literal uniform `o(nu)` remainder.
The exceptional fraction, deterministic readouts and comparison with the
actual infinite independent-sign word field follow with the stated rate.

For information adaptation, the root is constructed using the continuous
parameterized saddle, and monotonicity proves uniqueness, constrained
optimization and strict improvement. The displayed leading limit follows
from an exact quadratic identity. The actual full conditional spatial field
obeys `67*exp(-cprime*nu)+64*N^(-1/3+epsilon)` at the literal paper regime.
No length-band hypothesis is added: it follows from the margin. Both source
and target tails are removed using an already certified larger deterministic
truncation. The derivative formulas in the proof are unnecessary and are
not newly formalized. The prescribed-floor leading optimization is proved;
its separate unnumbered full field specialization remains to be assembled.

See the [thirteenth-batch receipt](../extension_evidence/v3prel8/typical-and-information/README.md).
At that checkpoint affine sampling and Palm/cumulant complements remained open.
That receipt does not claim complete alignment or a new Palomar qualification.

The fourteenth batch adds **67 theorems (503 total, 107 modules)** and proves
**corollary 5.4 and the extended part (ii) of introduction theorem 1.3**.
Uniform full-row-rank matrices and independent offsets are explicitly
identified with the actual sampled surjections. Kernel transitivity and
fibre counting prove the one/two inclusion identities, including endpoint
ranks. Only the degree-two selection costs are transferred from uniform
subsets: each conditional field distance is bounded with its dictionary
fixed before averaging. The finite masked bound has the same constants.

An affine-specific supremum rate supplies one uniform little-oh remainder,
the actual exceptional sample fraction, arbitrary deterministic readouts and
an infinite iid comparison with remainder `8*Lambda^2*B/N`. Both genuine
source distances converge in selection probability for each ensemble.
The logarithmic example has explicit positive lower and upper multiples of
N for its dictionary size, and an explicit log-squared description bound.
The baseline process AGG/PNT inputs are retained throughout the asymptotic
field comparisons; the sampling and description algebra needs neither.

See the [fourteenth-batch receipt](../extension_evidence/v3prel8/affine-dictionaries/README.md).
Palm/cumulant complements and the unnumbered review still prevent a claim
of complete 3PREL8 alignment or a new Palomar qualification.

The fifteenth batch adds **43 theorems (546 total, 115 modules)** for the
Palm complements. It establishes the actual arithmetic presence product
for a private-prime regular plant, on every small-prime environment and
under every positive small-prime event. Raw occurrences are indexed separately;
repeated vertices cannot satisfy the private-prime condition accidentally.

The countable target-side mass-deficit identity and regular-class restriction
are proved with normalized summable laws. Actual finite conditional Palm
probabilities give ordinary deleted-event costs after summing disjoint
configurations. The log-normalization estimate needs no upper bound on the
normalized void; an explicit `K*p+g*p^2/(1-p)` penalty suffices. The general
G.4 comparison keeps the configuration-mass and projection premises visible.
For bounded defects on varying countable spaces, vanishing target expectation
is equivalent to convergence in target probability.

The exact finite avoidance polynomial retains singleton corrections under
an arbitrary actual planted law. Its t=1 numerator is the genuine void event.
The target-sign mean/variance deficit bound has the sharp factor one half.
These results do not yet identify the signed affine Fourier coefficients or
the Walsh energy, and do not assert regular-cloud probability estimates.
No analytic or arithmetic literature premise is needed for this batch.

**G.3–G.6 remain partial at this checkpoint.** Its receipt is
[here](../extension_evidence/v3prel8/palm-identities/README.md). This is not a
completion claim for the Palm/cumulant family or a new Palomar qualification.

The sixteenth batch adds **28 theorems (574 total, 120 modules)** for the
rough-kernel estimates of Appendix G. The actual small-kernel count and the
nontrivial omega-weighted reciprocal sum are proved by the canonical support
injection. Both bounds dispense with the paper's zeta factor. The reciprocal
weight parameter is independent of the cutoff, and the empty support is removed
before forming the finite Euler product. All power tails are proved over integers.

The actual stronger good set has an exact real-threshold/floor equivalence.
Its additional deletion count has the literal multiplicity `Q+1` and ceiling
`n+Q`; original and additional deletions partition the full deleted grid.
The original PNT remainder gives the uniform Euler prefactor for every `X>=M`
and the hard-cutoff bound `exp(-V+epsilon*nu)`, retaining the explicit threshold
factor. No other literature premise is used in this batch.

**G.1 is partial:** absorption for the literal `T_M`, final little-oh deletion
limits and the actual deletion coupling remain to be assembled. CRT allocation
and high-probability regular clouds are not claimed. The
[sixteenth-batch receipt](../extension_evidence/v3prel8/rough-kernels/README.md) records
this scope; it is not a new Palomar qualification.

The seventeenth batch adds **35 theorems (609 total, 127 modules)** for the
literal stronger-deletion regime. The threshold `T_M=exp(theta*H/u)` has the
exact tilted exponent, is subpolynomial and eventually exceeds `exp(V)`.
The reciprocal-tilt and support factors are absorbed at scale nu, giving
actual extra counts `n*exp(-V+(theta+epsilon)*nu)` for every positive epsilon.
The complete omitted grid has the rounded shallow-prefix bound without
counting the original bad-pivot exclusions twice.

At the literal paper `E_*`, `Y` and information budget, the actual additionally
deleted mass tends to zero and the total complement is `o(M/log M)`.
All auxiliary geometric conditions are discharged. An actual independent
Poisson mixture on the original finite coordinate space replaces the deleted
low signed types. Its half-L1 distance from the genuine arithmetic conditional
field is at most `2*p` per deleted site, hence at most
`2*exp(-(c-theta)*nu/2)` under the paper regime, uniformly in the original
positive small-prime event. No factor from its inverse probability occurs.

**G.1 remains partial only at the final restoration assembly:** the new
arithmetic, density and low-type replacement endpoints are proved; their
composition with the original whole-field deletion and high-mark-tail
procedure has not yet been recorded as a combined source-facing theorem.
CRT allocations and regular-cloud probabilities remain open. The
[seventeenth-batch receipt](../extension_evidence/v3prel8/stronger-deletion/README.md)
records this scope and the unchanged baseline inputs. No new Palomar
qualification is claimed.

The eighteenth batch adds **20 theorems (629 total, 132 modules)**.
**G.1 is now proved with its explicit baseline arithmetic inputs.** The actual
full infinite conditioned spatial field is reduced to the constructed
independently replaced low field, with completion error
`8*exp(-cprime*nu)+2*M^(-1/3+epsilon)+2*exp(-(c-theta)*nu/2)`.
This error tends to zero for theta<c, cprime>0 and epsilon<1/3.
The restoration reduction uses no Stein solution assumption and assumes no
comparison for the replaced field. The separate F.2 limitation is unchanged.

**G.2 is partial.** Its all-prime CRT allocation inequality is proved for the
actual rough kernel and the uniform Cartesian-grid law. The empty target
blocks cost exactly one, so the factor three is charged per assigned prime,
not per target block. The actual threshold-power estimate and single-support
regularity are proved, as is the deterministic obstruction forcing all primes
of a source occurrence into other blocks. The final multi-source probability
union bound, and then the Poisson-size regular-cloud estimate G.3, remain.
The [eighteenth-batch receipt](../extension_evidence/v3prel8/restoration-crt/README.md)
records exact sources and validation. No new Palomar qualification is claimed.

The nineteenth batch adds **29 theorems (658 total, 137 modules)**.
**G.2 is now proved**, with its explicit ambient size and cutoff conditions.
Finite fibres expose any source index; CRT applies to the remaining independent
indices. Averaging and then summing every source occurrence gives the literal
`k*(Q+1)*T^(-1+log(3*k*(Q+1))/log(Y))` bound. Real-threshold membership in the
stronger good set supplies all kernel hypotheses. No literature premise is used.

**G.3 remains partial**, with a new actual Poisson-size ordered spatial cloud.
Its countable mass function is proved nonnegative and normalized. Event series
are summable and equal the Poisson averages of actual finite-grid event laws.
The expected omitted-site cost is `Lambda*omitted/n`. The uniform regularity
cost through K is `K*(Q+1)*T^(-1+log(3*K*(Q+1))/log(Y))`. The actual tail at
`K=ceil(2*Lambda)` is at most `exp(-(2*log(2)-1)*Lambda)`, tending to zero
when Lambda tends to infinity, as assumed in Appendix F/G.

The identification with the full signed/excess same-grid target, high-mark
cost and literal saddle-scale absorption/convergence remain open. The finite
bound is not presented as the complete conclusion of G.3. The
[nineteenth-batch receipt](../extension_evidence/v3prel8/poisson-cloud/README.md)
records exact sources and validation. No new Palomar qualification is claimed.

The twentieth batch adds **43 theorems (701 total, 144 modules)**.
**G.3 now has its actual complete signed/excess target bound.** The independent
Poisson sample is identified with the existing full target on arbitrary finite
sites. Its finite position prefixes and count/grid atoms recover exactly the
ordered CRT mixture. The intrinsic regular set includes the empty configuration,
bounds actual total multiplicity and excludes every high excess. Its complement
is bounded by the expected omitted-site cost, CRT failures, the genuine Poisson
tail and `Lambda/2^(E+1)`.

The literal hard-saddle ratio `nu^2/(u*V)` diverges. The rounded cutoffs
`K=ceil(2*Lambda)` and `Y=floor(exp V)` satisfy the required CRT logarithmic gap
uniformly under `log Lambda<=V-c*nu` and `Q+1<=B*H`. The full prefactor is
absorbed into `exp(-c*theta*nu^2/(4*u))`, which tends to zero. The final full-target
bound is instantiated at `H=log M`, the actual `E_*`, stronger good set and
paper length/information regime; no CRT side condition remains assumed there.

**G.3 remains partial only at the final asymptotic assembly:** the excluded-site
and high-mark costs, together with `Lambda->infinity`, still need to be combined
into its displayed complete bound and o(1). The presence identity was proved
in an earlier batch. Subsequent Palm/Fourier/cumulant obligations remain open.
The [current receipt](../extension_evidence/v3prel8/regular-target/README.md)
records the validation; no new Palomar qualification is claimed.

## Remaining dependency chains

- **Typical and affine dictionaries**: The full typical theorem 5.3, affine corollary 5.4 and extended introduction 1.3 are proved under baseline AGG/PNT inputs. Actual matrix/offset sampling, uniform little-oh rates, exceptional fractions, readouts, both source comparisons in selection probability, and the short-description example are covered.
- **Information-adapted cutoff**: Proposition 6.2 is proved at the literal source regime under baseline AGG/PNT inputs. Actual root existence, uniqueness, endpoints, constrained leading-budget maximum, strict improvement and displayed leading limit are proved. The unnumbered derivative formulas and the full field bound for a separately prescribed admissible floor are not newly proved; the endpoint proof uses monotonicity and a larger existing deterministic truncation.
- **Microscopic signed prefix field**: The prefix, literal dyadic one-factor comparison and all measurable/common-Markov-kernel readouts are proved. The analytic directional Stein solution construction in F.2 remains an explicit premise. The stronger unnumbered derivative estimate in the dyadic proof was not needed or newly proved; a monotonicity argument replaces it.
- **Empirical Poisson and support obstruction**: Corollary 7.8a is proved at its literal scales with the baseline analytic/arithmetic inputs. Remark 7.8b, including the finite bound, positive liminf for every realization and N*p^2=M^(-1+o(1)), is proved without those inputs. This pair has no additional numerical or support obligation; the analytic solution premise in 7.8a remains the baseline F.2 limitation.
- **Palm complements**: G.1 and G.2 are proved. G.3 now identifies the complete signed/excess same-grid target with the actual iid-marked Poisson sample, transfers its ordered positions to the CRT cloud law, includes all high marks, and proves the literal rounded-cutoff gap and saddle absorption. The full target bound is instantiated uniformly at the paper length/information regime. Final assembly of the excluded-site and high-mark asymptotics, with Lambda->infinity, into the displayed complete o(1) remains. Full arithmetic G.4/G.5 instantiation, signed Fourier/Walsh identities, pair activity and the cumulant inequality/arithmetic obstruction remain open.

Additional unnumbered content in article Sections 1, 3, 5–7 and companion C, F, G requires review beyond the numbered-block inventory. In particular D.1/D.4 remain unnumbered and their prior coverage is not inferred from the 71-count.

The proved microscopic comparison can now feed the remaining Palm-deficit and empirical consequences. The shifted scalar tail is now proved independently of that comparison, avoiding circular reasoning.
