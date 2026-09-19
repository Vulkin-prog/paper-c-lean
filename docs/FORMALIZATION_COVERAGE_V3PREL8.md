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
| article | [1.3](../manuscripts/v3prel8/sections/01_introduction.tex#L171) | `thm:patterns-summary` | extended statement open |
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
| article | [5.3](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L196) | `thm:typical-dictionaries` | new statement partial |
| article | [5.4](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L294) | `cor:affine-dictionaries` | new statement open |
| article | [5.5](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L332) | `cor:generic-dictionaries` | preserved statement |
| article | [5.6](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L365) | `cor:marker-dictionaries` | preserved statement |
| article | [5.7](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L411) | `thm:patterns` | preserved statement |
| article | [5.8](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L458) | `thm:marked-field` | preserved statement |
| article | [5.9](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L533) | `cor:window-clusters` | preserved statement |
| article | [5.10](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L586) | `thm:moving-comparison` | preserved statement |
| article | [5.11](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L675) | `cor:signed-growing` | preserved statement |
| article | [5.12](../manuscripts/v3prel8/sections/05_patterns_fields.tex#L730) | `thm:bridge` | preserved statement |
| article | [6.1](../manuscripts/v3prel8/sections/06_conditioning.tex#L62) | `lem:stable-lift` | preserved statement |
| article | [6.2](../manuscripts/v3prel8/sections/06_conditioning.tex#L149) | `prop:information-labelled` | new statement partial |
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
| article | [7.8a](../manuscripts/v3prel8/sections/07a_empirical_poisson.tex#L12) | `cor:empirical-poisson` | new statement partial |
| article | [7.8b](../manuscripts/v3prel8/sections/07a_empirical_poisson.tex#L154) | `rem:empirical-field-obstruction` | new statement open |
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
| companion | [G.1](../manuscripts/v3prel8/companion/G_palm_complements.tex#L44) | `supp:palm:prop:deletion` | new statement open |
| companion | [G.2](../manuscripts/v3prel8/companion/G_palm_complements.tex#L67) | `supp:palm:lem:crt` | new statement open |
| companion | [G.3](../manuscripts/v3prel8/companion/G_palm_complements.tex#L83) | `supp:palm:thm:regular` | new statement open |
| companion | [G.4](../manuscripts/v3prel8/companion/G_palm_complements.tex#L137) | `supp:palm:prop:palm` | new statement open |
| companion | [G.5](../manuscripts/v3prel8/companion/G_palm_complements.tex#L183) | `supp:palm:cor:palm-completion` | new statement open |
| companion | [G.6](../manuscripts/v3prel8/companion/G_palm_complements.tex#L219) | `supp:palm:prop:signed-void` | new statement open |
| companion | [G.7](../manuscripts/v3prel8/companion/G_palm_complements.tex#L311) | `supp:palm:prop:pair-activity` | new statement open |
| companion | [G.8](../manuscripts/v3prel8/companion/G_palm_complements.tex#L338) | `supp:palm:lem:cumulant` | new statement open |
| companion | [G.9](../manuscripts/v3prel8/companion/G_palm_complements.tex#L371) | `supp:palm:thm:cumulant-obstruction` | new statement open |

The machine-readable [inventory](FORMALIZATION_COVERAGE_V3PREL8.json) contains titles, page/source locators, comment-stripped statement hashes, prior proof references and the limits of new components.

## Arithmetic forcing and finite footprint

The checkpoints below describe the scope and open obligations at each historical snapshot. The current state is in the tenth checkpoint and the remaining dependency chains below.

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
not yet proved. See the [current receipt](../extension_evidence/v3prel8/empirical-windows/README.md).

## Remaining dependency chains

- **Typical and affine dictionaries**: Collision rank, averaged finite transfer, asymptotic rates and affine-ensemble inclusion identities.
- **Information-adapted cutoff**: Existence and uniform asymptotics of the information-dependent saddle, free-cutoff transfer and optimized admissible-information domain.
- **Microscopic signed prefix field**: The prefix, literal dyadic one-factor comparison and all measurable/common-Markov-kernel readouts are proved. The analytic directional Stein solution construction in F.2 remains an explicit premise. The stronger unnumbered derivative estimate in the dyadic proof was not needed or newly proved; a monotonicity argument replaces it.
- **Empirical Poisson and support obstruction**: The exact overlap variance, Poisson window means, one-event arithmetic transfer, normalized almost-sure completion and dyadic full-field error summability are proved. Still instantiate the literal 7.8a length/window sequence: eventual admissibility and information budget, h/N summability and vanishing site rate. The fixed-realization full-field support obstruction (7.8b) remains open.
- **Palm complements**: Rough-kernel Rankin bounds, CRT cloud regularity, normalized void identities, signed pair activity, cumulant bound and arithmetic obstruction.

Additional unnumbered content in article Sections 1, 3, 5–7 and companion C, F, G requires review beyond the numbered-block inventory. In particular D.1/D.4 remain unnumbered and their prior coverage is not inferred from the 71-count.

The proved microscopic comparison can now feed the remaining Palm-deficit and empirical consequences. The shifted scalar tail is now proved independently of that comparison, avoiding circular reasoning.
