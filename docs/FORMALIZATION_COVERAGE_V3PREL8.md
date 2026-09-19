# Paper C 3PREL8 — formalization correspondence

**Status: extension in progress. The complete 3PREL8 paper is not yet formalized.**

The curated [manuscripts](../manuscripts/v3prel8/README.md) contain 96 numbered statement blocks. Relative to the first V3PREL, 71 retain the same statement text (ignoring comments and whitespace), one introductory statement is extended, and 24 are new. These counts include introductory restatements and remarks and are not a percentage of the mathematical work.

Preserved statements retain the [earlier correspondence](FORMALIZATION_COVERAGE_V3PREL.md), including its explicit literature premises and fidelity limits. Textual preservation does not independently certify every proof or unnumbered assertion in the new paper. The old Lean 4.34 validation receipt remains bound to its original source snapshot.

New finite components are proved in `PaperCPrel8`; they are not substitutes for the missing arithmetic/asymptotic conclusions. No additional literature premise, axiom, `sorry`, or assumption of a final comparison theorem is used to close those gaps.

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
| article | [7.7](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L387) | `thm:micro-run-tv` | new statement open |
| article | [7.8](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L458) | `cor:micro-readout` | new statement open |
| article | [7.9](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L507) | `thm:relative-bulk` | preserved statement |
| article | [7.10](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L562) | `thm:crossover` | preserved statement |
| article | [7.11](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L640) | `thm:two-clock` | preserved statement |
| article | [7.12](../manuscripts/v3prel8/sections/07_prefix_boundary.tex#L725) | `thm:affine-crossover` | preserved statement |
| article | [7.7a](../manuscripts/v3prel8/sections/07b_dyadic_restriction.tex#L6) | `cor:dyadic-micro` | new statement open |
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
| companion | [F.1](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L36) | `supp:pivot:lem:inputs` | new statement open |
| companion | [F.2](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L113) | `supp:pivot:lem:palm` | new statement partial |
| companion | [F.3](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L174) | `supp:pivot:lem:rankin` | new statement partial |
| companion | [F.4](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L206) | `supp:pivot:lem:saddle` | new statement proved |
| companion | [F.5](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L231) | `supp:pivot:prop:reciprocal` | new statement proved |
| companion | [F.6](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L316) | `supp:pivot:prop:footprint` | new statement proved |
| companion | [F.7](../manuscripts/v3prel8/companion/F_microscopic_pivots.tex#L333) | `supp:pivot:prop:forcing` | new statement partial |
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

The second component batch proved 35 additional theorems (68 at that snapshot). Actual largest-odd-prime pivots are identified in the existing cylinder; deterministic forcing preserves nonpivot and small-prime coordinates and raw windows outside its directed footprint. Its law is the complete conditional arithmetic-sample law under any positive-mass event of the small-prime trace. The signed-run specialization retains both boundary equations, the exact excess and the sign, with mass `2^(-L-e-2)`. A weighted version also covers small-prime tilts.

The third batch proves 30 further theorems (98 total). F.4, F.5 and F.6 now have their finite and asymptotic bounds: the actual saddle has a uniform loss at most `2*nu/u`, hence `epsilon*nu` eventually; the reciprocal sum is bounded uniformly for every natural ceiling `X` with `2X >= M`; and the directed-footprint polynomial factor is absorbed for logarithmic supports. The exact hypotheses and the unchanged ordinary-PNT premise are listed in the JSON correspondence. These are proved estimates, independently of the still-incomplete stochastic field assembly. F.7 remains partial at the complete source-field level: assembly of the maximal-support `G0` marked vector and the infinite-source conditional measure has not yet been recorded as one endpoint. These finite proofs do not establish the microscopic Poisson theorem 7.7.

## Remaining dependency chains

- **Typical and affine dictionaries**: Collision rank, averaged finite transfer, asymptotic rates and affine-ensemble inclusion identities.
- **Information-adapted cutoff**: Existence and uniform asymptotics of the information-dependent saddle, free-cutoff transfer and optimized admissible-information domain.
- **Microscopic signed prefix field**: Assembly of the maximal-support marked field and its infinite-source conditional law, finite categorical ledger, independent tails, asymptotic completion and dyadic restriction. The reciprocal-pivot and full directed-footprint estimates, and the exact finite-cylinder signed-run forcing law, are now proved.
- **Empirical Poisson and support obstruction**: Overlapping-window variance, summability, Borel–Cantelli transfer and fixed-realization support lower bound.
- **Palm complements**: Rough-kernel Rankin bounds, CRT cloud regularity, normalized void identities, signed pair activity, cumulant bound and arithmetic obstruction.

Additional unnumbered content in article Sections 1, 3, 5–7 and companion C, F, G requires review beyond the numbered-block inventory. In particular D.1/D.4 remain unnumbered and their prior coverage is not inferred from the 71-count.

The signed microscopic comparison must be proved before the Palm-deficit and empirical consequences. The shifted scalar tail must be available independently of that comparison to avoid circular reasoning.
