# 3PREL8 proof components

This library contains **245 proved theorems in 51 modules**. It is an
extension of the previously validated development, not a formalization of every
new 3PREL8 conclusion. The [coverage ledger](../docs/FORMALIZATION_COVERAGE_V3PREL8.md)
records the remaining arithmetic, probability and asymptotic obligations.

| Module | Proved component |
|---|---|
| `PalmStein` | Lattice gradient bound, exact Palm generator identity and finite Poisson comparison |
| `DictionarySelection` | Actual uniform subset inclusion and averaged source-pair collision identity |
| `InformationBudget` | Unique crossing, constrained maximum and both exponent margins |
| `PrivateForcing` | Constructed private-block forcing and its full conditional-law identity |
| `OddPrimePivot` | Actual largest-odd-prime count and inherited uniform Rankin estimate |
| `PivotGeometry` | Actual largest-odd-prime private coordinates in the retained finite cylinder |
| `PrimeForcing` | Arithmetic prime-sign modification, original uniform conditional law and directed preservation |
| `HardConditionalForcing` | Complete conditional arithmetic-sample law for small-prime events and weighted identities |
| `SignedPalmForcing` | Actual signed exact-run conditional law and its exact geometric rate |
| `DirectedFootprint` | Both finite F.6 inequalities using the actual reciprocal-pivot population |
| `SaddleEnvelope` | Actual tangent envelope, explicit O(nu/u) loss and uniform little-o(nu) precision |
| `PivotRankinUniform` | Rankin bounds at a fixed reference height for enlarged populations |
| `ReciprocalPivotShells` | Exact integer-cutoff identity, shell sum and residual tail |
| `ReciprocalPivotAsymptotics` | F.5 reciprocal bound uniform for 2X >= M, from ordinary PNT |
| `DirectedFootprintAsymptotics` | Full F.6 bound with logarithmic support factors absorbed |
| `EmpiricalTransfer` | Discrete overlap identity, Scheffe convergence and countable almost-sure completion |
| `FiniteConditioning` | Actual normalized finite conditional laws and domination of nonnegative expectations |
| `CategoricalPalm` | Directed categorical comparison without reciprocal mark rates |
| `CategoricalSummation` | Exact grouping by site before bounding excess-sign categories |
| `ActualSignedPalm` | Actual retained marked field, arithmetic coupling and exact Palm law |
| `MicroscopicGoodField` | Literal G0, maximal pivots and whole-field directed preservation |
| `SmallPrimeMixture` | Exact prime-block disintegration and bounds under arbitrary small-prime events |
| `MicroscopicFiniteLedger` | Same-site, product and joint costs with geometric rates summed first |
| `ActualSignedPairs` | Local fibrewise pair bounds and conditional full-value relation bounds |
| `MicroscopicPairLedger` | Finite source comparison with explicit actual arithmetic pair weights |
| `MicroscopicInfiniteField` | Exact conditional infinite-field law and its arithmetic comparison |
| `ActualSignedConditionalLaw` | F.7 as an equality of complete conditional field distributions |
| `MicroscopicFootprintLedger` | Actual product-of-means edges bounded by the asymptotic pivot footprint |
| `IndependentScalarTail` | Independent scalar vacancy/hit estimate for a shifted length |
| `MicroscopicDiscardBounds` | Stronger masked first-moment hit/tail/deletion bounds under any positive event |
| `MicroscopicBadPivotCount` | Actual bad-support exponential count and conditional deletion bound |
| `MicroscopicValueProfile` | Actual retained full-value excess equals the established arithmetic mass; coarse and normalized bounds |
| `MicroscopicInformationCutoff` | Literal information cutoff, exact tail budget, shifted band and subpolynomial inflation |
| `MicroscopicProfileBudget` | Uniform conditioned relation-term power saving at the actual cutoff |
| `MicroscopicRelationExcess` | Sparse baseline separated from full-value excess; local count and infinite comparison |
| `MicroscopicDeletedSites` | Literal deleted set, boundary-to-start conversion and conditional source deletion cost |
| `PivotRankinExpandedBand` | F.3 on V-2..3V+2, uniformly for M <= 2X |
| `MicroscopicPaperBudget` | Paper-to-ambient information budget with the strict margin retained |
| `MicroscopicActualGeometry` | Every actual good-field geometric condition derived from the paper regime |
| `MicroscopicRetainedRates` | Uniform graph and local-term rates with a finite numerical assembly |
| `MicroscopicRetainedTheorem` | Full retained finite field with exponential-plus-power rate |
| `MicroscopicDiscardRates` | Uniform shallow and deep conditional remainder rates |
| `MicroscopicDiscardTheorem` | Actual conditional deleted-start and excess-tail rates |
| `MicroscopicSourceRelabelling` | Exact boundary/start source-vector and Poisson product equivalences |
| `MicroscopicConditionalSpatial` | Actual event normalization, TV equivalence and countable excess restoration |
| `MicroscopicSpatialRates` | Unbounded exact marks on retained sites with a uniform rate |
| `MicroscopicSiteRestoration` | Interior-site geometry and restoration by the actual conditional hit event |
| `MicroscopicDeletedTarget` | Independent target deletion intensity at the paper rate |
| `MicroscopicFullTheorem` | Full interior spatial comparison for every positive full-F_Y event |
| `MicroscopicNormalization` | Literal moving-depth normalization and quantitative full-field endpoint of 7.7 |
| `MicroscopicReadouts` | Arbitrary measurable readouts and convergence under the explicit source regime |

The analytic Stein and PNT inputs remain explicit theorem arguments, as in the
baseline. The maximal-support marked field, its complete arithmetic Palm law,
its infinite-source conditional masses and its finite categorical comparison
are now constructed. The local pair bounds hold on every small-prime fibre;
the full-value relation bound pays the actual conditioning mass.
The literal paper information budget now implies the ambient budget and all
actual geometric conditions. All source and target deletions and tails are
assembled. The full interior field, with all positions, signs and unbounded
excesses, obeys `10*exp(-c′*nu)+4*M^(-1/3+epsilon)`, uniformly under the fixed
logarithmic band, Lambda>=1 and paper budget, for every positive event of the
full small-prime sigma-algebra. The existing directional Stein and arithmetic
inputs remain explicit. The error tends to zero and so do the actual varying
field distances under the eventual source regime. Every measurable statistic
contracts the actual distance.
The literal moving-depth normalization of 7.7 is also instantiated. The dyadic
endpoint, common Markov-kernel readouts and other new families remain open;
the analytic solution construction in F.2 remains an explicit input.
No proof placeholder or new Lean axiom is used.

```sh
lake build PaperCPrel8
lake env lean PaperCPrel8/Audit.lean > prel8-audit.log 2>&1
python3 scripts/check_prel8_audit.py --log prel8-audit.log
```

The audit requires all names in `audit-names.json`, in order, and rejects any
foundational axiom outside `propext`, `Classical.choice` and `Quot.sound`.
[Current validation evidence](../extension_evidence/v3prel8/full-microscopic/README.md) binds the build and
audit results to exact source hashes. No new Palomar qualification is claimed.
