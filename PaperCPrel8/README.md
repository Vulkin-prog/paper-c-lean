# 3PREL8 proof components

This library contains **1,005 proved theorems in 202 modules**. It is an
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
| `MarkovReadouts` | Sharp common-kernel TV contraction and auxiliary marking/readouts for actual microscopic laws |
| `SaddleScaleMonotonicity` | Monotonicity of actual cutoffs and secondary scales; bounded-height information-margin transfer |
| `DyadicRestriction` | Literal integer-site source/target restriction and inclusion of full prime sigma-algebras |
| `DyadicBudget` | One-factor dyadic budget transported to 4N; fixed logarithmic bands and hard cutoff inclusion |
| `DyadicMicroscopicTheorem` | Full signed dyadic comparison at the paper budget and exact moving-depth normalization |
| `EmpiricalWindowVariance` | Actual disjoint-window independence and sharp (2h-1)/(4N) empirical variance |
| `EmpiricalWindowLaw` | Exact Poisson window means, Chebyshev and one-event source-TV transfer |
| `EmpiricalWindowConvergence` | Normalized frequencies and almost-sure TV completion from summable field errors and overlap ratios |
| `EmpiricalScaleBounds` | Literal dyadic error summability, rounded-window mean control and Poisson mass continuity |
| `EmpiricalStartField` | Exact ordered arithmetic starts, true empirical tail bound and almost-sure endpoint under explicit numerical conditions |
| `EmpiricalPaperScales` | Literal dyadic heights, rounded base lengths, vanishing site rates and exact rounded-window mean |
| `EmpiricalPaperBudget` | Actual intensity and information budget; summable h/n and h/N; eventual window containment |
| `EmpiricalPaperTheorem` | Corollary 7.8a for the genuine arithmetic empirical law at the literal scales, with baseline microscopic inputs |
| `EmpiricalWindowGrowth` | Explicit constants for h=M*exp(-alpha*V+O(1)) and log h/log M -> 1 |
| `EmpiricalSupportTarget` | Actual product-Poisson atom and two-or-more event masses; strict positivity of the obstruction |
| `EmpiricalFiniteSupport` | Exact uniform empirical frequencies and support-cardinality TV obstruction |
| `EmpiricalSupportScales` | Vanishing literal N*p^2 penalty and convergence of the finite lower bound |
| `EmpiricalSupportGrowth` | Actual origin count and proof of N*p^2=M^(-1+o(1)) |
| `EmpiricalSupportTheorem` | Remark 7.8b for every realization, with exact arithmetic coordinates and positive liminf |
| `DictionarySamplingBounds` | Exact selection coefficients, inequalities and average one-word costs |
| `DictionaryCollision` | Injective collision-to-stacked relation map and nullity comparison |
| `DictionaryArithmeticCollision` | Actual arithmetic word collision and selected pair bounds |
| `DictionaryAverage` | Finite selection/environment averaging and exact exceptional fractions |
| `DictionaryMaskedCosts` | Local graph and overlap costs proportional to the actual mask size |
| `TypicalDictionaryPairs` | Averaged actual pair mass with the full-value excess profile |
| `TypicalDictionaryDeletion` | Exact mean deletion cost on every prime fibre |
| `TypicalDictionaryTransfer` | Actual fixed-dictionary conditional field transfer followed by selection averaging |
| `TypicalDictionaryFinite` | Literal finite masked estimate with explicit numerical constants |
| `TypicalDictionaryRates` | Uniform arithmetic bounds at the actual hard cutoff |
| `TypicalDictionaryTheorem` | Uniform fixed-slack mean rate, exceptional fraction and unconditional contraction |
| `TypicalDictionaryIid` | Actual independent-sign comparison and normalized Lambda-squared remainder |
| `UniformExponentialEnvelope` | Constructive logarithmic envelope converting arbitrary fixed slack to a little-oh term |
| `TypicalDictionaryUniform` | One deterministic actual-mean supremum and its literal uniform little-oh rate |
| `TypicalDictionaryConsequences` | Typical classes, arbitrary readouts and full infinite iid comparison |
| `InformationSaddle` | Existence and uniqueness of the actual information-dependent root |
| `InformationSaddleBudget` | Root endpoints, strict monotonicity, improvement, actual and constrained maxima |
| `InformationSaddleScales` | Uniform parameter asymptotics and exact quadratic identity |
| `InformationSaddleLimit` | The displayed leading information-budget formula |
| `InformationFieldBudget` | Separate linear/quadratic error margins and uniform tail/polynomial absorption |
| `InformationFieldTheorem` | Actual full signed field at the information cutoff, with explicit uniform rate |
| `InformationFieldPaper` | Proposition 6.2 without extra band assumptions, and arbitrary deterministic readouts |
| `AffineDictionarySample` | Actual uniform surjections/offsets, fibre cardinality and nonzero-vector transitivity |
| `AffineDictionaryInclusion` | Kernel double counting and exact two-word probabilities |
| `AffineDictionaryMoments` | Exact matching of degree-two selection costs with uniform subsets |
| `AffineDictionaryCosts` | Actual fibrewise deletion, arithmetic pair mass and overlap averages |
| `AffineDictionaryFinite` | Finite masked process bound with constants 2,8,6,2 |
| `AffineDictionaryRates` | Actual hard-cutoff arithmetic rates under affine sampling |
| `AffineDictionaryTheorem` | Uniform intensity-capped mean field bound |
| `AffineDictionaryUniform` | Affine-specific supremum rate and literal uniform little-oh remainder |
| `AffineDictionaryExceptional` | Actual matrix/offset sample fraction and Markov bound |
| `AffineDictionaryIid` | Genuine infinite arithmetic and independent-sign comparison |
| `AffineDictionaryConsequences` | Uniform exceptional classes, readouts and normalized iid error |
| `AffineDictionaryMatrix` | Literal full-row-rank matrix bijection and uniform expectation equality |
| `AffineDictionaryDescription` | Explicit inclusion formulas, linear-size dictionaries and log-squared bits |
| `TypicalDictionaryConvergence` | Both actual field distances converge in uniform-subset selection probability |
| `AffineDictionaryConvergence` | Both actual field distances converge in affine selection probability |
| `RegularPlantPresence` | Actual joint signed-mark presence under private-prime geometry and small-prime conditioning |
| `PalmDeficit` | Countable target-side positive mass deficit and regular-class restriction |
| `PalmDeletionIdentity` | Actual finite conditional Palm mass cancellation and ordinary deletion cost |
| `PalmVoidNormalization` | Logarithmic normalization bound without an upper bound on the void ratio |
| `PalmVoidAverage` | Target-averaged normalized comparison with explicit configuration/projection hypotheses |
| `PalmDeficitProbability` | Target-weighted bounded-defect expectation/probability equivalence on varying spaces |
| `PalmVoidPolynomial` | Exact finite avoidance expansion, singleton corrections and actual void event |
| `PalmTargetSignBound` | Finite-law mean/variance bound with sharp factor one half |
| `RoughKernelPowerSums` | Finite variable-exponent integer sums and convergent tails |
| `RoughKernelRankin` | Actual small rough-kernel Rankin counts without a zeta factor |
| `RoughKernelReciprocal` | Actual nontrivial omega-weighted reciprocal sums and Euler tail |
| `RoughKernelDeletion` | Stronger good set, exact threshold floor and finite deletion counts |
| `RoughKernelSaddle` | Uniform PNT Euler prefactor and hard-cutoff kernel counts |
| `RoughKernelThreshold` | Literal T_M, exact tilted power, floor, subpolynomial scale and cutoff separation |
| `RoughKernelStrongCount` | Uniform absorbed stronger-deletion count with arbitrary theta+epsilon exponent |
| `RoughKernelGoodSet` | Exact G_theta and total-complement count without double charging bad pivots |
| `RoughKernelDeletionLimits` | Actual extra mass and complete omitted-density limits |
| `FiniteFieldReplacement` | Normalized independent Poisson replacement and source-plus-target cost |
| `SignedGoodReplacement` | Actual conditional signed-field replacement at cost 2*p per deleted site |
| `StrongerDeletionTheorem` | Literal paper E_*, Y, geometry, information margin and replacement endpoints |
| `StrongerRestoration` | Full original conditional field restored from the actual low replacement, with explicit vanishing error |
| `RoughKernelCRT` | Distinct-prime CRT certificates, allocation partitions and exact empty-block costs |
| `RoughKernelAllocation` | Actual rough-kernel hosting probabilities on the uniform Cartesian grid |
| `RoughKernelExponent` | Actual omega/log bound and threshold-power conversion |
| `RoughKernelRegularity` | Occurrence-level regularity, single support and deterministic hosting obstruction |
| `UniformGridFibres` | Actual uniform coordinate fibres, averaging and omitted-grid fractions |
| `RoughKernelCloudBound` | G.2 full multi-source probability union bound at the real kernel threshold |
| `PoissonCloudTail` | Exact generating series and exponential tail at ceil(2*Lambda) |
| `PoissonCloudMixture` | Normalized countable Poisson mixture and expected affine loss before truncation |
| `PoissonRegularCloud` | Actual ordered spatial cloud: omitted sites, private pivots and count tail |
| `BulkCloudLawExt` | Full marked target law determined by finite projections on arbitrary finite sites |
| `BulkCloudIdentification` | Actual Poisson sample with uniform sites, fair signs and all geometric excesses |
| `OrderedLabelCloud` | Exact recovery of every finite-grid Poisson-mixture event from sampled positions |
| `RegularTargetCloud` | Intrinsic regular configurations and full target probability bound including high marks |
| `RegularCloudSaddle` | Divergence of nu^2/(u*V), uniform prefactor absorption and error convergence |
| `RegularCloudCutoff` | Exact rounded K and Y, information-margin CRT gap and absorbed cloud cost |
| `RegularTargetSaddle` | Full same-grid target bound at the literal paper length/information regime |
| `AffinePalmCharacters` | Signed characters on an actual finite affine Palm fibre -/ |
| `AffinePalmEnvironment` | The small-prime environment survives planting and remains in Fourier coefficients -/ |
| `ArithmeticPalmAvoidance` | Exact Palm voids are absence of all additional base starts -/ |
| `ArithmeticPalmCompletion` | Completion of the arithmetic one-sided Palm deficit |
| `ArithmeticPalmDeficit` | Countable Palm deficit and deletion for the actual arithmetic field -/ |
| `ArithmeticPalmMass` | The Palm mass identity on the actual conditional arithmetic field |
| `ArithmeticPalmNormalization` | The normalized arithmetic Palm void and its exact comparison error -/ |
| `ArithmeticPalmProbability` | Actual Palm completion in mean and target-configuration probability -/ |
| `EnumeratedTargetAtoms` | Complete Poisson atom formula for the same enumerated regular plants -/ |
| `InfinitePalmDeletion` | Ordinary Palm deletion on the genuine infinite probability space |
| `InfinitePlantMass` | Exact arithmetic configuration masses for enumerated regular plants -/ |
| `InfinitePlantPresence` | Exact regular-plant presence in the original infinite arithmetic law -/ |
| `PalmNormalizationRate` | Vanishing normalized-void penalty at the literal paper budget -/ |
| `PalmWalsh` | Exact Walsh energy under the independent fair target signs |
| `RegularConfigurationAtoms` | Exact masses of simple marked plants under the complete target law |
| `RegularTargetCompletion` | Complete regular-target error and its vanishing under the paper regime -/ |
| `RegularTargetPresence` | From the intrinsic regular target geometry to exact arithmetic presence -/ |
| `ArithmeticEnvironmentLaw` | Actual conditioned arithmetic law as its small/large prime product |
| `ArithmeticLowCategory` | The original arithmetic low-type categorical field in G.8 and G.9 |
| `ArithmeticPalmFourier` | The arithmetic signed centered coefficient and normalized Palm polynomial |
| `ArithmeticPalmMatrices` | Actual valuation matrices in the signed Palm Fourier formula |
| `ArithmeticPalmOutside` | The full arithmetic Palm void in the ordinary outside-start identity |
| `ArithmeticPalmSigns` | The actual arithmetic normalized void under independent fair target signs |
| `CategoricalActivityWitness` | A rare-event lower bound for the actual categorical cumulant activity |
| `CategoricalCumulantBound` | The finite categorical total-variation bound of G.8 |
| `CategoricalMomentExpansion` | Exact signed tensor expansion of an actual categorical law |
| `CategoricalOccupancyEnvelope` | The positive occupancy polynomial and the lower bound on categorical activity |
| `CategoricalTransversals` | Categorical choices as distinct-site finite subsets |
| `CenteredAffineBlocks` | Exact centered character expansion for overlapping affine blocks |
| `CenteredPalmFourier` | The exact signed centered Palm coefficient, including its environment |
| `ConditionalPairDeviation` | The absolute conditional pair layer pays only one conditioning mass |
| `CumulantFamilyEnvelope` | Cumulant envelopes restricted to a downward-closed family of subsets |
| `FiniteCumulantEnvelope` | Finite product envelope for cumulant partitions |
| `FiniteCumulantPartitions` | Finite moment/cumulant partitions, with no analytic series |
| `PrimeRunWitness` | The arithmetic one-negative-prime run witness used in G.9 |
| `PrimeWitnessRetention` | Retention and the exact probability of the G.9 prime witness |
| `PullSiteTarget` | Exact target law under an arbitrary injective relabelling of sites |
| `RetainedRegularSaddle` | The retained regular target exception at the literal paper parameters |
| `RetainedRegularTarget` | Exact boundary/start and retained-mask transfer of regular target configurations |
| `RoughPairHosts` | Single-target CRT hosting count for the rough pair layer |
| `TwoRankPair` | The exact two-rank absolute conditional deviation in G.7 |
| `ArithmeticLowMarginals` | Exact unconditioned low-type marginals from the actual private-prime geometry |
| `CumulantActivityLayers` | The exact pair and higher-order layers of the categorical activity |
| `LogarithmicSaddleBudget` | Every logarithmic cost fits every fixed second-order saddle margin |
| `PalmCumulantEnvelope` | The finite Palm cumulant criterion, with its singleton corrections |
| `PrimeActivityAsymptotics` | The normalized G.9 obstruction on the literal prime windows |
| `PrimeActivityDivergence` | Divergence on every sequence of primes tending to infinity |
| `PrimeActivityLower` | A simpler finite lower bound for the prime witness |
| `PrimeCumulantObstruction` | G.9's arithmetic obstruction for the named original and stronger good sets |
| `PrimeMicroscopicComparison` | Vanishing full microscopic distance on the explicit obstruction windows |
| `PrimeRetainedDensity` | The G.9 omission hypothesis for both named retained sets |
| `PrimeWindowBudget` | All fixed saddle margins hold along the literal G.9 windows |
| `PrimeWindowErrors` | Vanishing errors and the exact positive obstruction constant |
| `PrimeWindowGeometry` | The literal low-mark cutoff and sampling cylinder on the prime windows |
| `PrimeWindowIntensity` | Intensity and small marginal errors on the explicit prime windows |
| `PrimeWindowScales` | The literal q-1+floor(log₂ q) window in G.9 |
| `PrimeWitnessCountBounds` | Uniform explicit errors in the certified-prime-site count |
| `ShiftedCylinderPNT` | PNT normalization on a sublinearly enlarged sampling cylinder |

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
The literal moving-depth normalization of 7.7 and the dyadic endpoint 7.7a
are instantiated. All common Markov-kernel readouts, including auxiliary marking
and a measurable output, obey the sharp constant-one bound. The dyadic proof
uses monotonicity rather than implicit differentiation. Other new families
remain open; the analytic solution construction in F.2 is still an explicit input.
The empirical count-law probability argument now includes the actual source,
sharp overlapping-window variance and normalized almost-sure completion.
The literal length/window regime, summability and normalization are now
instantiated: corollary 7.8a, including its window-size clauses, is proved with
the same explicit analytic/arithmetic inputs as the microscopic comparison.
The support obstruction 7.8b is now proved for every fixed realization,
including its finite bound, positive liminf and displayed logarithmic penalty
exponent. That deterministic result needs no analytic/arithmetic inputs.
No proof placeholder or new Lean axiom is used.

```sh
lake build PaperCPrel8
lake env lean PaperCPrel8/Audit.lean > prel8-audit.log 2>&1
python3 scripts/check_prel8_audit.py --log prel8-audit.log
```

The audit requires all names in `audit-names.json`, in order, and rejects any
foundational axiom outside `propext`, `Classical.choice` and `Quot.sound`.
[Current validation evidence](../extension_evidence/v3prel8/prime-obstruction/README.md) binds the build and
audit results to exact source hashes. No new Palomar qualification is claimed.

Theorem 5.3 (typical dictionaries) and proposition 6.2 (information-adapted
labelled comparison) are proved under the explicit baseline AGG/PNT inputs.
The affine corollary 5.4 and extended introduction 1.3 are also proved.
Palm/cumulant complements and remaining unnumbered assertions still prevent
a claim of complete realignment.

G.1–G.6 numbered conclusions and G.8 finite bounds are recorded, with explicit baseline inputs where required. G.6 also has the finite Palm cumulant criterion retaining singleton corrections. G.9 now has its actual positive normalized lower limit and total-activity divergence for G0 and every fixed G_theta, with the exact prime windows, minimal M+Q cylinder, original marginals and omission estimates discharged; the independent microscopic distance tends to zero with the existing F.2 inputs. G.7 still needs the full arithmetic pair-activity summation and uniform asymptotic rough-host bound. The remaining G.9 assertion about divergence at orders >=3 depends on that vanishing pair estimate; its exact layer decomposition is proved. Final unnumbered review (named outside-deletion convergence, cumulant conventions, tilted-void identities, the pair example and witness threshold) and the separate prescribed-floor full-field specialization remain. F.2 retains its explicit baseline analytic solution premise.
