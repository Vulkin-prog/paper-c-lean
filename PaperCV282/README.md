# Paper C development: v2.8.2 baseline and V3PREL

The `PaperCV282` namespace is retained to preserve theorem names and imports.
Its current source is the supplied V3PREL article and companion, archived in
[manuscripts/v3prel](../manuscripts/v3prel/README.md). The historical `PaperC`
core retains authority `b3cf107d2df629453a5da8e84f2bad29eea0bf94`.

Batch25 audits all **59 numbered article results and, separately, 8 companion
results**, together with the unnumbered conclusions; see the
[V3PREL mapping](../docs/FORMALIZATION_COVERAGE_V3PREL.md). The earlier v2.8.2
denominator was 61 because two arithmetic lemmas were removed in the revision.

Seven literature propositions remain explicit, unproved theorem arguments.
Batch25 **changes the directional Stein proposition**: the former Euclidean
quadratic estimate was false. The corrected same-solution entrywise constant
and weighted quadratic estimates match V3PREL C.3. The development proves a
counterexample to the old formulation and rederives the downstream bounds.
Thus the earlier batch24 claim cannot be read as completion under seven
unchanged source-faithful propositions. See
[LITERATURE_INPUTS.md](LITERATURE_INPUTS.md) and the current mapping.

The [five new Palomar candidates](../docs/PALOMAR_V3PREL.md) specify selected
results. A source mapping, Lean build or axiom inventory is not a Palomar
registration and does not prove the literature inputs themselves.

## Sources, toolchain and verification

The baseline v2.8.2 PDFs below are historical inputs. Their identities are recorded in
[`source_manifest.json`](source_manifest.json):

| Input | Pages | SHA-256 |
|---|---:|---|
| `paper_C_version_2_8_2_en.pdf` | 52 | `263682a1f2aa8301f06bf811fea1f81f42cd4493ccc4e1b94242a66cacfbd623` |
| `paper_C_version_2_8_2_technical_companion_en.pdf` | 23 | `60d6f110aa057ebd9b1c79eaa291bc42759b5f021ef03807d9405a7ec473b094` |

The original pins remain **Lean 4.32.0 and mathlib v4.32.0**, mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`. No toolchain upgrade is needed.

The 753 mathematical modules contain **6094 named declarations: 4539 theorems, 1039 definitions and 516 named instances**. Batch25 adds the formal Stein counterexample; the candidate interfaces are counted separately.

The complete mathematical module and named-instance lists are in the source
manifest. The source gate requires exact named-declaration coverage and the
pinned versions. The kernel transcript permits only `propext`,
`Classical.choice` and `Quot.sound`. Inventory checking is distinct from
Lean kernel verification; importing a historical conditional interface does
not introduce its assumptions into an independently proved endpoint.

With dependencies available:

```sh
lake build PaperCV11 PaperCV282
python3 scripts/check_v282_audit.py --check-source
lake env lean PaperCV282/Audit.lean > PaperCV282-Audit.log
python3 scripts/check_v282_audit.py --log PaperCV282-Audit.log
python3 -m unittest discover -s scripts -p 'test_v282_audit.py'
```

Build outcomes and remote checks are recorded separately for the exact
published commit. They do not constitute a new Palomar qualification.

## Mathematical coverage

Use `B=L+1`, `Q_B=2^B`, and the literal start interval
`U=[ceil(M^delta),M)`. The separated pair mask consists of ordered pairs
with `L < dist(x,y)`. Actual vertices are `x−1,…,x+L−1`; the mask selects
starts and does not truncate a window. Empty populations are allowed.

For the sector profiles, fix `0 < betaMin < betaMax`, `delta>0` and
`epsilon>0`. A threshold is chosen before every `M`, length and pair in the
full band `betaMin log M ≤ B ≤ betaMax log M`. The canonical choice is
`A=3`. Neither `Q_B≈M` nor a bounded ratio between the two starts is assumed.
Some individual theorems have stronger uniformity in `A`, lower endpoints
or `delta`; [`ENDPOINTS.md`](ENDPOINTS.md) records it explicitly.

| Contribution | Proved upper profile, up to `M^epsilon` |
|---|---|
| Rational height 2 / height at least 3 | `M Q_B^(1/2)` / `M Q_B^(1/3)` |
| Sector 1: `P#≤M` | `M^(3/2)+M Q_B^(1/2)` |
| Sector 2: positive small-height channel | `M Q_B^(1/2)+M Q_B^(1/3)` |
| Sector 3: shallow corrected core | `M^(3/2) Q_B^(1/6)` |
| Sector 4: aligned, beyond the shallow cutoff | Empty eventually |
| Sector 5: moderate deep core | `M Q_B^(2/3)` |
| Sector 6: dense core and at least three corrected defects | `M^(1/2) Q_B` |
| Sector 7: dense core, few defects, sufficient rank loss | `M Q_B^(2/3)` |
| Sector 8 | `M^(2/3) Q_B + M^(3/4) Q_B^(2/3)` |

The partition is successive and literal, with complementary tests and the
actual canonical rank. Lean indices `0,…,7` correspond to manuscript
sectors `1,…,8`. Its exact finite residual sum retains the true weight
`2^sigma*(2^tau−1)`, without hypothetical rank or classification inputs.

The small-product proof uses `(B+1)^c#≤P#≤M` and the corrected-defect bound
to obtain a pointwise subpolynomial factor. The sector-5 and sector-6
proofs use internal polynomial-height Pell, squareclass localization and
one-sided split-product counts. The size-two branch is counted jointly by
a finite harmonic/Euler estimate. No Evertse–Silverman or Nicolas–Robin
premise is assumed by these sector endpoints. Batch20 uses Nicolas–Robin explicitly for the distinct precise intermediate count.

The terminal energy counts the literal binomial second moment
`sum_{X≤x<2X} choose(A_T(x),2)`. For an integer kernel cap
`T≤D*sqrt(X*B)` and `B≤C*log X`, it is at most
`X^(2/3+epsilon)*B^2`, with a threshold before `L,T`. The proof includes
small-kernel anchors, affine congruence fibres, both dyadic kernel-range
sums, exact window double counting and the enlarged value interval at the
window boundaries. The terminal graph-to-kernel bridge, uniform partners, first-start container
and complete larger-start summation are now proved. The two-branch proof
retains the same real cap, with no symmetry premise on canonical sectors.

The explicit minorants retain both orientations of the families `(t,2t)`
and `(2t,3t)`, their actual separated-domain membership, and their numerical
coefficient errors. They prove (3.22) and (3.23) for the true relation mass;
no canonical selection of these subspaces is presumed.

## Module groups and exact endpoints

| Group | Main modules |
|---|---|
| Infinite word laws and first moments | `InfiniteWordTransfer`, `InfiniteConditionalWords`, `InfiniteWordFirstMoment`, `WordDefectAsymptotics`, `WordFirstMomentAsymptotics` |
| Full-value parity and host comparison | `TwoWindowParity`, `ValueSquareRelations`, `TwoWindowSquareHosts`, `FullHostComparison`, `FullIntervalHostAsymptotics`, `BoundedRatioFullHosts` |
| Canonical rational contribution | `MacroscopicCanonicalCode`, `RationalHeightMass`, `RationalGeometryMass`, `RationalProfile` |
| Exact residual sectors | `ResidualSectorPartition`, `ResidualSectorMass`, `ResidualSectorMasks` |
| Sectors 1–4 | `MacroscopicSmallProductProfile`, `MacroscopicSmallHeightSector`, `MacroscopicShallowSectors`, `MacroscopicAlignedExclusion`, `MacroscopicEarlyProfile` |
| Internal polynomial-height arithmetic | `DivisorSubpolynomial`, `PolynomialPellCount`, `SplitProductLocalization`, `PositiveSquareclassPairs`, `PolynomialSplitProducts`, `PolynomialSplitSolutions`, `MacroscopicOneSidedFibers` |
| Sectors 5–7 | `MacroscopicBoundedHosts`, `SectorFiveProfile`, `MacroscopicTwoDefectStarts`, `SectorSixProfile`, `SizeTwoHostAsymptotics` |
| Kernel energy | `ShiftedKernelBoxCount`, `ShiftedKernelQuotients`, `ShiftedKernelRangeCount`, `ShiftedKernelBoxAsymptotics`, `SmallKernelAnchors`, `ShiftedKernelDyadicCover`, `ShiftedKernelPairCount`, `KernelWindowEnergy`, `MacroscopicKernelEnergy` |
| Lower bounds | `RationalLowerBounds`, `RationalFamilyMass`, `IntervalRationalLowerBounds` |
| Finite and nonterminal capped reductions | `CappedRelationMass`, `CappedSectorMass`, `CappedSectorSixProfile`, `NonterminalProfile` |
| Numerical interpolation and conditional assembly | `ProfileMonomials`, `ProfileAssembly` |
| Hard/soft rates and genuine convergence | `HardPoissonRates`, `SoftRateAssembly`, `FreeCutoffSoftRates`, `PoissonRateConvergence` |
| Iid replacement and word counts | `IidWordInfinite`, `IidWordComparison`, `PoissonFieldAggregation`, `DictionaryCountTargets` |
| Random and common-sign dictionaries | `RandomDictionaryCritical`, `RandomDictionaryOverlap`, `SignOverlap`, `SignPatternCounts` |
| Dictionary fields and contraction | `WordOverlapSum`, `DictionaryFieldBounds`, `DictionaryFieldRates`, `DictionaryFieldCritical`, `DictionaryFieldStatistics` |
| Explicit marker dictionaries | `MarkerDictionaryAsymptotics`, `MarkerDictionaryCritical` |
| Actual prime-event conditioning and information | `PrimeFieldEventConditioning`, `RestrictedPoissonTransfer`, `RareConditioningRates`, `HardRelativeMargin`, `PoissonRareProbabilities`, `SmallIntensityConditioning` |

The [endpoint ledger](ENDPOINTS.md) gives the declarations and hypotheses.
The [V3 revision log](../docs/PAPER_V3_REVISION_LOG.md) records **one confirmed
wording correction and sixteen suggestions**, including the small-product
simplification and the distinction between quantitative rates. No error is
attributed to the companion without evidence. V3 manuscript sources can be
incorporated when supplied and frozen by the author.

The historical `PaperC` core, earlier `PaperCV11` overlay and existing
Palomar records retain their original identities and scope. A future
Palomar submission requires its own frozen statements and evidence.

## Global progress and manuscript revision

The [whole-paper assessment](../docs/FORMALIZATION_COVERAGE_V282.md) records the final closure of all 19 fixed effort blocks and 105 units. The relative mathematical scope is 100% complete: 61/61 numbered article results and, separately, 8/8 companion results. The two denominators must not be added. All previously open unnumbered conclusions are included; declaration counts remain an audit inventory, not the completion metric.

The V3 revision log contains one confirmed wording correction and sixteen
suggestions. S007 records the verified two-branch simplification of the
terminal summation; S008 records the mask-local deletion budget of 4.1;
S009 records the unified soft proof at the same cutoff for all intensities.
S010 strengthens the random-dictionary overlap estimate to an exact expectation.
The supplied PDFs and historical Palomar boundary remain unchanged.

S011 records the directional Stein input and the internally proved comparison.
The exact printed C.1 obligation is now closed. S012 records the effective
intensity-uniform local Poisson estimate with relative error at most1/(12n).

S013 records the proved global counting simplification for deep first moments,
without an extra dyadic-slice factor.

S014 records the proved simplification of the contained-prefix overflow
correction, using the existing masked first moment.

S015 records the exact one-hit mixture normalization and a simpler proof of
the moving marked crossover: truncate only the prime-index clock, then remove
that truncation by uniform geometric tails. No convergence of the weights
or exact finite-size independence is assumed.

S016 suggests making the inherited rare regime and future-neutrality
quantifiers explicit in7.10. It is a clarification, not a newly identified
mathematical error. All ten numbered results of section7 are now covered
under the existing explicit literature arguments.

## Historical batch24 scope (read with the batch25 correction)

Precise Pell and split-product rates, sharp singleton Euler estimates,
arbitrary positive aligned-core density, arbitrary Fourier tuples and
cyclomatic ranks are now explicit. Intrinsic Gaussian/local/moderate-tail
estimates and their actual hard/soft transfers close D.1. Constructed
couplings close the labelled and simultaneous-band quenched extensions.
D.4 is represented by the whole integer-level point measure, its actual
half-line restrictions and conditional mark laws, Laplace formulas and
extremes. Auxiliary unnumbered estimates were audited separately.

Companion B.2 is expressed through measurable finite conditional joint
laws on an arbitrary probability environment. The source hypotheses are
required almost everywhere; automatic kernel construction from another
presentation of the original probability space is outside this interface.
Only fixed lower reverse segments and individual-scale maximal couplings
are asserted, with the source quantifiers. The existing future-neutrality
condition is used only where the full affine geometric clock requires it.

The revision log preserves the earlier suggestions and records their V3PREL
status. V3PREL sources are now integrated. The correction of the old Stein
premise is documented separately; new Palomar registration remains a
subsequent action after qualification of the selected candidates.
