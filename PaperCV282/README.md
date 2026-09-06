# Paper C v2.8.2 formalization overlay

`PaperCV282` develops the English article *Long runs and rare patterns of a
random completely multiplicative function* and its technical companion,
version 2.8.2, dated 5 September 2026. It reuses the historical `PaperC`
model and proofs, with retained-core authority
`b3cf107d2df629453a5da8e84f2bad29eea0bf94`.

The ninth development batch closes the actual eighth sector and assembles
Theorem 3.1 and Propositions 3.25–3.27: raw, coarse and capped start/full
relation profiles on the macroscopic, dyadic and bounded-ratio domains.
It also completes Corollary 2.5, Lemma 2.8 and Corollary 4.4, including the
actual infinite-model mean, second factorial moment and variance. The
macroscopic dictionary first moment extends Corollary 2.6 uniformly before
the position mask and the dictionary.

The complete paper and companion remain a larger project. In particular,
the sharp two-saddle analysis, intensity-sensitive Stein transfer, growing
marked/dictionary fields, conditional paths and microscopic crossover are
not claimed complete. Some auxiliary arithmetic refinements also remain:
the precise Pell/split-product exp(log/loglog) rate, the sharpened size-two
Euler rate, and the aligned-core proposition for every positive density.
The proved uniform M^epsilon consequences suffice for the profiles above.

## Sources, toolchain and verification

The supplied PDFs remain unchanged. Their exact identities are recorded in
[`source_manifest.json`](source_manifest.json):

| Input | Pages | SHA-256 |
|---|---:|---|
| `paper_C_version_2_8_2_en.pdf` | 52 | `263682a1f2aa8301f06bf811fea1f81f42cd4493ccc4e1b94242a66cacfbd623` |
| `paper_C_version_2_8_2_technical_companion_en.pdf` | 23 | `60d6f110aa057ebd9b1c79eaa291bc42759b5f021ef03807d9405a7ec473b094` |

The original pins remain **Lean 4.32.0 and mathlib v4.32.0**, mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`. No toolchain upgrade is needed.

The 115 mathematical modules contain **830 named declarations: 707 theorems, 111 definitions and 12 named local instances**. Batch 9 adds 182 theorems in 26 new modules.

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
premise is assumed by these new arithmetic endpoints.

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

The [endpoint ledger](ENDPOINTS.md) gives the declarations and hypotheses.
The [V3 revision log](../docs/PAPER_V3_REVISION_LOG.md) records **one confirmed
wording correction and seven suggestions**, including the small-product
simplification and the distinction between quantitative rates. No error is
attributed to the companion without evidence. V3 manuscript sources can be
incorporated when supplied and frozen by the author.

The historical `PaperC` core, earlier `PaperCV11` overlay and existing
Palomar records retain their original identities and scope. A future
Palomar submission requires its own frozen statements and evidence.

## Global progress and manuscript revision

A separate coverage assessment tracks numbered manuscript statements and a
weighted estimate of the remaining effort. The count of Lean declarations
is an audit inventory, not a percentage of the complete paper. The current
estimate is about 60% of the total formalization effort, with a conservative
50–65% range; later probabilistic and companion results account for much of
the remaining work. Strict statement coverage is 25/61 numbered article
results. See the [whole-paper assessment](../docs/FORMALIZATION_COVERAGE_V282.md)
and the endpoint ledger for the exact definitions and proved scope.

The V3 revision log contains one confirmed wording correction and seven
suggestions. S007 records the verified two-branch simplification of the
terminal summation. The supplied PDFs and historical Palomar boundary remain
unchanged.
