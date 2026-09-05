# Paper C v2.8.2 formalization overlay

`PaperCV282` is an additive Lean library for the English article *Long runs
and rare patterns of a random completely multiplicative function*, version
2.8.2, and its technical companion, both dated 5 September 2026. It reuses
the historical `PaperC` model and proofs. The retained-core authority is
commit `b3cf107d2df629453a5da8e84f2bad29eea0bf94`.

The current four-batch development covers the three clauses of Corollary
2.6 through explicit representations: the infinite pointwise bound, exact
conditional probability on every positive `F_Y` atom, and the dyadic summed
first-moment estimate for arbitrary masks and dictionaries in a fixed
logarithmic band. The last result is an inequality for the actual integral
of the occurrence count under the infinite Rademacher law. Its threshold
is chosen before the length, mask and dictionary; no independence of
occurrences is assumed.

It also proves finite inequality (3.24) for actual separated windows and a
uniform dyadic `N^(3/2+o(1))` bound for unrestricted square-product hosts.
The macroscopic host extensions and relation profiles needed for the
complete asymptotic conclusion (3.25) remain open.

## Sources and toolchain

The input documents remain exactly v2.8.2. Their identities are recorded in
[`source_manifest.json`](source_manifest.json):

| Input | Pages | SHA-256 |
|---|---:|---|
| `paper_C_version_2_8_2_en.pdf` | 52 | `263682a1f2aa8301f06bf811fea1f81f42cd4493ccc4e1b94242a66cacfbd623` |
| `paper_C_version_2_8_2_technical_companion_en.pdf` | 23 | `60d6f110aa057ebd9b1c79eaa291bc42759b5f021ef03807d9405a7ec473b094` |

Use `leanprover/lean4:v4.32.0` and mathlib `v4.32.0`, locked to
`81a5d257c8e410db227a6665ed08f64fea08e997`. The historical pins are retained.
With the dependencies available, reproduce the build and declaration audit:

```sh
lake build PaperCV282
python3 scripts/check_v282_audit.py --check-source
lake env lean PaperCV282/Audit.lean > PaperCV282-Audit.log
python3 scripts/check_v282_audit.py --log PaperCV282-Audit.log
```

These are reproduction instructions; execution outcomes belong in the
corresponding build and audit evidence. The source manifest records input
provenance and mathematical scope, not a release verdict.

The fifteen mathematical modules contain **144 named declarations: 111
theorems, 28 definitions and five named local instances**. The instances
supply discrete measurable structures, the source probability-law instance,
and local decidability of the defect predicate. Their complete names are
recorded in the source manifest. The audit gate requires
complete named-declaration coverage, allows only `propext`,
`Classical.choice` and `Quot.sound` as kernel axiom dependencies, and checks
the Lean/mathlib pins. The source inventory is a restricted coverage check;
Lean's kernel checks the proof terms. The development workflow also builds
the earlier `PaperCV11` overlay.

## Implemented components

| Module | Content |
|---|---|
| [`PrescribedValues.lean`](PrescribedValues.lean) | Absolute valuation systems, affine word probabilities, private-coordinate rank bounds, and translation after fixing small primes. |
| [`WindowValues.lean`](WindowValues.lean) | Actual consecutive vertices and prime pivots; pointwise and fixed-assignment conditional clauses of Corollary 2.6 in finite cylinders. |
| [`InfiniteWordTransfer.lean`](InfiniteWordTransfer.lean) | Measurable word events, exact finite/infinite measure and probability identities, and the real pointwise bound of Corollary 2.6 in the infinite source model. |
| [`InfiniteConditionalWords.lean`](InfiniteConditionalWords.lean) | Positive measurable assignment atoms, identification with `F_Y`, exact joint word/atom measure and conditional ratio in the infinite model. |
| [`InfiniteWordFirstMoment.lean`](InfiniteWordFirstMoment.lean) | Finite probability sum, integrable occurrence count, exact first-moment identity and summed pointwise error. |
| [`WordDefectCounting.lean`](WordDefectCounting.lean) | Word defect mass and finite comparison with the historical arithmetic mass, explicitly accounting for the shifted root `x - 1`. |
| [`WordDefectAsymptotics.lean`](WordDefectAsymptotics.lean) | Uniform `N^(1/2+o(1))` word defect mass in every fixed logarithmic band. |
| [`WordFirstMomentAsymptotics.lean`](WordFirstMomentAsymptotics.lean) | Summed probability and actual expectation clauses of Corollary 2.6, uniformly over all dyadic masks and distinct-word dictionaries. |
| [`ValueRelations.lean`](ValueRelations.lean) | Abstract two-parity nullity and factor-four weight comparisons, including the finite host correction. |
| [`TwoWindowParity.lean`](TwoWindowParity.lean) | Actual two-window value matrices, separate block parities, their linear equivalence with start relations, and finite sums over ordered separated pairs. |
| [`ValueSquareRelations.lean`](ValueSquareRelations.lean) | Full-value relations characterized by square products of indexed subsets; nonzero nullity characterized by a nonempty square-product subset. |
| [`TwoWindowSquareHosts.lean`](TwoWindowSquareHosts.lean) | Identification of full-value hosts with unrestricted arithmetic square-product hosts, and the finite inequality (3.24) with those hosts. |
| [`FullPrimeAssignment.lean`](FullPrimeAssignment.lean) | Large-prime assignment lemmas for arbitrary full-value coefficients, without either block-parity constraint. |
| [`FullHostCounting.lean`](FullHostCounting.lean) | Inclusion of unrestricted square-product hosts in the retained congruence cover and an explicit finite dyadic kernel-sum bound. |
| [`FullHostAsymptotics.lean`](FullHostAsymptotics.lean) | Explicit exponential majorant and uniform `N^(3/2+o(1))` bound for every pair mask within a dyadic square. |

The main declarations and their exact hypotheses are listed in
[`ENDPOINTS.md`](ENDPOINTS.md). These endpoints add no external literature
premise; importing a historical module containing such an interface does
not itself make the new theorem conditional on that interface.

## Representation and scope

Words are `Fin B → F₂`; a bit denotes its sign through the retained `phase`
map. Their vertices are exactly `x - 1 + j`, for `j < B`. Finite probabilities
are rational cardinality ratios. `InfiniteWordTransfer` identifies them
with the corresponding event measure under `infiniteRademacherMeasure`
and its real-valued probability.

The finite one-window bounds require `x ≥ 2` and
`x - 1 + B ≤ M + 1`, where `M` is the inclusive prime-cylinder cutoff.
The infinite pointwise endpoint chooses an adequate cylinder internally and
exposes no cutoff hypothesis. The infinite conditional endpoint assumes
`Y ≤ M`, `B ≤ Y`, and an odd valuation at a prime above `Y` for every
vertex. It proves
`measure(word ∩ atom) = measure(atom) / 2^B` and the corresponding exact
ratio on every atom. The partition into positive measurable atoms generates
exactly `F_Y`. A general conditional-expectation API could repackage this
proved atom law; it is optional presentation work, not a missing step in
the established summed first moment.

For the summed clause, `s` is any finite mask in `[N, 2N)` and
`W : Finset (Fin B → F₂)` is a dictionary of distinct words. The finite
sum of event indicators is integrable and its integral equals
`wordProbabilitySum B s W`. For fixed `0 < c₁ < c₂` and every integer
`k > 0`, a threshold depending only on `c₁`, `c₂` and `k` gives

```text
|E[wordOccurrenceCount B s W] - |s| |W| / 2^B|^(2k)
  ≤ (|W| / 2^B)^(2k) N^(k+1)
```

simultaneously for every `B` with `c₁ log N ≤ B ≤ c₂ log N`, every
such `s`, and every `W`. This is the dyadic
`O(|W| 2^(-B) N^(1/2+o(1)))` statement. Empty masks and dictionaries are
included; no balance condition on `N / 2^B` is imposed. Macroscopic
extensions beyond the dyadic mask domain are not asserted here.

For two windows, `B = L + 1`. The final finite endpoint accepts any
`I : Finset ℕ` such that every `x ∈ I` satisfies `2 ≤ x` and
`x + L ≤ M + 1`. It sums over the ordered pairs in `I × I` with
`L < Nat.dist x y`. The correction counts pairs having a nonempty
square-product subset of the full vertex occurrences, with **no parity
restriction** on either block. This arithmetic host set is defined without
a cylinder cutoff and is proved equal to the full-value nullity host set
under the stated conditions.

The new counting theorem applies to every pair mask `s` inside
`dyadicBlock N × dyadicBlock N`, with `N ≥ 2` and `L ≤ N`; separation is
not required for the host bound. Its explicit majorant is
`8 (L + 1) N sqrt(3N) exp(4 sqrt(L + 1))`. For each `C ≥ 0` and integer
`k > 0`, a threshold depending on `C` and `k`, independent of `L` and `s`,
gives `card(squareProductHosts L s)^(2k) ≤ N^(3k+1)` whenever
`L + 1 ≤ C log N` and the other displayed hypotheses hold. This closes
the dyadic unrestricted host-count component, including deterministic masks.

The conditional wording on article page 9 should explicitly say that the
large prime has **odd valuation**. This is already the convention on page 8
and in Lean. [`MANUSCRIPT_NOTES.md`](MANUSCRIPT_NOTES.md) records a proposed
clarification for a future revision, with a counterexample to the literal
weaker reading. Proposed manuscript changes are tracked in the
[v3 revision log](../docs/PAPER_V3_REVISION_LOG.md). No v3 manuscript replaces
the v2.8.2 documents bound above.

## Remaining work and qualification boundary

- Proposition 3.26: extend the dyadic host estimate to the remaining
  macroscopic/geometric regimes, prove the raw profile of Theorem 3.1,
  and assemble asymptotic conclusion (3.25). The dyadic host estimate and
  finite parity, relation and square-host identifications are complete.
- Proposition 3.27 and the signed marked-field, dictionary and crossover
  theorems require further arithmetic and probabilistic development.

The historical `PaperC` core, its canonical declarations and the existing
Palomar records preserve their original scope. `PaperCV11` remains the name
of the earlier reusable overlay; its numbering is not the v2.8.2 theorem map.
No new Palomar qualification, Comparator result, or certification of the
complete article–companion package is claimed here. A future submission
requires its own frozen public statements, dependency audit and evidence.
