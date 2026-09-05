# Paper C v2.8.2 formalization overlay

`PaperCV282` is an additive Lean library for the English article *Long runs
and rare patterns of a random completely multiplicative function*, version
2.8.2, and its technical companion, both dated 5 September 2026. It reuses
the historical `PaperC` model and proofs. The retained-core authority is
commit `b3cf107d2df629453a5da8e84f2bad29eea0bf94`.

The current three-batch development proves the pointwise bound of Corollary
2.6 under the infinite Rademacher law and its exact conditional probability
on every small-prime assignment atom. The partition into these positive
measurable atoms generates exactly the sigma-algebra `F_Y` of all prime
signs at most `Y`.
It also proves finite inequality (3.24) for actual separated windows and a
uniform dyadic `N^(3/2+o(1))` bound for unrestricted square-product hosts.

The general conditional-kernel formulation, the summed first-moment clause
of Corollary 2.6, the macroscopic extensions and the relation profiles needed
for the complete asymptotic conclusion (3.25) remain separate obligations.

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

The eleven mathematical modules contain **116 named declarations: 89
theorems, 25 definitions and two named local instances**. The audit includes
`instMeasurableSpaceF2Discrete` in both `InfiniteWordTransfer` and
`InfiniteConditionalWords`, supplying the discrete measurable structure
used by the retained model. Its gate requires
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
ratio on every atom. Atom positivity and the equality of its generated
sigma-algebra with `F_Y` are proved. A general conditional-expectation or
kernel API is not asserted by these atom identities.

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

- Corollary 2.6: expose the infinite conditional kernel and close the uniform
  first-moment sum over masks and dictionaries in the logarithmic band.
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
