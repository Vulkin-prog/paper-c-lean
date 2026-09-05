# Paper C v2.8.2: first finite formalization batch

`PaperCV282` is an additive Lean library for the English article *Long runs
and rare patterns of a random completely multiplicative function*, version
2.8.2, and its technical companion, both dated 5 September 2026. It reuses the
historical `PaperC` model and proofs. The retained-core authority is commit
`b3cf107d2df629453a5da8e84f2bad29eea0bf94`.

This first batch proves the pointwise and fixed-small-prime-assignment
claims corresponding to Corollary 2.6 in a finite prime cylinder. It also
proves the abstract finite linear-algebra and summation step underlying
Proposition 3.26. It does **not** prove either result's asymptotic summed
conclusion, nor the new two-window estimate or main theorems of v2.8.2.

## Sources and toolchain

The exact input documents are bound by SHA-256 in
[`source_manifest.json`](source_manifest.json):

| Input | Pages | SHA-256 |
|---|---:|---|
| `paper_C_version_2_8_2_en.pdf` | 52 | `263682a1f2aa8301f06bf811fea1f81f42cd4493ccc4e1b94242a66cacfbd623` |
| `paper_C_version_2_8_2_technical_companion_en.pdf` | 23 | `60d6f110aa057ebd9b1c79eaa291bc42759b5f021ef03807d9405a7ec473b094` |

Use `leanprover/lean4:v4.32.0` and mathlib `v4.32.0`, locked in the repository
manifest to `81a5d257c8e410db227a6665ed08f64fea08e997`. This overlay does not
require a toolchain upgrade. With those dependencies available, its library
target is built with:

```sh
lake build PaperCV282
python3 scripts/check_v282_audit.py --check-source
lake env lean PaperCV282/Audit.lean > PaperCV282-Audit.log
python3 scripts/check_v282_audit.py --log PaperCV282-Audit.log
```

These commands are reproduction instructions, not a recorded build verdict.
The source manifest records provenance and scope; it is not a proof audit or
a release certificate.

The dedicated development workflow builds both overlays and audits all 32
named declarations in these three modules (24 theorems and 8 definitions).
The audit gate requires complete declaration coverage, permits only the
standard `propext`, `Classical.choice` and `Quot.sound` dependencies, and
rejects changes to the historical Lean/mathlib pins. Its source inventory
is a deliberately restricted coverage check; Lean's kernel checks the proofs.

## Implemented components

- [`PrescribedValues.lean`](PrescribedValues.lean) defines absolute valuation
  systems and word equations using the existing binary Rademacher model. It
  derives the affine probability formula, a nullity-based error bound,
  private-coordinate rank control, and the translation of the right-hand
  side after fixing the small prime coordinates.
- [`WindowValues.lean`](WindowValues.lean) specializes those facts to the
  article's consecutive vertices `x - 1 + j`, for `j : Fin B`. It constructs
  private primes from actual nondefectiveness and proves the pointwise bound
  and exact conditional marginal of Corollary 2.6 in the finite cylinder.
- [`ValueRelations.lean`](ValueRelations.lean) shows that imposing two linear
  parity constraints reduces the full relation-space dimension by at most
  two. It derives the factor-four weight comparison and sums the extra
  constant only over nonzero full-relation hosts.

The public endpoints and their precise boundaries are listed in
[`ENDPOINTS.md`](ENDPOINTS.md). These finite results introduce no external
literature premise. Their imports reuse historical definitions and proofs;
an imported file containing a literature interface does not mean that the
new endpoint assumes that interface.

## Representation and scope

Words are `Fin B → F₂`; bit `b` denotes the sign `phase b = (-1)^b` in the
retained model. Probabilities are rational cardinality ratios in the
uniform finite cylinder of primes at most `M`. In the window endpoints,
`x ≥ 2` makes every displayed integer positive, and
`x - 1 + B ≤ M + 1` ensures that every vertex, including `x + B - 2` when
`B > 0`, lies within the cylinder cutoff. Here `M` is the cylinder cutoff;
it need not be the ambient scale denoted by `M` elsewhere in the article.

The conditional endpoint means the uniform law of the remaining prime
coordinates above `Y`, for **each** fixed assignment at primes at most `Y`.
The assembly identity proves that these equations are the original word
equations with that assignment fixed. It does not yet expose a theorem
using a measure-theoretic conditional kernel on the infinite product model.

For Proposition 3.26, the map into `Fin 2 → F₂` is still an arbitrary linear
map. The actual two block-parity maps, their tree-boundary identification,
and the arithmetic host bound are not supplied by this first batch.

## Remaining mathematical work

For Corollary 2.6, connect the finite word law explicitly to the infinite
source law and its conditional formulation, then sum the defect weights
uniformly over the article's logarithmic band, deterministic masks and
collections of distinct words. The stated `O(m p_B N^(1/2+o(1)))` conclusion
is not yet an endpoint.

For Proposition 3.26, instantiate the full-value matrix and the two block
parities for separated windows, identify the constrained kernel with the
relative-sign start relations, and identify the finite host count with the
article's unrestricted square-relation hosts. Only then can the finite
comparison be combined with the required uniform host estimate and
Theorem 3.1 to obtain (3.24)–(3.25). Proposition 3.27's capped arithmetic
profile remains separate work.

## Historical and qualification boundary

The historical `PaperC` core, its canonical declarations, and the existing
Palomar records keep their original scope. `PaperCV11` remains the name of
the earlier reusable overlay; its v1.1 numbering and endpoint queue do not
constitute a theorem map for these v2.8.2 PDFs.

No new Palomar qualification, Comparator result, or certification of the
complete v2.8.2 article–companion package is claimed here. The article itself
distinguishes the historical v0.9 formalization record from the present PDFs
on page 50. A future v2.8.2 submission needs its own frozen public statements,
dependency audit, and qualification evidence.
