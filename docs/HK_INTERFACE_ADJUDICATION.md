# Historical Halter--Koch interface adjudication

This note adjudicates a historical attribution.  It does not claim that the
printed Halter--Koch argument has been formalized.

## Decision

The mathematical and formal statuses are separated.

1. **Printed mathematics.** The proof of the Pell-type counting lemma in the
   v09 manuscript works in the maximal order of the quadratic field: it counts
   ideal divisors of `(M)` and then generators of a principal ideal modulo the
   unit group. That printed route does not require the stronger
   `QuadraticOrderConductorData` compatibility record retained by the Lean
   encoding.
2. **Current Lean route.** Lean now proves
   `QuadraticOrderConductorFiberBoundStatement` internally. It constructs
   `K = ℚ(√D)`, the embedding `ℤ[√D] → O_K`, and the extended principal
   ideals. Trace and norm show that `2 O_K ⊆ ℤ[√D]`. The quotient
   `O_K / 2 O_K` has four elements and supplies the `Fin 4` colour of a relative
   unit. Equal colours make the quotient of two relative units congruent to
   one modulo `2`; lifting that unit and its inverse descends equality to
   principal ideals in `ℤ[√D]`. The construction is total off
   the norm equation and covers negative `M`.
3. **Registry status.** `HK13-QO-conductor-fibres` retains `kind: external`
   solely to record the historical provenance of the compatibility boundary,
   but now has `status: discharged`, with the internal Lean theorem as its
   discharge. The source-shaped three-coset record and its `Fin 3 → Fin 4`
   adapter remain for compatibility and for documenting the route that was
   originally contemplated. The discharge proof neither assumes nor
   instantiates that record.
4. **Public boundary.** Halter--Koch is no longer an argument of the canonical
   endpoints. The finite-cylinder form of Theorem 1.1 and its main Comparator
   target have exactly three open literature premises: Arratia--Goldstein--
   Gordon, Evertse--Silverman, and Nicolas--Robin. Across the repository, six
   external bridges remain open.

The historical source counter-audit may still document that the cited pages
were not turned into the former source-shaped record. That statement remains
true. It is no longer a formal gap in the canonical Lean route: the kernel
proof closes the registered compatibility proposition by an independent
elementary construction. It would therefore be inaccurate to describe this as
a formalization, verification, or machine-checked transcription of the
Halter--Koch pages.

The accurate short description is:

> The historically attributed conductor-fibre interface is discharged by a
> direct modulo-two Lean construction independent of the cited source.

## What the closure proves

The critical ingredients are all kernel-checked:

- the quadratic field and its ring of integers are connected to the given
  squarefree nonsquare `D`;
- every solution is assigned an ideal divisor of `(M)`, and harmless defaults
  make the assignment total on all integer pairs;
- the quotient `O_K / 2 O_K` has cardinality four;
- a maximal-order unit congruent to one modulo `2`, together with its inverse,
  lifts to a unit of `ℤ[√D]`;
- equal extended ideals and equal colours therefore imply equality of the
  original principal ideals.

This proves the registered `Fin 4` compatibility proposition directly. It
does not assert that the particular abstract `UnitQuotient` field in
`HalterKochConductorDescentData` has been instantiated, either from the cited
book or by the direct proof. The direct construction instead produces the
downstream `QuadraticOrderConductorData` required by the proposition.

## Review consequence

The historical objection "the cited pages have not been converted into the
source-shaped record" is preserved rather than erased, but is no longer an
open dependency of a canonical endpoint. A human reviewer may still review
the direct modulo-two construction on its own mathematical merits. Such a
review would concern the internal proof, not fidelity to Halter--Koch.

The disposition of this and the other historical review findings is recorded
in [`counter_reviews/DISPOSITION.md`](../counter_reviews/DISPOSITION.md).

## Release consequence

The closure changes the Lean core, the bridge inventory, canonical theorem
signatures, and the main Comparator theorem from four premises to three. The
published v0.48.0 hardened evidence therefore does not qualify the new state,
even though its historical run remains valid for the exact old bytes. A
qualified release requires regenerated audit artifacts and a fresh hardened,
non-root, no-fallback Comparator run bound to the final source commit and PDF
hashes. The transfer Comparator remains a separate unconditional exact-law
check and must be rerun as part of the same qualification.
