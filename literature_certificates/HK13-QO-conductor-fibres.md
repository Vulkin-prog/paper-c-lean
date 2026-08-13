# Halter--Koch conductor-fibre bridge: historical closure note

- Bridge ID: `HK13-QO-conductor-fibres`
- Lean proposition: `PaperC.PellInput.QuadraticOrderConductorFiberBoundStatement`
- Current bridge status: `discharged`
- Discharged by: `PaperC.PellInput.quadraticOrderConductorFiberBound`
- Historical role: `closure note`

This file is no longer an active literature certificate or an open-obligation
report. It preserves the history of the former source-facing boundary and
records how the project now closes it internally. The canonical endpoints do
not take the Halter--Koch proposition as a premise.

## Historical source route

The former bridge cited Franz Halter--Koch, *Quadratic Irrationals: An
Introduction to Classical Number Theory*, Chapman & Hall/CRC, 2013, DOI
[10.1201/b14968](https://doi.org/10.1201/b14968), especially Theorem
1.1.6(1)(b), Definition 5.1.6, Theorems 5.1.7(1),(3), 5.2.3(1),(2), and
5.2.5(1), on printed pages 4--5, 118--119, and 125--127.

That proposed route was to extend principal ideals from `Z[sqrt(D)]` to the
maximal quadratic order and then control the loss of information by a bounded
unit quotient. The previous version of this file correctly reported that the
full source-to-record construction had not been supplied in Lean.

## Current direct Lean construction

The public theorem now constructs the historical record directly, without
using a theorem from Halter--Koch. In outline, the implementation:

1. takes the quadratic algebra `K = Q(sqrt(D))` and embeds `Z[sqrt(D)]` into
   its ring of integers;
2. constructs the extended principal ideal attached to each solution and
   proves that it divides `(M)`;
3. proves from trace and norm calculations that `2 O_K` lies in the embedded
   quadratic order;
4. identifies `O_K / 2 O_K` with a four-element type and uses its residue as
   the required `Fin 4` conductor colour;
5. shows that equal extended ideals and equal colours make the relative unit
   congruent to one modulo `2`, lifts that unit back to `Z[sqrt(D)]`, and
   concludes equality of the two principal ideals in the smaller order.

This proves the exact compatibility statement consumed by the Pell counting
development. It does not claim a separate formalization of every printed
Halter--Koch theorem, nor the stronger source-shaped bound by three unit
cosets; the four residue classes modulo two suffice for the existing `Fin 4`
interface.

## Audit consequence

`HK13-QO-conductor-fibres` remains registered with kind `external` for stable
provenance, but its status is `discharged`. This note remains in the hashed
literature-documentation fileset so the former gap is not erased. It is not
one of the three active source certificates for Theorem 1.1 and it contributes
no open premise to the canonical endpoints.
