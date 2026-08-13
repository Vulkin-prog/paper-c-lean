# Halter--Koch conductor-fibre bridge

- Bridge ID: `HK13-QO-conductor-fibres`
- Lean proposition: `PaperC.PellInput.QuadraticOrderConductorFiberBoundStatement`
- Current rc2 implication status: `agent_checked_with_open_gap`
- Current source locator: `Theorem 1.1.6(1)(b), printed pp. 4-5; Definition 5.1.6 and Theorem 5.1.7(1),(3), printed pp. 118-119; Theorem 5.2.3(1),(2), printed p. 125; Theorem 5.2.5(1), printed pp. 126-127.`
- Primary-source access: `partial`
- Review level: agent counter-audit; independent human review required

This is an open-obligation report, not a positive certificate.  In particular,
it supersedes, for rc2 reporting purposes, the stronger historical wording
embedded in the frozen core metadata.  The 382 core files are intentionally
left byte-identical, so that wording is retained only as provenance.

## Cited source and intended use

Franz Halter--Koch, *Quadratic Irrationals: An Introduction to Classical
Number Theory*, Chapman & Hall/CRC, 2013, DOI
[10.1201/b14968](https://doi.org/10.1201/b14968).  The project cites Theorem
1.1.6(1)(b), Definition 5.1.6, Theorems 5.1.7(1),(3), 5.2.3(1),(2), and
5.2.5(1), on pages 4--5, 118--119, and 125--127.

The intended mathematical route is to extend a norm-`M` element of the order
`Z[sqrt(D)]` to an ideal of the maximal quadratic order, count the possible
extended ideals dividing `(M)`, and use the finite quotient of maximal-order
units by order units as a conductor colour.  Equal extended ideals and equal
unit cosets should then force equality of the original principal ideals.

## What the Lean premise actually asks for

For every admissible `D` and nonzero `M`, the record
`QuadraticOrderConductorData D M` contains:

1. a number field `K` declared to be a quadratic extension of `Q`;
2. for every integer pair, an ideal of `O_K` dividing `(M)`;
3. for every integer pair, a colour in `Fin 4`;
4. a uniform proof that two norm-`M` solutions with the same ideal and colour
   generate the same principal ideal in `Z[sqrt(D)]`.

The record is deliberately strong and global: it asks for choices on all
integer pairs, including harmless defaults off the norm equation.  Moreover,
the typeclass fields currently say only that `K/Q` is quadratic; the required
connection between `K` and this particular `D` must be part of the
construction, not inferred from the record type alone.

## Missing source-to-record construction

A complete derivation still has to provide all of the following steps.

- Construct `K = Q(sqrt(D))` and the embedding
  `Z[sqrt(D)] -> O_K`, handling the two possible maximal orders.
- Send `s=(x,y)` to `alpha_s=x+y*sqrt(D)` and construct an extended ideal
  `J_s`; prove `J_s` divides `(M)` from
  `alpha_s * conjugate(alpha_s) = M`.
- Identify the conductor (one or two in the relevant presentation) and prove
  the required bound on `O_K^x / Z[sqrt(D)]^x`.
- Choose representatives coherently and encode the at-most-three unit cosets
  in the historical padded type `Fin 4`.
- Prove that the same extended ideal and the same unit coset imply that the
  quotient of two generators is a unit of `Z[sqrt(D)]`, hence that their
  principal ideals in the smaller order are equal.
- Treat negative `M` and define the off-equation default values without
  disturbing the uniform implication.

The existing project theorem that pads `Fin 3` into `Fin 4` packages data once
the essential conductor-descent structure is assumed.  It does not construct
that structure from Halter--Koch and therefore does not close this gap.

## Conclusion

The cited material is relevant to the intended construction, but the full
implication to `QuadraticOrderConductorFiberBoundStatement` has not been
independently established.  The correct rc2 status is
`agent_checked_with_open_gap`.  Until a detailed derivation or a Lean
construction is supplied and reviewed, public claims must continue to say
that the current Lean certification of Theorem 1.1 is conditional on this
ordinary literature-facing premise. The printed maximal-order proof is a
separate mathematical route; see `docs/HK_INTERFACE_ADJUDICATION.md`.
