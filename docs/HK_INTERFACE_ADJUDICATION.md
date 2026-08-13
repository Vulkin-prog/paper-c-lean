# Halter--Koch interface adjudication

## Decision

The mathematical and formal statuses are separated.

1. **Printed mathematics.** The proof of the Pell-type counting lemma in the
   v09 manuscript works in the maximal order of the quadratic field: it counts
   ideal divisors of `(M)` and then generators of a principal ideal modulo the
   unit group. That printed route does not require the stronger
   `QuadraticOrderConductorData` record used by the current Lean encoding.
2. **Current Lean route.** The canonical Lean endpoints that consume
   `HK13-QO-conductor-fibres` remain conditional on the explicitly stated
   proposition `QuadraticOrderConductorFiberBoundStatement`. The source audit
   has not derived that entire record from the cited Halter--Koch pages.
3. **Permitted public claim.** It is accurate to say that the internal finite
   deductions are Lean-checked conditional on seven registered literature
   interfaces. It is not accurate to call the affected theorems fully and
   unconditionally Lean-certified.

This adjudication does **not** silently turn the manuscript's mathematical
theorems into statements conditional on Halter--Koch. It identifies a mismatch
between the conventional printed proof route and the stronger current formal
interface.

## Formal closure criteria

The formal gap is closed by either of the following routes.

- Formalize the maximal-order proof actually printed in the manuscript, with
  the ideal-divisor count and the unit-orbit count needed by the Pell lemma.
- Or construct, in Lean and from the cited source statements, the complete
  conductor/ideal/colour record currently assumed, including the field tied to
  the particular `D`, the two maximal-order cases, negative `M`, coherent unit
  cosets and off-equation defaults.

Until one route is completed and reviewed, the bridge remains `external/open`
and `agent_checked_with_open_gap`.

## Release consequence

A release may publish the repository as a transparent conditional
formalization, but release notes, repository metadata and papers must preserve
the distinction above. Hardened Comparator evidence certifies the implication
from the explicit premises; it does not discharge the premise or certify the
source-to-record mapping.
