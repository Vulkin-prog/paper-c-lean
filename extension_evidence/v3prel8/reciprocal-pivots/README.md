# Saddle, reciprocal pivots and directed footprint

The [receipt](validation.json) identifies the exact current sixteen-module
`PaperCPrel8` sources, a successful **24-library build (10,131 Lake jobs)** and
the **98-name axiom audit**. This batch adds **30 proved theorems**, with no
proof hole or axiom beyond `propext`, `Classical.choice` and `Quot.sound`.
Full compressed build and audit transcripts retain both hashes.

The estimates of F.4, F.5 and F.6 are now proved in explicit uniform forms:
the actual saddle envelope loses at most `2*nu/u` eventually; the reciprocal
bound holds for all natural ceilings `X` with `2X >= M`; and logarithmic support
factors are absorbed in the final directed-footprint estimate. The ordinary
PNT remainder remains the sole existing literature argument used by the
arithmetic estimates. No reciprocal bound is assumed.

The [coverage ledger](../../../docs/FORMALIZATION_COVERAGE_V3PREL8.md) records
the exact hypotheses and the remaining work. These estimates do not yet give
the full microscopic Poisson theorem: the maximal-support marked field,
infinite-source conditioning, Palm ledger and independent tails still need
assembly. Other new 3PREL8 families also remain incomplete.

All 1,171 baseline Lean files and the author's supplied source/PDF bytes are
unchanged. The ten payload/audit regression tests, inventories, root guards
and baseline audit source checks pass. Earlier [prime-forcing evidence](../prime-forcing/README.md)
is preserved as a historical snapshot.

This receipt is not a new Palomar, Comparator or NanoDa qualification.
