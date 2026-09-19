# Empirical Poisson corollary at the literal paper scales

The [receipt](validation.json) binds **321 proved theorems in 65 modules** to
exact source hashes. This batch adds **25 theorems**. All **24 libraries build
(10,180 Lake jobs)** and the exact **321-name axiom audit passes**, using only
`propext`, `Classical.choice` and `Quot.sound`.

**Corollary 7.8a is proved with the baseline microscopic inputs.** For each
fixed 0<alpha<1 and tau>0, at M_k=2^k and the exact rounded lengths and windows,
the genuine arithmetic empirical count law converges almost surely in TV to
Poisson(tau). The numerical prerequisites are all proved: the logarithmic
length band, intensity divergence, every fixed information margin, positive
contained windows, summable h/n and h/N, and the limiting mean tau.

The field error is `10*exp(-nu_M)+4*M^(-1/6)` and is summable on these scales.
The additional window-growth clauses have explicit constants:
`(tau/2)*M*exp(-alpha*V_M)<=h<=2*tau*M*exp(-alpha*V_M)` eventually, and
`log(h)/log(M)->1`.

The same explicit directional Stein solution, ordinary PNT, Laishram-Shorey
and Nicolas-Robin inputs remain. No simultaneous all-parameter or all-size
claim is made. The support obstruction 7.8b remains open, as do dictionary,
information-adapted saddle and Palm/cumulant families. F.2's analytic solution
construction remains an explicit baseline premise. Full 3PREL8 alignment
is incomplete.

All **1,171 baseline Lean files** and **28 manuscript payload files** remain
unchanged. Ten regression tests, inventories and repository guards pass.
Complete build/audit transcripts have compressed and uncompressed hashes.
The [previous receipt](../empirical-windows/README.md) remains historical and
bound to its original sources. No Palomar or NanoDa/Comparator qualification
is claimed for these new declarations.
