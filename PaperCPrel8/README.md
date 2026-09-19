# 3PREL8 proof components

This library contains **68 proved theorems in eleven modules**. It is an
extension of the previously validated development, not a formalization of every
new 3PREL8 conclusion. The [coverage ledger](../docs/FORMALIZATION_COVERAGE_V3PREL8.md)
records the remaining arithmetic, probability and asymptotic obligations.

| Module | Proved component |
|---|---|
| `PalmStein` | Lattice gradient bound, exact Palm generator identity and finite Poisson comparison |
| `DictionarySelection` | Actual uniform subset inclusion and averaged source-pair collision identity |
| `InformationBudget` | Unique crossing, constrained maximum and both exponent margins |
| `PrivateForcing` | Constructed private-block forcing and its full conditional-law identity |
| `OddPrimePivot` | Actual largest-odd-prime count and inherited uniform Rankin estimate |
| `PivotGeometry` | Actual largest-odd-prime private coordinates in the retained finite cylinder |
| `PrimeForcing` | Arithmetic prime-sign modification, original uniform conditional law and directed preservation |
| `HardConditionalForcing` | Complete conditional arithmetic-sample law for small-prime events and weighted identities |
| `SignedPalmForcing` | Actual signed exact-run conditional law and its exact geometric rate |
| `DirectedFootprint` | Both finite F.6 inequalities using the actual reciprocal-pivot population |
| `EmpiricalTransfer` | Discrete overlap identity, Scheffe convergence and countable almost-sure completion |

The analytic Stein and PNT inputs remain explicit theorem arguments, as in the
baseline. The actual finite-cylinder forcing is now proved; assembly of the maximal-support
marked field and its infinite-source conditional law remains open, along with
the reciprocal-pivot asymptotics, final Palm–Stein ledger and summable frequency
bounds for the specified moving windows. These assumptions are not presented as discharged
source-facing conclusions. No proof placeholder or new Lean axiom is used.

```sh
lake build PaperCPrel8
lake env lean PaperCPrel8/Audit.lean > prel8-audit.log 2>&1
python3 scripts/check_prel8_audit.py --log prel8-audit.log
```

The audit requires all names in `audit-names.json`, in order, and rejects any
foundational axiom outside `propext`, `Classical.choice` and `Quot.sound`.
[Current validation evidence](../extension_evidence/v3prel8/prime-forcing/README.md) binds the build and
audit results to exact source hashes. No new Palomar qualification is claimed.
