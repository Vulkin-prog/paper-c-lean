# Qualification of the D.4 upper-point-law correction

On 20 September 2026, all **29 Limits declarations** passed exact Comparator
comparison, the **Lean 4.34.0 kernel** and **NanoDa** at source commit:

`7821a698fa200b8a73cfeea32e1a190f8c0bd3b0`

The two strengthened D.4 statements prove measurability, probability normalization
and, for the conditional law, positive conditioning mass. No theorem premise was
added. The other six family interfaces and the dependency pins are unchanged.

## Evidence

- [validation.json](validation.json): source/configuration/metadata hashes before
  and after replay, tool binary hashes, exact selected declarations, exit status
  and successful acceptance by both kernels. The replay took 190 seconds.
- [preflight.json](preflight.json): official metadata contract and canonical import
  closure checks for all seven families (89 selected declarations, 8,908 canonical
  dependency sources). This compact receipt hashes the full local closure list.
- [transcript-excerpts.txt](transcript-excerpts.txt): both kernel acceptance messages;
  the full local transcript's hash is recorded in the validation receipt.

The two changed modules also compile directly, and all 20 candidate-guard tests
pass. The checks apply to the recorded source hashes; this documentation and
receipt packaging does not change those sources.

The installed tool revisions and local execution restrictions are the same as in
the [initial qualification record](../2026-09-20/README.md#tool-identities-and-execution).
The protected configuration retains all 29 names and `enable_nanoda: true`.
To reproduce the check, run:

```sh
./palomar/v3prel/verify-comparator.sh comparator/v3prel_limits.json
```

This is mechanical qualification, not a Palomar review or registration. The
[review follow-up](../../../../docs/PALOMAR_REVIEW_FOLLOWUP.md) describes the
objection and correction. GitHub repeats all seven configurations on the PR and
on `main` after merge; use the successfully qualified merged commit to resubmit.
