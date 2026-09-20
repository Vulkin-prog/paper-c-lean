# Qualification after the remaining-dossier audit

On 20 September 2026, all **33 declarations** in Boundary, Crossover,
Microscopic and Palm passed exact Comparator comparison, the **Lean 4.34.0
kernel** and **NanoDa** at source commit:

`ab244fb21363a66e84fd08053ba7d7ca367c3aac`

| Family | Declarations | Result | Replay time |
|---|---:|---|---:|
| boundary | 7 | Lean + NanoDa accepted | 134 s |
| crossover | 11 | Lean + NanoDa accepted | 158 s |
| microscopic | 6 | Lean + NanoDa accepted | 142 s |
| palm | 9 | Lean + NanoDa accepted | 144 s |

## Evidence

- [validation.json](validation.json): exact selected names, source/configuration/
  metadata hashes before and after every replay, tool binary hashes, statuses,
  timings and disk reserve. Each protected configuration enables NanoDa.
- [preflight.json](preflight.json): official metadata contract and canonical import
  checks for all seven configurations (89 declarations and 8,908 dependency
  sources). The compact receipt hashes the full local canonical closure list.
- [transcript-excerpts.txt](transcript-excerpts.txt): acceptance messages from both
  kernels in each replay. Full local transcript hashes remain in the receipt.

All eight changed Challenge/Solution modules compile directly, all 20 candidate
guard tests pass, and the current manuscript identity check passes. No manuscript
or mathematical-development source is changed by this audit.

These checks apply to the recorded hashes. The subsequent evidence packaging
changes only this record. The prior [Limits correction record](../2026-09-20-limits-probability/README.md)
remains unchanged: its two Lean modules and metadata are unchanged by the
remaining-dossier audit. Neither earlier receipt is relabelled with this commit.
The first two registered family interfaces are also unchanged.

## Reproduction and scope

Tool revisions and local resource restrictions match the
[initial qualification record](../2026-09-20/README.md#tool-identities-and-execution).
The four replays ran serially with real landrun, independent Lean export/NanoDa,
no AF_UNIX in the checking unit, a 70 GiB memory ceiling, no swap and disk guarding
on the Ubuntu partition. They do not reproduce Palomar's whole server pipeline.

Replay each family with the checked-in runner, for example:

```sh
./palomar/v3prel/verify-comparator.sh comparator/v3prel_crossover.json
```

The [audit report](../../../../docs/PALOMAR_REMAINING_DOSSIERS_AUDIT.md) records
what was strengthened and the limits of this review. GitHub repeats all seven
configurations on the PR and after merge. Submit the qualified merged commit;
mechanical verification is not automated-review acceptance or registration.
