# Palomar qualification entries

This repository maintains four independent Palomar entries. Palomar accepts
one Comparator configuration per submission, while one configuration may
select several declarations. The related clauses of a paper theorem are
therefore grouped together instead of being submitted one declaration at a
time.

Each registered result has a stable identifier and a fixed path pair:

| Entry | Palomar identifier | Comparator configuration | Formalization metadata |
|---|---|---|---|
| Theorem 1.1 | `PALOMAR-2026-08-20-000007` | `comparator/theorem_one_one.json` | `palomar/formalization.yaml` |
| Theorem 1.2(i--iii) | `PALOMAR-2026-08-26-000010` | `comparator/theorem_one_two.json` | `palomar/theorem_one_two/formalization.yaml` |
| Theorem 1.4 and Corollary 11.3 | `PALOMAR-2026-08-26-000012` | `comparator/theorem_one_four_and_corollary_eleven_three.json` | `palomar/theorem_one_four_and_corollary_eleven_three/formalization.yaml` |
| Theorem 16.2 and Corollary 16.4 | `PALOMAR-2026-08-27-000008` | `comparator/theorem_sixteen_two_and_corollary_sixteen_four.json` | `palomar/theorem_sixteen_two_and_corollary_sixteen_four/formalization.yaml` |

These are separate Palomar results because they select different mathematical
claims and different Comparator configurations. A correction to one result
must cite its existing identifier and retain the same repository, project path,
and Comparator path; Palomar then creates the next version of that identifier.
Unchanged results should not be resubmitted.

## Challenge boundaries

Every new Challenge is autonomous and imports only Mathlib modules. It does not
import `PaperC`, another local Challenge, or a local helper. Each Solution
reproduces the same declarative interface independently, imports the proved
project development, and contains no `sorry`.

| Challenge | Lines | Bytes | Intentional placeholders |
|---|---:|---:|---:|
| `Challenge.lean` | 721 | 30,480 | 1 |
| `ChallengeTheoremOneTwo.lean` | 816 | 31,042 | 3 |
| `ChallengeTheoremOneFour.lean` | 480 | 16,551 | 2 |
| `ChallengeTheoremSixteenTwo.lean` | 652 | 21,918 | 4 |

All four stay below Palomar's hard limits of 1,000 lines and 100 KiB. They
exceed the preferred 300-line surface because the audited statement boundaries
include explicit model definitions and literature-premise interfaces; this may
produce a non-blocking size warning.

Theorem 1.2(ii--iii) is represented by Laplace-functional convergence (plus
mark tightness for (iii)), rather than by a direct `Tendsto` of point-process
laws in the paper's vague topology. The metadata records this fidelity
boundary. The compared results remain conditional on ordinary, explicitly
stated literature propositions: three for Theorem 1.2, two for Theorem
1.4/Corollary 11.3, and six for Theorem 16.2/Corollary 16.4. These propositions
are theorem arguments, not Lean axioms.

## Reproduce the candidate checks

The three new configurations set `enable_nanoda: true` explicitly. The
historical Theorem 1.1 configuration retains its recorded false value; Palomar
does not trust this author-controlled switch and the replay script writes a
protected copy with NanoDa enabled before running every configuration.

`palomar/verify-comparator.sh` uses the trusted-tool revisions pinned by
`PalomarRegistry/PalomarSubmission` at commit
`0a2c287a924d2a7cb22e2b12f12b27321bb485a3` (2026-08-20). Pass the desired
configuration explicitly, for example:

```bash
PALOMAR_COMPARATOR_CACHE=/path/to/disposable/cache \
  ./palomar/verify-comparator.sh comparator/theorem_one_two.json
```

The candidates use Lean `v4.32.0`, Mathlib `v4.32.0` at commit
`81a5d257c8e410db227a6665ed08f64fea08e997`, lean4export commit
`4e7915201d3f9f04470d9eae002fa695f7cdc589`, Comparator commit
`575674928e239f5bc452aab72d1dd7b0f1326494`, and NanoDa commit
`68d5ca9db226849b41a6fff59d796ff19d0a8840`.

`palomar/check-mathlib-canonical-ancestry.sh` mirrors Palomar's canonical
Mathlib ancestry guard. The workflow
`.github/workflows/palomar-qualification.yml` validates every metadata/config
pair and runs each protected Lean+NanoDa replay in a separate matrix job. A
green workflow is a pre-submission compatibility result; Palomar's verification
of the submitted immutable commit remains authoritative.
