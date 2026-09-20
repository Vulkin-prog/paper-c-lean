# Local qualification of the current Paper C selection

On 20 September 2026, all **89 selected declarations in seven configurations**
passed exact Comparator comparison, the **Lean 4.34.0 kernel** and **NanoDa**.
The source commit is:

`bfaa6fd2f117f731d6f7ceea8fbb9c59de544598`

This record applies to that commit and its recorded file hashes. A later
packaging/documentation commit does not change the commit identified here.
It is not a Palomar registration, renderability check or editorial decision.

## Evidence

- [validation.json](validation.json): unmodified local runner receipt; all 1,427
  tracked Lean sources, project pins, configurations and metadata are hashed.
  It records the seven selected-name lists, tool binary hashes, exit codes,
  successful dual-kernel results, elapsed times and available disk space.
- [preflight.json](preflight.json): compact official-contract and canonical-import
  receipt. The full local receipt enumerates 8,908 canonical dependency sources;
  this public version keeps the count and a hash of that list, plus the full
  local receipt's SHA-256. Challenges satisfy both the line and byte limits.
- [transcript-excerpts.txt](transcript-excerpts.txt): labelled excerpts containing
  the two acceptance messages for every configuration. These are not full logs.

The full transcripts named and hashed in `validation.json` were retained in the
local workspace; they are not copied into the public repository. The public
receipt contains repository-relative paths and tool identities, not host paths.
The source/configuration/metadata hashes were checked before and after each
replay. The full static preflight was repeated on the qualified files.

## Tool identities and execution

| Component | Revision |
|---|---|
| Lean | `v4.34.0` |
| Mathlib | `5ed2965256430c3649e86755f9576b54eca72435` |
| Comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| lean4export | `076e8e57707e813375e8f9da8bf989799ace9680` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |
| Palomar submission contract | `3561d237dcc4b28482558ad28a64d767d7cc8615` |

Local execution reused these installed tools, invoked Comparator with its real
landrun adapter under `systemd-run --user --pipe`, disabled AF_UNIX inside that
unit, and imposed a 70 GiB memory limit, no swap and a 20-minute limit per entry.
The local disk guard stopped work below a 5 GiB reserve. The protected
configurations retain `enable_nanoda: true` and the exact selected names.
This local transport is not a claim to reproduce Palomar's entire server pipeline.

For an independent replay, use the checked-in
[runner](../../verify-comparator.sh) once per configuration, as described in the
[submission guide](../../../../docs/PALOMAR_SUBMISSIONS.md). It installs the
pinned tools, performs the full static preflight, invokes Comparator and checks
that the source tree remains unchanged. GitHub runs these seven jobs on the PR
and on `main` after merging; submit the actual successfully qualified merge SHA.

The seven explicit literature inputs remain ordinary theorem premises. In
particular, this verification does not establish the analytic Stein solution
premise of F.2. No new mathematical hypothesis was introduced for the interfaces.
