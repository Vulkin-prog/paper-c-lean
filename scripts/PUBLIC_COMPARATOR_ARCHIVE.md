# Public hardened Comparator archive

`derive_public_comparator_archive.py` creates the publishable derivative of a
successful raw `run_hardened_comparator.sh` output. The transformation is
omission-only: retained raw files are never rewritten. The independent
`verify_public_comparator_archive.py` reparses the raw and public archives and
does not import the derivation implementation.

## Prerequisites

- Python 3.10 or newer, using only the standard library;
- the `zstd` command-line interface (the creator records its exact version);
- Git, to bind the source snapshot, PDFs, and privacy tools to source commit
  `Q`;
- `sha256sum` only for the small `VERIFY.sh` shipped inside the public bundle.

The process needs no network access and no elevated privileges. Run it from a
clean checkout at the exact source commit `Q`. Keep the raw evidence directory,
its `.tar.zst` archive, both detached checksum files, and the new public output
directory outside the repository.

Independent verification may be repeated on another machine, but canonical
compressed-byte reproduction requires the exact `zstd --version` recorded in
the redaction manifest. A different local version fails closed; use the same
supported host/tool package as the creator.

The hardened runner now includes the creator, independent verifier, and their
self-test beneath `source-snapshot/scripts/`. Those three files are retained
byte-for-byte in the public bundle. `REDACTION_MANIFEST.json` also records their
SHA-256 values at `Q`; the later release binding carries the same `Q` and the
public archive SHA-256.

## Create and verify

If `RAW_DIR` is the evidence directory produced by the runner, the matching
archive must be `RAW_DIR.tar.zst` and its sidecar must be
`RAW_DIR.tar.zst.sha256`:

```sh
Q=$(git rev-parse HEAD)
RAW_DIR=/absolute/path/to/paper-c-hardened-evidence-Q
PUBLIC_PARENT=/absolute/path/to/new-public-output

test -z "$(git status --porcelain=v1 --untracked-files=all)"

python3 scripts/derive_public_comparator_archive.py \
  --source "$RAW_DIR" \
  --output-dir "$PUBLIC_PARENT"

PUBLIC_ARCHIVE="$PUBLIC_PARENT/paper-c-hardened-public-$Q.tar.zst"

python3 scripts/verify_public_comparator_archive.py \
  --source "$RAW_DIR" \
  --archive "$PUBLIC_ARCHIVE" \
  --repository "$PWD"
```

The raw archive can instead be supplied directly:

```sh
python3 scripts/derive_public_comparator_archive.py \
  --source /absolute/path/to/raw-evidence.tar.zst \
  --output-dir /absolute/path/to/new-public-output
```

When a raw directory and archive are not adjacent, pass the archive explicitly
to both commands with `--source-archive /absolute/path/to/raw.tar.zst`.

The output directory must not already exist. On success it contains exactly:

```text
paper-c-hardened-public-<full-Q>.tar.zst
paper-c-hardened-public-<full-Q>.tar.zst.sha256
paper-c-hardened-public-<full-Q>.tar.zst.verified.json
```

The creator writes `.partial` files and exposes the final names only after its
independent verifier passes.

The `.verified.json` file is an informational, publishable verification
report—not a signature or a self-sufficient proof. Binding creation reruns the
independent verifier against the locally retained private raw source. Publish
the archive, detached checksum, and report together.

## Fail-closed policy

The raw source must have exactly 33 classified files: 20 retained
byte-identically and the same 13 host-specific logs/transcripts omitted by the
v0.48.0 policy. Any extra, missing, duplicate, linked, sparse, unsafe, or
unclassified member is fatal. The redaction manifest represents every raw
path exactly once with its size, SHA-256, disposition, and omission reason.

The verifier additionally enforces:

- exact raw and public checksum inventories and detached sidecars;
- coherent `SUCCESS`, summary, two result records, configurations, source
  snapshot, Comparator fileset digest, tool commits, PDF hashes, and private
  transcript hashes;
- source snapshot equality with `git show Q:<path>`;
- one canonical level-19, single-worker zstd frame with no skippable frame;
- canonical POSIX ustar metadata, path order, modes, owner/group, timestamp,
  padding, and path sets;
- byte identity of every retained raw member, including the result JSON files;
- absence of concrete host-private paths and identity records in every public
  member.

The public archive intentionally excludes raw host logs. It supports artifact
identity and result provenance, not public line-by-line host forensics, a
dual-kernel claim, or a general host-security certification.

The two packaging inputs remain usable without conversion:

```text
evidence/theorem-one-one/result-theorem-one-one.json
evidence/infinite-finite-transfer/result-infinite-finite-transfer.json
```

Copy those exact bytes into `release_evidence/v0.48.1/`, then create and verify
the `Q -> R` release binding using the public archive and its SHA-256.

## Self-test

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/test_public_comparator_archive.py
```

The test builds synthetic raw evidence, proves deterministic repeat output,
and checks rejection of extra paths, symlinks, traversal, stale checksums,
changed retained bytes, and a concrete private-path leak.
