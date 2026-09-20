# Lean 4.34.0 validation evidence

The [validation receipt](validation.json) binds the local build, exact axiom
audits, all 80 strict interfaces and ten successful Comparator/NanoDa replays
to the [Lean source hashes](lean-sources.json). The source hash manifest is
independent of the later packaging commit, avoiding a self-referential receipt.

The replays use the pinned official tools, real Landrun and the systemd
`RestrictAddressFamilies=~AF_UNIX` restriction. They reuse prebuilt project
outputs and do not claim the full protected Palomar server pipeline.
The [printing receipt](core-notation-render.json) covers all 69 V3 Challenge
signatures using the corrected official core-notation audit only.

The complete 8,908-module import and metadata receipt is compressed as
`v3-preflight.json.gz`, with both hashes in `validation.json`.

Compressed transcripts in `logs/` preserve exact bytes. Each gzip hash and its
uncompressed SHA-256 are recorded in `validation.json`. For example:

```sh
gzip -dc logs/lean4340-core-audit.log.gz > core-audit.log
node ../../scripts/verify_audit.mjs --input core-audit.log
```

The example paths above are relative to this evidence directory. The complete
commands, pins and semantic review are in the
[migration guide](../../docs/LEAN_4_34_0_MIGRATION.md).

The seven literature premises remain explicit. Nothing in this directory
registers a Palomar entry or updates an old submission. Historical 4.32 and
4.33.1 receipts and manuscript bytes are preserved separately.
