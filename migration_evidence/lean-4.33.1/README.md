# Local Lean 4.33.1 migration evidence

The [validation receipt](validation.json) binds the successful 23-library
build, the three exact axiom audits and the local comparison of 80 selected
interfaces to their source and transcript hashes. The
[source snapshot](lean-sources.json) records all 1,171 checked Lean files;
the [interface receipt](strict-boundary.json) records the ten configurations.
The source hashes, rather than the later packaging commit, identify the
inputs that were checked. Full local transcripts remain with the maintainer.

The interface diagnostic compares existing compiled Lean environments and
their reachable constants. It does not run the official Comparator export
parser and proof kernel or NanoDa. These files are migration evidence, not
new Palomar qualification receipts. Historical 4.32.0 registrations retain
their own source and toolchain bindings.

See the [migration guide](../../docs/LEAN_4_33_1_MIGRATION.md) for exact
versions, proof adaptations, reproducible build/audit commands and the
remaining upstream admission and rendering issues. The seven explicit
literature premises remain assumptions in the relevant theorem signatures.
