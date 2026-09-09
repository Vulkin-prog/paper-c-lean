#!/usr/bin/env python3
"""Check the pinned exporter source and its effective Lean compiler separately.

PalomarSubmission PR 122 permits a stable patch release to rebuild the same
release line's patch-zero exporter. This repository pins that one exact pair;
it does not accept arbitrary compatible-looking exporter or compiler versions.
The caller must also verify the exporter's exact Git commit before this check.
"""

import json
import re
import sys

PROJECT_TOOLCHAIN = "leanprover/lean4:v4.33.1"
EXPORTER_SOURCE_TOOLCHAIN = "leanprover/lean4:v4.33.0"
LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"


def validate(project: str, source: str, compiler_version: str) -> dict[str, str]:
    if project.strip() != PROJECT_TOOLCHAIN:
        raise ValueError(f"project toolchain must be exactly {PROJECT_TOOLCHAIN}")
    if source.strip() != EXPORTER_SOURCE_TOOLCHAIN:
        raise ValueError(
            f"pinned exporter source toolchain must be exactly {EXPORTER_SOURCE_TOOLCHAIN}"
        )
    match = re.fullmatch(
        r"Lean \(version (?P<version>[^,\s]+),[^\r\n]*, "
        r"commit (?P<commit>[0-9a-f]{40}), Release\)",
        compiler_version.strip(),
    )
    if match is None:
        raise ValueError("could not identify the effective Lean release and full commit")
    if match["version"] != "4.33.1" or match["commit"] != LEAN_COMMIT:
        raise ValueError("exporter must be built with the exact pinned Lean 4.33.1 compiler")
    return {
        "lean4export_source_toolchain": source.strip(),
        "lean4export_build_toolchain": project.strip(),
        "lean4export_compiler_commit": match["commit"],
        "lean4export_compiler_version": compiler_version.strip(),
    }


def main() -> int:
    if len(sys.argv) != 4:
        print("usage: check_exporter_toolchain.py PROJECT SOURCE LEAN_VERSION", file=sys.stderr)
        return 2
    try:
        evidence = validate(*sys.argv[1:])
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print(json.dumps(evidence, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
