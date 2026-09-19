#!/usr/bin/env python3
"""Match an exact release tag from the separately queried canonical remote.

The caller must query leanprover-community/mathlib4, never the submitted remote.
Annotated tags are matched by their peeled commit, not by their tag object.
"""

import re
import sys

RELEASE = re.compile(r"refs/tags/(v[0-9]+\.[0-9]+\.[0-9]+(?:-rc[0-9]+)?)(\^\{\})?")
SHA = re.compile(r"[0-9a-f]{40}")


def matching_tags(listing: str, revision: str) -> list[str]:
    if not SHA.fullmatch(revision):
        raise ValueError("revision must be a full lowercase commit SHA")
    tags: dict[str, dict[bool, str]] = {}
    for line in listing.splitlines():
        fields = line.split()
        if len(fields) != 2 or not SHA.fullmatch(fields[0]):
            continue
        match = RELEASE.fullmatch(fields[1])
        if match:
            variants = tags.setdefault(match[1], {})
            peeled = bool(match[2])
            if peeled in variants and variants[peeled] != fields[0]:
                raise ValueError("conflicting canonical tag listing")
            variants[peeled] = fields[0]
    return sorted(name for name, variants in tags.items()
                  if variants.get(True, variants.get(False)) == revision)


if __name__ == "__main__":
    for tag in matching_tags(sys.stdin.read(), sys.argv[1]):
        print(tag)
