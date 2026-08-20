#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
manifest_path=${1:-"$repository_root/lake-manifest.json"}
canonical_repository=https://github.com/leanprover-community/mathlib4.git
official_ref=refs/heads/master
fetched_ref=refs/remotes/palomar-official/head

mathlib_revision=$(
  python3 - "$manifest_path" "$canonical_repository" <<'PY'
import json
import pathlib
import re
import sys

manifest_path = pathlib.Path(sys.argv[1])
canonical_repository = sys.argv[2]
manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
packages = manifest.get("packages")
if not isinstance(packages, list):
    raise SystemExit(f"error: {manifest_path}: packages must be a list")

matches = [package for package in packages if package.get("name") == "mathlib"]
if len(matches) != 1:
    raise SystemExit(
        f"error: {manifest_path}: expected exactly one mathlib package, found {len(matches)}"
    )

package = matches[0]
if package.get("type") != "git":
    raise SystemExit(f"error: {manifest_path}: mathlib must be a git package")
if package.get("url") != canonical_repository:
    raise SystemExit(
        f"error: {manifest_path}: mathlib URL must be {canonical_repository}"
    )

revision = package.get("rev")
if not isinstance(revision, str) or re.fullmatch(r"[0-9a-f]{40}", revision) is None:
    raise SystemExit(f"error: {manifest_path}: mathlib rev must be a full lowercase Git SHA")
print(revision)
PY
)

checkout_root=$(mktemp -d "${TMPDIR:-/tmp}/paper-c-mathlib-ancestry.XXXXXX")
trap 'rm -rf -- "$checkout_root"' EXIT
package_dir="$checkout_root/mathlib4"

secure_git() {
  env \
    GIT_CONFIG_GLOBAL=/dev/null \
    GIT_CONFIG_NOSYSTEM=1 \
    GIT_TERMINAL_PROMPT=0 \
    GIT_LFS_SKIP_SMUDGE=1 \
    git \
      -c core.hooksPath=/dev/null \
      -c protocol.file.allow=never \
      -C "$package_dir" \
      "$@"
}

git init --quiet "$package_dir"
secure_git remote add palomar-official "$canonical_repository"
secure_git fetch --quiet --filter=tree:0 --no-tags \
  palomar-official "$mathlib_revision"
secure_git fetch --quiet --filter=tree:0 --no-tags \
  palomar-official "+$official_ref:$fetched_ref"

ancestry_status=0
secure_git merge-base --is-ancestor "$mathlib_revision" "$fetched_ref" || \
  ancestry_status=$?
if [ "$ancestry_status" -eq 1 ]; then
  echo "error: leanprover-community/mathlib4 revision $mathlib_revision is not an ancestor of canonical $official_ref" >&2
  exit 1
fi
if [ "$ancestry_status" -ne 0 ]; then
  echo "error: could not establish official ancestry for leanprover-community/mathlib4" >&2
  exit "$ancestry_status"
fi

canonical_head=$(secure_git rev-parse "$fetched_ref")
echo "PALOMAR_MATHLIB_CANONICAL_ANCESTRY_OK revision=$mathlib_revision canonical_ref=$official_ref canonical_head=$canonical_head"
