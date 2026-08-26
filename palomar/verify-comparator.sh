#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
configuration=${1:-comparator/theorem_one_one.json}
case "$configuration" in
  comparator/theorem_one_one.json | \
  comparator/theorem_one_one_transfer.json | \
  comparator/theorem_one_two.json | \
  comparator/theorem_one_four_and_corollary_eleven_three.json | \
  comparator/theorem_sixteen_two_and_corollary_sixteen_four.json)
    ;;
  *)
    echo "error: unsupported Palomar Comparator configuration: $configuration" >&2
    exit 2
    ;;
esac
source_config="$repository_root/$configuration"
if [ ! -f "$source_config" ]; then
  echo "error: Comparator configuration not found: $configuration" >&2
  exit 1
fi
cache_root=${PALOMAR_COMPARATOR_CACHE:-"$repository_root/.cache/palomar-qualification"}
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"
submission_dir="$cache_root/palomar-submission"
config_slug=$(basename "$configuration" .json)
protected_config="$cache_root/protected-$config_slug.json"

# PalomarSubmission commit 0a2c287a924d2a7cb22e2b12f12b27321bb485a3,
# workflow submission.yml, read on 2026-08-20.
comparator_commit=575674928e239f5bc452aab72d1dd7b0f1326494
lean4export_commit=4e7915201d3f9f04470d9eae002fa695f7cdc589
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840
submission_commit=0a2c287a924d2a7cb22e2b12f12b27321bb485a3

for required_command in cargo git go lake python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required for the Palomar replay" >&2
    exit 1
  fi
done

"$repository_root/palomar/check-mathlib-canonical-ancestry.sh"

python3 - "$source_config" "$protected_config" <<'PY'
import json
import pathlib
import sys

source = pathlib.Path(sys.argv[1])
destination = pathlib.Path(sys.argv[2])
config = json.loads(source.read_text(encoding="utf-8"))
if not isinstance(config, dict):
    raise SystemExit(f"error: {source}: expected one JSON object")
config["enable_nanoda"] = True
destination.parent.mkdir(parents=True, exist_ok=True)
destination.write_text(
    json.dumps(config, indent=2, ensure_ascii=False) + "\n",
    encoding="utf-8",
)
protected = json.loads(destination.read_text(encoding="utf-8"))
if protected.get("enable_nanoda") is not True:
    raise SystemExit("error: protected Comparator configuration did not enable NanoDa")
PY

mkdir -p "$cache_root" "$bin_dir"

checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none "$repository" "$destination"
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

checkout_exact https://github.com/leanprover/lean4export.git \
  "$lean4export_dir" "$lean4export_commit"

project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
lean4export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$lean4export_toolchain" ]; then
  echo "error: project and lean4export toolchains differ" >&2
  echo "project: $project_toolchain" >&2
  echo "lean4export: $lean4export_toolchain" >&2
  exit 1
fi

checkout_exact https://github.com/leanprover/comparator.git \
  "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git \
  "$nanoda_dir" "$nanoda_commit"
checkout_exact https://github.com/PalomarRegistry/PalomarSubmission.git \
  "$submission_dir" "$submission_commit"

CGO_ENABLED=0 GOBIN="$bin_dir" go install \
  "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"

(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)

cd "$repository_root"
lake exe cache get
PALOMAR_LANDRUN_REAL="$bin_dir/landrun" \
COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
COMPARATOR_LANDRUN="$submission_dir/scripts/landrun_passthrough.py" \
  lake env "$comparator_dir/.lake/build/bin/comparator" \
    "$protected_config"
