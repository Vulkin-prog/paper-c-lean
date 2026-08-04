#!/bin/bash

set -Eeuo pipefail
set +x
umask 077

# Exported Bash functions can shadow external programs even after PATH is
# replaced. No function should exist before this script defines its own.
INITIAL_FUNCTIONS=$(builtin declare -Fx)
if [[ -n "$INITIAL_FUNCTIONS" ]]; then
  printf '[paper-c-hardened] ERROR: inherited Bash functions are not accepted\n' >&2
  exit 1
fi
unset INITIAL_FUNCTIONS

PROGRAM=${0##*/}
OUTPUT_ARGUMENT=
PREFLIGHT_ONLY=false
KEEP_WORKDIR=false
TIMEOUT_MINUTES=90

SOURCE_ROOT=
OUTPUT_DIR=
OUTPUT_OWNED=false
WORK_ROOT=
SETUP_LOG=
CURRENT_UNIT=
RUN_SUCCEEDED=false
SYSTEMD_PREFLIGHT_LOG=

usage() {
  cat <<'EOF'
Usage: scripts/run_hardened_comparator.sh [options]

Build the pinned Comparator, lean4export, and real landrun tools, then run both
Paper C Comparator configurations in separate fresh checkouts through the
official systemd-run security wrapper.  There is no unsandboxed fallback.

Options:
  --output-dir DIR       New directory for evidence (default: sibling of repo)
  --timeout-minutes N    Per-target systemd RuntimeMaxSec (default: 90; 0 disables)
  --keep-workdir         Preserve temporary tool/project checkouts after success
  --preflight-only       Check the host, terminal, user bus, and source tree only
  -h, --help             Show this help

Run this script from an interactive Ubuntu 24.04 or 26.04 terminal as an
ordinary user, through the clean PATH and setpriv invocation documented in
README.md. Do not use sudo, nohup, a pipe, an IDE task runner, or a container.
EOF
}

note() {
  printf '[paper-c-hardened] %s\n' "$*"
}

die() {
  printf '[paper-c-hardened] ERROR: %s\n' "$*" >&2
  exit 1
}

require_command() {
  local name=$1
  command -v "$name" >/dev/null 2>&1 || die "required command not found: $name"
}

transcript_has_exact_line() {
  local transcript=$1
  local marker=$2

  # Match an exact raw record, allowing only one optional terminal CR.
  # Do not put an early-exit grep -q after a producer under pipefail: on a
  # long transcript, the producer can receive SIGPIPE after a valid match.
  /usr/bin/grep -aFx -e "$marker" -e "$marker"$'\r' -- "$transcript" \
    >/dev/null
}

quote_command() {
  local quoted= argument
  for argument in "$@"; do
    printf -v argument '%q' "$argument"
    if [[ -n "$quoted" ]]; then
      quoted+=" "
    fi
    quoted+="$argument"
  done
  printf '%s' "$quoted"
}

cleanup_unit() {
  local unit=${1:-}
  [[ -n "$unit" ]] || return 0
  "$SYSTEMCTL_BIN" --user stop "$unit.service" >/dev/null 2>&1 || true
  "$SYSTEMCTL_BIN" --user kill --kill-who=all --signal=KILL "$unit.service" \
    >/dev/null 2>&1 || true
  local state attempt
  for attempt in {1..20}; do
    state=$("$SYSTEMCTL_BIN" --user show --property=ActiveState --value \
      "$unit.service" 2>/dev/null || true)
    case "$state" in
      ''|inactive|failed) break ;;
    esac
    sleep 0.25
  done
  case "$state" in
    ''|inactive|failed) ;;
    *) return 1 ;;
  esac
  "$SYSTEMCTL_BIN" --user reset-failed "$unit.service" >/dev/null 2>&1 || true
}

on_exit() {
  local status=$?
  trap - EXIT INT TERM
  set +e

  if [[ -n "$SYSTEMD_PREFLIGHT_LOG" && -f "$SYSTEMD_PREFLIGHT_LOG" ]]; then
    rm -f -- "$SYSTEMD_PREFLIGHT_LOG"
  fi

  if [[ -n "$CURRENT_UNIT" ]]; then
    note "stopping transient unit $CURRENT_UNIT.service"
    cleanup_unit "$CURRENT_UNIT" || \
      note "WARNING: transient unit may still be active: $CURRENT_UNIT.service"
  fi

  if [[ -n "$WORK_ROOT" && -d "$WORK_ROOT" ]]; then
    if [[ "$KEEP_WORKDIR" == true || $status -ne 0 ]]; then
      note "temporary work directory preserved: $WORK_ROOT"
    else
      local tmp_parent
      tmp_parent=$(realpath "${TMPDIR:-/tmp}")
      case "$WORK_ROOT" in
        "$tmp_parent"/paper-c-hardened.*)
          rm -rf -- "$WORK_ROOT"
          ;;
        *)
          note "refusing to remove unexpected temporary path: $WORK_ROOT"
          ;;
      esac
    fi
  fi

  if [[ $status -ne 0 && "$OUTPUT_OWNED" == true ]]; then
    if [[ "$RUN_SUCCEEDED" != true ]]; then
      rm -f -- \
        "$OUTPUT_DIR/SUCCESS" \
        "$OUTPUT_DIR.tar.zst" \
        "$OUTPUT_DIR.tar.zst.partial" \
        "$OUTPUT_DIR.tar.zst.sha256" \
        "$OUTPUT_DIR.tar.zst.sha256.partial"
    fi
    note "no SUCCESS marker was created; preserved diagnostics: $OUTPUT_DIR"
  fi
  exit "$status"
}

trap on_exit EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

while [[ $# -gt 0 ]]; do
  case "$1" in
    --output-dir)
      [[ $# -ge 2 ]] || die '--output-dir requires a value'
      OUTPUT_ARGUMENT=$2
      shift 2
      ;;
    --timeout-minutes)
      [[ $# -ge 2 ]] || die '--timeout-minutes requires a value'
      TIMEOUT_MINUTES=$2
      shift 2
      ;;
    --keep-workdir)
      KEEP_WORKDIR=true
      shift
      ;;
    --preflight-only)
      PREFLIGHT_ONLY=true
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      die "unknown option: $1"
      ;;
  esac
done

[[ "$TIMEOUT_MINUTES" =~ ^[0-9]+$ ]] || die '--timeout-minutes must be an integer'
TIMEOUT_MINUTES=$((10#$TIMEOUT_MINUTES))
(( TIMEOUT_MINUTES <= 1440 )) || die '--timeout-minutes must be at most 1440'

# Resolve every ordinary command from the stock system directories before the
# user-owned Elan proxy directory. The exact Elan paths are verified below.
export PATH="/usr/bin:/bin:$HOME/.elan/bin"

for command_name in \
  bash cat cp curl date df dirname elan env find git grep id install lake mkdir \
  mktemp mv node realpath rm sed setpriv sha256sum sleep sort stat systemctl \
  systemd-detect-virt systemd-run tar tee touch tr truncate uname xargs zstd; do
  require_command "$command_name"
done
require_command script

[[ "$(/usr/bin/uname -s)" == Linux ]] || die 'the hardened runner requires Linux'
[[ "$(/usr/bin/id -u)" -ne 0 ]] || die 'must not be run as root or through sudo'
[[ -t 0 && -t 1 && -t 2 ]] || \
  die 'stdin, stdout, and stderr must all be attached to an interactive terminal'
set +e
CONTAINER_KIND=$(/usr/bin/systemd-detect-virt --container 2>&1)
CONTAINER_STATUS=$?
set -e
if [[ $CONTAINER_STATUS -eq 0 ]]; then
  die 'containers are not accepted for hardened publication evidence'
fi
[[ $CONTAINER_STATUS -eq 1 && "$CONTAINER_KIND" == none ]] || \
  die 'could not establish that the hardened runner is outside a container'

OS_ID=$(/usr/bin/sed -n 's/^ID=//p' /etc/os-release | /usr/bin/tr -d '"')
OS_VERSION_ID=$(/usr/bin/sed -n 's/^VERSION_ID=//p' /etc/os-release | \
  /usr/bin/tr -d '"')
[[ "$OS_ID" == ubuntu ]] || die "supported reference operating system is Ubuntu, not $OS_ID"
case "$OS_VERSION_ID" in
  24.04|26.04) ;;
  *) die "supported Ubuntu releases are 24.04 and 26.04, not $OS_VERSION_ID" ;;
esac

mapfile -t CAPABILITY_LINES < <(grep -E '^Cap(Inh|Prm|Eff|Amb):' /proc/self/status)
[[ ${#CAPABILITY_LINES[@]} -eq 4 ]] || \
  die 'could not read all four Linux process capability fields'
capability_failure=false
declare -A CAPABILITY_NAMES
for capability_line in "${CAPABILITY_LINES[@]}"; do
  read -r capability_name capability_value <<<"$capability_line"
  [[ "$capability_name" =~ ^Cap(Inh|Prm|Eff|Amb):$ && \
     "$capability_value" =~ ^[0-9A-Fa-f]+$ ]] || \
    die "malformed Linux capability field: $capability_line"
  [[ -z "${CAPABILITY_NAMES[$capability_name]-}" ]] || \
    die "duplicate Linux capability field: $capability_name"
  CAPABILITY_NAMES[$capability_name]=true
  if [[ "${capability_value//0/}" != '' ]]; then
    printf '[paper-c-hardened] active Linux capability: %s %s\n' \
      "$capability_name" "$capability_value" >&2
    capability_failure=true
  fi
done
[[ "$capability_failure" == false ]] || \
  die 'effective, permitted, inheritable, and ambient capabilities must be zero'

NO_NEW_PRIVS=$(/usr/bin/sed -n 's/^NoNewPrivs:[[:space:]]*//p' /proc/self/status)
[[ "$NO_NEW_PRIVS" == 1 ]] || \
  die 'NoNewPrivs must be set; use the documented /usr/bin/setpriv invocation'

for variable_name in \
  BASH_ENV BASH_XTRACEFD COMPARATOR_BIN COMPARATOR_CONFIG COMPARATOR_LANDRUN \
  COMPARATOR_LEAN4EXPORT COMPARATOR_NANODA ELAN_DIST_SERVER ELAN_TOOLCHAIN \
  ELAN_UPDATE_ROOT ENV GIT_ALTERNATE_OBJECT_DIRECTORIES GIT_ATTR_NOSYSTEM \
  GIT_CEILING_DIRECTORIES GIT_COMMON_DIR GIT_CONFIG GIT_CONFIG_COUNT \
  GIT_CONFIG_GLOBAL GIT_CONFIG_PARAMETERS GIT_CONFIG_SYSTEM GIT_DIR \
  GIT_DISCOVERY_ACROSS_FILESYSTEM GIT_EXEC_PATH GIT_INDEX_FILE \
  GIT_OBJECT_DIRECTORY GIT_SSH GIT_SSH_COMMAND GIT_SSH_VARIANT \
  GIT_TEMPLATE_DIR GIT_WORK_TREE \
  GOWORK ELAN_HOME GZIP LAKE_HOME LD_AUDIT LD_LIBRARY_PATH LD_PRELOAD LEAN_PATH \
  LEAN_SRC_PATH LEAN_SYSROOT LEAN_OPTS MATHLIB_CACHE_URL NODE_OPTIONS \
  SYSTEMD_ADJUST_TERMINAL_TITLE TAR_OPTIONS ZSTD_CLEVEL ZSTD_NBTHREADS; do
  if [[ -n "${!variable_name-}" ]]; then
    die "environment variable must be unset: $variable_name"
  fi
done

SYSTEMD_VERSION=$(/usr/bin/systemd-run --version | \
  sed -n '1s/^systemd \([0-9][0-9]*\).*/\1/p')
[[ "$SYSTEMD_VERSION" =~ ^[0-9]+$ ]] || die 'could not determine systemd version'
(( SYSTEMD_VERSION >= 240 )) || die 'systemd 240 or newer is required'

KERNEL_RELEASE=$(/usr/bin/uname -r)
KERNEL_MAJOR=${KERNEL_RELEASE%%.*}
kernel_remainder=${KERNEL_RELEASE#*.}
KERNEL_MINOR=${kernel_remainder%%[^0-9]*}
[[ "$KERNEL_MAJOR" =~ ^[0-9]+$ && "$KERNEL_MINOR" =~ ^[0-9]+$ ]] || \
  die "could not parse kernel release: $KERNEL_RELEASE"
if (( KERNEL_MAJOR < 6 || (KERNEL_MAJOR == 6 && KERNEL_MINOR < 2) )); then
  die 'Linux 6.2 or newer is required for Landlock truncate protection'
fi

NODE_MAJOR=$(node -p 'Number(process.versions.node.split(".")[0])')
[[ "$NODE_MAJOR" =~ ^[0-9]+$ ]] || die 'could not determine Node.js version'
(( NODE_MAJOR >= 18 )) || die 'Node.js 18 or newer is required by the evidence validators'

SCRIPT_PATH=$(realpath "${BASH_SOURCE[0]}")
SOURCE_ROOT=$(/usr/bin/git -C "$(dirname "$SCRIPT_PATH")/.." rev-parse --show-toplevel)
SOURCE_ROOT=$(realpath "$SOURCE_ROOT")
[[ "$SCRIPT_PATH" == "$SOURCE_ROOT"/scripts/run_hardened_comparator.sh ]] || \
  die 'script must be executed from its committed Paper C repository location'

PAPER_COMMIT=$(/usr/bin/git -C "$SOURCE_ROOT" rev-parse --verify HEAD^{commit})
[[ "$PAPER_COMMIT" =~ ^[0-9a-f]{40}$ ]] || die 'Paper C HEAD is not a full commit SHA'
SOURCE_STATUS=$(/usr/bin/git -C "$SOURCE_ROOT" status --porcelain --untracked-files=all)
if [[ -n "$SOURCE_STATUS" ]]; then
  printf '%s\n' "$SOURCE_STATUS" >&2
  die 'source repository must be completely clean, including untracked files'
fi
SCRIPT_GIT_BLOB=$(/usr/bin/git -C "$SOURCE_ROOT" rev-parse \
  'HEAD:scripts/run_hardened_comparator.sh')
[[ "$(/usr/bin/git -C "$SOURCE_ROOT" hash-object "$SCRIPT_PATH")" == \
    "$SCRIPT_GIT_BLOB" ]] || \
  die 'the executing runner does not match the script committed at HEAD'

AUDIT_CONFIG="$SOURCE_ROOT/audit_config.json"
[[ -f "$AUDIT_CONFIG" ]] || die 'audit_config.json is missing'
mapfile -t PINS < <(node - "$AUDIT_CONFIG" <<'NODE'
const fs = require('node:fs');
const config = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const verification = config.verification;
const tools = verification.comparator.tools;
const values = [
  verification.toolchain.lean.toolchain,
  verification.toolchain.lean.commit,
  verification.toolchain.mathlib.commit,
  tools.comparator.repository,
  tools.comparator.commit,
  tools.lean4export.repository,
  tools.lean4export.commit,
  tools.landrun.repository,
  tools.landrun.commit,
];
for (const value of values) {
  if (typeof value !== 'string' || value.length === 0 || value.includes('\n')) {
    throw new Error('invalid hardened-run pin in audit_config.json');
  }
  process.stdout.write(`${value}\n`);
}
NODE
)
[[ ${#PINS[@]} -eq 9 ]] || die 'could not load all hardened-run pins'

PROJECT_TOOLCHAIN=${PINS[0]}
LEAN_COMMIT=${PINS[1]}
MATHLIB_COMMIT=${PINS[2]}
COMPARATOR_REPOSITORY=${PINS[3]}
COMPARATOR_COMMIT=${PINS[4]}
LEAN4EXPORT_REPOSITORY=${PINS[5]}
LEAN4EXPORT_COMMIT=${PINS[6]}
LANDRUN_REPOSITORY=${PINS[7]}
LANDRUN_COMMIT=${PINS[8]}

for commit_value in \
  "$LEAN_COMMIT" "$MATHLIB_COMMIT" "$COMPARATOR_COMMIT" \
  "$LEAN4EXPORT_COMMIT" "$LANDRUN_COMMIT"; do
  [[ "$commit_value" =~ ^[0-9a-f]{40}$ ]] || die "invalid pinned commit: $commit_value"
done

mapfile -t CONFIG_PATHS < <(node - "$AUDIT_CONFIG" <<'NODE'
const fs = require('node:fs');
const config = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
for (const item of config.verification.comparator.configurations) {
  process.stdout.write(`${item.path}\n`);
}
NODE
)
EXPECTED_CONFIGS=(
  comparator/theorem_one_one.json
  comparator/theorem_one_one_transfer.json
)
[[ "${CONFIG_PATHS[*]}" == "${EXPECTED_CONFIGS[*]}" ]] || \
  die 'audit_config.json does not contain the two expected Comparator configurations in order'

# Keep lexical /usr/bin paths for Ubuntu system programs. Ubuntu 26.04's
# provider packages intentionally make several of those paths symlinks to
# /usr/lib/cargo/bin/coreutils/* or /usr/bin/gnu*. The verifier below checks
# both the fixed invocation path and its resolved, root-owned target.
ELAN_COMMAND=$(command -v elan)
LAKE_COMMAND=$(command -v lake)
EXPECTED_ELAN_HOME=$(realpath -m -- "$HOME/.elan")
[[ "$ELAN_COMMAND" == "$EXPECTED_ELAN_HOME/bin/elan" && \
   "$LAKE_COMMAND" == "$EXPECTED_ELAN_HOME/bin/lake" ]] || \
  die 'use the official per-user Elan proxies in $HOME/.elan/bin'
ELAN_BIN=$(realpath "$ELAN_COMMAND")
ELAN_BIN_DIR=$EXPECTED_ELAN_HOME/bin
LAKE_BIN=$(realpath "$LAKE_COMMAND")
GIT_BIN=$(command -v git)
NODE_BIN=$(command -v node)
SCRIPT_BIN=$(command -v script)
SETPRIV_BIN=$(command -v setpriv)
SYSTEMD_RUN_BIN=$(command -v systemd-run)
SYSTEMCTL_BIN=$(command -v systemctl)
SHA256SUM_BIN=$(command -v sha256sum)
TRUNCATE_BIN=$(command -v truncate)
TOUCH_BIN=$(command -v touch)
RM_BIN=$(command -v rm)
MV_BIN=$(command -v mv)

[[ "$ELAN_BIN" == "$EXPECTED_ELAN_HOME/bin/elan" && \
   -f "$ELAN_BIN" && -x "$ELAN_BIN" && \
   -f "$LAKE_BIN" && -x "$LAKE_BIN" ]] || \
  die 'use the official per-user Elan installation in $HOME/.elan'

verify_root_owned_directory_chain() {
  local directory=$1 owner mode
  while :; do
    owner=$(stat -Lc '%u' "$directory")
    mode=$(stat -Lc '%a' "$directory")
    [[ "$owner" == 0 ]] || \
      die "system binary parent is not root-owned: $directory"
    (( (8#$mode & 8#022) == 0 )) || \
      die "system binary parent is group/world writable: $directory"
    [[ "$directory" == / ]] && break
    directory=$(dirname "$directory")
  done
}

verify_system_binary() {
  local actual=$1
  local expected=$2
  shift 2
  [[ "$actual" == "$expected" ]] || \
    die "expected Ubuntu system binary $expected, found $actual"
  local allowed allowed_target=false owner mode resolved
  resolved=$(realpath "$actual")
  for allowed in "$@"; do
    if [[ "$resolved" == "$allowed" ]]; then
      allowed_target=true
      break
    fi
  done
  [[ "$allowed_target" == true ]] || \
    die "system binary has an unapproved Ubuntu target: $actual -> $resolved"
  [[ -f "$resolved" && -x "$resolved" ]] || \
    die "system binary target is not an executable regular file: $resolved"

  verify_root_owned_directory_chain "$(dirname "$actual")"
  verify_root_owned_directory_chain "$(dirname "$resolved")"

  owner=$(stat -Lc '%u' "$resolved")
  mode=$(stat -Lc '%a' "$resolved")
  [[ "$owner" == 0 ]] || die "system binary is not root-owned: $actual"
  (( (8#$mode & 8#022) == 0 )) || \
    die "system binary is group/world writable: $actual"
}

verify_all_system_binaries() {
  verify_system_binary "$GIT_BIN" /usr/bin/git /usr/bin/git
  verify_system_binary "$NODE_BIN" /usr/bin/node /usr/bin/node /usr/bin/nodejs
  verify_system_binary "$SCRIPT_BIN" /usr/bin/script /usr/bin/script
  verify_system_binary "$SETPRIV_BIN" /usr/bin/setpriv /usr/bin/setpriv
  verify_system_binary \
    "$SYSTEMD_RUN_BIN" /usr/bin/systemd-run /usr/bin/systemd-run
  verify_system_binary "$SYSTEMCTL_BIN" /usr/bin/systemctl /usr/bin/systemctl
  verify_system_binary "$SHA256SUM_BIN" /usr/bin/sha256sum \
    /usr/bin/sha256sum /usr/bin/gnusha256sum \
    /usr/lib/cargo/bin/coreutils/sha256sum
  verify_system_binary "$TRUNCATE_BIN" /usr/bin/truncate \
    /usr/bin/truncate /usr/bin/gnutruncate \
    /usr/lib/cargo/bin/coreutils/truncate
  verify_system_binary "$TOUCH_BIN" /usr/bin/touch \
    /usr/bin/touch /usr/bin/gnutouch /usr/lib/cargo/bin/coreutils/touch
  verify_system_binary "$RM_BIN" /usr/bin/rm \
    /usr/bin/rm /usr/bin/gnurm /usr/lib/cargo/bin/coreutils/rm
  verify_system_binary "$MV_BIN" /usr/bin/mv \
    /usr/bin/mv /usr/bin/gnumv /usr/lib/cargo/bin/coreutils/mv
}

verify_all_system_binaries
SCRIPT_SHA=$("$SHA256SUM_BIN" "$SCRIPT_PATH" | sed 's/[[:space:]].*$//')

compute_system_binary_state() {
  local name actual resolved digest index
  local -a names=(
    git node script setpriv systemd_run systemctl sha256sum truncate touch rm mv
  )
  local -a paths=(
    "$GIT_BIN" "$NODE_BIN" "$SCRIPT_BIN" "$SETPRIV_BIN" "$SYSTEMD_RUN_BIN"
    "$SYSTEMCTL_BIN" "$SHA256SUM_BIN" "$TRUNCATE_BIN" "$TOUCH_BIN"
    "$RM_BIN" "$MV_BIN"
  )
  for index in "${!names[@]}"; do
    name=${names[$index]}
    actual=${paths[$index]}
    resolved=$(realpath "$actual")
    digest=$("$SHA256SUM_BIN" "$resolved" | sed 's/[[:space:]].*$//')
    printf 'system_binary_%s_path=%s\n' "$name" "$actual"
    printf 'system_binary_%s_resolved=%s\n' "$name" "$resolved"
    printf 'system_binary_%s_sha256=%s\n' "$name" "$digest"
  done
}

SYSTEM_BINARY_STATE=$(compute_system_binary_state)

assert_system_binary_state() {
  local current_state
  verify_all_system_binaries
  current_state=$(compute_system_binary_state)
  [[ "$current_state" == "$SYSTEM_BINARY_STATE" ]] || \
    die 'an audited Ubuntu system binary changed during the run'
}

TRUSTED_BASE_PATH="/usr/bin:/bin:$ELAN_BIN_DIR"
export PATH="$TRUSTED_BASE_PATH"
[[ "$(command -v git)" == "$GIT_BIN" && \
   "$(realpath "$(command -v git)")" == "$(realpath "$GIT_BIN")" && \
   "$(command -v lake)" == "$LAKE_COMMAND" && \
   "$(realpath "$(command -v lake)")" == "$LAKE_BIN" ]] || \
  die 'trusted PATH does not resolve the expected Git and Lake binaries'

USER_MANAGER_ENV=$($SYSTEMCTL_BIN --user show-environment) || \
  die 'systemd --user is unavailable; install dbus-user-session and log out/in'
if /usr/bin/grep -Eq '^BASH_FUNC_[^=]*=' <<<"$USER_MANAGER_ENV"; then
  die 'systemd --user manager contains an exported Bash function'
fi
for variable_name in \
  BASH_ENV BASH_XTRACEFD COMPARATOR_BIN COMPARATOR_CONFIG COMPARATOR_LANDRUN \
  COMPARATOR_LEAN4EXPORT COMPARATOR_NANODA ELAN_DIST_SERVER ELAN_HOME \
  ELAN_TOOLCHAIN ELAN_UPDATE_ROOT ENV GIT_ALTERNATE_OBJECT_DIRECTORIES \
  GIT_ATTR_NOSYSTEM GIT_CEILING_DIRECTORIES GIT_COMMON_DIR GIT_CONFIG \
  GIT_CONFIG_COUNT GIT_CONFIG_GLOBAL GIT_CONFIG_PARAMETERS \
  GIT_CONFIG_SYSTEM GIT_DIR GIT_DISCOVERY_ACROSS_FILESYSTEM GIT_EXEC_PATH \
  GIT_INDEX_FILE GIT_OBJECT_DIRECTORY GIT_SSH GIT_SSH_COMMAND \
  GIT_SSH_VARIANT GIT_TEMPLATE_DIR GIT_WORK_TREE GOWORK GZIP LAKE_HOME LD_AUDIT \
  LD_LIBRARY_PATH LD_PRELOAD LEAN_PATH LEAN_SRC_PATH LEAN_SYSROOT LEAN_OPTS \
  MATHLIB_CACHE_URL NODE_OPTIONS SYSTEMD_ADJUST_TERMINAL_TITLE TAR_OPTIONS \
  ZSTD_CLEVEL ZSTD_NBTHREADS; do
  if grep -Fq "$variable_name=" <<<"$USER_MANAGER_ENV"; then
    die "systemd --user manager contains forbidden environment variable: $variable_name"
  fi
done

# systemd 259 writes an OSC window-title sequence immediately before the first
# payload byte of an interactive systemd-run --pty session. Disable that
# transport decoration so exact security markers remain exact transcript lines.
export SYSTEMD_ADJUST_TERMINAL_TITLE=0

TRANSIENT_SECURITY_ASSERTION='/usr/bin/grep -Eq "^CapInh:[[:space:]]*0+$" /proc/self/status'
TRANSIENT_SECURITY_ASSERTION+=' && /usr/bin/grep -Eq "^CapPrm:[[:space:]]*0+$" /proc/self/status'
TRANSIENT_SECURITY_ASSERTION+=' && /usr/bin/grep -Eq "^CapEff:[[:space:]]*0+$" /proc/self/status'
TRANSIENT_SECURITY_ASSERTION+=' && /usr/bin/grep -Eq "^CapAmb:[[:space:]]*0+$" /proc/self/status'
TRANSIENT_SECURITY_ASSERTION+=' && /usr/bin/grep -Eq "^NoNewPrivs:[[:space:]]*1$" /proc/self/status'
TRANSIENT_SECURITY_ASSERTION+=' && echo transient_security_context=passed'

# pam_systemd gives CAP_WAKE_ALARM to local user sessions and user@.service on
# current Ubuntu releases. A transient --user unit is forked by that independent
# manager, not by this already-clean launcher. Drop the manager's inheritable
# capability inside every payload, while retaining systemd's NNP property and
# the fail-closed assertions above.
TRANSIENT_PRIVILEGE_DROP=(
  "$SETPRIV_BIN"
  --inh-caps=-all
  --ambient-caps=-all
  --no-new-privs
  --
)

set +e
SHELL=/bin/bash "$SCRIPT_BIN" --quiet --return --flush \
  --output-limit 16M \
  --command 'test -t 0 && test -t 1 && test -t 2 || exit 38; exit 37' \
  /dev/null >/dev/null 2>&1
SCRIPT_STATUS=$?
set -e
[[ $SCRIPT_STATUS -eq 37 ]] || \
  die 'util-linux script did not provide three TTY file descriptors and propagate exit status 37'

SYSTEMD_PREFLIGHT=(
  "$SYSTEMD_RUN_BIN"
  '--property=RestrictAddressFamilies=~AF_UNIX'
  '--property=NoNewPrivileges=yes'
  --user --pty --wait --collect
  -E "PATH=$TRUSTED_BASE_PATH"
  --working-directory "$SOURCE_ROOT"
  -- "${TRANSIENT_PRIVILEGE_DROP[@]}" /bin/bash -c "$TRANSIENT_SECURITY_ASSERTION"
)
SYSTEMD_PREFLIGHT_COMMAND=$(quote_command "${SYSTEMD_PREFLIGHT[@]}")
SYSTEMD_PREFLIGHT_LOG=$(mktemp "${TMPDIR:-/tmp}/paper-c-systemd-preflight.XXXXXX")
set +e
SHELL=/bin/bash "$SCRIPT_BIN" --quiet --return --flush \
  --output-limit 16M --command "$SYSTEMD_PREFLIGHT_COMMAND" "$SYSTEMD_PREFLIGHT_LOG" \
  >/dev/null 2>&1
SYSTEMD_PREFLIGHT_STATUS=$?
set -e
if [[ $SYSTEMD_PREFLIGHT_STATUS -ne 0 ]]; then
  note 'systemd --user PTY wrapper diagnostic follows:' >&2
  sed -n '1,80l' "$SYSTEMD_PREFLIGHT_LOG" >&2
  rm -f -- "$SYSTEMD_PREFLIGHT_LOG"
  SYSTEMD_PREFLIGHT_LOG=
  die 'the systemd --user PTY wrapper probe failed'
fi
if ! transcript_has_exact_line "$SYSTEMD_PREFLIGHT_LOG" 'transient_security_context=passed'; then
  note 'systemd --user PTY marker diagnostic follows:' >&2
  sed -n '1,80l' "$SYSTEMD_PREFLIGHT_LOG" >&2
  rm -f -- "$SYSTEMD_PREFLIGHT_LOG"
  SYSTEMD_PREFLIGHT_LOG=
  die 'the systemd --user PTY security marker is not an exact line'
fi
rm -f -- "$SYSTEMD_PREFLIGHT_LOG"
SYSTEMD_PREFLIGHT_LOG=

SYSTEMD_FAILURE_UNIT="paper-c-exit-probe-$$"
SYSTEMD_FAILURE_PREFLIGHT=(
  "$SYSTEMD_RUN_BIN"
  "--unit=$SYSTEMD_FAILURE_UNIT"
  '--property=RestrictAddressFamilies=~AF_UNIX'
  '--property=NoNewPrivileges=yes'
  '--property=RuntimeMaxSec=2min'
  --user --pty --wait --collect
  -E "PATH=$TRUSTED_BASE_PATH"
  --working-directory "$SOURCE_ROOT"
  -- "${TRANSIENT_PRIVILEGE_DROP[@]}" /bin/bash -c \
  "$TRANSIENT_SECURITY_ASSERTION || exit 38; exit 37"
)
SYSTEMD_FAILURE_COMMAND=$(quote_command "${SYSTEMD_FAILURE_PREFLIGHT[@]}")
CURRENT_UNIT=$SYSTEMD_FAILURE_UNIT
set +e
SHELL=/bin/bash "$SCRIPT_BIN" --quiet --return --flush \
  --output-limit 16M --command "$SYSTEMD_FAILURE_COMMAND" /dev/null \
  >/dev/null 2>&1
SYSTEMD_FAILURE_STATUS=$?
set -e
cleanup_unit "$SYSTEMD_FAILURE_UNIT" || \
  die 'failed systemd exit-propagation probe left an active unit'
CURRENT_UNIT=
[[ $SYSTEMD_FAILURE_STATUS -eq 37 ]] || \
  die "systemd-run did not propagate child exit status 37 (got $SYSTEMD_FAILURE_STATUS)"

note "preflight passed for Paper C commit $PAPER_COMMIT"
note "Lean toolchain: $PROJECT_TOOLCHAIN"
note "systemd: $SYSTEMD_VERSION; kernel: $KERNEL_RELEASE"
if [[ "$PREFLIGHT_ONLY" == true ]]; then
  note 'preflight-only mode: no tools were downloaded and no Comparator run was started'
  exit 0
fi

if [[ -n "$OUTPUT_ARGUMENT" ]]; then
  OUTPUT_DIR=$(realpath -m -- "$OUTPUT_ARGUMENT")
else
  OUTPUT_DIR="$(dirname "$SOURCE_ROOT")/paper-c-hardened-evidence-${PAPER_COMMIT:0:12}-$(date -u +%Y%m%dT%H%M%SZ)"
fi
case "$OUTPUT_DIR" in
  "$SOURCE_ROOT"|"$SOURCE_ROOT"/*)
    die 'the evidence directory must be outside the source repository'
    ;;
esac
[[ ! -e "$OUTPUT_DIR" ]] || die "output path already exists: $OUTPUT_DIR"
[[ ! -e "$OUTPUT_DIR.tar.zst" && ! -e "$OUTPUT_DIR.tar.zst.partial" && \
   ! -e "$OUTPUT_DIR.tar.zst.sha256" && \
   ! -e "$OUTPUT_DIR.tar.zst.sha256.partial" ]] || \
  die "evidence bundle path already exists beside: $OUTPUT_DIR"
mkdir -m 700 -p "$OUTPUT_DIR/evidence"
OUTPUT_OWNED=true
SETUP_LOG="$OUTPUT_DIR/setup.log"
touch "$SETUP_LOG"

TMP_PARENT=$(realpath "${TMPDIR:-/tmp}")
case "$TMP_PARENT" in
  "$SOURCE_ROOT"|"$SOURCE_ROOT"/*)
    die 'TMPDIR must be outside the source repository'
    ;;
esac
WORK_ROOT=$(mktemp -d "$TMP_PARENT/paper-c-hardened.XXXXXXXX")
note "evidence directory: $OUTPUT_DIR" | tee -a "$SETUP_LOG"
note "temporary work directory: $WORK_ROOT" | tee -a "$SETUP_LOG"
df -h "$WORK_ROOT" | tee -a "$SETUP_LOG"

run_logged() {
  local status
  printf '[paper-c-hardened] command=' | tee -a "$SETUP_LOG"
  printf ' %q' "$@" | tee -a "$SETUP_LOG"
  printf '\n' | tee -a "$SETUP_LOG"
  set +e
  "$@" 2>&1 | tee -a "$SETUP_LOG"
  status=${PIPESTATUS[0]}
  set -e
  [[ $status -eq 0 ]] || die "setup command failed with status $status: $1"
}

run_logged_in() {
  local directory=$1
  shift
  local status
  printf '[paper-c-hardened] cwd=%q command=' "$directory" | tee -a "$SETUP_LOG"
  printf ' %q' "$@" | tee -a "$SETUP_LOG"
  printf '\n' | tee -a "$SETUP_LOG"
  set +e
  (
    cd "$directory"
    "$@"
  ) 2>&1 | tee -a "$SETUP_LOG"
  status=${PIPESTATUS[0]}
  set -e
  [[ $status -eq 0 ]] || die "setup command failed with status $status in $directory"
}

probe_lean_toolchain() {
  env -i PATH="$TRUSTED_BASE_PATH" HOME="$HOME" \
    ELAN_HOME="$EXPECTED_ELAN_HOME" LANG=C.UTF-8 LC_ALL=C.UTF-8 \
    "$ELAN_BIN" run "$PROJECT_TOOLCHAIN" lean --version
}

note "ensuring Lean toolchain $PROJECT_TOOLCHAIN" | tee -a "$SETUP_LOG"
run_logged env -i PATH="$TRUSTED_BASE_PATH" HOME="$HOME" \
  ELAN_HOME="$EXPECTED_ELAN_HOME" LANG=C.UTF-8 LC_ALL=C.UTF-8 \
  "$ELAN_BIN" run --install "$PROJECT_TOOLCHAIN" lean --version
set +e
LEAN_VERSION_OUTPUT=$(probe_lean_toolchain 2>&1)
LEAN_VERSION_STATUS=$?
set -e
if [[ $LEAN_VERSION_STATUS -ne 0 ]]; then
  printf '%s\n' "$LEAN_VERSION_OUTPUT" | tee -a "$SETUP_LOG" >&2
  die "Lean toolchain is unusable after setup: $PROJECT_TOOLCHAIN"
fi
LEAN_VERSION_PATTERN='^Lean \(version [^,]+, [^,]+, commit ([0-9a-f]{40}), [^)]+\)$'
[[ "$LEAN_VERSION_OUTPUT" != *$'\n'* && \
   "$LEAN_VERSION_OUTPUT" =~ $LEAN_VERSION_PATTERN ]] || \
  die 'Lean version output does not have the expected single-line structure'
LEAN_VERSION_COMMIT=${BASH_REMATCH[1]}
[[ "$LEAN_VERSION_COMMIT" == "$LEAN_COMMIT" ]] || \
  die "Lean version reports unexpected commit $LEAN_VERSION_COMMIT"
printf '%s\n' "$LEAN_VERSION_OUTPUT" | tee -a "$SETUP_LOG"

GO_VERSION=1.24.13
case "$(uname -m)" in
  x86_64)
    GO_ARCH=amd64
    GO_ARCHIVE_SHA=1fc94b57134d51669c72173ad5d49fd62afb0f1db9bf3f798fd98ee423f8d730
    ;;
  aarch64|arm64)
    GO_ARCH=arm64
    GO_ARCHIVE_SHA=74d97be1cc3a474129590c67ebf748a96e72d9f3a2b6fef3ed3275de591d49b3
    ;;
  *)
    die "unsupported architecture for pinned Go toolchain: $(uname -m)"
    ;;
esac
GO_ARCHIVE="$WORK_ROOT/go${GO_VERSION}.linux-${GO_ARCH}.tar.gz"
GO_URL="https://go.dev/dl/go${GO_VERSION}.linux-${GO_ARCH}.tar.gz"
run_logged curl --disable --proto '=https' --tlsv1.2 \
  --fail --location --silent --show-error \
  "$GO_URL" --output "$GO_ARCHIVE"
printf '%s  %s\n' "$GO_ARCHIVE_SHA" "$GO_ARCHIVE" | sha256sum --check - | \
  tee -a "$SETUP_LOG"
mkdir -p "$WORK_ROOT/go-toolchain"
run_logged tar -C "$WORK_ROOT/go-toolchain" -xzf "$GO_ARCHIVE"
GO_BIN="$WORK_ROOT/go-toolchain/go/bin/go"
[[ -x "$GO_BIN" ]] || die 'pinned Go binary was not extracted'
GO_VERSION_OUTPUT=$($GO_BIN version)
[[ "$GO_VERSION_OUTPUT" == "go version go${GO_VERSION} "* ]] || \
  die "unexpected pinned Go version: $GO_VERSION_OUTPUT"
printf '%s\n' "$GO_VERSION_OUTPUT" | tee -a "$SETUP_LOG"

TRUSTED_PATH="$(dirname "$GO_BIN"):$TRUSTED_BASE_PATH"
TOOLS_ROOT="$WORK_ROOT/tools"
mkdir -p "$TOOLS_ROOT/bin"

clone_pinned() {
  local repository=$1
  local commit=$2
  local destination=$3
  run_logged "$GIT_BIN" init --quiet "$destination"
  run_logged "$GIT_BIN" -C "$destination" remote add origin "$repository"
  run_logged "$GIT_BIN" -C "$destination" fetch --quiet --depth=1 origin "$commit"
  run_logged "$GIT_BIN" -C "$destination" checkout --quiet --detach FETCH_HEAD
  [[ "$($GIT_BIN -C "$destination" rev-parse HEAD)" == "$commit" ]] || \
    die "pinned checkout mismatch in $destination"
}

COMPARATOR_SOURCE="$TOOLS_ROOT/comparator"
LEAN4EXPORT_SOURCE="$TOOLS_ROOT/lean4export"
LANDRUN_SOURCE="$TOOLS_ROOT/landrun"
clone_pinned "$COMPARATOR_REPOSITORY" "$COMPARATOR_COMMIT" "$COMPARATOR_SOURCE"
clone_pinned "$LEAN4EXPORT_REPOSITORY" "$LEAN4EXPORT_COMMIT" "$LEAN4EXPORT_SOURCE"
clone_pinned "$LANDRUN_REPOSITORY" "$LANDRUN_COMMIT" "$LANDRUN_SOURCE"

run_logged_in "$COMPARATOR_SOURCE" \
  env -i PATH="$TRUSTED_PATH" HOME="$HOME" \
    ELAN_HOME="$EXPECTED_ELAN_HOME" LANG=C.UTF-8 LC_ALL=C.UTF-8 \
    "$ELAN_BIN" run "$PROJECT_TOOLCHAIN" lake build comparator
[[ "$($GIT_BIN -C "$COMPARATOR_SOURCE/.lake/packages/lean4export" rev-parse HEAD)" \
    == "$LEAN4EXPORT_COMMIT" ]] || \
  die 'Comparator resolved an unexpected lean4export revision'
run_logged_in "$LEAN4EXPORT_SOURCE" \
  env -i PATH="$TRUSTED_PATH" HOME="$HOME" \
    ELAN_HOME="$EXPECTED_ELAN_HOME" LANG=C.UTF-8 LC_ALL=C.UTF-8 \
    "$ELAN_BIN" run "$PROJECT_TOOLCHAIN" lake build lean4export
GO_BUILD_HOME="$WORK_ROOT/go-build-home"
GO_CACHE="$WORK_ROOT/go-build-cache"
GO_MODULE_CACHE="$WORK_ROOT/go-module-cache"
GO_PATH="$WORK_ROOT/go-path"
mkdir -m 700 -p "$GO_BUILD_HOME" "$GO_CACHE" "$GO_MODULE_CACHE" "$GO_PATH"
run_logged_in "$LANDRUN_SOURCE" \
  env -i PATH="$TRUSTED_PATH" HOME="$GO_BUILD_HOME" \
    GOENV=off GOFLAGS= GOWORK=off GOTOOLCHAIN=local CGO_ENABLED=0 \
    GOCACHE="$GO_CACHE" GOMODCACHE="$GO_MODULE_CACHE" GOPATH="$GO_PATH" \
    GOPROXY=https://proxy.golang.org,direct GOSUMDB=sum.golang.org \
    GONOPROXY= GOPRIVATE= GONOSUMDB= GOINSECURE= \
    "$GO_BIN" build -buildvcs=true -mod=readonly -trimpath \
      -o "$TOOLS_ROOT/bin/landrun" ./cmd/landrun

COMPARATOR_BIN=$(realpath "$COMPARATOR_SOURCE/.lake/build/bin/comparator")
LEAN4EXPORT_BIN=$(realpath "$LEAN4EXPORT_SOURCE/.lake/build/bin/lean4export")
LANDRUN_BIN=$(realpath "$TOOLS_ROOT/bin/landrun")
for executable in "$COMPARATOR_BIN" "$LEAN4EXPORT_BIN" "$LANDRUN_BIN"; do
  [[ -x "$executable" ]] || die "expected executable is missing: $executable"
done

GO_BUILD_INFO=$($GO_BIN version -m "$LANDRUN_BIN")
grep -Fq "vcs.revision=$LANDRUN_COMMIT" <<<"$GO_BUILD_INFO" || \
  die 'landrun binary does not record the pinned VCS revision'
grep -Fq 'vcs.modified=false' <<<"$GO_BUILD_INFO" || \
  die 'landrun binary records a modified source tree'
printf '%s\n' "$GO_BUILD_INFO" | tee -a "$SETUP_LOG"

COMPARATOR_SHA=$(sha256sum "$COMPARATOR_BIN" | sed 's/[[:space:]].*$//')
LEAN4EXPORT_SHA=$(sha256sum "$LEAN4EXPORT_BIN" | sed 's/[[:space:]].*$//')
LANDRUN_SHA=$(sha256sum "$LANDRUN_BIN" | sed 's/[[:space:]].*$//')
TRANSPORT_SHA=$(sha256sum "$SCRIPT_BIN" | sed 's/[[:space:]].*$//')
TRANSPORT_VERSION=$($SCRIPT_BIN --version | sed -n '1p')

for source_tree in "$COMPARATOR_SOURCE" "$LEAN4EXPORT_SOURCE" "$LANDRUN_SOURCE"; do
  $GIT_BIN -C "$source_tree" diff --quiet
  $GIT_BIN -C "$source_tree" diff --cached --quiet
done
[[ "$($GIT_BIN -C "$COMPARATOR_SOURCE" rev-parse HEAD)" == "$COMPARATOR_COMMIT" && \
   "$($GIT_BIN -C "$LEAN4EXPORT_SOURCE" rev-parse HEAD)" == "$LEAN4EXPORT_COMMIT" && \
   "$($GIT_BIN -C "$LANDRUN_SOURCE" rev-parse HEAD)" == "$LANDRUN_COMMIT" ]] || \
  die 'a pinned tool checkout changed revision during its build'

declare -A PROJECT_PATHS
declare -A PREEXISTING_OLEAN_COUNTS

assert_checkout_unchanged() {
  local project=$1
  local phase=$2
  [[ "$($GIT_BIN -C "$project" rev-parse HEAD)" == "$PAPER_COMMIT" ]] || \
    die "Paper C HEAD changed $phase: $project"
  local tracked_status
  tracked_status=$($GIT_BIN -C "$project" status --porcelain --untracked-files=no)
  if [[ -n "$tracked_status" ]]; then
    printf '%s\n' "$tracked_status" >&2
    die "tracked Paper C files changed $phase: $project"
  fi
  local unexpected=()
  while IFS= read -r -d '' relative_path; do
    unexpected+=("$relative_path")
  done < <(
    "$GIT_BIN" -C "$project" ls-files --others -z -- \
      . ':(exclude).lake/**'
  )
  if (( ${#unexpected[@]} > 0 )); then
    printf '%s\n' "${unexpected[@]}" >&2
    die "untracked file outside .lake $phase: $project"
  fi
}

assert_no_project_build_artifacts() {
  local project=$1
  local phase=$2
  [[ ! -e "$project/.lake/build" && ! -e "$project/.lake/config" ]] || \
    die "project build/config artifacts exist $phase: $project"
  local project_oleans
  project_oleans=$(find "$project" \
    -path "$project/.lake/packages" -prune -o \
    -type f -name '*.olean' -print)
  if [[ -n "$project_oleans" ]]; then
    printf '%s\n' "$project_oleans" >&2
    die "project olean exists $phase: $project"
  fi
}

verify_package_revisions() {
  local project=$1
  "$NODE_BIN" - "$project/lake-manifest.json" "$project" "$GIT_BIN" <<'NODE'
const fs = require('node:fs');
const path = require('node:path');
const {spawnSync} = require('node:child_process');
const manifest = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const root = process.argv[3];
const git = process.argv[4];
for (const pkg of manifest.packages) {
  if (typeof pkg.rev !== 'string' || !/^[0-9a-f]{40}$/.test(pkg.rev)) continue;
  const directory = path.join(root, '.lake', 'packages', pkg.name);
  const head = spawnSync(git, ['-C', directory, 'rev-parse', 'HEAD'], {encoding: 'utf8'});
  const worktree = spawnSync(git, ['-C', directory, 'diff', '--quiet']);
  const index = spawnSync(git, ['-C', directory, 'diff', '--cached', '--quiet']);
  if (head.status !== 0 || head.stdout.trim() !== pkg.rev ||
      worktree.status !== 0 || index.status !== 0) {
    throw new Error(`${pkg.name}: package checkout does not match manifest rev ${pkg.rev}`);
  }
}
console.log('all Git packages match lake-manifest.json and have clean tracked sources');
NODE
}

prepare_project() {
  local label=$1
  local project="$WORK_ROOT/project-$label"
  note "preparing fresh project checkout: $label" | tee -a "$SETUP_LOG"
  run_logged "$GIT_BIN" clone --quiet --no-local "$SOURCE_ROOT" "$project"
  run_logged "$GIT_BIN" -C "$project" checkout --quiet --detach "$PAPER_COMMIT"
  [[ "$($GIT_BIN -C "$project" rev-parse HEAD)" == "$PAPER_COMMIT" ]] || \
    die "Paper C commit mismatch in $project"
  [[ -z "$($GIT_BIN -C "$project" status --porcelain --untracked-files=all)" ]] || \
    die "fresh Paper C checkout is not clean: $project"

  local before_oleans
  before_oleans=$(find "$project" -type f -name '*.olean' -print)
  [[ -z "$before_oleans" ]] || die "fresh checkout contains a pre-existing .olean: $project"
  PREEXISTING_OLEAN_COUNTS[$label]=0

  run_logged_in "$project" "$NODE_BIN" scripts/check_comparator_sources.mjs
  run_logged_in "$project" "$NODE_BIN" scripts/generate_audit.mjs --check-pdfs
  run_logged_in "$project" "$NODE_BIN" scripts/generate_audit.mjs --check-source-digest
  run_logged_in "$project" "$NODE_BIN" \
    scripts/generate_audit.mjs --check-literature-certificates
  run_logged_in "$project" "$NODE_BIN" scripts/generate_audit.mjs --check
  run_logged_in "$project" \
    env -i PATH="$TRUSTED_PATH" HOME="$HOME" \
      ELAN_HOME="$EXPECTED_ELAN_HOME" LANG=C.UTF-8 LC_ALL=C.UTF-8 \
      "$ELAN_BIN" run "$PROJECT_TOOLCHAIN" lake exe cache get
  verify_package_revisions "$project" 2>&1 | tee -a "$SETUP_LOG"

  # Cache setup may compile Lake's own configuration.  Remove only those
  # known project-local setup artifacts, retain dependency caches, then fail
  # if any project olean remains outside .lake/packages.
  rm -rf -- "$project/.lake/build" "$project/.lake/config"
  rm -f -- "$project/.lake/lakefile.olean" "$project/.lake/lakefile.ilean"
  assert_no_project_build_artifacts "$project" 'after cache preparation'
  assert_checkout_unchanged "$project" 'during cache preparation'

  local mathlib_head
  mathlib_head=$($GIT_BIN -C "$project/.lake/packages/mathlib" rev-parse HEAD)
  [[ "$mathlib_head" == "$MATHLIB_COMMIT" ]] || \
    die "Mathlib checkout mismatch: $mathlib_head"
  PROJECT_PATHS[$label]=$project
}

compute_fileset_digest() {
  local project=$1
  "$NODE_BIN" - "$project/audit_config.json" "$project" <<'NODE'
const crypto = require('node:crypto');
const fs = require('node:fs');
const path = require('node:path');
const config = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const root = process.argv[3];
const compare = (left, right) => Buffer.from(left).compare(Buffer.from(right));
const hash = crypto.createHash('sha256');
for (const relativePath of [...config.verification.comparator.fileset].sort(compare)) {
  hash.update(relativePath);
  hash.update('\0');
  hash.update(fs.readFileSync(path.join(root, relativePath)));
  hash.update('\0');
}
process.stdout.write(hash.digest('hex'));
NODE
}

cleanup_failed_unit_if_needed() {
  local unit=$1
  cleanup_unit "$unit" || die "transient unit remains active: $unit.service"
}

run_target() {
  local label=$1
  local config_relative=$2
  local project=${PROJECT_PATHS[$label]}
  local partial_dir="$OUTPUT_DIR/evidence/$label.partial"
  local final_dir="$OUTPUT_DIR/evidence/$label"
  mkdir -m 700 "$partial_dir"

  local environment_log="$partial_dir/comparator-environment.txt"
  local probe_log="$partial_dir/hardening-probe.log"
  local run_log="$partial_dir/comparator-$label.log"
  local transcript="$partial_dir/comparator-$label.txt"
  local result_json="$partial_dir/result-$label.json"
  local pty_raw="$partial_dir/systemd-pty.raw"
  local probe_raw="$partial_dir/systemd-probe-pty.raw"
  local config_path="$project/$config_relative"
  local config_sha fileset_sha mathlib_head

  assert_system_binary_state
  [[ -f "$config_path" ]] || die "Comparator configuration is missing: $config_relative"
  "$NODE_BIN" - "$config_path" <<'NODE'
const fs = require('node:fs');
const config = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const expectedAxioms = ['propext', 'Quot.sound', 'Classical.choice'];
if (config.enable_nanoda !== false) throw new Error('enable_nanoda must be false');
if (JSON.stringify(config.permitted_axioms) !== JSON.stringify(expectedAxioms)) {
  throw new Error('unexpected permitted_axioms');
}
if (!Array.isArray(config.theorem_names) || config.theorem_names.length !== 1) {
  throw new Error('each Paper C Comparator config must contain exactly one theorem');
}
NODE

  assert_checkout_unchanged "$project" "before $label"
  assert_no_project_build_artifacts "$project" "before $label"
  config_sha=$(sha256sum "$config_path" | sed 's/[[:space:]].*$//')
  fileset_sha=$(compute_fileset_digest "$project")
  mathlib_head=$($GIT_BIN -C "$project/.lake/packages/mathlib" rev-parse HEAD)

  {
    echo "timestamp=$(date --iso-8601=seconds)"
    echo 'github_repository=local-hardened-run'
    echo "github_sha=$PAPER_COMMIT"
    echo 'github_run_id=local'
    echo 'github_run_attempt=1'
    echo "paper_c_commit=$PAPER_COMMIT"
    echo 'tracked_worktree_dirty_count=0'
    echo "preexisting_project_olean_count=${PREEXISTING_OLEAN_COUNTS[$label]}"
    echo "comparator_commit=$COMPARATOR_COMMIT"
    echo "lean4export_commit=$LEAN4EXPORT_COMMIT"
    echo "landrun_commit=$LANDRUN_COMMIT"
    echo "lean_commit=$LEAN_COMMIT"
    echo "mathlib_commit=$MATHLIB_COMMIT"
    echo "config=$config_relative"
    echo "$config_sha  $config_relative"
    echo "comparator_fileset_digest_sha256=$fileset_sha"
    echo "project_toolchain=$PROJECT_TOOLCHAIN"
    echo "comparator_source_toolchain=$(tr -d '\r\n' < "$COMPARATOR_SOURCE/lean-toolchain")"
    echo 'comparator_build_toolchain=Paper C project toolchain'
    echo 'lean4export_build_toolchain=Paper C project toolchain'
    echo 'ld_preload=unset'
    echo 'non_root=true'
    echo "launcher_no_new_privs=$NO_NEW_PRIVS"
    echo 'transient_no_new_privs_required=true'
    echo 'transient_zero_capabilities_required=true'
    echo 'transient_capability_drop_method=setpriv'
    echo 'systemd_adjust_terminal_title=0'
    echo "execution_uid=$(id -u)"
    echo "execution_gid=$(id -g)"
    echo 'runner_os=Linux'
    echo "runner_arch=$(uname -m)"
    echo "uname=$(uname -a)"
    echo "os_release=$(tr '\n' ';' < /etc/os-release)"
    "$SYSTEMD_RUN_BIN" --version | sed -n '1p'
    "$GIT_BIN" --version
    "$NODE_BIN" -e '
      const fs = require("node:fs");
      const manifest = JSON.parse(fs.readFileSync(process.argv[1], "utf8"));
      const mathlib = manifest.packages.find(pkg => pkg.name === "mathlib");
      if (!mathlib) throw new Error("mathlib missing from lake-manifest.json");
      console.log(`mathlib_manifest_revision=${mathlib.rev}`);
      console.log(`mathlib_manifest_input_revision=${mathlib.inputRev}`);
    ' "$project/lake-manifest.json"
    env ELAN_HOME="$EXPECTED_ELAN_HOME" \
      "$ELAN_BIN" run "$PROJECT_TOOLCHAIN" lean --version
    env ELAN_HOME="$EXPECTED_ELAN_HOME" \
      "$ELAN_BIN" run "$PROJECT_TOOLCHAIN" lake --version
    echo "$GO_VERSION_OUTPUT"
    echo "mathlib_checkout_commit=$mathlib_head"
    echo "$COMPARATOR_SHA  comparator-binary"
    echo "$LEAN4EXPORT_SHA  lean4export-binary"
    echo "$LANDRUN_SHA  landrun-binary"
    echo "runner_script_sha256=$SCRIPT_SHA"
    echo "pty_transport_sha256=$TRANSPORT_SHA"
    echo "pty_transport_version=$TRANSPORT_VERSION"
    printf '%s\n' "$SYSTEM_BINARY_STATE"
    echo "git_binary_path=$GIT_BIN"
    echo "git_binary_resolved=$(realpath "$GIT_BIN")"
    echo "sha256sum_binary_path=$SHA256SUM_BIN"
    echo "sha256sum_binary_resolved=$(realpath "$SHA256SUM_BIN")"
    echo "truncate_binary_resolved=$(realpath "$TRUNCATE_BIN")"
    echo "touch_binary_resolved=$(realpath "$TOUCH_BIN")"
    echo "rm_binary_resolved=$(realpath "$RM_BIN")"
    echo "mv_binary_resolved=$(realpath "$MV_BIN")"
    echo "systemd_run_binary_sha256=$(sha256sum "$SYSTEMD_RUN_BIN" | sed 's/[[:space:]].*$//')"
    echo "systemctl_binary_sha256=$(sha256sum "$SYSTEMCTL_BIN" | sed 's/[[:space:]].*$//')"
    echo "git_binary_sha256=$(sha256sum "$GIT_BIN" | sed 's/[[:space:]].*$//')"
    echo "sha256sum_binary_sha256=$(sha256sum "$SHA256SUM_BIN" | sed 's/[[:space:]].*$//')"
    "$LANDRUN_BIN" --version
    id
  } >"$environment_log" 2>&1

  : >"$probe_log"
  {
    echo 'wrapper_stdin_tty=true'
    echo 'wrapper_stdout_tty=true'
    echo 'wrapper_stderr_tty=true'
    echo 'Probing landrun with the flags used by pinned Comparator.'
  } >>"$probe_log"
  "$LANDRUN_BIN" --best-effort --ro / --rw /dev -ldd -add-exec -- \
    /usr/bin/true >>"$probe_log" 2>&1 || \
    die "landrun positive probe failed for $label"

  local negative_dir="$project/.landrun-negative-controls"
  rm -rf -- "$negative_dir"
  mkdir -m 700 "$negative_dir"

  local create_probe="$negative_dir/create-must-fail"
  set +e
  "$LANDRUN_BIN" --best-effort --ro / --rw /dev -ldd -add-exec -- \
    "$TOUCH_BIN" "$create_probe" >>"$probe_log" 2>&1
  local create_status=$?
  set -e
  if [[ $create_status -eq 0 || -e "$create_probe" ]]; then
    echo 'landrun create control failed.' >>"$probe_log"
    die "landrun allowed a forbidden file creation for $label"
  fi

  local truncate_probe="$negative_dir/truncate-must-fail"
  printf 'landrun-truncate-control\n' >"$truncate_probe"
  local truncate_sha
  truncate_sha=$(sha256sum "$truncate_probe" | sed 's/[[:space:]].*$//')
  set +e
  "$LANDRUN_BIN" --best-effort --ro / --rw /dev -ldd -add-exec -- \
    "$TRUNCATE_BIN" -s 0 "$truncate_probe" >>"$probe_log" 2>&1
  local truncate_status=$?
  set -e
  if [[ $truncate_status -eq 0 || ! -s "$truncate_probe" || \
        "$(sha256sum "$truncate_probe" | sed 's/[[:space:]].*$//')" != \
          "$truncate_sha" ]]; then
    echo 'landrun truncate control failed.' >>"$probe_log"
    die "landrun allowed forbidden truncation for $label"
  fi

  local remove_probe="$negative_dir/remove-must-fail"
  printf 'landrun-remove-control\n' >"$remove_probe"
  local remove_sha
  remove_sha=$(sha256sum "$remove_probe" | sed 's/[[:space:]].*$//')
  set +e
  "$LANDRUN_BIN" --best-effort --ro / --rw /dev -ldd -add-exec -- \
    "$RM_BIN" -- "$remove_probe" >>"$probe_log" 2>&1
  local remove_status=$?
  set -e
  if [[ $remove_status -eq 0 || ! -f "$remove_probe" || \
        "$(sha256sum "$remove_probe" | sed 's/[[:space:]].*$//')" != \
          "$remove_sha" ]]; then
    echo 'landrun remove control failed.' >>"$probe_log"
    die "landrun allowed forbidden removal for $label"
  fi

  local rename_source="$negative_dir/rename-source-must-remain"
  local rename_target="$negative_dir/rename-target-must-not-exist"
  printf 'landrun-rename-control\n' >"$rename_source"
  set +e
  "$LANDRUN_BIN" --best-effort --ro / --rw /dev -ldd -add-exec -- \
    "$MV_BIN" -- "$rename_source" "$rename_target" >>"$probe_log" 2>&1
  local rename_status=$?
  set -e
  if [[ $rename_status -eq 0 || ! -f "$rename_source" || \
        -e "$rename_target" ]]; then
    echo 'landrun rename control failed.' >>"$probe_log"
    die "landrun allowed forbidden rename for $label"
  fi

  rm -rf -- "$negative_dir"
  echo 'landrun create/truncate/remove/rename controls all passed.' >>"$probe_log"
  echo 'landrun negative control refused the write as required.' >>"$probe_log"

  local probe_unit="paper-c-probe-${label//[^A-Za-z0-9]/-}-$$"
  local probe_shell=$TRANSIENT_SECURITY_ASSERTION
  probe_shell+=' && test "$(id -u)" = "$EXPECTED_UID"'
  probe_shell+=' && test "$PWD" = "$EXPECTED_CWD"'
  probe_shell+=' && test "$HOME" = "$EXPECTED_HOME"'
  probe_shell+=' && test "$ELAN_HOME" = "$EXPECTED_ELAN_HOME"'
  probe_shell+=' && test "$(realpath "$(command -v lake)")" = "$EXPECTED_LAKE_BIN"'
  probe_shell+=' && test -t 0 && test -t 1 && test -t 2'
  probe_shell+=' && echo systemd_wrapper_probe=passed'
  local probe_run=(
    "$SYSTEMD_RUN_BIN"
    "--unit=$probe_unit"
    '--property=RestrictAddressFamilies=~AF_UNIX'
    '--property=NoNewPrivileges=yes'
    '--property=RuntimeMaxSec=2min'
    --user --pty --wait --collect
    -E "PATH=$TRUSTED_PATH"
    -E "HOME=$HOME"
    -E "ELAN_HOME=$EXPECTED_ELAN_HOME"
    -E "EXPECTED_UID=$(id -u)"
    -E "EXPECTED_CWD=$project"
    -E "EXPECTED_HOME=$HOME"
    -E "EXPECTED_ELAN_HOME=$EXPECTED_ELAN_HOME"
    -E "EXPECTED_LAKE_BIN=$LAKE_BIN"
    --working-directory "$project"
    -- "${TRANSIENT_PRIVILEGE_DROP[@]}" /bin/bash -c "$probe_shell"
  )
  local probe_command
  probe_command=$(quote_command "${probe_run[@]}")
  echo "wrapper_command=$probe_command" >>"$probe_log"
  CURRENT_UNIT=$probe_unit
  set +e
  SHELL=/bin/bash "$SCRIPT_BIN" --quiet --return --flush \
    --output-limit 16M --command "$probe_command" "$probe_raw" \
    >/dev/null 2>&1
  local wrapper_status=$?
  set -e
  sed 's/\r$//' "$probe_raw" >>"$probe_log"
  cleanup_failed_unit_if_needed "$probe_unit"
  CURRENT_UNIT=
  [[ $wrapper_status -eq 0 ]] || die "systemd-run wrapper probe failed for $label"
  transcript_has_exact_line "$probe_raw" 'systemd_wrapper_probe=passed' || \
    die "systemd-run wrapper probe marker is missing for $label"
  transcript_has_exact_line "$probe_raw" 'transient_security_context=passed' || \
    die "systemd-run security-context marker is missing for $label"
  echo 'hardened_wrapper_available=true' >>"$probe_log"

  assert_checkout_unchanged "$project" "immediately before $label"
  assert_no_project_build_artifacts "$project" "immediately before $label"

  {
    echo 'mode=sandboxed Comparator verification'
    echo 'sandboxed=true'
    echo 'certifying=true'
    echo 'nanoda=disabled'
    echo 'kernels=lean'
    echo 'pty_transport=util-linux-script'
  } >"$run_log"

  local unit="paper-c-comparator-${label//[^A-Za-z0-9]/-}-$$"
  local comparator_shell=$TRANSIENT_SECURITY_ASSERTION
  comparator_shell+=' && lake env "$COMPARATOR_BIN" "$COMPARATOR_CONFIG"'
  local run=(
    "$SYSTEMD_RUN_BIN"
    "--unit=$unit"
    '--property=RestrictAddressFamilies=~AF_UNIX'
    '--property=NoNewPrivileges=yes'
  )
  if (( TIMEOUT_MINUTES > 0 )); then
    run+=("--property=RuntimeMaxSec=${TIMEOUT_MINUTES}min")
  fi
  run+=(
    --user --pty --wait --collect
    -E "PATH=$TRUSTED_PATH"
    -E "HOME=$HOME"
    -E "ELAN_HOME=$EXPECTED_ELAN_HOME"
    -E "COMPARATOR_BIN=$COMPARATOR_BIN"
    -E "COMPARATOR_CONFIG=$config_relative"
    -E "COMPARATOR_LANDRUN=$LANDRUN_BIN"
    -E "COMPARATOR_LEAN4EXPORT=$LEAN4EXPORT_BIN"
    --working-directory "$project"
    -- "${TRANSIENT_PRIVILEGE_DROP[@]}" /bin/bash -c "$comparator_shell"
  )
  local run_command
  run_command=$(quote_command "${run[@]}")
  echo "command=$run_command" >>"$run_log"

  note "starting hardened Comparator target: $label"
  CURRENT_UNIT=$unit
  set +e
  SHELL=/bin/bash "$SCRIPT_BIN" --quiet --return --flush \
    --output-limit 512M --command "$run_command" "$pty_raw" \
    >/dev/null 2>&1
  local run_status=$?
  set -e
  sed 's/\r$//' "$pty_raw" >>"$run_log"
  echo "exit_code=$run_status" >>"$run_log"
  cleanup_failed_unit_if_needed "$unit"
  CURRENT_UNIT=
  [[ $run_status -eq 0 ]] || die "Comparator target $label failed with status $run_status"
  transcript_has_exact_line "$pty_raw" 'transient_security_context=passed' || \
    die "Comparator security-context marker is missing for $label"

  assert_system_binary_state
  [[ "$(sha256sum "$COMPARATOR_BIN" | sed 's/[[:space:]].*$//')" == "$COMPARATOR_SHA" ]] || \
    die 'Comparator binary changed during the run'
  [[ "$(sha256sum "$LEAN4EXPORT_BIN" | sed 's/[[:space:]].*$//')" == "$LEAN4EXPORT_SHA" ]] || \
    die 'lean4export binary changed during the run'
  [[ "$(sha256sum "$LANDRUN_BIN" | sed 's/[[:space:]].*$//')" == "$LANDRUN_SHA" ]] || \
    die 'landrun binary changed during the run'
  assert_checkout_unchanged "$project" "after $label"

  "$NODE_BIN" "$project/scripts/assemble_comparator_evidence.mjs" \
    --environment "$environment_log" \
    --probe "$probe_log" \
    --run "$run_log" \
    --config "$config_path" \
    --config-relative "$config_relative" \
    --project "$project" \
    --transcript "$transcript" \
    --result "$result_json" \
    --require-hardened true

  "$NODE_BIN" - "$result_json" "$PAPER_COMMIT" "$config_relative" <<'NODE'
const fs = require('node:fs');
const result = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const commit = process.argv[3];
const config = process.argv[4];
if (result.status !== 'sandboxed_lean_kernel_passed' ||
    result.certifying !== true || result.sandboxed !== true ||
    result.non_root !== true || result.exit_code !== 0 ||
    result.enable_nanoda !== false ||
    JSON.stringify(result.kernels) !== JSON.stringify(['lean']) ||
    result.paper_c_commit !== commit || result.config !== config) {
  throw new Error('unexpected hardened Comparator result');
}
NODE

  mv "$partial_dir" "$final_dir"
  note "validated hardened Comparator target: $label"
}

prepare_project theorem-one-one
run_target theorem-one-one comparator/theorem_one_one.json
prepare_project infinite-finite-transfer
[[ "${PROJECT_PATHS[theorem-one-one]}" != \
    "${PROJECT_PATHS[infinite-finite-transfer]}" ]] || \
  die 'Comparator targets unexpectedly share one project checkout'
run_target infinite-finite-transfer comparator/theorem_one_one_transfer.json

SNAPSHOT_DIR="$OUTPUT_DIR/source-snapshot"
mkdir -m 700 -p "$SNAPSHOT_DIR"
SNAPSHOT_SOURCE=${PROJECT_PATHS[theorem-one-one]}
assert_checkout_unchanged "$SNAPSHOT_SOURCE" 'before source snapshot'
SNAPSHOT_FILES=(
  Challenge.lean
  Solution.lean
  ChallengeTransfer.lean
  SolutionTransfer.lean
  comparator/theorem_one_one.json
  comparator/theorem_one_one_transfer.json
  audit_config.json
  lean-toolchain
  lake-manifest.json
  lakefile.toml
  scripts/assemble_comparator_evidence.mjs
  scripts/run_hardened_comparator.sh
)
for relative_path in "${SNAPSHOT_FILES[@]}"; do
  install -D -m 600 "$SNAPSHOT_SOURCE/$relative_path" \
    "$SNAPSHOT_DIR/$relative_path"
done

"$NODE_BIN" - "$OUTPUT_DIR" "$PAPER_COMMIT" <<'NODE'
const crypto = require('node:crypto');
const fs = require('node:fs');
const path = require('node:path');
const output = process.argv[2];
const expectedCommit = process.argv[3];
const labels = ['theorem-one-one', 'infinite-finite-transfer'];
const results = labels.map(label => {
  const resultPath = path.join(output, 'evidence', label, `result-${label}.json`);
  const result = JSON.parse(fs.readFileSync(resultPath, 'utf8'));
  const transcriptPath = path.join(output, 'evidence', label, result.transcript);
  const digest = crypto.createHash('sha256').update(fs.readFileSync(transcriptPath)).digest('hex');
  if (result.status !== 'sandboxed_lean_kernel_passed' ||
      result.certifying !== true || result.sandboxed !== true ||
      result.non_root !== true || result.exit_code !== 0 ||
      result.enable_nanoda !== false ||
      JSON.stringify(result.kernels) !== JSON.stringify(['lean']) ||
      result.paper_c_commit !== expectedCommit ||
      result.transcript_sha256 !== digest) {
    throw new Error(`${label}: final result validation failed`);
  }
  return result;
});
if (results[0].config === results[1].config ||
    results[0].comparator_fileset_digest_sha256 !== results[1].comparator_fileset_digest_sha256 ||
    JSON.stringify(results[0].tool_commits) !== JSON.stringify(results[1].tool_commits) ||
    JSON.stringify(results[0].manuscript_sha256) !== JSON.stringify(results[1].manuscript_sha256)) {
  throw new Error('the two Comparator results are not independent, compatible targets');
}
const summary = {
  status: 'two_hardened_comparator_targets_passed',
  paper_c_commit: expectedCommit,
  certifying: true,
  sandboxed: true,
  kernels: ['lean'],
  enable_nanoda: false,
  pty_transport: 'util-linux-script around systemd-run --user --pty',
  comparator_fileset_digest_sha256: results[0].comparator_fileset_digest_sha256,
  tool_commits: results[0].tool_commits,
  manuscript_sha256: results[0].manuscript_sha256,
  results,
  qualification: 'Lean-kernel Comparator evidence; not a dual-kernel result or a general host-security certification.',
};
fs.writeFileSync(path.join(output, 'summary.json'), `${JSON.stringify(summary, null, 2)}\n`);
NODE

(
  cd "$OUTPUT_DIR"
  find . -type f ! -name SHA256SUMS ! -name SUCCESS -print0 | \
    sort -z | xargs -0 sha256sum >SHA256SUMS
)
printf 'Both hardened Comparator targets validated at %s.\n' "$PAPER_COMMIT" \
  >"$OUTPUT_DIR/SUCCESS"

EVIDENCE_ARCHIVE="$OUTPUT_DIR.tar.zst"
EVIDENCE_ARCHIVE_PARTIAL="$EVIDENCE_ARCHIVE.partial"
EVIDENCE_CHECKSUM="$EVIDENCE_ARCHIVE.sha256"
EVIDENCE_CHECKSUM_PARTIAL="$EVIDENCE_CHECKSUM.partial"
tar --zstd -C "$(dirname "$OUTPUT_DIR")" -cf "$EVIDENCE_ARCHIVE_PARTIAL" \
  "$(basename "$OUTPUT_DIR")"
EVIDENCE_ARCHIVE_SHA=$(sha256sum "$EVIDENCE_ARCHIVE_PARTIAL" | \
  sed 's/[[:space:]].*$//')
printf '%s  %s\n' "$EVIDENCE_ARCHIVE_SHA" "$(basename "$EVIDENCE_ARCHIVE")" \
  >"$EVIDENCE_CHECKSUM_PARTIAL"
mv "$EVIDENCE_ARCHIVE_PARTIAL" "$EVIDENCE_ARCHIVE"
mv "$EVIDENCE_CHECKSUM_PARTIAL" "$EVIDENCE_CHECKSUM"
RUN_SUCCEEDED=true

note "SUCCESS: both hardened Comparator targets passed"
note "evidence: $OUTPUT_DIR"
note "upload bundle: $EVIDENCE_ARCHIVE"
note "bundle checksum: $EVIDENCE_ARCHIVE.sha256"
note 'This is a Lean-kernel result only; nanoda remains disabled.'
