#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

const root = process.cwd();
const challengeFiles = ['Challenge.lean', 'ChallengeTransfer.lean'];
const requiredSolutionFiles = ['Solution.lean', 'SolutionTransfer.lean'];
const hardenedRunnerFile = 'scripts/run_hardened_comparator.sh';
const evidenceAssemblerFile = 'scripts/assemble_comparator_evidence.mjs';

function fail(message) {
  console.error(`Comparator source guard: ${message}`);
  process.exitCode = 1;
}

function readRequired(relativePath) {
  const absolutePath = path.join(root, relativePath);
  if (!fs.existsSync(absolutePath)) {
    fail(`required file is missing: ${relativePath}`);
    return null;
  }
  return fs.readFileSync(absolutePath, 'utf8');
}

function importsOf(source) {
  return [...source.matchAll(/^\s*import\s+(\S+)/gm)].map(match => match[1]);
}

function countMatches(source, pattern) {
  return [...source.matchAll(pattern)].length;
}

function walkLeanFiles(relativeDirectory) {
  const absoluteDirectory = path.join(root, relativeDirectory);
  if (!fs.existsSync(absoluteDirectory)) return [];

  const files = [];
  const pending = [absoluteDirectory];
  while (pending.length > 0) {
    const directory = pending.pop();
    for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
      const absolutePath = path.join(directory, entry.name);
      if (entry.isDirectory()) {
        pending.push(absolutePath);
      } else if (entry.isFile() && entry.name.endsWith('.lean')) {
        files.push(path.relative(root, absolutePath));
      }
    }
  }
  return files;
}

const challengeSources = new Map(
  challengeFiles.map(file => [file, readRequired(file)]),
);

const challenge = challengeSources.get('Challenge.lean');
if (challenge !== null) {
  const imports = importsOf(challenge);
  if (imports.length === 0) {
    fail('Challenge.lean must import at least one Mathlib module.');
  }
  for (const moduleName of imports) {
    if (moduleName !== 'Mathlib' && !moduleName.startsWith('Mathlib.')) {
      fail(`Challenge.lean has a non-Mathlib import: ${moduleName}`);
    }
  }
}

const challengeTransfer = challengeSources.get('ChallengeTransfer.lean');
if (challengeTransfer !== null) {
  const imports = importsOf(challengeTransfer);
  if (imports.length !== 1 || imports[0] !== 'Challenge') {
    fail(
      'ChallengeTransfer.lean must import exactly Challenge; ' +
      `observed imports: ${imports.length === 0 ? '(none)' : imports.join(', ')}`,
    );
  }
}

const challengeForbidden =
  /(^|[^A-Za-z0-9_])(axiom|admit|opaque|unsafe|partial|native_decide|definition_names)(?=[^A-Za-z0-9_]|$)/g;
for (const [file, source] of challengeSources) {
  if (source === null) continue;

  const bySorryCount = countMatches(source, /\bby\s+sorry\b/g);
  const totalSorryCount = countMatches(source, /\bsorry\b/g);
  if (bySorryCount !== 1 || totalSorryCount !== 1) {
    fail(
      `${file} must contain exactly one 'by sorry' and no other sorry ` +
      `(by sorry: ${bySorryCount}; total sorry: ${totalSorryCount}).`,
    );
  }

  const forbidden = [...source.matchAll(challengeForbidden)].map(match => match[2]);
  if (forbidden.length > 0) {
    fail(`${file} contains forbidden token(s): ${[...new Set(forbidden)].join(', ')}`);
  }
}

const rootSolutionFiles = fs
  .readdirSync(root, { withFileTypes: true })
  .filter(entry => entry.isFile() && /^Solution.*\.lean$/.test(entry.name))
  .map(entry => entry.name);
const solutionFiles = [
  ...rootSolutionFiles,
  ...walkLeanFiles('ComparatorSupport'),
  ...walkLeanFiles(path.join('PaperC', 'ComparatorSupport')),
].sort();

for (const file of requiredSolutionFiles) {
  if (!solutionFiles.includes(file)) {
    fail(`required file is missing: ${file}`);
  }
}

const solutionForbidden =
  /(^|[^A-Za-z0-9_])(sorry|axiom|admit|opaque|unsafe|partial|native_decide|definition_names)(?=[^A-Za-z0-9_]|$)/g;
for (const file of solutionFiles) {
  const source = fs.readFileSync(path.join(root, file), 'utf8');
  const forbidden = [...source.matchAll(solutionForbidden)].map(match => match[2]);
  if (forbidden.length > 0) {
    fail(`${file} contains forbidden token(s): ${[...new Set(forbidden)].join(', ')}`);
  }
  if (/^\s*import\s+Challenge(?:\s|\.|$)/m.test(source)) {
    fail(`${file} imports a Challenge module.`);
  }
}

const hardenedRunner = readRequired(hardenedRunnerFile);
if (hardenedRunner !== null) {
  const lexicalSystemCommands = new Map([
    ['GIT_BIN', 'git'],
    ['NODE_BIN', 'node'],
    ['SCRIPT_BIN', 'script'],
    ['SETPRIV_BIN', 'setpriv'],
    ['SYSTEMD_RUN_BIN', 'systemd-run'],
    ['SYSTEMCTL_BIN', 'systemctl'],
    ['SHA256SUM_BIN', 'sha256sum'],
    ['TRUNCATE_BIN', 'truncate'],
    ['TOUCH_BIN', 'touch'],
    ['RM_BIN', 'rm'],
    ['MV_BIN', 'mv'],
  ]);
  for (const [variable, command] of lexicalSystemCommands) {
    const expected = `${variable}=$(command -v ${command})`;
    const assignment = new RegExp(
      `^${variable}=\\$\\(command -v ${command.replace('-', '\\-')}\\)$`,
      'm',
    );
    if (!assignment.test(hardenedRunner)) {
      fail(
        `${hardenedRunnerFile} must retain the lexical system path: ${expected}`,
      );
    }
  }
  if (!hardenedRunner.includes(
        'export PATH="/usr/bin:/bin:$HOME/.elan/bin"',
      ) || !hardenedRunner.includes(
        'TRUSTED_BASE_PATH="/usr/bin:/bin:$ELAN_BIN_DIR"',
      )) {
    fail(
      `${hardenedRunnerFile} must put audited system paths before Elan.`,
    );
  }
  for (const target of [
    '/usr/bin/gnusha256sum',
    '/usr/lib/cargo/bin/coreutils/sha256sum',
    '/usr/bin/gnutruncate',
    '/usr/lib/cargo/bin/coreutils/truncate',
    '/usr/bin/gnutouch',
    '/usr/lib/cargo/bin/coreutils/touch',
    '/usr/bin/gnurm',
    '/usr/bin/gnumv',
  ]) {
    if (!hardenedRunner.includes(target)) {
      fail(
        `${hardenedRunnerFile} is missing approved Ubuntu provider target: ` +
        target,
      );
    }
  }
  if (!hardenedRunner.includes('resolved=$(realpath "$actual")')) {
    fail(`${hardenedRunnerFile} does not resolve system-binary targets.`);
  }
  if (!hardenedRunner.includes("owner=$(stat -Lc '%u' \"$resolved\")") ||
      !hardenedRunner.includes("mode=$(stat -Lc '%a' \"$resolved\")")) {
    fail(
      `${hardenedRunnerFile} does not check ownership and mode on the ` +
      'resolved system-binary target.',
    );
  }
  if (!hardenedRunner.includes("owner=$(stat -Lc '%u' \"$directory\")") ||
      !hardenedRunner.includes("mode=$(stat -Lc '%a' \"$directory\")")) {
    fail(
      `${hardenedRunnerFile} does not check the resolved target's parent ` +
      'directory chain.',
    );
  }
  if (!/^INITIAL_FUNCTIONS=\$\(builtin declare -Fx\)$/m.test(hardenedRunner)) {
    fail(`${hardenedRunnerFile} does not reject inherited Bash functions.`);
  }
  const noNewPrivilegesProperties = hardenedRunner.match(
    /'--property=NoNewPrivileges=yes'/g,
  ) ?? [];
  if (noNewPrivilegesProperties.length !== 4 ||
      !hardenedRunner.includes('transient_security_context=passed')) {
    fail(
      `${hardenedRunnerFile} does not enforce the expected transient ` +
      'NoNewPrivileges security contexts.',
    );
  }
  const transientPrivilegeDropUses = hardenedRunner.match(
    /"\$\{TRANSIENT_PRIVILEGE_DROP\[@\]\}"/g,
  ) ?? [];
  if (transientPrivilegeDropUses.length !== 4 ||
      !hardenedRunner.includes('TRANSIENT_PRIVILEGE_DROP=(') ||
      !hardenedRunner.includes(
        'verify_system_binary "$SETPRIV_BIN" /usr/bin/setpriv /usr/bin/setpriv',
      ) ||
      !hardenedRunner.includes('  "$SETPRIV_BIN"\n') ||
      !hardenedRunner.includes('  --inh-caps=-all\n') ||
      !hardenedRunner.includes('  --ambient-caps=-all\n') ||
      !hardenedRunner.includes('  --no-new-privs\n')) {
    fail(
      `${hardenedRunnerFile} does not clean capabilities inside all four ` +
      'systemd user-manager payloads.',
    );
  }
  if (!hardenedRunner.includes('SYSTEMD_PREFLIGHT_LOG=$(mktemp ') ||
      !hardenedRunner.includes(
        "note 'systemd --user PTY wrapper diagnostic follows:'",
      )) {
    fail(`${hardenedRunnerFile} suppresses initial systemd probe diagnostics.`);
  }
  const exactTransientMarkerChecks = hardenedRunner.match(
    /grep -Fqx 'transient_security_context=passed'/g,
  ) ?? [];
  const terminalTitleSetting = hardenedRunner.indexOf(
    'export SYSTEMD_ADJUST_TERMINAL_TITLE=0',
  );
  const callerEnvironmentCheck = hardenedRunner.indexOf(
    'LEAN_SYSROOT LEAN_OPTS MATHLIB_CACHE_URL NODE_OPTIONS \\\n' +
    '  SYSTEMD_ADJUST_TERMINAL_TITLE TAR_OPTIONS',
  );
  const managerEnvironmentCheck = hardenedRunner.indexOf(
    'MATHLIB_CACHE_URL NODE_OPTIONS SYSTEMD_ADJUST_TERMINAL_TITLE TAR_OPTIONS',
  );
  const systemdPreflight = hardenedRunner.indexOf('SYSTEMD_PREFLIGHT=(');
  if (terminalTitleSetting < 0 ||
      callerEnvironmentCheck < 0 ||
      managerEnvironmentCheck < 0 ||
      systemdPreflight < 0 ||
      terminalTitleSetting < callerEnvironmentCheck ||
      terminalTitleSetting < managerEnvironmentCheck ||
      terminalTitleSetting > systemdPreflight ||
      exactTransientMarkerChecks.length !== 3 ||
      !hardenedRunner.includes("echo 'systemd_adjust_terminal_title=0'")) {
    fail(
      `${hardenedRunnerFile} does not disable systemd PTY title decoration ` +
      'before performing exact security-marker checks.',
    );
  }
  const leanToolchainEnsure = hardenedRunner.indexOf(
    '"$ELAN_BIN" run --install "$PROJECT_TOOLCHAIN" lean --version',
  );
  const leanToolchainVerify = hardenedRunner.indexOf(
    'LEAN_VERSION_OUTPUT=$(probe_lean_toolchain 2>&1)',
  );
  const leanToolchainEnsures = hardenedRunner.match(
    /"\$ELAN_BIN" run --install "\$PROJECT_TOOLCHAIN" lean --version/g,
  ) ?? [];
  if (!hardenedRunner.includes('probe_lean_toolchain() {') ||
      leanToolchainEnsure < 0 || leanToolchainVerify < leanToolchainEnsure ||
      leanToolchainEnsures.length !== 1 ||
      hardenedRunner.includes('already installed') ||
      hardenedRunner.includes('toolchain install "$PROJECT_TOOLCHAIN"') ||
      !hardenedRunner.includes(
        '"$ELAN_BIN" run "$PROJECT_TOOLCHAIN" lean --version',
      ) ||
      !hardenedRunner.includes(
        'LEAN_VERSION_OUTPUT=$(probe_lean_toolchain 2>&1)',
      ) ||
      !hardenedRunner.includes('LEAN_VERSION_STATUS=$?') ||
      !hardenedRunner.includes('if [[ $LEAN_VERSION_STATUS -ne 0 ]]') ||
      !hardenedRunner.includes(
        'LEAN_VERSION_COMMIT=${BASH_REMATCH[1]}',
      ) ||
      !hardenedRunner.includes(
        '[[ "$LEAN_VERSION_COMMIT" == "$LEAN_COMMIT" ]]',
      )) {
    fail(
      `${hardenedRunnerFile} does not idempotently ensure and exactly ` +
      'validate the pinned Lean toolchain.',
    );
  }
  if (hardenedRunner.includes('/usr/bin/*|/usr/lib/cargo/bin/coreutils/*)')) {
    fail(`${hardenedRunnerFile} contains an over-broad system target pattern.`);
  }
}

const evidenceAssembler = readRequired(evidenceAssemblerFile);
if (evidenceAssembler !== null) {
  for (const requiredField of [
    'launcher_no_new_privs',
    'transient_no_new_privs_required',
    'transient_zero_capabilities_required',
    'transient_capability_drop_method',
    'systemd_adjust_terminal_title',
    'transient_security_context=passed',
    'system_binary_${name}_path',
    'system_binary_${name}_resolved',
    'system_binary_${name}_sha256',
  ]) {
    if (!evidenceAssembler.includes(requiredField)) {
      fail(
        `${evidenceAssemblerFile} does not enforce hardened evidence field: ` +
        requiredField,
      );
    }
  }
}

if (process.exitCode) process.exit(process.exitCode);
console.log(
  `Comparator source guard passed (${challengeFiles.length} challenges, ` +
  `${solutionFiles.length} solutions/support modules).`,
);
