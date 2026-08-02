#!/usr/bin/env node

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';

const argumentsMap = new Map();
for (let index = 2; index < process.argv.length; index += 2) {
  const key = process.argv[index];
  const value = process.argv[index + 1];
  if (!key?.startsWith('--') || value === undefined) {
    throw new Error('arguments must be --key value pairs');
  }
  argumentsMap.set(key.slice(2), value);
}

const requiredArgument = key => {
  const value = argumentsMap.get(key);
  if (!value) {
    throw new Error(`missing --${key}`);
  }
  return value;
};

const environmentPath = requiredArgument('environment');
const probePath = requiredArgument('probe');
const runPath = requiredArgument('run');
const configPath = requiredArgument('config');
const configRelativePath = requiredArgument('config-relative');
const projectRoot = requiredArgument('project');
const transcriptPath = requiredArgument('transcript');
const resultPath = requiredArgument('result');
const requireHardened = requiredArgument('require-hardened') === 'true';

for (const inputPath of [environmentPath, probePath, runPath, configPath]) {
  if (!fs.existsSync(inputPath)) {
    throw new Error(`Comparator evidence input is missing: ${inputPath}`);
  }
}

const chunks = [environmentPath, probePath, runPath].map(inputPath =>
  fs.readFileSync(inputPath, 'utf8').trimEnd(),
);
const transcript = `${chunks.join('\n')}\n`;
fs.writeFileSync(transcriptPath, transcript);

if (transcript.includes('\u0000')) {
  throw new Error('Comparator transcript contains a NUL byte');
}
const lines = transcript.split(/\r?\n/);
const field = name => {
  const prefix = `${name}=`;
  const values = lines
    .filter(line => line.startsWith(prefix))
    .map(line => line.slice(prefix.length));
  if (values.length !== 1 || values[0].length === 0) {
    throw new Error(`expected exactly one nonempty ${name} field`);
  }
  return values[0];
};
const exactLine = expected => {
  if (lines.filter(line => line === expected).length !== 1) {
    throw new Error(`expected exactly one transcript marker: ${expected}`);
  }
};

const auditConfig = JSON.parse(
  fs.readFileSync(path.join(projectRoot, 'audit_config.json'), 'utf8'),
);
const comparatorMetadata = auditConfig.verification.comparator;
const comparatorConfig = JSON.parse(fs.readFileSync(configPath, 'utf8'));
if (comparatorConfig.enable_nanoda !== false) {
  throw new Error('release evidence currently requires enable_nanoda=false');
}

const configSha256 = crypto
  .createHash('sha256')
  .update(fs.readFileSync(configPath))
  .digest('hex');
exactLine(`${configSha256}  ${configRelativePath}`);

const binaryCompare = (left, right) =>
  Buffer.from(left).compare(Buffer.from(right));
const filesetHash = crypto.createHash('sha256');
for (const relativePath of [...comparatorMetadata.fileset].sort(binaryCompare)) {
  filesetHash.update(relativePath);
  filesetHash.update('\0');
  filesetHash.update(fs.readFileSync(path.join(projectRoot, relativePath)));
  filesetHash.update('\0');
}
const filesetSha256 = filesetHash.digest('hex');

const mode = field('mode');
const sandboxed = field('sandboxed') === 'true';
const expectedMode = sandboxed
  ? 'sandboxed Comparator verification'
  : 'unsandboxed Comparator semantic smoke test (non-certifying)';
if (mode !== expectedMode) {
  throw new Error(`unexpected Comparator mode: ${mode}`);
}
if (field('certifying') !== String(sandboxed)) {
  throw new Error('certifying and sandboxed fields disagree');
}
if (requireHardened && !sandboxed) {
  throw new Error('strict release mode did not produce sandboxed evidence');
}
if (sandboxed) {
  if (field('hardened_wrapper_available') !== 'true') {
    throw new Error('sandboxed run lacks a successful hardening probe');
  }
  if (field('launcher_no_new_privs') !== '1' ||
      field('transient_no_new_privs_required') !== 'true' ||
      field('transient_zero_capabilities_required') !== 'true') {
    throw new Error('sandboxed run lacks the required capability context');
  }
  if (lines.filter(
    line => line === 'transient_security_context=passed',
  ).length !== 2) {
    throw new Error('sandboxed run lacks two security-context markers');
  }
  if (!transcript.includes('landrun negative control refused the write as required.')) {
    throw new Error('sandboxed run lacks the landrun negative control marker');
  }
  if (transcript.includes('THIS IS NOT REAL LANDRUN')) {
    throw new Error('sandboxed transcript contains the fake-landrun marker');
  }

  const systemBinaryTargets = new Map([
    ['git', ['/usr/bin/git', ['/usr/bin/git']]],
    ['node', ['/usr/bin/node', ['/usr/bin/node', '/usr/bin/nodejs']]],
    ['script', ['/usr/bin/script', ['/usr/bin/script']]],
    ['systemd_run', ['/usr/bin/systemd-run', ['/usr/bin/systemd-run']]],
    ['systemctl', ['/usr/bin/systemctl', ['/usr/bin/systemctl']]],
    ['sha256sum', [
      '/usr/bin/sha256sum',
      [
        '/usr/bin/sha256sum',
        '/usr/bin/gnusha256sum',
        '/usr/lib/cargo/bin/coreutils/sha256sum',
      ],
    ]],
    ['truncate', [
      '/usr/bin/truncate',
      [
        '/usr/bin/truncate',
        '/usr/bin/gnutruncate',
        '/usr/lib/cargo/bin/coreutils/truncate',
      ],
    ]],
    ['touch', [
      '/usr/bin/touch',
      [
        '/usr/bin/touch',
        '/usr/bin/gnutouch',
        '/usr/lib/cargo/bin/coreutils/touch',
      ],
    ]],
    ['rm', [
      '/usr/bin/rm',
      ['/usr/bin/rm', '/usr/bin/gnurm', '/usr/lib/cargo/bin/coreutils/rm'],
    ]],
    ['mv', [
      '/usr/bin/mv',
      ['/usr/bin/mv', '/usr/bin/gnumv', '/usr/lib/cargo/bin/coreutils/mv'],
    ]],
  ]);
  for (const [name, [expectedPath, allowedTargets]] of systemBinaryTargets) {
    if (field(`system_binary_${name}_path`) !== expectedPath) {
      throw new Error(`unexpected audited system path for ${name}`);
    }
    if (!allowedTargets.includes(field(`system_binary_${name}_resolved`))) {
      throw new Error(`unexpected audited system target for ${name}`);
    }
    if (!/^[0-9a-f]{64}$/.test(field(`system_binary_${name}_sha256`))) {
      throw new Error(`invalid audited system digest for ${name}`);
    }
  }
}

if (field('config') !== configRelativePath) {
  throw new Error('Comparator configuration path mismatch');
}
if (field('comparator_fileset_digest_sha256') !== filesetSha256) {
  throw new Error('Comparator fileset digest mismatch');
}
if (field('tracked_worktree_dirty_count') !== '0') {
  throw new Error('Comparator source checkout was dirty');
}
if (field('preexisting_project_olean_count') !== '0') {
  throw new Error('Comparator checkout contained a pre-existing .olean');
}
if (field('ld_preload') !== 'unset' || field('non_root') !== 'true') {
  throw new Error('Comparator evidence violates the process trust boundary');
}
if (field('nanoda') !== 'disabled' || field('kernels') !== 'lean') {
  throw new Error('Comparator kernel metadata is inaccurate');
}
if (field('exit_code') !== '0') {
  throw new Error('Comparator did not exit with status 0');
}

const expectedCommits = new Map([
  ['lean_commit', auditConfig.verification.toolchain.lean.commit],
  ['mathlib_commit', auditConfig.verification.toolchain.mathlib.commit],
  ['comparator_commit', comparatorMetadata.tools.comparator.commit],
  ['lean4export_commit', comparatorMetadata.tools.lean4export.commit],
  ['landrun_commit', comparatorMetadata.tools.landrun.commit],
]);
for (const [name, expected] of expectedCommits) {
  if (field(name) !== expected) {
    throw new Error(`${name} does not match audit_config.json`);
  }
}

const paperCommit = field('paper_c_commit');
if (!/^[0-9a-f]{40}$/.test(paperCommit)) {
  throw new Error('invalid Paper C commit in Comparator transcript');
}
exactLine('Lean default kernel accepts the solution');
exactLine('Your solution is okay!');

const status = sandboxed
  ? 'sandboxed_lean_kernel_passed'
  : 'unsandboxed_semantic_smoke_passed';
const result = {
  status,
  certifying: sandboxed,
  sandboxed,
  non_root: true,
  kernels: ['lean'],
  enable_nanoda: false,
  exit_code: 0,
  config: configRelativePath,
  configuration_sha256: configSha256,
  comparator_fileset_digest_sha256: filesetSha256,
  paper_c_commit: paperCommit,
  transcript: path.basename(transcriptPath),
  transcript_sha256: crypto
    .createHash('sha256')
    .update(fs.readFileSync(transcriptPath))
    .digest('hex'),
};
fs.writeFileSync(resultPath, `${JSON.stringify(result, null, 2)}\n`);
process.stdout.write(
  `Comparator evidence validated: ${status}; ${result.transcript_sha256}\n`,
);
