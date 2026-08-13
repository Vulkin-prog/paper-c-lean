#!/usr/bin/env node
import crypto from 'node:crypto';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const sourceRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const temporaryRoot = fs.mkdtempSync(path.join(os.tmpdir(), 'paper-c-release-binding-test-'));
const repository = path.join(temporaryRoot, 'repository');
const archive = path.join(temporaryRoot, 'hardened-public.tar.zst');
const evidenceRelative = 'release_evidence/v0.48.1';
const resultSpecs = new Map([
  ['result-theorem-one-one.json', 'comparator/theorem_one_one.json'],
  ['result-infinite-finite-transfer.json', 'comparator/theorem_one_one_transfer.json'],
]);
const fileset = [
  'Challenge.lean',
  'Solution.lean',
  'ChallengeTransfer.lean',
  'SolutionTransfer.lean',
  'comparator/theorem_one_one.json',
  'comparator/theorem_one_one_transfer.json',
];

function run(command, args, options = {}) {
  const result = spawnSync(command, args, {
    cwd: options.cwd ?? repository,
    encoding: 'utf8',
  });
  const succeeds = result.status === 0;
  if (options.expectFailure ? succeeds : !succeeds) {
    throw new Error(
      `${command} ${args.join(' ')} ${options.expectFailure ? 'unexpectedly passed' : 'failed'}\n` +
      `stdout:\n${result.stdout}\nstderr:\n${result.stderr}`,
    );
  }
  return result;
}

function write(relative, contents) {
  const target = path.join(repository, relative);
  fs.mkdirSync(path.dirname(target), { recursive: true });
  fs.writeFileSync(target, contents);
}

function sha256(contents) {
  return crypto.createHash('sha256').update(contents).digest('hex');
}

function fileSha256(relative) {
  return sha256(fs.readFileSync(path.join(repository, relative)));
}

function filesetSha256() {
  const compare = (left, right) => Buffer.from(left).compare(Buffer.from(right));
  const hash = crypto.createHash('sha256');
  for (const relative of [...fileset].sort(compare)) {
    hash.update(relative);
    hash.update('\0');
    hash.update(fs.readFileSync(path.join(repository, relative)));
    hash.update('\0');
  }
  return hash.digest('hex');
}

function writeResults(sourceCommit) {
  const englishSha256 = fileSha256('paper_C_complete_v09_en.pdf');
  const frenchSha256 = fileSha256('paper_C_complete_v09.pdf');
  const digest = filesetSha256();
  for (const [name, config] of resultSpecs) {
    const result = {
      status: 'sandboxed_lean_kernel_passed',
      certifying: true,
      sandboxed: true,
      non_root: true,
      kernels: ['lean'],
      enable_nanoda: false,
      exit_code: 0,
      config,
      configuration_sha256: fileSha256(config),
      comparator_fileset_digest_sha256: digest,
      paper_c_commit: sourceCommit,
      manuscript_sha256: {
        target_pdf: englishSha256,
        source_pdf_fr: frenchSha256,
      },
    };
    write(`${evidenceRelative}/${name}`, `${JSON.stringify(result, null, 2)}\n`);
  }
}

function createBinding() {
  return run(process.execPath, [
    'scripts/create_release_binding.mjs',
    '--evidence-dir', evidenceRelative,
    '--archive', archive,
    '--output', `${evidenceRelative}/release-binding.json`,
  ]);
}

function verifyBinding(expectedArchiveSha256, expectFailure = false) {
  return run(process.execPath, [
    'scripts/verify_release_binding.mjs',
    '--binding', `${evidenceRelative}/release-binding.json`,
    '--evidence-dir', evidenceRelative,
    '--expected-archive-sha256', expectedArchiveSha256,
  ], { expectFailure });
}

try {
  fs.mkdirSync(repository, { recursive: true });
  fs.mkdirSync(path.join(repository, 'scripts'), { recursive: true });
  for (const script of ['create_release_binding.mjs', 'verify_release_binding.mjs']) {
    fs.copyFileSync(path.join(sourceRoot, 'scripts', script), path.join(repository, 'scripts', script));
  }

  write('paper_C_complete_v09_en.pdf', Buffer.from('synthetic English PDF bytes\n'));
  write('paper_C_complete_v09.pdf', Buffer.from('synthetic French PDF bytes\n'));
  for (const relative of fileset) write(relative, `synthetic source for ${relative}\n`);
  const auditConfig = {
    target_pdf: { sha256: fileSha256('paper_C_complete_v09_en.pdf') },
    source_pdf_fr: { sha256: fileSha256('paper_C_complete_v09.pdf') },
    verification: { comparator: { fileset } },
  };
  write('audit_config.json', `${JSON.stringify(auditConfig, null, 2)}\n`);
  fs.writeFileSync(archive, 'synthetic privacy-minimized hardened archive\n');
  const archiveSha256 = sha256(fs.readFileSync(archive));

  run('git', ['init', '-q']);
  run('git', ['config', 'user.name', 'Release Binding Self-Test']);
  run('git', ['config', 'user.email', 'release-binding-self-test@example.invalid']);
  run('git', ['add', '.']);
  run('git', ['commit', '-q', '-m', 'source Q']);
  const sourceCommit = run('git', ['rev-parse', 'HEAD']).stdout.trim();

  writeResults(sourceCommit);
  createBinding();
  const binding = JSON.parse(
    fs.readFileSync(path.join(repository, evidenceRelative, 'release-binding.json'), 'utf8'),
  );
  if (binding.paper_c_commit !== sourceCommit) {
    throw new Error('created binding did not carry source commit Q');
  }
  run('git', ['add', evidenceRelative]);
  run('git', ['commit', '-q', '-m', 'packaging R']);
  verifyBinding(archiveSha256);

  run('git', ['checkout', '-q', '-b', 'negative', sourceCommit]);
  writeResults(sourceCommit);
  write('UNRELATED.txt', 'must not enter packaging commit R\n');
  const rejectedCreate = run(process.execPath, [
    'scripts/create_release_binding.mjs',
    '--evidence-dir', evidenceRelative,
    '--archive', archive,
    '--output', `${evidenceRelative}/release-binding.json`,
  ], { expectFailure: true });
  if (!rejectedCreate.stderr.includes('dirty outside')) {
    throw new Error('creator did not explain its fail-closed dirty-worktree rejection');
  }
  fs.rmSync(path.join(repository, 'UNRELATED.txt'));
  createBinding();
  write('UNRELATED.txt', 'must make verifier reject packaging commit R\n');
  run('git', ['add', evidenceRelative, 'UNRELATED.txt']);
  run('git', ['commit', '-q', '-m', 'invalid packaging R']);
  const rejectedVerify = verifyBinding(archiveSha256, true);
  if (!rejectedVerify.stderr.includes('outside')) {
    throw new Error('verifier did not explain its restricted-diff rejection');
  }

  run('git', ['checkout', '-q', '-b', 'pdf-negative', sourceCommit]);
  writeResults(sourceCommit);
  createBinding();
  run('git', ['add', evidenceRelative]);
  run('git', ['commit', '-q', '-m', 'packaging R before PDF mutation']);
  write('paper_C_complete_v09_en.pdf', Buffer.from('mutated English PDF bytes\n'));
  run('git', ['add', 'paper_C_complete_v09_en.pdf']);
  run('git', ['commit', '-q', '--amend', '--no-edit']);
  const rejectedPdf = verifyBinding(archiveSha256, true);
  if (!rejectedPdf.stderr.includes('paper_C_complete_v09_en.pdf differs between Q and R')) {
    throw new Error('verifier did not exercise its PDF identity rejection');
  }

  run('git', ['checkout', '-q', '-b', 'fileset-negative', sourceCommit]);
  writeResults(sourceCommit);
  createBinding();
  run('git', ['add', evidenceRelative]);
  run('git', ['commit', '-q', '-m', 'packaging R before fileset mutation']);
  write('Challenge.lean', 'mutated Comparator source\n');
  run('git', ['add', 'Challenge.lean']);
  run('git', ['commit', '-q', '--amend', '--no-edit']);
  const rejectedFileset = verifyBinding(archiveSha256, true);
  if (!rejectedFileset.stderr.includes('Comparator fileset differs')) {
    throw new Error('verifier did not exercise its Comparator fileset rejection');
  }

  run('git', ['checkout', '-q', '-b', 'merge-side', sourceCommit]);
  write('MERGE_SIDE.txt', 'second-parent history\n');
  run('git', ['add', 'MERGE_SIDE.txt']);
  run('git', ['commit', '-q', '-m', 'merge side']);
  const mergeSide = run('git', ['rev-parse', 'HEAD']).stdout.trim();
  run('git', ['checkout', '-q', '-b', 'parent-negative', sourceCommit]);
  writeResults(sourceCommit);
  createBinding();
  run('git', ['add', evidenceRelative]);
  run('git', ['commit', '-q', '-m', 'packaging candidate']);
  const packagingTree = run('git', ['rev-parse', 'HEAD^{tree}']).stdout.trim();
  const mergeCommit = run('git', [
    'commit-tree', packagingTree,
    '-p', sourceCommit,
    '-p', mergeSide,
    '-m', 'invalid merge packaging R',
  ]).stdout.trim();
  run('git', ['reset', '-q', '--hard', mergeCommit]);
  const rejectedParent = verifyBinding(archiveSha256, true);
  if (!rejectedParent.stderr.includes('exactly one parent')) {
    throw new Error('verifier did not explain its merge-parent rejection');
  }

  console.log('release-binding two-commit protocol self-test passed');
} finally {
  fs.rmSync(temporaryRoot, { recursive: true, force: true });
}
