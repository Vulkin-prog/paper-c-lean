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
let archive;
const evidenceRelative = 'release_evidence/v0.48.1';
const resultSpecs = new Map([
  ['result-theorem-one-one.json', {
    config: 'comparator/theorem_one_one.json', challenge: 'Challenge.lean',
    solution: 'Solution.lean', transcript: 'comparator-theorem-one-one.txt',
    theorem: 'paper_c_theorem_one_one_finite_cylinder',
  }],
  ['result-infinite-finite-transfer.json', {
    config: 'comparator/theorem_one_one_transfer.json', challenge: 'ChallengeTransfer.lean',
    solution: 'SolutionTransfer.lean', transcript: 'comparator-infinite-finite-transfer.txt',
    theorem: 'paper_c_theorem_one_one_infinite_finite_law_identity',
  }],
]);
const permittedAxioms = ['propext', 'Quot.sound', 'Classical.choice'];
const toolCommits = {
  lean: '1111111111111111111111111111111111111111',
  mathlib: '2222222222222222222222222222222222222222',
  comparator: '3333333333333333333333333333333333333333',
  lean4export: '4444444444444444444444444444444444444444',
  landrun: '5555555555555555555555555555555555555555',
};
const verifierStub = `#!/usr/bin/env python3
import argparse
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--source', required=True)
parser.add_argument('--archive', required=True)
parser.add_argument('--repository', required=True)
parser.add_argument('--packaging-evidence-dir', required=True)
parser.add_argument('--result-hashes-output', required=True)
args = parser.parse_args()
for value in (args.source, args.archive, args.repository, args.packaging_evidence_dir):
    if not Path(value).exists():
        raise SystemExit(f'missing required test input: {value}')
import hashlib, json
evidence = Path(args.packaging_evidence_dir)
hashes = {}
for name in ('result-theorem-one-one.json', 'result-infinite-finite-transfer.json'):
    hashes[name] = hashlib.sha256((evidence / name).read_bytes()).hexdigest()
archive_bytes = Path(args.archive).read_bytes()
commit = Path(args.archive).name.removeprefix('paper-c-hardened-public-').removesuffix('.tar.zst')
Path(args.result_hashes_output).write_text(json.dumps({
    'schema': 1,
    'paper_c_commit': commit,
    'archive_sha256': hashlib.sha256(archive_bytes).hexdigest(),
    'result_sha256': hashes,
}, indent=2) + '\\n')
print('synthetic committed verifier invoked with complete binding arguments')
`;
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
  for (const [name, spec] of resultSpecs) {
    const result = {
      status: 'sandboxed_lean_kernel_passed',
      certifying: true,
      sandboxed: true,
      non_root: true,
      kernels: ['lean'],
      enable_nanoda: false,
      exit_code: 0,
      config: spec.config,
      configuration_sha256: fileSha256(spec.config),
      comparator_fileset_digest_sha256: digest,
      paper_c_commit: sourceCommit,
      theorem_names: [spec.theorem],
      permitted_axioms: permittedAxioms,
      challenge: {
        module: path.parse(spec.challenge).name,
        file: spec.challenge,
        sha256: fileSha256(spec.challenge),
      },
      solution: {
        module: path.parse(spec.solution).name,
        file: spec.solution,
        sha256: fileSha256(spec.solution),
      },
      tool_commits: toolCommits,
      manuscript_sha256: {
        target_pdf: englishSha256,
        source_pdf_fr: frenchSha256,
      },
      transcript: spec.transcript,
      transcript_sha256: sha256(`synthetic private transcript for ${name}\n`),
    };
    write(`${evidenceRelative}/${name}`, `${JSON.stringify(result, null, 2)}\n`);
  }
}

function createBinding(expectFailure = false) {
  return run(process.execPath, [
    'scripts/create_release_binding.mjs',
    '--evidence-dir', evidenceRelative,
    '--archive', archive,
    '--raw-source', path.join(temporaryRoot, 'raw-source'),
    '--output', `${evidenceRelative}/release-binding.json`,
  ], { expectFailure });
}

function writeArchiveFor(sourceCommit) {
  archive = path.join(
    temporaryRoot,
    `paper-c-hardened-public-${sourceCommit}.tar.zst`,
  );
  fs.writeFileSync(archive, 'synthetic privacy-minimized hardened archive\n');
  const digest = sha256(fs.readFileSync(archive));
  fs.writeFileSync(`${archive}.sha256`, `${digest}  ${path.basename(archive)}\n`);
  const verifierBytes = Buffer.from(verifierStub);
  const receipt = {
    schema: 1,
    status: 'public_comparator_archive_verification_report',
    paper_c_commit: sourceCommit,
    archive_filename: path.basename(archive),
    archive_sha256: digest,
    result_sha256: Object.fromEntries(
      [...resultSpecs.keys()].map(name => [
        name,
        sha256(fs.readFileSync(path.join(repository, evidenceRelative, name))),
      ]),
    ),
    verifier: 'scripts/verify_public_comparator_archive.py',
    verifier_sha256: sha256(verifierBytes),
    qualification: (
      'Informational report from the local mandatory verifier; not a signature or ' +
      'self-sufficient proof. Release binding creation reruns the verifier against the ' +
      'private raw source.'
    ),
  };
  fs.writeFileSync(`${archive}.verified.json`, `${JSON.stringify(receipt, null, 2)}\n`);
  return digest;
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
  for (const script of [
    'create_release_binding.mjs',
    'verify_release_binding.mjs',
  ]) {
    fs.copyFileSync(path.join(sourceRoot, 'scripts', script), path.join(repository, 'scripts', script));
  }
  fs.writeFileSync(
    path.join(repository, 'scripts', 'verify_public_comparator_archive.py'),
    verifierStub,
  );
  fs.writeFileSync(path.join(temporaryRoot, 'raw-source'), 'synthetic private raw source\n');

  write('paper_C_complete_v09_en.pdf', Buffer.from('synthetic English PDF bytes\n'));
  write('paper_C_complete_v09.pdf', Buffer.from('synthetic French PDF bytes\n'));
  for (const relative of fileset) {
    const spec = [...resultSpecs.values()].find(value => value.config === relative);
    write(relative, spec ? `${JSON.stringify({
      challenge_module: path.parse(spec.challenge).name,
      solution_module: path.parse(spec.solution).name,
      theorem_names: [spec.theorem],
      permitted_axioms: permittedAxioms,
      enable_nanoda: false,
    }, null, 2)}\n` : `synthetic source for ${relative}\n`);
  }
  const auditConfig = {
    target_pdf: { sha256: fileSha256('paper_C_complete_v09_en.pdf') },
    source_pdf_fr: { sha256: fileSha256('paper_C_complete_v09.pdf') },
    verification: {
      toolchain: {
        lean: { commit: toolCommits.lean },
        mathlib: { commit: toolCommits.mathlib },
      },
      comparator: {
        fileset,
        tools: {
          comparator: { commit: toolCommits.comparator },
          lean4export: { commit: toolCommits.lean4export },
          landrun: { commit: toolCommits.landrun },
        },
      },
    },
  };
  write('audit_config.json', `${JSON.stringify(auditConfig, null, 2)}\n`);
  run('git', ['init', '-q']);
  run('git', ['config', 'user.name', 'Release Binding Self-Test']);
  run('git', ['config', 'user.email', 'release-binding-self-test@example.invalid']);
  run('git', ['add', '.']);
  run('git', ['commit', '-q', '-m', 'source Q']);
  const sourceCommit = run('git', ['rev-parse', 'HEAD']).stdout.trim();
  run('git', ['checkout', '-q', '-b', 'source-evidence-negative', sourceCommit]);
  write(`${evidenceRelative}/stale.json`, '{}\n');
  run('git', ['add', evidenceRelative]);
  run('git', ['commit', '-q', '-m', 'invalid source Q with stale evidence']);
  const staleSource = run('git', ['rev-parse', 'HEAD']).stdout.trim();
  writeResults(staleSource);
  writeArchiveFor(staleSource);
  const staleRejected = createBinding(true);
  if (!staleRejected.stderr.includes('already contains files') &&
      !staleRejected.stderr.includes('unexpected release-evidence file')) {
    throw new Error('creator accepted source Q preloaded with current release evidence');
  }
  run('git', ['checkout', '-q', '-B', 'main', sourceCommit]);
  writeResults(sourceCommit);
  const archiveSha256 = writeArchiveFor(sourceCommit);
  const preexistingTemporarySentinel = path.join(
    temporaryRoot,
    '.paper-c-verified-result-hashes-existing-sentinel',
  );
  fs.writeFileSync(preexistingTemporarySentinel, 'must remain untouched\n');
  createBinding();
  if (fs.readFileSync(preexistingTemporarySentinel, 'utf8') !== 'must remain untouched\n') {
    throw new Error('binding creator altered a pre-existing temporary-path sentinel');
  }
  const leakedTemporaryDirectories = fs.readdirSync(temporaryRoot).filter(
    name => name.startsWith('.paper-c-verified-result-hashes-') &&
      name !== path.basename(preexistingTemporarySentinel),
  );
  if (leakedTemporaryDirectories.length !== 0) {
    throw new Error(
      `binding creator leaked owned temporary directories: ${leakedTemporaryDirectories.join(', ')}`,
    );
  }
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
    '--raw-source', path.join(temporaryRoot, 'raw-source'),
    '--output', `${evidenceRelative}/release-binding.json`,
  ], { expectFailure: true });
  if (!rejectedCreate.stderr.includes('dirty outside')) {
    throw new Error(
      'creator did not explain its fail-closed dirty-worktree rejection:\n' +
      rejectedCreate.stderr,
    );
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

  for (const [field, replacement, expectedMessage] of [
    ['theorem_names', ['wrong_theorem'], 'theorem names'],
    ['permitted_axioms', ['propext'], 'permitted axioms'],
    ['challenge', { module: 'Challenge', file: 'Challenge.lean', sha256: '0'.repeat(64) }, 'endpoint binding'],
    ['tool_commits', { ...toolCommits, lean: '0'.repeat(40) }, 'tool commit pins'],
    ['transcript_sha256', 'not-a-digest', 'transcript binding'],
  ]) {
    run('git', ['checkout', '-q', '-B', `result-negative-${field}`, sourceCommit]);
    writeResults(sourceCommit);
    const resultPath = `${evidenceRelative}/result-theorem-one-one.json`;
    const value = JSON.parse(fs.readFileSync(path.join(repository, resultPath), 'utf8'));
    value[field] = replacement;
    write(resultPath, `${JSON.stringify(value, null, 2)}\n`);
    const rejectedCreate = createBinding(true);
    if (!`${rejectedCreate.stdout}${rejectedCreate.stderr}`.includes(expectedMessage)) {
      throw new Error(`creator did not explain ${field} rejection`);
    }
  }

  run('git', ['checkout', '-q', '-B', 'result-negative-extra-key', sourceCommit]);
  writeResults(sourceCommit);
  {
    const resultPath = `${evidenceRelative}/result-theorem-one-one.json`;
    const value = JSON.parse(fs.readFileSync(path.join(repository, resultPath), 'utf8'));
    value.qualified = false;
    write(resultPath, `${JSON.stringify(value, null, 2)}\n`);
    const rejectedExtra = createBinding(true);
    if (!`${rejectedExtra.stdout}${rejectedExtra.stderr}`.includes('exact-key schema')) {
      throw new Error('creator accepted an extra result-record key');
    }
  }

  run('git', ['checkout', '-q', '-B', 'result-negative-duplicate-key', sourceCommit]);
  writeResults(sourceCommit);
  {
    const resultPath = `${evidenceRelative}/result-theorem-one-one.json`;
    const target = path.join(repository, resultPath);
    const bytes = fs.readFileSync(target, 'utf8').replace(
      '  "certifying": true,',
      '  "certifying": false,\n  "certifying": true,',
    );
    fs.writeFileSync(target, bytes);
    const rejectedDuplicate = createBinding(true);
    if (!`${rejectedDuplicate.stdout}${rejectedDuplicate.stderr}`.includes('not canonical')) {
      throw new Error('creator accepted a duplicate JSON key');
    }
  }

  run('git', ['checkout', '-q', '-B', 'binding-negative-extra-key', sourceCommit]);
  writeResults(sourceCommit);
  createBinding();
  {
    const bindingPath = `${evidenceRelative}/release-binding.json`;
    const value = JSON.parse(fs.readFileSync(path.join(repository, bindingPath), 'utf8'));
    value.qualified = false;
    write(bindingPath, `${JSON.stringify(value, null, 2)}\n`);
    run('git', ['add', evidenceRelative]);
    run('git', ['commit', '-q', '-m', 'packaging R with extra binding key']);
    const rejectedBindingExtra = verifyBinding(archiveSha256, true);
    if (!rejectedBindingExtra.stderr.includes('exact-key schema')) {
      throw new Error('verifier accepted an extra release-binding key');
    }
  }

  console.log('release-binding two-commit protocol self-test passed');
} finally {
  fs.rmSync(temporaryRoot, { recursive: true, force: true });
}
