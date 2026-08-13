#!/usr/bin/env node
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const RELEASE = 'v0.48.1';
const EVIDENCE_RELATIVE = 'release_evidence/v0.48.1';
const BINDING_RELATIVE = `${EVIDENCE_RELATIVE}/release-binding.json`;
const RESULT_SPECS = new Map([
  ['result-theorem-one-one.json', {
    config: 'comparator/theorem_one_one.json', challenge: 'Challenge.lean',
    solution: 'Solution.lean', transcript: 'comparator-theorem-one-one.txt',
  }],
  ['result-infinite-finite-transfer.json', {
    config: 'comparator/theorem_one_one_transfer.json', challenge: 'ChallengeTransfer.lean',
    solution: 'SolutionTransfer.lean', transcript: 'comparator-infinite-finite-transfer.txt',
  }],
]);
const RESULT_KEYS = new Set([
  'status', 'certifying', 'sandboxed', 'non_root', 'kernels', 'enable_nanoda',
  'exit_code', 'config', 'configuration_sha256', 'comparator_fileset_digest_sha256',
  'paper_c_commit', 'theorem_names', 'permitted_axioms', 'challenge', 'solution',
  'tool_commits', 'manuscript_sha256', 'transcript', 'transcript_sha256',
]);
const BINDING_KEYS = new Set([
  'schema', 'release', 'protocol', 'paper_c_commit',
  'comparator_fileset_digest_sha256', 'english_pdf_sha256', 'french_pdf_sha256',
  'hardened_archive_sha256', 'evidence', 'certifying', 'sandboxed', 'non_root',
  'enable_nanoda', 'kernels',
]);
const ENDPOINT_KEYS = new Set(['module', 'file', 'sha256']);
const TOOL_KEYS = new Set(['lean', 'mathlib', 'comparator', 'lean4export', 'landrun']);
const MANUSCRIPT_KEYS = new Set(['target_pdf', 'source_pdf_fr']);
const EXPECTED_PACKAGING_PATHS = new Set([
  BINDING_RELATIVE,
  ...[...RESULT_SPECS.keys()].map(name => `${EVIDENCE_RELATIVE}/${name}`),
]);

function arg(name) {
  const i = process.argv.indexOf(name);
  if (i < 0 || i + 1 >= process.argv.length) throw new Error(`missing ${name}`);
  return process.argv[i + 1];
}

function sha256Buffer(buffer) {
  return crypto.createHash('sha256').update(buffer).digest('hex');
}

function parseCanonicalJson(bytes, label) {
  const value = JSON.parse(bytes.toString('utf8'));
  const canonical = Buffer.from(`${JSON.stringify(value, null, 2)}\n`);
  if (!bytes.equals(canonical)) {
    throw new Error(`${label}: JSON is not canonical pretty-printed UTF-8`);
  }
  return value;
}

function git(root, args, encoding = 'utf8') {
  return execFileSync('git', ['-C', root, ...args], { encoding });
}

function gitFile(root, commit, relative) {
  return git(root, ['show', `${commit}:${relative}`], null);
}

function nulPaths(buffer) {
  return buffer.toString('utf8').split('\0').filter(Boolean);
}

function sameSet(actual, expected) {
  return actual.size === expected.size && [...actual].every(value => expected.has(value));
}

function expectedTools(config) {
  try {
    return {
      lean: config.verification.toolchain.lean.commit,
      mathlib: config.verification.toolchain.mathlib.commit,
      comparator: config.verification.comparator.tools.comparator.commit,
      lean4export: config.verification.comparator.tools.lean4export.commit,
      landrun: config.verification.comparator.tools.landrun.commit,
    };
  } catch {
    throw new Error('source commit Q audit_config.json has incomplete tool pins');
  }
}

function configAndFilesetAt(root, commit) {
  const config = JSON.parse(gitFile(root, commit, 'audit_config.json').toString('utf8'));
  const fileset = config?.verification?.comparator?.fileset;
  if (!Array.isArray(fileset) || fileset.length === 0 ||
      new Set(fileset).size !== fileset.length) {
    throw new Error(`${commit}: invalid Comparator fileset`);
  }
  for (const relative of fileset) {
    if (typeof relative !== 'string' || relative.length === 0 ||
        path.posix.isAbsolute(relative) || relative.split('/').includes('..') ||
        relative.includes('\\')) {
      throw new Error(`${commit}: unsafe Comparator fileset path: ${relative}`);
    }
  }
  const compare = (left, right) => Buffer.from(left).compare(Buffer.from(right));
  const hash = crypto.createHash('sha256');
  for (const relative of [...fileset].sort(compare)) {
    hash.update(relative);
    hash.update('\0');
    hash.update(gitFile(root, commit, relative));
    hash.update('\0');
  }
  return { config, fileset, digest: hash.digest('hex') };
}

const bindingPath = path.resolve(arg('--binding'));
const evidenceDir = path.resolve(arg('--evidence-dir'));
const expectedArchive = arg('--expected-archive-sha256');
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const canonicalEvidenceDir = path.join(root, ...EVIDENCE_RELATIVE.split('/'));
const canonicalBindingPath = path.join(root, ...BINDING_RELATIVE.split('/'));
if (evidenceDir !== canonicalEvidenceDir || bindingPath !== canonicalBindingPath) {
  throw new Error(`binding and result records must be read from ${EVIDENCE_RELATIVE}`);
}
if (!/^[0-9a-f]{64}$/.test(expectedArchive)) {
  throw new Error('expected hardened archive SHA-256 is not 64 lowercase hex characters');
}

const packagingCommit = git(root, ['rev-parse', '--verify', 'HEAD^{commit}']).trim();
const parents = git(root, ['show', '-s', '--format=%P', packagingCommit]).trim().split(/\s+/).filter(Boolean);
if (parents.length !== 1) throw new Error('packaging commit R must have exactly one parent');
const sourceCommit = parents[0];

for (const relative of ['paper_C_complete_v09_en.pdf', 'paper_C_complete_v09.pdf']) {
  const sourceBlob = git(root, ['rev-parse', `${sourceCommit}:${relative}`]).trim();
  const packagingBlob = git(root, ['rev-parse', `${packagingCommit}:${relative}`]).trim();
  if (sourceBlob !== packagingBlob) throw new Error(`${relative} differs between Q and R`);
}

const sourceState = configAndFilesetAt(root, sourceCommit);
const packagingState = configAndFilesetAt(root, packagingCommit);
if (JSON.stringify(sourceState.fileset) !== JSON.stringify(packagingState.fileset) ||
    sourceState.digest !== packagingState.digest) {
  throw new Error('Comparator fileset differs between source commit Q and packaging commit R');
}
const sourceEvidencePaths = nulPaths(git(root, [
  'ls-tree', '-r', '--name-only', '-z', sourceCommit, '--', EVIDENCE_RELATIVE,
], null));
if (sourceEvidencePaths.length !== 0) {
  throw new Error(`source commit Q must contain no files under ${EVIDENCE_RELATIVE}`);
}

const changedPaths = new Set(nulPaths(git(root, [
  'diff', '--name-only', '-z', sourceCommit, packagingCommit, '--',
], null)));
if (!sameSet(changedPaths, EXPECTED_PACKAGING_PATHS)) {
  const outside = [...changedPaths].filter(value => !value.startsWith(`${EVIDENCE_RELATIVE}/`));
  throw new Error(
    outside.length > 0
      ? `packaging commit R changes paths outside ${EVIDENCE_RELATIVE}: ${outside.join(', ')}`
      : `packaging commit R must add exactly the binding and two result records; observed: ${[...changedPaths].join(', ')}`,
  );
}
const addedPaths = new Set(nulPaths(git(root, [
  'diff', '--diff-filter=A', '--name-only', '-z', sourceCommit, packagingCommit, '--',
], null)));
if (!sameSet(addedPaths, EXPECTED_PACKAGING_PATHS)) {
  throw new Error('packaging commit R must add, not replace or modify, its three evidence files');
}
const packagedTreePaths = new Set(nulPaths(git(root, [
  'ls-tree', '-r', '--name-only', '-z', packagingCommit, '--', EVIDENCE_RELATIVE,
], null)));
if (!sameSet(packagedTreePaths, EXPECTED_PACKAGING_PATHS)) {
  throw new Error(`unexpected files in ${EVIDENCE_RELATIVE} at packaging commit R`);
}

const bindingBytes = fs.readFileSync(bindingPath);
if (!bindingBytes.equals(gitFile(root, packagingCommit, BINDING_RELATIVE))) {
  throw new Error('working-tree release binding differs from packaging commit R');
}
const binding = parseCanonicalJson(bindingBytes, 'release binding');
if (!sameSet(new Set(Object.keys(binding)), BINDING_KEYS)) {
  throw new Error('release binding has an unexpected exact-key schema');
}
if (binding.schema !== 2 || binding.release !== RELEASE ||
    binding.protocol !== 'source-parent-packaging-v1') {
  throw new Error('unexpected release-binding schema, release or protocol');
}
if (binding.paper_c_commit !== sourceCommit) {
  throw new Error('release binding does not carry parent source commit Q');
}
if (binding.hardened_archive_sha256 !== expectedArchive) {
  throw new Error('hardened archive SHA-256 mismatch');
}
if (binding.certifying !== true || binding.sandboxed !== true ||
    binding.non_root !== true || binding.enable_nanoda !== false ||
    JSON.stringify(binding.kernels) !== JSON.stringify(['lean'])) {
  throw new Error('binding is not hardened/certifying Lean-kernel evidence');
}
if (binding.comparator_fileset_digest_sha256 !== sourceState.digest) {
  throw new Error('binding Comparator digest does not match source commit Q');
}

const englishSourceBytes = gitFile(root, sourceCommit, 'paper_C_complete_v09_en.pdf');
const frenchSourceBytes = gitFile(root, sourceCommit, 'paper_C_complete_v09.pdf');
const englishSha256 = sha256Buffer(englishSourceBytes);
const frenchSha256 = sha256Buffer(frenchSourceBytes);
if (binding.english_pdf_sha256 !== englishSha256 ||
    binding.french_pdf_sha256 !== frenchSha256) {
  throw new Error('binding PDF hashes do not match source commit Q');
}
if (sourceState.config.target_pdf?.sha256 !== englishSha256 ||
    sourceState.config.source_pdf_fr?.sha256 !== frenchSha256) {
  throw new Error('source commit Q audit_config.json PDF hashes are inconsistent');
}

const evidenceNames = Object.keys(binding.evidence ?? {});
if (typeof binding.evidence !== 'object' || binding.evidence === null ||
    Array.isArray(binding.evidence) ||
    !sameSet(new Set(evidenceNames), new Set(RESULT_SPECS.keys())) ||
    evidenceNames.some(name => !/^[0-9a-f]{64}$/.test(binding.evidence[name]))) {
  throw new Error('binding evidence map must contain exactly the two result records');
}
const tools = expectedTools(sourceState.config);
for (const [name, spec] of RESULT_SPECS) {
  const relative = `${EVIDENCE_RELATIVE}/${name}`;
  const file = path.join(canonicalEvidenceDir, name);
  const bytes = fs.readFileSync(file);
  if (!bytes.equals(gitFile(root, packagingCommit, relative))) {
    throw new Error(`${name}: working-tree bytes differ from packaging commit R`);
  }
  if (sha256Buffer(bytes) !== binding.evidence[name]) {
    throw new Error(`${name}: SHA-256 mismatch`);
  }
  const result = parseCanonicalJson(bytes, name);
  const configBytes = gitFile(root, sourceCommit, spec.config);
  const config = JSON.parse(configBytes.toString('utf8'));
  if (!sameSet(new Set(Object.keys(result)), RESULT_KEYS)) {
    throw new Error(`${name}: unexpected exact-key schema`);
  }
  if (result.status !== 'sandboxed_lean_kernel_passed' ||
      result.paper_c_commit !== sourceCommit || result.config !== spec.config ||
      result.certifying !== true || result.sandboxed !== true ||
      result.non_root !== true || result.exit_code !== 0 ||
      result.enable_nanoda !== false ||
      JSON.stringify(result.kernels) !== JSON.stringify(['lean'])) {
    throw new Error(`${name}: invalid hardened result record for source commit Q`);
  }
  if (result.configuration_sha256 !== sha256Buffer(configBytes)) {
    throw new Error(`${name}: Comparator configuration does not match source commit Q`);
  }
  if (result.comparator_fileset_digest_sha256 !== sourceState.digest) {
    throw new Error(`${name}: Comparator fileset digest mismatch`);
  }
  if (result.manuscript_sha256?.target_pdf !== englishSha256 ||
      result.manuscript_sha256?.source_pdf_fr !== frenchSha256) {
    throw new Error(`${name}: manuscript hashes do not match source commit Q`);
  }
  if (JSON.stringify(result.theorem_names) !== JSON.stringify(config.theorem_names) ||
      JSON.stringify(result.permitted_axioms) !== JSON.stringify(config.permitted_axioms) ||
      config.enable_nanoda !== false) {
    throw new Error(`${name}: theorem names, permitted axioms, or Nanoda policy mismatch`);
  }
  for (const endpoint of ['challenge', 'solution']) {
    const relative = spec[endpoint];
    const expected = {
      module: config[`${endpoint}_module`],
      file: relative,
      sha256: sha256Buffer(gitFile(root, sourceCommit, relative)),
    };
    if (typeof result[endpoint] !== 'object' || result[endpoint] === null ||
        Array.isArray(result[endpoint]) ||
        !sameSet(new Set(Object.keys(result[endpoint])), ENDPOINT_KEYS) ||
        JSON.stringify(result[endpoint]) !== JSON.stringify(expected)) {
      throw new Error(`${name}: ${endpoint} endpoint binding mismatch`);
    }
  }
  if (typeof result.tool_commits !== 'object' || result.tool_commits === null ||
      Array.isArray(result.tool_commits) ||
      !sameSet(new Set(Object.keys(result.tool_commits)), TOOL_KEYS) ||
      JSON.stringify(result.tool_commits) !== JSON.stringify(tools)) {
    throw new Error(`${name}: tool commit pins do not match source commit Q`);
  }
  if (result.transcript !== spec.transcript ||
      !/^[0-9a-f]{64}$/.test(result.transcript_sha256)) {
    throw new Error(`${name}: private transcript binding is malformed`);
  }
  if (typeof result.manuscript_sha256 !== 'object' ||
      result.manuscript_sha256 === null || Array.isArray(result.manuscript_sha256) ||
      !sameSet(new Set(Object.keys(result.manuscript_sha256)), MANUSCRIPT_KEYS)) {
    throw new Error(`${name}: manuscript hash object has an unexpected exact-key schema`);
  }
}

console.log(`release binding verified: source Q ${sourceCommit}; packaging R ${packagingCommit}`);
