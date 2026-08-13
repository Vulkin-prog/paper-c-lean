#!/usr/bin/env node
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';

const RELEASE = 'v0.48.1';
const EVIDENCE_RELATIVE = 'release_evidence/v0.48.1';
const BINDING_NAME = 'release-binding.json';
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
const ENDPOINT_KEYS = new Set(['module', 'file', 'sha256']);
const TOOL_KEYS = new Set(['lean', 'mathlib', 'comparator', 'lean4export', 'landrun']);
const MANUSCRIPT_KEYS = new Set(['target_pdf', 'source_pdf_fr']);

function arg(name) {
  const i = process.argv.indexOf(name);
  if (i < 0 || i + 1 >= process.argv.length) throw new Error(`missing ${name}`);
  return process.argv[i + 1];
}

function optionalArg(name) {
  const i = process.argv.indexOf(name);
  return i < 0 ? null : process.argv[i + 1];
}

function sha256(file) {
  return crypto.createHash('sha256').update(fs.readFileSync(file)).digest('hex');
}

function parseCanonicalJson(bytes, label) {
  const value = JSON.parse(bytes.toString('utf8'));
  const canonical = Buffer.from(`${JSON.stringify(value, null, 2)}\n`);
  if (!bytes.equals(canonical)) {
    throw new Error(`${label}: JSON is not canonical pretty-printed UTF-8`);
  }
  return value;
}

function assertRegularFile(file, label) {
  const stat = fs.lstatSync(file);
  if (!stat.isFile() || stat.isSymbolicLink()) {
    throw new Error(`${label} must be a regular, non-symbolic file`);
  }
}

function assertOutsideRepository(candidate, root, label) {
  const resolvedCandidate = fs.realpathSync(candidate);
  const resolvedRoot = fs.realpathSync(root);
  const relative = path.relative(resolvedRoot, resolvedCandidate);
  if (relative === '' || (!relative.startsWith(`..${path.sep}`) && relative !== '..')) {
    throw new Error(`${label} must be outside the source repository`);
  }
}

function validateFileset(config, root) {
  const fileset = config?.verification?.comparator?.fileset;
  if (!Array.isArray(fileset) || fileset.length === 0) {
    throw new Error('audit_config.json has no Comparator fileset');
  }
  if (new Set(fileset).size !== fileset.length) {
    throw new Error('Comparator fileset contains duplicates');
  }
  for (const relative of fileset) {
    if (typeof relative !== 'string' || relative.length === 0 ||
        path.posix.isAbsolute(relative) || relative.split('/').includes('..') ||
        relative.includes('\\')) {
      throw new Error(`unsafe Comparator fileset path: ${relative}`);
    }
    assertRegularFile(path.join(root, relative), `Comparator fileset entry ${relative}`);
  }
  return fileset;
}

function filesetDigest(fileset, root) {
  const compare = (left, right) => Buffer.from(left).compare(Buffer.from(right));
  const hash = crypto.createHash('sha256');
  for (const relative of [...fileset].sort(compare)) {
    hash.update(relative);
    hash.update('\0');
    hash.update(fs.readFileSync(path.join(root, relative)));
    hash.update('\0');
  }
  return hash.digest('hex');
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
    throw new Error('audit_config.json has incomplete tool pins');
  }
}

function dirtyPaths(root) {
  const output = execFileSync(
    'git',
    ['-C', root, 'status', '--porcelain=v1', '-z', '--untracked-files=all'],
  );
  const records = output.toString('utf8').split('\0').filter(Boolean);
  const paths = [];
  for (let i = 0; i < records.length; i += 1) {
    const record = records[i];
    if (record.length < 4 || record[2] !== ' ') {
      throw new Error('could not parse git status while creating release binding');
    }
    const status = record.slice(0, 2);
    paths.push(record.slice(3));
    if (status.includes('R') || status.includes('C')) {
      i += 1;
      if (i >= records.length) throw new Error('incomplete rename/copy in git status');
      paths.push(records[i]);
    }
  }
  return paths;
}

const evidenceDir = path.resolve(arg('--evidence-dir'));
const archive = path.resolve(arg('--archive'));
const rawSourceArgument = optionalArg('--raw-source');
if (rawSourceArgument === null) {
  throw new Error('missing --raw-source for mandatory independent archive verification');
}
const rawSource = path.resolve(rawSourceArgument);
const output = path.resolve(arg('--output'));
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const canonicalEvidenceDir = path.join(root, ...EVIDENCE_RELATIVE.split('/'));
const canonicalOutput = path.join(canonicalEvidenceDir, BINDING_NAME);
if (evidenceDir !== canonicalEvidenceDir || output !== canonicalOutput) {
  throw new Error(`binding and result records must be created in ${EVIDENCE_RELATIVE}`);
}
assertOutsideRepository(archive, root, 'hardened public archive');
assertOutsideRepository(rawSource, root, 'private raw evidence source');
assertRegularFile(archive, 'hardened public archive');
const expectedArchiveNamePattern = /^paper-c-hardened-public-([0-9a-f]{40})\.tar\.zst$/;
const archiveNameMatch = expectedArchiveNamePattern.exec(path.basename(archive));
if (archiveNameMatch === null) {
  throw new Error(
    'hardened public archive must be named ' +
    'paper-c-hardened-public-<full-source-Q>.tar.zst',
  );
}

const head = execFileSync('git', ['-C', root, 'rev-parse', '--verify', 'HEAD^{commit}'], {
  encoding: 'utf8',
}).trim();
if (!/^[0-9a-f]{40}$/.test(head)) throw new Error('HEAD is not an exact commit');
if (archiveNameMatch[1] !== head) {
  throw new Error('hardened public archive filename does not bind source commit Q');
}
const archiveSidecar = `${archive}.sha256`;
assertRegularFile(archiveSidecar, 'hardened public archive checksum sidecar');
const archiveSha256 = sha256(archive);
const expectedArchiveSidecar = `${archiveSha256}  ${path.basename(archive)}\n`;
if (fs.readFileSync(archiveSidecar, 'utf8') !== expectedArchiveSidecar) {
  throw new Error('hardened public archive checksum sidecar mismatch');
}
const publicVerifierRelative = 'scripts/verify_public_comparator_archive.py';
const publicVerifier = path.join(root, publicVerifierRelative);
assertRegularFile(publicVerifier, 'public archive independent verifier');
const committedVerifier = execFileSync(
  'git',
  ['-C', root, 'show', `${head}:${publicVerifierRelative}`],
);
if (!fs.readFileSync(publicVerifier).equals(committedVerifier)) {
  throw new Error('public archive verifier differs from source commit Q');
}
const resultHashesTemporaryDirectory = fs.mkdtempSync(
  path.join(path.dirname(archive), '.paper-c-verified-result-hashes-'),
);
const resultHashesOutput = path.join(
  resultHashesTemporaryDirectory,
  'result-hashes.json',
);
let verifiedResultHashes;
try {
  execFileSync(
    '/usr/bin/python3',
    [
      publicVerifier,
      '--source', rawSource,
      '--archive', archive,
      '--repository', root,
      '--packaging-evidence-dir', canonicalEvidenceDir,
      '--result-hashes-output', resultHashesOutput,
    ],
    { stdio: 'inherit' },
  );
  verifiedResultHashes = JSON.parse(fs.readFileSync(resultHashesOutput, 'utf8'));
} finally {
  fs.rmSync(resultHashesTemporaryDirectory, { recursive: true, force: true });
}
if (verifiedResultHashes.schema !== 1 ||
    verifiedResultHashes.paper_c_commit !== head ||
    verifiedResultHashes.archive_sha256 !== archiveSha256 ||
    typeof verifiedResultHashes.result_sha256 !== 'object' ||
    verifiedResultHashes.result_sha256 === null ||
    Array.isArray(verifiedResultHashes.result_sha256)) {
  throw new Error('invalid result-hash output from independent public verifier');
}
const committedEvidence = execFileSync(
  'git',
  ['-C', root, 'ls-tree', '-r', '--name-only', '-z', head, '--', EVIDENCE_RELATIVE],
);
if (committedEvidence.length !== 0) {
  throw new Error(`source commit Q already contains files under ${EVIDENCE_RELATIVE}`);
}

const allowedPrefix = `${EVIDENCE_RELATIVE}/`;
const outsideEvidence = dirtyPaths(root).filter(relative => !relative.startsWith(allowedPrefix));
if (outsideEvidence.length !== 0) {
  throw new Error(
    `source commit worktree is dirty outside ${EVIDENCE_RELATIVE}: ${outsideEvidence.join(', ')}`,
  );
}

fs.mkdirSync(canonicalEvidenceDir, { recursive: true });
const allowedNames = new Set([...RESULT_SPECS.keys(), BINDING_NAME]);
const observedNames = fs.readdirSync(canonicalEvidenceDir);
for (const name of observedNames) {
  if (!allowedNames.has(name)) throw new Error(`unexpected release-evidence file: ${name}`);
}

const englishPdf = path.join(root, 'paper_C_complete_v09_en.pdf');
const frenchPdf = path.join(root, 'paper_C_complete_v09.pdf');
assertRegularFile(englishPdf, 'English PDF');
assertRegularFile(frenchPdf, 'French PDF');
const englishPdfSha256 = sha256(englishPdf);
const frenchPdfSha256 = sha256(frenchPdf);

const auditConfig = JSON.parse(fs.readFileSync(path.join(root, 'audit_config.json'), 'utf8'));
if (auditConfig.target_pdf?.sha256 !== englishPdfSha256 ||
    auditConfig.source_pdf_fr?.sha256 !== frenchPdfSha256) {
  throw new Error('audit_config.json PDF hashes do not match source commit Q');
}
const comparatorFileset = validateFileset(auditConfig, root);
const comparatorDigest = filesetDigest(comparatorFileset, root);
const tools = expectedTools(auditConfig);

for (const [name, spec] of RESULT_SPECS) {
  const resultPath = path.join(canonicalEvidenceDir, name);
  assertRegularFile(resultPath, name);
  const result = parseCanonicalJson(fs.readFileSync(resultPath), name);
  if (!sameSet(new Set(Object.keys(result)), RESULT_KEYS)) {
    throw new Error(`${name}: unexpected exact-key schema`);
  }
  if (result.status !== 'sandboxed_lean_kernel_passed' ||
      result.certifying !== true || result.sandboxed !== true ||
      result.non_root !== true || result.exit_code !== 0 ||
      result.enable_nanoda !== false ||
      JSON.stringify(result.kernels) !== JSON.stringify(['lean'])) {
    throw new Error(`${name}: evidence is not certifying hardened evidence`);
  }
  if (result.config !== spec.config) throw new Error(`${name}: unexpected Comparator config`);
  if (result.paper_c_commit !== head) throw new Error(`${name}: paper_c_commit is not source commit Q`);
  const config = JSON.parse(fs.readFileSync(path.join(root, spec.config), 'utf8'));
  if (result.configuration_sha256 !== sha256(path.join(root, spec.config))) {
    throw new Error(`${name}: Comparator configuration SHA-256 mismatch`);
  }
  if (result.comparator_fileset_digest_sha256 !== comparatorDigest) {
    throw new Error(`${name}: Comparator fileset digest mismatch at source commit Q`);
  }
  if (result.manuscript_sha256?.target_pdf !== englishPdfSha256 ||
      result.manuscript_sha256?.source_pdf_fr !== frenchPdfSha256) {
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
      module: config[`${endpoint}_module`], file: relative,
      sha256: sha256(path.join(root, relative)),
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
    throw new Error(`${name}: tool commit pins do not match audit_config.json`);
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
  if (verifiedResultHashes.result_sha256[name] !== sha256(resultPath)) {
    throw new Error(`${name}: bytes differ from independently verified public archive`);
  }
}
if (JSON.stringify(Object.keys(verifiedResultHashes.result_sha256).sort()) !==
    JSON.stringify([...RESULT_SPECS.keys()].sort())) {
  throw new Error('verification receipt has an unexpected result path set');
}

const binding = {
  schema: 2,
  release: RELEASE,
  protocol: 'source-parent-packaging-v1',
  paper_c_commit: head,
  comparator_fileset_digest_sha256: comparatorDigest,
  english_pdf_sha256: englishPdfSha256,
  french_pdf_sha256: frenchPdfSha256,
  hardened_archive_sha256: archiveSha256,
  evidence: Object.fromEntries(
    [...RESULT_SPECS.keys()].map(name => [name, sha256(path.join(canonicalEvidenceDir, name))]),
  ),
  certifying: true,
  sandboxed: true,
  non_root: true,
  enable_nanoda: false,
  kernels: ['lean'],
};
fs.writeFileSync(canonicalOutput, `${JSON.stringify(binding, null, 2)}\n`);
console.log(`release binding for source commit Q ${head} written to ${canonicalOutput}`);
