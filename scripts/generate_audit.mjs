import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';

const argumentsSet = new Set(process.argv.slice(2));
const supportedArguments = new Set([
  '--check',
  '--check-pdfs',
  '--check-source-digest',
  '--check-literature-certificates',
]);
for (const argument of argumentsSet) {
  if (!supportedArguments.has(argument)) {
    throw new Error(`unknown argument: ${argument}`);
  }
}
if (argumentsSet.size > 1) {
  throw new Error(
    '`--check`, `--check-pdfs`, `--check-source-digest`, and ' +
    '`--check-literature-certificates` are mutually exclusive',
  );
}

const checkOnly = argumentsSet.has('--check');
const checkPdfsOnly = argumentsSet.has('--check-pdfs');
const checkSourceDigestOnly = argumentsSet.has('--check-source-digest');
const checkLiteratureCertificatesOnly = argumentsSet.has(
  '--check-literature-certificates',
);
const scriptDirectory = path.dirname(fileURLToPath(import.meta.url));
const projectRoot = path.resolve(scriptDirectory, '..');
const sourceRoot = path.join(projectRoot, 'PaperC');
const auditPath = path.join(projectRoot, 'AuditCheck.lean');
const manifestPath = path.join(projectRoot, 'audit_manifest.json');
const formalizationPath = path.join(projectRoot, 'formalization.yaml');
const auditMarkdownPath = path.join(projectRoot, 'AXIOM_AUDIT.md');
const auditConfigPath = path.join(projectRoot, 'audit_config.json');
const readmePath = path.join(projectRoot, 'README.md');

const binaryCompare = (left, right) =>
  left < right ? -1 : left > right ? 1 : 0;

const asSentence = text => {
  const trimmed = text.trim();
  return /[.!?]$/.test(trimmed) ? trimmed : `${trimmed}.`;
};

const isPlainObject = value =>
  value !== null &&
  typeof value === 'object' &&
  !Array.isArray(value);

const requirePlainObject = (value, label) => {
  if (!isPlainObject(value)) {
    throw new Error(`audit_config.json has an invalid ${label}`);
  }
  return value;
};

const requireNonemptyString = (value, label) => {
  if (typeof value !== 'string' || value.length === 0) {
    throw new Error(`audit_config.json has an invalid ${label}`);
  }
  return value;
};

const requireUniqueStringArray = (value, label, {allowEmpty = false} = {}) => {
  if (
    !Array.isArray(value) ||
    (!allowEmpty && value.length === 0) ||
    value.some(item => typeof item !== 'string' || item.length === 0) ||
    new Set(value).size !== value.length
  ) {
    throw new Error(`audit_config.json has an invalid ${label}`);
  }
  return value;
};

const requireCommit = (value, label) => {
  if (typeof value !== 'string' || !/^[0-9a-f]{40}$/.test(value)) {
    throw new Error(`audit_config.json has an invalid ${label}`);
  }
  return value;
};

const declarationHeaderAt = (lines, index, relativePath) => {
  const line = lines[index];
  const splitDeclaration = line.match(
    /^\s*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|local|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma)\s*$/,
  );
  if (!splitDeclaration) {
    return line;
  }
  let continuationIndex = index + 1;
  while (
    continuationIndex < lines.length &&
    lines[continuationIndex].trim() === ''
  ) {
    continuationIndex += 1;
  }
  if (continuationIndex >= lines.length) {
    throw new Error(
      `${relativePath}:${index + 1}: declaration name missing after split header`,
    );
  }
  return `${line} ${lines[continuationIndex].trimStart()}`;
};

const splitHeaderSelfTest = declarationHeaderAt(
  ['theorem', '', '  split_name (h : True) : True := h'],
  0,
  '<declaration-header-self-test>',
);
if (
  !/^\s*theorem\s+split_name\b/.test(splitHeaderSelfTest)
) {
  throw new Error('declaration-header parser self-test failed');
}

const auditConfig = JSON.parse(fs.readFileSync(auditConfigPath, 'utf8'));
if (auditConfig.schema_version !== 5) {
  throw new Error('unsupported audit_config.json schema_version');
}
requirePlainObject(auditConfig.project, 'project');
requireNonemptyString(auditConfig.project.name, 'project.name');
requireNonemptyString(auditConfig.project.title, 'project.title');
requireUniqueStringArray(auditConfig.project.authors, 'project.authors');
requireNonemptyString(auditConfig.project.license, 'project.license');
requireNonemptyString(
  auditConfig.project.concept_doi,
  'project.concept_doi',
);

const coreSourceMetadata = requirePlainObject(
  auditConfig.core_source,
  'core_source',
);
requireNonemptyString(
  coreSourceMetadata.base_version,
  'core_source.base_version',
);
const configuredCoreSourceFileset = requireUniqueStringArray(
  coreSourceMetadata.fileset,
  'core_source.fileset',
);
if (
  !Number.isSafeInteger(coreSourceMetadata.file_count) ||
  coreSourceMetadata.file_count < 1
) {
  throw new Error('audit_config.json has an invalid core_source.file_count');
}
if (!/^[0-9a-f]{64}$/.test(coreSourceMetadata.digest_sha256 ?? '')) {
  throw new Error('audit_config.json has an invalid core_source.digest_sha256');
}

if (!Array.isArray(auditConfig.sources) || auditConfig.sources.length === 0) {
  throw new Error('audit_config.json has an invalid sources list');
}
const sourceKeys = new Set();
const sourceIds = new Set();
const sourceById = new Map();
const localSources = [];
for (const [index, source] of auditConfig.sources.entries()) {
  requirePlainObject(source, `sources[${index}]`);
  requireNonemptyString(source.key, `sources[${index}].key`);
  if (sourceKeys.has(source.key)) {
    throw new Error(`audit_config.json has duplicate source key ${source.key}`);
  }
  sourceKeys.add(source.key);
  requireNonemptyString(source.title, `sources[${index}].title`);
  requireUniqueStringArray(source.authors, `sources[${index}].authors`);
  requireNonemptyString(source.id, `sources[${index}].id`);
  if (sourceIds.has(source.id)) {
    throw new Error(`audit_config.json has duplicate source id ${source.id}`);
  }
  sourceIds.add(source.id);
  sourceById.set(source.id, source);
  requireNonemptyString(source.type, `sources[${index}].type`);
  const hasFilename = source.filename !== undefined;
  const hasSha256 = source.sha256 !== undefined;
  const hasPageCount = source.page_count !== undefined;
  const hasByteLength = source.byte_length !== undefined;
  if (
    ![hasFilename, hasSha256, hasPageCount, hasByteLength].every(
      present => present === hasFilename,
    )
  ) {
    throw new Error(
      `audit_config.json sources[${index}] must provide filename, sha256, ` +
      'page_count and byte_length together',
    );
  }
  if (hasFilename) {
    requireNonemptyString(source.filename, `sources[${index}].filename`);
    if (
      path.basename(source.filename) !== source.filename ||
      !source.filename.endsWith('.pdf')
    ) {
      throw new Error(
        `audit_config.json has an invalid sources[${index}].filename`,
      );
    }
    if (!/^[0-9a-f]{64}$/.test(source.sha256)) {
      throw new Error(
        `audit_config.json has an invalid sources[${index}].sha256`,
      );
    }
    if (!Number.isSafeInteger(source.page_count) || source.page_count < 1) {
      throw new Error(
        `audit_config.json has an invalid sources[${index}].page_count`,
      );
    }
    if (!Number.isSafeInteger(source.byte_length) || source.byte_length < 1) {
      throw new Error(
        `audit_config.json has an invalid sources[${index}].byte_length`,
      );
    }
    localSources.push(source);
  }
}

requirePlainObject(auditConfig.editorial, 'editorial');
requireNonemptyString(auditConfig.editorial.scope, 'editorial.scope');
requireUniqueStringArray(
  auditConfig.editorial.main_result_item_ids,
  'editorial.main_result_item_ids',
);
requireNonemptyString(
  auditConfig.editorial.paper_item_completeness_note,
  'editorial.paper_item_completeness_note',
);
requireUniqueStringArray(auditConfig.editorial.axioms, 'editorial.axioms');
requirePlainObject(auditConfig.editorial.automation, 'editorial.automation');
if (
  !Array.isArray(auditConfig.editorial.automation.methods) ||
  auditConfig.editorial.automation.methods.length === 0
) {
  throw new Error('audit_config.json has an invalid editorial.automation.methods');
}
for (const [index, method] of
  auditConfig.editorial.automation.methods.entries()) {
  requirePlainObject(method, `editorial.automation.methods[${index}]`);
  if (!['manual', 'copilot', 'agent', 'autonomous', 'other'].includes(
    method.method,
  )) {
    throw new Error(
      `audit_config.json has an invalid ` +
      `editorial.automation.methods[${index}].method`,
    );
  }
}
requirePlainObject(auditConfig.editorial.fidelity, 'editorial.fidelity');
requireNonemptyString(
  auditConfig.editorial.fidelity.divergences,
  'editorial.fidelity.divergences',
);
requirePlainObject(auditConfig.editorial.review, 'editorial.review');
requireNonemptyString(
  auditConfig.editorial.review.status,
  'editorial.review.status',
);

requirePlainObject(auditConfig.verification, 'verification');
const formalizationTemplate = requirePlainObject(
  auditConfig.verification.formalization_template,
  'verification.formalization_template',
);
if (formalizationTemplate.version !== 'v0.3') {
  throw new Error('formalization template version must be v0.3');
}
requireNonemptyString(
  formalizationTemplate.repository,
  'verification.formalization_template.repository',
);
requireCommit(
  formalizationTemplate.commit,
  'verification.formalization_template.commit',
);
const configuredToolchain = requirePlainObject(
  auditConfig.verification.toolchain,
  'verification.toolchain',
);
for (const tool of ['lean', 'mathlib']) {
  requirePlainObject(configuredToolchain[tool], `verification.toolchain.${tool}`);
  requireNonemptyString(
    configuredToolchain[tool].version,
    `verification.toolchain.${tool}.version`,
  );
  requireCommit(
    configuredToolchain[tool].commit,
    `verification.toolchain.${tool}.commit`,
  );
}
const configuredLeanToolchain = fs
  .readFileSync(path.join(projectRoot, 'lean-toolchain'), 'utf8')
  .trim();
if (configuredLeanToolchain !== configuredToolchain.lean.toolchain) {
  throw new Error(
    `lean-toolchain mismatch: configured ${configuredToolchain.lean.toolchain}, ` +
    `found ${configuredLeanToolchain}`,
  );
}
const lakeManifest = JSON.parse(
  fs.readFileSync(path.join(projectRoot, 'lake-manifest.json'), 'utf8'),
);
const mathlibPackage = lakeManifest.packages?.find(
  packageEntry => packageEntry.name === 'mathlib',
);
if (
  mathlibPackage?.rev !== configuredToolchain.mathlib.commit ||
  mathlibPackage?.inputRev !== configuredToolchain.mathlib.version
) {
  throw new Error(
    'configured Mathlib version/commit does not match lake-manifest.json',
  );
}
const literatureCertificateMetadata = requirePlainObject(
  auditConfig.verification.literature_certificates,
  'verification.literature_certificates',
);
requireNonemptyString(
  literatureCertificateMetadata.scope,
  'verification.literature_certificates.scope',
);
requireNonemptyString(
  literatureCertificateMetadata.review_status,
  'verification.literature_certificates.review_status',
);
if (literatureCertificateMetadata.review_status !== 'agent-reviewed') {
  throw new Error(
    'verification.literature_certificates.review_status must be agent-reviewed',
  );
}
if (literatureCertificateMetadata.human_peer_reviewed !== false) {
  throw new Error(
    'verification.literature_certificates.human_peer_reviewed must be false',
  );
}
requireNonemptyString(
  literatureCertificateMetadata.status_note,
  'verification.literature_certificates.status_note',
);
if (
  !Array.isArray(literatureCertificateMetadata.entries) ||
  literatureCertificateMetadata.entries.length === 0
) {
  throw new Error(
    'audit_config.json has an invalid ' +
    'verification.literature_certificates.entries',
  );
}
const allowedLiteratureImplicationStatuses = new Set([
  'agent_checked_supports',
  'agent_checked_with_open_gap',
  'not_established',
]);
const allowedPrimarySourceAccessStatuses = new Set([
  'full_text',
  'partial',
  'not_accessed',
]);
for (const [index, entry] of
  literatureCertificateMetadata.entries.entries()) {
  const label = `verification.literature_certificates.entries[${index}]`;
  requirePlainObject(entry, label);
  requireNonemptyString(entry.bridge_id, `${label}.bridge_id`);
  requireNonemptyString(entry.file, `${label}.file`);
  requireNonemptyString(entry.source_locator, `${label}.source_locator`);
  if (!allowedPrimarySourceAccessStatuses.has(entry.primary_source_access)) {
    throw new Error(
      `audit_config.json has an invalid ${label}.primary_source_access`,
    );
  }
  if (!allowedLiteratureImplicationStatuses.has(entry.implication_status)) {
    throw new Error(
      `audit_config.json has an invalid ${label}.implication_status`,
    );
  }
  requireNonemptyString(entry.limitations, `${label}.limitations`);
}
if (!Array.isArray(literatureCertificateMetadata.historical_closure_notes)) {
  throw new Error(
    'audit_config.json has an invalid ' +
    'verification.literature_certificates.historical_closure_notes',
  );
}
for (const [index, entry] of
  literatureCertificateMetadata.historical_closure_notes.entries()) {
  const label =
    `verification.literature_certificates.historical_closure_notes[${index}]`;
  requirePlainObject(entry, label);
  requireNonemptyString(entry.bridge_id, `${label}.bridge_id`);
  requireNonemptyString(entry.file, `${label}.file`);
  if (entry.status !== 'lean_discharged') {
    throw new Error(`audit_config.json has an invalid ${label}.status`);
  }
  requireNonemptyString(entry.discharged_by, `${label}.discharged_by`);
  requireNonemptyString(entry.note, `${label}.note`);
}
const comparatorMetadata = requirePlainObject(
  auditConfig.verification.comparator,
  'verification.comparator',
);
if (
  comparatorMetadata.source_snapshot_comparator_state !==
    'definitions_and_digests_only'
) {
  throw new Error(
    'audit_config.json has an invalid ' +
    'verification.comparator.source_snapshot_comparator_state',
  );
}
if (comparatorMetadata.release_evidence_state !== 'external_to_source_snapshot') {
  throw new Error(
    'audit_config.json has an invalid ' +
    'verification.comparator.release_evidence_state',
  );
}
if (
  comparatorMetadata.release_evidence_location !==
    `release_evidence/v${coreSourceMetadata.base_version}/`
) {
  throw new Error(
    'audit_config.json has an invalid ' +
    'verification.comparator.release_evidence_location',
  );
}
if (comparatorMetadata.packaging_commit_required !== true) {
  throw new Error(
    'audit_config.json must require a Comparator evidence packaging commit',
  );
}
requireNonemptyString(
  comparatorMetadata.state_note,
  'verification.comparator.state_note',
);
if (
  Object.hasOwn(comparatorMetadata, 'status') ||
  Object.hasOwn(comparatorMetadata, 'status_note')
) {
  throw new Error(
    'legacy current Comparator status fields are forbidden; source snapshots ' +
    'must use the timeless release-evidence protocol fields',
  );
}
const expectedComparatorMetadataKeys = [
  'compatibility_probe',
  'configurations',
  'fileset',
  'historical_configurations',
  'historical_published_evidence',
  'packaging_commit_required',
  'release_evidence_location',
  'release_evidence_state',
  'source_snapshot_comparator_state',
  'state_note',
  'tools',
].sort(binaryCompare);
if (
  JSON.stringify(Object.keys(comparatorMetadata).sort(binaryCompare)) !==
  JSON.stringify(expectedComparatorMetadataKeys)
) {
  throw new Error(
    'audit_config.json has unexpected verification.comparator fields',
  );
}
requirePlainObject(comparatorMetadata.tools, 'verification.comparator.tools');
for (const tool of ['comparator', 'lean4export', 'landrun']) {
  requirePlainObject(
    comparatorMetadata.tools[tool],
    `verification.comparator.tools.${tool}`,
  );
  requireNonemptyString(
    comparatorMetadata.tools[tool].repository,
    `verification.comparator.tools.${tool}.repository`,
  );
  requireCommit(
    comparatorMetadata.tools[tool].commit,
    `verification.comparator.tools.${tool}.commit`,
  );
}
requirePlainObject(
  comparatorMetadata.tools.nanoda,
  'verification.comparator.tools.nanoda',
);
if (typeof comparatorMetadata.tools.nanoda.installed !== 'boolean') {
  throw new Error(
    'audit_config.json has an invalid ' +
    'verification.comparator.tools.nanoda.installed',
  );
}
if (comparatorMetadata.tools.nanoda.installed) {
  requireCommit(
    comparatorMetadata.tools.nanoda.commit,
    'verification.comparator.tools.nanoda.commit',
  );
} else if (comparatorMetadata.tools.nanoda.commit !== null) {
  throw new Error('absent nanoda must have a null commit');
}
requirePlainObject(
  comparatorMetadata.compatibility_probe,
  'verification.comparator.compatibility_probe',
);
if (
  !['not_run', 'passed', 'failed'].includes(
    comparatorMetadata.compatibility_probe.status,
  ) ||
  typeof comparatorMetadata.compatibility_probe.sandboxed !== 'boolean' ||
  typeof comparatorMetadata.compatibility_probe
    .counts_as_project_verification !== 'boolean'
) {
  throw new Error(
    'audit_config.json has an invalid ' +
    'verification.comparator.compatibility_probe',
  );
}
requireNonemptyString(
  comparatorMetadata.compatibility_probe.scope,
  'verification.comparator.compatibility_probe.scope',
);
requireNonemptyString(
  comparatorMetadata.compatibility_probe.transcript,
  'verification.comparator.compatibility_probe.transcript',
);
if (
  !/^[0-9a-f]{64}$/.test(
    comparatorMetadata.compatibility_probe.transcript_sha256 ?? '',
  )
) {
  throw new Error(
    'audit_config.json has an invalid compatibility-probe transcript SHA-256',
  );
}
requireUniqueStringArray(
  comparatorMetadata.fileset,
  'verification.comparator.fileset',
);
if (
  !Array.isArray(comparatorMetadata.configurations) ||
  comparatorMetadata.configurations.length === 0
) {
  throw new Error(
    'audit_config.json has an invalid verification.comparator.configurations',
  );
}
if (!Array.isArray(comparatorMetadata.historical_configurations)) {
  throw new Error(
    'audit_config.json has an invalid ' +
    'verification.comparator.historical_configurations',
  );
}
const historicalPublishedComparatorEvidence = requirePlainObject(
  comparatorMetadata.historical_published_evidence,
  'verification.comparator.historical_published_evidence',
);
const expectedPublishedComparatorEvidenceKeys = [
  'archive',
  'archive_sha256',
  'archive_size_bytes',
  'comparator_fileset_digest_sha256',
  'enable_nanoda',
  'kernels',
  'metadata_verification',
  'non_root',
  'paper_c_commit',
  'privacy_profile',
  'qualification',
  'raw_archive',
  'raw_archive_retention',
  'raw_archive_sha256',
  'raw_archive_size_bytes',
  'raw_sha256sums_in_public_archive',
  'raw_sha256sums_sha256',
  'redaction_manifest',
  'redaction_manifest_sha256',
  'release_tag',
  'release_url',
  'sandboxed',
  'summary_sha256',
].sort(binaryCompare);
if (
  JSON.stringify(
    Object.keys(historicalPublishedComparatorEvidence).sort(binaryCompare),
  ) !==
  JSON.stringify(expectedPublishedComparatorEvidenceKeys)
) {
  throw new Error(
    'audit_config.json has unexpected Comparator published-evidence fields',
  );
}
for (const field of [
  'release_tag',
  'release_url',
  'archive',
  'privacy_profile',
  'redaction_manifest',
  'raw_archive',
  'raw_archive_retention',
  'raw_sha256sums_in_public_archive',
  'metadata_verification',
  'qualification',
]) {
  requireNonemptyString(
    historicalPublishedComparatorEvidence[field],
    `verification.comparator.historical_published_evidence.${field}`,
  );
}
for (const field of [
  'archive_sha256',
  'summary_sha256',
  'comparator_fileset_digest_sha256',
  'redaction_manifest_sha256',
  'raw_archive_sha256',
  'raw_sha256sums_sha256',
]) {
  if (!/^[0-9a-f]{64}$/.test(
    historicalPublishedComparatorEvidence[field] ?? '',
  )) {
    throw new Error(
      'audit_config.json has an invalid ' +
      `verification.comparator.historical_published_evidence.${field}`,
    );
  }
}
requireCommit(
  historicalPublishedComparatorEvidence.paper_c_commit,
  'verification.comparator.historical_published_evidence.paper_c_commit',
);
if (
  path.basename(historicalPublishedComparatorEvidence.archive) !==
    historicalPublishedComparatorEvidence.archive ||
  !historicalPublishedComparatorEvidence.archive.endsWith('.tar.zst') ||
  path.basename(historicalPublishedComparatorEvidence.raw_archive) !==
    historicalPublishedComparatorEvidence.raw_archive ||
  !historicalPublishedComparatorEvidence.raw_archive.endsWith('.tar.zst') ||
  historicalPublishedComparatorEvidence.redaction_manifest !==
    'REDACTION_MANIFEST.json' ||
  historicalPublishedComparatorEvidence.raw_sha256sums_in_public_archive !==
    'provenance/RAW_SHA256SUMS' ||
  historicalPublishedComparatorEvidence.archive ===
    historicalPublishedComparatorEvidence.raw_archive ||
  historicalPublishedComparatorEvidence.archive_sha256 ===
    historicalPublishedComparatorEvidence.raw_archive_sha256
) {
  throw new Error(
    'audit_config.json has invalid public/private Comparator evidence paths',
  );
}
if (
  !Number.isSafeInteger(
    historicalPublishedComparatorEvidence.archive_size_bytes,
  ) ||
  historicalPublishedComparatorEvidence.archive_size_bytes < 1 ||
  !Number.isSafeInteger(
    historicalPublishedComparatorEvidence.raw_archive_size_bytes,
  ) ||
  historicalPublishedComparatorEvidence.raw_archive_size_bytes < 1 ||
  historicalPublishedComparatorEvidence.privacy_profile !==
    'derived_privacy_minimized_bundle_v1' ||
  historicalPublishedComparatorEvidence.raw_archive_retention !==
    'local_only_not_published' ||
  historicalPublishedComparatorEvidence.sandboxed !== true ||
  historicalPublishedComparatorEvidence.non_root !== true ||
  historicalPublishedComparatorEvidence.enable_nanoda !== false ||
  JSON.stringify(historicalPublishedComparatorEvidence.kernels) !==
    JSON.stringify(['lean'])
) {
  throw new Error(
    'audit_config.json has an invalid ' +
    'verification.comparator.historical_published_evidence qualification',
  );
}
if (!Array.isArray(auditConfig.challenge_placeholders)) {
  throw new Error('audit_config.json has an invalid challenge_placeholders');
}
if (!Array.isArray(auditConfig.paper_items) || auditConfig.paper_items.length === 0) {
  throw new Error('audit_config.json has an invalid paper_items');
}
const validatePdfEntry = (field, entry) => {
  if (
    entry === null ||
    typeof entry !== 'object' ||
    Array.isArray(entry) ||
    Object.keys(entry).sort().join(',') !==
      'byte_length,filename,page_count,sha256' ||
    typeof entry.filename !== 'string' ||
    entry.filename.length === 0 ||
    path.basename(entry.filename) !== entry.filename ||
    !entry.filename.endsWith('.pdf') ||
    !/^[0-9a-f]{64}$/.test(entry.sha256) ||
    !Number.isSafeInteger(entry.page_count) ||
    entry.page_count < 1 ||
    !Number.isSafeInteger(entry.byte_length) ||
    entry.byte_length < 1
  ) {
    throw new Error(`audit_config.json has an invalid ${field} entry`);
  }
};
validatePdfEntry('target_pdf', auditConfig.target_pdf);
validatePdfEntry('source_pdf_fr', auditConfig.source_pdf_fr);
if (
  auditConfig.target_pdf.filename === auditConfig.source_pdf_fr.filename ||
  auditConfig.target_pdf.sha256 === auditConfig.source_pdf_fr.sha256
) {
  throw new Error('target_pdf and source_pdf_fr must identify distinct files');
}
if (
  localSources.length !== 1 ||
  localSources[0].filename !== auditConfig.target_pdf.filename ||
  localSources[0].sha256 !== auditConfig.target_pdf.sha256 ||
  localSources[0].page_count !== auditConfig.target_pdf.page_count ||
  localSources[0].byte_length !== auditConfig.target_pdf.byte_length
) {
  throw new Error(
    'sources must contain exactly one local entry matching all target_pdf metadata',
  );
}

const verifiedPdfEntries = {};
for (const field of ['target_pdf', 'source_pdf_fr']) {
  const entry = auditConfig[field];
  const pdfPath = path.join(projectRoot, entry.filename);
  if (!fs.existsSync(pdfPath)) {
    throw new Error(
      `${field} PDF is missing: ${entry.filename}`,
    );
  }
  const pdfBytes = fs.readFileSync(pdfPath);
  const actualSha256 = crypto
    .createHash('sha256')
    .update(pdfBytes)
    .digest('hex');
  if (actualSha256 !== entry.sha256) {
    throw new Error(
      `${field} PDF SHA-256 mismatch for ${entry.filename}: ` +
      `expected ${entry.sha256}, got ${actualSha256}`,
    );
  }
  if (pdfBytes.length !== entry.byte_length) {
    throw new Error(
      `${field} PDF byte-length mismatch for ${entry.filename}: ` +
      `expected ${entry.byte_length}, got ${pdfBytes.length}`,
    );
  }
  verifiedPdfEntries[field] = {
    filename: entry.filename,
    sha256: actualSha256,
    page_count: entry.page_count,
    byte_length: pdfBytes.length,
  };
}

if (checkPdfsOnly) {
  fs.writeSync(
    process.stdout.fd,
    `verified target_pdf ${verifiedPdfEntries.target_pdf.sha256} ` +
    `(${verifiedPdfEntries.target_pdf.byte_length} bytes; configured ` +
    `${verifiedPdfEntries.target_pdf.page_count} pages); ` +
    `source_pdf_fr ${verifiedPdfEntries.source_pdf_fr.sha256} ` +
    `(${verifiedPdfEntries.source_pdf_fr.byte_length} bytes; configured ` +
    `${verifiedPdfEntries.source_pdf_fr.page_count} pages)\n`,
  );
  process.exit(0);
}

const readme = fs.readFileSync(readmePath, 'utf8');
for (const field of ['target_pdf', 'source_pdf_fr']) {
  for (const key of ['filename', 'sha256', 'page_count', 'byte_length']) {
    if (readme.includes(auditConfig[field][key])) {
      continue;
    }
    throw new Error(
      `README.md does not contain the configured ${field} ${key}`,
    );
  }
}

const coreSourceFileset = configuredCoreSourceFileset;

function discoverLeanSources(directory, relativeDirectory) {
  if (!fs.existsSync(directory)) {
    throw new Error(`source directory is missing: ${relativeDirectory}`);
  }
  const entries = fs.readdirSync(directory, {withFileTypes: true})
    .sort((left, right) => binaryCompare(left.name, right.name));
  return entries.flatMap(entry => {
    const absolutePath = path.join(directory, entry.name);
    const relativePath = path.posix.join(relativeDirectory, entry.name);
    if (entry.isDirectory()) {
      return discoverLeanSources(absolutePath, relativePath);
    }
    if (entry.isFile()) {
      return entry.name.endsWith('.lean') ? [relativePath] : [];
    }
    throw new Error(
      `unsupported source-fileset entry (expected file or directory): ` +
      relativePath,
    );
  });
}

const rootSourcePath = path.join(projectRoot, 'PaperC.lean');
if (!fs.existsSync(rootSourcePath) || !fs.statSync(rootSourcePath).isFile()) {
  throw new Error('root source file is missing: PaperC.lean');
}
const sourceFiles = [
  'PaperC.lean',
  ...discoverLeanSources(sourceRoot, 'PaperC'),
].sort(binaryCompare);
if (sourceFiles.length !== coreSourceMetadata.file_count) {
  throw new Error(
    `frozen core source count mismatch: configured ` +
    `${coreSourceMetadata.file_count}, discovered ${sourceFiles.length}`,
  );
}

function stripCommentsAndStrings(source, filename) {
  let output = '';
  let blockDepth = 0;
  let inLineComment = false;
  let inString = false;
  let escaped = false;

  for (let index = 0; index < source.length; index += 1) {
    const character = source[index];
    const next = source[index + 1];

    if (inLineComment) {
      if (character === '\n') {
        inLineComment = false;
        output += '\n';
      } else {
        output += ' ';
      }
    } else if (blockDepth > 0) {
      if (character === '/' && next === '-') {
        blockDepth += 1;
        output += '  ';
        index += 1;
      } else if (character === '-' && next === '/') {
        blockDepth -= 1;
        output += '  ';
        index += 1;
      } else {
        output += character === '\n' ? '\n' : ' ';
      }
    } else if (inString) {
      output += character === '\n' ? '\n' : ' ';
      if (escaped) {
        escaped = false;
      } else if (character === '\\') {
        escaped = true;
      } else if (character === '"') {
        inString = false;
      }
    } else if (character === '-' && next === '-') {
      inLineComment = true;
      output += '  ';
      index += 1;
    } else if (character === '/' && next === '-') {
      blockDepth = 1;
      output += '  ';
      index += 1;
    } else if (character === '"') {
      inString = true;
      output += ' ';
    } else {
      output += character;
    }
  }

  if (blockDepth !== 0) {
    throw new Error(`${filename}: unterminated block comment`);
  }
  if (inString) {
    throw new Error(`${filename}: unterminated string`);
  }
  return output;
}

const sourceDigest = crypto.createHash('sha256');
const declarations = [];
const rawSources = new Map();
const cleanSources = new Map();

for (const relativePath of sourceFiles) {
  const absolutePath = path.join(projectRoot, relativePath);
  const rawSource = fs.readFileSync(absolutePath, 'utf8');
  rawSources.set(relativePath, rawSource);
  sourceDigest.update(relativePath);
  sourceDigest.update('\0');
  sourceDigest.update(rawSource);
  sourceDigest.update('\0');

  const cleanSource = stripCommentsAndStrings(rawSource, relativePath);
  cleanSources.set(relativePath, cleanSource);
  const lines = cleanSource.split('\n');
  const blocks = [];
  let namespacePrefix = [];

  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    let match;

    match = line.match(/^\s*namespace\s+([^\s]+)/);
    if (match) {
      const relativeNamespace = match[1];
      const oldLength = namespacePrefix.length;
      const isRooted = relativeNamespace.startsWith('_root_.');
      const components = (isRooted
        ? relativeNamespace.slice(7)
        : relativeNamespace).split('.');
      namespacePrefix = isRooted
        ? components
        : [...namespacePrefix, ...components];
      blocks.push({
        kind: 'namespace',
        label: relativeNamespace,
        oldLength,
      });
      continue;
    }

    match = line.match(
      /^\s*(?:noncomputable\s+)?section(?:\s+([^\s]+))?\s*$/,
    );
    if (match) {
      blocks.push({
        kind: 'section',
        label: match[1] ?? null,
        oldLength: namespacePrefix.length,
      });
      continue;
    }

    match = line.match(/^\s*end(?:\s+([^\s]+))?\s*$/);
    if (match) {
      if (blocks.length === 0) {
        throw new Error(`${relativePath}:${index + 1}: unmatched end`);
      }
      const block = blocks.pop();
      if (match[1] && block.label && match[1] !== block.label) {
        throw new Error(
          `${relativePath}:${index + 1}: end ${match[1]} closes ` +
          `${block.kind} ${block.label}`,
        );
      }
      namespacePrefix = namespacePrefix.slice(0, block.oldLength);
      continue;
    }

    const declarationHeader =
      declarationHeaderAt(lines, index, relativePath);
    match = declarationHeader.match(
      /^\s*(?:@\[[^\n]*?\]\s*)*((?:(?:private|protected|local|noncomputable|unsafe|partial)\s+)*)(theorem|lemma)\s+([^\s({:\[]+)/,
    );
    if (!match) {
      continue;
    }

    const modifiers = match[1].trim().split(/\s+/).filter(Boolean);
    if (modifiers.includes('private') || modifiers.includes('local')) {
      continue;
    }

    const localName = match[3];
    const fullName = localName.startsWith('_root_.')
      ? localName.slice(7)
      : [...namespacePrefix, ...localName.split('.')].join('.');
    if (!fullName.startsWith('PaperC.')) {
      throw new Error(
        `${relativePath}:${index + 1}: public declaration outside PaperC: ` +
        fullName,
      );
    }

    declarations.push({
      name: fullName,
      kind: match[2],
      source: relativePath,
      line: index + 1,
    });
  }

  if (blocks.length !== 0) {
    throw new Error(
      `${relativePath}: unclosed namespace/section blocks: ` +
      JSON.stringify(blocks),
    );
  }
}

const digest = sourceDigest.digest('hex');
if (digest !== coreSourceMetadata.digest_sha256) {
  throw new Error(
    `frozen v${coreSourceMetadata.base_version} core digest mismatch: ` +
    `configured ${coreSourceMetadata.digest_sha256}, computed ${digest}`,
  );
}

if (checkSourceDigestOnly) {
  if (!fs.existsSync(manifestPath)) {
    throw new Error('audit_manifest.json is missing');
  }
  let checkedManifest;
  try {
    checkedManifest = JSON.parse(fs.readFileSync(manifestPath, 'utf8'));
  } catch (error) {
    throw new Error(`audit_manifest.json is not valid JSON: ${error.message}`);
  }
  if (!/^[0-9a-f]{64}$/.test(checkedManifest.source_digest_sha256 ?? '')) {
    throw new Error(
      'audit_manifest.json has an invalid source_digest_sha256 field',
    );
  }
  if (checkedManifest.source_digest_sha256 !== digest) {
    throw new Error(
      'PaperC source digest mismatch: ' +
      `manifest records ${checkedManifest.source_digest_sha256}, ` +
      `computed ${digest}`,
    );
  }
  fs.writeSync(
    process.stdout.fd,
    `verified PaperC source digest ${digest}\n`,
  );
  process.exit(0);
}

declarations.sort((left, right) => binaryCompare(left.name, right.name));
const duplicateNames = declarations.filter(
  (declaration, index) =>
    index > 0 && declaration.name === declarations[index - 1].name,
);
if (duplicateNames.length !== 0) {
  throw new Error(
    `duplicate public names: ${duplicateNames.map(item => item.name).join(', ')}`,
  );
}

const additionalTargets = [
  {
    name: 'PaperC.LargePrimeGraphResolution.largePrimeSolutionLinearEquiv',
    kind: 'definition',
    reason: 'Proof-bearing public construction retained from ReviewAxioms.lean',
  },
  {
    name: 'PaperC.PinnedGraphResolution.pinnedGraphLinearEquiv',
    kind: 'definition',
    reason: 'Proof-bearing public construction retained from ReviewAxioms.lean',
  },
];

function parseBridgeMarkers(relativePath, rawSource) {
  const bridges = [];
  const markerPattern =
    /\/-\s*AUDIT_BRIDGE\s*\n([\s\S]*?)\nAUDIT_BRIDGE\s*-\//g;
  for (const match of rawSource.matchAll(markerPattern)) {
    let metadata;
    try {
      metadata = JSON.parse(match[1]);
    } catch (error) {
      throw new Error(
        `${relativePath}: malformed AUDIT_BRIDGE JSON: ${error.message}`,
      );
    }
    const requiredStringFields = [
      ['id', metadata.id],
      ['lean_name', metadata.lean_name],
      ['formalization_relation', metadata.formalization_relation],
      ['citation.title', metadata.citation?.title],
      ['citation.locator', metadata.citation?.locator],
      ['source_statement.verbatim', metadata.source_statement?.verbatim],
      ['source_statement.source_url', metadata.source_statement?.source_url],
      ['source_statement.verification', metadata.source_statement?.verification],
      ['manuscript_locator.result', metadata.manuscript_locator?.result],
    ];
    for (const [field, value] of requiredStringFields) {
      if (typeof value !== 'string' || value.length === 0) {
        throw new Error(
          `${relativePath}: bridge ${metadata.id ?? '<unknown>'} ` +
          `has an invalid ${field}`,
        );
      }
    }
    if (
      metadata.manuscript_locator.reference !== undefined &&
      /^(?:\[\d+\]|\d+)$/.test(metadata.manuscript_locator.reference)
    ) {
      throw new Error(
        `${relativePath}: bridge ${metadata.id} uses a fragile numeric ` +
        'manuscript bibliography reference; use bibliography_key or author-year',
      );
    }
    if (
      metadata.manuscript_locator.bibliography_key !== undefined &&
      (
        typeof metadata.manuscript_locator.bibliography_key !== 'string' ||
        !/^[A-Za-z][A-Za-z0-9:_-]*$/.test(
          metadata.manuscript_locator.bibliography_key,
        )
      )
    ) {
      throw new Error(
        `${relativePath}: bridge ${metadata.id} has an invalid ` +
        'manuscript bibliography_key',
      );
    }
    if (!['external', 'internal'].includes(metadata.kind)) {
      throw new Error(
        `${relativePath}: bridge ${metadata.id ?? '<unknown>'} ` +
        'has an invalid kind (expected external or internal)',
      );
    }
    if (!['open', 'discharged'].includes(metadata.status)) {
      throw new Error(
        `${relativePath}: bridge ${metadata.id ?? '<unknown>'} ` +
        'has an invalid status (expected open or discharged)',
      );
    }
    if (metadata.status === 'discharged') {
      if (
        !Array.isArray(metadata.discharged_by) ||
        metadata.discharged_by.length === 0 ||
        metadata.discharged_by.some(
          name =>
            typeof name !== 'string' ||
            name.length === 0 ||
            !name.startsWith('PaperC.'),
        ) ||
        new Set(metadata.discharged_by).size !==
          metadata.discharged_by.length
      ) {
        throw new Error(
          `${relativePath}: discharged bridge ${metadata.id} has an invalid ` +
          'discharged_by list',
        );
      }
    } else if (metadata.discharged_by !== undefined) {
      throw new Error(
        `${relativePath}: open bridge ${metadata.id} must not have ` +
        'discharged_by',
      );
    }
    if (
      !Array.isArray(metadata.citation.authors) ||
      metadata.citation.authors.length === 0 ||
      metadata.citation.authors.some(
        author => typeof author !== 'string' || author.length === 0,
      )
    ) {
      throw new Error(
        `${relativePath}: bridge ${metadata.id} has invalid citation authors`,
      );
    }
    if (!metadata.lean_name.startsWith('PaperC.')) {
      throw new Error(
        `${relativePath}: bridge ${metadata.id} is outside namespace PaperC`,
      );
    }
    if (
      metadata.source_statement.displayed_formulas !== undefined &&
      (
        metadata.source_statement.displayed_formulas === null ||
        Array.isArray(metadata.source_statement.displayed_formulas) ||
        typeof metadata.source_statement.displayed_formulas !== 'object' ||
        Object.entries(metadata.source_statement.displayed_formulas).some(
          ([label, formula]) =>
            label.length === 0 ||
            typeof formula !== 'string' ||
            formula.length === 0,
        )
      )
    ) {
      throw new Error(
        `${relativePath}: bridge ${metadata.id} has invalid displayed formulas`,
      );
    }
    if (
      metadata.source_statement.verbatim_is_excerpt !== undefined &&
      typeof metadata.source_statement.verbatim_is_excerpt !== 'boolean'
    ) {
      throw new Error(
        `${relativePath}: bridge ${metadata.id} has invalid verbatim_is_excerpt`,
      );
    }
    // Per-bridge manuscript citations are immutable historical provenance.
    // The synchronized current editions are recorded at manifest top level.
    if (
      metadata.citation.target_pdf_sha256 !== undefined &&
      !/^[0-9a-f]{64}$/.test(metadata.citation.target_pdf_sha256)
    ) {
      throw new Error(
        `${relativePath}: bridge ${metadata.id} has an invalid historical target PDF SHA-256`,
      );
    }

    const localName = metadata.lean_name.split('.').at(-1);
    const escapedName = localName.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const declarationPattern = new RegExp(
      `^(?:noncomputable\\s+)?def\\s+${escapedName}\\b`,
      'm',
    );
    const declarationMatch = declarationPattern.exec(rawSource);
    if (!declarationMatch) {
      throw new Error(
        `${relativePath}: bridge declaration ${metadata.lean_name} not found`,
      );
    }
    if (declarationMatch.index < match.index) {
      throw new Error(
        `${relativePath}: AUDIT_BRIDGE marker must precede ${localName}`,
      );
    }
    const intervening = rawSource.slice(
      match.index + match[0].length,
      declarationMatch.index,
    );
    if (!/^\s*$/.test(intervening)) {
      throw new Error(
        `${relativePath}: AUDIT_BRIDGE marker must be adjacent to ${localName}`,
      );
    }

    const declarationLine =
      rawSource.slice(0, declarationMatch.index).split('\n').length;
    const nextBlank = rawSource.indexOf('\n\n', declarationMatch.index);
    const declarationEnd =
      nextBlank === -1 ? rawSource.length : nextBlank;
    const declarationText = rawSource
      .slice(declarationMatch.index, declarationEnd)
      .trimEnd();
    const statementDigest = crypto
      .createHash('sha256')
      .update(declarationText)
      .digest('hex');
    const quoteDigest = crypto
      .createHash('sha256')
      .update(metadata.source_statement.verbatim)
      .digest('hex');

    bridges.push({
      ...metadata,
      declaration: {
        source: relativePath,
        line: declarationLine,
        statement_sha256: statementDigest,
      },
      source_statement: {
        ...metadata.source_statement,
        sha256: quoteDigest,
      },
      local_name: localName,
    });
  }
  return bridges;
}

const bridges = sourceFiles.flatMap(relativePath =>
  parseBridgeMarkers(relativePath, rawSources.get(relativePath)),
);
bridges.sort((left, right) => binaryCompare(left.id, right.id));

const duplicateBridgeIds = bridges.filter(
  (bridge, index) => index > 0 && bridge.id === bridges[index - 1].id,
);
if (duplicateBridgeIds.length !== 0) {
  throw new Error(
    `duplicate bridge ids: ${duplicateBridgeIds.map(item => item.id).join(', ')}`,
  );
}
const bridgeNames = [...bridges]
  .sort((left, right) => binaryCompare(left.lean_name, right.lean_name));
const duplicateBridgeNames = bridgeNames.filter(
  (bridge, index) =>
    index > 0 && bridge.lean_name === bridgeNames[index - 1].lean_name,
);
if (duplicateBridgeNames.length !== 0) {
  throw new Error(
    'duplicate bridge Lean names: ' +
    duplicateBridgeNames.map(item => item.lean_name).join(', '),
  );
}
const publicDeclarationNames =
  new Set(declarations.map(declaration => declaration.name));
for (const bridge of bridges) {
  for (const dischargeTheorem of bridge.discharged_by ?? []) {
    if (!publicDeclarationNames.has(dischargeTheorem)) {
      throw new Error(
        `bridge ${bridge.id} has unknown discharge theorem ` +
        dischargeTheorem,
      );
    }
  }
}

const literatureSourceIdByBridgeId = new Map();
for (const bridge of bridges) {
  if (bridge.kind !== 'external' || bridge.status !== 'open') {
    continue;
  }
  const doi = bridge.citation?.doi;
  if (typeof doi !== 'string' || !/^10\.\d{4,9}\/\S+$/.test(doi)) {
    throw new Error(
      `${bridge.source}: open external bridge ${bridge.id} has an invalid ` +
      'citation.doi',
    );
  }
  const sourceId = `https://doi.org/${doi}`;
  if (!sourceById.has(sourceId)) {
    throw new Error(
      `${bridge.source}: open external bridge ${bridge.id} has no unique ` +
      `sources entry with id ${sourceId}`,
    );
  }
  literatureSourceIdByBridgeId.set(bridge.id, sourceId);
}

function theoremSignature(declaration) {
  const source = cleanSources.get(declaration.source);
  const lines = source.split('\n');
  const signatureLines = [];
  for (
    let index = declaration.line - 1;
    index < lines.length && signatureLines.length < 300;
    index += 1
  ) {
    signatureLines.push(lines[index]);
    if (
      /:=\s*by\b/.test(lines[index]) ||
      /:=\s*$/.test(lines[index]) ||
      /^\s*where\s*$/.test(lines[index])
    ) {
      break;
    }
  }
  return signatureLines.join('\n');
}

const delimiterPairs = new Map([
  ['(', ')'],
  ['[', ']'],
  ['{', '}'],
  ['⦃', '⦄'],
  ['⟨', '⟩'],
  ['⟦', '⟧'],
]);
const closingDelimiters = new Set(delimiterPairs.values());

function findMatchingDelimiter(text, openingIndex) {
  const opening = text[openingIndex];
  if (!delimiterPairs.has(opening)) {
    return -1;
  }
  const expectedClosings = [];
  for (let index = openingIndex; index < text.length; index += 1) {
    const character = text[index];
    if (delimiterPairs.has(character)) {
      expectedClosings.push(delimiterPairs.get(character));
    } else if (closingDelimiters.has(character)) {
      if (expectedClosings.at(-1) !== character) {
        return -1;
      }
      expectedClosings.pop();
      if (expectedClosings.length === 0) {
        return index;
      }
    }
  }
  return -1;
}

function stripEnclosingParentheses(text) {
  let current = text.trim();
  while (
    current.startsWith('(') &&
    findMatchingDelimiter(current, 0) === current.length - 1
  ) {
    current = current.slice(1, -1).trim();
  }
  return current;
}

function findTopLevelToken(text, tokens, startIndex = 0) {
  const expectedClosings = [];
  const sortedTokens = [...tokens]
    .sort((left, right) => right.length - left.length);
  for (let index = startIndex; index < text.length; index += 1) {
    const character = text[index];
    if (delimiterPairs.has(character)) {
      expectedClosings.push(delimiterPairs.get(character));
      continue;
    }
    if (closingDelimiters.has(character)) {
      if (expectedClosings.at(-1) === character) {
        expectedClosings.pop();
      }
      continue;
    }
    if (expectedClosings.length !== 0) {
      continue;
    }
    const token = sortedTokens.find(candidate =>
      text.startsWith(candidate, index),
    );
    if (token !== undefined) {
      return {index, token};
    }
  }
  return null;
}

function findTopLevelResultColon(text, startIndex, endIndex) {
  const expectedClosings = [];
  for (let index = startIndex; index < endIndex; index += 1) {
    const character = text[index];
    if (delimiterPairs.has(character)) {
      expectedClosings.push(delimiterPairs.get(character));
    } else if (closingDelimiters.has(character)) {
      if (expectedClosings.at(-1) === character) {
        expectedClosings.pop();
      }
    } else if (
      character === ':' &&
      text[index + 1] !== '=' &&
      expectedClosings.length === 0
    ) {
      return index;
    }
  }
  return -1;
}

function topLevelColonIndex(text) {
  return findTopLevelResultColon(text, 0, text.length);
}

function binderContentAndKind(text) {
  const trimmed = text.trim();
  const opening = trimmed[0];
  if (
    delimiterPairs.has(opening) &&
    findMatchingDelimiter(trimmed, 0) === trimmed.length - 1
  ) {
    return {
      content: trimmed.slice(1, -1).trim(),
      opening,
    };
  }
  return {content: trimmed, opening: null};
}

function binderType(text, allowWholeBracketBinder = false) {
  const {content, opening} = binderContentAndKind(text);
  const colonIndex = topLevelColonIndex(content);
  if (colonIndex !== -1) {
    return content.slice(colonIndex + 1).trim();
  }
  if (allowWholeBracketBinder && opening === '[') {
    return content;
  }
  return null;
}

function explicitBinderTypes(text) {
  const types = [];
  for (let index = 0; index < text.length; index += 1) {
    const character = text[index];
    if (!delimiterPairs.has(character)) {
      continue;
    }
    const closingIndex = findMatchingDelimiter(text, index);
    if (closingIndex === -1) {
      throw new Error(
        `unmatched binder delimiter in theorem signature: ${text}`,
      );
    }
    const opening = character;
    if (['(', '[', '{', '⦃'].includes(opening)) {
      const type = binderType(
        text.slice(index, closingIndex + 1),
        true,
      );
      if (type !== null && type.length !== 0) {
        types.push(type);
      }
    }
    index = closingIndex;
  }
  return types;
}

function forallBinderTypes(text) {
  const types = explicitBinderTypes(text);
  let remainder = '';
  for (let index = 0; index < text.length; index += 1) {
    const character = text[index];
    if (!delimiterPairs.has(character)) {
      remainder += character;
      continue;
    }
    const closingIndex = findMatchingDelimiter(text, index);
    if (closingIndex === -1) {
      throw new Error(
        `unmatched forall-binder delimiter in theorem signature: ${text}`,
      );
    }
    remainder += ' ';
    index = closingIndex;
  }
  const bareType = binderType(remainder);
  if (bareType !== null && bareType.length !== 0) {
    types.push(bareType);
  }
  return types;
}

function leadingForallLength(text) {
  if (text.startsWith('∀')) {
    return 1;
  }
  if (/^forall\b/.test(text)) {
    return 'forall'.length;
  }
  return 0;
}

function resultPremiseTypes(resultType) {
  const premises = [];

  function visit(rawType) {
    const type = stripEnclosingParentheses(rawType);
    const forallLength = leadingForallLength(type);
    if (forallLength !== 0) {
      const comma = findTopLevelToken(type, [','], forallLength);
      if (comma === null) {
        return;
      }
      premises.push(
        ...forallBinderTypes(
          type.slice(forallLength, comma.index),
        ),
      );
      visit(type.slice(comma.index + comma.token.length));
      return;
    }

    const arrow = findTopLevelToken(type, ['->', '→']);
    if (arrow === null) {
      return;
    }
    const antecedent = type.slice(0, arrow.index);
    const directType = binderType(antecedent, true) ??
      stripEnclosingParentheses(antecedent);
    if (directType.length !== 0) {
      premises.push(directType);
    }
    visit(type.slice(arrow.index + arrow.token.length));
  }

  visit(resultType);
  return premises;
}

/*
Only direct bridge premises count as dependencies.  In particular:

* a theorem whose conclusion is a registered bridge discharges that bridge;
* curried arrows and `∀` binders in the result type are premises;
* a bridge mentioned only inside a higher-order premise, such as
  `(k : Bridge → P)`, is not itself supplied to the theorem.
*/
function theoremPremiseTypes(declaration, signature) {
  const declarationMatch =
    /\b(?:theorem|lemma)\s+[^\s({:\[]+/.exec(signature);
  if (!declarationMatch) {
    throw new Error(
      `${declaration.source}:${declaration.line}: ` +
      'cannot locate theorem declaration in signature',
    );
  }

  const bodyIndex = signature.lastIndexOf(':=');
  const headerEnd = bodyIndex === -1 ? signature.length : bodyIndex;
  const declarationEnd =
    declarationMatch.index + declarationMatch[0].length;
  const resultColon = findTopLevelResultColon(
    signature,
    declarationEnd,
    headerEnd,
  );
  const binderEnd = resultColon === -1 ? headerEnd : resultColon;
  const premises = explicitBinderTypes(
    signature.slice(declarationEnd, binderEnd),
  );
  if (resultColon !== -1) {
    premises.push(
      ...resultPremiseTypes(
        signature.slice(resultColon + 1, headerEnd),
      ),
    );
  }
  return premises;
}

function premiseTypeMentionsBridge(type, bridgeLocalName) {
  const normalized = stripEnclosingParentheses(type);
  if (normalized.startsWith('¬') || /^Not\b/.test(normalized)) {
    return false;
  }

  const forallLength = leadingForallLength(normalized);
  if (forallLength !== 0) {
    const comma = findTopLevelToken(
      normalized,
      [','],
      forallLength,
    );
    if (comma === null) {
      return false;
    }
    return premiseTypeMentionsBridge(
      normalized.slice(comma.index + comma.token.length),
      bridgeLocalName,
    );
  }

  const arrow = findTopLevelToken(normalized, ['->', '→']);
  if (arrow !== null) {
    return premiseTypeMentionsBridge(
      normalized.slice(arrow.index + arrow.token.length),
      bridgeLocalName,
    );
  }

  const escapedName = bridgeLocalName
    .replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  return new RegExp(`\\b${escapedName}\\b`).test(normalized);
}

function runPremiseParserSelfTests() {
  const bridge = 'RegisteredBridgeStatement';
  const fakeDeclaration = {
    source: '<premise-parser-self-test>',
    line: 1,
  };
  const cases = [
    {
      name: 'explicit_binder_detected',
      signature:
        `theorem test (h : ${bridge}) : True := by`,
      expected: true,
    },
    {
      name: 'multiline_binder_detected',
      signature:
        `theorem test\n    (h :\n      ${bridge}) :\n    True := by`,
      expected: true,
    },
    {
      name: 'strict_implicit_binder_detected',
      signature:
        `theorem test ⦃h : ${bridge}⦄ : True := by`,
      expected: true,
    },
    {
      name: 'unicode_arrow_antecedent_detected',
      signature:
        `theorem test : ${bridge} → True := by`,
      expected: true,
    },
    {
      name: 'ascii_arrow_antecedent_detected',
      signature:
        `theorem test : ${bridge} -> True := by`,
      expected: true,
    },
    {
      name: 'forall_result_binder_detected',
      signature:
        `theorem test : ∀ h : ${bridge}, True := by`,
      expected: true,
    },
    {
      name: 'nested_consequent_arrow_detected',
      signature:
        `theorem test : True → (${bridge} → True) := by`,
      expected: true,
    },
    {
      name: 'bridge_only_in_conclusion_ignored',
      signature:
        `theorem test : ${bridge} := by`,
      expected: false,
    },
    {
      name: 'higher_order_binder_ignored',
      signature:
        `theorem test (k : ${bridge} → True) : True := by`,
      expected: false,
    },
    {
      name: 'higher_order_arrow_antecedent_ignored',
      signature:
        `theorem test : (${bridge} → True) → True := by`,
      expected: false,
    },
    {
      name: 'higher_order_provider_detected',
      signature:
        `theorem test (k : True → ${bridge}) : True := by`,
      expected: true,
    },
    {
      name: 'forall_provider_detected',
      signature:
        `theorem test (k : ∀ n : Nat, ${bridge}) : True := by`,
      expected: true,
    },
  ];

  for (const testCase of cases) {
    const premises = theoremPremiseTypes(
      fakeDeclaration,
      testCase.signature,
    );
    const actual = premises.some(type =>
      premiseTypeMentionsBridge(type, bridge),
    );
    if (actual !== testCase.expected) {
      throw new Error(
        `premise parser self-test ${testCase.name} failed: ` +
        `expected ${testCase.expected}, got ${actual}; ` +
        `premises=${JSON.stringify(premises)}`,
      );
    }
  }

  const sourceBridge = 'SourceBridgeStatement';
  const conclusionBridge = 'ConclusionBridgeStatement';
  const implicationPremises = theoremPremiseTypes(
    fakeDeclaration,
    `theorem test : ${sourceBridge} → ${conclusionBridge} := by`,
  );
  const sourceDetected = implicationPremises.some(type =>
    premiseTypeMentionsBridge(type, sourceBridge),
  );
  const conclusionDetected = implicationPremises.some(type =>
    premiseTypeMentionsBridge(type, conclusionBridge),
  );
  if (!sourceDetected || conclusionDetected) {
    throw new Error(
      'premise parser self-test ' +
      'conclusion_bridge_implication_tracks_only_source failed: ' +
      `source=${sourceDetected}, conclusion=${conclusionDetected}; ` +
      `premises=${JSON.stringify(implicationPremises)}`,
    );
  }
}

runPremiseParserSelfTests();

const theoremRecords = declarations.map(declaration => {
  const signature = theoremSignature(declaration);
  const premiseTypes = theoremPremiseTypes(declaration, signature);
  const hypotheses = bridges
    .filter(bridge =>
      premiseTypes.some(type =>
        premiseTypeMentionsBridge(type, bridge.local_name),
      ),
    )
    .map(bridge => bridge.id)
    .sort(binaryCompare);
  return {
    ...declaration,
    conditionality:
      hypotheses.length === 0 ? 'inconditionnel' : 'conditionnel',
    hypotheses,
  };
});

for (const bridge of bridges) {
  if (
    !theoremRecords.some(record =>
      record.hypotheses.includes(bridge.id),
    )
  ) {
    throw new Error(
      `registered bridge ${bridge.id} is unused by every public theorem`,
    );
  }
}

const auditTargetNames = [
  ...declarations.map(declaration => declaration.name),
  ...additionalTargets.map(target => target.name),
].sort(binaryCompare);
const duplicateAuditTargets = auditTargetNames.filter(
  (name, index) => index > 0 && name === auditTargetNames[index - 1],
);
if (duplicateAuditTargets.length !== 0) {
  throw new Error(
    `duplicate audit targets: ${duplicateAuditTargets.join(', ')}`,
  );
}

const lakefile = fs.readFileSync(
  path.join(projectRoot, 'lakefile.toml'),
  'utf8',
);
const versionMatch = lakefile.match(/^version\s*=\s*"([^"]+)"/m);
if (!versionMatch) {
  throw new Error('project version not found in lakefile.toml');
}

const auditContent = [
  'import PaperC',
  '',
  '/-!',
  '# Exhaustive public-theorem dependency audit',
  '',
  'This file is generated by `node scripts/generate_audit.mjs`.',
  'It contains one `#print axioms` command for every explicit public',
  '`theorem` or `lemma` declaration in the complete PaperC source fileset.',
  'Private and local declarations are deliberately excluded.',
  '',
  `Public theorems/lemmas: ${declarations.length}.`,
  `Additional proof-bearing public definitions: ${additionalTargets.length}.`,
  `Source digest (SHA-256): ${digest}.`,
  '-/',
  '',
  ...auditTargetNames.map(name => `#print axioms ${name}`),
  '',
].join('\n');

const kindCounts = Object.fromEntries(
  [...new Set(declarations.map(declaration => declaration.kind))]
    .sort(binaryCompare)
    .map(kind => [
      kind,
      declarations.filter(declaration => declaration.kind === kind).length,
    ]),
);

const conditionalTheoremCount = theoremRecords.filter(
  record => record.conditionality === 'conditionnel',
).length;
const unconditionalTheoremCount =
  theoremRecords.length - conditionalTheoremCount;

const bridgeKinds = ['external', 'internal'];
const hypothesisKindCounts = Object.fromEntries(
  bridgeKinds.map(kind => [
    kind,
    bridges.filter(bridge => bridge.kind === kind).length,
  ]),
);
const conditionalTheoremCountsByHypothesisKind = Object.fromEntries(
  bridgeKinds.map(kind => {
    const bridgeIds = new Set(
      bridges
        .filter(bridge => bridge.kind === kind)
        .map(bridge => bridge.id),
    );
    return [
      kind,
      theoremRecords.filter(record =>
        record.hypotheses.some(id => bridgeIds.has(id)),
      ).length,
    ];
  }),
);
const bridgeStatuses = ['open', 'discharged'];
const hypothesisStatusCounts = Object.fromEntries(
  bridgeStatuses.map(status => [
    status,
    bridges.filter(bridge => bridge.status === status).length,
  ]),
);
const conditionalTheoremCountsByHypothesisStatus = Object.fromEntries(
  bridgeStatuses.map(status => {
    const bridgeIds = new Set(
      bridges
        .filter(bridge => bridge.status === status)
        .map(bridge => bridge.id),
    );
    return [
      status,
      theoremRecords.filter(record =>
        record.hypotheses.some(id => bridgeIds.has(id)),
      ).length,
    ];
  }),
);

const bridgeById = new Map(bridges.map(bridge => [bridge.id, bridge]));

const normalizeProjectRelativePath = (relativePath, label) => {
  requireNonemptyString(relativePath, label);
  if (
    path.isAbsolute(relativePath) ||
    relativePath.includes('\\') ||
    path.posix.normalize(relativePath) !== relativePath ||
    relativePath === '..' ||
    relativePath.startsWith('../')
  ) {
    throw new Error(`audit_config.json has an invalid ${label}`);
  }
  const absolutePath = path.join(projectRoot, relativePath);
  if (!fs.existsSync(absolutePath) || !fs.statSync(absolutePath).isFile()) {
    throw new Error(`${label} file is missing: ${relativePath}`);
  }
  return absolutePath;
};

const requiredLiteratureCertificateBridgeIds = [
  'AGG89-T1-finite-dependency-b3-zero',
  'ES86-T1b-Q-split-n2',
  'NR83-T1-divisor-log-bound',
].sort(binaryCompare);
const literatureCertificateDirectory = path.join(
  projectRoot,
  'literature_certificates',
);
const literatureCertificateDirectoryStat = fs.lstatSync(
  literatureCertificateDirectory,
);
if (
  !literatureCertificateDirectoryStat.isDirectory() ||
  literatureCertificateDirectoryStat.isSymbolicLink()
) {
  throw new Error('literature_certificates must be a real directory');
}
const discoveredLiteratureCertificateFiles = fs
  .readdirSync(literatureCertificateDirectory, {withFileTypes: true})
  .map(entry => {
    if (!entry.isFile() || entry.isSymbolicLink()) {
      throw new Error(
        `literature_certificates contains a non-file entry: ${entry.name}`,
      );
    }
    return `literature_certificates/${entry.name}`;
  })
  .sort(binaryCompare);
const configuredLiteratureCertificateFiles = [
  ...literatureCertificateMetadata.entries,
  ...literatureCertificateMetadata.historical_closure_notes,
].map(entry => entry.file).sort(binaryCompare);
if (
  JSON.stringify(discoveredLiteratureCertificateFiles) !==
  JSON.stringify(configuredLiteratureCertificateFiles)
) {
  throw new Error(
    'literature_certificates directory must contain exactly the configured ' +
    'active certificates and historical closure notes',
  );
}
const literatureCertificateBridgeIds = new Set();
const literatureCertificatePaths = new Set();
const parsedLiteratureCertificates = [];
for (const [index, entry] of
  literatureCertificateMetadata.entries.entries()) {
  const label = `verification.literature_certificates.entries[${index}]`;
  if (literatureCertificateBridgeIds.has(entry.bridge_id)) {
    throw new Error(`duplicate literature certificate bridge: ${entry.bridge_id}`);
  }
  literatureCertificateBridgeIds.add(entry.bridge_id);
  if (literatureCertificatePaths.has(entry.file)) {
    throw new Error(`duplicate literature certificate file: ${entry.file}`);
  }
  literatureCertificatePaths.add(entry.file);
  if (
    !entry.file.startsWith('literature_certificates/') ||
    !entry.file.endsWith('.md')
  ) {
    throw new Error(
      `audit_config.json has an invalid ${label}.file: ${entry.file}`,
    );
  }
  if (
    sourceFiles.includes(entry.file) ||
    comparatorMetadata.fileset.includes(entry.file) ||
    entry.file === auditConfig.target_pdf.filename ||
    entry.file === auditConfig.source_pdf_fr.filename
  ) {
    throw new Error(
      `literature certificate overlaps another audited fileset: ${entry.file}`,
    );
  }
  const bridge = bridgeById.get(entry.bridge_id);
  if (bridge === undefined) {
    throw new Error(
      `literature certificate refers to an unknown bridge: ${entry.bridge_id}`,
    );
  }
  if (bridge.kind !== 'external' || bridge.status !== 'open') {
    throw new Error(
      `literature certificate must refer to an open external bridge: ` +
      entry.bridge_id,
    );
  }
  const absolutePath = normalizeProjectRelativePath(
    entry.file,
    `${label}.file`,
  );
  const bytes = fs.readFileSync(absolutePath);
  let markdown;
  try {
    markdown = new TextDecoder('utf-8', {fatal: true}).decode(bytes);
  } catch (error) {
    throw new Error(
      `literature certificate is not valid UTF-8: ${entry.file}: ` +
      error.message,
    );
  }
  for (const requiredText of [
    `Bridge ID: \`${entry.bridge_id}\``,
    `Lean proposition: \`${bridge.lean_name}\``,
    `Current rc2 implication status: \`${entry.implication_status}\``,
    `Current source locator: \`${entry.source_locator}\``,
    `Primary-source access: \`${entry.primary_source_access}\``,
    'independent human review required',
  ]) {
    if (!markdown.includes(requiredText)) {
      throw new Error(
        `literature certificate ${entry.file} lacks required text: ` +
        requiredText,
      );
    }
  }
  parsedLiteratureCertificates.push({
    ...entry,
    lean_name: bridge.lean_name,
    sha256: crypto.createHash('sha256').update(bytes).digest('hex'),
    byte_length: bytes.length,
    review_status: literatureCertificateMetadata.review_status,
    human_peer_reviewed: literatureCertificateMetadata.human_peer_reviewed,
    supersedes_frozen_source_verification_wording_for_rc2: true,
    bytes,
  });
}
if (
  JSON.stringify([...literatureCertificateBridgeIds].sort(binaryCompare)) !==
  JSON.stringify(requiredLiteratureCertificateBridgeIds)
) {
  throw new Error(
    'active literature certificates must cover exactly the three open ' +
    'Theorem 1.1 bridges',
  );
}
const historicalLiteratureClosureNotes = [];
const historicalLiteratureClosureBridgeIds = new Set();
const historicalLiteratureClosurePaths = new Set();
for (const [index, entry] of
  literatureCertificateMetadata.historical_closure_notes.entries()) {
  const label =
    `verification.literature_certificates.historical_closure_notes[${index}]`;
  if (historicalLiteratureClosureBridgeIds.has(entry.bridge_id)) {
    throw new Error(`duplicate historical closure-note bridge: ${entry.bridge_id}`);
  }
  historicalLiteratureClosureBridgeIds.add(entry.bridge_id);
  if (
    historicalLiteratureClosurePaths.has(entry.file) ||
    literatureCertificatePaths.has(entry.file)
  ) {
    throw new Error(`duplicate literature documentation path: ${entry.file}`);
  }
  historicalLiteratureClosurePaths.add(entry.file);
  if (
    !entry.file.startsWith('literature_certificates/') ||
    !entry.file.endsWith('.md')
  ) {
    throw new Error(
      `audit_config.json has an invalid ${label}.file: ${entry.file}`,
    );
  }
  const bridge = bridgeById.get(entry.bridge_id);
  if (
    bridge === undefined ||
    bridge.kind !== 'external' ||
    bridge.status !== 'discharged'
  ) {
    throw new Error(
      `historical closure note must refer to a discharged external bridge: ` +
      entry.bridge_id,
    );
  }
  if (!(bridge.discharged_by ?? []).includes(entry.discharged_by)) {
    throw new Error(
      `historical closure note names an unregistered discharge theorem: ` +
      entry.discharged_by,
    );
  }
  const absolutePath = normalizeProjectRelativePath(entry.file, `${label}.file`);
  const bytes = fs.readFileSync(absolutePath);
  let markdown;
  try {
    markdown = new TextDecoder('utf-8', {fatal: true}).decode(bytes);
  } catch (error) {
    throw new Error(
      `historical closure note is not valid UTF-8: ${entry.file}: ` +
      error.message,
    );
  }
  for (const requiredText of [
    `Bridge ID: \`${entry.bridge_id}\``,
    `Lean proposition: \`${bridge.lean_name}\``,
    'Current bridge status: `discharged`',
    `Discharged by: \`${entry.discharged_by}\``,
    'Historical role: `closure note`',
  ]) {
    if (!markdown.includes(requiredText)) {
      throw new Error(
        `historical closure note ${entry.file} lacks required text: ` +
        requiredText,
      );
    }
  }
  historicalLiteratureClosureNotes.push({
    ...entry,
    lean_name: bridge.lean_name,
    sha256: crypto.createHash('sha256').update(bytes).digest('hex'),
    byte_length: bytes.length,
    bytes,
  });
}
if (
  JSON.stringify([...historicalLiteratureClosureBridgeIds].sort(binaryCompare)) !==
  JSON.stringify(['HK13-QO-conductor-fibres'])
) {
  throw new Error(
    'historical closure notes must record exactly the discharged HK13 bridge',
  );
}
const literatureCertificateFiles = parsedLiteratureCertificates
  .map(certificate => certificate.file)
  .sort(binaryCompare);
const literatureCertificateDigest = crypto.createHash('sha256');
for (const relativePath of literatureCertificateFiles) {
  const certificate = parsedLiteratureCertificates.find(
    entry => entry.file === relativePath,
  );
  literatureCertificateDigest.update(relativePath);
  literatureCertificateDigest.update('\0');
  literatureCertificateDigest.update(certificate.bytes);
  literatureCertificateDigest.update('\0');
}
const literatureCertificateDigestSha256 =
  literatureCertificateDigest.digest('hex');
const literatureDocumentationFiles = configuredLiteratureCertificateFiles;
const literatureDocumentationDigest = crypto.createHash('sha256');
for (const relativePath of literatureDocumentationFiles) {
  const certificate = parsedLiteratureCertificates.find(
    entry => entry.file === relativePath,
  );
  const closureNote = historicalLiteratureClosureNotes.find(
    entry => entry.file === relativePath,
  );
  const document = certificate ?? closureNote;
  literatureDocumentationDigest.update(relativePath);
  literatureDocumentationDigest.update('\0');
  literatureDocumentationDigest.update(document.bytes);
  literatureDocumentationDigest.update('\0');
}
const literatureDocumentationDigestSha256 =
  literatureDocumentationDigest.digest('hex');
for (const certificate of parsedLiteratureCertificates) {
  delete certificate.bytes;
}
for (const note of historicalLiteratureClosureNotes) {
  delete note.bytes;
}
const literatureCertificateByBridgeId = new Map(
  parsedLiteratureCertificates.map(certificate => [
    certificate.bridge_id,
    certificate,
  ]),
);
const historicalLiteratureClosureNoteByBridgeId = new Map(
  historicalLiteratureClosureNotes.map(note => [note.bridge_id, note]),
);
const effectiveSourceToLeanStatus = certificate =>
  certificate.implication_status === 'agent_checked_supports'
    ? 'agent_checked_supports'
    : 'source_to_lean_not_established';
const effectiveFormalizationRelation = (bridge, certificate) =>
  certificate.implication_status === 'agent_checked_supports'
    ? 'Agent counter-audit supports the registered source-to-proposition ' +
      'implication, without a Lean formalization or independent human review. ' +
      'Registered relation: ' +
      bridge.formalization_relation
    : 'The source-to-proposition implication is not established in rc2. ' +
      `Open construction: ${certificate.limitations}`;
const currentSourceLocator = bridge =>
  literatureCertificateByBridgeId.get(bridge.id)?.source_locator ??
  bridge.citation.locator;
const registeredCitationLabel = bridge =>
  `${bridge.citation.authors.join(', ')}, ${bridge.citation.title}, ` +
  bridge.citation.locator;
const citationLabel = bridge =>
  `${bridge.citation.authors.join(', ')}, ${bridge.citation.title}, ` +
  currentSourceLocator(bridge);
const publicBridgeEntries = bridges.map(
  ({local_name: _localName, ...bridge}) => {
    const certificate = literatureCertificateByBridgeId.get(bridge.id);
    const historicalClosureNote =
      historicalLiteratureClosureNoteByBridgeId.get(bridge.id);
    if (certificate === undefined) {
      return historicalClosureNote === undefined
        ? bridge
        : {...bridge, historical_closure_note: historicalClosureNote};
    }
    return {
      ...bridge,
      formalization_relation: effectiveFormalizationRelation(
        bridge,
        certificate,
      ),
      historical_frozen_formalization_relation: bridge.formalization_relation,
      source_statement: {
        ...bridge.source_statement,
        verification: effectiveSourceToLeanStatus(certificate),
        verification_note:
          `Current rc2 assessment: ${certificate.limitations}`,
        historical_frozen_verification:
          bridge.source_statement.verification,
        ...(bridge.source_statement.verification_note === undefined
          ? {}
          : {
              historical_frozen_verification_note:
                bridge.source_statement.verification_note,
            }),
      },
      current_source_locator: citationLabel(bridge),
      registered_frozen_source_locator: registeredCitationLabel(bridge),
      source_to_lean_status: effectiveSourceToLeanStatus(certificate),
      literature_certificate: certificate,
    };
  },
);

if (checkLiteratureCertificatesOnly) {
  const existingManifest = JSON.parse(
    fs.readFileSync(manifestPath, 'utf8'),
  );
  if (
    JSON.stringify(existingManifest.literature_certificate_fileset) !==
      JSON.stringify(literatureCertificateFiles) ||
    existingManifest.literature_certificate_digest_sha256 !==
      literatureCertificateDigestSha256 ||
    JSON.stringify(existingManifest.literature_certificates) !==
      JSON.stringify(parsedLiteratureCertificates) ||
    JSON.stringify(existingManifest.historical_literature_closure_notes) !==
      JSON.stringify(historicalLiteratureClosureNotes) ||
    JSON.stringify(existingManifest.literature_documentation_fileset) !==
      JSON.stringify(literatureDocumentationFiles) ||
    existingManifest.literature_documentation_digest_sha256 !==
      literatureDocumentationDigestSha256
  ) {
    throw new Error(
      'literature certificate bytes or mapping differ from audit_manifest.json; ' +
      'run `node scripts/generate_audit.mjs`',
    );
  }
  process.stdout.write(
    `verified ${parsedLiteratureCertificates.length} active literature ` +
    `certificates and ${historicalLiteratureClosureNotes.length} historical ` +
    `closure note (${literatureDocumentationDigestSha256})\n`,
  );
  process.exit(0);
}

const leanModulePath = (moduleName, label) => {
  requireNonemptyString(moduleName, label);
  if (!/^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$/.test(
    moduleName,
  )) {
    throw new Error(`invalid Lean module in ${label}: ${moduleName}`);
  }
  return `${moduleName.replaceAll('.', '/')}.lean`;
};

const interfaceDeclarationCache = new Map();
const interfaceTheoremNames = relativePath => {
  if (interfaceDeclarationCache.has(relativePath)) {
    return interfaceDeclarationCache.get(relativePath);
  }
  const absolutePath = normalizeProjectRelativePath(
    relativePath,
    `Lean interface ${relativePath}`,
  );
  const source = stripCommentsAndStrings(
    fs.readFileSync(absolutePath, 'utf8'),
    relativePath,
  );
  const lines = source.split('\n');
  const blocks = [];
  let namespacePrefix = [];
  const names = new Set();
  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index];
    let match = line.match(/^\s*namespace\s+([^\s]+)/);
    if (match) {
      const relativeNamespace = match[1];
      const oldLength = namespacePrefix.length;
      const isRooted = relativeNamespace.startsWith('_root_.');
      const components = (isRooted
        ? relativeNamespace.slice(7)
        : relativeNamespace).split('.');
      namespacePrefix = isRooted
        ? components
        : [...namespacePrefix, ...components];
      blocks.push({
        kind: 'namespace',
        label: relativeNamespace,
        oldLength,
      });
      continue;
    }
    match = line.match(
      /^\s*(?:noncomputable\s+)?section(?:\s+([^\s]+))?\s*$/,
    );
    if (match) {
      blocks.push({
        kind: 'section',
        label: match[1] ?? null,
        oldLength: namespacePrefix.length,
      });
      continue;
    }
    match = line.match(/^\s*end(?:\s+([^\s]+))?\s*$/);
    if (match) {
      if (blocks.length === 0) {
        throw new Error(`${relativePath}:${index + 1}: unmatched end`);
      }
      const block = blocks.pop();
      if (match[1] && block.label && match[1] !== block.label) {
        throw new Error(
          `${relativePath}:${index + 1}: end ${match[1]} closes ` +
          `${block.kind} ${block.label}`,
        );
      }
      namespacePrefix = namespacePrefix.slice(0, block.oldLength);
      continue;
    }
    const declarationHeader = declarationHeaderAt(
      lines,
      index,
      relativePath,
    );
    match = declarationHeader.match(
      /^\s*(?:@\[[^\n]*?\]\s*)*((?:(?:private|protected|local|noncomputable)\s+)*)(theorem|lemma)\s+([^\s({:\[]+)/,
    );
    if (!match) {
      continue;
    }
    const modifiers = match[1].trim().split(/\s+/).filter(Boolean);
    if (modifiers.includes('private') || modifiers.includes('local')) {
      continue;
    }
    const localName = match[3];
    const fullName = localName.startsWith('_root_.')
      ? localName.slice(7)
      : [...namespacePrefix, ...localName.split('.')].join('.');
    names.add(fullName);
  }
  if (blocks.length !== 0) {
    throw new Error(
      `${relativePath}: unclosed namespace/section blocks: ` +
      JSON.stringify(blocks),
    );
  }
  interfaceDeclarationCache.set(relativePath, names);
  return names;
};

const hasLeanTheoremDeclaration = (relativePath, theoremName) => {
  return interfaceTheoremNames(relativePath).has(theoremName);
};

const compatibilityTranscriptPath = normalizeProjectRelativePath(
  comparatorMetadata.compatibility_probe.transcript,
  'verification.comparator.compatibility_probe.transcript',
);
const compatibilityTranscriptSha256 = crypto
  .createHash('sha256')
  .update(fs.readFileSync(compatibilityTranscriptPath))
  .digest('hex');
if (
  compatibilityTranscriptSha256 !==
  comparatorMetadata.compatibility_probe.transcript_sha256
) {
  throw new Error(
    'Comparator compatibility-probe transcript SHA-256 mismatch: ' +
    `expected ${comparatorMetadata.compatibility_probe.transcript_sha256}, ` +
    `got ${compatibilityTranscriptSha256}`,
  );
}

const comparatorFiles = [...comparatorMetadata.fileset].sort(binaryCompare);
const comparatorDigest = crypto.createHash('sha256');
for (const relativePath of comparatorFiles) {
  const absolutePath = normalizeProjectRelativePath(
    relativePath,
    'verification.comparator.fileset entry',
  );
  comparatorDigest.update(relativePath);
  comparatorDigest.update('\0');
  comparatorDigest.update(fs.readFileSync(absolutePath));
  comparatorDigest.update('\0');
}
const comparatorDigestSha256 = comparatorDigest.digest('hex');

const configuredComparatorEvidenceFiles = [
  ...comparatorMetadata.configurations,
  ...comparatorMetadata.historical_configurations,
]
  .map((run, index) => {
    const relativePath = run.evidence_record ?? null;
    if (relativePath === null) {
      return null;
    }
    requireNonemptyString(
      relativePath,
      `verification.comparator.configurations[${index}].evidence_record`,
    );
    if (
      path.posix.dirname(relativePath) !== 'comparator/evidence' ||
      path.posix.extname(relativePath) !== '.json'
    ) {
      throw new Error(
        'Comparator evidence records must be JSON files directly under ' +
        'comparator/evidence/',
      );
    }
    return relativePath;
  })
  .filter(relativePath => relativePath !== null);
const uniqueConfiguredComparatorEvidenceFiles = [
  ...new Set(configuredComparatorEvidenceFiles),
].sort(binaryCompare);
const comparatorEvidenceDirectory = path.join(
  projectRoot,
  'comparator/evidence',
);
const comparatorEvidenceDirectoryStat = fs.lstatSync(
  comparatorEvidenceDirectory,
);
if (
  comparatorEvidenceDirectoryStat.isSymbolicLink() ||
  !comparatorEvidenceDirectoryStat.isDirectory()
) {
  throw new Error('comparator/evidence must be an ordinary directory');
}
const actualComparatorEvidenceFiles = fs
  .readdirSync(comparatorEvidenceDirectory, {withFileTypes: true})
  .map(entry => {
    if (entry.isSymbolicLink() || !entry.isFile()) {
      throw new Error(
        `comparator/evidence contains a non-ordinary file: ${entry.name}`,
      );
    }
    return `comparator/evidence/${entry.name}`;
  })
  .sort(binaryCompare);
if (
  JSON.stringify(actualComparatorEvidenceFiles) !==
  JSON.stringify(uniqueConfiguredComparatorEvidenceFiles)
) {
  throw new Error(
    'comparator/evidence must contain exactly the configured historical ' +
    'evidence records; release evidence is external to the source snapshot',
  );
}

const foundationalAxioms = auditConfig.editorial.axioms;
const comparatorConfigurationPaths = new Set();
const parsedComparatorConfigurations = [];
for (const [index, run] of comparatorMetadata.configurations.entries()) {
  requirePlainObject(run, `verification.comparator.configurations[${index}]`);
  const configPath = requireNonemptyString(
    run.path,
    `verification.comparator.configurations[${index}].path`,
  );
  if (comparatorConfigurationPaths.has(configPath)) {
    throw new Error(`duplicate Comparator configuration path: ${configPath}`);
  }
  comparatorConfigurationPaths.add(configPath);
  if (!comparatorMetadata.fileset.includes(configPath)) {
    throw new Error(
      `Comparator configuration is outside comparator fileset: ${configPath}`,
    );
  }
  if (
    JSON.stringify(Object.keys(run).sort(binaryCompare)) !==
    JSON.stringify(['path'])
  ) {
    throw new Error(
      `source-snapshot Comparator configuration must contain only path: ` +
      configPath,
    );
  }

  const configAbsolutePath = normalizeProjectRelativePath(
    configPath,
    `verification.comparator.configurations[${index}].path`,
  );
  let comparatorConfig;
  try {
    comparatorConfig = JSON.parse(fs.readFileSync(configAbsolutePath, 'utf8'));
  } catch (error) {
    throw new Error(`${configPath} is not valid JSON: ${error.message}`);
  }
  requirePlainObject(comparatorConfig, `Comparator configuration ${configPath}`);
  for (const field of ['challenge_module', 'solution_module']) {
    requireNonemptyString(comparatorConfig[field], `${configPath}.${field}`);
  }
  requireUniqueStringArray(
    comparatorConfig.theorem_names,
    `${configPath}.theorem_names`,
  );
  requireUniqueStringArray(
    comparatorConfig.permitted_axioms,
    `${configPath}.permitted_axioms`,
  );
  if (
    JSON.stringify(comparatorConfig.permitted_axioms) !==
    JSON.stringify(foundationalAxioms)
  ) {
    throw new Error(
      `${configPath} permitted_axioms must exactly equal the configured ` +
      'explicit foundational allowlist',
    );
  }
  if (typeof comparatorConfig.enable_nanoda !== 'boolean') {
    throw new Error(`${configPath} has an invalid enable_nanoda`);
  }
  if (
    comparatorConfig.enable_nanoda &&
    !comparatorMetadata.tools.nanoda.installed
  ) {
    throw new Error(`${configPath} enables nanoda, but nanoda is not installed`);
  }

  const challengePath = leanModulePath(
    comparatorConfig.challenge_module,
    `${configPath}.challenge_module`,
  );
  const solutionPath = leanModulePath(
    comparatorConfig.solution_module,
    `${configPath}.solution_module`,
  );
  for (const modulePath of [challengePath, solutionPath]) {
    if (!comparatorMetadata.fileset.includes(modulePath)) {
      throw new Error(
        `${configPath} module is outside comparator fileset: ${modulePath}`,
      );
    }
  }
  for (const theoremName of comparatorConfig.theorem_names) {
    for (const modulePath of [challengePath, solutionPath]) {
      if (!hasLeanTheoremDeclaration(modulePath, theoremName)) {
        throw new Error(
          `${configPath} target ${theoremName} is not declared in ${modulePath}`,
        );
      }
    }
  }
  const configSha256 = crypto
    .createHash('sha256')
    .update(fs.readFileSync(configAbsolutePath))
    .digest('hex');
  parsedComparatorConfigurations.push({
    ...comparatorConfig,
    path: configPath,
    sha256: configSha256,
    source_snapshot_comparator_state:
      comparatorMetadata.source_snapshot_comparator_state,
    challenge_file: challengePath,
    solution_file: solutionPath,
  });
}

const currentComparatorConfigurationByPath = new Map(
  parsedComparatorConfigurations.map(config => [config.path, config]),
);
const historicalComparatorConfigurationPaths = new Set();
const parsedHistoricalComparatorConfigurations = [];
let historicalComparatorSourceCommit = null;
let historicalComparatorFilesetDigest = null;
for (const [index, run] of
  comparatorMetadata.historical_configurations.entries()) {
  const label = `verification.comparator.historical_configurations[${index}]`;
  requirePlainObject(run, label);
  const configPath = requireNonemptyString(run.path, `${label}.path`);
  if (historicalComparatorConfigurationPaths.has(configPath)) {
    throw new Error(`duplicate historical Comparator configuration: ${configPath}`);
  }
  historicalComparatorConfigurationPaths.add(configPath);
  const currentConfig = currentComparatorConfigurationByPath.get(configPath);
  if (currentConfig === undefined) {
    throw new Error(
      `historical Comparator configuration has no current counterpart: ` +
      configPath,
    );
  }
  if (run.status !== 'sandboxed_lean_kernel_passed' || run.sandboxed !== true) {
    throw new Error(
      `historical Comparator configuration is not a recorded hardened pass: ` +
      configPath,
    );
  }
  const evidenceRecordRelativePath = requireNonemptyString(
    run.evidence_record,
    `${label}.evidence_record`,
  );
  const evidenceRecordAbsolutePath = normalizeProjectRelativePath(
    evidenceRecordRelativePath,
    `${label}.evidence_record`,
  );
  const evidenceRecordBytes = fs.readFileSync(evidenceRecordAbsolutePath);
  const evidenceRecordSha256 = crypto
    .createHash('sha256')
    .update(evidenceRecordBytes)
    .digest('hex');
  if (
    !/^[0-9a-f]{64}$/.test(run.evidence_record_sha256 ?? '') ||
    evidenceRecordSha256 !== run.evidence_record_sha256
  ) {
    throw new Error(
      `historical Comparator evidence-record SHA-256 mismatch for ${configPath}`,
    );
  }
  let evidenceRecord;
  try {
    evidenceRecord = JSON.parse(
      new TextDecoder('utf-8', {fatal: true}).decode(evidenceRecordBytes),
    );
  } catch (error) {
    throw new Error(
      `historical Comparator evidence record is invalid for ${configPath}: ` +
      error.message,
    );
  }
  const transcriptInPrivateRawArchive = requireNonemptyString(
    run.transcript_in_private_raw_archive,
    `${label}.transcript_in_private_raw_archive`,
  );
  if (
    !transcriptInPrivateRawArchive.startsWith('evidence/') ||
    path.posix.extname(transcriptInPrivateRawArchive) !== '.txt' ||
    !/^[0-9a-f]{64}$/.test(run.transcript_sha256 ?? '') ||
    !/^[0-9a-f]{64}$/.test(run.configuration_sha256_at_run ?? '') ||
    !/^[0-9a-f]{64}$/.test(
      run.comparator_fileset_digest_sha256_at_run ?? '',
    )
  ) {
    throw new Error(`invalid historical Comparator metadata for ${configPath}`);
  }
  if (
    run.configuration_sha256_at_run !== currentConfig.sha256 ||
    evidenceRecord.status !== run.status ||
    evidenceRecord.certifying !== true ||
    evidenceRecord.sandboxed !== true ||
    evidenceRecord.non_root !== true ||
    JSON.stringify(evidenceRecord.kernels) !== JSON.stringify(['lean']) ||
    evidenceRecord.enable_nanoda !== false ||
    evidenceRecord.exit_code !== 0 ||
    evidenceRecord.config !== configPath ||
    evidenceRecord.configuration_sha256 !== run.configuration_sha256_at_run ||
    evidenceRecord.comparator_fileset_digest_sha256 !==
      run.comparator_fileset_digest_sha256_at_run ||
    evidenceRecord.transcript !==
      path.posix.basename(transcriptInPrivateRawArchive) ||
    evidenceRecord.transcript_sha256 !== run.transcript_sha256
  ) {
    throw new Error(
      `historical Comparator evidence record is inconsistent for ${configPath}`,
    );
  }
  if (!/^[0-9a-f]{40}$/.test(evidenceRecord.paper_c_commit ?? '')) {
    throw new Error(
      `historical Comparator evidence has an invalid Paper C commit: ` +
      configPath,
    );
  }
  if (
    historicalComparatorSourceCommit !== null &&
    historicalComparatorSourceCommit !== evidenceRecord.paper_c_commit
  ) {
    throw new Error('historical Comparator records disagree on the source commit');
  }
  historicalComparatorSourceCommit = evidenceRecord.paper_c_commit;
  if (
    historicalComparatorFilesetDigest !== null &&
    historicalComparatorFilesetDigest !==
      run.comparator_fileset_digest_sha256_at_run
  ) {
    throw new Error('historical Comparator records disagree on the fileset digest');
  }
  historicalComparatorFilesetDigest =
    run.comparator_fileset_digest_sha256_at_run;
  parsedHistoricalComparatorConfigurations.push({
    ...run,
    evidence_record_sha256: evidenceRecordSha256,
  });
}
if (
  historicalPublishedComparatorEvidence.paper_c_commit !==
    historicalComparatorSourceCommit ||
  historicalPublishedComparatorEvidence.comparator_fileset_digest_sha256 !==
    historicalComparatorFilesetDigest
) {
  throw new Error(
    'historical published evidence does not match the historical Comparator ' +
    'records',
  );
}
if (
  path.basename(historicalPublishedComparatorEvidence.archive) !==
    historicalPublishedComparatorEvidence.archive ||
  !historicalPublishedComparatorEvidence.release_url.endsWith(
    `/tag/${historicalPublishedComparatorEvidence.release_tag}`,
  )
) {
  throw new Error(
    'published hardened evidence has an invalid archive or release URL',
  );
}

const comparatorConfigByPath = new Map(
  parsedComparatorConfigurations.map(config => [config.path, config]),
);
const placeholderKeys = new Set();
const placeholderCountByFile = auditConfig.challenge_placeholders.reduce(
  (counts, placeholder) => {
    if (placeholder !== null && typeof placeholder === 'object') {
      counts.set(placeholder.file, (counts.get(placeholder.file) ?? 0) + 1);
    }
    return counts;
  },
  new Map(),
);
for (const [index, placeholder] of auditConfig.challenge_placeholders.entries()) {
  requirePlainObject(placeholder, `challenge_placeholders[${index}]`);
  const relativePath = requireNonemptyString(
    placeholder.file,
    `challenge_placeholders[${index}].file`,
  );
  const declarationName = requireNonemptyString(
    placeholder.declaration,
    `challenge_placeholders[${index}].declaration`,
  );
  if (placeholder.token !== 'by sorry' || placeholder.count !== 1) {
    throw new Error(
      `${relativePath}: Comparator placeholder must record exactly one by sorry`,
    );
  }
  const key = `${relativePath}\0${declarationName}`;
  if (placeholderKeys.has(key)) {
    throw new Error(`duplicate challenge placeholder: ${declarationName}`);
  }
  placeholderKeys.add(key);
  if (!comparatorMetadata.fileset.includes(relativePath)) {
    throw new Error(`challenge placeholder is outside comparator fileset: ${relativePath}`);
  }
  if (!hasLeanTheoremDeclaration(relativePath, declarationName)) {
    throw new Error(
      `${relativePath}: challenge placeholder declaration not found: ` +
      declarationName,
    );
  }
  const source = fs.readFileSync(path.join(projectRoot, relativePath), 'utf8');
  const actualCount = source.split(placeholder.token).length - 1;
  const configuredCount = placeholderCountByFile.get(relativePath);
  if (actualCount !== configuredCount) {
    throw new Error(
      `${relativePath}: expected ${configuredCount} ${placeholder.token} ` +
      `placeholder, found ${actualCount}`,
    );
  }
  if (
    !parsedComparatorConfigurations.some(config =>
      config.challenge_file === relativePath &&
      config.theorem_names.includes(declarationName),
    )
  ) {
    throw new Error(
      `${relativePath}: placeholder ${declarationName} is not a Comparator target`,
    );
  }
}

for (const config of parsedComparatorConfigurations) {
  for (const theoremName of config.theorem_names) {
    const key = `${config.challenge_file}\0${theoremName}`;
    if (!placeholderKeys.has(key)) {
      throw new Error(
        `${config.path}: target ${theoremName} has no recorded challenge placeholder`,
      );
    }
  }
}

const theoremRecordByName = new Map(
  theoremRecords.map(record => [record.name, record]),
);
const paperItemIds = new Set();
const validatedPaperItems = [];
for (const [index, item] of auditConfig.paper_items.entries()) {
  requirePlainObject(item, `paper_items[${index}]`);
  const itemId = requireNonemptyString(item.id, `paper_items[${index}].id`);
  if (paperItemIds.has(itemId)) {
    throw new Error(`duplicate paper item id: ${itemId}`);
  }
  paperItemIds.add(itemId);
  requirePlainObject(item.paper_locator, `paper_items[${index}].paper_locator`);
  for (const field of ['result', 'pages', 'edition']) {
    requireNonemptyString(
      item.paper_locator[field],
      `paper_items[${index}].paper_locator.${field}`,
    );
  }
  if (!sourceKeys.has(item.paper_locator.edition)) {
    throw new Error(
      `paper item ${itemId} has unknown edition ${item.paper_locator.edition}`,
    );
  }
  if (
    !Array.isArray(item.lean_declarations) ||
    item.lean_declarations.length === 0
  ) {
    throw new Error(`paper item ${itemId} has no Lean declarations`);
  }
  const itemDeclarationNames = new Set();
  const computedBridgeIds = new Set();
  for (const [declarationIndex, declaration] of
    item.lean_declarations.entries()) {
    requirePlainObject(
      declaration,
      `paper_items[${index}].lean_declarations[${declarationIndex}]`,
    );
    requireNonemptyString(
      declaration.name,
      `paper_items[${index}].lean_declarations[${declarationIndex}].name`,
    );
    requireNonemptyString(
      declaration.file,
      `paper_items[${index}].lean_declarations[${declarationIndex}].file`,
    );
    if (itemDeclarationNames.has(declaration.name)) {
      throw new Error(
        `paper item ${itemId} repeats declaration ${declaration.name}`,
      );
    }
    itemDeclarationNames.add(declaration.name);
    const record = theoremRecordByName.get(declaration.name);
    if (record === undefined) {
      throw new Error(
        `paper item ${itemId} has unknown declaration ${declaration.name}`,
      );
    }
    if (record.source !== declaration.file) {
      throw new Error(
        `paper item ${itemId} maps ${declaration.name} to ` +
        `${declaration.file}, but it is declared in ${record.source}`,
      );
    }
    for (const bridgeId of record.hypotheses) {
      computedBridgeIds.add(bridgeId);
    }
  }
  if (item.main_result_declaration !== undefined) {
    requireNonemptyString(
      item.main_result_declaration,
      `paper_items[${index}].main_result_declaration`,
    );
    if (!itemDeclarationNames.has(item.main_result_declaration)) {
      throw new Error(
        `paper item ${itemId} has a main-result declaration outside its ` +
        `lean_declarations: ${item.main_result_declaration}`,
      );
    }
  }
  requireUniqueStringArray(
    item.bridge_ids,
    `paper_items[${index}].bridge_ids`,
    {allowEmpty: true},
  );
  for (const bridgeId of item.bridge_ids) {
    if (!bridgeById.has(bridgeId)) {
      throw new Error(`paper item ${itemId} has unknown bridge ${bridgeId}`);
    }
  }
  const declaredBridges = [...item.bridge_ids].sort(binaryCompare);
  const computedBridges = [...computedBridgeIds].sort(binaryCompare);
  if (JSON.stringify(declaredBridges) !== JSON.stringify(computedBridges)) {
    throw new Error(
      `paper item ${itemId} bridge mismatch: configured ` +
      `${JSON.stringify(declaredBridges)}, computed ` +
      `${JSON.stringify(computedBridges)}`,
    );
  }
  const computedConditionality =
    computedBridges.length === 0 ? 'inconditionnel' : 'conditionnel';
  if (item.conditionality !== computedConditionality) {
    throw new Error(
      `paper item ${itemId} conditionality mismatch: configured ` +
      `${item.conditionality}, computed ${computedConditionality}`,
    );
  }
  requireNonemptyString(
    item.formalization_status,
    `paper_items[${index}].formalization_status`,
  );
  requirePlainObject(item.comparator, `paper_items[${index}].comparator`);
  if (typeof item.comparator.covered !== 'boolean') {
    throw new Error(`paper item ${itemId} has an invalid Comparator coverage flag`);
  }
  const expectedPaperItemComparatorKeys = item.comparator.covered
    ? [
        'configuration',
        'covered',
        'source_snapshot_comparator_state',
        'theorem_name',
      ]
    : ['covered'];
  if (
    JSON.stringify(Object.keys(item.comparator).sort(binaryCompare)) !==
    JSON.stringify(expectedPaperItemComparatorKeys)
  ) {
    throw new Error(
      `paper item ${itemId} has unexpected Comparator metadata fields`,
    );
  }
  let comparatorRecord = {covered: false};
  if (item.comparator.covered) {
    const configPath = requireNonemptyString(
      item.comparator.configuration,
      `paper_items[${index}].comparator.configuration`,
    );
    const theoremName = requireNonemptyString(
      item.comparator.theorem_name,
      `paper_items[${index}].comparator.theorem_name`,
    );
    const comparatorConfig = comparatorConfigByPath.get(configPath);
    if (comparatorConfig === undefined) {
      throw new Error(
        `paper item ${itemId} has unknown Comparator configuration ${configPath}`,
      );
    }
    if (!comparatorConfig.theorem_names.includes(theoremName)) {
      throw new Error(
        `paper item ${itemId} target ${theoremName} is absent from ` +
        `${configPath} theorem_names`,
      );
    }
    if (
      item.comparator.source_snapshot_comparator_state !==
      comparatorConfig.source_snapshot_comparator_state
    ) {
      throw new Error(
        `paper item ${itemId} Comparator source-snapshot state differs from ` +
        configPath,
      );
    }
    comparatorRecord = {
      ...item.comparator,
      configuration_sha256: comparatorConfig.sha256,
      challenge_module: comparatorConfig.challenge_module,
      solution_module: comparatorConfig.solution_module,
      enable_nanoda: comparatorConfig.enable_nanoda,
    };
  }
  validatedPaperItems.push({
    ...item,
    bridge_ids: declaredBridges,
    comparator: comparatorRecord,
  });
}

const validatedPaperItemById = new Map(
  validatedPaperItems.map(item => [item.id, item]),
);
const formalizationMainResultItems =
  auditConfig.editorial.main_result_item_ids.map(itemId => {
    const item = validatedPaperItemById.get(itemId);
    if (item === undefined) {
      throw new Error(`unknown editorial main-result paper item id: ${itemId}`);
    }
    if (!item.comparator.covered && item.main_result_declaration === undefined) {
      throw new Error(
        `editorial main-result paper item lacks an explicit representative ` +
        `declaration: ${itemId}`,
      );
    }
    return item;
  });

const theoremOneOneBridgeIds = [
  'AGG89-T1-finite-dependency-b3-zero',
  'ES86-T1b-Q-split-n2',
  'NR83-T1-divisor-log-bound',
].sort(binaryCompare);
const finiteTheoremOneOneItem = validatedPaperItems.find(
  item => item.id === 'Thm-1.1-finite-cylinder',
);
if (
  finiteTheoremOneOneItem === undefined ||
  JSON.stringify(finiteTheoremOneOneItem.bridge_ids) !==
    JSON.stringify(theoremOneOneBridgeIds)
) {
  throw new Error(
    'Thm-1.1-finite-cylinder must consume exactly the three configured open ' +
    'literature bridges',
  );
}
if (
  !paperItemIds.has('Thm-1.1-infinite-finite-law-transfer')
) {
  throw new Error('paper item mapping is missing the infinite/finite law transfer');
}

for (const config of parsedComparatorConfigurations) {
  for (const theoremName of config.theorem_names) {
    if (
      !validatedPaperItems.some(item =>
        item.comparator.covered &&
        item.comparator.configuration === config.path &&
        item.comparator.theorem_name === theoremName,
      )
    ) {
      throw new Error(
        `${config.path} target ${theoremName} is not mapped to a paper item`,
      );
    }
  }
}

const formalizationCertificateSummary = certificate => ({
  file: certificate.file,
  sha256: certificate.sha256,
  source_locator: certificate.source_locator,
  review_status: certificate.review_status,
  implication_status: certificate.implication_status,
  human_peer_reviewed: certificate.human_peer_reviewed,
});

const formalizationMainResults = formalizationMainResultItems.map(item => {
  const comparatorConfig = item.comparator.covered
    ? comparatorConfigByPath.get(item.comparator.configuration)
    : null;
  const representativeDeclaration = item.comparator.covered
    ? null
    : item.lean_declarations.find(
      declaration => declaration.name === item.main_result_declaration,
    );
  return {
    paper_item_id: item.id,
    declaration: item.comparator.covered
      ? item.comparator.theorem_name
      : representativeDeclaration.name,
    file: item.comparator.covered
      ? comparatorConfig.solution_file
      : representativeDeclaration.file,
    sorry_count: 0,
    axioms: foundationalAxioms,
    comparator_config: item.comparator.covered
      ? item.comparator.configuration
      : '',
    source_snapshot_comparator_state: item.comparator.covered
      ? item.comparator.source_snapshot_comparator_state
      : 'not_configured',
    literature_dependencies: item.bridge_ids
      .map(bridgeId => bridgeById.get(bridgeId))
      .filter(bridge => bridge.kind === 'external' && bridge.status === 'open')
      .map(bridge => {
        const certificate = literatureCertificateByBridgeId.get(bridge.id);
        return {
          statement: certificate === undefined
            ? bridge.formalization_relation
            : effectiveFormalizationRelation(bridge, certificate),
          ...(certificate === undefined
            ? {}
            : {
                source_to_lean_status:
                  effectiveSourceToLeanStatus(certificate),
              }),
          source: literatureSourceIdByBridgeId.get(bridge.id),
          source_locator: citationLabel(bridge),
          ...(citationLabel(bridge) === registeredCitationLabel(bridge)
            ? {}
            : {
                registered_frozen_source_locator:
                  registeredCitationLabel(bridge),
              }),
          bridge_id: bridge.id,
          lean_name: bridge.lean_name,
          ...(certificate === undefined
            ? {}
            : {
                certificate: formalizationCertificateSummary(certificate),
              }),
        };
      }),
  };
});

const formalization = {
  version: formalizationTemplate.version,
  schema_extensions: {
    paper_c_audit: 4,
  },
  project: {
    name: auditConfig.project.name,
    authors: auditConfig.project.authors,
    license: auditConfig.project.license,
    concept_doi: auditConfig.project.concept_doi,
    release: versionMatch[1],
  },
  sources: auditConfig.sources.map(({key: _key, ...source}) => source),
  status: {
    scope: auditConfig.editorial.scope,
    paper_item_completeness_note:
      `This release maps ${validatedPaperItems.length} paper items. ` +
      auditConfig.editorial.paper_item_completeness_note,
    sorry_count: 0,
    sorry_in_definitions: 0,
    axioms: foundationalAxioms,
    main_results: formalizationMainResults,
    comparator_interface_placeholders: auditConfig.challenge_placeholders.map(
      placeholder => ({
        ...placeholder,
        excluded_from_proof_sorry_count: true,
      }),
    ),
    source_snapshot_comparator_configurations:
      parsedComparatorConfigurations.map(config => ({
      configuration: config.path,
      source_snapshot_comparator_state:
        config.source_snapshot_comparator_state,
      enable_nanoda: config.enable_nanoda,
    })),
    release_evidence_state: comparatorMetadata.release_evidence_state,
    release_evidence_location: comparatorMetadata.release_evidence_location,
    packaging_commit_required: comparatorMetadata.packaging_commit_required,
    literature_certificates: {
      scope: literatureCertificateMetadata.scope,
      review_status: literatureCertificateMetadata.review_status,
      human_peer_reviewed: literatureCertificateMetadata.human_peer_reviewed,
      status_note: literatureCertificateMetadata.status_note,
      fileset: literatureCertificateFiles,
      digest_sha256: literatureCertificateDigestSha256,
      entries: parsedLiteratureCertificates,
      historical_closure_notes: historicalLiteratureClosureNotes,
      documentation_fileset: literatureDocumentationFiles,
      documentation_digest_sha256: literatureDocumentationDigestSha256,
    },
    historical_comparator_runs: parsedHistoricalComparatorConfigurations,
  },
  automation: auditConfig.editorial.automation,
  fidelity: auditConfig.editorial.fidelity,
  review: auditConfig.editorial.review,
  alignment: {
    namespace: 'PaperC',
    statements: validatedPaperItems.map(item => ({
      id: item.id,
      source:
        `${item.paper_locator.result}, p. ${item.paper_locator.pages} ` +
        `(${item.paper_locator.edition})`,
      lean: item.lean_declarations.map(declaration => declaration.name).join('; '),
      module: item.lean_declarations.map(declaration => declaration.file).join('; '),
      status: item.formalization_status,
      conditionality: item.conditionality,
      bridge_ids: item.bridge_ids,
      comparator_covered: item.comparator.covered,
      comparator_config: item.comparator.covered
        ? item.comparator.configuration
        : '',
      source_snapshot_comparator_state: item.comparator.covered
        ? item.comparator.source_snapshot_comparator_state
        : 'not_configured',
      note: item.note,
    })),
  },
  verification: {
    formalization_template: formalizationTemplate,
    toolchain: configuredToolchain,
    comparator: {
      source_snapshot_comparator_state:
        comparatorMetadata.source_snapshot_comparator_state,
      release_evidence_state: comparatorMetadata.release_evidence_state,
      release_evidence_location: comparatorMetadata.release_evidence_location,
      packaging_commit_required: comparatorMetadata.packaging_commit_required,
      state_note: comparatorMetadata.state_note,
      tools: comparatorMetadata.tools,
      compatibility_probe: comparatorMetadata.compatibility_probe,
      fileset: comparatorFiles,
      digest_sha256: comparatorDigestSha256,
      historical_published_evidence:
        historicalPublishedComparatorEvidence,
      historical_configurations: parsedHistoricalComparatorConfigurations,
      configurations: parsedComparatorConfigurations.map(config => ({
        path: config.path,
        sha256: config.sha256,
        challenge_module: config.challenge_module,
        solution_module: config.solution_module,
        theorem_names: config.theorem_names,
        permitted_axioms: config.permitted_axioms,
        enable_nanoda: config.enable_nanoda,
        source_snapshot_comparator_state:
          config.source_snapshot_comparator_state,
      })),
    },
    literature_certificates: {
      scope: literatureCertificateMetadata.scope,
      review_status: literatureCertificateMetadata.review_status,
      human_peer_reviewed: literatureCertificateMetadata.human_peer_reviewed,
      status_note: literatureCertificateMetadata.status_note,
      fileset: literatureCertificateFiles,
      digest_sha256: literatureCertificateDigestSha256,
      entries: parsedLiteratureCertificates,
      historical_closure_notes: historicalLiteratureClosureNotes,
      documentation_fileset: literatureDocumentationFiles,
      documentation_digest_sha256: literatureDocumentationDigestSha256,
    },
  },
  acknowledgements:
    'Built on Lean 4 and Mathlib. External literature dependencies are ' +
    'identified by stable bridge ids in audit_manifest.json.',
};

const yamlKey = key =>
  /^[A-Za-z_][A-Za-z0-9_-]*$/.test(key) ? key : JSON.stringify(key);

const yamlScalar = value => {
  if (value === null) {
    return 'null';
  }
  if (typeof value === 'string') {
    return JSON.stringify(value);
  }
  if (typeof value === 'number' || typeof value === 'boolean') {
    return String(value);
  }
  throw new Error(`cannot serialize YAML scalar of type ${typeof value}`);
};

function renderYaml(value, indentation = 0) {
  const prefix = ' '.repeat(indentation);
  if (Array.isArray(value)) {
    if (value.length === 0) {
      return [`${prefix}[]`];
    }
    return value.flatMap(item => {
      if (
        item === null ||
        ['string', 'number', 'boolean'].includes(typeof item)
      ) {
        return [`${prefix}- ${yamlScalar(item)}`];
      }
      if (Array.isArray(item) && item.length === 0) {
        return [`${prefix}- []`];
      }
      if (isPlainObject(item) && Object.keys(item).length === 0) {
        return [`${prefix}- {}`];
      }
      return [`${prefix}-`, ...renderYaml(item, indentation + 2)];
    });
  }
  if (isPlainObject(value)) {
    if (Object.keys(value).length === 0) {
      return [`${prefix}{}`];
    }
    return Object.entries(value).flatMap(([key, item]) => {
      const field = `${prefix}${yamlKey(key)}:`;
      if (
        item === null ||
        ['string', 'number', 'boolean'].includes(typeof item)
      ) {
        return [`${field} ${yamlScalar(item)}`];
      }
      if (Array.isArray(item) && item.length === 0) {
        return [`${field} []`];
      }
      if (isPlainObject(item) && Object.keys(item).length === 0) {
        return [`${field} {}`];
      }
      return [field, ...renderYaml(item, indentation + 2)];
    });
  }
  return [`${prefix}${yamlScalar(value)}`];
}

const formalizationContent = [
  `# Generated deterministically from audit_config.json schema ${auditConfig.schema_version}.`,
  '# Schema v0.3: https://github.com/mathlib-initiative/formalization.yaml',
  `# Template commit: ${formalizationTemplate.commit}`,
  ...renderYaml(formalization),
  '',
].join('\n');

const bridgeRegistryStart = '<!-- BEGIN GENERATED BRIDGE REGISTRY -->';
const bridgeRegistryEnd = '<!-- END GENERATED BRIDGE REGISTRY -->';
const bridgeRegistryContent = [
  bridgeRegistryStart,
  '## Registre des ponts',
  '',
  '`#print axioms` ne détecte pas les hypothèses ordinaires passées en',
  'arguments. Ici, « inconditionnel » signifie uniquement « ne prend',
  'aucun pont enregistré comme prémisse utilisable ». Le présent registre est distinct',
  'de la liste blanche fondationnelle.',
  '',
  'Un pont `external` renvoie à une source publiée indépendante et peut être',
  'contrôlé par citation. Un pont `internal` renvoie au manuscrit cible',
  'lui-même. Cette nature décrit la provenance, et non l’état de la',
  'formalisation.',
  '',
  'Le statut `open` signale un pont qui reste à fournir comme entrée dans',
  'l’API canonique ou dans une couche inférieure. Le statut `discharged`',
  'signale qu’une construction Lean publique le décharge dans l’API canonique;',
  'son interface peut rester exposée pour compatibilité historique. Ce statut',
  'porte sur le projet dans son ensemble : un ancien théorème peut donc encore',
  'prendre explicitement un pont `discharged` comme prémisse.',
  '',
  'La couche de certificats bibliographiques rc2 est distincte de ces statuts',
  'Lean. Elle documente une contre-expertise source→proposition faite par des',
  'agents, sans constituer une preuve du noyau ni une revue humaine indépendante.',
  'Pour les trois ponts ouverts de Theorem 1.1, cette couche est la qualification',
  'documentaire courante et rend explicites les réserves conservées dans le cœur',
  'audité. Le fichier HK13 distinct est une note historique de clôture, et non',
  'un certificat actif ni une prémisse de cet endpoint.',
  '',
  `Ponts enregistrés : ${bridges.length}. Théorèmes publics inconditionnels : ` +
    `${unconditionalTheoremCount}. Théorèmes publics conditionnels : ` +
    `${conditionalTheoremCount}.`,
  `Répartition des ponts par provenance : ${hypothesisKindCounts.external} external, ` +
    `${hypothesisKindCounts.internal} internal. Théorèmes conditionnels par ` +
    `nature de pont (un théorème mixte compterait dans chaque catégorie) : ` +
    `${conditionalTheoremCountsByHypothesisKind.external} external, ` +
    `${conditionalTheoremCountsByHypothesisKind.internal} internal.`,
  `Répartition des ponts par statut : ${hypothesisStatusCounts.open} open, ` +
    `${hypothesisStatusCounts.discharged} discharged. Théorèmes conditionnels ` +
    `par statut de pont (un théorème mixte compterait dans chaque catégorie) : ` +
    `${conditionalTheoremCountsByHypothesisStatus.open} open, ` +
    `${conditionalTheoremCountsByHypothesisStatus.discharged} discharged.`,
  '',
  '| Identifiant | Nature | Statut | Proposition Lean | Déchargé par | Documentation rc2 | Source primaire | Localisation |',
  '|---|---|---|---|---|---|---|---|',
  ...bridges.map(bridge =>
    `| \`${bridge.id}\` | \`${bridge.kind}\` | \`${bridge.status}\` | ` +
    `\`${bridge.lean_name}\` | ` +
    `${bridge.discharged_by === undefined
      ? '—'
      : bridge.discharged_by.map(name => `\`${name}\``).join('<br>')} | ` +
    `${literatureCertificateByBridgeId.has(bridge.id)
      ? (() => {
          const certificate = literatureCertificateByBridgeId.get(bridge.id);
          return `[\`${effectiveSourceToLeanStatus(certificate)}\`](${certificate.file})`;
        })()
      : historicalLiteratureClosureNoteByBridgeId.has(bridge.id)
        ? (() => {
            const note = historicalLiteratureClosureNoteByBridgeId.get(bridge.id);
            return `[\`historical_closure_note\`](${note.file})`;
          })()
        : '—'} | ` +
    `${bridge.citation.authors.join(', ')}, *${bridge.citation.title}*, ` +
    `${currentSourceLocator(bridge)} | ${bridge.manuscript_locator.result} |`,
  ),
  '',
  '### Transcriptions sources à contrôler',
  '',
  ...bridges.flatMap(bridge => {
    const certificate = literatureCertificateByBridgeId.get(bridge.id);
    const displayedFormulas =
      bridge.source_statement.displayed_formulas &&
      typeof bridge.source_statement.displayed_formulas === 'object'
        ? Object.entries(bridge.source_statement.displayed_formulas)
            .sort(([left], [right]) => binaryCompare(left, right))
            .map(([label, formula]) =>
              `  - \`${label}\` : \`${formula}\``,
            )
        : [];
    return [
      `#### \`${bridge.id}\``,
      '',
      `- Source : ${bridge.citation.authors.join(', ')}, ` +
        `*${bridge.citation.title}*, ${asSentence(currentSourceLocator(bridge))}`,
      ...(certificate !== undefined &&
          currentSourceLocator(bridge) !== bridge.citation.locator
        ? [
            `- Localisation enregistrée dans le cœur gelé : ` +
              `${bridge.citation.locator} (supplantée pour rc2).`,
          ]
        : []),
      `- Nature : \`${bridge.kind}\`.`,
      `- Statut : \`${bridge.status}\`.`,
      ...(bridge.discharged_by === undefined
        ? []
        : [
            '- Déchargé par : ' +
              bridge.discharged_by
                .map(name => `\`${name}\``)
                .join(', ') +
              '.',
          ]),
      `- Proposition Lean : \`${bridge.lean_name}\`.`,
      `- Relation de formalisation courante : ${asSentence(
        certificate === undefined
          ? bridge.formalization_relation
          : effectiveFormalizationRelation(bridge, certificate),
      )}`,
      `- Contrôle source courant : \`${certificate === undefined
        ? bridge.source_statement.verification
        : effectiveSourceToLeanStatus(certificate)}\`.`,
      ...(certificate === undefined
        ? []
        : [
            `- Wording de contrôle dans le cœur gelé : ` +
              `\`${bridge.source_statement.verification}\` (supplanté pour rc2).`,
          ]),
      ...(certificate !== undefined
        ? (() => {
            return [
              `- Qualification rc2 : \`${certificate.implication_status}\`; ` +
                `lecture primaire \`${certificate.primary_source_access}\`; ` +
                'pas de revue humaine indépendante.',
              `- Certificat rc2 : [\`${certificate.file}\`](${certificate.file}), ` +
                `SHA-256 \`${certificate.sha256}\`, ` +
                `${certificate.byte_length} octets.`,
              `- Limites rc2 : ${asSentence(certificate.limitations)}`,
            ];
          })()
        : []),
      ...(historicalLiteratureClosureNoteByBridgeId.has(bridge.id)
        ? (() => {
            const note = historicalLiteratureClosureNoteByBridgeId.get(bridge.id);
            return [
              `- Note historique de clôture : [\`${note.file}\`](${note.file}), ` +
                `SHA-256 \`${note.sha256}\`, ${note.byte_length} octets.`,
              `- Rôle courant : ${asSentence(note.note)}`,
            ];
          })()
        : []),
      ...(bridge.source_statement.verbatim_is_excerpt === true
        ? ['- Citation littérale : extrait (les formules structurées ci-dessous complètent la transcription).']
        : []),
      ...(bridge.source_statement.verification_note
        ? [certificate === undefined
            ? `- Note de vérification : ${asSentence(
                bridge.source_statement.verification_note,
              )}`
            : `- Note de vérification du cœur gelé (supplantée pour rc2) : ` +
              asSentence(bridge.source_statement.verification_note)]
        : []),
      ...(displayedFormulas.length === 0
        ? []
        : ['- Formules affichées transcrites :', ...displayedFormulas]),
      '',
      `> ${bridge.source_statement.verbatim}`,
      '',
    ];
  }),
  '### Conditionnalité de chaque théorème public',
  '',
  '| Théorème | Conditionnalité | Ponts requis | Nature(s) | Statut(s) des ponts | Source |',
  '|---|---|---|---|---|---|',
  ...theoremRecords.map(record =>
    `| \`${record.name}\` | ${record.conditionality} | ` +
    `${record.hypotheses.length === 0
      ? '—'
      : record.hypotheses.map(id => `\`${id}\``).join(', ')} | ` +
    `${record.hypotheses.length === 0
      ? '—'
      : [...new Set(record.hypotheses.map(id =>
          bridgeById.get(id).kind,
        ))].sort(binaryCompare).map(kind => `\`${kind}\``).join(', ')} | ` +
    `${record.hypotheses.length === 0
      ? '—'
      : [...new Set(record.hypotheses.map(id =>
          bridgeById.get(id).status,
        ))].sort(binaryCompare).map(status => `\`${status}\``).join(', ')} | ` +
    `\`${record.source}:${record.line}\` |`,
  ),
  bridgeRegistryEnd,
].join('\n');

function updateGeneratedBridgeRegistry(markdown) {
  const startIndex = markdown.indexOf(bridgeRegistryStart);
  const endIndex = markdown.indexOf(bridgeRegistryEnd);
  if ((startIndex === -1) !== (endIndex === -1)) {
    throw new Error('AXIOM_AUDIT.md has incomplete bridge registry markers');
  }
  if (startIndex !== -1) {
    if (endIndex < startIndex) {
      throw new Error('AXIOM_AUDIT.md bridge registry markers are reversed');
    }
    const afterEnd = endIndex + bridgeRegistryEnd.length;
    return (
      markdown.slice(0, startIndex) +
      bridgeRegistryContent +
      markdown.slice(afterEnd)
    );
  }
  const insertionMarker = '\n## Catalogue historique documenté';
  const insertionIndex = markdown.indexOf(insertionMarker);
  if (insertionIndex === -1) {
    throw new Error(
      'AXIOM_AUDIT.md is missing the bridge-registry insertion point',
    );
  }
  return (
    markdown.slice(0, insertionIndex) +
    `\n\n${bridgeRegistryContent}\n` +
    markdown.slice(insertionIndex)
  );
}

const currentAuditMarkdown = fs.readFileSync(auditMarkdownPath, 'utf8');
const auditMarkdownContent =
  updateGeneratedBridgeRegistry(currentAuditMarkdown);

const manifest = {
  schema_version: 10,
  project: 'paper_c_lean',
  project_metadata: auditConfig.project,
  project_version: versionMatch[1],
  target_pdf: auditConfig.target_pdf,
  source_pdf_fr: auditConfig.source_pdf_fr,
  sources: auditConfig.sources,
  audit_file: 'AuditCheck.lean',
  import: 'PaperC',
  core_source_base_version: coreSourceMetadata.base_version,
  core_source_fileset: coreSourceFileset,
  core_source_file_count: sourceFiles.length,
  source_fileset: coreSourceFileset,
  core_source_digest_sha256: digest,
  source_digest_sha256: digest,
  comparator_fileset: comparatorFiles,
  comparator_digest_sha256: comparatorDigestSha256,
  source_snapshot_comparator_state:
    comparatorMetadata.source_snapshot_comparator_state,
  release_evidence_state: comparatorMetadata.release_evidence_state,
  release_evidence_location: comparatorMetadata.release_evidence_location,
  packaging_commit_required: comparatorMetadata.packaging_commit_required,
  comparator_state_note: comparatorMetadata.state_note,
  comparator_tools: comparatorMetadata.tools,
  comparator_compatibility_probe: comparatorMetadata.compatibility_probe,
  comparator_historical_published_evidence:
    historicalPublishedComparatorEvidence,
  comparator_configurations: parsedComparatorConfigurations,
  comparator_historical_configurations:
    parsedHistoricalComparatorConfigurations,
  literature_certificate_fileset: literatureCertificateFiles,
  literature_certificate_digest_sha256:
    literatureCertificateDigestSha256,
  literature_certificate_scope: literatureCertificateMetadata.scope,
  literature_certificate_status_note:
    literatureCertificateMetadata.status_note,
  literature_certificates: parsedLiteratureCertificates,
  historical_literature_closure_notes: historicalLiteratureClosureNotes,
  literature_documentation_fileset: literatureDocumentationFiles,
  literature_documentation_digest_sha256:
    literatureDocumentationDigestSha256,
  formalization_template: formalizationTemplate,
  automation: auditConfig.editorial.automation,
  fidelity: auditConfig.editorial.fidelity,
  review: auditConfig.editorial.review,
  proof_sorry_count: 0,
  comparator_interface_sorry_count:
    auditConfig.challenge_placeholders.reduce(
      (sum, placeholder) => sum + placeholder.count,
      0,
    ),
  comparator_interface_placeholders: auditConfig.challenge_placeholders,
  paper_item_count: validatedPaperItems.length,
  paper_items: validatedPaperItems,
  selection: {
    include:
      'explicit public theorem or lemma declarations under namespace PaperC',
    exclude: [
      'private declarations',
      'local declarations',
      'definitions',
      'abbreviations',
      'instances',
      'structures/classes',
      'generated/internal declarations',
    ],
  },
  theorem_count: declarations.length,
  theorem_kind_counts: kindCounts,
  conditionality_scope: {
    meaning: 'registered external and internal bridge hypotheses',
    axiom_audit_detects_hypotheses: false,
    inconditionnel:
      'the theorem takes no registered bridge as a usable premise',
    conditionnel:
      'the theorem takes one or more registered external or internal bridges as usable premises',
    bridge_kinds: {
      external:
        'independently published source; reviewer validation is by citation against that source',
      internal:
        'target-manuscript source; this is provenance and does not by itself imply remaining formalization debt',
    },
    bridge_statuses: {
      open:
        'not yet discharged by a public Lean construction at the canonical API boundary',
      discharged:
        'discharged by one or more public Lean theorems; the bridge interface may remain for historical compatibility',
    },
  },
  hypothesis_count: bridges.length,
  hypothesis_kind_counts: hypothesisKindCounts,
  hypothesis_status_counts: hypothesisStatusCounts,
  hypotheses: publicBridgeEntries,
  unconditional_theorem_count: unconditionalTheoremCount,
  conditional_theorem_count: conditionalTheoremCount,
  conditional_theorem_counts_by_hypothesis_kind:
    conditionalTheoremCountsByHypothesisKind,
  conditional_theorem_counts_by_hypothesis_status:
    conditionalTheoremCountsByHypothesisStatus,
  theorem_records: theoremRecords,
  additional_target_count: additionalTargets.length,
  audit_target_count: auditTargetNames.length,
  audit_targets: auditTargetNames,
  theorems: declarations.map(declaration => declaration.name),
  additional_targets: additionalTargets,
};
const manifestContent = `${JSON.stringify(manifest, null, 2)}\n`;

function checkExact(filename, expected) {
  if (!fs.existsSync(filename)) {
    throw new Error(`${path.basename(filename)} is missing`);
  }
  const actual = fs.readFileSync(filename, 'utf8');
  if (actual !== expected) {
    throw new Error(
      `${path.basename(filename)} is stale; run ` +
      '`node scripts/generate_audit.mjs`',
    );
  }
}

if (checkOnly) {
  checkExact(auditPath, auditContent);
  checkExact(manifestPath, manifestContent);
  checkExact(formalizationPath, formalizationContent);
  checkExact(auditMarkdownPath, auditMarkdownContent);
} else {
  fs.writeFileSync(auditPath, auditContent);
  fs.writeFileSync(manifestPath, manifestContent);
  fs.writeFileSync(formalizationPath, formalizationContent);
  fs.writeFileSync(auditMarkdownPath, auditMarkdownContent);
}

process.stdout.write(
  `${declarations.length} public theorem/lemma declarations; ` +
  `${declarations.length + additionalTargets.length} audit targets; ` +
  `${bridges.length} registered bridges; ` +
  `${hypothesisStatusCounts.open} open and ` +
  `${hypothesisStatusCounts.discharged} discharged; ` +
  `${conditionalTheoremCount} conditional public theorems; ` +
  `${validatedPaperItems.length} mapped paper items; ` +
  `${parsedLiteratureCertificates.length} literature certificates ` +
  `(${literatureCertificateDigestSha256}); ` +
  `${parsedComparatorConfigurations.length} source-snapshot Comparator ` +
  'configurations (release evidence external to source snapshot); ' +
  `formalization ${formalizationTemplate.version}\n`,
);
