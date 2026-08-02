import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';

const argumentsSet = new Set(process.argv.slice(2));
const supportedArguments = new Set([
  '--check',
  '--check-pdfs',
  '--check-source-digest',
]);
for (const argument of argumentsSet) {
  if (!supportedArguments.has(argument)) {
    throw new Error(`unknown argument: ${argument}`);
  }
}
if (argumentsSet.size > 1) {
  throw new Error(
    '`--check`, `--check-pdfs`, and `--check-source-digest` are mutually exclusive',
  );
}

const checkOnly = argumentsSet.has('--check');
const checkPdfsOnly = argumentsSet.has('--check-pdfs');
const checkSourceDigestOnly = argumentsSet.has('--check-source-digest');
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
if (auditConfig.schema_version !== 2) {
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
  if (hasFilename !== hasSha256) {
    throw new Error(
      `audit_config.json sources[${index}] must provide filename and sha256 together`,
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
const comparatorMetadata = requirePlainObject(
  auditConfig.verification.comparator,
  'verification.comparator',
);
requireNonemptyString(
  comparatorMetadata.status,
  'verification.comparator.status',
);
if (![
  'not_run',
  'failed',
  'unsandboxed_semantic_smoke_passed',
  'sandboxed_lean_kernel_passed',
].includes(comparatorMetadata.status)) {
  throw new Error(
    'audit_config.json has an invalid verification.comparator.status',
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
    Object.keys(entry).sort().join(',') !== 'filename,sha256' ||
    typeof entry.filename !== 'string' ||
    entry.filename.length === 0 ||
    path.basename(entry.filename) !== entry.filename ||
    !entry.filename.endsWith('.pdf') ||
    !/^[0-9a-f]{64}$/.test(entry.sha256)
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
  localSources[0].sha256 !== auditConfig.target_pdf.sha256
) {
  throw new Error(
    'sources must contain exactly one local entry matching target_pdf filename and SHA-256',
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
  verifiedPdfEntries[field] = {
    filename: entry.filename,
    sha256: actualSha256,
    byte_length: pdfBytes.length,
  };
}

if (checkPdfsOnly) {
  fs.writeSync(
    process.stdout.fd,
    `verified target_pdf ${verifiedPdfEntries.target_pdf.sha256} ` +
    `(${verifiedPdfEntries.target_pdf.byte_length} bytes); ` +
    `source_pdf_fr ${verifiedPdfEntries.source_pdf_fr.sha256} ` +
    `(${verifiedPdfEntries.source_pdf_fr.byte_length} bytes)\n`,
  );
  process.exit(0);
}

const readme = fs.readFileSync(readmePath, 'utf8');
for (const field of ['target_pdf', 'source_pdf_fr']) {
  for (const key of ['filename', 'sha256']) {
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

const publicBridgeEntries = bridges.map(({local_name: _localName, ...bridge}) =>
  bridge
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

const transcriptLines = (transcriptText, configPath) => {
  if (transcriptText.includes('\u0000')) {
    throw new Error(
      `Comparator transcript contains a NUL byte: ${configPath}`,
    );
  }
  return transcriptText.split(/\r?\n/);
};

const requireUniqueTranscriptField = (lines, field, configPath) => {
  const prefix = `${field}=`;
  const values = lines
    .filter(line => line.startsWith(prefix))
    .map(line => line.slice(prefix.length));
  if (values.length !== 1 || values[0].length === 0) {
    throw new Error(
      `passed Comparator transcript must contain exactly one nonempty ` +
      `${field} field: ${configPath}`,
    );
  }
  return values[0];
};

const requireExactTranscriptLine = (lines, expectedLine, label, configPath) => {
  const count = lines.filter(line => line === expectedLine).length;
  if (count !== 1) {
    throw new Error(
      `passed Comparator transcript must contain exactly one ${label}: ` +
      `${configPath}`,
    );
  }
};

let passedComparatorSourceCommit = null;

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

const foundationalAxioms = auditConfig.editorial.axioms;
const successfulComparatorStatuses = new Set([
  'unsandboxed_semantic_smoke_passed',
  'sandboxed_lean_kernel_passed',
]);
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
  if (![
    'not_run',
    'failed',
    ...successfulComparatorStatuses,
  ].includes(run.status)) {
    throw new Error(`invalid Comparator status for ${configPath}: ${run.status}`);
  }
  if (typeof run.sandboxed !== 'boolean') {
    throw new Error(`invalid Comparator sandboxed flag for ${configPath}`);
  }
  if (
    run.status === 'unsandboxed_semantic_smoke_passed' &&
    run.sandboxed
  ) {
    throw new Error(
      `unsandboxed Comparator status has sandboxed=true: ${configPath}`,
    );
  }
  if (run.status === 'sandboxed_lean_kernel_passed' && !run.sandboxed) {
    throw new Error(
      `sandboxed Comparator status has sandboxed=false: ${configPath}`,
    );
  }
  const runPassed = successfulComparatorStatuses.has(run.status);
  let transcriptSha256 = null;
  let transcriptBytes = null;
  if (run.transcript !== null) {
    const transcriptPath = normalizeProjectRelativePath(
      run.transcript,
      `verification.comparator.configurations[${index}].transcript`,
    );
    if (run.transcript_sha256 !== undefined && run.transcript_sha256 !== null) {
      if (!/^[0-9a-f]{64}$/.test(run.transcript_sha256)) {
        throw new Error(
          `invalid Comparator transcript SHA-256 for ${configPath}`,
        );
      }
      transcriptSha256 = run.transcript_sha256;
      transcriptBytes = fs.readFileSync(transcriptPath);
      const computedTranscriptSha256 = crypto
        .createHash('sha256')
        .update(transcriptBytes)
        .digest('hex');
      if (computedTranscriptSha256 !== transcriptSha256) {
        throw new Error(
          `Comparator transcript SHA-256 mismatch for ${configPath}: ` +
          `expected ${transcriptSha256}, got ${computedTranscriptSha256}`,
        );
      }
    }
  } else if (
    run.transcript_sha256 !== undefined &&
    run.transcript_sha256 !== null
  ) {
    throw new Error(
      `Comparator run without a transcript records a SHA-256: ${configPath}`,
    );
  }
  if (runPassed && run.transcript === null) {
    throw new Error(`passed Comparator run lacks a transcript: ${configPath}`);
  }
  if (runPassed && transcriptSha256 === null) {
    throw new Error(
      `passed Comparator run lacks a transcript SHA-256: ${configPath}`,
    );
  }
  if (run.status === 'not_run' && run.transcript !== null) {
    throw new Error(`unrun Comparator configuration has a transcript: ${configPath}`);
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
  const configurationSha256AtRun =
    run.configuration_sha256_at_run ?? null;
  const comparatorFilesetDigestSha256AtRun =
    run.comparator_fileset_digest_sha256_at_run ?? null;
  if (runPassed) {
    if (!/^[0-9a-f]{64}$/.test(configurationSha256AtRun ?? '')) {
      throw new Error(
        `passed Comparator run has an invalid configuration SHA-256: ${configPath}`,
      );
    }
    if (!/^[0-9a-f]{64}$/.test(comparatorFilesetDigestSha256AtRun ?? '')) {
      throw new Error(
        `passed Comparator run has an invalid fileset SHA-256: ${configPath}`,
      );
    }
    if (configurationSha256AtRun !== configSha256) {
      throw new Error(
        `passed Comparator run is stale for ${configPath}: configuration ` +
        `was ${configurationSha256AtRun}, now ${configSha256}`,
      );
    }
    if (comparatorFilesetDigestSha256AtRun !== comparatorDigestSha256) {
      throw new Error(
        `passed Comparator run is stale for ${configPath}: comparator fileset ` +
        `was ${comparatorFilesetDigestSha256AtRun}, now ${comparatorDigestSha256}`,
      );
    }
    let transcriptText;
    try {
      transcriptText = new TextDecoder('utf-8', {fatal: true})
        .decode(transcriptBytes);
    } catch (error) {
      throw new Error(
        `passed Comparator transcript is not valid UTF-8 for ${configPath}: ` +
        error.message,
      );
    }
    const lines = transcriptLines(transcriptText, configPath);
    const transcriptField = field =>
      requireUniqueTranscriptField(lines, field, configPath);

    const mode = transcriptField('mode');
    const expectedMode = run.sandboxed
      ? 'sandboxed Comparator verification'
      : 'unsandboxed Comparator semantic smoke test (non-certifying)';
    if (mode !== expectedMode) {
      throw new Error(
        `Comparator transcript mode/sandbox mismatch for ${configPath}: ` +
        `expected ${JSON.stringify(expectedMode)}, got ${JSON.stringify(mode)}`,
      );
    }
    const transcriptSandboxed = transcriptField('sandboxed');
    if (transcriptSandboxed !== String(run.sandboxed)) {
      throw new Error(
        `Comparator transcript sandboxed flag mismatch for ${configPath}: ` +
        `metadata records ${run.sandboxed}, transcript records ` +
        transcriptSandboxed,
      );
    }
    const expectedNanoda = comparatorConfig.enable_nanoda
      ? 'enabled'
      : 'disabled';
    const transcriptNanoda = transcriptField('nanoda');
    if (transcriptNanoda !== expectedNanoda) {
      throw new Error(
        `Comparator transcript nanoda mode mismatch for ${configPath}: ` +
        `expected ${expectedNanoda}, got ${transcriptNanoda}`,
      );
    }
    if (transcriptField('config') !== configPath) {
      throw new Error(
        `Comparator transcript configuration path mismatch: ${configPath}`,
      );
    }
    if (transcriptField('tracked_worktree_dirty_count') !== '0') {
      throw new Error(
        `passed Comparator transcript does not record a clean source ` +
        `worktree: ${configPath}`,
      );
    }

    const sourceCommit = transcriptField('paper_c_commit');
    if (!/^[0-9a-f]{40}$/.test(sourceCommit)) {
      throw new Error(
        `passed Comparator transcript has an invalid source commit: ` +
        `${configPath}`,
      );
    }
    if (
      passedComparatorSourceCommit !== null &&
      passedComparatorSourceCommit !== sourceCommit
    ) {
      throw new Error(
        `passed Comparator transcripts refer to different Paper C commits: ` +
        `${passedComparatorSourceCommit} and ${sourceCommit}`,
      );
    }
    passedComparatorSourceCommit = sourceCommit;

    const expectedTranscriptCommits = new Map([
      ['lean_commit', configuredToolchain.lean.commit],
      ['mathlib_commit', configuredToolchain.mathlib.commit],
      ['comparator_commit', comparatorMetadata.tools.comparator.commit],
      ['lean4export_commit', comparatorMetadata.tools.lean4export.commit],
      ['landrun_commit', comparatorMetadata.tools.landrun.commit],
    ]);
    if (comparatorConfig.enable_nanoda) {
      expectedTranscriptCommits.set(
        'nanoda_commit',
        comparatorMetadata.tools.nanoda.commit,
      );
    }
    for (const [field, expectedCommit] of expectedTranscriptCommits) {
      const transcriptCommit = transcriptField(field);
      if (transcriptCommit !== expectedCommit) {
        throw new Error(
          `Comparator transcript ${field} mismatch for ${configPath}: ` +
          `expected ${expectedCommit}, got ${transcriptCommit}`,
        );
      }
    }

    if (transcriptField('exit_code') !== '0') {
      throw new Error(
        `passed Comparator transcript does not record exit_code=0: ` +
        configPath,
      );
    }
    requireExactTranscriptLine(
      lines,
      'Lean default kernel accepts the solution',
      'Lean default-kernel acceptance marker',
      configPath,
    );
    requireExactTranscriptLine(
      lines,
      'Your solution is okay!',
      'Comparator success marker',
      configPath,
    );
    requireExactTranscriptLine(
      lines,
      `${configSha256}  ${configPath}`,
      'configuration SHA-256 binding',
      configPath,
    );
    if (
      transcriptField('comparator_fileset_digest_sha256') !==
      comparatorDigestSha256
    ) {
      throw new Error(
        `passed Comparator transcript does not bind the current fileset hash: ` +
        configPath,
      );
    }
  }
  parsedComparatorConfigurations.push({
    ...comparatorConfig,
    path: configPath,
    sha256: configSha256,
    status: run.status,
    sandboxed: run.sandboxed,
    transcript: run.transcript,
    transcript_sha256: transcriptSha256,
    configuration_sha256_at_run: configurationSha256AtRun,
    comparator_fileset_digest_sha256_at_run:
      comparatorFilesetDigestSha256AtRun,
    challenge_file: challengePath,
    solution_file: solutionPath,
  });
}

if (
  comparatorMetadata.status === 'not_run' &&
  parsedComparatorConfigurations.some(config => config.status !== 'not_run')
) {
  throw new Error(
    'global Comparator status is not_run but a project configuration has run',
  );
}
if (
  successfulComparatorStatuses.has(comparatorMetadata.status) &&
  parsedComparatorConfigurations.some(
    config => config.status !== comparatorMetadata.status,
  )
) {
  throw new Error(
    'global Comparator success status does not match every project configuration',
  );
}

const comparatorConfigByPath = new Map(
  parsedComparatorConfigurations.map(config => [config.path, config]),
);
const placeholderKeys = new Set();
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
  if (actualCount !== placeholder.count) {
    throw new Error(
      `${relativePath}: expected ${placeholder.count} ${placeholder.token} ` +
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
    if (item.comparator.status !== comparatorConfig.status) {
      throw new Error(
        `paper item ${itemId} Comparator status differs from ${configPath}`,
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
  'HK13-QO-conductor-fibres',
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
    'Thm-1.1-finite-cylinder must consume exactly the four configured ' +
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

const citationLabel = bridge =>
  `${bridge.citation.authors.join(', ')}, ${bridge.citation.title}, ` +
  bridge.citation.locator;

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
    comparator_status: item.comparator.covered
      ? item.comparator.status
      : 'not_configured',
    literature_dependencies: item.bridge_ids
      .map(bridgeId => bridgeById.get(bridgeId))
      .filter(bridge => bridge.kind === 'external' && bridge.status === 'open')
      .map(bridge => ({
        statement: bridge.formalization_relation,
        source: literatureSourceIdByBridgeId.get(bridge.id),
        source_locator: citationLabel(bridge),
        bridge_id: bridge.id,
        lean_name: bridge.lean_name,
      })),
  };
});

const formalization = {
  version: formalizationTemplate.version,
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
    comparator_runs: parsedComparatorConfigurations.map(config => ({
      configuration: config.path,
      status: config.status,
      sandboxed: config.sandboxed,
      transcript: config.transcript,
      transcript_sha256: config.transcript_sha256,
      configuration_sha256_at_run: config.configuration_sha256_at_run,
      comparator_fileset_digest_sha256_at_run:
        config.comparator_fileset_digest_sha256_at_run,
      enable_nanoda: config.enable_nanoda,
    })),
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
      comparator_status: item.comparator.covered
        ? item.comparator.status
        : 'not_configured',
      note: item.note,
    })),
  },
  verification: {
    formalization_template: formalizationTemplate,
    toolchain: configuredToolchain,
    comparator: {
      status: comparatorMetadata.status,
      status_note: comparatorMetadata.status_note,
      tools: comparatorMetadata.tools,
      compatibility_probe: comparatorMetadata.compatibility_probe,
      fileset: comparatorFiles,
      digest_sha256: comparatorDigestSha256,
      configurations: parsedComparatorConfigurations.map(config => ({
        path: config.path,
        sha256: config.sha256,
        challenge_module: config.challenge_module,
        solution_module: config.solution_module,
        theorem_names: config.theorem_names,
        permitted_axioms: config.permitted_axioms,
        enable_nanoda: config.enable_nanoda,
        status: config.status,
        sandboxed: config.sandboxed,
        transcript: config.transcript,
        transcript_sha256: config.transcript_sha256,
        configuration_sha256_at_run: config.configuration_sha256_at_run,
        comparator_fileset_digest_sha256_at_run:
          config.comparator_fileset_digest_sha256_at_run,
      })),
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
  '# Generated deterministically from audit_config.json schema 2.',
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
  '| Identifiant | Nature | Statut | Proposition Lean | Déchargé par | Source primaire | Localisation |',
  '|---|---|---|---|---|---|---|',
  ...bridges.map(bridge =>
    `| \`${bridge.id}\` | \`${bridge.kind}\` | \`${bridge.status}\` | ` +
    `\`${bridge.lean_name}\` | ` +
    `${bridge.discharged_by === undefined
      ? '—'
      : bridge.discharged_by.map(name => `\`${name}\``).join('<br>')} | ` +
    `${bridge.citation.authors.join(', ')}, *${bridge.citation.title}*, ` +
    `${bridge.citation.locator} | ${bridge.manuscript_locator.result} |`,
  ),
  '',
  '### Transcriptions sources à contrôler',
  '',
  ...bridges.flatMap(bridge => {
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
        `*${bridge.citation.title}*, ${bridge.citation.locator}.`,
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
      `- Relation de formalisation : ${asSentence(bridge.formalization_relation)}`,
      `- Contrôle : \`${bridge.source_statement.verification}\`.`,
      ...(bridge.source_statement.verbatim_is_excerpt === true
        ? ['- Citation littérale : extrait (les formules structurées ci-dessous complètent la transcription).']
        : []),
      ...(bridge.source_statement.verification_note
        ? [`- Note de vérification : ${asSentence(
            bridge.source_statement.verification_note,
          )}`]
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
  schema_version: 6,
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
  comparator_status: comparatorMetadata.status,
  comparator_status_note: comparatorMetadata.status_note,
  comparator_tools: comparatorMetadata.tools,
  comparator_compatibility_probe: comparatorMetadata.compatibility_probe,
  comparator_configurations: parsedComparatorConfigurations,
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
  `${parsedComparatorConfigurations.filter(config => successfulComparatorStatuses.has(config.status)).length} ` +
  'passed, ' +
  `${parsedComparatorConfigurations.filter(config => config.status === 'not_run').length} ` +
  'pending, and ' +
  `${parsedComparatorConfigurations.filter(config => config.status === 'failed').length} ` +
  'failed Comparator configurations; ' +
  `formalization ${formalizationTemplate.version}\n`,
);
