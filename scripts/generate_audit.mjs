import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { execFileSync } from 'node:child_process';
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
const auditMarkdownPath = path.join(projectRoot, 'AXIOM_AUDIT.md');
const auditConfigPath = path.join(projectRoot, 'audit_config.json');
const readmePath = path.join(projectRoot, 'README.md');

const binaryCompare = (left, right) =>
  left < right ? -1 : left > right ? 1 : 0;

const asSentence = text => {
  const trimmed = text.trim();
  return /[.!?]$/.test(trimmed) ? trimmed : `${trimmed}.`;
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
if (auditConfig.schema_version !== 1) {
  throw new Error('unsupported audit_config.json schema_version');
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

const sourceFiles = execFileSync(
  'rg',
  ['--files', 'PaperC', '-g', '*.lean'],
  { cwd: projectRoot, encoding: 'utf8' },
)
  .trim()
  .split('\n')
  .filter(Boolean)
  .sort(binaryCompare);

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
  'import PaperC.Main',
  '',
  '/-!',
  '# Exhaustive public-theorem dependency audit',
  '',
  'This file is generated by `node scripts/generate_audit.mjs`.',
  'It contains one `#print axioms` command for every explicit public',
  '`theorem` or `lemma` declaration under `PaperC`.',
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
  schema_version: 4,
  project: 'paper_c_lean',
  project_version: versionMatch[1],
  target_pdf: auditConfig.target_pdf,
  source_pdf_fr: auditConfig.source_pdf_fr,
  audit_file: 'AuditCheck.lean',
  import: 'PaperC.Main',
  source_glob: 'PaperC/**/*.lean',
  source_digest_sha256: digest,
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
  checkExact(auditMarkdownPath, auditMarkdownContent);
} else {
  fs.writeFileSync(auditPath, auditContent);
  fs.writeFileSync(manifestPath, manifestContent);
  fs.writeFileSync(auditMarkdownPath, auditMarkdownContent);
}

process.stdout.write(
  `${declarations.length} public theorem/lemma declarations; ` +
  `${declarations.length + additionalTargets.length} audit targets; ` +
  `${bridges.length} registered bridges; ` +
  `${hypothesisStatusCounts.open} open and ` +
  `${hypothesisStatusCounts.discharged} discharged; ` +
  `${conditionalTheoremCount} conditional public theorems\n`,
);
