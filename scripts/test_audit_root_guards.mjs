#!/usr/bin/env node

import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';

const scriptDirectory = path.dirname(fileURLToPath(import.meta.url));
const projectRoot = path.resolve(scriptDirectory, '..');
const temporaryRoot = fs.mkdtempSync(
  path.join(os.tmpdir(), 'paper-c-root-audit-guards-'),
);

function copyProjectFile(relativePath) {
  const source = path.join(projectRoot, relativePath);
  const destination = path.join(temporaryRoot, relativePath);
  fs.mkdirSync(path.dirname(destination), {recursive: true});
  fs.copyFileSync(source, destination);
}

function runGenerator(argumentsList = []) {
  return spawnSync(
    process.execPath,
    [path.join(temporaryRoot, 'scripts/generate_audit.mjs'), ...argumentsList],
    {
      cwd: temporaryRoot,
      encoding: 'utf8',
      env: process.env,
    },
  );
}

function requireSuccess(result, description) {
  if (result.error || result.status !== 0) {
    throw new Error(
      `${description} failed:\n${result.error?.message ?? ''}\n` +
      `${result.stdout ?? ''}${result.stderr ?? ''}`,
    );
  }
}

try {
  const config = JSON.parse(
    fs.readFileSync(path.join(projectRoot, 'audit_config.json'), 'utf8'),
  );
  fs.cpSync(
    path.join(projectRoot, 'PaperC'),
    path.join(temporaryRoot, 'PaperC'),
    {recursive: true},
  );
  const fixtureFiles = new Set([
    'PaperC.lean',
    'README.md',
    'AXIOM_AUDIT.md',
    'AuditCheck.lean',
    'audit_config.json',
    'audit_manifest.json',
    'lake-manifest.json',
    'lakefile.toml',
    'lean-toolchain',
    'scripts/generate_audit.mjs',
    config.target_pdf.filename,
    config.source_pdf_fr.filename,
    config.verification.comparator.compatibility_probe.transcript,
    ...config.verification.comparator.historical_configurations
      .map(run => run.evidence_record)
      .filter(evidenceRecord => typeof evidenceRecord === 'string'),
    ...config.verification.comparator.fileset,
    ...config.verification.literature_certificates.entries
      .map(entry => entry.file),
    ...config.verification.literature_certificates.historical_closure_notes
      .map(entry => entry.file),
  ]);
  for (const relativePath of fixtureFiles) {
    copyProjectFile(relativePath);
  }
  fs.appendFileSync(
    path.join(temporaryRoot, 'README.md'),
    `\n<!-- Root-audit test fixture: ${config.target_pdf.filename} ` +
    `${config.target_pdf.sha256}; ${config.source_pdf_fr.filename} ` +
    `${config.source_pdf_fr.sha256}. -->\n`,
  );

  const rootPath = path.join(temporaryRoot, 'PaperC.lean');
  const originalRootSource = fs.readFileSync(rootPath, 'utf8');
  const baselineResult = runGenerator();
  requireSuccess(baselineResult, 'baseline audit generation');
  const baselineManifest = JSON.parse(
    fs.readFileSync(
      path.join(temporaryRoot, 'audit_manifest.json'),
      'utf8',
    ),
  );
  const baselineTimelessArtifacts = new Map(
    ['AuditCheck.lean', 'audit_manifest.json', 'formalization.yaml',
      'AXIOM_AUDIT.md']
      .map(relativePath => [
        relativePath,
        fs.readFileSync(path.join(temporaryRoot, relativePath)),
      ]),
  );
  if (
    JSON.stringify(baselineManifest.source_fileset) !==
    JSON.stringify(['PaperC.lean', 'PaperC/**/*.lean'])
  ) {
    throw new Error('manifest does not record the exact root-inclusive source fileset');
  }
  if (baselineManifest.import !== 'PaperC') {
    throw new Error('generated audit does not import the root PaperC module');
  }
  if (
    baselineManifest.source_snapshot_comparator_state !==
      'definitions_and_digests_only' ||
    baselineManifest.release_evidence_state !==
      'external_to_source_snapshot' ||
    baselineManifest.release_evidence_location !==
      `release_evidence/v${config.core_source.base_version}/` ||
    baselineManifest.packaging_commit_required !== true ||
    Object.hasOwn(baselineManifest, 'comparator_status') ||
    Object.hasOwn(baselineManifest, 'comparator_status_note') ||
    baselineManifest.comparator_configurations.some(configuration =>
      configuration.source_snapshot_comparator_state !==
        baselineManifest.source_snapshot_comparator_state ||
      Object.hasOwn(configuration, 'status') ||
      Object.hasOwn(configuration, 'evidence_record')
    )
  ) {
    throw new Error(
      'generated audit does not preserve the timeless Comparator evidence model',
    );
  }
  if (
    baselineManifest.literature_certificates.length !==
      config.verification.literature_certificates.entries.length ||
    baselineManifest.historical_literature_closure_notes.length !==
      config.verification.literature_certificates.historical_closure_notes.length ||
    !/^[0-9a-f]{64}$/.test(
      baselineManifest.literature_certificate_digest_sha256,
    ) ||
    !/^[0-9a-f]{64}$/.test(
      baselineManifest.literature_documentation_digest_sha256,
    )
  ) {
    throw new Error('generated audit does not record literature certificates');
  }
  requireSuccess(
    runGenerator(['--check-literature-certificates']),
    'baseline literature-certificate verification',
  );

  const evidenceRecordPath = path.join(
    temporaryRoot,
    config.verification.comparator.historical_configurations[0].evidence_record,
  );
  const originalEvidenceRecord = fs.readFileSync(evidenceRecordPath, 'utf8');
  fs.appendFileSync(evidenceRecordPath, '\n');
  const evidenceRecordGuardResult = runGenerator();
  if (
    evidenceRecordGuardResult.status === 0 ||
    !`${evidenceRecordGuardResult.stdout}${evidenceRecordGuardResult.stderr}`
      .includes('historical Comparator evidence-record SHA-256 mismatch')
  ) {
    throw new Error(
      'modifying a Comparator evidence record did not invalidate its SHA-256',
    );
  }
  fs.writeFileSync(evidenceRecordPath, originalEvidenceRecord);

  const unexpectedEvidenceRecordPath = path.join(
    temporaryRoot,
    'comparator/evidence/untracked.json',
  );
  fs.writeFileSync(unexpectedEvidenceRecordPath, '{}\n');
  const unexpectedEvidenceRecordResult = runGenerator();
  if (
    unexpectedEvidenceRecordResult.status === 0 ||
    !`${unexpectedEvidenceRecordResult.stdout}`
      .concat(`${unexpectedEvidenceRecordResult.stderr}`)
      .includes(
        'comparator/evidence must contain exactly the configured historical ' +
        'evidence records; release evidence is external to the source snapshot',
      )
  ) {
    throw new Error('an undeclared Comparator evidence record was not rejected');
  }
  fs.rmSync(unexpectedEvidenceRecordPath);

  const literaturePath = path.join(
    temporaryRoot,
    config.verification.literature_certificates.entries[0].file,
  );
  const originalLiteratureSource = fs.readFileSync(literaturePath, 'utf8');
  fs.appendFileSync(
    literaturePath,
    '\n<!-- Literature-certificate digest guard mutation. -->\n',
  );
  const literatureGuardResult = runGenerator([
    '--check-literature-certificates',
  ]);
  if (
    literatureGuardResult.status === 0 ||
    !`${literatureGuardResult.stdout}${literatureGuardResult.stderr}`.includes(
      'literature certificate bytes or mapping differ',
    )
  ) {
    throw new Error(
      'modifying a literature certificate did not invalidate its manifest digest',
    );
  }
  fs.writeFileSync(literaturePath, originalLiteratureSource);

  const unexpectedLiteraturePath = path.join(
    temporaryRoot,
    'literature_certificates/untracked.md',
  );
  fs.writeFileSync(unexpectedLiteraturePath, '# Untracked certificate\n');
  const unexpectedLiteratureResult = runGenerator([
    '--check-literature-certificates',
  ]);
  if (
    unexpectedLiteratureResult.status === 0 ||
    !`${unexpectedLiteratureResult.stdout}${unexpectedLiteratureResult.stderr}`.includes(
      'directory must contain exactly the configured active certificates ' +
      'and historical closure notes',
    )
  ) {
    throw new Error(
      'an undeclared literature-certificate file was not rejected',
    );
  }
  fs.rmSync(unexpectedLiteraturePath);

  const closureNotePath = path.join(
    temporaryRoot,
    config.verification.literature_certificates.historical_closure_notes[0].file,
  );
  const originalClosureNote = fs.readFileSync(closureNotePath, 'utf8');
  fs.appendFileSync(
    closureNotePath,
    '\n<!-- Historical closure-note digest guard mutation. -->\n',
  );
  const closureNoteGuardResult = runGenerator([
    '--check-literature-certificates',
  ]);
  if (
    closureNoteGuardResult.status === 0 ||
    !`${closureNoteGuardResult.stdout}${closureNoteGuardResult.stderr}`.includes(
      'literature certificate bytes or mapping differ',
    )
  ) {
    throw new Error(
      'modifying the historical closure note did not invalidate its manifest digest',
    );
  }
  fs.writeFileSync(closureNotePath, originalClosureNote);

  const comparatorConfigPath = path.join(temporaryRoot, 'audit_config.json');
  const originalComparatorConfig = fs.readFileSync(comparatorConfigPath, 'utf8');
  const legacyComparatorConfig = JSON.parse(originalComparatorConfig);
  legacyComparatorConfig.verification.comparator.status =
    'sandboxed_lean_kernel_passed';
  fs.writeFileSync(
    comparatorConfigPath,
    `${JSON.stringify(legacyComparatorConfig, null, 2)}\n`,
  );
  const legacyComparatorResult = runGenerator();
  if (
    legacyComparatorResult.status === 0 ||
    !`${legacyComparatorResult.stdout}${legacyComparatorResult.stderr}`.includes(
      'legacy current Comparator status fields are forbidden',
    )
  ) {
    throw new Error(
      'legacy mutable Comparator status was accepted in source metadata',
    );
  }
  fs.writeFileSync(comparatorConfigPath, originalComparatorConfig);

  const legacyPaperItemConfig = JSON.parse(originalComparatorConfig);
  legacyPaperItemConfig.paper_items.find(item => item.comparator.covered)
    .comparator.status = 'not_run';
  fs.writeFileSync(
    comparatorConfigPath,
    `${JSON.stringify(legacyPaperItemConfig, null, 2)}\n`,
  );
  const legacyPaperItemResult = runGenerator();
  if (
    legacyPaperItemResult.status === 0 ||
    !`${legacyPaperItemResult.stdout}${legacyPaperItemResult.stderr}`.includes(
      'unexpected Comparator metadata fields',
    )
  ) {
    throw new Error(
      'legacy mutable Comparator status was accepted on a paper item',
    );
  }
  fs.writeFileSync(comparatorConfigPath, originalComparatorConfig);

  for (const [field, invalidValue, expectedMessage] of [
    [
      'source_snapshot_comparator_state',
      'not_run',
      'source_snapshot_comparator_state',
    ],
    [
      'release_evidence_state',
      'not_present',
      'release_evidence_state',
    ],
    [
      'release_evidence_location',
      'release_evidence/current/',
      'release_evidence_location',
    ],
    [
      'packaging_commit_required',
      false,
      'must require a Comparator evidence packaging commit',
    ],
  ]) {
    const invalidProtocolConfig = JSON.parse(originalComparatorConfig);
    invalidProtocolConfig.verification.comparator[field] = invalidValue;
    fs.writeFileSync(
      comparatorConfigPath,
      `${JSON.stringify(invalidProtocolConfig, null, 2)}\n`,
    );
    const invalidProtocolResult = runGenerator();
    if (
      invalidProtocolResult.status === 0 ||
      !`${invalidProtocolResult.stdout}${invalidProtocolResult.stderr}`.includes(
        expectedMessage,
      )
    ) {
      throw new Error(`invalid Comparator protocol field was accepted: ${field}`);
    }
  }
  fs.writeFileSync(comparatorConfigPath, originalComparatorConfig);

  fs.mkdirSync(
    path.join(temporaryRoot, config.verification.comparator.release_evidence_location),
    {recursive: true},
  );
  fs.writeFileSync(
    path.join(
      temporaryRoot,
      config.verification.comparator.release_evidence_location,
      'release-binding.json',
    ),
    '{}\n',
  );
  requireSuccess(
    runGenerator(),
    'source audit with descendant-style release evidence present',
  );
  for (const [relativePath, baselineBytes] of baselineTimelessArtifacts) {
    if (
      !fs.readFileSync(path.join(temporaryRoot, relativePath)).equals(
        baselineBytes,
      )
    ) {
      throw new Error(
        `later release evidence changed source-snapshot artifact ${relativePath}`,
      );
    }
  }

  const primarySourceAccess =
    config.verification.literature_certificates.entries[0]
      .primary_source_access;
  fs.writeFileSync(
    literaturePath,
    originalLiteratureSource.replace(
      `Primary-source access: \`${primarySourceAccess}\``,
      'Primary-source access: `not_accessed`',
    ),
  );
  const accessMappingResult = runGenerator();
  if (
    accessMappingResult.status === 0 ||
    !`${accessMappingResult.stdout}${accessMappingResult.stderr}`.includes(
      `Primary-source access: \`${primarySourceAccess}\``,
    )
  ) {
    throw new Error(
      'a contradictory primary-source access marker was not rejected',
    );
  }
  fs.writeFileSync(literaturePath, originalLiteratureSource);

  fs.appendFileSync(rootPath, '\n-- Root source-digest guard mutation.\n');
  const digestGuardResult = runGenerator(['--check-source-digest']);
  if (
    digestGuardResult.status === 0 ||
    !`${digestGuardResult.stdout}${digestGuardResult.stderr}`.includes(
      'core digest mismatch',
    )
  ) {
    throw new Error(
      'modifying PaperC.lean did not invalidate the recorded source digest',
    );
  }

  fs.writeFileSync(
    rootPath,
    `${originalRootSource.trimEnd()}\n\n` +
    'namespace PaperC\n\n' +
    'theorem auditRootGuardPublicTheorem : True := by\n' +
    '  trivial\n\n' +
    'end PaperC\n',
  );
  const frozenTheoremResult = runGenerator();
  const frozenTheoremOutput =
    `${frozenTheoremResult.stdout}${frozenTheoremResult.stderr}`;
  const mutatedDigest = /computed ([0-9a-f]{64})/.exec(frozenTheoremOutput)?.[1];
  if (frozenTheoremResult.status === 0 || !mutatedDigest) {
    throw new Error(
      'adding a root theorem did not invalidate the frozen core digest',
    );
  }
  const mutatedConfigPath = path.join(temporaryRoot, 'audit_config.json');
  const mutatedConfig = JSON.parse(fs.readFileSync(mutatedConfigPath, 'utf8'));
  mutatedConfig.core_source.digest_sha256 = mutatedDigest;
  fs.writeFileSync(
    mutatedConfigPath,
    `${JSON.stringify(mutatedConfig, null, 2)}\n`,
  );
  const theoremGuardResult = runGenerator();
  requireSuccess(theoremGuardResult, 'root public-theorem audit generation');
  const theoremManifest = JSON.parse(
    fs.readFileSync(
      path.join(temporaryRoot, 'audit_manifest.json'),
      'utf8',
    ),
  );
  const guardName = 'PaperC.auditRootGuardPublicTheorem';
  const guardRecord = theoremManifest.theorem_records.find(
    record => record.name === guardName,
  );
  if (
    guardRecord?.source !== 'PaperC.lean' ||
    !theoremManifest.theorems.includes(guardName) ||
    !theoremManifest.audit_targets.includes(guardName) ||
    theoremManifest.theorem_count !== baselineManifest.theorem_count + 1
  ) {
    throw new Error(
      'a public theorem added to PaperC.lean is absent from the generated inventory',
    );
  }
  const auditSource = fs.readFileSync(
    path.join(temporaryRoot, 'AuditCheck.lean'),
    'utf8',
  );
  if (
    !auditSource.startsWith('import PaperC\n') ||
    !auditSource.includes(`#print axioms ${guardName}\n`)
  ) {
    throw new Error(
      'a public theorem added to PaperC.lean has no generated #print axioms command',
    );
  }

  process.stdout.write(
    'root and literature audit guards passed: PaperC.lean changes invalidate ' +
    'the digest; root public theorems enter the inventory and AuditCheck.lean; ' +
    'historical Comparator evidence mutations, legacy mutable current-run ' +
    'statuses, invalid timeless-protocol fields, undeclared evidence, ' +
    'undeclared certificates, historical closure-note mutations, and ' +
    'access-marker drift are rejected; later release evidence does not alter ' +
    'source-snapshot generation\n',
  );
} finally {
  fs.rmSync(temporaryRoot, {recursive: true, force: true});
}
