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
    ...config.verification.comparator.configurations
      .map(run => run.transcript)
      .filter(transcript => transcript !== null),
    ...config.verification.comparator.fileset,
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
  if (
    JSON.stringify(baselineManifest.source_fileset) !==
    JSON.stringify(['PaperC.lean', 'PaperC/**/*.lean'])
  ) {
    throw new Error('manifest does not record the exact root-inclusive source fileset');
  }
  if (baselineManifest.import !== 'PaperC') {
    throw new Error('generated audit does not import the root PaperC module');
  }

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
    'root audit guards passed: PaperC.lean changes invalidate the digest; ' +
    'root public theorems enter the inventory and AuditCheck.lean\n',
  );
} finally {
  fs.rmSync(temporaryRoot, {recursive: true, force: true});
}
