#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';

const scriptDirectory = path.dirname(fileURLToPath(import.meta.url));
const projectRoot = path.resolve(scriptDirectory, '..');
const manifestPath = path.join(projectRoot, 'audit_manifest.json');
const auditPath = path.join(projectRoot, 'AuditCheck.lean');
const manifest = JSON.parse(fs.readFileSync(manifestPath, 'utf8'));
const lake = process.env.LAKE ?? 'lake';

const argumentsList = process.argv.slice(2);
let auditLogPath = null;
if (argumentsList.length !== 0) {
  if (
    argumentsList.length !== 2 ||
    argumentsList[0] !== '--input' ||
    argumentsList[1].length === 0
  ) {
    throw new Error('usage: verify_audit.mjs [--input AUDIT_LOG]');
  }
  auditLogPath = path.resolve(projectRoot, argumentsList[1]);
}

function parseAuditRecords(output) {
  const recordPattern =
    /'([^\n]*)' (?:(?:depends on axioms:\s*\[([\s\S]*?)\])|(?:does not depend on any axioms))/g;
  return [...output.matchAll(recordPattern)].map(match => ({
    name: match[1],
    axioms: (match[2] ?? '')
      .split(',')
      .map(item => item.trim())
      .filter(item => item.length !== 0),
  }));
}

const parserProbe = parseAuditRecords(
  "'withAxioms' depends on axioms: [propext,\n Classical.choice]\n" +
  "'withoutAxioms' does not depend on any axioms\n",
);
if (
  parserProbe.length !== 2 ||
  parserProbe[0].name !== 'withAxioms' ||
  parserProbe[0].axioms.join(',') !== 'propext,Classical.choice' ||
  parserProbe[1].name !== 'withoutAxioms' ||
  parserProbe[1].axioms.length !== 0
) {
  throw new Error('internal audit-output parser self-test failed');
}

let output;
if (auditLogPath !== null) {
  if (!fs.existsSync(auditLogPath)) {
    throw new Error(`audit log is missing: ${auditLogPath}`);
  }
  output = fs.readFileSync(auditLogPath, 'utf8');
} else {
  const result = spawnSync(
    lake,
    ['env', 'lean', path.basename(auditPath)],
    {
      cwd: projectRoot,
      env: process.env,
      encoding: 'utf8',
      maxBuffer: 1024 * 1024 * 1024,
    },
  );

  if (result.error) {
    throw new Error(
      `cannot execute ${lake}: ${result.error.message}. ` +
      'Set LAKE to the absolute lake executable if it is not on PATH.',
    );
  }
  if (result.status !== 0) {
    process.stderr.write(result.stdout ?? '');
    process.stderr.write(result.stderr ?? '');
    throw new Error(`AuditCheck.lean failed with exit code ${result.status}`);
  }

  output = `${result.stdout ?? ''}${result.stderr ?? ''}`;
}
const records = parseAuditRecords(output);

if (records.length !== manifest.audit_target_count) {
  throw new Error(
    `expected ${manifest.audit_target_count} audit outputs, ` +
    `found ${records.length}`,
  );
}

const actualNames = records.map(record => record.name);
if (
  JSON.stringify(actualNames) !==
  JSON.stringify(manifest.audit_targets)
) {
  const mismatch = actualNames.findIndex(
    (name, index) => name !== manifest.audit_targets[index],
  );
  throw new Error(
    `audit target order/name mismatch at index ${mismatch}: ` +
    `expected ${manifest.audit_targets[mismatch]}, ` +
    `found ${actualNames[mismatch]}`,
  );
}

const allowedAxioms = new Set([
  'propext',
  'Classical.choice',
  'Quot.sound',
]);
const violations = records.flatMap(record =>
  record.axioms
    .filter(axiom => !allowedAxioms.has(axiom))
    .map(axiom => `${record.name}: ${axiom}`),
);
if (violations.length !== 0) {
  throw new Error(
    'axioms outside the foundational allowlist:\n' +
    violations.join('\n'),
  );
}

for (const forbidden of ['sorryAx', 'Lean.ofReduceBool']) {
  if (output.includes(forbidden)) {
    throw new Error(`forbidden audit dependency: ${forbidden}`);
  }
}

console.log(
  `${records.length}/${manifest.audit_target_count} audit outputs verified; ` +
  'all axiom lists are subsets of ' +
  '[propext, Classical.choice, Quot.sound]',
);
