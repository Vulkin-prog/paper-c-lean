#!/usr/bin/env node
import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';

function arg(name) {
  const i = process.argv.indexOf(name);
  if (i < 0 || i + 1 >= process.argv.length) throw new Error(`missing ${name}`);
  return process.argv[i + 1];
}
function sha256(file) {
  return crypto.createHash('sha256').update(fs.readFileSync(file)).digest('hex');
}
const evidenceDir = path.resolve(arg('--evidence-dir'));
const archive = path.resolve(arg('--archive'));
const output = path.resolve(arg('--output'));
const root = path.resolve(path.dirname(new URL(import.meta.url).pathname), '..');
const head = execFileSync('git', ['-C', root, 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
const resultNames = ['result-theorem-one-one.json', 'result-infinite-finite-transfer.json'];
const results = resultNames.map(name => JSON.parse(fs.readFileSync(path.join(evidenceDir, name), 'utf8')));
for (const result of results) {
  if (result.certifying !== true || result.sandboxed !== true || result.non_root !== true || result.exit_code !== 0) {
    throw new Error(`${result.config}: evidence is not certifying hardened evidence`);
  }
  if (result.paper_c_commit !== head) throw new Error(`${result.config}: paper_c_commit does not equal HEAD`);
}
if (results[0].comparator_fileset_digest_sha256 !== results[1].comparator_fileset_digest_sha256) {
  throw new Error('Comparator fileset digests differ');
}
const binding = {
  schema: 1,
  release: 'v0.48.1',
  paper_c_commit: head,
  comparator_fileset_digest_sha256: results[0].comparator_fileset_digest_sha256,
  english_pdf_sha256: sha256(path.join(root, 'paper_C_complete_v09_en.pdf')),
  french_pdf_sha256: sha256(path.join(root, 'paper_C_complete_v09.pdf')),
  hardened_archive_sha256: sha256(archive),
  evidence: Object.fromEntries(resultNames.map(name => [name, sha256(path.join(evidenceDir, name))])),
  certifying: true,
  sandboxed: true,
  non_root: true,
  kernels: ['lean'],
};
fs.mkdirSync(path.dirname(output), { recursive: true });
fs.writeFileSync(output, JSON.stringify(binding, null, 2) + '\n');
console.log(`wrote ${output}`);
