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
const bindingPath = path.resolve(arg('--binding'));
const evidenceDir = path.resolve(arg('--evidence-dir'));
const expectedArchive = arg('--expected-archive-sha256');
const root = path.resolve(path.dirname(new URL(import.meta.url).pathname), '..');
const binding = JSON.parse(fs.readFileSync(bindingPath, 'utf8'));
const head = execFileSync('git', ['-C', root, 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
if (binding.schema !== 1 || binding.release !== 'v0.48.1') throw new Error('unexpected release-binding schema/release');
if (binding.paper_c_commit !== head) throw new Error('release binding is not for checked-out HEAD');
if (binding.hardened_archive_sha256 !== expectedArchive) throw new Error('hardened archive SHA-256 mismatch');
if (binding.english_pdf_sha256 !== sha256(path.join(root, 'paper_C_complete_v09_en.pdf'))) throw new Error('English PDF mismatch');
if (binding.french_pdf_sha256 !== sha256(path.join(root, 'paper_C_complete_v09.pdf'))) throw new Error('French PDF mismatch');
if (binding.certifying !== true || binding.sandboxed !== true || binding.non_root !== true) throw new Error('binding is not hardened/certifying');
for (const [name, expected] of Object.entries(binding.evidence)) {
  const file = path.join(evidenceDir, name);
  if (sha256(file) !== expected) throw new Error(`${name}: SHA-256 mismatch`);
  const result = JSON.parse(fs.readFileSync(file, 'utf8'));
  if (result.paper_c_commit !== head || result.certifying !== true || result.sandboxed !== true || result.non_root !== true || result.exit_code !== 0) {
    throw new Error(`${name}: invalid hardened result record`);
  }
  if (result.comparator_fileset_digest_sha256 !== binding.comparator_fileset_digest_sha256) {
    throw new Error(`${name}: Comparator fileset digest mismatch`);
  }
}
console.log('release binding verified');
