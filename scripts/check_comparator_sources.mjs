#!/usr/bin/env node

import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

const root = process.cwd();
const challengeFiles = ['Challenge.lean', 'ChallengeTransfer.lean'];
const requiredSolutionFiles = ['Solution.lean', 'SolutionTransfer.lean'];

function fail(message) {
  console.error(`Comparator source guard: ${message}`);
  process.exitCode = 1;
}

function readRequired(relativePath) {
  const absolutePath = path.join(root, relativePath);
  if (!fs.existsSync(absolutePath)) {
    fail(`required file is missing: ${relativePath}`);
    return null;
  }
  return fs.readFileSync(absolutePath, 'utf8');
}

function importsOf(source) {
  return [...source.matchAll(/^\s*import\s+(\S+)/gm)].map(match => match[1]);
}

function countMatches(source, pattern) {
  return [...source.matchAll(pattern)].length;
}

function walkLeanFiles(relativeDirectory) {
  const absoluteDirectory = path.join(root, relativeDirectory);
  if (!fs.existsSync(absoluteDirectory)) return [];

  const files = [];
  const pending = [absoluteDirectory];
  while (pending.length > 0) {
    const directory = pending.pop();
    for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
      const absolutePath = path.join(directory, entry.name);
      if (entry.isDirectory()) {
        pending.push(absolutePath);
      } else if (entry.isFile() && entry.name.endsWith('.lean')) {
        files.push(path.relative(root, absolutePath));
      }
    }
  }
  return files;
}

const challengeSources = new Map(
  challengeFiles.map(file => [file, readRequired(file)]),
);

const challenge = challengeSources.get('Challenge.lean');
if (challenge !== null) {
  const imports = importsOf(challenge);
  if (imports.length === 0) {
    fail('Challenge.lean must import at least one Mathlib module.');
  }
  for (const moduleName of imports) {
    if (moduleName !== 'Mathlib' && !moduleName.startsWith('Mathlib.')) {
      fail(`Challenge.lean has a non-Mathlib import: ${moduleName}`);
    }
  }
}

const challengeTransfer = challengeSources.get('ChallengeTransfer.lean');
if (challengeTransfer !== null) {
  const imports = importsOf(challengeTransfer);
  if (imports.length !== 1 || imports[0] !== 'Challenge') {
    fail(
      'ChallengeTransfer.lean must import exactly Challenge; ' +
      `observed imports: ${imports.length === 0 ? '(none)' : imports.join(', ')}`,
    );
  }
}

const challengeForbidden =
  /(^|[^A-Za-z0-9_])(axiom|admit|opaque|unsafe|partial|native_decide|definition_names)(?=[^A-Za-z0-9_]|$)/g;
for (const [file, source] of challengeSources) {
  if (source === null) continue;

  const bySorryCount = countMatches(source, /\bby\s+sorry\b/g);
  const totalSorryCount = countMatches(source, /\bsorry\b/g);
  if (bySorryCount !== 1 || totalSorryCount !== 1) {
    fail(
      `${file} must contain exactly one 'by sorry' and no other sorry ` +
      `(by sorry: ${bySorryCount}; total sorry: ${totalSorryCount}).`,
    );
  }

  const forbidden = [...source.matchAll(challengeForbidden)].map(match => match[2]);
  if (forbidden.length > 0) {
    fail(`${file} contains forbidden token(s): ${[...new Set(forbidden)].join(', ')}`);
  }
}

const rootSolutionFiles = fs
  .readdirSync(root, { withFileTypes: true })
  .filter(entry => entry.isFile() && /^Solution.*\.lean$/.test(entry.name))
  .map(entry => entry.name);
const solutionFiles = [
  ...rootSolutionFiles,
  ...walkLeanFiles('ComparatorSupport'),
  ...walkLeanFiles(path.join('PaperC', 'ComparatorSupport')),
].sort();

for (const file of requiredSolutionFiles) {
  if (!solutionFiles.includes(file)) {
    fail(`required file is missing: ${file}`);
  }
}

const solutionForbidden =
  /(^|[^A-Za-z0-9_])(sorry|axiom|admit|opaque|unsafe|partial|native_decide|definition_names)(?=[^A-Za-z0-9_]|$)/g;
for (const file of solutionFiles) {
  const source = fs.readFileSync(path.join(root, file), 'utf8');
  const forbidden = [...source.matchAll(solutionForbidden)].map(match => match[2]);
  if (forbidden.length > 0) {
    fail(`${file} contains forbidden token(s): ${[...new Set(forbidden)].join(', ')}`);
  }
  if (/^\s*import\s+Challenge(?:\s|\.|$)/m.test(source)) {
    fail(`${file} imports a Challenge module.`);
  }
}

if (process.exitCode) process.exit(process.exitCode);
console.log(
  `Comparator source guard passed (${challengeFiles.length} challenges, ` +
  `${solutionFiles.length} solutions/support modules).`,
);
