#!/usr/bin/env python3
"""Check the current manuscript's byte identity and recorded Lean correspondence.

This verifies a source-bound review; it does not prove that a prose argument is
correct, discharge literature premises, or replace Lean/Comparator execution.
"""
import hashlib
import json
import re
from pathlib import Path

from check_v3prel8_sources import check as check_payload
from check_v3prel8_coverage import blocks, check as check_baseline

ROOT = Path(__file__).resolve().parents[1]
PROOF = re.compile(r'\\begin\{proof\}(.*?)\\end\{proof\}', re.S)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def clean(text):
    return re.sub(r'(?<!\\)%[^\n]*', '', text)


def normalized(text):
    return re.sub(r'\s+', ' ', text)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check(root=ROOT):
    payload = check_payload(root, directory='manuscripts/paper-c', version='3PREL9')
    check_baseline(root)
    data = json.loads((root / 'docs/MANUSCRIPT_ALIGNMENT.json').read_text())
    require(data['version'] == '3PREL9', 'Unexpected manuscript version')
    for record in data['baseline_evidence']:
        require(digest((root / record['path']).read_bytes()) == record['sha256'],
                f'Stale baseline evidence: {record["path"]}')
    receipt = json.loads((root / 'extension_evidence/v3prel8/realignment-final/validation.json').read_text())
    for record in receipt['source_files']:
        require(digest((root / record['path']).read_bytes()) == record['sha256'],
                f'Lean source differs from recorded validation: {record["path"]}')

    old = blocks(root / 'manuscripts/v3prel8')
    current = blocks(root / 'manuscripts/paper-c')
    require(set(old) == set(current), 'Numbered statement labels changed')
    rows = data['numbered']
    require(len(rows) == len(current) == 96 and {r['label'] for r in rows} == set(current),
            'Incomplete numbered correspondence')
    changed = []
    for row in rows:
        label = row['label']
        path, statement = current[label]
        require(str(path.relative_to(root)) == row['source'] and
                digest(statement.encode()) == row['statement_sha256'],
                f'Stale statement locator: {label}')
        require('\\label{' + label + '}' in path.read_text().splitlines()[row['line'] - 1],
                f'Stale line number: {label}')
        same = normalized(statement) == normalized(old[label][1])
        relation = 'unchanged' if same else 'ambient_hypotheses_made_explicit'
        require(row['relation'] == relation and row['baseline_label'] == label,
                f'Incorrect statement relation: {label}')
        if not same:
            changed.append(label)
    require(changed == ['supp:palm:lem:crt'], 'Unreviewed statement change')
    prior = json.loads((root / 'docs/FORMALIZATION_COVERAGE_V3PREL8.json').read_text())
    crt = next(r for r in prior['numbered'] if r['label'] == changed[0])
    require(data['clarified_statement_proofs'] == crt['new_lean_components'],
            'G.2 must retain its complete existing proof correspondence')

    expected = {str(p.relative_to(root)) for p in (root / 'manuscripts/paper-c').rglob('*.tex')}
    records = data['files']
    require(len(records) == len(expected) and {r['source'] for r in records} == expected,
            'Every TeX source must be reviewed exactly once')
    changed_proofs = []
    proof_count = same_proofs = 0
    old_labels, new_labels = [], []
    for record in records:
        a_path, b_path = root / record['baseline'], root / record['source']
        a, b = a_path.read_bytes(), b_path.read_bytes()
        require(digest(a) == record['baseline_sha256'] and digest(b) == record['sha256'],
                f'Stale whole-file review: {record["source"]}')
        require(record['changed'] == (a != b), 'Incorrect file-change flag')
        before, after = clean(a.decode()), clean(b.decode())
        old_labels.extend(re.findall(r'\\label\{([^}]+)\}', before))
        new_labels.extend(re.findall(r'\\label\{([^}]+)\}', after))
        aa, bb = PROOF.findall(before), PROOF.findall(after)
        require(len(aa) == len(bb), 'Inserted or deleted proof block needs review')
        proof_count += len(aa)
        for i, (x, y) in enumerate(zip(aa, bb), 1):
            if normalized(x) == normalized(y):
                same_proofs += 1
            else:
                changed_proofs.append({'source': record['source'], 'proof_index': i,
                                       'old_sha256': digest(x.encode()),
                                       'new_sha256': digest(y.encode())})
    require(changed_proofs == data['changed_proof_blocks'], 'Stale proof-block review')
    require(sorted(old_labels) == sorted(new_labels), 'Manuscript label keys changed')
    counts = {'statements': 96, 'unchanged_statements': 95, 'clarified_statements': 1,
              'proof_blocks': proof_count, 'unchanged_proof_blocks': same_proofs}
    require(counts == data['counts'], 'Incorrect comparison counts')
    return {**payload, **counts, 'lean_source_files_matched': len(receipt['source_files']),
            'new_lean_build': False, 'new_palomar_qualification': False}


if __name__ == '__main__':
    try:
        print(json.dumps(check()))
    except (KeyError, OSError, ValueError, IndexError) as error:
        raise SystemExit(f'Current manuscript check failed: {error}')
