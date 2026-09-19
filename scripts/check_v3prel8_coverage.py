#!/usr/bin/env python3
"""Check the complete numbered inventory without treating partial work as coverage."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ENV = r'theorem|lemma|proposition|corollary|remark|empiricalcorollary|empiricalobstruction|dyadiccorollary'


def blocks(base):
    result = {}
    for path in sorted(base.rglob('*.tex')):
        text = re.sub(r'(?<!\\)%[^\n]*', '', path.read_text())
        for match in re.finditer(r'\\begin\{(' + ENV + r')\}(.*?)\\end\{\1\}', text, re.S):
            labels = re.findall(r'\\label\{([^}]+)\}', match[2])
            if not labels:
                raise ValueError(f'Unlabelled statement in {path}')
            if labels[0] in result:
                raise ValueError(f'Duplicate statement label {labels[0]}')
            result[labels[0]] = (path, match[0])
    return result


def check(root=ROOT):
    base = root / 'manuscripts/v3prel8'
    current = blocks(base)
    old = blocks(root / 'manuscripts/v3prel/source')
    data = json.loads((root / 'docs/FORMALIZATION_COVERAGE_V3PREL8.json').read_text())
    rows = data['numbered']
    if len(rows) != 96 or len({x['label'] for x in rows}) != 96 or set(current) != {x['label'] for x in rows}:
        raise ValueError('Coverage inventory must match all 96 numbered blocks exactly')
    preserved = 0
    extended = 0
    new = 0
    for row in rows:
        label = row['label']
        path, statement = current[label]
        if path != root / row['source'] or hashlib.sha256(statement.encode()).hexdigest() != row['statement_sha256']:
            raise ValueError(f'Stale statement identity: {label}')
        unchanged = label in old and re.sub(r'\s+', ' ', old[label][1]) == re.sub(r'\s+', ' ', statement)
        if unchanged:
            preserved += 1
            if row['status'] != 'preserved_statement':
                raise ValueError(f'Incorrect baseline status: {label}')
        elif label in old:
            extended += 1
            if not row['status'].startswith('extended_statement_'):
                raise ValueError(f'Extended statement presented as preserved: {label}')
        else:
            new += 1
            if not row['status'].startswith('new_statement_'):
                raise ValueError(f'New statement presented as preserved: {label}')
        for component in row['new_lean_components']:
            source = (root / component['path']).read_text()
            if not re.search(r'(?m)^theorem\s+' + re.escape(component['declaration']) + r'\b', source):
                raise ValueError(f'Missing Lean component for {label}')
            if not component['scope']:
                raise ValueError(f'Missing component limitation for {label}')
    expected = {'numbered_blocks': 96, 'preserved_statements': preserved,
                'extended_statements': extended, 'new_statements': new}
    if data['counts'] != expected:
        raise ValueError('Coverage counts differ from source comparison')
    return expected


if __name__ == '__main__':
    try:
        print(json.dumps(check()))
    except (KeyError, OSError, ValueError) as error:
        raise SystemExit(f'3PREL8 correspondence check failed: {error}')
