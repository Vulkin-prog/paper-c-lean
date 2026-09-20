#!/usr/bin/env python3
"""Require the exact new theorem inventory and only Lean's foundational axioms."""
import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def source_names(root=ROOT):
    names = []
    for path in sorted((root / 'PaperCPrel8').glob('*.lean')):
        if path.name == 'Audit.lean':
            continue
        text = path.read_text()
        namespace = re.search(r'^namespace (\S+)', text, re.M)[1]
        names.extend(namespace + '.' + name for name in re.findall(r'^theorem (\w+)', text, re.M))
    return names


def check(log, root=ROOT):
    expected = json.loads((root / 'PaperCPrel8/audit-names.json').read_text())
    if expected != source_names(root):
        raise ValueError('New theorem source inventory differs from the audited names')
    declared = re.findall(r'^#print axioms (\S+)', (root / 'PaperCPrel8/Audit.lean').read_text(), re.M)
    if declared != expected:
        raise ValueError('Audit commands differ from the exact inventory')
    if re.search(r'\berror:|\berror\(|declaration uses .sorry.', log):
        raise ValueError('Lean reported a compilation error or proof hole')
    found = []
    for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log, re.S):
        axioms = set(filter(None, re.split(r'[\s,]+', m[2] or '')))
        if not axioms <= ALLOWED:
            raise ValueError(f'Unexpected axioms for {m[1]}: {axioms - ALLOWED}')
        found.append(m[1])
    if found != expected:
        raise ValueError(f'Expected {len(expected)} ordered audit records, found {len(found)}')
    return {'status': 'passed', 'theorems': len(found), 'allowed_axioms': sorted(ALLOWED)}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--log', type=Path, required=True)
    args = parser.parse_args()
    try:
        print(json.dumps(check(args.log.read_text())))
    except (KeyError, OSError, ValueError) as error:
        raise SystemExit(f'3PREL8 axiom audit failed: {error}')
