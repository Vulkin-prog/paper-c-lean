#!/usr/bin/env python3
"""Validate the deliberately minimal 3PREL8 public payload and its TeX inputs."""
import hashlib
import json
import re
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]
TOP = {
    'paper_c_version_3PREL8_en.pdf', 'paper_c_version_3PREL8_technical_companion_en.pdf',
    'paper_c_version_3PREL8_en.tex', 'paper_c_version_3PREL8_technical_companion_en.tex',
    'preamble.tex', 'declarations.tex', 'references.bib', 'corpus.dbx', 'build.sh',
}


def safe_path(value):
    p = PurePosixPath(value)
    if not value or p.is_absolute() or '..' in p.parts or '\\' in value or str(p) != value:
        raise ValueError(f'Invalid payload path: {value!r}')
    return p


def check(root=ROOT, *, directory='manuscripts/v3prel8', version='3PREL8'):
    base = root / directory
    top = {name.replace('3PREL8', version) for name in TOP}
    if version == '3':
        top.add('formalization_v3_en.tex')
    expected_count = 29 if version == '3' else 28
    manifest = json.loads((base / 'manifest.json').read_text())
    if manifest['version'] != version:
        raise ValueError('Wrong manuscript version')
    entries = manifest['files']
    names = [str(safe_path(x['path'])) for x in entries]
    if len(names) != expected_count or len(set(names)) != expected_count:
        raise ValueError(f'Expected exactly {expected_count} distinct delivered files')
    actual = {p.relative_to(base).as_posix() for p in base.rglob('*') if p.is_file()}
    if actual != set(names) | {'README.md', 'manifest.json'}:
        raise ValueError('Unexpected or missing public payload file')
    if not top <= set(names):
        raise ValueError('Missing top-level compilation input or PDF')
    for item in entries:
        name = item['path']
        parts = safe_path(name).parts
        if name not in top and not (len(parts) == 2 and parts[0] in {'sections', 'companion'}
                                    and name.endswith('.tex')):
            raise ValueError(f'Nonessential payload file: {name}')
        p = base / name
        if any(q.is_symlink() for q in [p, *p.parents] if q != base.parent):
            raise ValueError(f'Symlink in public payload: {name}')
        data = p.read_bytes()
        if len(data) != item['size_bytes'] or hashlib.sha256(data).hexdigest() != item['sha256']:
            raise ValueError(f'Content mismatch: {name}')
    # Follow source directives without executing any delivered script or TeX.
    inputs = set()
    for name in names:
        if not name.endswith('.tex'):
            continue
        text = re.sub(r'(?<!\\)%[^\n]*', '', (base / name).read_text())
        for command, target in re.findall(r'\\(input|include|addbibresource)(?:\[[^]]*\])?\{([^}]+)\}', text):
            if command != 'addbibresource' and not target.endswith('.tex'):
                target += '.tex'
            safe_path(target)
            if target not in names:
                raise ValueError(f'Missing TeX input {target} from {name}')
            inputs.add(target)
    if 'references.bib' not in inputs:
        raise ValueError('Bibliography not connected to the delivered sources')
    return {'files': len(names), 'compilation_inputs': len(names)-2, 'pdfs': 2, 'status': 'verified'}


if __name__ == '__main__':
    try:
        print(json.dumps(check()))
    except (KeyError, OSError, ValueError) as error:
        raise SystemExit(f'3PREL8 payload check failed: {error}')
