#!/usr/bin/env python3
"""Verify the frozen author-supplied V3PREL pair and complete source payload.

This checks artifact identity, not the truth of the manuscript or its Lean
correspondence. The manifest is reviewable source; it is not a digital signature.
"""
import hashlib
import json
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]
PDFS = {
    'paper_C_version_3PREL_en.pdf': '0ec4144dc81c4ee9930a8e4e4815ae274da36e3c1ebeae4a5c0ffa411853a9d7',
    'paper_C_version_3PREL_technical_companion_en.pdf': 'd64150c995f07ee39b016bb20a16b5fc3a01ce53b0ddcda893d1ceb41eefadee',
}


def relative_path(value):
    path = PurePosixPath(value)
    if not value or path.is_absolute() or '..' in path.parts or '\\' in value or str(path) != value:
        raise ValueError(f'Invalid source path: {value!r}')
    return path


def check(root=ROOT):
    base = root / 'manuscripts/v3prel'
    data = json.loads((base / 'manifest.json').read_text())
    if data['version'] != '3PREL' or data['lean_namespace_retained'] != 'PaperC.V282':
        raise ValueError('Unexpected manuscript version or Lean namespace')
    entries = data['files']
    names = [str(relative_path(e['path'])) for e in entries]
    if len(names) != 36 or len(set(names)) != len(names):
        raise ValueError('Expected 36 distinct delivered files')
    actual = {str(p.relative_to(base)) for p in (base / 'source').rglob('*') if p.is_file()}
    actual.update(p.name for p in base.glob('*.pdf'))
    if actual != set(names):
        raise ValueError('Delivered source/PDF inventory differs from manifest')
    for e in entries:
        path = base / e['path']
        if path.is_symlink() or any(p.is_symlink() for p in path.parents if p != base.parent):
            raise ValueError(f'Symlink in delivered source: {e["path"]}')
        content = path.read_bytes()
        digest = hashlib.sha256(content).hexdigest()
        if len(content) != e['size_bytes'] or digest != e['sha256']:
            raise ValueError(f'Content identity mismatch: {e["path"]}')
        if e['path'] in PDFS and digest != PDFS[e['path']]:
            raise ValueError(f'PDF differs from the author-supplied release: {e["path"]}')
    checksums = set()
    for line in (base / 'source/SHA256SUMS').read_text().splitlines():
        digest, name = line.split(maxsplit=1)
        path = relative_path(name)
        if name in checksums:
            raise ValueError('Duplicate original source checksum')
        checksums.add(name)
        if hashlib.sha256((base / 'source' / path).read_bytes()).hexdigest() != digest:
            raise ValueError(f'Original source checksum mismatch: {name}')
    expected = {n.removeprefix('source/') for n in names if n.startswith('source/')}
    if checksums != expected - {'SHA256SUMS'}:
        raise ValueError('Original source checksum list is incomplete')
    return len(entries)


if __name__ == '__main__':
    try:
        count = check()
    except (ValueError, KeyError, OSError) as error:
        raise SystemExit(f'V3PREL source check failed: {error}')
    print(f'V3PREL: {count} delivered files verified; both PDF identities and original source checksums match')
