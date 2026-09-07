#!/usr/bin/env python3
"""Optional structural PDF preflight (requires PyMuPDF).

This checks PDF integrity, text bounds, embedded fonts and internal/cross-document
link destinations. It does not validate the mathematics or replace visual review.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path


def run(root: Path) -> dict:
    try:
        import fitz
    except ImportError as exc:
        raise SystemExit('Optional PDF audit requires PyMuPDF (import fitz).') from exc
    filenames = [
        'paper_C_version_3PREL_en.pdf',
        'paper_C_version_3PREL_technical_companion_en.pdf',
    ]
    docs = {}
    try:
        for name in filenames:
            if not (root / name).is_file():
                raise FileNotFoundError(root / name)
            docs[name] = fitz.open(root / name)
        destinations = {name: doc.resolve_names() for name, doc in docs.items()}
        outputs = {}
        for name, doc in docs.items():
            errors: list[dict] = []
            links = Counter()
            fonts: dict[int, tuple] = {}
            chars = []
            page_sizes = set()
            for index, page in enumerate(doc):
                page_sizes.add((round(page.rect.width, 3), round(page.rect.height, 3)))
                text = page.get_text('text')
                chars.append(len(text.strip()))
                if len(text.strip()) < 40:
                    errors.append({'page': index+1, 'issue': 'nearly empty page'})
                if re.search(r'migration note|detached verification|working (?:draft|version)|revision log|recorded valuation correction', text, re.I):
                    errors.append({'page': index+1, 'issue': 'excluded working-history phrase'})
                if '\ufffd' in text:
                    errors.append({'page': index+1, 'issue': 'replacement character in extracted text'})
                for block in page.get_text('dict')['blocks']:
                    if block.get('type') != 0:
                        continue
                    for line in block.get('lines', []):
                        for span in line.get('spans', []):
                            if not span.get('text', '').strip():
                                continue
                            x0,y0,x1,y1 = span['bbox']
                            if x0 < -1 or y0 < -1 or x1 > page.rect.width+1 or y1 > page.rect.height+1:
                                errors.append({'page': index+1, 'issue': 'text outside page', 'text': span['text']})
                for font in page.get_fonts(full=True):
                    fonts[font[0]] = font
                for link in page.get_links():
                    kind = link['kind']
                    links[str(kind)] += 1
                    if kind in (fitz.LINK_GOTO, fitz.LINK_NAMED):
                        if not (0 <= link.get('page', -1) < len(doc)):
                            errors.append({'page': index+1, 'issue': 'unresolved internal link', 'link': str(link)})
                        dest = link.get('nameddest')
                        if dest and dest not in destinations[name]:
                            errors.append({'page': index+1, 'issue': 'missing internal named destination', 'destination': dest})
                    elif kind in (fitz.LINK_LAUNCH, fitz.LINK_GOTOR):
                        target, sep, fragment = link.get('file', '').partition('#nameddest=')
                        if target not in docs or not sep or fragment not in destinations.get(target, {}):
                            errors.append({'page': index+1, 'issue': 'unresolved companion link', 'file': link.get('file')})
                    elif kind == fitz.LINK_URI:
                        if not link.get('uri', '').startswith(('https://', 'http://')):
                            errors.append({'page': index+1, 'issue': 'unexpected URI scheme'})
            for xref, font in fonts.items():
                font_bytes = doc.extract_font(xref)[3]
                if not font_bytes:
                    errors.append({'issue': 'font not embedded', 'font': font[3], 'xref': xref})
            outputs[name] = {
                'pages': len(doc),
                'sha256': hashlib.sha256((root/name).read_bytes()).hexdigest(),
                'file_bytes': (root/name).stat().st_size,
                'page_sizes_pt': sorted(page_sizes),
                'text_characters_per_page': chars,
                'embedded_font_count': len(fonts),
                'link_kind_counts': dict(links),
                'internal_and_cross_document_destinations_checked': True,
                'external_urls_live_checked': False,
                'errors': errors,
            }
        return {
            'revision': '3PREL',
            'status': 'PASS' if all(not x['errors'] for x in outputs.values()) else 'FAIL',
            'engine': f'PyMuPDF {fitz.VersionBind}',
            'scope': 'PDF structural checks, not mathematical certification or a substitute for visual inspection.',
            'files': outputs,
        }
    finally:
        for doc in docs.values():
            doc.close()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path, default=Path('build_reports/PDF_QA.json'))
    args = parser.parse_args()
    result = run(args.root.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    raise SystemExit(0 if result['status'] == 'PASS' else 1)

if __name__ == '__main__':
    main()
