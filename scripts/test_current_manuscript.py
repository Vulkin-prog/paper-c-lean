"""Publication boundary checks, without network, Lean, or TeX execution."""
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from check_current_manuscript import ROOT, check_publication


class PublishedV3Tests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.base = self.root / 'manuscripts/paper-c'
        shutil.copytree(ROOT / 'manuscripts/paper-c', self.base)

    def rewrite_manifest(self, update):
        path = self.base / 'manifest.json'
        data = json.loads(path.read_text())
        update(data)
        path.write_text(json.dumps(data))

    def refresh_entry(self, name):
        content = (self.base / name).read_bytes()
        def update(data):
            entry = next(x for x in data['files'] if x['path'] == name)
            entry.update(size_bytes=len(content), sha256=hashlib.sha256(content).hexdigest())
        self.rewrite_manifest(update)

    def test_published_package_passes(self):
        result = check_publication(self.root)
        self.assertEqual((result['files'], result['compilation_inputs']), (29, 27))

    def test_manifest_cannot_retarget_published_pdf(self):
        name = 'paper_c_version_3_en.pdf'
        (self.base / name).write_bytes(b'%PDF-different-publication')
        self.refresh_entry(name)
        with self.assertRaisesRegex(ValueError, 'Wrong published PDF'):
            check_publication(self.root)

    def test_concept_doi_is_not_the_version_doi(self):
        self.rewrite_manifest(lambda d: d['publication'].update(doi='10.5281/zenodo.21736676'))
        with self.assertRaisesRegex(ValueError, 'Wrong published DOI'):
            check_publication(self.root)

    def test_original_download_name_cannot_drift(self):
        self.rewrite_manifest(lambda d: d['publication']['pdf_downloads'][0].update(remote_name='other.pdf'))
        with self.assertRaisesRegex(ValueError, 'download provenance'):
            check_publication(self.root)

    def test_formalization_section_is_required(self):
        (self.base / 'formalization_v3_en.tex').unlink()
        with self.assertRaisesRegex(ValueError, 'Unexpected or missing'):
            check_publication(self.root)

    def test_rehashed_source_cannot_change_registered_identifier(self):
        name = 'formalization_v3_en.tex'
        path = self.base / name
        path.write_text(path.read_text().replace('PALOMAR-2026-09-21-000003', 'PALOMAR-2026-09-21-999999'))
        self.refresh_entry(name)
        with self.assertRaisesRegex(ValueError, 'Palomar identifiers differ'):
            check_publication(self.root)


if __name__ == '__main__':
    unittest.main()
