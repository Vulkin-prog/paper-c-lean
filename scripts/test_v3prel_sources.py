import json
from pathlib import Path
import shutil
import tempfile
import unittest

from check_v3prel_sources import ROOT, check


class FrozenManuscriptTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.base = self.root / 'manuscripts/v3prel'
        shutil.copytree(ROOT / 'manuscripts/v3prel', self.base)

    def test_original_passes(self):
        self.assertEqual(check(self.root), 36)

    def test_edited_source_fails(self):
        path = self.base / 'source/companion/C_fields.tex'
        path.write_text(path.read_text() + '\n% modified\n')
        with self.assertRaisesRegex(ValueError, 'identity mismatch'):
            check(self.root)

    def test_unlisted_source_fails(self):
        (self.base / 'source/extra.tex').write_text('extra')
        with self.assertRaisesRegex(ValueError, 'inventory differs'):
            check(self.root)

    def test_parent_path_fails_before_read(self):
        path = self.base / 'manifest.json'
        data = json.loads(path.read_text())
        data['files'][0]['path'] = '../outside'
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'Invalid source path'):
            check(self.root)

    def test_manifest_cannot_retarget_pdf(self):
        path = self.base / 'manifest.json'
        data = json.loads(path.read_text())
        entry = next(e for e in data['files'] if e['path'].endswith('_en.pdf'))
        payload = b'changed PDF'
        (self.base / entry['path']).write_bytes(payload)
        import hashlib
        entry.update(size_bytes=len(payload), sha256=hashlib.sha256(payload).hexdigest())
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'author-supplied release'):
            check(self.root)


if __name__ == '__main__':
    unittest.main()
