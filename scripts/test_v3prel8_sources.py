import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path

from check_v3prel8_sources import ROOT, check


class CuratedPayloadTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.base = self.root / 'manuscripts/v3prel8'
        shutil.copytree(ROOT / 'manuscripts/v3prel8', self.base)

    def test_exact_payload(self):
        self.assertEqual(check(self.root)['files'], 28)

    def test_modified_source_rejected(self):
        p = self.base / 'preamble.tex'
        p.write_bytes(p.read_bytes() + b'\n% mutation\n')
        with self.assertRaisesRegex(ValueError, 'Content mismatch'):
            check(self.root)

    def test_internal_archive_rejected(self):
        (self.base / 'old-release.zip').write_bytes(b'not a public input')
        with self.assertRaisesRegex(ValueError, 'Unexpected'):
            check(self.root)

    def test_duplicate_manifest_entry_rejected(self):
        p = self.base / 'manifest.json'
        d = json.loads(p.read_text())
        d['files'][-1] = copy.deepcopy(d['files'][0])
        p.write_text(json.dumps(d))
        with self.assertRaisesRegex(ValueError, 'distinct'):
            check(self.root)

    def test_symlink_rejected(self):
        p = self.base / 'references.bib'
        target = self.root / 'external.bib'
        p.rename(target)
        p.symlink_to(target)
        with self.assertRaisesRegex(ValueError, 'Symlink'):
            check(self.root)
