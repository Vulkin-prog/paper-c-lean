import unittest
from check_prel8_audit import check, source_names


class AuditTests(unittest.TestCase):
    def transcript(self):
        return '\n'.join(f"'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in source_names())

    def test_complete_inventory(self):
        self.assertEqual(check(self.transcript())['theorems'], len(source_names()))

    def test_missing_record(self):
        with self.assertRaisesRegex(ValueError, 'ordered audit'):
            check(self.transcript().split('\n', 1)[1])

    def test_duplicate_record(self):
        with self.assertRaisesRegex(ValueError, 'ordered audit'):
            check(self.transcript() + '\n' + self.transcript().split('\n')[0])

    def test_proof_hole(self):
        with self.assertRaisesRegex(ValueError, 'Unexpected axioms'):
            check(self.transcript().replace('propext', 'sorryAx', 1))

    def test_error_even_with_complete_inventory(self):
        with self.assertRaisesRegex(ValueError, 'compilation error'):
            check('error: failed\n' + self.transcript())
