"""Release admission regressions; no network or package installation."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    "canonical_mathlib_tag", Path(__file__).resolve().parents[1] / "palomar/canonical_mathlib_tag.py")
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
COMMIT, OBJECT, OTHER = "a" * 40, "b" * 40, "c" * 40


class CanonicalReleaseTests(unittest.TestCase):
    def test_lightweight_release_and_rc(self):
        listing = f"{COMMIT}\trefs/tags/v4.34.0\n{COMMIT}\trefs/tags/v4.34.0-rc1\n"
        self.assertEqual(guard.matching_tags(listing, COMMIT), ["v4.34.0", "v4.34.0-rc1"])

    def test_annotated_release_uses_peeled_commit(self):
        listing = f"{OBJECT}\trefs/tags/v4.34.0\n{COMMIT}\trefs/tags/v4.34.0^{{}}\n"
        self.assertEqual(guard.matching_tags(listing, COMMIT), ["v4.34.0"])
        self.assertEqual(guard.matching_tags(listing, OBJECT), [])

    def test_nightly_arbitrary_branch_and_near_matches_are_rejected(self):
        refs = ["refs/tags/nightly-2026-09-19", "refs/tags/release", "refs/heads/v4.34.0",
                "refs/tags/v4.34.0-extra", "refs/tags/v4.34", "refs/tags/4.34.0"]
        self.assertEqual(guard.matching_tags("\n".join(f"{COMMIT}\t{r}" for r in refs), COMMIT), [])

    def test_unrelated_commit_is_rejected(self):
        self.assertEqual(guard.matching_tags(f"{OTHER}\trefs/tags/v4.34.0", COMMIT), [])

    def test_malformed_and_conflicting_identities_are_rejected(self):
        self.assertEqual(guard.matching_tags("short\trefs/tags/v4.34.0", COMMIT), [])
        with self.assertRaises(ValueError):
            guard.matching_tags("", "short")
        with self.assertRaises(ValueError):
            guard.matching_tags(f"{COMMIT}\trefs/tags/v4.34.0\n{OTHER}\trefs/tags/v4.34.0", COMMIT)


if __name__ == "__main__":
    unittest.main()
