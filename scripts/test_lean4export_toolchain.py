"""Fail-closed exporter/compiler identity tests; no Lean or network execution."""

import importlib.util
from pathlib import Path
import subprocess
import sys
import unittest

CHECKER = Path(__file__).resolve().parents[1] / "palomar/check_exporter_toolchain.py"
SPEC = importlib.util.spec_from_file_location("exporter_toolchain", CHECKER)
assert SPEC is not None and SPEC.loader is not None
guard = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(guard)

GOOD_VERSION = (
    "Lean (version 4.33.1, x86_64-unknown-linux-gnu, "
    "commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)"
)


class ExporterToolchainTests(unittest.TestCase):
    def check(self, *, project=guard.PROJECT_TOOLCHAIN,
              source=guard.EXPORTER_SOURCE_TOOLCHAIN, version=GOOD_VERSION):
        return guard.validate(project, source, version)

    def test_patch_zero_source_uses_exact_patch_one_compiler(self):
        evidence = self.check()
        self.assertNotEqual(evidence["lean4export_source_toolchain"],
                            evidence["lean4export_build_toolchain"])
        self.assertEqual(evidence["lean4export_compiler_commit"], guard.LEAN_COMMIT)

    def test_project_version_is_not_inferred_from_the_exporter(self):
        for project in ["leanprover/lean4:v4.33.0", "leanprover/lean4:v4.32.0",
                        "leanprover/lean4:v4.33.1-rc1"]:
            with self.subTest(project=project), self.assertRaises(ValueError):
                self.check(project=project)

    def test_other_exporter_sources_are_not_implicitly_allowed(self):
        for source in ["leanprover/lean4:v4.32.0", "leanprover/lean4:v4.34.0",
                       "leanprover/lean4:v4.33.1", "leanprover/lean4:v4.33.0-rc1"]:
            with self.subTest(source=source), self.assertRaises(ValueError):
                self.check(source=source)

    def test_correct_declared_toolchains_do_not_hide_old_compiler(self):
        with self.assertRaises(ValueError):
            self.check(version=GOOD_VERSION.replace("version 4.33.1", "version 4.33.0"))

    def test_same_version_with_wrong_commit_is_rejected(self):
        with self.assertRaises(ValueError):
            self.check(version=GOOD_VERSION.replace(guard.LEAN_COMMIT, "0" * 40))

    def test_missing_short_or_ambiguous_identity_is_rejected(self):
        for version in ["", "Lean 4.33.1", GOOD_VERSION + "\n" + GOOD_VERSION,
                        GOOD_VERSION.replace(guard.LEAN_COMMIT, guard.LEAN_COMMIT[:12]),
                        GOOD_VERSION.replace("Release", "Debug")]:
            with self.subTest(version=version), self.assertRaises(ValueError):
                self.check(version=version)

    def test_line_endings_do_not_change_the_identified_release(self):
        evidence = self.check(version=GOOD_VERSION + "\r\n")
        self.assertEqual(evidence["lean4export_compiler_version"], GOOD_VERSION)

    def test_cli_returns_failure_for_runtime_mismatch(self):
        for version, expected in [(GOOD_VERSION, 0), ("Lean 4.32.0", 1)]:
            result = subprocess.run(
                [sys.executable, "-B", str(CHECKER), guard.PROJECT_TOOLCHAIN,
                 guard.EXPORTER_SOURCE_TOOLCHAIN, version],
                capture_output=True, text=True, check=False,
            )
            self.assertEqual(result.returncode, expected, result.stderr)


if __name__ == "__main__":
    unittest.main()
