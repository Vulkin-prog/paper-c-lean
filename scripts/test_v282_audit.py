"""Failure-path tests for the development overlay's independent axiom gate."""

from pathlib import Path
import shutil
import tempfile
import unittest

from check_v282_audit import ROOT, check_log, check_pins, declarations, inventory


class AuditTests(unittest.TestCase):
    def test_accepts_standard_and_empty_dependencies(self):
        check_log("'A' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
                  "'B' does not depend on any axioms\n", ["A", "B"])

    def test_rejects_nonstandard_dependencies(self):
        for name in ("sorryAx", "Lean.ofReduceBool", "Unproved.assumption"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                check_log(f"'A' depends on axioms: [{name}]\n", ["A"])

    def test_rejects_missing_extra_duplicate_and_diagnostics(self):
        valid = "'A' depends on axioms: [propext]\n"
        for log in ("", valid * 2, valid + "'B' does not depend on any axioms\n",
                    "error: kernel failure\n" + valid, valid + "warning: audit incomplete\n"):
            with self.subTest(log=log), self.assertRaises(ValueError):
                check_log(log, ["A"])

    def test_nested_comments_and_placeholders(self):
        prefix = "namespace PaperC.V282.Test\n/- /- sorry -/ axiom -/\n"
        self.assertEqual(declarations(prefix + "theorem t : True := by trivial", "test"),
                         ["PaperC.V282.Test.t"])
        with self.assertRaises(ValueError):
            declarations(prefix + "theorem t : False := by sorry", "test")

    def test_rejects_uninventoried_declaration_forms(self):
        source = "namespace PaperC.V282.Test\ntheorem t : True := by trivial\n"
        for command in ("abbrev untracked : Nat := 0", "instance untracked : Inhabited Nat := ⟨0⟩",
                        "constant untracked : Nat", "example : True := by trivial"):
            with self.subTest(command=command), self.assertRaises(ValueError):
                declarations(source + command, "test")

    def test_missing_inventory_and_unimported_module(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            shutil.copytree(ROOT / "PaperCV282", root / "PaperCV282")
            shutil.copy(ROOT / "PaperCV282.lean", root / "PaperCV282.lean")
            self.assertTrue(inventory(root))
            audit = root / "PaperCV282/Audit.lean"
            original = audit.read_text()
            audit.write_text(original[:original.rfind("#print axioms")])
            with self.assertRaises(ValueError):
                inventory(root)
            audit.write_text(original)
            (root / "PaperCV282/New.lean").write_text(
                "namespace PaperC.V282.New\ntheorem t : True := by trivial\nend PaperC.V282.New\n")
            with self.assertRaises(ValueError):
                inventory(root)
            (root / "PaperCV282/New.lean").unlink()
            (root / "PaperCV282/Sub").mkdir()
            (root / "PaperCV282/Sub/Main.lean").write_text(
                "namespace PaperC.V282.Sub\ntheorem t : True := by trivial\nend PaperC.V282.Sub\n")
            with self.assertRaises(ValueError):
                inventory(root)

    def test_rejects_toolchain_and_dependency_drift(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            files = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")
            for file in files:
                shutil.copy(ROOT / file, root / file)
            check_pins(root)
            for file in files:
                path = root / file
                original = path.read_text()
                path.write_text(original.replace("v4.32.0", "v4.32.2"))
                with self.subTest(file=file), self.assertRaises(ValueError):
                    check_pins(root)
                path.write_text(original)


if __name__ == "__main__":
    unittest.main()
