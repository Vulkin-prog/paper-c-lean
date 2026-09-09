"""Exercise the actual runner functions against small local Git repositories.

No Lean, network, tool download, or official replay is involved.
"""

from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
RUNNERS = (ROOT / "palomar/verify-comparator.sh",
           ROOT / "palomar/v3prel/verify-comparator.sh")


def git(directory, *args):
    return subprocess.check_output(
        ["git", "-C", str(directory), *args], text=True, stderr=subprocess.PIPE,
    ).strip()


def checkout_function(runner):
    matches = re.findall(r"^checkout_exact\(\) \{\n.*?^\}", runner.read_text(),
                         flags=re.MULTILINE | re.DOTALL)
    if len(matches) != 1:
        raise AssertionError(f"Expected one checkout_exact function in {runner}")
    return matches[0]


class CheckoutExactTests(unittest.TestCase):
    def exercise(self, state):
        for runner in RUNNERS:
            with self.subTest(runner=runner.relative_to(ROOT), state=state):
                with tempfile.TemporaryDirectory(prefix="palomar-checkout-test-") as tmp:
                    root = Path(tmp)
                    origin = root / "origin"
                    origin.mkdir()
                    git(origin, "init", "-q")
                    (origin / "tracked.txt").write_text("pinned source\n")
                    git(origin, "add", "tracked.txt")
                    git(origin, "-c", "user.name=Local Test", "-c",
                        "user.email=local-test@example.invalid", "commit", "-qm", "fixture")
                    commit = git(origin, "rev-parse", "HEAD")
                    destination = root / "cache"
                    git(root, "clone", "-q", str(origin), str(destination))
                    tracked = destination / "tracked.txt"
                    if state in ("unstaged", "staged"):
                        tracked.write_text("local modified source\n")
                        if state == "staged":
                            git(destination, "add", "tracked.txt")
                    artifact = destination / "untracked-build-output"
                    artifact.write_text("keep cached build output\n")
                    before_worktree = tracked.read_bytes()
                    before_index = git(destination, "show", ":tracked.txt")
                    command = ("set -euo pipefail\n" + checkout_function(runner) +
                               '\ncheckout_exact "$1" "$2" "$3"\n' +
                               'printf "CHECKOUT_ACCEPTED\\n"\n')
                    result = subprocess.run(
                        ["bash", "-c", command, "checkout-test", str(origin),
                         str(destination), commit], capture_output=True, text=True,
                    )
                    self.assertEqual(git(destination, "rev-parse", "HEAD"), commit)
                    self.assertEqual(tracked.read_bytes(), before_worktree)
                    self.assertEqual(git(destination, "show", ":tracked.txt"), before_index)
                    self.assertEqual(artifact.read_text(), "keep cached build output\n")
                    if state == "clean":
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertIn("CHECKOUT_ACCEPTED", result.stdout)
                    else:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertNotIn("CHECKOUT_ACCEPTED", result.stdout)
                        self.assertIn("tracked files differ from pinned commit", result.stderr)
                        self.assertIn("cache preserved", result.stderr)

    def test_exact_clean_head_accepts_and_preserves_untracked_artifacts(self):
        self.exercise("clean")

    def test_unstaged_tracked_change_rejects_without_removing_it(self):
        self.exercise("unstaged")

    def test_staged_tracked_change_rejects_without_removing_it(self):
        self.exercise("staged")


if __name__ == "__main__":
    unittest.main()
