#!/usr/bin/env python3
"""Self-test the public-only post-publication release verifier."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
ARCHIVE_DIR = Path(
    "/home/vulkin/paper-c-hardened-public-"
    "ea8775e09f09c2e480c2c232886e38363d8066dd-20260813"
)
ARCHIVE_NAME = (
    "paper-c-hardened-public-"
    "ea8775e09f09c2e480c2c232886e38363d8066dd.tar.zst"
)
PACKAGING = "a580c1346c1d1cc3ae57b307676cd9f593015893"


def run(arguments: list[str], expect_failure: bool = False) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        [sys.executable, "scripts/verify_published_release_assets.py", *arguments],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if (result.returncode == 0) == expect_failure:
        raise RuntimeError(
            f"unexpected status for {arguments}: {result.returncode}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def arguments(directory: Path, report: str) -> list[str]:
    return [
        "--repository", str(ROOT), "--packaging-commit", PACKAGING,
        "--release-tag", "v0.48.1", "--archive", str(directory / ARCHIVE_NAME),
        "--checksum", str(directory / f"{ARCHIVE_NAME}.sha256"),
        "--receipt", str(directory / f"{ARCHIVE_NAME}.verified.json"),
        "--report", str(directory / report),
    ]


def copy_triplet(directory: Path) -> None:
    for suffix in ("", ".sha256", ".verified.json"):
        shutil.copyfile(ARCHIVE_DIR / f"{ARCHIVE_NAME}{suffix}", directory / f"{ARCHIVE_NAME}{suffix}")


def main() -> int:
    if not (ARCHIVE_DIR / ARCHIVE_NAME).is_file():
        print("post-publication self-test skipped: local candidate archive is unavailable")
        return 0
    with tempfile.TemporaryDirectory(prefix="paper-c-post-publication-test.") as name:
        temporary = Path(name)
        positive = temporary / "positive"
        positive.mkdir()
        copy_triplet(positive)
        run(arguments(positive, "report.json"))
        report = json.loads((positive / "report.json").read_text())
        if report.get("status") != "published_release_assets_verified":
            raise RuntimeError("positive post-publication report status is wrong")

        archive_negative = temporary / "archive-negative"
        archive_negative.mkdir()
        copy_triplet(archive_negative)
        target = archive_negative / ARCHIVE_NAME
        target.write_bytes(target.read_bytes() + b"mutation")
        rejected = run(arguments(archive_negative, "report.json"), True)
        if "disagrees with release binding" not in rejected.stderr:
            raise RuntimeError("mutated archive rejection was not precise")

        checksum_negative = temporary / "checksum-negative"
        checksum_negative.mkdir()
        copy_triplet(checksum_negative)
        (checksum_negative / f"{ARCHIVE_NAME}.sha256").write_text(
            f"{'0' * 64}  {ARCHIVE_NAME}\n", encoding="ascii"
        )
        rejected = run(arguments(checksum_negative, "report.json"), True)
        if "detached checksum" not in rejected.stderr:
            raise RuntimeError("mutated checksum rejection was not precise")

        receipt_negative = temporary / "receipt-negative"
        receipt_negative.mkdir()
        copy_triplet(receipt_negative)
        receipt_path = receipt_negative / f"{ARCHIVE_NAME}.verified.json"
        receipt = json.loads(receipt_path.read_text())
        receipt["archive_sha256"] = "0" * 64
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
        rejected = run(arguments(receipt_negative, "report.json"), True)
        if "informational receipt" not in rejected.stderr:
            raise RuntimeError("mutated receipt rejection was not precise")

    module = __import__("verify_published_release_assets")
    malformed = """# Zstandard Frames: 1\nDictID: 0\nWindow Size: 129 MiB (135266304 B)\nDecompressed Size: 1 KiB (1024 B)\nCheck: XXH64 abcd\n"""
    try:
        module.parse_zstd_listing(malformed)
    except module.VerificationError as exc:
        if "window exceeds" not in str(exc):
            raise RuntimeError("zstd window rejection was not precise") from exc
    else:
        raise RuntimeError("oversized zstd window was accepted")
    print("post-publication verification self-test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
