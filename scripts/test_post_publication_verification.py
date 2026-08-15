#!/usr/bin/env python3
"""Hermetic self-test for the public-only post-publication verifier."""

from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile


ROOT = Path(__file__).resolve().parent.parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / "scripts"))

RESULT_PATHS = {
    "result-theorem-one-one.json": (
        "evidence/theorem-one-one/result-theorem-one-one.json"
    ),
    "result-infinite-finite-transfer.json": (
        "evidence/infinite-finite-transfer/result-infinite-finite-transfer.json"
    ),
}
VERIFY_SCRIPT = b'''#!/bin/sh
set -eu

cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
'''


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def canonical_json(value: dict) -> bytes:
    return f"{json.dumps(value, indent=2)}\n".encode()


def checked(arguments: list[str], cwd: Path | None = None) -> str:
    result = subprocess.run(
        arguments,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"command failed ({result.returncode}): {' '.join(arguments)}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result.stdout


def write(path: Path, contents: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(contents)


def commit(repository: Path, message: str) -> str:
    checked(["git", "add", "--all"], repository)
    checked(["git", "commit", "--quiet", "-m", message], repository)
    return checked(["git", "rev-parse", "HEAD"], repository).strip()


def add_tar_member(
    archive: tarfile.TarFile,
    name: str,
    contents: bytes | None,
    mode: int,
) -> None:
    member = tarfile.TarInfo(name)
    member.uid = 0
    member.gid = 0
    member.uname = ""
    member.gname = ""
    member.mtime = 0
    member.mode = mode
    if contents is None:
        member.type = tarfile.DIRTYPE
        member.size = 0
        archive.addfile(member)
    else:
        member.type = tarfile.REGTYPE
        member.size = len(contents)
        archive.addfile(member, io.BytesIO(contents))


def build_public_archive(directory: Path, source_commit: str) -> tuple[Path, dict[str, str]]:
    root_name = f"paper-c-hardened-public-{source_commit}"
    archive_name = f"{root_name}.tar.zst"
    result_bytes = {
        name: canonical_json({"schema": 1, "name": name, "paper_c_commit": source_commit})
        for name in RESULT_PATHS
    }
    archived_verifier = b"#!/usr/bin/env python3\n# synthetic independent verifier fixture\n"
    files = {
        "VERIFY.sh": VERIFY_SCRIPT,
        "REDACTION_MANIFEST.json": canonical_json(
            {"schema": 1, "paper_c_commit": source_commit}
        ),
        "SUCCESS": b"synthetic hardened public evidence fixture\n",
        "source-snapshot/scripts/verify_public_comparator_archive.py": archived_verifier,
        **{RESULT_PATHS[name]: contents for name, contents in result_bytes.items()},
    }
    checksum_lines = [
        f"{sha256_bytes(contents)}  {relative}"
        for relative, contents in sorted(files.items(), key=lambda item: item[0].encode())
    ]
    files["SHA256SUMS"] = ("\n".join(checksum_lines) + "\n").encode()

    tar_path = directory / "public.tar"
    directories = {""}
    for relative in files:
        parent = Path(relative).parent
        while str(parent) != ".":
            directories.add(parent.as_posix())
            parent = parent.parent
    with tarfile.open(tar_path, "x:", format=tarfile.USTAR_FORMAT) as archive:
        for relative in sorted(directories, key=lambda value: (value.count("/"), value.encode())):
            name = root_name if not relative else f"{root_name}/{relative}"
            add_tar_member(archive, name, None, 0o755)
        for relative, contents in sorted(files.items(), key=lambda item: item[0].encode()):
            mode = 0o755 if relative == "VERIFY.sh" else 0o644
            add_tar_member(archive, f"{root_name}/{relative}", contents, mode)

    archive_path = directory / archive_name
    checked([
        "zstd", "-q", "-19", "--check", "-T1", "-o", str(archive_path),
        "--", str(tar_path),
    ])
    tar_path.unlink()
    return archive_path, {
        name: sha256_bytes(contents) for name, contents in result_bytes.items()
    }


def build_fixture(directory: Path) -> tuple[Path, str, Path]:
    repository = directory / "repository"
    repository.mkdir()
    checked(["git", "init", "--quiet"], repository)
    checked(["git", "config", "user.name", "post-publication-self-test"], repository)
    checked([
        "git", "config", "user.email", "post-publication-self-test@example.invalid",
    ], repository)
    checked(["git", "config", "commit.gpgsign", "false"], repository)
    checked(["git", "config", "core.hooksPath", "/dev/null"], repository)
    write(repository / "SOURCE", b"synthetic immutable source snapshot\n")
    source_commit = commit(repository, "synthetic source Q")

    assets = directory / "assets"
    assets.mkdir()
    archive, result_hashes = build_public_archive(assets, source_commit)
    archive_sha = sha256_bytes(archive.read_bytes())
    archive_name = archive.name
    (assets / f"{archive_name}.sha256").write_text(
        f"{archive_sha}  {archive_name}\n", encoding="ascii"
    )

    archived_verifier = b"#!/usr/bin/env python3\n# synthetic independent verifier fixture\n"
    receipt = {
        "schema": 1,
        "status": "public_comparator_archive_verification_report",
        "paper_c_commit": source_commit,
        "archive_filename": archive_name,
        "archive_sha256": archive_sha,
        "verifier": "scripts/verify_public_comparator_archive.py",
        "verifier_sha256": sha256_bytes(archived_verifier),
        "result_sha256": result_hashes,
        "qualification": "Synthetic informational report; not a signature.",
    }
    write(assets / f"{archive_name}.verified.json", canonical_json(receipt))

    evidence = repository / "release_evidence" / "v0.48.1"
    for name in RESULT_PATHS:
        # The public result bytes are deterministic, so reproduce them without
        # trusting the archive being tested.
        write(
            evidence / name,
            canonical_json({"schema": 1, "name": name, "paper_c_commit": source_commit}),
        )
    binding = {
        "schema": 2,
        "release": "v0.48.1",
        "protocol": "source-parent-packaging-v1",
        "paper_c_commit": source_commit,
        "hardened_archive_sha256": archive_sha,
        "evidence": result_hashes,
    }
    write(evidence / "release-binding.json", canonical_json(binding))
    packaging_commit = commit(repository, "synthetic packaging R")
    return repository, packaging_commit, assets


def copy_triplet(source: Path, destination: Path) -> str:
    destination.mkdir()
    archive = next(source.glob("*.tar.zst"))
    for suffix in ("", ".sha256", ".verified.json"):
        shutil.copyfile(source / f"{archive.name}{suffix}", destination / f"{archive.name}{suffix}")
    return archive.name


def run_verifier(
    repository: Path,
    packaging_commit: str,
    directory: Path,
    archive_name: str,
    report: str,
    expect_failure: bool = False,
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        [
            sys.executable,
            "scripts/verify_published_release_assets.py",
            "--repository", str(repository),
            "--packaging-commit", packaging_commit,
            "--release-tag", "v0.48.1",
            "--archive", str(directory / archive_name),
            "--checksum", str(directory / f"{archive_name}.sha256"),
            "--receipt", str(directory / f"{archive_name}.verified.json"),
            "--report", str(directory / report),
        ],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if (result.returncode == 0) == expect_failure:
        raise RuntimeError(
            f"unexpected verifier status: {result.returncode}\n"
            f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
        )
    return result


def main() -> int:
    if shutil.which("zstd") is None:
        raise RuntimeError("zstd is required for the post-publication self-test")
    with tempfile.TemporaryDirectory(prefix="paper-c-post-publication-test.") as name:
        temporary = Path(name)
        repository, packaging_commit, assets = build_fixture(temporary)

        positive = temporary / "positive"
        archive_name = copy_triplet(assets, positive)
        run_verifier(repository, packaging_commit, positive, archive_name, "report.json")
        report = json.loads((positive / "report.json").read_text())
        if report.get("status") != "published_release_assets_verified":
            raise RuntimeError("positive post-publication report status is wrong")

        archive_negative = temporary / "archive-negative"
        copy_triplet(assets, archive_negative)
        archive_path = archive_negative / archive_name
        archive_path.write_bytes(archive_path.read_bytes() + b"mutation")
        rejected = run_verifier(
            repository, packaging_commit, archive_negative, archive_name,
            "report.json", True,
        )
        if "disagrees with release binding" not in rejected.stderr:
            raise RuntimeError("mutated archive rejection was not precise")

        checksum_negative = temporary / "checksum-negative"
        copy_triplet(assets, checksum_negative)
        (checksum_negative / f"{archive_name}.sha256").write_text(
            f"{'0' * 64}  {archive_name}\n", encoding="ascii"
        )
        rejected = run_verifier(
            repository, packaging_commit, checksum_negative, archive_name,
            "report.json", True,
        )
        if "detached checksum" not in rejected.stderr:
            raise RuntimeError("mutated checksum rejection was not precise")

        receipt_negative = temporary / "receipt-negative"
        copy_triplet(assets, receipt_negative)
        receipt_path = receipt_negative / f"{archive_name}.verified.json"
        receipt = json.loads(receipt_path.read_text())
        receipt["archive_sha256"] = "0" * 64
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
        rejected = run_verifier(
            repository, packaging_commit, receipt_negative, archive_name,
            "report.json", True,
        )
        if "informational receipt" not in rejected.stderr:
            raise RuntimeError("mutated receipt rejection was not precise")

    module = __import__("verify_published_release_assets")
    oversized_window = """# Zstandard Frames: 1
DictID: 0
Window Size: 129 MiB (135266304 B)
Decompressed Size: 1 KiB (1024 B)
Check: XXH64 abcd
"""
    try:
        module.parse_zstd_listing(oversized_window)
    except module.VerificationError as exc:
        if "window exceeds" not in str(exc):
            raise RuntimeError("zstd window rejection was not precise") from exc
    else:
        raise RuntimeError("oversized zstd window was accepted")
    print("post-publication verification hermetic self-test passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
