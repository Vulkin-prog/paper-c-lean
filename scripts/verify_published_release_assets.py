#!/usr/bin/env python3
"""Fail-closed verification of the public Comparator assets as downloaded.

This is deliberately a public-only, post-publication check.  It proves that
the downloaded archive bytes agree with the packaging commit R, validates the
detached checksum and informational receipt, and runs the archive's own
checksum verifier after a safe extraction.  The stronger pre-publication
verifier additionally requires the private raw evidence and remains mandatory.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
import tarfile
import tempfile


RELEASE = "v0.48.1"
HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")
MAX_ARCHIVE_BYTES = 2 << 30
MAX_DECOMPRESSED_BYTES = 4 << 30
MAX_MEMBER_BYTES = 1 << 30
MAX_MEMBERS = 256
MAX_WINDOW_BYTES = 128 << 20
EXPECTED_RESULTS = {
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


class VerificationError(RuntimeError):
    """One post-publication invariant failed."""


def regular(path: Path, label: str) -> os.stat_result:
    try:
        info = path.lstat()
    except FileNotFoundError as exc:
        raise VerificationError(f"{label} is missing: {path}") from exc
    if not stat.S_ISREG(info.st_mode) or path.is_symlink():
        raise VerificationError(f"{label} must be a regular non-symlink: {path}")
    return info


def stable_digest(path: Path, label: str) -> tuple[int, str]:
    before = regular(path, label)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    descriptor = os.open(path, flags)
    digest = hashlib.sha256()
    observed = 0
    try:
        opened = os.fstat(descriptor)
        if not stat.S_ISREG(opened.st_mode):
            raise VerificationError(f"{label} changed type while opening")
        while chunk := os.read(descriptor, 1024 * 1024):
            observed += len(chunk)
            digest.update(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    final = path.lstat()
    states = {
        (entry.st_dev, entry.st_ino, entry.st_size, entry.st_mtime_ns)
        for entry in (before, opened, after, final)
    }
    if len(states) != 1 or observed != before.st_size:
        raise VerificationError(f"{label} changed while being hashed")
    return observed, digest.hexdigest()


def parse_json_file(path: Path, label: str, limit: int = 2 << 20) -> dict:
    size, _ = stable_digest(path, label)
    if size > limit:
        raise VerificationError(f"{label} is unexpectedly large")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError, OSError) as exc:
        raise VerificationError(f"invalid {label}: {exc}") from exc
    if not isinstance(value, dict):
        raise VerificationError(f"{label} is not a JSON object")
    return value


def safe_relative(value: str) -> str:
    if not value or value.startswith("/") or "\\" in value or "\x00" in value:
        raise VerificationError(f"unsafe archive path: {value!r}")
    candidate = value[:-1] if value.endswith("/") else value
    parts = candidate.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        raise VerificationError(f"non-canonical archive path: {value!r}")
    if str(PurePosixPath(*parts)) != candidate:
        raise VerificationError(f"non-canonical archive path: {value!r}")
    return candidate


def git(repository: Path, arguments: list[str], binary: bool = False):
    result = subprocess.run(
        ["git", "-C", str(repository), *arguments],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=not binary,
    )
    if result.returncode != 0:
        error = result.stderr.decode(errors="replace") if binary else result.stderr
        raise VerificationError(f"git {' '.join(arguments)} failed: {error.strip()}")
    return result.stdout


def verify_packaging(repository: Path, packaging_commit: str) -> tuple[str, dict]:
    if HEX40.fullmatch(packaging_commit) is None:
        raise VerificationError("packaging commit R must be 40 lowercase hexadecimal characters")
    resolved = git(repository, ["rev-parse", "--verify", f"{packaging_commit}^{{commit}}"])
    if resolved.strip() != packaging_commit:
        raise VerificationError("packaging commit R did not resolve to the exact requested commit")
    parents = git(repository, ["show", "-s", "--format=%P", packaging_commit]).split()
    if len(parents) != 1:
        raise VerificationError("packaging commit R must have exactly one parent Q")
    source_commit = parents[0]
    evidence_root = "release_evidence/v0.48.1"
    expected_paths = {
        f"{evidence_root}/release-binding.json",
        *(f"{evidence_root}/{name}" for name in EXPECTED_RESULTS),
    }
    source_paths = {
        value for value in git(
            repository,
            ["ls-tree", "-r", "--name-only", source_commit, "--", evidence_root],
        ).splitlines() if value
    }
    if source_paths:
        raise VerificationError(
            "source commit Q must contain no current v0.48.1 release evidence; "
            f"observed: {sorted(source_paths)}"
        )
    changed = {
        value for value in git(
            repository,
            ["diff", "--name-only", source_commit, packaging_commit, "--"],
        ).splitlines() if value
    }
    added = {
        value for value in git(
            repository,
            ["diff", "--diff-filter=A", "--name-only", source_commit, packaging_commit, "--"],
        ).splitlines() if value
    }
    if changed != expected_paths or added != expected_paths:
        raise VerificationError(
            "packaging commit R must add exactly the three v0.48.1 evidence files; "
            f"changed={sorted(changed)}, added={sorted(added)}"
        )
    binding_bytes = git(
        repository,
        ["show", f"{packaging_commit}:{evidence_root}/release-binding.json"],
        binary=True,
    )
    try:
        binding = json.loads(binding_bytes)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"invalid release binding at R: {exc}") from exc
    if (
        not isinstance(binding, dict)
        or binding.get("schema") != 2
        or binding.get("release") != RELEASE
        or binding.get("protocol") != "source-parent-packaging-v1"
        or binding.get("paper_c_commit") != source_commit
        or HEX64.fullmatch(str(binding.get("hardened_archive_sha256", ""))) is None
    ):
        raise VerificationError("release binding at R has an unexpected protocol or identity")
    return source_commit, binding


def verify_sidecar(sidecar: Path, archive_name: str, digest: str) -> None:
    size, _ = stable_digest(sidecar, "published detached checksum")
    if size > 4096:
        raise VerificationError("published detached checksum is unexpectedly large")
    try:
        contents = sidecar.read_text(encoding="ascii")
    except (UnicodeDecodeError, OSError) as exc:
        raise VerificationError("published detached checksum is not ASCII") from exc
    expected = f"{digest}  {archive_name}\n"
    if contents != expected:
        raise VerificationError("published detached checksum has non-canonical or wrong contents")


def parse_zstd_listing(text: str) -> tuple[int, int, int]:
    frames = re.search(r"(?m)^# Zstandard Frames:\s*(\d+)\s*$", text)
    window = re.search(r"(?m)^Window Size:.*\((\d+) B\)\s*$", text)
    decompressed = re.search(r"(?m)^Decompressed Size:.*\((\d+) B\)\s*$", text)
    if frames is None or window is None or decompressed is None:
        raise VerificationError("could not parse zstd frame inventory")
    values = (int(frames.group(1)), int(window.group(1)), int(decompressed.group(1)))
    if values[0] != 1:
        raise VerificationError("published archive must contain exactly one zstd frame")
    if values[1] > MAX_WINDOW_BYTES:
        raise VerificationError("published archive zstd window exceeds 128 MiB")
    if values[2] > MAX_DECOMPRESSED_BYTES:
        raise VerificationError("published archive declared size exceeds limit")
    if not re.search(r"(?m)^DictID:\s*0\s*$", text) or not re.search(
        r"(?m)^Check:\s*(?!None\b)\S+", text
    ):
        raise VerificationError("published archive needs no dictionary and must carry a frame check")
    return values


def inspect_zstd(archive: Path) -> int:
    probe = subprocess.run(
        ["zstd", "-lv", "--", str(archive)],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    if probe.returncode != 0:
        raise VerificationError(f"zstd frame inspection failed: {probe.stdout.strip()}")
    return parse_zstd_listing(probe.stdout)[2]


def decompress(archive: Path, output: Path, expected_size: int) -> None:
    process = subprocess.Popen(
        ["zstd", "-q", "-d", "-M128MiB", "-c", "--", str(archive)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert process.stdout is not None
    total = 0
    try:
        with output.open("xb") as destination:
            while chunk := process.stdout.read(1024 * 1024):
                total += len(chunk)
                if total > MAX_DECOMPRESSED_BYTES:
                    process.kill()
                    raise VerificationError("published archive exceeds decompressed-size limit")
                destination.write(chunk)
        stderr = process.stderr.read() if process.stderr else b""
        status = process.wait()
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    if status != 0:
        raise VerificationError(
            f"zstd could not decompress published archive: {stderr.decode(errors='replace').strip()}"
        )
    if total != expected_size:
        raise VerificationError("zstd decompressed size differs from inspected frame inventory")


def extract_public_tree(tar_path: Path, destination: Path, expected_root: str) -> Path:
    members_seen = 0
    files: set[str] = set()
    directories: set[str] = set()
    with tarfile.open(tar_path, "r:") as archive:
        for member in archive:
            members_seen += 1
            if members_seen > MAX_MEMBERS:
                raise VerificationError("published archive has too many members")
            canonical = safe_relative(member.name)
            parts = canonical.split("/")
            if parts[0] != expected_root:
                raise VerificationError("published archive root does not bind source commit Q")
            relative = "/".join(parts[1:])
            if member.pax_headers or getattr(member, "sparse", None):
                raise VerificationError(f"PAX or sparse metadata is forbidden: {canonical}")
            if member.isdir():
                if not relative or relative in directories:
                    if not relative and canonical == expected_root and not directories:
                        directories.add(relative)
                        continue
                    raise VerificationError(f"duplicate archive directory: {canonical}")
                directories.add(relative)
                continue
            if not member.isfile() or not relative:
                raise VerificationError(f"forbidden archive member type: {canonical}")
            if relative in files or member.size > MAX_MEMBER_BYTES:
                raise VerificationError(f"duplicate or oversized archive member: {relative}")
            files.add(relative)
            target = destination.joinpath(*parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            source = archive.extractfile(member)
            if source is None:
                raise VerificationError(f"could not read archive member: {relative}")
            with target.open("xb") as output:
                remaining = member.size
                while remaining:
                    chunk = source.read(min(1024 * 1024, remaining))
                    if not chunk:
                        raise VerificationError(f"truncated archive member: {relative}")
                    output.write(chunk)
                    remaining -= len(chunk)
                if source.read(1):
                    raise VerificationError(f"oversized archive member payload: {relative}")
            source.close()
            target.chmod(0o755 if relative == "VERIFY.sh" else 0o644)
    required = {
        "VERIFY.sh", "SHA256SUMS", "REDACTION_MANIFEST.json", "SUCCESS",
        *EXPECTED_RESULTS.values(),
    }
    if not required.issubset(files):
        raise VerificationError(f"published archive omits required files: {sorted(required - files)}")
    root = destination / expected_root
    if root.is_symlink() or not root.is_dir():
        raise VerificationError("extracted public root is not a real directory")
    return root


def verify_receipt(
    receipt: dict,
    receipt_name: str,
    archive_name: str,
    archive_sha: str,
    source_commit: str,
    binding: dict,
    public_root: Path,
) -> None:
    expected_receipt_name = f"{archive_name}.verified.json"
    if receipt_name != expected_receipt_name:
        raise VerificationError(f"verification receipt must be named {expected_receipt_name}")
    if (
        receipt.get("schema") != 1
        or receipt.get("status") != "public_comparator_archive_verification_report"
        or receipt.get("paper_c_commit") != source_commit
        or receipt.get("archive_filename") != archive_name
        or receipt.get("archive_sha256") != archive_sha
        or receipt.get("verifier") != "scripts/verify_public_comparator_archive.py"
        or HEX64.fullmatch(str(receipt.get("verifier_sha256", ""))) is None
        or not isinstance(receipt.get("qualification"), str)
        or "not a signature" not in receipt["qualification"]
    ):
        raise VerificationError("published informational receipt is inconsistent")
    receipt_results = receipt.get("result_sha256")
    binding_results = binding.get("evidence")
    if (
        not isinstance(receipt_results, dict)
        or set(receipt_results) != set(EXPECTED_RESULTS)
        or not isinstance(binding_results, dict)
        or set(binding_results) != set(EXPECTED_RESULTS)
    ):
        raise VerificationError("receipt or binding has an unexpected result inventory")
    for name, relative in EXPECTED_RESULTS.items():
        _, observed = stable_digest(public_root / relative, f"published {name}")
        if observed != receipt_results[name] or observed != binding_results[name]:
            raise VerificationError(f"published result bytes disagree with receipt/binding: {name}")
    verifier = public_root / "source-snapshot/scripts/verify_public_comparator_archive.py"
    _, verifier_sha = stable_digest(verifier, "archived independent verifier")
    if verifier_sha != receipt["verifier_sha256"]:
        raise VerificationError("receipt does not bind the independent verifier in the archive")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=str(Path(__file__).resolve().parent.parent))
    parser.add_argument("--packaging-commit", required=True)
    parser.add_argument("--release-tag", required=True)
    parser.add_argument("--archive", required=True)
    parser.add_argument("--checksum", required=True)
    parser.add_argument("--receipt", required=True)
    parser.add_argument("--report", required=True)
    args = parser.parse_args()
    report_path = Path(args.report).resolve()
    try:
        if args.release_tag != RELEASE:
            raise VerificationError(f"release tag must be exactly {RELEASE}")
        repository = Path(args.repository).resolve()
        source_commit, binding = verify_packaging(repository, args.packaging_commit)
        archive = Path(args.archive).resolve()
        checksum = Path(args.checksum).resolve()
        receipt_path = Path(args.receipt).resolve()
        report_directory = report_path.parent
        report_directory.mkdir(parents=True, exist_ok=True)
        if report_path.exists() or report_path.is_symlink():
            raise VerificationError("post-publication report path must be new")
        expected_archive_name = f"paper-c-hardened-public-{source_commit}.tar.zst"
        if archive.name != expected_archive_name:
            raise VerificationError(f"published archive must be named {expected_archive_name}")
        archive_identity = stable_digest(archive, "published hardened public archive")
        size, archive_sha = archive_identity
        if size > MAX_ARCHIVE_BYTES:
            raise VerificationError("published archive exceeds compressed-size limit")
        if archive_sha != binding["hardened_archive_sha256"]:
            raise VerificationError("published archive SHA-256 disagrees with release binding at R")
        if checksum.name != f"{expected_archive_name}.sha256":
            raise VerificationError("published detached checksum filename is wrong")
        checksum_identity = stable_digest(checksum, "published detached checksum")
        verify_sidecar(checksum, expected_archive_name, archive_sha)
        receipt_identity = stable_digest(receipt_path, "published informational receipt")
        receipt = parse_json_file(receipt_path, "published informational receipt")
        with tempfile.TemporaryDirectory(prefix="paper-c-post-publication.") as temporary_name:
            temporary = Path(temporary_name)
            tar_path = temporary / "public.tar"
            expected_decompressed_size = inspect_zstd(archive)
            decompress(archive, tar_path, expected_decompressed_size)
            extract = temporary / "extract"
            extract.mkdir()
            public_root = extract_public_tree(
                tar_path, extract, expected_archive_name.removesuffix(".tar.zst")
            )
            archived_verify = public_root / "VERIFY.sh"
            if stable_digest(archived_verify, "archived public verifier")[0] != len(VERIFY_SCRIPT):
                raise VerificationError("archived public verifier size is unexpected")
            if archived_verify.read_bytes() != VERIFY_SCRIPT:
                raise VerificationError("archived public verifier is not the expected fail-closed shim")
            verifier_run = subprocess.run(
                ["/bin/sh", str(archived_verify)],
                cwd=public_root,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            if verifier_run.returncode != 0:
                raise VerificationError(
                    "archived public verifier failed: "
                    f"{verifier_run.stdout}{verifier_run.stderr}".strip()
                )
            verify_receipt(
                receipt, receipt_path.name, expected_archive_name, archive_sha,
                source_commit, binding, public_root,
            )
        if stable_digest(archive, "published archive after extraction") != archive_identity:
            raise VerificationError("published archive changed during verification")
        if stable_digest(checksum, "published checksum after use") != checksum_identity:
            raise VerificationError("published detached checksum changed during verification")
        if stable_digest(receipt_path, "published receipt after use") != receipt_identity:
            raise VerificationError("published informational receipt changed during verification")
        report = {
            "schema": 1,
            "status": "published_release_assets_verified",
            "release": RELEASE,
            "packaging_commit": args.packaging_commit,
            "source_commit": source_commit,
            "archive_filename": expected_archive_name,
            "archive_bytes": size,
            "archive_sha256": archive_sha,
            "checks": {
                "release_binding_at_packaging_commit": "passed",
                "source_q_has_no_current_release_evidence": "passed",
                "packaging_r_adds_exactly_three_evidence_files": "passed",
                "downloaded_detached_checksum": "passed",
                "downloaded_informational_receipt": "passed",
                "safe_archive_extraction": "passed",
                "archived_public_verifier": "passed",
                "published_result_hashes": "passed",
            },
            "qualification": (
                "Post-publication identity and public-integrity verification. The mandatory "
                "pre-publication private-raw verification is a separate gate."
            ),
        }
        with report_path.open("xb") as output:
            output.write(f"{json.dumps(report, indent=2)}\n".encode())
    except (VerificationError, OSError, subprocess.SubprocessError, tarfile.TarError) as exc:
        print(f"PUBLISHED_RELEASE_ASSETS: FAIL: {exc}", file=sys.stderr)
        return 1
    print("PUBLISHED_RELEASE_ASSETS: PASS")
    print(f"release={RELEASE}")
    print(f"packaging_commit={args.packaging_commit}")
    print(f"source_commit={source_commit}")
    print(f"archive_sha256={archive_sha}")
    print(f"report={report_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
