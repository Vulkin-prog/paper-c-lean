#!/usr/bin/env python3
"""Derive the privacy-minimized public Comparator archive.

The transformation is deliberately omission-only.  A fixed policy retains the
two result records, the complete source snapshot, the aggregate summary, the
SUCCESS marker, and the raw checksum inventory.  Every other expected raw
member is host-specific and is represented only by its size and SHA-256 in the
redaction manifest.  Any missing or unexpected source path is fatal.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
from dataclasses import dataclass
from typing import BinaryIO


HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")
MAX_RAW_MEMBER_BYTES = 1 << 30
MAX_RAW_TOTAL_BYTES = 4 << 30
MAX_RAW_HEADERS = 256
FIXED_MTIME = 0

RESULT_SPECS = {
    "theorem-one-one": {
        "result": "evidence/theorem-one-one/result-theorem-one-one.json",
        "config": "comparator/theorem_one_one.json",
        "challenge": "Challenge.lean",
        "solution": "Solution.lean",
        "transcript": "evidence/theorem-one-one/comparator-theorem-one-one.txt",
    },
    "infinite-finite-transfer": {
        "result": (
            "evidence/infinite-finite-transfer/"
            "result-infinite-finite-transfer.json"
        ),
        "config": "comparator/theorem_one_one_transfer.json",
        "challenge": "ChallengeTransfer.lean",
        "solution": "SolutionTransfer.lean",
        "transcript": (
            "evidence/infinite-finite-transfer/"
            "comparator-infinite-finite-transfer.txt"
        ),
    },
}

SNAPSHOT_PATHS = {
    "source-snapshot/Challenge.lean",
    "source-snapshot/Solution.lean",
    "source-snapshot/ChallengeTransfer.lean",
    "source-snapshot/SolutionTransfer.lean",
    "source-snapshot/ChallengeTheoremOneTwo.lean",
    "source-snapshot/SolutionTheoremOneTwo.lean",
    "source-snapshot/ChallengeTheoremOneFour.lean",
    "source-snapshot/SolutionTheoremOneFour.lean",
    "source-snapshot/ChallengeTheoremSixteenTwo.lean",
    "source-snapshot/SolutionTheoremSixteenTwo.lean",
    "source-snapshot/comparator/theorem_one_one.json",
    "source-snapshot/comparator/theorem_one_one_transfer.json",
    "source-snapshot/comparator/theorem_one_two.json",
    "source-snapshot/comparator/theorem_one_four_and_corollary_eleven_three.json",
    "source-snapshot/comparator/theorem_sixteen_two_and_corollary_sixteen_four.json",
    "source-snapshot/audit_config.json",
    "source-snapshot/lean-toolchain",
    "source-snapshot/lake-manifest.json",
    "source-snapshot/lakefile.toml",
    "source-snapshot/scripts/assemble_comparator_evidence.mjs",
    "source-snapshot/scripts/derive_public_comparator_archive.py",
    "source-snapshot/scripts/run_hardened_comparator.sh",
    "source-snapshot/scripts/test_public_comparator_archive.py",
    "source-snapshot/scripts/verify_public_comparator_archive.py",
}

OMITTED_REASONS = {
    "setup.log": (
        "Setup command transcript exposes absolute workspace, home, toolchain, "
        "and randomized temporary paths."
    ),
}
for _label in RESULT_SPECS:
    _prefix = f"evidence/{_label}"
    OMITTED_REASONS[f"{_prefix}/comparator-environment.txt"] = (
        "Environment capture exposes local hostname, account, UID/GID, groups, "
        "home/toolchain paths, and host binary paths."
    )
    OMITTED_REASONS[f"{_prefix}/comparator-{_label}.log"] = (
        "Execution log embeds systemd command lines with local home, toolchain, "
        "temporary paths, PTY/session identifiers, and transient-unit suffix."
    )
    OMITTED_REASONS[f"{_prefix}/comparator-{_label}.txt"] = (
        "Full transcript includes environment capture, local account/groups, "
        "host paths, PTY/session identifiers, and transient-unit suffix."
    )
    OMITTED_REASONS[f"{_prefix}/hardening-probe.log"] = (
        "Hardening probe embeds randomized temporary paths, local home/toolchain "
        "paths, PTY/session identifiers, and transient-unit suffix."
    )
    OMITTED_REASONS[f"{_prefix}/systemd-probe-pty.raw"] = (
        "Raw PTY probe header embeds local home/toolchain and temporary paths, "
        "PTY device, and transient-unit suffix."
    )
    OMITTED_REASONS[f"{_prefix}/systemd-pty.raw"] = (
        "Raw execution PTY header embeds local home/toolchain and temporary paths, "
        "PTY device, and transient-unit suffix."
    )

RETAINED_PATHS = {
    "SHA256SUMS",
    "SUCCESS",
    "summary.json",
    *SNAPSHOT_PATHS,
    *(spec["result"] for spec in RESULT_SPECS.values()),
}
EXPECTED_RAW_PATHS = RETAINED_PATHS | set(OMITTED_REASONS)
PUBLIC_RENAMES = {"SHA256SUMS": "provenance/RAW_SHA256SUMS"}
ADDED_PUBLIC_PATHS = {
    "PRIVACY.md",
    "REDACTION_MANIFEST.json",
    "SHA256SUMS",
    "VERIFY.sh",
}

EXPECTED_RESULT_KEYS = {
    "status",
    "certifying",
    "sandboxed",
    "non_root",
    "kernels",
    "enable_nanoda",
    "exit_code",
    "config",
    "configuration_sha256",
    "comparator_fileset_digest_sha256",
    "paper_c_commit",
    "theorem_names",
    "permitted_axioms",
    "challenge",
    "solution",
    "tool_commits",
    "manuscript_sha256",
    "transcript",
    "transcript_sha256",
}
EXPECTED_SUMMARY_KEYS = {
    "status",
    "paper_c_commit",
    "certifying",
    "sandboxed",
    "kernels",
    "enable_nanoda",
    "pty_transport",
    "comparator_fileset_digest_sha256",
    "tool_commits",
    "manuscript_sha256",
    "results",
    "qualification",
}
EXPECTED_TOOL_KEYS = {"lean", "mathlib", "comparator", "lean4export", "landrun"}
EXPECTED_MANUSCRIPT_KEYS = {"target_pdf", "source_pdf_fr"}
EXPECTED_ENDPOINT_KEYS = {"module", "file", "sha256"}
EXPECTED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
EXPECTED_COMPARATOR_FILESET = {
    "Challenge.lean",
    "Solution.lean",
    "ChallengeTransfer.lean",
    "SolutionTransfer.lean",
    "ChallengeTheoremOneTwo.lean",
    "SolutionTheoremOneTwo.lean",
    "ChallengeTheoremOneFour.lean",
    "SolutionTheoremOneFour.lean",
    "ChallengeTheoremSixteenTwo.lean",
    "SolutionTheoremSixteenTwo.lean",
    "comparator/theorem_one_one.json",
    "comparator/theorem_one_one_transfer.json",
    "comparator/theorem_one_two.json",
    "comparator/theorem_one_four_and_corollary_eleven_three.json",
    "comparator/theorem_sixteen_two_and_corollary_sixteen_four.json",
}
POLICY_TOOL_PATHS = (
    "scripts/derive_public_comparator_archive.py",
    "scripts/verify_public_comparator_archive.py",
    "scripts/test_public_comparator_archive.py",
)

PRIVATE_PATH_PATTERNS = (
    re.compile(rb"(?:^|[\s\"'=])/(?:home|Users)/[^\s\"'<>]+"),
    re.compile(rb"(?:^|[\s\"'=])/(?:tmp|var/tmp|run/user)/[^\s\"'<>]+"),
    re.compile(rb"(?:^|[\s\"'=])/(?:private/var|Volumes)/[^\s\"'<>]+"),
    re.compile(rb"(?:^|[\s\"'=])[A-Za-z]:\\[^\s\"'<>]+"),
    re.compile(rb"file://(?:localhost)?/", re.IGNORECASE),
    re.compile(rb"(?m)^(?:HOME|PWD|USER|LOGNAME|HOSTNAME)=[^\r\n]+$"),
    re.compile(rb"(?m)^uname=Linux\s+[^\r\n]+$"),
    re.compile(rb"(?m)^uid=\d+\([^)]+\)\s+gid=\d+\([^)]+\)"),
)


class PolicyError(RuntimeError):
    """A fail-closed policy violation."""


@dataclass(frozen=True)
class FileRecord:
    size: int
    sha256: str
    retained_copy: Path | None = None


def bytewise(values: set[str] | list[str]) -> list[str]:
    return sorted(values, key=lambda value: value.encode("utf-8"))


def safe_relative(name: str) -> str:
    if not name or "\x00" in name or "\\" in name or name.startswith("/"):
        raise PolicyError(f"unsafe archive path: {name!r}")
    try:
        encoded = name.encode("ascii")
    except UnicodeEncodeError as exc:
        raise PolicyError(f"non-ASCII archive path: {name!r}") from exc
    if any(byte < 0x20 or byte == 0x7F for byte in encoded):
        raise PolicyError(f"archive path contains a control byte: {name!r}")
    candidate = name[:-1] if name.endswith("/") else name
    parts = candidate.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        raise PolicyError(f"non-canonical archive path: {name!r}")
    normalized = str(PurePosixPath(*parts))
    if normalized != candidate:
        raise PolicyError(f"non-canonical archive path: {name!r}")
    return normalized


def assert_regular_file(path: Path, label: str) -> os.stat_result:
    try:
        info = path.lstat()
    except FileNotFoundError as exc:
        raise PolicyError(f"{label} does not exist: {path}") from exc
    if not stat.S_ISREG(info.st_mode) or path.is_symlink():
        raise PolicyError(f"{label} must be a regular, non-symbolic file: {path}")
    return info


def stable_file_digest(path: Path, label: str) -> tuple[int, str]:
    before = assert_regular_file(path, label)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise PolicyError(f"could not safely open {label}: {path}: {exc}") from exc
    digest = hashlib.sha256()
    size = 0
    try:
        opened = os.fstat(descriptor)
        if not stat.S_ISREG(opened.st_mode):
            raise PolicyError(f"{label} changed type while opening: {path}")
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
            size += len(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    final = path.lstat()
    fingerprints = (
        (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns),
        (opened.st_dev, opened.st_ino, opened.st_size, opened.st_mtime_ns),
        (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns),
        (final.st_dev, final.st_ino, final.st_size, final.st_mtime_ns),
    )
    if len(set(fingerprints)) != 1 or size != opened.st_size:
        raise PolicyError(f"{label} changed while it was being read: {path}")
    return size, digest.hexdigest()


def verify_detached_checksum(archive: Path, digest: str, label: str) -> None:
    sidecar = Path(f"{archive}.sha256")
    size, _ = stable_file_digest(sidecar, f"{label} checksum sidecar")
    if size > 4096:
        raise PolicyError(f"{label} checksum sidecar is unexpectedly large")
    try:
        payload = sidecar.read_text(encoding="ascii")
    except (UnicodeDecodeError, OSError) as exc:
        raise PolicyError(f"{label} checksum sidecar is not ASCII") from exc
    expected = f"{digest}  {archive.name}\n"
    if payload != expected:
        raise PolicyError(f"{label} checksum sidecar mismatch")


def expected_raw_directories() -> set[str]:
    directories = {""}
    for relative in EXPECTED_RAW_PATHS:
        parent = PurePosixPath(relative).parent
        while str(parent) != ".":
            directories.add(str(parent))
            parent = parent.parent
    return directories


def collect_raw_archive(archive: Path, retained_dir: Path) -> tuple[dict[str, FileRecord], str]:
    assert_regular_file(archive, "raw hardened archive")
    retained_dir.mkdir(mode=0o700, parents=True)
    process = subprocess.Popen(
        ["zstd", "-q", "-d", "-M128MiB", "-c", "--", str(archive)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert process.stdout is not None
    assert process.stderr is not None
    files: dict[str, FileRecord] = {}
    directories: set[str] = set()
    roots: set[str] = set()
    total_size = 0
    header_count = 0
    failure: BaseException | None = None
    try:
        with tarfile.open(fileobj=process.stdout, mode="r|") as source_tar:
            for member in source_tar:
                header_count += 1
                if header_count > MAX_RAW_HEADERS:
                    raise PolicyError("raw archive contains too many headers")
                canonical = safe_relative(member.name)
                parts = canonical.split("/")
                roots.add(parts[0])
                relative = "/".join(parts[1:])
                if member.isdir():
                    if relative in directories:
                        raise PolicyError(f"duplicate raw archive directory: {relative or '/'}")
                    directories.add(relative)
                    continue
                if member.pax_headers or getattr(member, "sparse", None):
                    raise PolicyError(
                        f"raw archive contains forbidden PAX or sparse metadata: {canonical}"
                    )
                if not member.isfile():
                    raise PolicyError(
                        f"raw archive contains forbidden non-regular member: {canonical}"
                    )
                if not relative:
                    raise PolicyError("raw archive root is a regular file")
                if relative in files:
                    raise PolicyError(f"duplicate raw archive file: {relative}")
                if member.size < 0 or member.size > MAX_RAW_MEMBER_BYTES:
                    raise PolicyError(f"raw archive member has unsafe size: {relative}")
                total_size += member.size
                if total_size > MAX_RAW_TOTAL_BYTES:
                    raise PolicyError("raw archive exceeds the fail-closed total size limit")
                payload = source_tar.extractfile(member)
                if payload is None:
                    raise PolicyError(f"could not read raw archive member: {relative}")
                digest = hashlib.sha256()
                observed = 0
                retained_path: Path | None = None
                output: BinaryIO | None = None
                if relative in RETAINED_PATHS:
                    retained_path = retained_dir.joinpath(*relative.split("/"))
                    retained_path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
                    output = retained_path.open("xb")
                try:
                    while True:
                        chunk = payload.read(1024 * 1024)
                        if not chunk:
                            break
                        digest.update(chunk)
                        observed += len(chunk)
                        if output is not None:
                            output.write(chunk)
                finally:
                    payload.close()
                    if output is not None:
                        output.close()
                if observed != member.size:
                    raise PolicyError(f"truncated raw archive member: {relative}")
                files[relative] = FileRecord(observed, digest.hexdigest(), retained_path)
    except BaseException as exc:  # preserve the policy error after reaping zstd
        failure = exc
        process.kill()
    finally:
        process.stdout.close()
    stderr = process.stderr.read().decode("utf-8", "replace")
    process.stderr.close()
    status_code = process.wait()
    if failure is not None:
        raise failure
    if status_code != 0:
        raise PolicyError(f"zstd could not decode raw archive: {stderr.strip()}")
    if len(roots) != 1:
        raise PolicyError(f"raw archive must have exactly one root directory, found {roots}")
    missing = EXPECTED_RAW_PATHS - set(files)
    unexpected = set(files) - EXPECTED_RAW_PATHS
    if missing or unexpected:
        raise PolicyError(
            f"raw source path set mismatch; missing={bytewise(missing)}, "
            f"unexpected={bytewise(unexpected)}"
        )
    expected_directories = expected_raw_directories()
    if directories != expected_directories:
        raise PolicyError(
            "raw source directory set mismatch; "
            f"missing={bytewise(expected_directories - directories)}, "
            f"unexpected={bytewise(directories - expected_directories)}"
        )
    return files, next(iter(roots))


def collect_raw_directory(directory: Path) -> dict[str, FileRecord]:
    try:
        root_info = directory.lstat()
    except FileNotFoundError as exc:
        raise PolicyError(f"raw evidence directory does not exist: {directory}") from exc
    if not stat.S_ISDIR(root_info.st_mode) or directory.is_symlink():
        raise PolicyError(f"raw evidence source must be a non-symbolic directory: {directory}")
    files: dict[str, FileRecord] = {}
    directories = {""}
    for current, child_dirs, child_files in os.walk(directory, followlinks=False):
        current_path = Path(current)
        relative_dir = current_path.relative_to(directory).as_posix()
        if relative_dir == ".":
            relative_dir = ""
        for name in list(child_dirs):
            child = current_path / name
            info = child.lstat()
            if not stat.S_ISDIR(info.st_mode) or child.is_symlink():
                raise PolicyError(f"raw evidence contains non-directory or symlink: {child}")
            relative = f"{relative_dir}/{name}".lstrip("/")
            safe_relative(relative)
            directories.add(relative)
        for name in child_files:
            child = current_path / name
            relative = f"{relative_dir}/{name}".lstrip("/")
            safe_relative(relative)
            size, digest = stable_file_digest(child, f"raw evidence member {relative}")
            files[relative] = FileRecord(size, digest)
    missing = EXPECTED_RAW_PATHS - set(files)
    unexpected = set(files) - EXPECTED_RAW_PATHS
    if missing or unexpected:
        raise PolicyError(
            f"raw directory path set mismatch; missing={bytewise(missing)}, "
            f"unexpected={bytewise(unexpected)}"
        )
    expected_directories = expected_raw_directories()
    if directories != expected_directories:
        raise PolicyError(
            "raw directory set mismatch; "
            f"missing={bytewise(expected_directories - directories)}, "
            f"unexpected={bytewise(directories - expected_directories)}"
        )
    return files


def compare_inventories(
    archive_records: dict[str, FileRecord], directory_records: dict[str, FileRecord]
) -> None:
    for relative in bytewise(EXPECTED_RAW_PATHS):
        archived = archive_records[relative]
        live = directory_records[relative]
        if (archived.size, archived.sha256) != (live.size, live.sha256):
            raise PolicyError(
                f"raw directory differs from its source archive at {relative}"
            )


def parse_checksum_inventory(payload: bytes) -> dict[str, str]:
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise PolicyError("raw SHA256SUMS is not UTF-8") from exc
    if not text.endswith("\n") or "\r" in text or "\x00" in text:
        raise PolicyError("raw SHA256SUMS has non-canonical line endings")
    checksums: dict[str, str] = {}
    for line in text.splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  \./(.+)", line)
        if match is None:
            raise PolicyError(f"malformed raw SHA256SUMS line: {line!r}")
        relative = safe_relative(match.group(2))
        if relative in checksums:
            raise PolicyError(f"duplicate raw SHA256SUMS path: {relative}")
        checksums[relative] = match.group(1)
    expected = EXPECTED_RAW_PATHS - {"SHA256SUMS", "SUCCESS"}
    if set(checksums) != expected:
        raise PolicyError(
            "raw SHA256SUMS coverage mismatch; "
            f"missing={bytewise(expected - set(checksums))}, "
            f"unexpected={bytewise(set(checksums) - expected)}"
        )
    return checksums


def read_retained(records: dict[str, FileRecord], relative: str) -> bytes:
    retained = records[relative].retained_copy
    if retained is None:
        raise PolicyError(f"internal error: no retained copy for {relative}")
    return retained.read_bytes()


def exact_keys(value: object, expected: set[str], label: str) -> dict:
    if not isinstance(value, dict) or set(value) != expected:
        observed = set(value) if isinstance(value, dict) else type(value).__name__
        raise PolicyError(f"{label} has unexpected schema keys: {observed}")
    return value


def parse_json(records: dict[str, FileRecord], relative: str) -> dict:
    payload = read_retained(records, relative)
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise PolicyError(f"invalid JSON in {relative}: {exc}") from exc
    if not isinstance(value, dict):
        raise PolicyError(f"{relative} must contain a JSON object")
    return value


def assert_hex(value: object, pattern: re.Pattern[str], label: str) -> str:
    if not isinstance(value, str) or pattern.fullmatch(value) is None:
        raise PolicyError(f"{label} is not a canonical lowercase hexadecimal digest")
    return value


def fileset_digest(records: dict[str, FileRecord], paths: list[str]) -> str:
    digest = hashlib.sha256()
    for relative in bytewise(paths):
        snapshot_relative = f"source-snapshot/{relative}"
        if snapshot_relative not in records:
            raise PolicyError(f"Comparator fileset is absent from snapshot: {relative}")
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        retained = records[snapshot_relative].retained_copy
        assert retained is not None
        with retained.open("rb") as source:
            while chunk := source.read(1024 * 1024):
                digest.update(chunk)
        digest.update(b"\0")
    return digest.hexdigest()


def validate_result(
    result: dict,
    label: str,
    spec: dict[str, str],
    records: dict[str, FileRecord],
    commit: str,
    comparator_digest: str,
    config: dict,
    expected_tools: dict[str, str],
) -> None:
    exact_keys(result, EXPECTED_RESULT_KEYS, f"result {label}")
    if (
        result["status"] != "sandboxed_lean_kernel_passed"
        or result["certifying"] is not True
        or result["sandboxed"] is not True
        or result["non_root"] is not True
        or result["kernels"] != ["lean"]
        or result["enable_nanoda"] is not False
        or result["exit_code"] != 0
    ):
        raise PolicyError(f"result {label} is not certifying hardened Lean evidence")
    if result["paper_c_commit"] != commit or result["config"] != spec["config"]:
        raise PolicyError(f"result {label} has the wrong commit or configuration")
    if result["permitted_axioms"] != EXPECTED_AXIOMS or result[
        "permitted_axioms"
    ] != config["permitted_axioms"]:
        raise PolicyError(f"result {label} has unexpected permitted axioms")
    theorem_names = result["theorem_names"]
    if (
        not isinstance(theorem_names, list)
        or len(theorem_names) != 1
        or not isinstance(theorem_names[0], str)
        or re.fullmatch(r"[A-Za-z0-9_'.]+", theorem_names[0]) is None
    ):
        raise PolicyError(f"result {label} has unsafe theorem names")
    if theorem_names != config["theorem_names"]:
        raise PolicyError(f"result {label} theorem names disagree with its configuration")
    tools = exact_keys(result["tool_commits"], EXPECTED_TOOL_KEYS, f"result {label} tools")
    for tool, tool_commit in tools.items():
        assert_hex(tool_commit, HEX40, f"result {label} tool commit {tool}")
    if tools != expected_tools:
        raise PolicyError(f"result {label} tool commits disagree with audit_config.json")
    manuscripts = exact_keys(
        result["manuscript_sha256"], EXPECTED_MANUSCRIPT_KEYS, f"result {label} manuscripts"
    )
    for name, digest in manuscripts.items():
        assert_hex(digest, HEX64, f"result {label} manuscript hash {name}")
    for endpoint_name in ("challenge", "solution"):
        endpoint = exact_keys(
            result[endpoint_name], EXPECTED_ENDPOINT_KEYS, f"result {label} {endpoint_name}"
        )
        expected_file = spec[endpoint_name]
        if endpoint["file"] != expected_file:
            raise PolicyError(f"result {label} has unexpected {endpoint_name} file")
        if not isinstance(endpoint["module"], str) or endpoint["module"] != Path(expected_file).stem:
            raise PolicyError(f"result {label} has unexpected {endpoint_name} module")
        if endpoint["module"] != config[f"{endpoint_name}_module"]:
            raise PolicyError(
                f"result {label} {endpoint_name} module disagrees with configuration"
            )
        snapshot = records[f"source-snapshot/{expected_file}"]
        if endpoint["sha256"] != snapshot.sha256:
            raise PolicyError(f"result {label} {endpoint_name} hash mismatch")
    config_record = records[f"source-snapshot/{spec['config']}"]
    if result["configuration_sha256"] != config_record.sha256:
        raise PolicyError(f"result {label} configuration hash mismatch")
    if result["comparator_fileset_digest_sha256"] != comparator_digest:
        raise PolicyError(f"result {label} Comparator fileset digest mismatch")
    expected_transcript_name = PurePosixPath(spec["transcript"]).name
    if result["transcript"] != expected_transcript_name:
        raise PolicyError(f"result {label} transcript path is not the expected basename")
    if result["transcript_sha256"] != records[spec["transcript"]].sha256:
        raise PolicyError(f"result {label} private transcript hash mismatch")


def assert_public_payload_safe(relative: str, payload: bytes) -> None:
    if b"\x00" in payload and not relative.endswith(".pdf"):
        # No retained member in this protocol is binary.  Rejecting NUL bytes
        # keeps the privacy scan auditable instead of silently skipping data.
        raise PolicyError(f"retained public member is unexpectedly binary: {relative}")
    for pattern in PRIVATE_PATH_PATTERNS:
        match = pattern.search(payload)
        if match is not None:
            excerpt = match.group(0)[:120].decode("utf-8", "backslashreplace")
            raise PolicyError(
                f"retained public evidence contains a concrete private path or "
                f"identity in {relative}: {excerpt!r}"
            )


def scan_public_safe(records: dict[str, FileRecord], relatives: list[str]) -> None:
    for relative in relatives:
        payload = read_retained(records, relative)
        assert_public_payload_safe(relative, payload)


def validate_raw_evidence(records: dict[str, FileRecord]) -> dict:
    raw_inventory = read_retained(records, "SHA256SUMS")
    checksums = parse_checksum_inventory(raw_inventory)
    for relative, expected_digest in checksums.items():
        if records[relative].sha256 != expected_digest:
            raise PolicyError(f"raw SHA256SUMS digest mismatch for {relative}")

    summary = parse_json(records, "summary.json")
    exact_keys(summary, EXPECTED_SUMMARY_KEYS, "summary.json")
    commit = assert_hex(summary["paper_c_commit"], HEX40, "Paper C commit")
    if (
        summary["status"] != "two_hardened_comparator_targets_passed"
        or summary["certifying"] is not True
        or summary["sandboxed"] is not True
        or summary["kernels"] != ["lean"]
        or summary["enable_nanoda"] is not False
        or summary["pty_transport"] != "util-linux-script around systemd-run --user --pty"
    ):
        raise PolicyError("summary.json is not hardened two-target Lean evidence")
    if summary["qualification"] != (
        "Lean-kernel Comparator evidence; not a dual-kernel result or a general "
        "host-security certification."
    ):
        raise PolicyError("summary.json has an unexpected qualification statement")
    tools = exact_keys(summary["tool_commits"], EXPECTED_TOOL_KEYS, "summary tools")
    for tool, tool_commit in tools.items():
        assert_hex(tool_commit, HEX40, f"summary tool commit {tool}")
    manuscripts = exact_keys(
        summary["manuscript_sha256"], EXPECTED_MANUSCRIPT_KEYS, "summary manuscripts"
    )
    for name, digest in manuscripts.items():
        assert_hex(digest, HEX64, f"summary manuscript hash {name}")

    audit_config = parse_json(records, "source-snapshot/audit_config.json")
    fileset = audit_config.get("verification", {}).get("comparator", {}).get("fileset")
    if (
        not isinstance(fileset, list)
        or any(not isinstance(value, str) for value in fileset)
        or len(fileset) != len(set(fileset))
        or set(fileset) != EXPECTED_COMPARATOR_FILESET
    ):
        raise PolicyError("source snapshot has an unexpected Comparator fileset")
    comparator_digest = fileset_digest(records, fileset)
    if summary["comparator_fileset_digest_sha256"] != comparator_digest:
        raise PolicyError("summary Comparator fileset digest mismatch")

    comparator_tools = audit_config.get("verification", {}).get("comparator", {}).get("tools")
    toolchain = audit_config.get("verification", {}).get("toolchain")
    try:
        expected_tools = {
            "lean": toolchain["lean"]["commit"],
            "mathlib": toolchain["mathlib"]["commit"],
            "comparator": comparator_tools["comparator"]["commit"],
            "lean4export": comparator_tools["lean4export"]["commit"],
            "landrun": comparator_tools["landrun"]["commit"],
        }
    except (KeyError, TypeError) as exc:
        raise PolicyError("audit_config.json has incomplete pinned tool commits") from exc
    for name, digest_value in expected_tools.items():
        assert_hex(digest_value, HEX40, f"audit_config.json tool commit {name}")
    if tools != expected_tools:
        raise PolicyError("summary tool commits disagree with audit_config.json")

    results: list[dict] = []
    for label, spec in RESULT_SPECS.items():
        result = parse_json(records, spec["result"])
        config = parse_json(records, f"source-snapshot/{spec['config']}")
        expected_config_keys = {
            "challenge_module",
            "solution_module",
            "theorem_names",
            "permitted_axioms",
            "enable_nanoda",
        }
        exact_keys(config, expected_config_keys, f"Comparator config {label}")
        if config["enable_nanoda"] is not False:
            raise PolicyError(f"Comparator config {label} enables Nanoda")
        validate_result(
            result,
            label,
            spec,
            records,
            commit,
            comparator_digest,
            config,
            expected_tools,
        )
        if result["tool_commits"] != tools or result["manuscript_sha256"] != manuscripts:
            raise PolicyError(f"result {label} disagrees with shared summary identities")
        results.append(result)
    if summary["results"] != results:
        raise PolicyError("summary results are not byte-semantic copies of both result records")
    success = read_retained(records, "SUCCESS")
    expected_success = f"Both hardened Comparator targets validated at {commit}.\n".encode()
    if success != expected_success:
        raise PolicyError("SUCCESS marker does not bind the summary Paper C commit")
    runner_snapshot = read_retained(
        records, "source-snapshot/scripts/run_hardened_comparator.sh"
    )
    for tool_path in POLICY_TOOL_PATHS:
        marker = f"  {tool_path}\n".encode("utf-8")
        if marker not in runner_snapshot:
            raise PolicyError(
                f"hardened runner snapshot does not retain privacy tool: {tool_path}"
            )
    scan_public_safe(records, bytewise(RETAINED_PATHS))
    return {
        "commit": commit,
        "comparator_digest": comparator_digest,
        "tools": tools,
        "manuscripts": manuscripts,
        "results": results,
        "raw_inventory": raw_inventory,
    }


def build_manifest(
    records: dict[str, FileRecord],
    raw_archive_size: int,
    raw_archive_sha256: str,
    evidence: dict,
    zstd_cli_version: str,
    policy_tooling: dict[str, str],
) -> dict:
    commit = evidence["commit"]
    public_base = f"paper-c-hardened-public-{commit}"
    private_base = f"paper-c-hardened-private-{commit}"
    source_paths = []
    for relative in bytewise(EXPECTED_RAW_PATHS):
        record = records[relative]
        entry: dict[str, object] = {
            "source_path": relative,
            "source_bytes": record.size,
            "source_sha256": record.sha256,
        }
        if relative in OMITTED_REASONS:
            entry.update(
                disposition="omitted_host_specific", reason=OMITTED_REASONS[relative]
            )
        else:
            public_path = PUBLIC_RENAMES.get(relative, relative)
            entry.update(
                disposition=(
                    "retained_byte_identical_renamed"
                    if relative in PUBLIC_RENAMES
                    else "retained_byte_identical"
                ),
                public_path=public_path,
                public_bytes=record.size,
                public_sha256=record.sha256,
            )
        source_paths.append(entry)

    result_summaries = []
    for label, spec in RESULT_SPECS.items():
        result = next(value for value in evidence["results"] if value["config"] == spec["config"])
        result_summaries.append(
            {
                "config": result["config"],
                "configuration_sha256": result["configuration_sha256"],
                "theorem_names": result["theorem_names"],
                "exit_code": result["exit_code"],
                "status": result["status"],
                "result_json": spec["result"],
                "omitted_private_transcript": spec["transcript"],
                "omitted_private_transcript_sha256": result["transcript_sha256"],
                "challenge_sha256": result["challenge"]["sha256"],
                "solution_sha256": result["solution"]["sha256"],
            }
        )
    raw_inventory_record = records["SHA256SUMS"]
    return {
        "schema_version": 2,
        "profile": "paper_c_hardened_public_omission_v2",
        "status": "privacy_minimized_public_derivative_by_omission",
        "transformation": "omission_only; every retained source member is byte-identical",
        "source_archive": {
            "private_filename": f"{private_base}.tar.zst",
            "bytes": raw_archive_size,
            "sha256": raw_archive_sha256,
            "logical_root": f"{private_base}/",
            "local_input_path_published": False,
        },
        "public_archive": {
            "intended_filename": f"{public_base}.tar.zst",
            "root": f"{public_base}/",
            "deterministic_container_metadata": {
                "tar_format": "ustar",
                "member_order": "UTF-8 bytewise lexicographic",
                "owner_group": "0:0 numeric; empty names",
                "mtime_utc": "1970-01-01T00:00:00Z",
                "permissions": "directories 0755; files 0644; VERIFY.sh and runner 0755",
                "zstd": "level 19; one worker; content checksum enabled",
                "zstd_cli_version": zstd_cli_version,
            },
        },
        "coverage": {
            "source_paths_total": len(EXPECTED_RAW_PATHS),
            "represented_in_manifest": len(source_paths),
            "retained_byte_identical": len(RETAINED_PATHS),
            "omitted_host_specific": len(OMITTED_REASONS),
            "added_public_documentation_files": bytewise(ADDED_PUBLIC_PATHS),
        },
        "raw_checksum_inventory": {
            "source_path": "SHA256SUMS",
            "public_path": "provenance/RAW_SHA256SUMS",
            "bytes": raw_inventory_record.size,
            "sha256": raw_inventory_record.sha256,
            "semantics": (
                f"Checksums of {len(EXPECTED_RAW_PATHS) - 2} source members; the "
                "hardened runner intentionally "
                "excluded SHA256SUMS itself and SUCCESS."
            ),
        },
        "privacy_tooling": {
            "paper_c_commit": commit,
            "binding": (
                "Each SHA-256 is computed from the named regular file committed at "
                "Paper C source commit Q. The release binding carries the same Q."
            ),
            "files": policy_tooling,
        },
        "essential_evidence": {
            "paper_c_commit": commit,
            "comparator_fileset_digest_sha256": evidence["comparator_digest"],
            "tool_commits": evidence["tools"],
            "manuscript_sha256": evidence["manuscripts"],
            "results": result_summaries,
        },
        "privacy_policy": {
            "omitted_categories": [
                "local username and hostname",
                "home, workspace, toolchain, and randomized temporary paths",
                "UID, GID, and local group memberships",
                "PTY/session identifiers and transient-unit suffixes",
            ],
            "byte_rewriting": False,
            "retained_private_hash_links": True,
            "unexpected_source_paths": "reject",
        },
        "public_audit_limit": (
            "The public archive records and cryptographically binds the commit, "
            "source snapshot, configurations, declared outcomes, exit codes, and "
            "hashes of private transcripts. It does not expose the host-bound logs; "
            "line-by-line forensic review requires the private archive or a fresh run."
        ),
        "source_paths": source_paths,
    }


def privacy_document(manifest: dict) -> bytes:
    essential = manifest["essential_evidence"]
    coverage = manifest["coverage"]
    omitted = [entry for entry in manifest["source_paths"] if entry["disposition"] == "omitted_host_specific"]
    lines = [
        "# Public privacy-minimized hardened Comparator evidence",
        "",
        "## Construction",
        "",
        f"This archive is the omission-only public derivative for Paper C commit `{essential['paper_c_commit']}`.",
        "No retained source file was rewritten. The private input archive is identified only by",
        f"size ({manifest['source_archive']['bytes']} bytes) and SHA-256",
        f"`{manifest['source_archive']['sha256']}`; its local path and host-specific root are not published.",
        "",
        f"Exactly {coverage['retained_byte_identical']} of {coverage['source_paths_total']} source files are retained byte-for-byte.",
        f"Exactly {coverage['omitted_host_specific']} host-specific files are omitted. `REDACTION_MANIFEST.json`",
        "covers every source file with its byte count, SHA-256, disposition, and omission reason.",
        "The unchanged raw inventory is published as `provenance/RAW_SHA256SUMS`.",
        "",
        "## Retained evidence",
        "",
        "The archive retains both result JSON files at their original relative paths, `summary.json`,",
        f"`SUCCESS`, all {len(SNAPSHOT_PATHS)} `source-snapshot/` files, and the raw checksum inventory. Result JSON",
        "files can therefore be copied directly into the release-evidence packaging commit.",
        "",
        "## Omitted host-specific source files",
        "",
    ]
    for index, entry in enumerate(omitted, 1):
        lines.append(f"{index}. `{entry['source_path']}` — {entry['reason']}")
    lines.extend(
        [
            "",
            "## Scope and verification",
            "",
            "The public derivative records and cryptographically binds artifact identity and result",
            "provenance, but does not expose",
            "the private host trace. It is Lean-kernel-only evidence with Nanoda disabled; it is not",
            "a dual-kernel result or a general host-security certification.",
            "",
            "After extraction, run `./VERIFY.sh`. Before publication, run the repository's independent",
            "`scripts/verify_public_comparator_archive.py` against both this archive and the raw source.",
            "",
        ]
    )
    return "\n".join(lines).encode("utf-8")


VERIFY_SCRIPT = b'''#!/bin/sh
set -eu

cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
'''


def write_bytes(path: Path, payload: bytes, mode: int = 0o644) -> None:
    path.parent.mkdir(mode=0o755, parents=True, exist_ok=True)
    with path.open("xb") as output:
        output.write(payload)
    path.chmod(mode)


def populate_public_tree(
    public_dir: Path, records: dict[str, FileRecord], manifest: dict
) -> set[str]:
    public_files: set[str] = set()
    for source_relative in bytewise(RETAINED_PATHS):
        public_relative = PUBLIC_RENAMES.get(source_relative, source_relative)
        target = public_dir.joinpath(*public_relative.split("/"))
        target.parent.mkdir(mode=0o755, parents=True, exist_ok=True)
        source = records[source_relative].retained_copy
        if source is None:
            raise PolicyError(f"internal error: retained source missing for {source_relative}")
        with source.open("rb") as input_file, target.open("xb") as output_file:
            shutil.copyfileobj(input_file, output_file, 1024 * 1024)
        target.chmod(0o755 if public_relative.endswith("run_hardened_comparator.sh") else 0o644)
        size, digest = stable_file_digest(target, f"public retained member {public_relative}")
        source_record = records[source_relative]
        if (size, digest) != (source_record.size, source_record.sha256):
            raise PolicyError(f"retained member was not copied byte-identically: {source_relative}")
        public_files.add(public_relative)

    manifest_payload = f"{json.dumps(manifest, indent=2, ensure_ascii=False)}\n".encode("utf-8")
    write_bytes(public_dir / "REDACTION_MANIFEST.json", manifest_payload)
    write_bytes(public_dir / "PRIVACY.md", privacy_document(manifest))
    write_bytes(public_dir / "VERIFY.sh", VERIFY_SCRIPT, 0o755)
    public_files.update({"REDACTION_MANIFEST.json", "PRIVACY.md", "VERIFY.sh"})

    checksum_lines = []
    for relative in bytewise(public_files):
        _, digest = stable_file_digest(
            public_dir.joinpath(*relative.split("/")), f"public member {relative}"
        )
        checksum_lines.append(f"{digest}  ./{relative}\n")
    write_bytes(public_dir / "SHA256SUMS", "".join(checksum_lines).encode("utf-8"))
    public_files.add("SHA256SUMS")
    for relative in bytewise(public_files):
        assert_public_payload_safe(
            relative, public_dir.joinpath(*relative.split("/")).read_bytes()
        )
    return public_files


def public_directories(public_files: set[str]) -> set[str]:
    directories = {""}
    for relative in public_files:
        parent = PurePosixPath(relative).parent
        while str(parent) != ".":
            directories.add(str(parent))
            parent = parent.parent
    return directories


def write_deterministic_tar(public_dir: Path, root_name: str, output_tar: Path, files: set[str]) -> None:
    entries: list[tuple[str, bool]] = [("", True)]
    entries.extend((relative, True) for relative in public_directories(files) if relative)
    entries.extend((relative, False) for relative in files)
    entries.sort(key=lambda item: (f"{root_name}/{item[0]}").encode("utf-8"))
    with tarfile.open(output_tar, mode="x", format=tarfile.USTAR_FORMAT) as archive:
        for relative, is_directory in entries:
            archive_name = root_name if not relative else f"{root_name}/{relative}"
            info = tarfile.TarInfo(archive_name)
            info.uid = 0
            info.gid = 0
            info.uname = ""
            info.gname = ""
            info.mtime = FIXED_MTIME
            if is_directory:
                info.type = tarfile.DIRTYPE
                info.mode = 0o755
                info.size = 0
                archive.addfile(info)
            else:
                info.type = tarfile.REGTYPE
                info.mode = 0o755 if relative in {
                    "VERIFY.sh",
                    "source-snapshot/scripts/run_hardened_comparator.sh",
                } else 0o644
                source = public_dir.joinpath(*relative.split("/"))
                info.size = source.stat().st_size
                with source.open("rb") as payload:
                    archive.addfile(info, payload)


def resolve_source(source: Path, explicit_archive: Path | None) -> tuple[Path, Path | None]:
    if source.is_dir() and not source.is_symlink():
        archive = explicit_archive if explicit_archive is not None else Path(f"{source}.tar.zst")
        assert_regular_file(archive, "raw archive corresponding to directory")
        return archive.resolve(), source.resolve()
    assert_regular_file(source, "raw evidence source")
    if explicit_archive is not None:
        raise PolicyError("--source-archive is only valid when --source is a directory")
    if not source.name.endswith(".tar.zst"):
        raise PolicyError("raw archive input must end in .tar.zst")
    return source.resolve(), None


def zstd_version() -> str:
    probe = subprocess.run(
        ["zstd", "--version"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
    )
    if probe.returncode != 0:
        raise PolicyError(f"zstd is required: {probe.stderr.strip()}")
    version = probe.stdout.strip()
    if not version or re.search(r"Zstandard CLI.*v\d+\.\d+\.\d+", version) is None:
        raise PolicyError(f"unexpected zstd version output: {version!r}")
    return version


def policy_tooling_identity(
    commit: str, records: dict[str, FileRecord]
) -> dict[str, str]:
    repository = Path(__file__).resolve().parent.parent
    head = subprocess.run(
        ["git", "-C", str(repository), "rev-parse", "--verify", "HEAD^{commit}"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if head.returncode != 0 or head.stdout.strip() != commit:
        raise PolicyError("privacy tooling repository HEAD is not source commit Q")
    status_result = subprocess.run(
        [
            "git",
            "-C",
            str(repository),
            "status",
            "--porcelain=v1",
            "--untracked-files=all",
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if status_result.returncode != 0 or status_result.stdout:
        raise PolicyError("privacy tooling repository must be completely clean at Q")
    identities: dict[str, str] = {}
    for relative in POLICY_TOOL_PATHS:
        current = repository.joinpath(*relative.split("/"))
        current_size, current_sha = stable_file_digest(current, f"privacy tool {relative}")
        committed = subprocess.run(
            ["git", "-C", str(repository), "show", f"{commit}:{relative}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if (
            committed.returncode != 0
            or len(committed.stdout) != current_size
            or hashlib.sha256(committed.stdout).hexdigest() != current_sha
        ):
            raise PolicyError(f"privacy tool differs from source commit Q: {relative}")
        snapshot_record = records[f"source-snapshot/{relative}"]
        if (snapshot_record.size, snapshot_record.sha256) != (current_size, current_sha):
            raise PolicyError(
                f"privacy tool snapshot is not byte-identical to Q tooling: {relative}"
            )
        identities[relative] = current_sha
    return identities


def derive(args: argparse.Namespace) -> tuple[Path, Path, str]:
    source = Path(args.source)
    source_archive_argument = Path(args.source_archive) if args.source_archive else None
    raw_archive, raw_directory = resolve_source(source, source_archive_argument)
    raw_size_before, raw_sha_before = stable_file_digest(raw_archive, "raw hardened archive")
    verify_detached_checksum(raw_archive, raw_sha_before, "raw hardened archive")
    repository = Path(__file__).resolve().parent.parent
    for candidate, label in (
        (raw_archive, "raw hardened archive"),
        *(([(raw_directory, "raw evidence directory")] if raw_directory else [])),
    ):
        try:
            candidate.relative_to(repository)
        except ValueError:
            pass
        else:
            raise PolicyError(f"{label} must be outside the source repository")
    output_argument = Path(args.output_dir)
    if output_argument.exists() or output_argument.is_symlink():
        raise PolicyError(f"output directory must be new: {output_argument}")
    output_dir = output_argument.resolve()
    try:
        output_dir.relative_to(repository)
    except ValueError:
        pass
    else:
        raise PolicyError("output directory must be outside the source repository")
    output_dir.mkdir(mode=0o755, parents=True)

    with tempfile.TemporaryDirectory(prefix=".paper-c-public-build.", dir=output_dir) as temporary:
        temporary_root = Path(temporary)
        retained_dir = temporary_root / "retained"
        records, _raw_root = collect_raw_archive(raw_archive, retained_dir)
        raw_size_after, raw_sha_after = stable_file_digest(raw_archive, "raw hardened archive")
        if (raw_size_before, raw_sha_before) != (raw_size_after, raw_sha_after):
            raise PolicyError("raw hardened archive changed during derivation")
        verify_detached_checksum(raw_archive, raw_sha_after, "raw hardened archive")
        if raw_directory is not None:
            directory_records = collect_raw_directory(raw_directory)
            compare_inventories(records, directory_records)
        evidence = validate_raw_evidence(records)
        tooling = policy_tooling_identity(evidence["commit"], records)
        compressor_version = zstd_version()
        manifest = build_manifest(
            records,
            raw_size_before,
            raw_sha_before,
            evidence,
            compressor_version,
            tooling,
        )
        commit = evidence["commit"]
        root_name = f"paper-c-hardened-public-{commit}"
        archive_name = f"{root_name}.tar.zst"
        final_archive = output_dir / archive_name
        final_checksum = output_dir / f"{archive_name}.sha256"
        partial_archive = output_dir / f"{archive_name}.partial"
        partial_checksum = output_dir / f"{archive_name}.sha256.partial"
        if any(
            candidate.exists() or candidate.is_symlink()
            for candidate in (
                final_archive,
                final_checksum,
                partial_archive,
                partial_checksum,
            )
        ):
            raise PolicyError(f"refusing to overwrite existing public output: {final_archive}")
        public_dir = temporary_root / "public"
        public_dir.mkdir(mode=0o755)
        public_files = populate_public_tree(public_dir, records, manifest)
        tar_path = temporary_root / f"{root_name}.tar"
        write_deterministic_tar(public_dir, root_name, tar_path, public_files)
        candidate_archive = temporary_root / archive_name
        compression = subprocess.run(
            [
                "zstd",
                "-q",
                "-19",
                "-T1",
                "--no-progress",
                "--check",
                str(tar_path),
                "-o",
                str(candidate_archive),
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        if compression.returncode != 0:
            raise PolicyError(f"zstd compression failed: {compression.stderr.strip()}")
        candidate_archive.chmod(0o644)
        _, public_sha = stable_file_digest(candidate_archive, "candidate public archive")
        candidate_checksum = temporary_root / f"{archive_name}.sha256"
        write_bytes(
            candidate_checksum,
            f"{public_sha}  {archive_name}\n".encode("utf-8"),
        )

        verifier = Path(__file__).with_name("verify_public_comparator_archive.py")
        command = [
            sys.executable,
            str(verifier),
            "--source",
            str(source.resolve()),
            "--archive",
            str(candidate_archive),
            "--repository",
            str(Path(__file__).resolve().parent.parent),
        ]
        if source_archive_argument is not None:
            command.extend(["--source-archive", str(source_archive_argument.resolve())])
        verification = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        if verification.returncode != 0:
            raise PolicyError(
                "independent public-archive verification failed:\n"
                f"stdout:\n{verification.stdout}stderr:\n{verification.stderr}"
            )
        os.replace(candidate_archive, partial_archive)
        os.replace(candidate_checksum, partial_checksum)
        os.replace(partial_archive, final_archive)
        os.replace(partial_checksum, final_checksum)
        receipt_path = output_dir / f"{archive_name}.verified.json"
        receipt_partial = output_dir / f"{archive_name}.verified.json.partial"
        if receipt_path.exists() or receipt_path.is_symlink() or receipt_partial.exists():
            raise PolicyError(f"refusing to overwrite verification receipt: {receipt_path}")
        result_hashes = {
            Path(spec["result"]).name: records[spec["result"]].sha256
            for spec in RESULT_SPECS.values()
        }
        receipt = {
            "schema": 1,
            "status": "public_comparator_archive_verification_report",
            "paper_c_commit": commit,
            "archive_filename": archive_name,
            "archive_sha256": public_sha,
            "result_sha256": result_hashes,
            "verifier": "scripts/verify_public_comparator_archive.py",
            "verifier_sha256": tooling["scripts/verify_public_comparator_archive.py"],
            "qualification": (
                "Informational report from the local mandatory verifier; not a signature "
                "or self-sufficient proof. Release binding creation reruns the verifier "
                "against the private raw source."
            ),
        }
        write_bytes(
            receipt_partial,
            f"{json.dumps(receipt, indent=2)}\n".encode("utf-8"),
        )
        os.replace(receipt_partial, receipt_path)
    return final_archive, final_checksum, public_sha


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        description="Derive a deterministic omission-only public Comparator archive."
    )
    result.add_argument(
        "--source",
        required=True,
        help="raw evidence directory or its .tar.zst archive",
    )
    result.add_argument(
        "--source-archive",
        help="raw .tar.zst identity when --source is a directory (default: DIR.tar.zst)",
    )
    result.add_argument(
        "--output-dir",
        required=True,
        help="directory receiving archive and detached SHA-256; existing files are never overwritten",
    )
    return result


def main() -> int:
    try:
        args = parser().parse_args()
        archive, checksum, digest = derive(args)
    except (PolicyError, OSError, subprocess.SubprocessError, tarfile.TarError) as exc:
        print(f"PUBLIC_COMPARATOR_DERIVATION: FAIL: {exc}", file=sys.stderr)
        return 1
    print("PUBLIC_COMPARATOR_DERIVATION: PASS")
    print(f"archive={archive}")
    print(f"archive_sha256={digest}")
    print(f"checksum={checksum}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
