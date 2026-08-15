#!/usr/bin/env python3
"""Independently verify a public Comparator archive against its raw source.

This verifier intentionally does not import the derivation implementation.
It reparses both containers, reconstructs the omission policy from constants,
checks every raw and public path, and validates the evidence semantics.
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
from dataclasses import dataclass


HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")
MAX_COMPRESSED_BYTES = 2 << 30
MAX_DECOMPRESSED_BYTES = 4 << 30
MAX_MEMBER_BYTES = 1 << 30
MAX_MEMBERS = 256
MAX_WINDOW_BYTES = 128 << 20
BLOCK = 512

RESULTS = {
    "theorem-one-one": {
        "path": "evidence/theorem-one-one/result-theorem-one-one.json",
        "config": "comparator/theorem_one_one.json",
        "challenge": "Challenge.lean",
        "solution": "Solution.lean",
        "transcript": "evidence/theorem-one-one/comparator-theorem-one-one.txt",
    },
    "infinite-finite-transfer": {
        "path": "evidence/infinite-finite-transfer/result-infinite-finite-transfer.json",
        "config": "comparator/theorem_one_one_transfer.json",
        "challenge": "ChallengeTransfer.lean",
        "solution": "SolutionTransfer.lean",
        "transcript": (
            "evidence/infinite-finite-transfer/"
            "comparator-infinite-finite-transfer.txt"
        ),
    },
}
SNAPSHOT = {
    "source-snapshot/Challenge.lean",
    "source-snapshot/Solution.lean",
    "source-snapshot/ChallengeTransfer.lean",
    "source-snapshot/SolutionTransfer.lean",
    "source-snapshot/comparator/theorem_one_one.json",
    "source-snapshot/comparator/theorem_one_one_transfer.json",
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
OMITTED = {"setup.log"}
for _label in RESULTS:
    _prefix = f"evidence/{_label}"
    OMITTED.update(
        {
            f"{_prefix}/comparator-environment.txt",
            f"{_prefix}/comparator-{_label}.log",
            f"{_prefix}/comparator-{_label}.txt",
            f"{_prefix}/hardening-probe.log",
            f"{_prefix}/systemd-probe-pty.raw",
            f"{_prefix}/systemd-pty.raw",
        }
    )
RETAINED = {
    "SHA256SUMS",
    "SUCCESS",
    "summary.json",
    *SNAPSHOT,
    *(spec["path"] for spec in RESULTS.values()),
}
RAW_FILES = RETAINED | OMITTED
RENAMES = {"SHA256SUMS": "provenance/RAW_SHA256SUMS"}
ADDED = {"PRIVACY.md", "REDACTION_MANIFEST.json", "SHA256SUMS", "VERIFY.sh"}
PUBLIC_FILES = {RENAMES.get(relative, relative) for relative in RETAINED} | ADDED
EXECUTABLE_PUBLIC = {
    "VERIFY.sh",
    "source-snapshot/scripts/run_hardened_comparator.sh",
}
EXPECTED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
RESULT_KEYS = {
    "status", "certifying", "sandboxed", "non_root", "kernels",
    "enable_nanoda", "exit_code", "config", "configuration_sha256",
    "comparator_fileset_digest_sha256", "paper_c_commit", "theorem_names",
    "permitted_axioms", "challenge", "solution", "tool_commits",
    "manuscript_sha256", "transcript", "transcript_sha256",
}
SUMMARY_KEYS = {
    "status", "paper_c_commit", "certifying", "sandboxed", "kernels",
    "enable_nanoda", "pty_transport", "comparator_fileset_digest_sha256",
    "tool_commits", "manuscript_sha256", "results", "qualification",
}
CONFIG_KEYS = {
    "challenge_module", "solution_module", "theorem_names",
    "permitted_axioms", "enable_nanoda",
}
COMPARATOR_FILESET = {
    "Challenge.lean",
    "Solution.lean",
    "ChallengeTransfer.lean",
    "SolutionTransfer.lean",
    "comparator/theorem_one_one.json",
    "comparator/theorem_one_one_transfer.json",
}
POLICY_TOOL_PATHS = (
    "scripts/derive_public_comparator_archive.py",
    "scripts/verify_public_comparator_archive.py",
    "scripts/test_public_comparator_archive.py",
)
PRIVATE_PATTERNS = (
    re.compile(rb"(?:^|[\s\"'=])/(?:home|Users)/[^\s\"'<>]+"),
    re.compile(rb"(?:^|[\s\"'=])/(?:tmp|var/tmp|run/user)/[^\s\"'<>]+"),
    re.compile(rb"(?:^|[\s\"'=])/(?:private/var|Volumes)/[^\s\"'<>]+"),
    re.compile(rb"(?:^|[\s\"'=])[A-Za-z]:\\[^\s\"'<>]+"),
    re.compile(rb"file://(?:localhost)?/", re.IGNORECASE),
    re.compile(rb"(?m)^(?:HOME|PWD|USER|LOGNAME|HOSTNAME)=[^\r\n]+$"),
    re.compile(rb"(?m)^uname=Linux\s+[^\r\n]+$"),
    re.compile(rb"(?m)^uid=\d+\([^)]+\)\s+gid=\d+\([^)]+\)"),
)
VERIFY_SCRIPT = b'''#!/bin/sh
set -eu

cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
'''


class VerificationError(RuntimeError):
    """A verification invariant failed."""


@dataclass(frozen=True)
class Record:
    size: int
    sha256: str
    payload: bytes | None


def ordered(values) -> list[str]:
    return sorted(values, key=lambda value: value.encode("utf-8"))


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def safe_path(value: str) -> str:
    if not value or value.startswith("/") or "\\" in value or "\x00" in value:
        raise VerificationError(f"unsafe archive path: {value!r}")
    try:
        encoded = value.encode("ascii")
    except UnicodeEncodeError as exc:
        raise VerificationError(f"non-ASCII archive path: {value!r}") from exc
    if any(byte < 0x20 or byte == 0x7F for byte in encoded):
        raise VerificationError(f"control byte in archive path: {value!r}")
    candidate = value[:-1] if value.endswith("/") else value
    parts = candidate.split("/")
    if any(part in {"", ".", ".."} for part in parts):
        raise VerificationError(f"non-canonical archive path: {value!r}")
    if str(PurePosixPath(*parts)) != candidate:
        raise VerificationError(f"non-canonical archive path: {value!r}")
    return candidate


def regular(path: Path, label: str) -> os.stat_result:
    try:
        info = path.lstat()
    except FileNotFoundError as exc:
        raise VerificationError(f"{label} is missing: {path}") from exc
    if not stat.S_ISREG(info.st_mode) or path.is_symlink():
        raise VerificationError(f"{label} is not a regular non-symlink: {path}")
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
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
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


def verify_sidecar(archive: Path, digest: str, label: str) -> None:
    sidecar = Path(f"{archive}.sha256")
    sidecar_size, _ = stable_digest(sidecar, f"{label} checksum sidecar")
    if sidecar_size > 4096:
        raise VerificationError(f"{label} checksum sidecar is unexpectedly large")
    try:
        payload = sidecar.read_text(encoding="ascii")
    except (UnicodeDecodeError, OSError) as exc:
        raise VerificationError(f"{label} checksum sidecar is not ASCII") from exc
    if payload != f"{digest}  {archive.name}\n":
        raise VerificationError(f"{label} checksum sidecar mismatch")


def parse_octal(field: bytes, label: str) -> int:
    if field and field[0] & 0x80:
        raise VerificationError(f"base-256 tar number is forbidden in {label}")
    stripped = field.rstrip(b"\0 ").lstrip(b" ")
    if not stripped:
        return 0
    if re.fullmatch(rb"[0-7]+", stripped) is None:
        raise VerificationError(f"invalid octal tar number in {label}")
    return int(stripped, 8)


def header_name(header: bytes) -> str:
    def text(field: bytes, label: str) -> str:
        prefix = field.split(b"\0", 1)[0]
        if field[len(prefix) :].strip(b"\0"):
            raise VerificationError(f"garbage after NUL in tar {label}")
        try:
            return prefix.decode("ascii")
        except UnicodeDecodeError as exc:
            raise VerificationError(f"non-ASCII tar {label}") from exc

    name = text(header[0:100], "name")
    prefix = text(header[345:500], "prefix")
    return f"{prefix}/{name}" if prefix else name


def validate_tar_blocks(path: Path, public: bool) -> None:
    size = path.stat().st_size
    if size < 2 * BLOCK or size % BLOCK:
        raise VerificationError("decompressed tar has an invalid block length")
    members = 0
    pending_long_name = False
    with path.open("rb") as stream:
        while True:
            header = stream.read(BLOCK)
            if len(header) != BLOCK:
                raise VerificationError("tar ended before its zero terminator")
            if header == bytes(BLOCK):
                second = stream.read(BLOCK)
                if second != bytes(BLOCK):
                    raise VerificationError("tar has only one zero terminator block")
                while remainder := stream.read(1024 * 1024):
                    if remainder.strip(b"\0"):
                        raise VerificationError("tar contains non-zero trailing data")
                if pending_long_name:
                    raise VerificationError("dangling GNU long-name header")
                break
            members += 1
            if members > MAX_MEMBERS:
                raise VerificationError("tar contains too many headers")
            checksum = parse_octal(header[148:156], "checksum")
            check_header = bytearray(header)
            check_header[148:156] = b"        "
            if sum(check_header) != checksum:
                raise VerificationError("tar header checksum mismatch")
            typeflag = header[156:157]
            if public:
                if header[257:263] != b"ustar\0" or header[263:265] != b"00":
                    raise VerificationError("public archive is not canonical POSIX ustar")
                if typeflag not in {b"0", b"5"}:
                    raise VerificationError(f"forbidden public tar type {typeflag!r}")
                if header[157:257].strip(b"\0"):
                    raise VerificationError("public tar linkname field is not empty")
                if parse_octal(header[329:337], "device major") != 0 or parse_octal(
                    header[337:345], "device minor"
                ) != 0:
                    raise VerificationError("public tar device fields are not zero")
                if header[500:512].strip(b"\0"):
                    raise VerificationError("public tar reserved header bytes are not zero")
            elif typeflag not in {b"0", b"\0", b"5", b"L"}:
                raise VerificationError(f"forbidden raw tar extension or type {typeflag!r}")
            name = header_name(header)
            member_size = parse_octal(header[124:136], "size")
            if member_size > MAX_MEMBER_BYTES:
                raise VerificationError("tar member exceeds the size limit")
            if typeflag == b"L":
                if public or pending_long_name:
                    raise VerificationError("nested or public GNU long-name header")
                pending_long_name = True
            else:
                safe_path(name)
                if pending_long_name:
                    pending_long_name = False
            if public:
                if parse_octal(header[108:116], "uid") != 0 or parse_octal(
                    header[116:124], "gid"
                ) != 0:
                    raise VerificationError("public tar owner/group is not numeric 0:0")
                if parse_octal(header[136:148], "mtime") != 0:
                    raise VerificationError("public tar mtime is not the fixed epoch")
                if header[265:297].strip(b"\0") or header[297:329].strip(b"\0"):
                    raise VerificationError("public tar uname/gname is not empty")
                expected_mode = 0o755 if typeflag == b"5" else 0o644
                relative_name = name.split("/", 1)[1] if "/" in name else ""
                if relative_name in EXECUTABLE_PUBLIC:
                    expected_mode = 0o755
                if parse_octal(header[100:108], "mode") != expected_mode:
                    raise VerificationError("public tar mode is not canonical")
                if typeflag == b"5" and member_size != 0:
                    raise VerificationError("public tar directory has a payload")
            payload = stream.read(member_size)
            if len(payload) != member_size:
                raise VerificationError("truncated tar member")
            padding_size = (-member_size) % BLOCK
            padding = stream.read(padding_size)
            if len(padding) != padding_size or padding.strip(b"\0"):
                raise VerificationError("tar member has non-zero or truncated padding")
            if typeflag == b"L":
                long_value = payload.rstrip(b"\0")
                try:
                    safe_path(long_value.decode("ascii"))
                except UnicodeDecodeError as exc:
                    raise VerificationError("non-ASCII GNU long-name payload") from exc


def inspect_zstd(archive: Path, label: str, require_content_size: bool) -> int | None:
    size, _ = stable_digest(archive, label)
    if size > MAX_COMPRESSED_BYTES:
        raise VerificationError(f"{label} exceeds the compressed-size limit")
    environment = dict(os.environ)
    environment.update(LC_ALL="C", LANG="C")
    listing = subprocess.run(
        ["zstd", "-lv", "--", str(archive)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=environment,
    )
    output = f"{listing.stdout}\n{listing.stderr}"
    if listing.returncode != 0:
        raise VerificationError(f"could not inspect {label} as zstd: {output.strip()}")
    if re.search(r"# Zstandard Frames:\s+1\b", output) is None:
        raise VerificationError(f"{label} must contain exactly one zstd frame")
    skippable = re.search(r"# Skippable Frames:\s+(\d+)\b", output)
    if skippable is not None and int(skippable.group(1)) != 0:
        raise VerificationError(f"{label} contains a forbidden skippable zstd frame")
    if re.search(r"DictID:\s+0\b", output) is None:
        raise VerificationError(f"{label} must not use a zstd dictionary")
    if re.search(r"Check:\s+XXH64\b", output) is None:
        raise VerificationError(f"{label} zstd frame must carry a checksum")
    window = re.search(r"Window Size:.*\((\d+) B\)", output)
    if window is None or int(window.group(1)) > MAX_WINDOW_BYTES:
        raise VerificationError(f"{label} has an absent or excessive zstd window")
    exact = re.search(r"Decompressed Size:.*\((\d+) B\)", output)
    if exact is None:
        if require_content_size:
            raise VerificationError(f"{label} does not record its decompressed size")
        return None
    decompressed = int(exact.group(1))
    if decompressed < 2 * BLOCK or decompressed > MAX_DECOMPRESSED_BYTES:
        raise VerificationError(f"{label} has an unsafe decompressed size")
    return decompressed


def decompress(
    archive: Path, target: Path, expected_size: int | None, label: str
) -> None:
    process = subprocess.Popen(
        ["zstd", "-q", "-d", "-M128MiB", "-c", "--", str(archive)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert process.stdout is not None and process.stderr is not None
    observed = 0
    failure: BaseException | None = None
    try:
        with target.open("xb") as output:
            while True:
                chunk = process.stdout.read(1024 * 1024)
                if not chunk:
                    break
                observed += len(chunk)
                if (expected_size is not None and observed > expected_size) or (
                    observed > MAX_DECOMPRESSED_BYTES
                ):
                    raise VerificationError(f"{label} exceeded its declared decompressed size")
                output.write(chunk)
    except BaseException as exc:
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
        raise VerificationError(f"zstd failed to decode {label}: {stderr.strip()}")
    if expected_size is not None and observed != expected_size:
        raise VerificationError(f"{label} decompressed-size mismatch")


def canonical_zstd_bytes(tar_path: Path, temporary: Path) -> bytes:
    candidate = temporary / "canonical-public.tar.zst"
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
            str(candidate),
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if compression.returncode != 0:
        raise VerificationError(
            f"could not reproduce canonical public compression: {compression.stderr.strip()}"
        )
    return candidate.read_bytes()


def directory_set(files: set[str]) -> set[str]:
    result = {""}
    for relative in files:
        parent = PurePosixPath(relative).parent
        while str(parent) != ".":
            result.add(str(parent))
            parent = parent.parent
    return result


def read_tar(
    tar_path: Path,
    wanted_payloads: set[str],
    public: bool,
) -> tuple[str, dict[str, Record], set[str], list[str], dict[str, int]]:
    validate_tar_blocks(tar_path, public)
    roots: set[str] = set()
    files: dict[str, Record] = {}
    directories: set[str] = set()
    order: list[str] = []
    modes: dict[str, int] = {}
    with tarfile.open(tar_path, mode="r:") as archive:
        for member in archive:
            canonical = safe_path(member.name)
            parts = canonical.split("/")
            roots.add(parts[0])
            relative = "/".join(parts[1:])
            order.append(canonical)
            if member.pax_headers or getattr(member, "sparse", None):
                raise VerificationError(f"PAX or sparse metadata is forbidden: {canonical}")
            if member.isdir():
                if relative in directories:
                    raise VerificationError(f"duplicate archive directory: {relative or '/'}")
                directories.add(relative)
                modes[relative] = member.mode
                if public and (
                    member.uid != 0
                    or member.gid != 0
                    or member.uname != ""
                    or member.gname != ""
                    or member.mtime != 0
                    or member.mode != 0o755
                ):
                    raise VerificationError(f"non-canonical public directory metadata: {relative}")
                continue
            if not member.isfile() or not relative:
                raise VerificationError(f"forbidden archive member type: {canonical}")
            if relative in files:
                raise VerificationError(f"duplicate archive file: {relative}")
            if member.size > MAX_MEMBER_BYTES:
                raise VerificationError(f"archive member is too large: {relative}")
            source = archive.extractfile(member)
            if source is None:
                raise VerificationError(f"could not read archive member: {relative}")
            digest = hashlib.sha256()
            pieces: list[bytes] | None = [] if relative in wanted_payloads else None
            observed = 0
            while True:
                chunk = source.read(1024 * 1024)
                if not chunk:
                    break
                observed += len(chunk)
                digest.update(chunk)
                if pieces is not None:
                    pieces.append(chunk)
            source.close()
            if observed != member.size:
                raise VerificationError(f"truncated member: {relative}")
            payload = b"".join(pieces) if pieces is not None else None
            files[relative] = Record(observed, digest.hexdigest(), payload)
            modes[relative] = member.mode
            if public:
                expected_mode = 0o755 if relative in EXECUTABLE_PUBLIC else 0o644
                if (
                    member.uid != 0
                    or member.gid != 0
                    or member.uname != ""
                    or member.gname != ""
                    or member.mtime != 0
                    or member.mode != expected_mode
                ):
                    raise VerificationError(f"non-canonical public file metadata: {relative}")
    if len(roots) != 1:
        raise VerificationError(f"archive must contain exactly one root: {roots}")
    return next(iter(roots)), files, directories, order, modes


def archive_records(
    archive: Path, wanted: set[str], public: bool, temporary: Path, label: str
) -> tuple[str, dict[str, Record], set[str], list[str], dict[str, int], Path]:
    expected_size = inspect_zstd(archive, label, require_content_size=public)
    tar_path = temporary / ("public.tar" if public else "raw.tar")
    decompress(archive, tar_path, expected_size, label)
    root, files, directories, order, modes = read_tar(tar_path, wanted, public)
    return root, files, directories, order, modes, tar_path


def directory_records(directory: Path) -> tuple[dict[str, Record], set[str]]:
    try:
        root_info = directory.lstat()
    except FileNotFoundError as exc:
        raise VerificationError(f"raw directory is missing: {directory}") from exc
    if not stat.S_ISDIR(root_info.st_mode) or directory.is_symlink():
        raise VerificationError("raw directory must be a real non-symlink directory")
    files: dict[str, Record] = {}
    directories = {""}
    for current, children, names in os.walk(directory, followlinks=False):
        current_path = Path(current)
        parent = current_path.relative_to(directory).as_posix()
        parent = "" if parent == "." else parent
        for name in children:
            child = current_path / name
            info = child.lstat()
            if not stat.S_ISDIR(info.st_mode) or child.is_symlink():
                raise VerificationError(f"non-directory or symlink in raw tree: {child}")
            relative = f"{parent}/{name}".lstrip("/")
            directories.add(safe_path(relative))
        for name in names:
            child = current_path / name
            relative = safe_path(f"{parent}/{name}".lstrip("/"))
            size, digest = stable_digest(child, f"raw directory member {relative}")
            payload = child.read_bytes() if relative in RETAINED else None
            if relative in RETAINED and sha256_bytes(payload) != digest:
                raise VerificationError(f"raw directory member changed: {relative}")
            files[relative] = Record(size, digest, payload)
    return files, directories


def resolve_source(source: Path, archive_argument: Path | None) -> tuple[Path, Path | None]:
    if source.is_dir() and not source.is_symlink():
        raw_archive = archive_argument or Path(f"{source}.tar.zst")
        regular(raw_archive, "raw source archive")
        return raw_archive.resolve(), source.resolve()
    regular(source, "raw source archive")
    if archive_argument is not None:
        raise VerificationError("--source-archive is only valid with a raw directory")
    if not source.name.endswith(".tar.zst"):
        raise VerificationError("raw source archive must end in .tar.zst")
    return source.resolve(), None


def parse_json(record: Record, label: str) -> dict:
    if record.payload is None:
        raise VerificationError(f"internal error: no payload for {label}")
    try:
        value = json.loads(record.payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise VerificationError(f"invalid JSON in {label}: {exc}") from exc
    if not isinstance(value, dict):
        raise VerificationError(f"{label} is not a JSON object")
    return value


def checksum_inventory(payload: bytes, expected: set[str], label: str) -> dict[str, str]:
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise VerificationError(f"{label} is not UTF-8") from exc
    if not text.endswith("\n") or "\r" in text or "\x00" in text:
        raise VerificationError(f"{label} has non-canonical line endings")
    result: dict[str, str] = {}
    for line in text.splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  \./(.+)", line)
        if match is None:
            raise VerificationError(f"malformed {label} line: {line!r}")
        relative = safe_path(match.group(2))
        if relative in result:
            raise VerificationError(f"duplicate {label} path: {relative}")
        result[relative] = match.group(1)
    if set(result) != expected:
        raise VerificationError(
            f"{label} path coverage mismatch; missing={ordered(expected - set(result))}, "
            f"unexpected={ordered(set(result) - expected)}"
        )
    return result


def comparator_digest(raw: dict[str, Record], fileset: list[str]) -> str:
    digest = hashlib.sha256()
    for relative in ordered(fileset):
        record = raw[f"source-snapshot/{relative}"]
        if record.payload is None:
            raise VerificationError(f"snapshot payload is missing: {relative}")
        digest.update(relative.encode())
        digest.update(b"\0")
        digest.update(record.payload)
        digest.update(b"\0")
    return digest.hexdigest()


def validate_evidence(raw: dict[str, Record]) -> dict:
    raw_sums_record = raw["SHA256SUMS"]
    assert raw_sums_record.payload is not None
    raw_sums = checksum_inventory(
        raw_sums_record.payload, RAW_FILES - {"SHA256SUMS", "SUCCESS"}, "raw SHA256SUMS"
    )
    for relative, digest in raw_sums.items():
        if raw[relative].sha256 != digest:
            raise VerificationError(f"raw SHA256SUMS mismatch: {relative}")
    summary = parse_json(raw["summary.json"], "summary.json")
    if set(summary) != SUMMARY_KEYS:
        raise VerificationError("summary has an unexpected exact-key schema")
    commit = summary.get("paper_c_commit")
    if not isinstance(commit, str) or HEX40.fullmatch(commit) is None:
        raise VerificationError("summary has no canonical Paper C commit")
    if (
        summary.get("status") != "two_hardened_comparator_targets_passed"
        or summary.get("certifying") is not True
        or summary.get("sandboxed") is not True
        or summary.get("kernels") != ["lean"]
        or summary.get("enable_nanoda") is not False
        or summary.get("pty_transport") != "util-linux-script around systemd-run --user --pty"
        or summary.get("qualification")
        != (
            "Lean-kernel Comparator evidence; not a dual-kernel result or a general "
            "host-security certification."
        )
    ):
        raise VerificationError("summary is not certifying hardened two-target Lean evidence")
    audit = parse_json(raw["source-snapshot/audit_config.json"], "snapshot audit_config.json")
    fileset = audit.get("verification", {}).get("comparator", {}).get("fileset")
    if (
        not isinstance(fileset, list)
        or any(not isinstance(value, str) for value in fileset)
        or len(fileset) != len(set(fileset))
        or set(fileset) != COMPARATOR_FILESET
    ):
        raise VerificationError("snapshot Comparator fileset is unexpected")
    digest = comparator_digest(raw, fileset)
    if summary.get("comparator_fileset_digest_sha256") != digest:
        raise VerificationError("summary Comparator digest mismatch")
    tools = summary.get("tool_commits")
    if not isinstance(tools, dict) or set(tools) != {
        "lean", "mathlib", "comparator", "lean4export", "landrun"
    } or any(not isinstance(value, str) or HEX40.fullmatch(value) is None for value in tools.values()):
        raise VerificationError("summary tool commits are malformed")
    try:
        audit_tools = audit["verification"]["comparator"]["tools"]
        audit_toolchain = audit["verification"]["toolchain"]
        expected_tools = {
            "lean": audit_toolchain["lean"]["commit"],
            "mathlib": audit_toolchain["mathlib"]["commit"],
            "comparator": audit_tools["comparator"]["commit"],
            "lean4export": audit_tools["lean4export"]["commit"],
            "landrun": audit_tools["landrun"]["commit"],
        }
    except (KeyError, TypeError) as exc:
        raise VerificationError("snapshot audit_config has incomplete tool pins") from exc
    if tools != expected_tools:
        raise VerificationError("summary tools disagree with snapshot audit_config")
    manuscripts = summary.get("manuscript_sha256")
    if not isinstance(manuscripts, dict) or set(manuscripts) != {
        "target_pdf", "source_pdf_fr"
    } or any(not isinstance(value, str) or HEX64.fullmatch(value) is None for value in manuscripts.values()):
        raise VerificationError("summary manuscript hashes are malformed")
    parsed_results = []
    for label, spec in RESULTS.items():
        result = parse_json(raw[spec["path"]], spec["path"])
        config = parse_json(
            raw[f"source-snapshot/{spec['config']}"],
            f"source-snapshot/{spec['config']}",
        )
        if set(config) != CONFIG_KEYS:
            raise VerificationError(f"Comparator config has unexpected keys: {label}")
        if set(result) != RESULT_KEYS:
            raise VerificationError(f"result has an unexpected exact-key schema: {label}")
        if (
            result.get("status") != "sandboxed_lean_kernel_passed"
            or result.get("certifying") is not True
            or result.get("sandboxed") is not True
            or result.get("non_root") is not True
            or result.get("kernels") != ["lean"]
            or result.get("enable_nanoda") is not False
            or result.get("exit_code") != 0
            or result.get("paper_c_commit") != commit
            or result.get("config") != spec["config"]
            or result.get("permitted_axioms") != EXPECTED_AXIOMS
            or result.get("comparator_fileset_digest_sha256") != digest
            or result.get("tool_commits") != tools
            or result.get("manuscript_sha256") != manuscripts
            or result.get("theorem_names") != config.get("theorem_names")
            or result.get("permitted_axioms") != config.get("permitted_axioms")
            or config.get("enable_nanoda") is not False
        ):
            raise VerificationError(f"result record is inconsistent: {label}")
        names = result.get("theorem_names")
        if (
            not isinstance(names, list)
            or len(names) != 1
            or not isinstance(names[0], str)
            or re.fullmatch(r"[A-Za-z0-9_'.]+", names[0]) is None
        ):
            raise VerificationError(f"result theorem name is malformed: {label}")
        for endpoint in ("challenge", "solution"):
            value = result.get(endpoint)
            expected_file = spec[endpoint]
            expected_hash = raw[f"source-snapshot/{expected_file}"].sha256
            if not isinstance(value, dict) or value != {
                "module": config.get(f"{endpoint}_module"),
                "file": expected_file,
                "sha256": expected_hash,
            } or config.get(f"{endpoint}_module") != Path(expected_file).stem:
                raise VerificationError(f"result {label} {endpoint} binding mismatch")
        if result.get("configuration_sha256") != raw[
            f"source-snapshot/{spec['config']}"
        ].sha256:
            raise VerificationError(f"result {label} configuration hash mismatch")
        if result.get("transcript") != PurePosixPath(spec["transcript"]).name or result.get(
            "transcript_sha256"
        ) != raw[spec["transcript"]].sha256:
            raise VerificationError(f"result {label} private transcript binding mismatch")
        parsed_results.append(result)
    if summary.get("results") != parsed_results:
        raise VerificationError("summary does not embed both exact result objects")
    success = raw["SUCCESS"].payload
    if success != f"Both hardened Comparator targets validated at {commit}.\n".encode():
        raise VerificationError("SUCCESS marker does not bind the summary commit")
    runner = raw["source-snapshot/scripts/run_hardened_comparator.sh"].payload
    assert runner is not None
    for tool_path in POLICY_TOOL_PATHS:
        if f"  {tool_path}\n".encode() not in runner:
            raise VerificationError(
                f"hardened runner snapshot omits privacy tool: {tool_path}"
            )
    return {
        "commit": commit,
        "summary": summary,
        "audit": audit,
        "fileset_digest": digest,
        "tools": tools,
        "manuscripts": manuscripts,
        "results": parsed_results,
    }


def check_repository(
    repository: Path,
    raw: dict[str, Record],
    evidence: dict,
    packaging_evidence_dir: Path | None,
) -> dict[str, str]:
    if not repository.is_dir() or repository.is_symlink():
        raise VerificationError(f"repository is not a real directory: {repository}")
    head = subprocess.run(
        ["git", "-C", str(repository), "rev-parse", "--verify", "HEAD^{commit}"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if head.returncode != 0 or head.stdout.strip() != evidence["commit"]:
        raise VerificationError("repository HEAD is not the certified source commit Q")
    status_result = subprocess.run(
        ["git", "-C", str(repository), "status", "--porcelain=v1", "--untracked-files=all"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if status_result.returncode != 0:
        raise VerificationError("could not inspect repository cleanliness at source commit Q")
    dirty_records = status_result.stdout.decode("utf-8").splitlines()
    if packaging_evidence_dir is None:
        if dirty_records:
            raise VerificationError("repository must be completely clean at source commit Q")
    else:
        canonical_evidence = repository / "release_evidence/v0.48.1"
        if packaging_evidence_dir != canonical_evidence:
            raise VerificationError(
                "packaging allowance is restricted to release_evidence/v0.48.1"
            )
        allowed = {
            "release_evidence/v0.48.1/result-theorem-one-one.json",
            "release_evidence/v0.48.1/result-infinite-finite-transfer.json",
        }
        observed: set[str] = set()
        for record in dirty_records:
            if len(record) < 4 or record[:3] != "?? ":
                raise VerificationError(
                    "packaging verifier permits only two untracked result records"
                )
            observed.add(record[3:])
        if observed != allowed:
            raise VerificationError(
                f"packaging verifier observed unexpected dirty paths: {sorted(observed)}"
            )
    commit = evidence["commit"]
    for snapshot_relative in ordered(SNAPSHOT):
        repository_relative = snapshot_relative.removeprefix("source-snapshot/")
        shown = subprocess.run(
            ["git", "-C", str(repository), "show", f"{commit}:{repository_relative}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        record = raw[snapshot_relative]
        if shown.returncode != 0 or record.payload is None or shown.stdout != record.payload:
            raise VerificationError(
                f"source snapshot differs from commit Q: {repository_relative}"
            )
    for name, key in (
        ("paper_C_complete_v09_en.pdf", "target_pdf"),
        ("paper_C_complete_v09.pdf", "source_pdf_fr"),
    ):
        shown = subprocess.run(
            ["git", "-C", str(repository), "show", f"{commit}:{name}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if shown.returncode != 0 or sha256_bytes(shown.stdout) != evidence["manuscripts"][key]:
            raise VerificationError(f"manuscript hash does not match commit Q: {name}")
    tooling: dict[str, str] = {}
    for relative in POLICY_TOOL_PATHS:
        current = repository.joinpath(*relative.split("/"))
        size, digest = stable_digest(current, f"privacy tool {relative}")
        shown = subprocess.run(
            ["git", "-C", str(repository), "show", f"{commit}:{relative}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if (
            shown.returncode != 0
            or len(shown.stdout) != size
            or sha256_bytes(shown.stdout) != digest
        ):
            raise VerificationError(f"privacy tool differs from commit Q: {relative}")
        tooling[relative] = digest
        snapshot = raw[f"source-snapshot/{relative}"]
        if (snapshot.size, snapshot.sha256) != (size, digest):
            raise VerificationError(
                f"privacy tool snapshot is not byte-identical to Q tooling: {relative}"
            )
    return tooling


def scan_private(public: dict[str, Record]) -> None:
    for relative, record in public.items():
        if record.payload is None:
            raise VerificationError(f"public payload was not retained for scanning: {relative}")
        if b"\0" in record.payload:
            raise VerificationError(f"unexpected binary public member: {relative}")
        for pattern in PRIVATE_PATTERNS:
            match = pattern.search(record.payload)
            if match is not None:
                excerpt = match.group(0)[:120].decode("utf-8", "backslashreplace")
                raise VerificationError(
                    f"private path or identity leaked in {relative}: {excerpt!r}"
                )


def local_zstd_version() -> str:
    probe = subprocess.run(
        ["zstd", "--version"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if probe.returncode != 0:
        raise VerificationError(f"zstd version probe failed: {probe.stderr.strip()}")
    return probe.stdout.strip()


def validate_manifest(
    manifest: dict,
    raw: dict[str, Record],
    raw_archive_size: int,
    raw_archive_sha: str,
    evidence: dict,
    public_name: str,
    policy_tooling: dict[str, str],
) -> None:
    expected_top = {
        "schema_version",
        "profile",
        "status",
        "transformation",
        "source_archive",
        "public_archive",
        "coverage",
        "raw_checksum_inventory",
        "privacy_tooling",
        "essential_evidence",
        "privacy_policy",
        "public_audit_limit",
        "source_paths",
    }
    if set(manifest) != expected_top:
        raise VerificationError("REDACTION_MANIFEST top-level schema mismatch")
    if (
        manifest["schema_version"] != 2
        or manifest["profile"] != "paper_c_hardened_public_omission_v2"
        or manifest["status"] != "privacy_minimized_public_derivative_by_omission"
        or manifest["transformation"]
        != "omission_only; every retained source member is byte-identical"
    ):
        raise VerificationError("REDACTION_MANIFEST profile/status mismatch")
    commit = evidence["commit"]
    expected_private = f"paper-c-hardened-private-{commit}.tar.zst"
    if manifest["source_archive"] != {
        "private_filename": expected_private,
        "bytes": raw_archive_size,
        "sha256": raw_archive_sha,
        "logical_root": f"paper-c-hardened-private-{commit}/",
        "local_input_path_published": False,
    }:
        raise VerificationError("REDACTION_MANIFEST raw archive identity mismatch")
    public_info = manifest["public_archive"]
    if not isinstance(public_info, dict) or set(public_info) != {
        "intended_filename", "root", "deterministic_container_metadata"
    }:
        raise VerificationError("REDACTION_MANIFEST public archive schema mismatch")
    if public_info["intended_filename"] != public_name or public_info["root"] != (
        f"paper-c-hardened-public-{commit}/"
    ):
        raise VerificationError("REDACTION_MANIFEST public name/root mismatch")
    metadata = public_info["deterministic_container_metadata"]
    expected_metadata = {
        "tar_format": "ustar",
        "member_order": "UTF-8 bytewise lexicographic",
        "owner_group": "0:0 numeric; empty names",
        "mtime_utc": "1970-01-01T00:00:00Z",
        "permissions": "directories 0755; files 0644; VERIFY.sh and runner 0755",
        "zstd": "level 19; one worker; content checksum enabled",
        "zstd_cli_version": metadata.get("zstd_cli_version") if isinstance(metadata, dict) else None,
    }
    version = expected_metadata["zstd_cli_version"]
    if (
        not isinstance(version, str)
        or re.search(r"Zstandard CLI.*v\d+\.\d+\.\d+", version) is None
        or metadata != expected_metadata
    ):
        raise VerificationError("REDACTION_MANIFEST deterministic metadata mismatch")
    if version != local_zstd_version():
        raise VerificationError(
            "canonical recompression requires the exact zstd CLI version recorded by creator"
        )
    if manifest["coverage"] != {
        "source_paths_total": len(RAW_FILES),
        "represented_in_manifest": len(RAW_FILES),
        "retained_byte_identical": len(RETAINED),
        "omitted_host_specific": len(OMITTED),
        "added_public_documentation_files": ordered(ADDED),
    }:
        raise VerificationError("REDACTION_MANIFEST coverage counts mismatch")
    raw_sums = raw["SHA256SUMS"]
    if manifest["raw_checksum_inventory"] != {
        "source_path": "SHA256SUMS",
        "public_path": "provenance/RAW_SHA256SUMS",
        "bytes": raw_sums.size,
        "sha256": raw_sums.sha256,
        "semantics": (
            f"Checksums of {len(RAW_FILES) - 2} source members; the hardened runner "
            "intentionally "
            "excluded SHA256SUMS itself and SUCCESS."
        ),
    }:
        raise VerificationError("REDACTION_MANIFEST raw checksum metadata mismatch")
    if manifest["privacy_tooling"] != {
        "paper_c_commit": evidence["commit"],
        "binding": (
            "Each SHA-256 is computed from the named regular file committed at "
            "Paper C source commit Q. The release binding carries the same Q."
        ),
        "files": policy_tooling,
    }:
        raise VerificationError("REDACTION_MANIFEST privacy tooling binding mismatch")
    essential = manifest["essential_evidence"]
    if not isinstance(essential, dict) or (
        essential.get("paper_c_commit") != commit
        or essential.get("comparator_fileset_digest_sha256") != evidence["fileset_digest"]
        or essential.get("tool_commits") != evidence["tools"]
        or essential.get("manuscript_sha256") != evidence["manuscripts"]
    ):
        raise VerificationError("REDACTION_MANIFEST essential evidence mismatch")
    summaries = essential.get("results")
    if not isinstance(summaries, list) or len(summaries) != 2:
        raise VerificationError("REDACTION_MANIFEST result summary count mismatch")
    for expected_result, label, spec in zip(evidence["results"], RESULTS, RESULTS.values()):
        expected_summary = {
            "config": expected_result["config"],
            "configuration_sha256": expected_result["configuration_sha256"],
            "theorem_names": expected_result["theorem_names"],
            "exit_code": 0,
            "status": "sandboxed_lean_kernel_passed",
            "result_json": spec["path"],
            "omitted_private_transcript": spec["transcript"],
            "omitted_private_transcript_sha256": raw[spec["transcript"]].sha256,
            "challenge_sha256": expected_result["challenge"]["sha256"],
            "solution_sha256": expected_result["solution"]["sha256"],
        }
        if summaries[list(RESULTS).index(label)] != expected_summary:
            raise VerificationError(f"REDACTION_MANIFEST result summary mismatch: {label}")
    entries = manifest["source_paths"]
    if not isinstance(entries, list) or len(entries) != len(RAW_FILES):
        raise VerificationError("REDACTION_MANIFEST source path count mismatch")
    seen: set[str] = set()
    for entry in entries:
        if not isinstance(entry, dict) or not isinstance(entry.get("source_path"), str):
            raise VerificationError("malformed REDACTION_MANIFEST source entry")
        relative = safe_path(entry["source_path"])
        if relative in seen:
            raise VerificationError(f"duplicate REDACTION_MANIFEST source path: {relative}")
        seen.add(relative)
        if relative not in RAW_FILES:
            raise VerificationError(f"unexpected REDACTION_MANIFEST source path: {relative}")
        record = raw[relative]
        common = {
            "source_path": relative,
            "source_bytes": record.size,
            "source_sha256": record.sha256,
        }
        if relative in OMITTED:
            if set(entry) != {*common, "disposition", "reason"} or any(
                entry[key] != value for key, value in common.items()
            ) or entry["disposition"] != "omitted_host_specific" or not isinstance(
                entry["reason"], str
            ) or not entry["reason"]:
                raise VerificationError(f"malformed omitted source entry: {relative}")
        else:
            public_relative = RENAMES.get(relative, relative)
            expected_disposition = (
                "retained_byte_identical_renamed" if relative in RENAMES else "retained_byte_identical"
            )
            expected_entry = {
                **common,
                "disposition": expected_disposition,
                "public_path": public_relative,
                "public_bytes": record.size,
                "public_sha256": record.sha256,
            }
            if entry != expected_entry:
                raise VerificationError(f"retained source entry mismatch: {relative}")
    if seen != RAW_FILES or [entry["source_path"] for entry in entries] != ordered(RAW_FILES):
        raise VerificationError("REDACTION_MANIFEST does not cover source paths canonically")
    policy = manifest["privacy_policy"]
    if (
        not isinstance(policy, dict)
        or policy.get("byte_rewriting") is not False
        or policy.get("retained_private_hash_links") is not True
        or policy.get("unexpected_source_paths") != "reject"
        or not isinstance(policy.get("omitted_categories"), list)
        or len(policy["omitted_categories"]) != 4
    ):
        raise VerificationError("REDACTION_MANIFEST privacy policy mismatch")
    if not isinstance(manifest["public_audit_limit"], str) or "does not expose" not in manifest[
        "public_audit_limit"
    ]:
        raise VerificationError("REDACTION_MANIFEST public audit limit is missing")


def verify(args: argparse.Namespace) -> tuple[str, str]:
    source = Path(args.source)
    raw_archive, raw_directory = resolve_source(
        source, Path(args.source_archive) if args.source_archive else None
    )
    public_archive = Path(args.archive).resolve()
    raw_archive_size, raw_archive_sha = stable_digest(raw_archive, "raw source archive")
    public_size, public_sha = stable_digest(public_archive, "public archive")
    repository_root = Path(args.repository).resolve()
    for candidate, label in (
        (raw_archive, "raw source archive"),
        (public_archive, "public archive"),
        *(([(raw_directory, "raw source directory")] if raw_directory else [])),
    ):
        try:
            candidate.resolve().relative_to(repository_root)
        except ValueError:
            pass
        else:
            raise VerificationError(f"{label} must be outside the source repository")
    verify_sidecar(raw_archive, raw_archive_sha, "raw source archive")
    verify_sidecar(public_archive, public_sha, "public archive")
    if public_size > MAX_COMPRESSED_BYTES:
        raise VerificationError("public archive exceeds the compressed-size limit")

    with tempfile.TemporaryDirectory(prefix="paper-c-public-verify.") as temporary_name:
        temporary = Path(temporary_name)
        _, raw, raw_dirs, _, _, _ = archive_records(
            raw_archive, RETAINED, False, temporary, "raw source archive"
        )
        if set(raw) != RAW_FILES or raw_dirs != directory_set(RAW_FILES):
            raise VerificationError(
                f"raw archive path set mismatch; missing={ordered(RAW_FILES - set(raw))}, "
                f"unexpected={ordered(set(raw) - RAW_FILES)}"
            )
        if raw_directory is not None:
            live, live_dirs = directory_records(raw_directory)
            if set(live) != RAW_FILES or live_dirs != directory_set(RAW_FILES):
                raise VerificationError("raw directory path set mismatch")
            for relative in ordered(RAW_FILES):
                if (live[relative].size, live[relative].sha256) != (
                    raw[relative].size,
                    raw[relative].sha256,
                ):
                    raise VerificationError(f"raw directory/archive mismatch: {relative}")
        evidence = validate_evidence(raw)
        repository = Path(args.repository).resolve()
        packaging_dir = (
            Path(args.packaging_evidence_dir).resolve()
            if args.packaging_evidence_dir
            else None
        )
        tooling = check_repository(repository, raw, evidence, packaging_dir)
        expected_name = f"paper-c-hardened-public-{evidence['commit']}.tar.zst"
        if public_archive.name != expected_name:
            raise VerificationError(
                f"public archive filename must be {expected_name}, got {public_archive.name}"
            )
        public_root, public, public_dirs, member_order, _, public_tar_path = archive_records(
            public_archive, PUBLIC_FILES, True, temporary, "public archive"
        )
        if public_root != expected_name.removesuffix(".tar.zst"):
            raise VerificationError("public archive root does not bind the Paper C commit")
        if set(public) != PUBLIC_FILES or public_dirs != directory_set(PUBLIC_FILES):
            raise VerificationError(
                f"public archive path set mismatch; missing={ordered(PUBLIC_FILES - set(public))}, "
                f"unexpected={ordered(set(public) - PUBLIC_FILES)}"
            )
        if member_order != ordered(member_order):
            raise VerificationError("public tar member order is not bytewise lexicographic")
        if public_archive.read_bytes() != canonical_zstd_bytes(public_tar_path, temporary):
            raise VerificationError(
                "public archive is not the canonical level-19 single-worker zstd encoding"
            )
        for source_relative in ordered(RETAINED):
            public_relative = RENAMES.get(source_relative, source_relative)
            source_record = raw[source_relative]
            public_record = public[public_relative]
            if (source_record.size, source_record.sha256) != (
                public_record.size,
                public_record.sha256,
            ) or source_record.payload != public_record.payload:
                raise VerificationError(
                    f"retained member is not byte-identical: {source_relative}"
                )
        if public["provenance/RAW_SHA256SUMS"].payload != raw["SHA256SUMS"].payload:
            raise VerificationError("RAW_SHA256SUMS is not the unchanged raw inventory")
        if public["VERIFY.sh"].payload != VERIFY_SCRIPT:
            raise VerificationError("VERIFY.sh is not the canonical verifier shim")
        assert public["SHA256SUMS"].payload is not None
        public_sums = checksum_inventory(
            public["SHA256SUMS"].payload, PUBLIC_FILES - {"SHA256SUMS"}, "public SHA256SUMS"
        )
        for relative, digest in public_sums.items():
            if public[relative].sha256 != digest:
                raise VerificationError(f"public SHA256SUMS mismatch: {relative}")
        manifest = parse_json(public["REDACTION_MANIFEST.json"], "REDACTION_MANIFEST.json")
        validate_manifest(
            manifest,
            raw,
            raw_archive_size,
            raw_archive_sha,
            evidence,
            expected_name,
            tooling,
        )
        scan_private(public)
        privacy = public["PRIVACY.md"].payload
        assert privacy is not None
        for required in (
            evidence["commit"].encode(),
            raw_archive_sha.encode(),
            b"omission-only",
            b"byte-for-byte",
            b"does not expose",
        ):
            if required not in privacy:
                raise VerificationError("PRIVACY.md omits a required qualification or binding")

        if stable_digest(raw_archive, "raw source archive") != (
            raw_archive_size,
            raw_archive_sha,
        ):
            raise VerificationError("raw source archive changed during verification")
        if stable_digest(public_archive, "public archive") != (public_size, public_sha):
            raise VerificationError("public archive changed during verification")
        verify_sidecar(raw_archive, raw_archive_sha, "raw source archive")
        verify_sidecar(public_archive, public_sha, "public archive")

    return evidence["commit"], public_sha


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        description="Independently verify a privacy-minimized Comparator archive."
    )
    result.add_argument("--source", required=True, help="raw evidence directory or .tar.zst")
    result.add_argument(
        "--source-archive", help="raw archive identity when --source is a directory"
    )
    result.add_argument(
        "--result-hashes-output",
        help="write verified public result SHA-256 values to a new JSON file outside the repository",
    )
    result.add_argument("--archive", required=True, help="public .tar.zst to verify")
    result.add_argument(
        "--repository",
        default=str(Path(__file__).resolve().parent.parent),
        help="clean repository at certified source commit Q",
    )
    result.add_argument(
        "--packaging-evidence-dir",
        help=(
            "allow exactly the two untracked v0.48.1 result records while the "
            "release-binding creator reruns verification"
        ),
    )
    return result


def main() -> int:
    try:
        args = parser().parse_args()
        commit, digest = verify(args)
        if args.result_hashes_output:
            output = Path(args.result_hashes_output).resolve()
            repository = Path(args.repository).resolve()
            if output.exists() or output.is_symlink():
                raise VerificationError(f"result hash output must be new: {output}")
            try:
                output.relative_to(repository)
            except ValueError:
                pass
            else:
                raise VerificationError("result hash output must be outside repository")
            hashes = {
                Path(spec["path"]).name: None for spec in RESULTS.values()
            }
            with tempfile.TemporaryDirectory(prefix="paper-c-public-hashes.") as temporary_name:
                temporary = Path(temporary_name)
                _, public, _, _, _, _ = archive_records(
                    Path(args.archive).resolve(), set(PUBLIC_FILES), True, temporary, "public archive"
                )
                for spec in RESULTS.values():
                    hashes[Path(spec["path"]).name] = public[spec["path"]].sha256
            if stable_digest(
                Path(args.archive).resolve(), "public archive after result-hash extraction"
            )[1] != digest:
                raise VerificationError(
                    "public archive changed while producing verified result hashes"
                )
            payload = {
                "schema": 1,
                "paper_c_commit": commit,
                "archive_sha256": digest,
                "result_sha256": hashes,
            }
            output.parent.mkdir(parents=True, exist_ok=True)
            with output.open("xb") as destination:
                destination.write(f"{json.dumps(payload, indent=2)}\n".encode())
    except (VerificationError, OSError, subprocess.SubprocessError, tarfile.TarError) as exc:
        print(f"PUBLIC_COMPARATOR_VERIFICATION: FAIL: {exc}", file=sys.stderr)
        return 1
    print("PUBLIC_COMPARATOR_VERIFICATION: PASS")
    print(f"paper_c_commit={commit}")
    print(f"archive_sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
