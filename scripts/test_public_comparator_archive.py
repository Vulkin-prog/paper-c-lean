#!/usr/bin/env python3
"""Self-test for deterministic public Comparator archive derivation/verification."""

from __future__ import annotations

import hashlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile

sys.dont_write_bytecode = True

SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent
DERIVER = SCRIPT_DIR / "derive_public_comparator_archive.py"
VERIFIER = SCRIPT_DIR / "verify_public_comparator_archive.py"

spec = importlib.util.spec_from_file_location("paper_c_public_deriver", DERIVER)
if spec is None or spec.loader is None:
    raise RuntimeError("could not import derivation policy for synthetic fixture creation")
policy = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = policy
spec.loader.exec_module(policy)


class TestFailure(RuntimeError):
    pass


def sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def run(args: list[str], cwd: Path, success: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        args,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if (result.returncode == 0) != success:
        expectation = "pass" if success else "fail"
        raise TestFailure(
            f"command did not {expectation}: {' '.join(args)}\n"
            f"stdout:\n{result.stdout}stderr:\n{result.stderr}"
        )
    return result


def git_show(repository: Path, relative: str) -> bytes:
    result = subprocess.run(
        ["git", "-C", str(repository), "show", f"HEAD:{relative}"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        raise TestFailure(f"could not read HEAD:{relative}: {result.stderr.decode()}")
    return result.stdout


def source_snapshot(repository: Path) -> dict[str, bytes]:
    result: dict[str, bytes] = {}
    for snapshot_relative in policy.SNAPSHOT_PATHS:
        repository_relative = snapshot_relative.removeprefix("source-snapshot/")
        result[snapshot_relative] = git_show(repository, repository_relative)
    return result


def comparator_fileset_digest(files: dict[str, bytes]) -> str:
    audit = json.loads(files["source-snapshot/audit_config.json"])
    paths = audit["verification"]["comparator"]["fileset"]
    digest = hashlib.sha256()
    for relative in sorted(paths, key=lambda value: value.encode()):
        digest.update(relative.encode())
        digest.update(b"\0")
        digest.update(files[f"source-snapshot/{relative}"])
        digest.update(b"\0")
    return digest.hexdigest()


def build_raw_files(
    repository: Path, private_marker: bytes = b"private host trace\n"
) -> tuple[dict[str, bytes], str]:
    files = source_snapshot(repository)
    commit = subprocess.run(
        ["git", "-C", str(repository), "rev-parse", "HEAD"],
        stdout=subprocess.PIPE,
        text=True,
        check=True,
    ).stdout.strip()
    digest = comparator_fileset_digest(files)
    audit = json.loads(files["source-snapshot/audit_config.json"])
    tools = {
        "lean": audit["verification"]["toolchain"]["lean"]["commit"],
        "mathlib": audit["verification"]["toolchain"]["mathlib"]["commit"],
        "comparator": audit["verification"]["comparator"]["tools"]["comparator"]["commit"],
        "lean4export": audit["verification"]["comparator"]["tools"]["lean4export"]["commit"],
        "landrun": audit["verification"]["comparator"]["tools"]["landrun"]["commit"],
    }
    manuscripts = {
        "target_pdf": sha256(git_show(repository, "paper_C_complete_v09_en.pdf")),
        "source_pdf_fr": sha256(git_show(repository, "paper_C_complete_v09.pdf")),
    }
    results = []
    for label, target in policy.RESULT_SPECS.items():
        transcript = f"private Comparator transcript for {label}\n".encode()
        files[target["transcript"]] = transcript
        for relative in policy.OMITTED_REASONS:
            if relative not in files:
                files[relative] = private_marker + relative.encode() + b"\n"
        result = {
            "status": "sandboxed_lean_kernel_passed",
            "certifying": True,
            "sandboxed": True,
            "non_root": True,
            "kernels": ["lean"],
            "enable_nanoda": False,
            "exit_code": 0,
            "config": target["config"],
            "configuration_sha256": sha256(files[f"source-snapshot/{target['config']}"]),
            "comparator_fileset_digest_sha256": digest,
            "paper_c_commit": commit,
            "theorem_names": [
                "paper_c_theorem_one_one_finite_cylinder"
                if label == "theorem-one-one"
                else "paper_c_theorem_one_one_infinite_finite_law_identity"
            ],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            "challenge": {
                "module": Path(target["challenge"]).stem,
                "file": target["challenge"],
                "sha256": sha256(files[f"source-snapshot/{target['challenge']}"]),
            },
            "solution": {
                "module": Path(target["solution"]).stem,
                "file": target["solution"],
                "sha256": sha256(files[f"source-snapshot/{target['solution']}"]),
            },
            "tool_commits": tools,
            "manuscript_sha256": manuscripts,
            "transcript": Path(target["transcript"]).name,
            "transcript_sha256": sha256(transcript),
        }
        result_payload = f"{json.dumps(result, indent=2)}\n".encode()
        files[target["result"]] = result_payload
        results.append(result)
    summary = {
        "status": "two_hardened_comparator_targets_passed",
        "paper_c_commit": commit,
        "certifying": True,
        "sandboxed": True,
        "kernels": ["lean"],
        "enable_nanoda": False,
        "pty_transport": "util-linux-script around systemd-run --user --pty",
        "comparator_fileset_digest_sha256": digest,
        "tool_commits": tools,
        "manuscript_sha256": manuscripts,
        "results": results,
        "qualification": (
            "Lean-kernel Comparator evidence; not a dual-kernel result or a general "
            "host-security certification."
        ),
    }
    files["summary.json"] = f"{json.dumps(summary, indent=2)}\n".encode()
    files["SUCCESS"] = (
        f"Both hardened Comparator targets validated at {commit}.\n".encode()
    )
    inventory_paths = policy.EXPECTED_RAW_PATHS - {"SHA256SUMS", "SUCCESS"}
    files["SHA256SUMS"] = "".join(
        f"{sha256(files[relative])}  ./{relative}\n"
        for relative in sorted(inventory_paths, key=lambda value: value.encode())
    ).encode()
    if set(files) != policy.EXPECTED_RAW_PATHS:
        raise TestFailure(
            f"synthetic raw set mismatch: missing={policy.EXPECTED_RAW_PATHS - set(files)}, "
            f"extra={set(files) - policy.EXPECTED_RAW_PATHS}"
        )
    return files, commit


def write_raw_archive(
    archive: Path,
    files: dict[str, bytes],
    root: str,
    extra: tuple[str, bytes] | None = None,
    symlink: str | None = None,
    traversal: bool = False,
    stream_compression: bool = False,
) -> None:
    tar_path = archive.with_suffix("").with_suffix("")
    with tarfile.open(tar_path, "w", format=tarfile.USTAR_FORMAT) as output:
        directories = {""}
        names = set(files)
        if extra:
            names.add(extra[0])
        if symlink:
            names.add(symlink)
        for relative in names:
            parent = Path(relative).parent
            while str(parent) != ".":
                directories.add(parent.as_posix())
                parent = parent.parent
        for relative in sorted(directories, key=lambda value: f"{root}/{value}".encode()):
            info = tarfile.TarInfo(root if not relative else f"{root}/{relative}")
            info.type = tarfile.DIRTYPE
            info.mode = 0o700
            output.addfile(info)
        for relative in sorted(files, key=lambda value: value.encode()):
            payload = files[relative]
            info = tarfile.TarInfo(f"{root}/{relative}")
            info.size = len(payload)
            info.mode = 0o600
            output.addfile(info, io.BytesIO(payload))
        if extra:
            info = tarfile.TarInfo(f"{root}/{extra[0]}")
            info.size = len(extra[1])
            output.addfile(info, io.BytesIO(extra[1]))
        if symlink:
            info = tarfile.TarInfo(f"{root}/{symlink}")
            info.type = tarfile.SYMTYPE
            info.linkname = "/etc/passwd"
            output.addfile(info)
        if traversal:
            info = tarfile.TarInfo(f"{root}/../escape")
            info.size = 1
            output.addfile(info, io.BytesIO(b"x"))
    if stream_compression:
        with tar_path.open("rb") as source, archive.open("xb") as destination:
            compression = subprocess.run(
                ["zstd", "-q", "-3", "-T1", "--check", "-c"],
                stdin=source,
                stdout=destination,
                stderr=subprocess.PIPE,
            )
    else:
        compression = subprocess.run(
            ["zstd", "-q", "-3", "-T1", "--check", str(tar_path), "-o", str(archive)],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    if compression.returncode != 0:
        raise TestFailure(f"could not compress raw fixture: {compression.stderr.decode()}")
    tar_path.unlink()
    digest = sha256(archive.read_bytes())
    Path(f"{archive}.sha256").write_text(f"{digest}  {archive.name}\n")


def derive(
    repository: Path, raw: Path, output: Path, success: bool = True
) -> subprocess.CompletedProcess[str]:
    return run(
        [
            sys.executable,
            str(repository / "scripts/derive_public_comparator_archive.py"),
            "--source",
            str(raw),
            "--output-dir",
            str(output),
        ],
        repository,
        success,
    )


def verify(
    repository: Path, raw: Path, public: Path, success: bool = True
) -> subprocess.CompletedProcess[str]:
    return run(
        [
            sys.executable,
            str(repository / "scripts/verify_public_comparator_archive.py"),
            "--source",
            str(raw),
            "--archive",
            str(public),
            "--repository",
            str(repository),
        ],
        repository,
        success,
    )


def mutate_public_archive(
    repository: Path, public: Path, mutation, update_sidecar: bool = True
) -> Path:
    target = public.parent / f"mutated-{public.name}"
    tar_path = target.with_suffix("").with_suffix("")
    extraction = public.parent / "public-tree"
    extraction.mkdir()
    run(["tar", "--zstd", "-xf", str(public), "-C", str(extraction)], repository)
    root = next(extraction.iterdir())
    mutation(root)
    with tarfile.open(tar_path, "w", format=tarfile.USTAR_FORMAT) as output:
        paths = [root, *root.rglob("*")]
        for path in sorted(paths, key=lambda value: value.relative_to(extraction).as_posix().encode()):
            relative = path.relative_to(extraction).as_posix()
            info = tarfile.TarInfo(relative)
            info.uid = info.gid = 0
            info.uname = info.gname = ""
            info.mtime = 0
            if path.is_dir():
                info.type = tarfile.DIRTYPE
                info.mode = 0o755
                output.addfile(info)
            else:
                info.size = path.stat().st_size
                inner = path.relative_to(root).as_posix()
                info.mode = 0o755 if inner in {
                    "VERIFY.sh", "source-snapshot/scripts/run_hardened_comparator.sh"
                } else 0o644
                with path.open("rb") as payload:
                    output.addfile(info, payload)
    run(
        ["zstd", "-q", "-19", "-T1", "--check", str(tar_path), "-o", str(target)],
        repository,
    )
    tar_path.unlink()
    target.rename(public.parent / public.name)
    target = public.parent / public.name
    if update_sidecar:
        digest = sha256(target.read_bytes())
        Path(f"{target}.sha256").write_text(f"{digest}  {target.name}\n")
    return target


def main() -> int:
    if shutil.which("zstd") is None or shutil.which("git") is None:
        raise TestFailure("self-test requires documented commands: zstd and git")
    with tempfile.TemporaryDirectory(prefix="paper-c-public-self-test.") as temporary:
        base = Path(temporary)
        repository = base / "repository"
        shutil.copytree(
            ROOT,
            repository,
            ignore=shutil.ignore_patterns(
                ".git",
                ".lake",
                "ci-logs",
                "__pycache__",
                "*.pyc",
            ),
        )
        run(["git", "init", "-q"], repository)
        run(["git", "config", "user.name", "Public Archive Self-Test"], repository)
        run(
            ["git", "config", "user.email", "public-archive-self-test@example.invalid"],
            repository,
        )
        run(["git", "add", "."], repository)
        run(["git", "commit", "-q", "-m", "synthetic source Q"], repository)
        files, commit = build_raw_files(repository)
        raw = base / "raw.tar.zst"
        write_raw_archive(raw, files, "raw-evidence", stream_compression=True)

        first_out = base / "out-1"
        derive(repository, raw, first_out)
        public_name = f"paper-c-hardened-public-{commit}.tar.zst"
        first = first_out / public_name
        verify(repository, raw, first)

        second_out = base / "out-2"
        derive(repository, raw, second_out)
        second = second_out / public_name
        if first.read_bytes() != second.read_bytes():
            raise TestFailure("derivation is not byte-for-byte deterministic")

        noncanonical_out = base / "out-noncanonical-public"
        derive(repository, raw, noncanonical_out)
        noncanonical_public = noncanonical_out / public_name
        noncanonical_tar = base / "noncanonical-public.tar"
        run(
            [
                "zstd",
                "-q",
                "-d",
                str(noncanonical_public),
                "-o",
                str(noncanonical_tar),
            ],
            repository,
        )
        noncanonical_public.unlink()
        run(
            [
                "zstd",
                "-q",
                "-3",
                "-T1",
                "--check",
                str(noncanonical_tar),
                "-o",
                str(noncanonical_public),
            ],
            repository,
        )
        noncanonical_sha = sha256(noncanonical_public.read_bytes())
        Path(f"{noncanonical_public}.sha256").write_text(
            f"{noncanonical_sha}  {noncanonical_public.name}\n"
        )
        rejected = verify(repository, raw, noncanonical_public, False)
        if "not the canonical level-19" not in rejected.stderr:
            raise TestFailure(
                f"noncanonical public compression was not rejected: {rejected.stderr}"
            )

        bad_raw_sidecar = base / "raw-bad-sidecar.tar.zst"
        shutil.copyfile(raw, bad_raw_sidecar)
        Path(f"{bad_raw_sidecar}.sha256").write_text(
            f"{'0' * 64}  {bad_raw_sidecar.name}\n"
        )
        rejected = derive(
            repository, bad_raw_sidecar, base / "out-bad-raw-sidecar", False
        )
        if "checksum sidecar mismatch" not in rejected.stderr:
            raise TestFailure(f"bad raw sidecar was not rejected: {rejected.stderr}")

        for name, kwargs, expected_text in (
            ("extra", {"extra": ("unexpected.txt", b"x\n")}, "path set mismatch"),
            ("symlink", {"symlink": "unexpected-link"}, "forbidden non-regular"),
            ("traversal", {"traversal": True}, "non-canonical archive path"),
        ):
            malicious = base / f"raw-{name}.tar.zst"
            write_raw_archive(malicious, files, "raw-evidence", **kwargs)
            rejected = derive(repository, malicious, base / f"out-{name}", False)
            if expected_text not in rejected.stderr:
                raise TestFailure(f"{name} rejection lacked diagnostic: {rejected.stderr}")

        leaking_files, _ = build_raw_files(repository)
        result_path = policy.RESULT_SPECS["theorem-one-one"]["result"]
        synthetic_private_path = b"/" + b"home" + b"/alice/private-project\n"
        leaking_files[result_path] += synthetic_private_path
        # Deliberately leave SHA256SUMS stale: the fail-closed pipeline must reject
        # before any public archive can be emitted, regardless of the first guard.
        leaking = base / "raw-leak.tar.zst"
        write_raw_archive(leaking, leaking_files, "raw-evidence")
        rejected = derive(repository, leaking, base / "out-leak", False)
        if "mismatch" not in rejected.stderr and "private path" not in rejected.stderr:
            raise TestFailure(f"privacy leak was not rejected: {rejected.stderr}")

        skippable_out = base / "out-skippable"
        derive(repository, raw, skippable_out)
        skippable_public = skippable_out / public_name
        with skippable_public.open("ab") as output:
            output.write(b"\x50\x2a\x4d\x18\x04\x00\x00\x00LEAK")
        skippable_sha = sha256(skippable_public.read_bytes())
        Path(f"{skippable_public}.sha256").write_text(
            f"{skippable_sha}  {skippable_public.name}\n"
        )
        rejected = verify(repository, raw, skippable_public, False)
        if "skippable zstd frame" not in rejected.stderr:
            raise TestFailure(
                f"skippable zstd payload was not rejected: {rejected.stderr}"
            )

        mutation_out = base / "out-mutated"
        derive(repository, raw, mutation_out)
        mutated = mutation_out / public_name

        def modify_result(root: Path) -> None:
            target = root / "evidence/theorem-one-one/result-theorem-one-one.json"
            target.write_bytes(target.read_bytes() + b" ")

        mutate_public_archive(repository, mutated, modify_result)
        rejected = verify(repository, raw, mutated, False)
        if "byte-identical" not in rejected.stderr:
            raise TestFailure(f"retained-byte mutation was not rejected: {rejected.stderr}")

        stale_sidecar_out = base / "out-stale-public-sidecar"
        derive(repository, raw, stale_sidecar_out)
        stale_sidecar_public = stale_sidecar_out / public_name

        def change_privacy_without_sidecar(root: Path) -> None:
            privacy = root / "PRIVACY.md"
            privacy.write_bytes(privacy.read_bytes() + b"\nchanged\n")

        mutate_public_archive(
            repository,
            stale_sidecar_public,
            change_privacy_without_sidecar,
            update_sidecar=False,
        )
        rejected = verify(repository, raw, stale_sidecar_public, False)
        if "checksum sidecar mismatch" not in rejected.stderr:
            raise TestFailure(
                f"stale public sidecar was not rejected: {rejected.stderr}"
            )

        extra_out = base / "out-public-extra"
        derive(repository, raw, extra_out)
        extra_public = extra_out / public_name

        def add_public_extra(root: Path) -> None:
            (root / "unexpected-public.txt").write_text("unexpected\n")

        mutate_public_archive(repository, extra_public, add_public_extra)
        rejected = verify(repository, raw, extra_public, False)
        if "path set mismatch" not in rejected.stderr:
            raise TestFailure(f"public extra path was not rejected: {rejected.stderr}")

        leak_out = base / "out-public-leak"
        derive(repository, raw, leak_out)
        leak_public = leak_out / public_name

        def add_public_leak(root: Path) -> None:
            privacy = root / "PRIVACY.md"
            privacy.write_bytes(
                privacy.read_bytes()
                + b"\n/"
                + b"home"
                + b"/alice/private-project\n"
            )
            sums = root / "SHA256SUMS"
            lines = []
            for line in sums.read_text().splitlines():
                if line.endswith("./PRIVACY.md"):
                    line = f"{sha256(privacy.read_bytes())}  ./PRIVACY.md"
                lines.append(line)
            sums.write_text("\n".join(lines) + "\n")

        mutate_public_archive(repository, leak_public, add_public_leak)
        rejected = verify(repository, raw, leak_public, False)
        if "private path or identity leaked" not in rejected.stderr:
            raise TestFailure(f"public privacy leak was not rejected: {rejected.stderr}")

    print("PUBLIC_COMPARATOR_ARCHIVE_SELF_TEST: PASS")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (TestFailure, OSError, subprocess.SubprocessError) as error:
        print(f"PUBLIC_COMPARATOR_ARCHIVE_SELF_TEST: FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
