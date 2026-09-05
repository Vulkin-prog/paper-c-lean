#!/usr/bin/env python3
"""Check the named declaration inventory and kernel axiom output of PaperCV282.

The source inventory deliberately supports this overlay's simple layout: one
qualified namespace per proof module and named def/theorem/lemma/instance declarations.
It is a coverage/hygiene check, not a Lean parser or a replacement for the kernel.
Unsupported declaration forms fail rather than silently leaving the inventory.
"""

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import tomllib


ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
LEAN_PIN = "leanprover/lean4:v4.32.0"
MATHLIB_PIN = "81a5d257c8e410db227a6665ed08f64fea08e997"
FORBIDDEN = re.compile(
    r"\b(sorry|admit|axiom|native_decide|unsafe|partial|opaque|"
    r"macro|elab|syntax|run_elab|run_meta|initialize|inductive|structure|class|"
    r"abbrev|constant|example|export|alias)\b"
)


def uncomment(source):
    """Remove nested Lean comments, preserving lines and token boundaries."""
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif not depth and source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i] if not depth or source[i] == "\n" else " ")
            i += 1
    if depth:
        raise ValueError("Unclosed source comment")
    return "".join(out)


def declarations(source, label):
    code = uncomment(source)
    # This fixed field instance is the only supported unnamed instance command.
    # Its proof is checked transitively by the actual kernel axiom transcript.
    code = re.sub(r"^local instance : Fact \(Nat.Prime 2\) := Fact.mk Nat.prime_two$",
                  "", code, flags=re.M)
    if '"' in code:
        raise ValueError(f"{label}: strings require extending the source inventory parser")
    forbidden = FORBIDDEN.search(code)
    if forbidden:
        raise ValueError(f"{label}: unsupported/forbidden token {forbidden.group()}")
    namespaces = re.findall(r"^namespace\s+(\S+)\s*$", code, re.M)
    if len(namespaces) != 1 or not namespaces[0].startswith("PaperC.V282."):
        raise ValueError(f"{label}: expected one qualified PaperC.V282 namespace")
    names = re.findall(r"^(?:local\s+)?(?:def|theorem|lemma|instance)\s+([A-Za-z_][A-Za-z_0-9']*)\b", code, re.M)
    if not names or len(names) != len(re.findall(r"\b(?:def|theorem|lemma|instance)\b", code)):
        raise ValueError(f"{label}: unsupported or empty declaration layout")
    return [f"{namespaces[0]}.{name}" for name in names]


def inventory(root):
    directory = root / "PaperCV282"
    wrappers = {directory / "Main.lean", directory / "Audit.lean"}
    files = sorted(p for p in directory.rglob("*.lean") if p not in wrappers)
    if not files:
        raise ValueError("No proof modules found")
    modules = [str(p.relative_to(root).with_suffix("")).replace("/", ".") for p in files]
    main = uncomment((directory / "Main.lean").read_text()).split()
    if main != [token for module in modules for token in ("import", module)]:
        # Import ordering is immaterial; other commands in Main are not.
        lines = uncomment((directory / "Main.lean").read_text()).strip().splitlines()
        if Counter(line.strip() for line in lines if line.strip()) != Counter("import " + m for m in modules):
            raise ValueError("Main.lean must import exactly every proof module")
    if uncomment((root / "PaperCV282.lean").read_text()).split() != ["import", "PaperCV282.Main"]:
        raise ValueError("PaperCV282.lean must import only PaperCV282.Main")
    names = [name for p in files for name in declarations(p.read_text(), str(p.relative_to(root)))]
    if len(set(names)) != len(names):
        raise ValueError("Duplicate source declaration")
    audit = uncomment((directory / "Audit.lean").read_text())
    commands = re.findall(r"^#print axioms (\S+)\s*$", audit, re.M)
    remainder = re.sub(r"^#print axioms \S+\s*$", "", audit, flags=re.M)
    if remainder.split() != ["import", "PaperCV282.Main"]:
        raise ValueError("Audit.lean contains unsupported commands")
    if Counter(commands) != Counter(names):
        missing = sorted(set(names) - set(commands))
        extra = sorted(set(commands) - set(names))
        raise ValueError(f"Audit inventory mismatch: missing={missing}, extra={extra}, or duplicate entry")
    return names


def check_pins(root):
    if (root / "lean-toolchain").read_text().strip() != LEAN_PIN:
        raise ValueError("Lean must remain at the historical Palomar version 4.32.0")
    manifest = json.loads((root / "lake-manifest.json").read_text())
    mathlib = [p for p in manifest["packages"] if p["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != MATHLIB_PIN or mathlib[0]["inputRev"] != "v4.32.0":
        raise ValueError("Mathlib must retain the historical 4.32.0 revision")
    lake = tomllib.loads((root / "lakefile.toml").read_text())
    requirements = [p for p in lake["require"] if p["name"] == "mathlib"]
    if len(requirements) != 1 or requirements[0]["rev"] != "v4.32.0":
        raise ValueError("Lake must request Mathlib v4.32.0")


RECORD = re.compile(
    r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
)


def check_log(log, expected):
    seen = []
    end = 0
    for record in RECORD.finditer(log):
        if log[end:record.start()].strip():
            raise ValueError("Unrecognized output in Lean audit log")
        name, axioms = record.groups()
        dependencies = {a.strip() for a in (axioms or "").split(",") if a.strip()}
        unexpected = dependencies - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"{name}: unexpected axioms {sorted(unexpected)}")
        seen.append(name)
        end = record.end()
    if log[end:].strip():
        raise ValueError("Unrecognized trailing output in Lean audit log")
    if Counter(seen) != Counter(expected):
        raise ValueError("Lean audit log has missing, extra, or duplicate declarations")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-source", action="store_true")
    parser.add_argument("--log", type=Path)
    args = parser.parse_args()
    if not args.check_source and args.log is None:
        parser.error("use --check-source and/or --log")
    try:
        check_pins(ROOT)
        names = inventory(ROOT)
        if args.log:
            check_log(args.log.read_text(), names)
    except (ValueError, OSError) as error:
        parser.exit(1, f"PaperCV282 audit failed: {error}\n")
    print(f"PaperCV282: {len(names)} named declarations covered" +
          ("; all kernel axiom dependencies allowed" if args.log else ""))


if __name__ == "__main__":
    main()
