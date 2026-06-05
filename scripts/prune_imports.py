#!/usr/bin/env python3
"""Per-import prune helper.

Given a .v file, walks through its Require / From-Require directives and tries
removing each module name individually. For each successful removal, the
change is kept; for each failure, the file is restored.

Usage:
  prune_imports.py <file.v>

Assumes Makefile.coq is at /root/pyrosome-ai/Makefile.coq.
"""

import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path("/root/pyrosome-ai")
MAKEFILE = ROOT / "Makefile.coq"

REQ_RE = re.compile(
    r"^(?P<lead>\s*)"
    r"(?:From\s+(?P<src>\S+)\s+)?"
    r"Require(?:\s+(?P<mode>Import|Export))?"
    r"\s+(?P<mods>[^\(\)]+?)"
    r"\s*\.\s*(?:\(\*.*?\*\)\s*)?$"
)


def build(vfile: Path) -> tuple[bool, str]:
    """Build a single .v file via Makefile.coq. Returns (ok, output)."""
    vo = vfile.with_suffix(".vo")
    vok = vfile.with_suffix(".vok")
    vos = vfile.with_suffix(".vos")
    for p in (vo, vok, vos):
        try:
            p.unlink()
        except FileNotFoundError:
            pass
    res = subprocess.run(
        ["make", "-f", str(MAKEFILE), str(vo.resolve())],
        capture_output=True,
        text=True,
        cwd=str(ROOT),
    )
    ok = res.returncode == 0 and vo.exists()
    return ok, res.stdout + res.stderr


def parse_require_lines(lines: list[str]) -> list[tuple[int, dict]]:
    """Return list of (idx, parsed) for each Require line."""
    out = []
    for i, line in enumerate(lines):
        m = REQ_RE.match(line.rstrip("\n"))
        if m:
            mods = m.group("mods").split()
            if not mods:
                continue
            out.append((i, {
                "lead": m.group("lead"),
                "src": m.group("src"),
                "mode": m.group("mode"),
                "mods": mods,
                "raw": line,
            }))
    return out


def rebuild_line(parsed: dict, new_mods: list[str]) -> str:
    if not new_mods:
        return ""  # remove line
    parts = [parsed["lead"]]
    if parsed["src"]:
        parts.append(f"From {parsed['src']} ")
    parts.append("Require")
    if parsed["mode"]:
        parts.append(f" {parsed['mode']}")
    parts.append(" " + " ".join(new_mods) + ".\n")
    return "".join(parts)


def main():
    if len(sys.argv) != 2:
        print("usage: prune_imports.py <file.v>", file=sys.stderr)
        sys.exit(2)

    vfile = Path(sys.argv[1]).resolve()
    if not vfile.exists():
        print(f"no such file: {vfile}", file=sys.stderr)
        sys.exit(2)

    original = vfile.read_text()
    # First, confirm the file builds as-is
    ok, out = build(vfile)
    if not ok:
        print(f"!! initial build of {vfile} FAILS, aborting")
        print(out[-2000:])
        sys.exit(1)

    lines = vfile.read_text().splitlines(keepends=True)
    requires = parse_require_lines(lines)

    # iterate through each require line; try removing each module.
    # Only attempt removal on `Require Import` lines — `Require Export` and
    # bare `Require` are load-bearing for downstream files (re-exporting
    # instances, notations, hint dbs).
    removed = []
    kept = []
    for idx, parsed in requires:
        if parsed["mode"] != "Import":
            continue
        current_mods = list(parsed["mods"])
        i = 0
        while i < len(current_mods):
            trial = current_mods[:i] + current_mods[i+1:]
            lines[idx] = rebuild_line(parsed, trial)
            vfile.write_text("".join(lines))
            ok, _ = build(vfile)
            if ok:
                src = parsed["src"] or "Stdlib?"
                removed.append((src, current_mods[i], parsed["raw"].strip()))
                current_mods = trial
                # don't advance i; the next module slides into position i
            else:
                kept.append((parsed["src"], current_mods[i]))
                i += 1
        # Rewrite final line based on what's left
        lines[idx] = rebuild_line(parsed, current_mods)
        vfile.write_text("".join(lines))

    # Final build to confirm
    ok, out = build(vfile)
    if not ok:
        print("!! final build failed, restoring original")
        vfile.write_text(original)
        print(out[-2000:])
        sys.exit(1)

    print(f"OK {vfile.relative_to(ROOT)}: removed {len(removed)} modules")
    for src, mod, raw in removed:
        print(f"  - {src} :: {mod}")


if __name__ == "__main__":
    main()
