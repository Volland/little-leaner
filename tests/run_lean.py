#!/usr/bin/env python3
"""Check every Lean example in the book against its golden output.

For each `FILE.lean` under `chNN/` or `solutions/` that has a `FILE.out`
beside it, run (from the `code/` folder)

    lake env lean --json chNN/FILE.lean

and turn Lean's messages into text: `#check`, `#eval`, `#print` and
`trace_state` output as it is, errors and warnings with an `error: ` or
`warning: ` prefix on their first line. A message is filed under the
`-- ANCHOR: name` region of the source that contains it, so the golden
file has the same anchors and the book can quote one output at a time:

    %% snippet: ch01/types.out#frog

A file whose first line is `-- expect: error` shows an error on purpose:
it must have at least one. Every other file must have none.

  python3 tests/run_lean.py [--update] [PATH...]

`--update` rewrites the golden files from the current output; read the
diff before you commit it. Run `lake build` once first so `Pond` exists.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FOLDERS = sorted(p for p in ROOT.iterdir()
                 if p.is_dir() and (p.name.startswith("ch")
                                    or p.name == "solutions"))
ANCHOR = re.compile(r"^\s*-- ANCHOR(_END)?: ([\w.-]+)\s*$")


def regions(src: str) -> list[tuple[int, int, str]]:
    """(first line, last line, name) of every anchor, 1-based."""
    open_, out = {}, []
    for n, line in enumerate(src.splitlines(), 1):
        m = ANCHOR.match(line)
        if not m:
            continue
        if m.group(1):
            out.append((open_.pop(m.group(2)), n, m.group(2)))
        else:
            open_[m.group(2)] = n
    return sorted(out)


def render(msg: dict) -> str:
    text = msg["data"].rstrip()
    sev = msg["severity"]
    if sev == "error":
        return "error: " + text
    if sev == "warning":
        return "warning: " + text
    return text


def run(f: Path) -> tuple[int, int, str]:
    """Exit status, error count, golden text."""
    p = subprocess.run(["lake", "env", "lean", "--json",
                        str(f.relative_to(ROOT))], cwd=ROOT,
                       capture_output=True, text=True, timeout=300)
    msgs = []
    for line in p.stdout.splitlines():
        line = line.strip()
        if line.startswith("{"):
            msgs.append(json.loads(line))
        elif line:
            msgs.append({"data": line, "severity": "error",
                         "pos": {"line": 0}})
    if p.stderr.strip():
        msgs.append({"data": p.stderr, "severity": "error",
                     "pos": {"line": 0}})
    src = f.read_text(encoding="utf-8")
    regs = regions(src)
    groups: dict[str, list[str]] = {}
    order: list[str] = []
    for m in msgs:
        line = m["pos"]["line"]
        name = next((r[2] for r in reversed(regs)
                     if r[0] <= line <= r[1]), "")
        if name not in groups:
            groups[name] = []
            order.append(name)
        groups[name].append(render(m))
    out = []
    for name in order:
        sep = "\n\n" if any("\n" in g for g in groups[name]) else "\n"
        body = sep.join(groups[name])
        if name:
            out += [f"-- ANCHOR: {name}", body, f"-- ANCHOR_END: {name}"]
        else:
            out.append(body)
    errors = sum(m["severity"] == "error" for m in msgs)
    return p.returncode, errors, "\n".join(out) + ("\n" if out else "")


def main(argv: list[str]) -> int:
    update = "--update" in argv
    paths = [Path(a).resolve() for a in argv if not a.startswith("--")] \
        or FOLDERS
    files = []
    for p in paths:
        files += [p] if p.is_file() else sorted(p.rglob("*.lean"))
    files = [f for f in files if f.with_suffix(".out").exists()]
    bad = 0
    for f in files:
        name = str(f.relative_to(ROOT))
        expect_error = f.read_text(encoding="utf-8") \
            .startswith("-- expect: error")
        rc, errors, out = run(f)
        if expect_error and errors == 0:
            print(f"FAIL {name}: expected an error, got none")
            bad += 1
            continue
        if not expect_error and (errors or rc):
            print(f"FAIL {name}: unexpected error\n{out}")
            bad += 1
            continue
        golden = f.with_suffix(".out")
        if update:
            golden.write_text(out, encoding="utf-8")
            continue
        want = golden.read_text(encoding="utf-8")
        if out != want:
            print(f"FAIL {name}: output differs from {golden.name}")
            print("--- expected\n" + want + "--- got\n" + out)
            bad += 1
    print(f"{len(files) - bad}/{len(files)} examples pass")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
