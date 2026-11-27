#!/usr/bin/env python3
"""Regenerate the synthetic fixture and run the current tool's actual format_py.

No shell sourcing, lease action, network request, or Lean process is performed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pnp-tool", type=Path, required=True)
    parser.add_argument("--lean-root", type=Path, required=True)
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    p = base / "smoke"
    cmd = [sys.executable, str(base / "generate_promise_proof.py"),
           "--circuit", str(p / "circuit.json"), "--rows", str(p / "rows.json"),
           "--left", "1", "--right", "3", "--bound", "1",
           "--statement", str(p / "statement.txt"),
           "--theorem", "PEqualNP.Outside.L_meta_generator_smoke",
           "--output", str(p / "L_meta_generator_smoke.lean"),
           "--lean-root", str(args.lean_root), "--scalar-all"]
    result = subprocess.run(cmd, capture_output=True, text=True)
    (p / "generation.log").write_text(result.stdout + result.stderr)
    if result.returncode:
        return result.returncode
    source = p / "L_meta_generator_smoke.lean"
    text = source.read_text()
    # This one fixed generated fixture has only whole-line comments, no strings.
    assert '/-' not in text and '"' not in text
    stripped = "\n".join("" if line.lstrip().startswith("--") else line for line in text.split("\n"))
    checked = p / "L_meta_generator_smoke.comments-removed.lean"
    checked.write_text(stripped)
    state = {"gap": {"imports": ["PEqualNP.Defs", "PEqualNP.Library.Helpers.PromiseColTree"]},
             "note": "Synthetic tooling-only guard input; no public gap or lease"}
    (p / "format-state.json").write_text(json.dumps(state, indent=2) + "\n")
    full = args.pnp_tool.read_text()
    guard = full.split("format_py() { cat <<'PY'\n", 1)[1].split("\nPY\n}", 1)[0] + "\n"
    rel = "lean/PEqualNP/Outside/L_meta_generator_smoke.lean"
    result = subprocess.run([sys.executable, "-I", "-", str(checked), rel, str(p / "format-state.json")],
                            input=guard, text=True, capture_output=True)
    (p / "format.log").write_text(result.stdout + result.stderr)
    digest = lambda data: hashlib.sha256(data).hexdigest()
    report = {
        "scope": "Synthetic tooling candidate only; not a posted proof or lease",
        "format_py_source": str(args.pnp_tool),
        "format_py_source_sha256": digest(args.pnp_tool.read_bytes()),
        "extracted_format_py_sha256": digest(guard.encode()),
        "candidate_sha256": digest(source.read_bytes()),
        "checked_comments_removed_sha256": digest(checked.read_bytes()),
        "exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr,
        "lean_compilation": "NOT_RUN",
    }
    (p / "format-result.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
