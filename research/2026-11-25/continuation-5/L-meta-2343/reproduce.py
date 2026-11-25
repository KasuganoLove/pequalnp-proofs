#!/usr/bin/env python3
"""Rebuild the archived research modules in the project's pinned Lean environment."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time


MODULES = [
    "Pnp1031OwnershipFinite",
    "Pnp2343Pruning",
    "Pnp2343PruningProductive",
    "Pnp2343QuadClean",
    "Pnp2343CleanCost",
    "Pnp2343FreeOr",
    "Pnp2343CounterexampleShape",
    "Pnp2343SignatureRanks",
    "Pnp2343AxiomAudit",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lean_root", type=Path, help="The checkout's lean/ directory")
    parser.add_argument("--logs", type=Path, help="Output directory; defaults to ./reproduction-logs")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    lean_root = args.lean_root.resolve()
    logs = (args.logs or Path("reproduction-logs")).resolve()
    logs.mkdir(parents=True, exist_ok=True)
    dependencies = json.loads((here / "dependencies.json").read_text())
    for name, expected in dependencies["files"].items():
        actual = sha256(lean_root / name)
        if actual != expected:
            raise SystemExit(f"Pinned dependency differs: {name}; use the documented checkout.")
    defs = hashlib.sha256()
    for path in sorted((lean_root / "PEqualNP/Defs").rglob("*.lean")):
        defs.update(path.relative_to(lean_root).as_posix().encode() + b"\0")
        defs.update(path.read_bytes() + b"\0")
    if defs.hexdigest() != dependencies["defs_tree_sha256"]:
        raise SystemExit("The pinned Defs source tree differs; use the documented checkout.")

    version = subprocess.run(
        ["lake", "env", "lean", "--version"], cwd=lean_root,
        check=True, capture_output=True, text=True,
    ).stdout.strip()
    if "version 4.36.0" not in version:
        raise SystemExit(f"Unexpected compiler: {version}")

    for module in MODULES:
        source = here / "lean" / f"{module}.lean"
        target = lean_root / source.name
        if target.exists() and source.read_bytes() != target.read_bytes():
            raise SystemExit(f"Refusing to overwrite a different existing file: {target}")
        if not target.exists():
            shutil.copy2(source, target)

    output_root = lean_root / ".lake/build/lib/lean"
    output_root.mkdir(parents=True, exist_ok=True)
    upstream = "PEqualNP/Outside/L_meta_4101"
    build = list(MODULES)
    if not (output_root / f"{upstream}.olean").exists():
        build.insert(0, upstream)
    report = {"mode": "ordinary Lean compilation", "compiler": version,
              "official_strict_checker_run": False, "modules": []}
    for module in build:
        output = output_root / f"{module}.olean"
        output.parent.mkdir(parents=True, exist_ok=True)
        log_name = module.replace("/", "_") + ".log"
        command = ["lake", "env", "lean", "-j1", "-o", str(output), f"{module}.lean"]
        started = time.monotonic()
        with (logs / log_name).open("w") as log:
            result = subprocess.run(command, cwd=lean_root, stdout=log, stderr=subprocess.STDOUT)
        entry = {"module": module, "exit_code": result.returncode,
                 "seconds": round(time.monotonic() - started, 3),
                 "source_sha256": sha256(lean_root / f"{module}.lean"), "log": log_name}
        report["modules"].append(entry)
        (logs / "build-results.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"{module}: exit {result.returncode}", flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
