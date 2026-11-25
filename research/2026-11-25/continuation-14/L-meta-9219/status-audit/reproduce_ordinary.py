#!/usr/bin/env python3
"""Recheck the exact public PR13445 source; this is not the project strict checker."""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess

ap = argparse.ArgumentParser()
ap.add_argument("--repo", type=Path, required=True)
ap.add_argument("--source", type=Path, required=True)
args = ap.parse_args()
data = args.source.read_bytes()
expected = "b8a123a25d592f139cf6b212a39a4959de320bf7d32708367603b8a8f8f403d9"
if hashlib.sha256(data).hexdigest() != expected:
    raise SystemExit("Source SHA-256 mismatch; no files changed.")
lean_dir = args.repo.resolve() / "lean"
module = "Pnp9219Negative13445"
target = lean_dir / (module + ".lean")
if target.exists() and target.read_bytes() != data:
    raise SystemExit("Existing module differs; refusing to overwrite.")
target.write_bytes(data)
axioms = lean_dir / (module + "Axioms.lean")
axioms_data = ("import " + module + "\n#print axioms PEqualNP.Outside.L_meta_9224\n").encode()
if axioms.exists() and axioms.read_bytes() != axioms_data:
    raise SystemExit("Existing axioms module differs; refusing to overwrite.")
axioms.write_bytes(axioms_data)
olean = lean_dir / ".lake/build/lib/lean" / (module + ".olean")
olean.parent.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env["LEAN_NUM_THREADS"] = "1"
for cmd in (
    ["lake", "env", "lean", "-j1", "-o", str(olean), target.name],
    ["lake", "env", "lean", "-j1", axioms.name],
):
    subprocess.run(cmd, cwd=lean_dir, env=env, check=True)
