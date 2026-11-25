#!/usr/bin/env python3
"""Reconstruct the already-checked local candidate from its pinned upstream source."""
import argparse
import hashlib
from pathlib import Path
import re

ap = argparse.ArgumentParser()
ap.add_argument("--source", type=Path, required=True)
ap.add_argument("--output", type=Path, required=True)
args = ap.parse_args()
raw = args.source.read_bytes()
if hashlib.sha256(raw).hexdigest() != "b358ad57b53243df24c1908382c59f29819715761f8eacec38d032b0826aea20":
    raise SystemExit("Wrong L9195 source; no file changed.")
s = raw.decode().replace("L_meta_9195", "L_meta_9269").replace("7387710", "16223860")
oo = [i for i in range(25) if (16223860 >> i) & 1]
zz = [i for i in range(25) if not ((16223860 >> i) & 1)]
for name, values in (("OO", oo), ("ZZ", zz)):
    s, count = re.subn(r"^def " + name + r" : List ℕ := .*?$", "def " + name + " : List ℕ := " + str(values), s, flags=re.M)
    assert count == 1
marker = "namespace PEqualNP.Outside.L_meta_9269\n"
credit = "\n-- Adapted from the checked L-meta-9195 proof by tb-16 in open-goat/pequalnp-proofs.\n-- The argument is unchanged; this instance uses mask 16223860 and its exact one and zero lists.\n"
s = s.replace(marker, marker + credit, 1)
data = s.encode()
assert hashlib.sha256(data).hexdigest() == "9253c0badb498bde9adaa04174a4e4af04c83119c3033de9fa724d3c3d1c4d5f"
if args.output.exists() and args.output.read_bytes() != data:
    raise SystemExit("Output differs; refusing to overwrite.")
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_bytes(data)
print("Reconstructed exact9253c0ba candidate; no Lean or strict checker run.")
