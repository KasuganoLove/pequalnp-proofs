#!/usr/bin/env python3
"""Reconstruct the attributed standalone bundle, checking both recorded hashes.

Default output stays in this reproducibility directory. Never edits the canonical
repository source. This is byte-preserving apart from the recorded header insert.
"""
from pathlib import Path
import argparse
import hashlib
import json

BASE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('slim', nargs='?', type=Path, default=BASE / 'slim-L_meta_8323.lean')
parser.add_argument('finalization', nargs='?', type=Path, default=BASE / 'finalization.json')
args = parser.parse_args()
record = json.loads(args.finalization.read_text())
source = args.slim.read_bytes()
digest = lambda b: hashlib.sha256(b).hexdigest()
assert digest(source) == record['slim_input_sha256'], 'Slim input hash does not match finalization record'
prefix = b'import Mathlib\nimport PEqualNP.Defs\n\n'
assert source.startswith(prefix), 'Unexpected imports/header boundary'
result = prefix + record['attribution_header'].encode('utf-8') + source[len(prefix):]
assert digest(result) == record['canonical_sha256'], 'Reconstructed canonical hash does not match record'
output = BASE / 'finalized-L_meta_8323.lean'
output.write_bytes(result)
print(json.dumps({'output': str(output), 'sha256': digest(result), 'bytes': len(result)}, indent=2))
