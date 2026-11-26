#!/usr/bin/env python3
"""Remove the unnecessary umbrella library directive from the checked source."""
from pathlib import Path
import hashlib,json

base=Path(__file__).resolve().parent
data=(base/'symbolic-L_meta_8323.lean').read_bytes()
record=json.loads((base/'minimal-imports.json').read_text())
assert hashlib.sha256(data).hexdigest()==record['input_sha256']
assert data.startswith(b'import Mathlib\nimport PEqualNP.Defs\n')
data=data.removeprefix(b'import Mathlib\n')
assert hashlib.sha256(data).hexdigest()==record['output_sha256']
(base/'defs-only-L_meta_8323.lean').write_bytes(data)
print(json.dumps({'sha256':record['output_sha256'],'bytes':len(data)}))
