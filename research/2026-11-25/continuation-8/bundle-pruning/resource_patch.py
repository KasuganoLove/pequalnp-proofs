#!/usr/bin/env python3
"""Replace a full edge-count dependency with the explicit edge (0, 21)."""
from pathlib import Path
import argparse
import hashlib
import json

BASE = Path(__file__).resolve().parent
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--input', type=Path, default=BASE / 'finalized-L_meta_8323.lean')
p.add_argument('--output', type=Path, default=BASE / 'optimized-L_meta_8323.lean')
args = p.parse_args()
source = args.input.read_text()
before = hashlib.sha256(source.encode()).hexdigest()
assert before == 'b4c715f1b925e001f5d107ad6e47c7f2e1ed360a6fa3ba390ec129017eb75ef7'
certificate = '''set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
theorem edgeFinset_card : pg4.edgeFinset.card = 105 := by
  decide +kernel
'''
old = '  have hG : pg4.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [edgeFinset_card]; decide)'
new = '''  have hG : pg4.edgeFinset.Nonempty := by
    refine ⟨s((0 : Fin 42), (21 : Fin 42)), ?_⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change (0 : Fin 42) ≠ 21 ∧ (Forward 0 21 ∨ Forward 21 0)
    decide'''
assert source.count(certificate) == 1
assert source.count(old) == 1
source = source.replace(certificate, '').replace(old, new)
assert 'edgeFinset_card' not in source
args.output.write_text(source)
report = {'input_sha256':before, 'output_sha256':hashlib.sha256(source.encode()).hexdigest(),
          'output_bytes':len(source.encode()), 'full_edge_count_declarations_removed':1,
          'replacement':'An explicit edge between vertices 0 and 21 proves nonemptiness.',
          'public_theorem_statement_changed':False}
(BASE / 'resource-patch.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
