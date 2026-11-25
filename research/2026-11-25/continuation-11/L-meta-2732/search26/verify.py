"""Independent scalar evaluation on every 14-input assignment."""
from pathlib import Path
import json
import re
import sys

HERE = Path(__file__).resolve().parent
path = Path(sys.argv[1])
candidate = json.loads(path.read_text())
edges = [tuple(map(int, p)) for p in re.findall(r'\(\((\d+) : ℕ\), \((\d+) : ℕ\)\)',
                                              (HERE.parent/'statement.txt').read_text())]
assert len(edges) == 21
gates = candidate['gates']
assert candidate['size'] == len(gates)
assert all(op in (0, 1) and 0 <= a < 14+k and 0 <= b < 14+k
           for k, (op, a, b) in enumerate(gates))
assert 0 <= candidate['output'] < 14+len(gates)
fp = fn = 0
first = []
for mask in range(1 << 14):
    wires = [bool(mask & (1 << i)) for i in range(14)]
    expected = any(wires[u] and wires[v] for u, v in edges)
    for op, a, b in gates:
        wires.append(wires[a] and wires[b] if op == 0 else wires[a] or wires[b])
    actual = wires[candidate['output']]
    fp += actual and not expected
    fn += expected and not actual
    if actual != expected and len(first) < 8: first.append(mask)
result = {'source': path.name, 'inputs_checked': 1 << 14, 'size': len(gates),
          'false_positive': fp, 'false_negative': fn, 'first_mismatches': first,
          'correct': fp == fn == 0, 'within_26': len(gates) <= 26}
print(json.dumps(result, indent=2))
