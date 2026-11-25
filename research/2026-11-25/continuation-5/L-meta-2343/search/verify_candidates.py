#!/usr/bin/env python3
"""Independent scalar evaluator of every exact row in L-meta-2343.

This does not import the search generator or trust its stored truth signatures.
It enumerates all 8192 point sets and filters the exact quadrangle predicate.
Only a candidate passing all rows could be a counterexample; near misses are
recorded as failures and are not Lean proofs.
"""
from pathlib import Path
import json

BASE = Path(__file__).resolve().parent


def incidence(p, line):
    return (p-line) % 13 in (0, 1, 3, 9)


line_masks = [sum(1 << p for p in range(13) if incidence(p, l)) for l in range(13)]
positives = [(p, l) for p in range(13) for l in range(13) if incidence(p, l)]
quadrangles = [q for q in range(8192) if q.bit_count() == 4
               and all((q & line).bit_count() <= 2 for line in line_masks)]
assert len(positives) == 52
assert len(quadrangles) == 234


def evaluate(candidate, row):
    wires = list(row)
    raw_length = len(wires)
    assert raw_length == 26
    ops = candidate['free_or']
    assert len(ops) <= 2 and all(isinstance(w, int) and w >= 0 for w in ops)
    wires.append(any(wires[w] if w < raw_length else False for w in ops))
    for j, g in enumerate(candidate['gates']):
        assert len(g) == 3
        op, a, b = g
        assert op in (0, 1)
        assert all(isinstance(w, int) and 0 <= w < 27+j for w in (a, b))
        wires.append((wires[a] and wires[b]) if op == 0 else (wires[a] or wires[b]))
    assert candidate['size'] == len(candidate['gates'])
    o = candidate['output']
    assert isinstance(o, int) and o >= 0
    return wires[o] if o < len(wires) else False


def verify(filename):
    candidate = json.loads((BASE/filename).read_text())
    wrong_positive = []
    wrong_negative = []
    for p, l in positives:
        row = [u == p for u in range(13)] + [v == l for v in range(13)]
        if not evaluate(candidate, row):
            wrong_positive.append([p, l])
    for q in quadrangles:
        row = [bool(q & (1 << p)) for p in range(13)] + [not (q & line) for line in line_masks]
        if evaluate(candidate, row):
            wrong_negative.append([p for p in range(13) if q & (1 << p)])
    return {'file': filename, 'suffix_size': candidate['size'],
            'free_or': candidate['free_or'], 'rows_checked': 286,
            'false_negative_count': len(wrong_positive),
            'false_positive_count': len(wrong_negative),
            'wrong_positive_edges': wrong_positive,
            'wrong_negative_quadrangles': wrong_negative,
            'passes_all_rows': not wrong_positive and not wrong_negative,
            'is_counterexample_to_2343': candidate['size'] < 63 and not wrong_positive and not wrong_negative}


def decode_multioutput():
    source = json.loads((BASE/'multioutput-best.json').read_text())
    gates = source['gates']
    assert len(gates) == 38 and gates[0][0] == 1
    assert all(0 <= w < 13 for w in gates[0][1:])
    for j, (op, a, b) in enumerate(gates):
        assert op in (0, 1) and 0 <= a < 13+j and 0 <= b < 13+j
    def translate(w):
        return w if w < 13 else w+13
    suffix = [[op, translate(a), translate(b)] for op, a, b in gates[1:]]
    terms = []
    for l, output in enumerate(source['outputs']):
        terms.append(27+len(suffix))
        suffix.append([0, 13+l, translate(output)])
    output = terms[0]
    for term in terms[1:]:
        suffix.append([1, output, term])
        output = 26+len(suffix)
    candidate = {'free_or': gates[0][1:], 'gates': suffix, 'output': output, 'size': len(suffix)}
    assert len(suffix) == 62
    (BASE/'multioutput-best-suffix.json').write_text(json.dumps(candidate, indent=2)+'\n')


decode_multioutput()
results = [verify(name) for name in
           ['baseline_0.json', 'baseline_1.json', 'best-62.json', 'multioutput-best-suffix.json']]
assert results[0]['passes_all_rows'] and results[1]['passes_all_rows']
assert all(r['false_negative_count'] == 1 and r['false_positive_count'] == 0 for r in results[2:])
report = {'method': 'Independent scalar circuit evaluator; full point-subset enumeration',
          'positive_rows': 52, 'quadrangle_negative_rows': 234, 'total_rows': 286,
          'results': results, 'any_counterexample': any(r['is_counterexample_to_2343'] for r in results)}
(BASE/'independent-verification.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
