#!/usr/bin/env python3
"""Instantiate the checked ptrdsh/L10458 structure proof for leased L12030."""
from pathlib import Path
import argparse
import hashlib
import json
import re

P = Path(__file__).resolve().parent
ROOT = P.parents[2]
parser = argparse.ArgumentParser()
parser.add_argument('--reference', type=Path,
    default=P.parent / 'L-meta-11315/status-audit/closure-20261125-1421/L_meta_11315.upstream-reference.lean')
parser.add_argument('--output', type=Path,
    default=ROOT / 'pequalnp-proofs/lean/PEqualNP/Outside/L_meta_12030.lean')
args = parser.parse_args()
SOURCE = args.reference
SOURCE_SHA = 'e13152ef69931ca79dc9f4354f6752a38f3c17a48863616654032ab41a18b131'
data = SOURCE.read_bytes()
assert hashlib.sha256(data).hexdigest() == SOURCE_SHA
source = data.decode()
statement = (P / 'statement.txt').read_text().strip()
gap = json.loads((P / 'gap.json').read_text())
assert statement == gap['statement'].strip()
flat_literals = re.findall(r'\(\[([0-9, ]+)\] : List ℕ\)', statement)
assert flat_literals and len(set(flat_literals)) == 1
flat = [int(x) for x in flat_literals[0].split(',')]
edges = list(zip(flat[::2], flat[1::2]))
assert edges == [(0,3),(1,3),(0,4),(1,4),(0,5),(1,5),(3,5),(4,5),
                 (0,6),(1,6),(2,6),(3,6),(4,6),(5,6)]
assert len(set(edges)) == 14 and all(0 <= a < b < 7 for a,b in edges)

def truth(row):
    return any((row >> a) & 1 and (row >> b) & 1 for a,b in edges)

deleted = [[], [1], [1,2], [1,2,4]]
tables = [sum(1 << row for row in range(128)
              if truth(row & ~sum(1 << p for p in removed))) for removed in deleted]
witnesses = [10,68,17]
for i,(p,row) in enumerate(zip([1,2,4],witnesses)):
    assert bool(tables[i] >> row & 1) != bool(tables[i] >> (row & ~(1 << p)) & 1)
    assert tables[i+1] >> 9 & 1
    assert tables[i+1] == sum(1 << x for x in range(128) if tables[i] >> (x & ~(1 << p)) & 1)
core = [0,3,5,6]
assert all(not (tables[3] >> (1 << i) & 1) for i in core)
assert all(tables[3] >> ((1 << i) | (1 << j)) & 1 for i in core for j in core if i != j)

gates = [('or',[0,1]),('or',[3,4]),('and',[7,8]),('or',[7,8]),
         ('and',[10,5]),('or',[9,11]),('or',[10,5]),('or',[13,2]),
         ('and',[14,6]),('or',[12,15])]
for row in range(128):
    wires = [bool(row >> i & 1) for i in range(7)]
    for j,(op,ins) in enumerate(gates):
        assert len(ins) == 2 and all(0 <= q < 7+j for q in ins)
        wires.append(all(wires[q] for q in ins) if op == 'and' else any(wires[q] for q in ins))
    assert wires[16] == truth(row), row

prefix, tail = source.split('\ntheorem lower_with_not ', 1)
old_tables = [340282366920937254223960062001523108352,
              340282366920932417266301880280542784000,
              340282366920835703200710191947082017280,
              340282366920835703200710191947070876160]
for old,new in zip(old_tables,tables):
    assert str(old) in tail
    tail = tail.replace(str(old),str(new))
tail = tail.replace('⟨assignment 18, by decide⟩','⟨assignment 10, by decide⟩')
tail = tail.replace('⟨assignment 20, by decide⟩','⟨assignment 68, by decide⟩')
new_graph = 'def graph (x : Fin 7 → Bool) : Bool := ' + ' || '.join(f'(x {a} && x {b})' for a,b in edges)
tail,count = re.subn(r'^def graph .*$',lambda _:new_graph,tail,flags=re.M)
assert count == 1
witness = 'def witness : List Gate := [' + ', '.join('⟨.'+op+', ['+', '.join(map(str,ins))+']⟩' for op,ins in gates) + ']'
tail,count = re.subn(r'^def witness : List Gate := .*$',lambda _:witness,tail,flags=re.M)
assert count == 1
old_cases = 'rcases hg with ' + ' | '.join(['rfl']*11) + ' <;> simp'
new_cases = 'rcases hg with ' + ' | '.join(['rfl']*10) + ' <;> simp'
assert tail.count(old_cases) == 1
tail = tail.replace(old_cases,new_cases)
tail = tail.replace('⟨witness, 17⟩','⟨witness, 16⟩').replace('⟨witness, 17,','⟨witness, 16,')
tail = tail.replace('witness.length = 11','witness.length = 10')
old_flat = '[0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 5, 6]'
assert old_flat in tail
tail = tail.replace(old_flat,'['+', '.join(map(str,flat))+']')
new_source = (prefix+'\ntheorem lower_with_not '+tail).replace('PEqualNP.Outside.L_meta_11315','PEqualNP.Outside.L_meta_12030')
marker = '\ntheorem PEqualNP.Outside.L_meta_12030 :\n'
before, after = new_source.split(marker)
_, proof = after.split(' := by\n',1)
new_source = before+marker+statement+' := by\n'+proof
credit = (
    '-- Reused with graph-specific data from ptrdsh, merged upstream PR #15263 (L-meta-11315).\n'
    '-- Its generic proof is adapted from merged L-meta-10458; repository Apache-2.0.\n'
    '-- Reference commit: 7dd594cc96b1fc5b83ca9266a00cef93d6871df6\n'
    '-- Reference SHA-256: '+SOURCE_SHA+'\n'
)
new_source = new_source.replace('import PEqualNP.Defs\n','import PEqualNP.Defs\n\n'+credit,1)
check_prefix = new_source.split('\ntheorem lower_with_not ',1)[0]
check_prefix = check_prefix.replace('\n'+credit,'',1).replace('PEqualNP.Outside.L_meta_12030','PEqualNP.Outside.L_meta_11315')
assert check_prefix == prefix
assert new_source.split(marker,1)[1].split(' := by\n',1)[0] == statement
target = args.output
if target.exists():
    assert target.read_text() == new_source, 'Preserve different existing output; review before regeneration'
else:
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text(new_source)
(P/'formalization').mkdir(exist_ok=True)
(P/'formalization/L_meta_12030.structural.lean').write_text(new_source)
report = {
    'task':'L-meta-12030','source_author':'ptrdsh','source_pr':15263,
    'source_sha256':SOURCE_SHA,'generic_prefix_unchanged_except_namespace_and_credit':True,
    'statement_sha256':hashlib.sha256(statement.encode()).hexdigest(),
    'candidate_sha256':hashlib.sha256(new_source.encode()).hexdigest(),
    'candidate_bytes':len(new_source.encode()),'edges':edges,
    'restriction_order':[1,2,4],'truth_tables':tables,
    'restriction_change_witnesses':witnesses,'nonzero_witness_each_stage':9,
    'core_embedding':core,'core_singletons_false':True,'core_pairs_true':True,
    'monotone_witness':{'gates':[{'op':op,'inputs':ins} for op,ins in gates],
                        'output':16,'size':10,'verified_assignments':128},
    'public_statement_exact':True,'ordinary_lean_result':'pending','strict_result':'not run by worker'
}
(P/'formalization/structural-data-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['monotone_witness','edges']},indent=2))

if __name__ == '__main__':
    pass
