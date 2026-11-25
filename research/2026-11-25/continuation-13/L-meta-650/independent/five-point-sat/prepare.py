from pathlib import Path
import json,re
P=Path(__file__).resolve().parent
statement=(P.parents[1]/'statement.txt').read_text()
full_edges=[tuple(map(int,p)) for p in re.findall(r'\((\d+), (\d+)\)',statement)]
points=[0,1,4,5,7];mapping=points+list(range(13,26));inv={v:i for i,v in enumerate(mapping)}
edges=[(inv[a],inv[b]) for a,b in full_edges if a in points]
assert len(edges)==20 and len({v for e in edges for v in e})==18
collinear=[0,4,5,7]
assert all((p,22) in full_edges for p in collinear) and (1,22) not in full_edges
line_neighbors=[sum(1<<a for a,b in edges if b==l) for l in range(5,18)]
positive=[(1<<a)|(1<<b) for a,b in edges]
negative=[]
for s in range(32):
    ls=[l for l in range(13) if not(s&line_neighbors[l])]
    cover=0
    for l in ls:cover|=line_neighbors[l]
    if cover==(31^s):negative.append(s+sum(1<<(5+l) for l in ls))
assert len(negative)==31
rows=positive+negative
problem={'original_points':points,'collinear_points':collinear,'common_line':22,'off_line_point':1,'raw_to_full650':mapping,'raw_inputs':18,'edges':edges,'positive_masks':positive,'maximal_false_masks':negative,'boundary_rows':rows,'gate_budget':23,'baseline_gate_count':24,'remaining_full650_points':[p for p in range(13) if p not in points],'full650_edges':full_edges,'extension_cost':40}
(P/'problem.json').write_text(json.dumps(problem,indent=2)+'\n')
gates=[]
def emit(op,a,b):gates.append([op,a,b]);return 18+len(gates)-1
stars=[]
for p in range(5):
    ns=[l for a,l in edges if a==p]
    n1=emit(1,ns[0],ns[1]);n2=emit(1,ns[2],ns[3]);n3=emit(1,n1,n2)
    stars.append(emit(0,p,n3))
out=stars[0]
for w in stars[1:]:out=emit(1,out,w)
assert len(gates)==24
(P/'baseline-24.json').write_text(json.dumps({'input_count':18,'gates':gates,'output':out},indent=2)+'\n')
source='''import PEqualNP.Defs
open PEqualNP.Defs.LratEncoding

def positives : List Nat := POSITIVES
def rows : List Nat := ROWS

def dimacsLiteral (l : Nat) : String :=
  (if l % 2 = 1 then "-" else "") ++ toString (l / 2)

def main (args : List String) : IO UInt32 := do
  let output := (args[0]?).getD "five-point-23-sparse.cnf"
  let formula := enc2 18 23 (fun r => positives.contains r) rows
  let variableCount := formula.foldl (fun m c => c.foldl (fun a l => max a (l / 2)) m) 0
  let body := String.intercalate "\\n" (formula.map fun c =>
    String.intercalate " " (c.map dimacsLiteral) ++ " 0")
  IO.FS.writeFile output s!"p cnf {variableCount} {formula.length}\\n{body}\\n"
  IO.println s!"gates=23; rows={rows.length}; maximum_variable={variableCount}; clauses={formula.length}"
  return 0
'''.replace('POSITIVES',str(positive)).replace('ROWS',str(rows))
(P/'ExportFivePointCNF.lean').write_text(source)
print(json.dumps({'selected_points':points,'raw_inputs':18,'edges':20,'positive_rows':len(positive),'maximal_false_rows':len(negative),'total_rows':len(rows),'baseline_gates':len(gates)}))
