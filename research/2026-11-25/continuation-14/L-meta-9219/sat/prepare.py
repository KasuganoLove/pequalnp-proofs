"""Build the exact 25 oneEach rows of the public L-meta-9219 statement."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
mask=7586366;n=10;s=10
rows=[(1<<u)|(1<<(5+v)) for u in range(5) for v in range(5)]
values=[bool(mask>>(5*u+v)&1) for u in range(5) for v in range(5)]
positives=[r for r,b in zip(rows,values) if b]
problem={'task':'L-meta-9219','matrix_mask':mask,'left_inputs':list(range(5)),'right_inputs':list(range(5,10)),'raw_inputs':n,'gate_budget':s,'rows':rows,'values':values,'matrix':[[int(mask>>(5*u+v)&1) for v in range(5)] for u in range(5)],'scope':'Only the 25 oneEach inputs, exactly as RepSizeAtMost; no full Boolean-function claim','statement_sha256':hashlib.sha256((P.parent/'statement.txt').read_bytes()).hexdigest()}
(P/'problem.json').write_text(json.dumps(problem,indent=2)+'\n')
source='''import PEqualNP.Defs
open PEqualNP.Defs.LratEncoding

def positives : List Nat := POSITIVES
def rows : List Nat := ROWS
def dimacsLiteral (l : Nat) : String :=
  (if l % 2 = 1 then "-" else "") ++ toString (l / 2)

def main (args : List String) : IO UInt32 := do
  let output := (args[0]?).getD "representation-10-sparse.cnf"
  let formula := enc2 10 10 (fun r => positives.contains r) rows
  let variableCount := formula.foldl (fun m c => c.foldl (fun a l => max a (l / 2)) m) 0
  let body := String.intercalate "\\n" (formula.map fun c =>
    String.intercalate " " (c.map dimacsLiteral) ++ " 0")
  IO.FS.writeFile output s!"p cnf {variableCount} {formula.length}\\n{body}\\n"
  IO.println s!"gates=10; rows={rows.length}; maximum_variable={variableCount}; clauses={formula.length}"
  return 0
'''.replace('POSITIVES',str(positives)).replace('ROWS',str(rows))
(P/'ExportCNF.lean').write_text(source)
print(json.dumps({'matrix':problem['matrix'],'rows':len(rows),'positive_rows':len(positives),'gate_budget':s}))
