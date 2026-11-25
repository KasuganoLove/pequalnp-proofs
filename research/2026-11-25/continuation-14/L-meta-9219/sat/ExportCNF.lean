import PEqualNP.Defs
open PEqualNP.Defs.LratEncoding

def positives : List Nat := [65, 129, 257, 513, 34, 514, 516, 40, 72, 136, 48, 80, 144]
def rows : List Nat := [33, 65, 129, 257, 513, 34, 66, 130, 258, 514, 36, 68, 132, 260, 516, 40, 72, 136, 264, 520, 48, 80, 144, 272, 528]
def dimacsLiteral (l : Nat) : String :=
  (if l % 2 = 1 then "-" else "") ++ toString (l / 2)

def main (args : List String) : IO UInt32 := do
  let output := (args[0]?).getD "representation-10-sparse.cnf"
  let formula := enc2 10 10 (fun r => positives.contains r) rows
  let variableCount := formula.foldl (fun m c => c.foldl (fun a l => max a (l / 2)) m) 0
  let body := String.intercalate "\n" (formula.map fun c =>
    String.intercalate " " (c.map dimacsLiteral) ++ " 0")
  IO.FS.writeFile output s!"p cnf {variableCount} {formula.length}\n{body}\n"
  IO.println s!"gates=10; rows={rows.length}; maximum_variable={variableCount}; clauses={formula.length}"
  return 0
