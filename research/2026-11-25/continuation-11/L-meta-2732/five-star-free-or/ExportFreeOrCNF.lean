import PEqualNP.Defs

open PEqualNP.Defs.LratEncoding

def positives : List Nat := [33, 34, 20, 24, 65, 68, 129, 136, 258, 260, 514, 520]
def physicalRows : List Nat := [1057, 1058, 1044, 1048, 65, 68, 129, 136, 258, 260, 514, 520, 15, 1043, 1068, 74, 134, 1234, 265, 1384, 517, 1700, 1809, 2032]

def dimacsLiteral (l : Nat) : String :=
  (if l % 2 = 1 then "-" else "") ++ toString (l / 2)

def main (args : List String) : IO UInt32 := do
  let output := (args[0]?).getD "subdivision-k4-free-or-14.cnf"
  let formula := enc2 11 14 (fun r => positives.contains (r % 1024)) physicalRows
  let variableCount := formula.foldl (fun m c => c.foldl (fun a l => max a (l / 2)) m) 0
  let body := String.intercalate "\n" (formula.map fun c =>
    String.intercalate " " (c.map dimacsLiteral) ++ " 0")
  IO.FS.writeFile output s!"p cnf {variableCount} {formula.length}\n{body}\n"
  IO.println s!"slots=14; rows={physicalRows.length}; variables={variableCount}; clauses={formula.length}"
  return 0
