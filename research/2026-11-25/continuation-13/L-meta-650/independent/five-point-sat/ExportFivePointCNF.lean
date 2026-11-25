import PEqualNP.Defs
open PEqualNP.Defs.LratEncoding

def positives : List Nat := [33, 65, 257, 16385, 34, 130, 8194, 131074, 1028, 16388, 32772, 131076, 520, 8200, 16392, 65544, 144, 2064, 4112, 16400]
def rows : List Nat := [33, 65, 257, 16385, 34, 130, 8194, 131074, 1028, 16388, 32772, 131076, 520, 8200, 16392, 65544, 144, 2064, 4112, 16400, 262112, 245377, 122690, 105987, 80868, 80517, 72518, 72199, 171496, 171145, 40266, 39947, 6636, 6285, 6478, 6159, 239472, 239121, 100178, 99859, 74612, 74261, 66390, 66071, 165240, 164889, 34138, 33819, 380, 350, 31]

def dimacsLiteral (l : Nat) : String :=
  (if l % 2 = 1 then "-" else "") ++ toString (l / 2)

def main (args : List String) : IO UInt32 := do
  let output := (args[0]?).getD "five-point-23-sparse.cnf"
  let formula := enc2 18 23 (fun r => positives.contains r) rows
  let variableCount := formula.foldl (fun m c => c.foldl (fun a l => max a (l / 2)) m) 0
  let body := String.intercalate "\n" (formula.map fun c =>
    String.intercalate " " (c.map dimacsLiteral) ++ " 0")
  IO.FS.writeFile output s!"p cnf {variableCount} {formula.length}\n{body}\n"
  IO.println s!"gates=23; rows={rows.length}; maximum_variable={variableCount}; clauses={formula.length}"
  return 0
