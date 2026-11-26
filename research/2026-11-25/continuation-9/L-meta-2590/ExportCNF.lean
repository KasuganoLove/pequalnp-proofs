import PEqualNP.Defs

open PEqualNP.Defs.LratEncoding

def positives : List Nat := [3,6,12,24,17,33,66,132,264,528,160,640,576,320,288]
def negatives : List Nat := [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]

def dimacsLiteral (l : Nat) : String :=
  (if l % 2 = 1 then "-" else "") ++ toString (l / 2)

def main (args : List String) : IO UInt32 := do
  let slots := ((args[0]?).bind String.toNat?).getD 19
  let output := (args[1]?).getD "petersen-19.cnf"
  let formula := enc2 10 slots (fun r => positives.contains r) (positives ++ negatives)
  let variableCount := formula.foldl (fun m c => c.foldl (fun a l => max a (l / 2)) m) 0
  let body := String.intercalate "\n" (formula.map fun c =>
    String.intercalate " " (c.map dimacsLiteral) ++ " 0")
  IO.FS.writeFile output s!"p cnf {variableCount} {formula.length}\n{body}\n"
  IO.println s!"slots={slots}; rows=30; variables={variableCount}; clauses={formula.length}"
  return 0
