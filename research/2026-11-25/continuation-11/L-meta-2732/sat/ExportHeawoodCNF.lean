import PEqualNP.Defs

open PEqualNP.Defs.LratEncoding

def positives : List Nat := [129, 257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
def negatives : List Nat := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

def dimacsLiteral (l : Nat) : String :=
  (if l % 2 = 1 then "-" else "") ++ toString (l / 2)

def main (args : List String) : IO UInt32 := do
  let slots := ((args[0]?).bind String.toNat?).getD 26
  let output := (args[1]?).getD "heawood-26.cnf"
  let formula := enc2 14 slots (fun r => positives.contains r) (positives ++ negatives)
  let variableCount := formula.foldl (fun m c => c.foldl (fun a l => max a (l / 2)) m) 0
  let body := String.intercalate "\n" (formula.map fun c =>
    String.intercalate " " (c.map dimacsLiteral) ++ " 0")
  IO.FS.writeFile output s!"p cnf {variableCount} {formula.length}\n{body}\n"
  IO.println s!"slots={slots}; rows=58; variables={variableCount}; clauses={formula.length}"
  return 0
