import PEqualNP.Outside.L_meta_1667
open PEqualNP.Outside.L_meta_1667

abbrev Links := Std.HashMap Nat (List (List Sig))

def checkLayer (root : System.FilePath) (cap : Nat) (previous : Links)
    (check : Bool) : IO (Nat × Links) := do
  let path := root / s!"native1673-{cap}.txt"
  let lines := (← IO.FS.readFile path).splitOn "\n"
  let inputsWithRows := wiresOf dead
  let goal := targetOf dead
  let depth := 15-cap
  let mut current : Links := ∅
  let mut count := 0
  let since ← IO.monoMsNow
  let total := lines.length-1
  let mut milestone := 0
  for line in lines do
    if line.isEmpty then continue
    let fields := (line.splitOn " ").map String.toNat!
    let ops := fields[0]!
    let mask := fields[1]!
    let bank := decodeBank depth ops inputsWithRows
    let ws := selectLive mask bank
    let values := ws.map Prod.fst
    if check then
      let rules := (fields.drop 2).filterMap fun item =>
        buildRule dead ops depth bank (item &&& 127) (item >>> 7)
      let links := fun tag => previous.getD tag []
      let ok := decide values.Nodup && !(values.contains goal) &&
        testAll (cap, ws.length, ws, preCov ws, rules, links) ws
      unless ok do
        throw (IO.userError s!"failed at cap {cap}, node {count}")
    let key := keySet values
    current := current.insert key (values :: current.getD key [])
    count := count+1
    if check && count*5/total > milestone then
      milestone := count*5/total
      IO.println s!"cap {cap}, rows {count}/{total}, ms {(← IO.monoMsNow)-since}"
      (← IO.getStdout).flush
  return (count,current)

def main (args : List String) : IO Unit := do
  let root : System.FilePath := args[0]!
  let start := args[1]!.toNat!
  let stop := args[2]!.toNat!
  let mut previous : Links := ∅
  if start>7 then
    previous := (← checkLayer root (start-1) previous false).2
  for cap in [start:stop+1] do
    let (count,cur) ← checkLayer root cap previous true
    previous := cur
    IO.println s!"finished cap {cap}, all {count} verified"
    (← IO.getStdout).flush
