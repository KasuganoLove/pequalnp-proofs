import PEqualNP.Outside.L_meta_8323
import Lean

open Lean Elab Command

private def rangeJson (r : DeclarationRanges) : Json :=
  Json.mkObj [
    ("startLine", toJson r.range.pos.line),
    ("startColumn", toJson r.range.pos.column),
    ("endLine", toJson r.range.endPos.line),
    ("endColumn", toJson r.range.endPos.column),
    ("selectionLine", toJson r.selectionRange.pos.line),
    ("selectionColumn", toJson r.selectionRange.pos.column)]

private def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

set_option maxHeartbeats 0 in
run_elab do
  let env ← getEnv
  let target := `PEqualNP.Outside.L_meta_8323
  let some idx := env.getModuleIdx? target | throwError "Target module is not imported"
  let own := env.header.moduleData[idx]!.constants
  let mut table : Std.HashMap Name ConstantInfo := {}
  for ci in own do table := table.insert ci.name ci
  let mut seen : NameSet := {}
  let mut todo := #[target]
  let mut position := 0
  while position < todo.size do
    let n := todo[position]!
    position := position + 1
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := table[n]? | continue
    for d in ci.getUsedConstantsAsSet do
      if table.contains d && !seen.contains d then todo := todo.push d
  let mut rows : Array Json := #[]
  let mut ranged : Nat := 0
  for ci in own do
    let dr ← findDeclarationRanges? ci.name
    if dr.isSome then ranged := ranged + 1
    let deps := ci.getUsedConstantsAsSet.toArray.filter fun d => table.contains d
    rows := rows.push (Json.mkObj [
      ("name", toJson ci.name.toString),
      ("kind", toJson (kindName ci)),
      ("needed", toJson (seen.contains ci.name)),
      ("dependencies", toJson (deps.map Name.toString)),
      ("range", dr.map rangeJson |>.getD Json.null)])
  let result := Json.mkObj [
    ("module", toJson target.toString),
    ("constantCount", toJson own.size),
    ("rangedCount", toJson ranged),
    ("neededCount", toJson seen.size),
    ("constants", Json.arr rows)]
  let output := (← IO.getEnv "PNP8323_DEPENDENCIES_OUT").getD "dependencies.json"
  IO.FS.writeFile output result.compress
  logInfo m!"Module constants: {own.size}; with ranges: {ranged}; final theorem closure: {seen.size}"
