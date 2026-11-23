import Test.Vm
open Lean (Json)
open Damp Damp.Ledger Damp.VmTest

/-! Audit (docs/audit.md, hypothesis `σ.WF` of `Pass.SoundLedger`): is it satisfied by the states the
real runtime actually produces? `σ.WF` is `decodeEffects σ.effects = some σ.effects`. Every vector of
test/vm.sh records the real VM's starting stack (context, effects, state) and, for a successful
query, the effects it left. Both must be well formed for the ledger-pass theorems to say anything
about real calls (the states mid-call are the effects a query leaves). Reads $AUDIT_VM_VECTORS
(default build/vm-ledger/vectors/vectors.json). -/

def wf (v : SV) : Bool := match decodeEffects v with
  | some v' => canon v' == canon v
  | none => false

#eval show IO Unit from do
  let file := (← IO.getEnv "AUDIT_VM_VECTORS").getD "build/vm-ledger/vectors/vectors.json"
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let values := (← IO.ofExcept (do (← arr j "values").mapM svOf)).toArray
  let vecs ← IO.ofExcept (arr j "vectors")
  let mut start := 0
  let mut startBad := 0
  let mut after := 0
  let mut afterBad := 0
  let mut examples : List String := []
  for vj in vecs do
    let v ← IO.ofExcept (vecOf values vj)
    if let [_, (eff, _), _] := v.init then
      start := start + 1
      unless wf eff do
        startBad := startBad + 1
        if examples.length < 3 then examples := examples ++ [s!"start of vector {v.id} [{v.group}]: {canon eff |>.take 200}"]
    if (v.query.getObjValAs? Bool "ok").toOption == some true then
      if let .ok i := v.query.getObjValAs? Nat "effects" then
        after := after + 1
        unless wf values[i]! do
          afterBad := afterBad + 1
          if examples.length < 6 then examples := examples ++ [s!"after vector {v.id} [{v.group}]: {canon values[i]! |>.take 200}"]
  IO.println s!"WF: starting effects {start - startBad} of {start} well formed; effects after a successful query {after - afterBad} of {after}"
  for e in examples do IO.println s!"  not WF: {e}"
  if startBad + afterBad > 0 then throw (IO.userError "some real states are not WF")
