import Examples.PruneSound
open Damp Damp.IR Damp.Zkir Examples.PruneSound

/-! Writes the circuits of `Examples/PruneSound.lean` for test/prune-sound.sh: for every case
and level (`--no-opt`, default, `--O2`, `--O3`) the ZKIR the build ships, and a *control*: the
same circuit emitted with the pruning used before `Emit.pruneDeadBinds` kept bindings that can
fail (every unused binding dropped). With each, the honest and the forged proof data, the
outputs computed with Damp's evaluator (forged: on the control, which accepts it), for
executor/test/prune-sound.mjs to hand to Midnight's checker; and the two contracts of
`Examples/PruneSound.lean` as the build writes them at each level, for the executor.

Usage: lake env lean --run test/PruneSound.lean OUT_DIR -/

/-- The emitter's pruning before the fix: every unused binding dropped. -/
def oldPrune (c : Circuit) : Circuit :=
  let step (s : Stmt) (acc : List Stmt × List Var) : List Stmt × List Var :=
    match s with
    | .bind v _ _ => if acc.2.contains v then (s :: acc.1, Emit.uses s ++ acc.2) else acc
    | _ => (s :: acc.1, Emit.uses s ++ acc.2)
  { c with body := (c.body.toList.foldr step ([], c.outputs.flatMap Expr.vars)).1.toArray }

structure PCase where
  name : String
  circ : Circuit
  honest : Option (List Int × List Int)
  forged : List Int × List Int

def cases : List PCase :=
  [⟨"ex1", ex1, some ([3], []), ([1000], [])⟩, ⟨"ex2", ex2, some ([3], []), ([1000], [])⟩,
   ⟨"ex3", ex3, some ([3], []), ([1000], [])⟩, ⟨"ex4", ex4, some ([3], []), ([1000], [])⟩,
   ⟨"ex5", ex5, some ([], [200]), ([], [1000])⟩, ⟨"ex6", ex6, some ([3], []), ([1000], [])⟩,
   ⟨"ex7", ex7, some ([3], [1]), ([1000], [1])⟩, ⟨"ex8", ex8, none, ([1000], [])⟩,
   ⟨"surface", f.circuit, some ([], [7]), ([], [1000])⟩]

def levelName : OptLevel → String
  | .none => "noopt" | .default => "default" | .full => "o2" | .max => "o3"

def ints (xs : List Int) : Lean.Json := .arr (xs.map fun x => Lean.toJson (toString x)).toArray
def frs (xs : List Fr) : Lean.Json := .arr (xs.map fun x => Lean.toJson (toString x.val)).toArray

/-- Outputs of an accepted run, with Damp's evaluator. -/
def outputsOf (src : IrSource) (inputs priv : List Int) : Option (List Fr) :=
  (src.run Crypto.prims (inputs.map Fr.ofInt) (priv.map Fr.ofInt) []).map (·.outputs)

/-- The public inputs of the instructions that ran, in an accepted run. -/
def activeOf (src : IrSource) (inputs priv : List Int) : Option (List Fr) :=
  (src.run Crypto.prims (inputs.map Fr.ofInt) (priv.map Fr.ofInt) []).map (·.activeInputs)

def main (args : List String) : IO UInt32 := do
  let out := System.FilePath.mk (args.headD "build/prune-sound")
  IO.FS.createDirAll out
  let mut rows : Array Lean.Json := #[]
  for cs in cases do
    for lvl in levels do
      let s := buildPassWith lvl false cs.circ
      let src ← IO.ofExcept (Emit.circuit s)
      let ctrl ← IO.ofExcept (Emit.circuitCore (oldPrune s))
      let zkir := out / s!"{cs.name}.{levelName lvl}.zkir"
      let czkir := out / s!"{cs.name}.{levelName lvl}.control.zkir"
      IO.FS.writeFile zkir (src.toJson.pretty ++ "\n")
      IO.FS.writeFile czkir (ctrl.toJson.pretty ++ "\n")
      let (fi, fp) := cs.forged
      let nOut := cs.circ.outputs.length
      -- Outputs claimed with the forged data: what the control computes, if it accepts.
      let fOut := (outputsOf ctrl fi fp).getD (List.replicate nOut 0)
      let honest := match cs.honest with
        | some (hi, hp) => Lean.Json.mkObj
            [("inputs", ints hi), ("priv", ints hp),
             ("outputs", match outputsOf src hi hp with | some o => frs o | none => .null),
             ("ptIn", frs ((activeOf src hi hp).getD []))]
        | none => .null
      rows := rows.push <| Lean.Json.mkObj
        [("case", cs.name), ("level", levelName lvl), ("zkir", s!"{cs.name}.{levelName lvl}.zkir"), ("control", s!"{cs.name}.{levelName lvl}.control.zkir"),
         ("honest", honest),
         ("forged", Lean.Json.mkObj [("inputs", ints fi), ("priv", ints fp), ("outputs", frs fOut),
           ("ptIn", frs ((activeOf ctrl fi fp).getD ((activeOf src fi fp).getD [])))]),
         ("controlAccepts", (outputsOf ctrl fi fp).isSome),
         ("leanAccepts", (outputsOf src fi fp).isSome)]
  IO.FS.writeFile (out / "cases.json") (Lean.Json.arr rows).pretty
  -- The two contracts, as the build ships them at each level, for the executor.
  for c in [Examples.PruneSound.contract, Examples.PruneSound.Hash.contract] do
    for lvl in levels do
      let m := c.optimize lvl false
      let srcs ← IO.ofExcept m.emitAll
      m.writeFiles (out / "contracts" / levelName lvl / c.name) srcs
  IO.println s!"wrote {rows.size} cases to {out}"
  return 0
