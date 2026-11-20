/-
Damp's reading of each `.zkir` file under the given directories, for
test/loader.py: one line `<path>\t<json>` per file, where <json> is the circuit
`Zkir.IrSource.parse` returned, printed back with `IrSource.toJson` (which Damp
reads as the same circuit, `IrSource.ofJson_toJson`), or `<path>\tFAIL <error>`.

usage: lake env lean --run test/LoaderDump.lean DIR...
-/
import Damp.Zkir.Json

open Damp.Zkir

partial def files (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let mut out := #[]
    for e in ← p.readDir do
      out := out ++ (← files e.path)
    return out
  else if p.extension == some "zkir" then return #[p]
  else return #[]

def main (args : List String) : IO UInt32 := do
  for d in args do
    for p in (← files d).qsort (·.toString < ·.toString) do
      match IrSource.parse (← IO.FS.readFile p) with
      | .ok s => IO.println s!"{p}\t{s.toJson.compress}"
      | .error e => IO.println s!"{p}\tFAIL {e}"
  return 0
