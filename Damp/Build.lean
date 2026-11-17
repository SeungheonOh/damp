/-
Building contracts: writing the compiler's output, and running Midnight's
`zkir` tool on it for the prover and verifier keys.
-/
import Damp.Export
import Damp.Optimize
import Damp.LedgerAgreement

namespace Damp

/-- Why a circuit cannot be shipped, if it cannot: it does not compile, leaks
    private data, or has a ledger statement whose public inputs would not be
    the instructions sent to the ledger. Checked where a circuit is declared. -/
def circuitProblem (c : IR.Circuit) : Option String :=
  match Emit.problem c with
  | some e => some e
  | none =>
      match c.optimize.checkLedger with
      | .error e => some e
      | .ok _ => none

/-- The contract with every circuit optimized. The emitter and the executor
    both read the result, so they keep agreeing. -/
def Contract.optimize (c : Contract) : Contract :=
  { c with circuits := c.circuits.map IR.Circuit.optimize,
           constructor := c.constructor.map IR.Circuit.optimize }

/-- Write the contract under `dir`. With `zkir`, also generate `keys/` by
    running that program (Midnight's `zkir-v3`) on the emitted circuits. -/
def Contract.build (c : Contract) (dir : System.FilePath) (zkir : Option String := none)
    (optimize : Bool := true) : IO Unit := do
  for circ in c.circuits ++ c.constructor.toList do
    if let .error e := circ.checkDisclosure then
      throw (IO.userError s!"{c.name}.{circ.name}: {e}")
  let shipped := if optimize then c.optimize else c
  -- What is sent to the ledger must be what the circuit declares; this is
  -- checked on the circuits that are actually emitted and executed.
  for circ in shipped.circuits ++ shipped.constructor.toList do
    if let .error e := circ.checkLedger then
      throw (IO.userError s!"{c.name}: {e}")
  shipped.write dir
  if let some tool := zkir then
    IO.FS.createDirAll (dir / "keys")
    let out ← IO.Process.output
      { cmd := tool, args := #["compile-many", (dir / "zkir").toString, (dir / "keys").toString] }
    unless out.exitCode == 0 do
      throw (IO.userError s!"{tool} failed for {c.name}:\n{out.stderr}")

private def usage : String :=
  "usage: [--keys] [--zkir PROGRAM] [--no-opt] [OUT_DIR]\n\
   Writes each contract to OUT_DIR/<name>/ (default build/out).\n\
   --keys          also generate prover and verifier keys\n\
   --no-opt        emit circuits as written, without optimizing\n\
   --zkir PROGRAM  the zkir tool to use for --keys (default: zkir-v3 on PATH)"

/-- A command-line entry point for a set of contracts:
    `def main := Damp.cli [MyContract.contract]`. -/
def cli (contracts : List Contract) (args : List String) : IO UInt32 := do
  let rec parse (args : List String) (keys opt : Bool) (tool : String) (out : String) :
      Except String (Bool × Bool × String × String) :=
    match args with
    | [] => pure (keys, opt, tool, out)
    | "--keys" :: rest => parse rest true opt tool out
    | "--no-opt" :: rest => parse rest keys false tool out
    | "--zkir" :: t :: rest => parse rest true opt t out
    | a :: rest =>
        if a.startsWith "-" then throw s!"unknown option {a}" else parse rest keys opt tool a
  match parse args false true "zkir-v3" "build/out" with
  | .error e =>
      IO.eprintln s!"{e}\n{usage}"
      return 2
  | .ok (keys, opt, tool, out) =>
      for c in contracts do
        try
          c.build (System.FilePath.mk out / c.name) (if keys then some tool else none) opt
          IO.println s!"{c.name}: {c.circuits.length} circuit(s) written to {out}/{c.name}"
        catch e =>
          IO.eprintln s!"{c.name}: {e}"
          return 1
      return 0

end Damp
