/-
Building contracts: writing the compiler's output, and running Midnight's
`zkir` tool on it for the prover and verifier keys.
-/
import Damp.Compile.Export
import Damp.Optimize.Pipeline
import Damp.IR.LedgerCheck

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

/-- An optimization level: `--no-opt`, the default, `--O2`, `--O3`. -/
inductive OptLevel where
  | none
  | default
  | full
  | max
  deriving DecidableEq, Repr, Inhabited

/-- The pass a level applies to every circuit. -/
def OptLevel.pass : OptLevel → IR.Pass
  | .none => fun c => c
  | .default => IR.Circuit.optimize
  | .full => IR.Circuit.optimizeFull
  | .max => IR.Circuit.optimizeMax

/-- The pass the flags select (`--no-opt`: none; default; `--O2`; `--O3`). -/
def buildPass (level : OptLevel) : IR.Pass := level.pass

/-- The contract with every circuit optimized at `level`. The emitter and the
    executor both read the result, so they keep agreeing. -/
def Contract.optimize (c : Contract) (level : OptLevel := .default) : Contract :=
  { c with circuits := c.circuits.map level.pass, constructor := c.constructor.map level.pass }

/-- Everything `Contract.build` computes, without the file system and without
    key generation: the disclosure check on every circuit, the optimization
    the flags select, the ledger check on every shipped circuit, then
    `Contract.emitAll` on the shipped contract (`Contract.check`, and
    `Emit.circuit` on every shipped circuit). Returns the shipped contract
    (what goes to `contract.json`) and each shipped circuit with its emitted
    ZKIR (what goes to `zkir/`). `Damp/Proofs/Build.lean` proves what its
    success guarantees (`build_correct`). -/
def Contract.buildCore (c : Contract) (level : OptLevel := .default) :
    Except String (Contract × List (IR.Circuit × Zkir.IrSource)) := do
  for circ in c.circuits ++ c.constructor.toList do
    if let .error e := circ.checkDisclosure then
      throw s!"{c.name}.{circ.name}: {e}"
  let shipped := c.optimize level
  -- What is sent to the ledger must be what the circuit declares; this is
  -- checked on the circuits that are actually emitted and executed.
  for circ in shipped.circuits ++ shipped.constructor.toList do
    if let .error e := circ.checkLedger then
      throw s!"{c.name}: {e}"
  let srcs ← shipped.emitAll
  pure (shipped, srcs)

/-- Write the contract under `dir`: run `Contract.buildCore` and write the
    files it returns (`Contract.writeFiles`). With `zkir`, also generate
    `keys/` by running that program (Midnight's `zkir-v3`) on the emitted
    circuits. -/
def Contract.build (c : Contract) (dir : System.FilePath) (zkir : Option String := none)
    (level : OptLevel := .default) : IO Unit := do
  let (shipped, srcs) ← IO.ofExcept (c.buildCore level)
  shipped.writeFiles dir srcs
  if let some tool := zkir then
    IO.FS.createDirAll (dir / "keys")
    let out ← IO.Process.output
      { cmd := tool, args := #["compile-many", (dir / "zkir").toString, (dir / "keys").toString] }
    unless out.exitCode == 0 do
      throw (IO.userError s!"{tool} failed for {c.name}:\n{out.stderr}")

private def usage : String :=
  "usage: [--keys] [--zkir PROGRAM] [--no-opt | --O2 | --O3] [OUT_DIR]\n\
   Writes each contract to OUT_DIR/<name>/ (default build/out).\n\
   --keys          also generate prover and verifier keys\n\
   --no-opt        emit circuits as written, without optimizing\n\
   --O2            every optimization pass; a circuit may then be smaller than compactc's\n\
   --O3            --O2, and hashes of constants computed at compile time (sound relative\n\
                   to Damp's implementations of Midnight's hash functions)\n\
   --zkir PROGRAM  the zkir tool to use for --keys (default: zkir-v3 on PATH)"

/-- A command-line entry point for a set of contracts:
    `def main := Damp.cli [MyContract.contract]`. -/
def cli (contracts : List Contract) (args : List String) : IO UInt32 := do
  let rec parse (args : List String) (keys : Bool) (level : OptLevel) (tool : String) (out : String) :
      Except String (Bool × OptLevel × String × String) :=
    match args with
    | [] => pure (keys, level, tool, out)
    | "--keys" :: rest => parse rest true level tool out
    | "--no-opt" :: rest => parse rest keys .none tool out
    | "--O2" :: rest => parse rest keys .full tool out
    | "--O3" :: rest => parse rest keys .max tool out
    | "--zkir" :: t :: rest => parse rest true level t out
    | a :: rest =>
        if a.startsWith "-" then throw s!"unknown option {a}" else parse rest keys level tool a
  match parse args false .default "zkir-v3" "build/out" with
  | .error e =>
      IO.eprintln s!"{e}\n{usage}"
      return 2
  | .ok (keys, level, tool, out) =>
      for c in contracts do
        try
          c.build (System.FilePath.mk out / c.name) (if keys then some tool else none) level
          IO.println s!"{c.name}: {c.circuits.length} circuit(s) written to {out}/{c.name}"
        catch e =>
          IO.eprintln s!"{c.name}: {e}"
          return 1
      return 0

end Damp
