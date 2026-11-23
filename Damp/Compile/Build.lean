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

/-- The pass the flags select: the level's (`--no-opt`: none; default;
    `--O2`; `--O3`), then, with `--ledger-opt` (`ledgerOpt`), the ledger
    passes (`IR.ledgerPasses`). -/
def buildPassWith (level : OptLevel) (ledgerOpt : Bool) : IR.Pass :=
  match ledgerOpt with
  | false => level.pass
  | true => fun c => IR.runPasses IR.ledgerPasses (level.pass c)

/-- The pass the level selects, without `--ledger-opt`. -/
def buildPass (level : OptLevel) : IR.Pass := buildPassWith level false

/-- The contract with every circuit optimized at `level` (and, with
    `ledgerOpt`, by the ledger passes). The emitter and the executor both read
    the result, so they keep agreeing. -/
def Contract.optimize (c : Contract) (level : OptLevel := .default) (ledgerOpt : Bool := false) : Contract :=
  { c with circuits := c.circuits.map (buildPassWith level ledgerOpt),
           constructor := c.constructor.map (buildPassWith level ledgerOpt) }

/-- Everything `Contract.build` computes, without the file system and without
    key generation: the disclosure check on every circuit, the optimization
    the flags select, the ledger check on every shipped circuit, then
    `Contract.emitAll` on the shipped contract (`Contract.check`, and
    `Emit.circuit` on every shipped circuit). Returns the shipped contract
    (what goes to `contract.json`) and each shipped circuit with its emitted
    ZKIR (what goes to `zkir/`). `Damp/Proofs/Build.lean` proves what its
    success guarantees (`build_correct`). -/
def Contract.buildCore (c : Contract) (level : OptLevel := .default) (ledgerOpt : Bool := false) :
    Except String (Contract × List (IR.Circuit × Zkir.IrSource)) := do
  for circ in c.circuits ++ c.constructor.toList do
    if let .error e := circ.checkDisclosure then
      throw s!"{c.name}.{circ.name}: {e}"
  let shipped := c.optimize level ledgerOpt
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
    (level : OptLevel := .default) (ledgerOpt : Bool := false) : IO Unit := do
  let (shipped, srcs) ← IO.ofExcept (c.buildCore level ledgerOpt)
  shipped.writeFiles dir srcs
  if let some tool := zkir then
    IO.FS.createDirAll (dir / "keys")
    let out ← IO.Process.output
      { cmd := tool, args := #["compile-many", (dir / "zkir").toString, (dir / "keys").toString] }
    unless out.exitCode == 0 do
      throw (IO.userError s!"{tool} failed for {c.name}:\n{out.stderr}")

private def usage : String :=
  "usage: [--keys] [--zkir PROGRAM] [--no-opt | --O2 | --O3] [--ledger-opt] [OUT_DIR]\n\
   Writes each contract to OUT_DIR/<name>/ (default build/out).\n\
   --keys          also generate prover and verifier keys\n\
   --no-opt        emit circuits as written, without optimizing\n\
   --O2            every optimization pass; a circuit may then be smaller than compactc's\n\
   --O3            --O2, and hashes of constants computed at compile time (sound relative\n\
                   to Damp's implementations of Midnight's hash functions)\n\
   --ledger-opt    after the level's passes, also rewrite ledger reads and writes (reuse a\n\
                   value read or written, drop an overwritten write); proved only against\n\
                   the Lean model of Midnight's ledger, and the circuit's public transcript\n\
                   and verifier key change; not with --no-opt\n\
   --zkir PROGRAM  the zkir tool to use for --keys (default: zkir-v3 on PATH)"

/-- The options `cli` reads: keys, level, `--ledger-opt`, key tool, output directory. -/
structure CliOpts where
  keys : Bool := false
  level : OptLevel := .default
  ledgerOpt : Bool := false
  tool : String := "zkir-v3"
  out : String := "build/out"

/-- Parse `cli`'s arguments. `--ledger-opt` runs after the level's passes, so
    it is refused with `--no-opt`, which runs none. -/
def parseCli (args : List String) : Except String CliOpts := do
  let rec go (args : List String) (o : CliOpts) : Except String CliOpts :=
    match args with
    | [] => pure o
    | "--keys" :: rest => go rest { o with keys := true }
    | "--no-opt" :: rest => go rest { o with level := .none }
    | "--O2" :: rest => go rest { o with level := .full }
    | "--O3" :: rest => go rest { o with level := .max }
    | "--ledger-opt" :: rest => go rest { o with ledgerOpt := true }
    | "--zkir" :: t :: rest => go rest { o with keys := true, tool := t }
    | a :: rest =>
        if a.startsWith "-" then throw s!"unknown option {a}" else go rest { o with out := a }
  let o ← go args {}
  if o.ledgerOpt && o.level == .none then
    throw "--ledger-opt runs after an optimization level's passes and cannot be used with --no-opt \
      (use it with the default level, --O2 or --O3)"
  pure o

#guard (match parseCli ["--no-opt", "--ledger-opt"] with | .error _ => true | .ok _ => false)
#guard (match parseCli ["--ledger-opt", "--no-opt"] with | .error _ => true | .ok _ => false)
#guard (match parseCli ["--O2", "--ledger-opt", "out"] with
  | .ok o => o.level == .full && o.ledgerOpt && o.out == "out" | .error _ => false)
#guard (match parseCli ["--ledger-opt"] with | .ok o => o.level == .default && o.ledgerOpt | .error _ => false)
#guard (match parseCli ["--O3", "--ledger-opt"] with | .ok o => o.level == .max && o.ledgerOpt | .error _ => false)
#guard (match parseCli ["--O2"] with | .ok o => !o.ledgerOpt | .error _ => false)

/-- A command-line entry point for a set of contracts:
    `def main := Damp.cli [MyContract.contract]`. -/
def cli (contracts : List Contract) (args : List String) : IO UInt32 := do
  match parseCli args with
  | .error e =>
      IO.eprintln s!"{e}\n{usage}"
      return 2
  | .ok o =>
      for c in contracts do
        try
          c.build (System.FilePath.mk o.out / c.name) (if o.keys then some o.tool else none) o.level o.ledgerOpt
          IO.println s!"{c.name}: {c.circuits.length} circuit(s) written to {o.out}/{c.name}"
        catch e =>
          IO.eprintln s!"{c.name}: {e}"
          return 1
      return 0

end Damp
