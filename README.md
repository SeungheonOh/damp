# Damp

Midnight smart contracts written as ordinary Lean definitions, compiled to the
ZKIR circuits Midnight executes.

- [docs/language.md](docs/language.md): how to write a contract.
- [DESIGN.md](DESIGN.md): the research, the architecture, and what is and is
  not done.
- [docs/ledger-types.md](docs/ledger-types.md): every ledger operation and the
  on-chain instructions it becomes.
- [docs/tokens.md](docs/tokens.md): coins and tokens: the library, the kernel
  operations, the built-in witnesses, and how they match compactc.
- [docs/calls.md](docs/calls.md): cross-contract calls: contract types, the
  call's circuit, the executor's part, casting an address, the network trial.

## Layout

| Path | What |
|---|---|
| `Damp/Field.lean` | BLS12-381 scalar field |
| `Damp/Zkir.lean` | ZKIR v3 data type, JSON printer, single-assignment check |
| `Damp/Impact.lean` | Impact VM instructions and their public-input encoding |
| `Damp/IR.lean` | the circuit IR |
| `Damp/Contract.lean` | the interface contracts are written against: values, operators, statements |
| `Damp/Ledger.lean` | ledger types: `Cell`, `Counter`, `Map`, `Set`, `LedgerList`, Merkle trees, kernel operations (coins included) |
| `Damp/Tokens.lean` | Compact's coin and token library: minting, sending and receiving shielded and unshielded tokens |
| `Damp/Calls.lean` | cross-contract calls: contract types, the entry-point hash, the call |
| `Damp/Optimize.lean` | the optimizer and its soundness proof |
| `Damp/Disclosure.lean` | the check that private data is disclosed deliberately |
| `Damp/Syntax.lean` | notation: `circuit`, `witness`, `ledger`, `struct`, `enum`, `contract`, `const`, operators, `if` |
| `Damp/Build.lean` | writing output, key generation, command-line entry point |
| `Damp/Emit.lean` | IR to ZKIR |
| `Damp/ZkirSemantics.lean` | Midnight's ZKIR evaluator, ported to Lean |
| `Damp/Crypto/` | Poseidon, SHA-256 and the persistent hash, as Midnight computes them |
| `Damp/Semantics.lean` | what the IR means |
| `Damp/EmitCorrect.lean`, `OptimizeCorrect.lean`, `PruneCorrect.lean`, `Correct.lean` | the compiler's correctness proofs |
| `Damp/Executor.lean`, `ExecutorCorrect.lean`, `ExecutorComplete.lean` | what the executor must do; its calls are accepted; it fails only when it must |
| `Damp/OptimizeExecutor.lean` | optimizing does not change what the executor does |
| `Damp/LedgerAgreement.lean` | the public inputs are the instructions sent to the ledger |
| `Damp/InterfaceCorrect.lean` | the typed interface means what it says |
| `Damp/ZkirChecks.lean` | the obligations the ZKIR specification places on a producer |
| `Damp/Export.lean` | contract data for the executor |
| `Examples/` | example contracts, diagnostics, evaluator checks, a first theorem |
| `docs/bytes-lowering.md` | how Compact represents byte strings, with evidence |
| `executor/src/executor.mjs` | generic JS executor |
| `executor/bin/damp-package.mjs` | packages a built contract for midnight-js, with TypeScript declarations |
| `deploy/` | local Midnight network and scripts that deploy and call contracts on it |
| `executor/harness/` | ZKIR checker harness and runtime API notes |
| `test/oracle/*.compact` | Compact counterparts of the examples |

## A contract

```lean
import Damp
open Damp

struct Point where
  x : Field
  y : Uint8

ledger
  balances : Map Uint16 Field
  origin : Cell Point

witness pick : Point

circuit pay (k : Uint16) (amt : Field) : Field := do
  let has ← balances.member k
  const cur ← if% has then balances.lookup k else pure 0
  balances.insert k (cur + amt)
  return (← balances.size).toField

contract Example
```

`const x := e` computes a value once at that point, as Compact's `const` does.
`contract Example` gathers the ledger and every circuit declared in the
namespace.

To build, give the contracts a `main`:

```lean
def main (args : List String) : IO UInt32 := Damp.cli [contract] args
```

Running it writes `zkir/<circuit>.zkir` and `contract.json` per contract; with
`--keys` it also runs Midnight's `zkir-v3` for the prover and verifier keys.
Load `contract.json` with `makeContract` from the executor.

In the editor, `#zkir pay` prints a circuit's ZKIR and `#circuit_info pay`
summarises it. A circuit that cannot be compiled is reported on its name.

## From source to a deployed contract

```bash
lake exe damp-examples --keys build/out
```

```bash
node executor/bin/damp-package.mjs build/out/counter build/pkg/counter
```

The first command needs Midnight's `zkir-v3` on `PATH`. The second produces a
directory with `contract/index.js`, keys, ZKIR and a manifest, which
midnight-js loads like a contract compiled by compactc. `deploy/README.md`
shows the whole path against a local network.

## Build and test

```bash
lake build
```

| Script | Checks | Needs |
|---|---|---|
| `./test/golden.sh` | emitted ZKIR and contract data equal the checked-in copies | Lean only |
| `./test/all.sh` | verifier keys equal compactc's; executor equals compactc's module; ZKIR checker accepts | compactc, Node |
| `./test/semantics.sh` | the Lean ZKIR evaluator agrees with Midnight's real checker | compactc, Node |
| `./test/executor.sh` | the JavaScript executor does what its Lean definition says | compactc, Node |
| `./test/opt.sh` | optimized and unoptimized circuits agree; prints sizes | compactc's `zkir-v3`, Node |
| `deploy/scripts/all.sh` | deploys and calls contracts on a fresh local network | Docker, Node |

compactc 0.36.1 with its bundled `zkir-v3` is looked up under
`~/.compact/versions/0.36.1/` (set `COMPACT_HOME` otherwise). Run `npm install`
once in `executor/`. After an intended change to the compiler's output, run
`./test/golden.sh --update`.

Core Lean only; no Mathlib.
