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
| `Damp/Zkir/` | Midnight's circuit format: the data type and JSON (`Basic`, `Json`), the producer's obligations (`Checks`), and Midnight's evaluator ported to Lean (`Semantics`) |
| `Damp/Crypto/` | Poseidon, SHA-256 and the persistent hash, as Midnight computes them |
| `Damp/IR/` | the circuit IR (`Basic`), what it means (`Semantics`), Impact VM instructions and their encoding (`Impact`), the disclosure check (`Disclosure`), the ledger-statement check (`LedgerCheck`) |
| `Damp/Optimize/` | optimization passes, one per file (`Simplify`, `Bounds`, `Bounds2`, `Algebra`, `Asserts`, `Forward`, `InlineAll`, `AssertEq`, `Commute`, `FoldHashes`; `Choose` keeps the better of two results), put in order by `Pipeline` at three levels: default, `--O2`, `--O3` |
| `Damp/Compile/` | IR to ZKIR (`Emit`), contract data for the executor (`Export`), the build as a pure function (`Contract.buildCore`), output, key generation and the command line (`Build`) |
| `Damp/Executor/` | what the executor must do (`Spec`) |
| `Damp/Ledger/` | a Lean model of Midnight's on-chain (Impact) VM, differentially tested against the real runtime (`Vm`, `Query`, `Merkle`) |
| `Damp/Lang/` | what contracts are written in: values, operators and statements (`Contract`), ledger types and kernel operations (`Ledger`), cross-contract calls (`Calls`), the token library (`Tokens`), notation (`Syntax`) |
| `Damp/Proofs/` | every theorem: the emitter (`Emit`, `Prune`), the optimizer (`Optimize/`: one file per pass, `Sound` for what a sound pass is, `Pipeline` for the whole), the compiler end to end (`Compiler`), the executor (`Executor`, `ExecutorComplete`, `LedgerAgreement`), the typed interface (`Interface`, `Interface/`), what a successful build guarantees (`Build`), the optimizer keeping ledger statements well formed (`Optimize/LedgerCheck`), the ZKIR JSON reading back (`ZkirJson`), noninterference of the disclosure check (`Disclosure`), the ledger operations against the VM model (`Ledger/`), field lemmas (`Field`) |
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
| `./test/vm.sh` | the Lean model of the ledger VM agrees with Midnight's runtime | Node |
| `./test/opt.sh` | optimized and unoptimized circuits agree; prints sizes | compactc's `zkir-v3`, Node |
| `deploy/scripts/all.sh` | deploys and calls contracts on a fresh local network | Docker, Node |

compactc 0.36.1 with its bundled `zkir-v3` is looked up under
`~/.compact/versions/0.36.1/` (set `COMPACT_HOME` otherwise). Run `npm install`
once in `executor/`. After an intended change to the compiler's output, run
`./test/golden.sh --update`.

Core Lean only; no Mathlib.
