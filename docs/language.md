# Writing contracts in Damp

A Damp contract is a Lean file. Circuits are ordinary Lean definitions; the
notation below is a thin layer of macros over plain functions.

```lean
import Damp
open Damp

ledger
  owner : Cell (Bytes 32)
  spent : Counter

witness key : Bytes 32

constructor (o : Bytes 32) := do
  owner.write (disclose o)

circuit spend (amount : Uint16) : Unit := do
  const h := disclose (persistentHash (← key))
  require (h ==. (← owner.read)) "not owner"
  spent.increment (disclose amount)

contract vault
```

## Two levels

Everything in a circuit is one of two things.

- **Circuit values** exist when the contract runs: `Field`, `Boolean`,
  `Uint max`, `Bytes n`, enumerations, and structures, tuples, vectors and
  `Maybe` of those.
- **Everything else is Lean**, evaluated while the circuit is built: `Nat`,
  `List`, functions, recursion, `for` loops, type classes, plain `if` on a Lean
  condition. None of it appears in the circuit.

So a loop is a Lean loop over a bound known at compile time, a generic helper
is a Lean function, and a configuration value is a Lean constant.

## Types

| Type | Notes |
|---|---|
| `Field` | an element of the proof system's field; `+ - *` wrap |
| `Boolean` | `Boolean.true`, `Boolean.false`, `Boolean.ofBool b` |
| `Uint max` | unsigned, at most `max`. `Uint8`, `Uint16`, `Uint32`, `Uint64` are abbreviations |
| `Bytes n` | `Bytes.pad n "text"`, `Bytes.ofBytes n [..]`, `Bytes.zero n` |
| `Maybe α` | `Maybe.some x`, `Maybe.none`; fields `isSome`, `value` |
| `Vector α n` | Lean's `Vector`; index with `v[i]` |
| `α × β` | tuples |
| `struct S where …` | named fields |
| `enum E where \| a \| b` | variants `E.a`, `E.b` |

`Uint` arithmetic follows Compact:

- `a + b` and `a * b` widen the bound in the type, so they cannot overflow.
- `a.sub b` fails the transaction if `b > a`.
- `a.widen` forgets precision for free; `a.castTo k` narrows with a check.
- `a.toField` leaves the `Uint` rules; `f.toUint max` returns with a check and
  `f.unsafeToUint max` without one.
- No `Uint` may exceed 2^248 − 1.

A numeral is accepted wherever a `Uint` or `Field` is expected. One that does
not fit its `Uint` is reported when the circuit is checked.

## Operators

Comparisons and boolean connectives on circuit values carry a trailing dot,
because Lean's own produce `Prop` or `Bool`:

`<.` `<=.` `>.` `>=.` `==.` `!=.` `&&.` `||.` `!.`

`==.` and `!=.` work on every circuit type. Ordering works on `Uint`.
`select c a b` picks between two values.

## Statements

| Form | Meaning |
|---|---|
| `const x := e` | compute `e` once, here, and call it `x` |
| `const x ← action` | the same for the result of an action |
| `let x := e` | only a Lean name: `e` is computed where it is first used |
| `require c "message"` | fail the transaction unless `c` holds |
| `if% c then a else b` | both branches are built; effects are guarded by `c` |
| `if c then a else b` | the same when `c` is a circuit `Boolean`, as an expression or as the last statement of a block; may assign `let mut` variables |
| `for i in [0:n] do …` | a Lean loop, unrolled |

A circuit `if` always builds both branches. Use `if%` when statements follow
the conditional: Lean's `do` notation would otherwise copy them into both
branches, and the compiler rejects that when it would repeat an effect.
`break` under a circuit condition is rejected for the same reason.

## Declarations

| Form | Meaning |
|---|---|
| `ledger` + `name : Type` lines | the contract's public state |
| `witness w (a : A) : R` | a private input supplied by the user's machine |
| `constructor (a : A) := do …` | runs once at deployment |
| `circuit f (a : A) : R := do …` | an entry point; also a plain function `f` |
| `contract name` | the ledger, constructor and circuits declared in this namespace |

A helper that is not an entry point is a plain `def` returning `CircuitM R`.
A circuit that never touches the ledger needs no proof and gets no ZKIR; it
runs on the user's machine only.

## Ledger types

| Type | Operations |
|---|---|
| `Cell α` | `read`, `write`, `resetToDefault` |
| `Counter` | `increment`, `decrement`, `read`, `lessThan`, `resetToDefault` |
| `Map κ ν` | `member`, `lookup`, `insert`, `insertDefault`, `remove`, `size`, `isEmpty`, `resetToDefault` |
| `Set α` | `member`, `insert`, `remove`, `size`, `isEmpty`, `resetToDefault` |
| `LedgerList α` | `pushFront`, `popFront`, `head`, `length`, `isEmpty`, `resetToDefault` |
| `MerkleTree d α`, `HistoricMerkleTree d α` | `insert` and its variants, `checkRoot`, `isFull`, `resetToDefault` |

A map's values may themselves be ledger types; `(← m.lookup k)` then gives a
handle to operate on. Kernel operations: `Kernel.self`, `Kernel.checkpoint`,
and the block-time checks. `docs/ledger-types.md` has the full list.

## Coins and tokens

`Damp/Tokens.lean` (part of `import Damp`) has Compact's token library under
the same names: `mintShieldedToken`, `receiveShielded`, `sendShielded`,
`sendImmediateShielded`, `mergeCoin`, `mergeCoinImmediate`, `evolveNonce`,
`tokenType`, `nativeToken`, `shieldedBurnAddress`, `mintUnshieldedToken`,
`sendUnshielded`, `receiveUnshielded`, `unshieldedBalance` and its
comparisons, the types `ShieldedCoinInfo`, `QualifiedShieldedCoinInfo`,
`ZswapCoinPublicKey`, `UserAddress`, `Either` (`left x`, `right y`), and
`ownPublicKey`. A coin the contract receives is stored, qualified with its
Merkle-tree index (looked up by the ledger), with `Cell.writeCoin`,
`Map.insertCoin`, `Set.insertCoin` or `LedgerList.pushFrontCoin` on a field of
`QualifiedShieldedCoinInfo`; the stored coin is what `sendShielded` and
`mergeCoin` spend. The kernel operations under them are in `Kernel`
(`Kernel.mintShielded`, `Kernel.claimZswapCoinSpend`, `Kernel.balance`, …).
`ownPublicKey`, `createZswapInput` and `createZswapOutput` are built-in
witnesses: the executor runs them; a contract does not declare or supply
them. Coins, values, nonces and recipients from arguments or witnesses need
`disclose` where Compact needs it. See [tokens.md](tokens.md).

```lean
circuit mint (amount : Uint64) (n : Bytes 32) (to : ZswapCoinPublicKey) : Unit := do
  last.write (← mintShieldedToken (Bytes.pad 32 "damp:token") (disclose amount) (disclose n)
    (left (disclose to)))
```

## Hashes and commitments

| Function | Result |
|---|---|
| `transientHash x` | `Field` |
| `transientCommit x r` | `Field`, with opening `r : Field` |
| `persistentHash x` | `Bytes 32` |
| `persistentCommit x r` | `Bytes 32`, with opening `r : Bytes 32` |

## Disclosure

Circuit arguments and witness results are private. Before one of them can be
stored in the ledger, decide whether a ledger operation happens, or (for
witness results) be returned, it must pass through `disclose`:

```lean
total.write (disclose (x + secret))
if% disclose on then hits.increment 1
```

Hashing a private value does not make it public; committing to it does. Values
read from the ledger are public already. The check is there to stop accidental
leaks: it does not change the circuit.

## Tooling

In the editor:

- A circuit that cannot be compiled is reported on its name: a leak, an
  oversized literal, an `if` that would repeat an effect.
- `#zkir f` prints the circuit emitted for `f`; `#circuit_info f` summarises it.

From the command line, give the contracts a `main`:

```lean
def main (args : List String) : IO UInt32 := Damp.cli [contract] args
```

| Option | Effect |
|---|---|
| `OUT_DIR` | where to write; default `build/out` |
| `--keys` | also generate prover and verifier keys with Midnight's `zkir-v3` |
| `--zkir PROGRAM` | the `zkir` tool to use |
| `--no-opt` | emit circuits as written |

Each contract is written as `zkir/<circuit>.zkir` plus `contract.json`, which
the executor loads with `makeContract`.

## Proving things

A circuit is a Lean value, `f.circuit : IR.Circuit`, and `IR.Circuit.run`
gives it meaning: inputs, private transcript and public reads in; outputs and
public inputs out, or `none` if the run is rejected. `Damp/Correct.lean`
proves that the ZKIR the compiler ships evaluates, under a Lean port of
Midnight's evaluator, to that same meaning. So a theorem about
`f.circuit.run` is a theorem about what the shipped circuit accepts.
`Examples/Semantics.lean` has a small one.
