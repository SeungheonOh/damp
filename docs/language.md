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
- No `Uint` may exceed 2^248 − 1. A bound past it is reported when the circuit
  is checked, wherever the `Uint` comes from (`f.unsafeToUint max` included),
  and a ledger field whose type holds one is reported at the `ledger`
  declaration.

### Casts

Compact's `x as T`, as functions; a cast that checks its value is a `CircuitM`
action (`(← x.toBytes 4)`), and its check, like `toUint`'s, only applies where
the branch it is in runs.

| Compact | Damp | Emitted |
|---|---|---|
| `b as Field`, `b : Bytes<n>`, n ≤ 31 | `b.toField` | nothing |
| `x as Bytes<n>`, `x : Field` or `Uint`, n ≤ 31 | `x.toBytes n` | a check of `8n` bits |
| `x as Bytes<n>`, n ≥ 32 | `x.toBytes n` | one division by 2^248 |
| `b as Uint<..k>` | `b.toUint k` | a check, as `Field.toUint` |
| `b as Vector<n, Uint<8>>` | `b.toVector` | n − 1 divisions by 256 per 31 bytes |
| `v as Bytes<n>` | `Bytes.ofVector v` | `mul` and `add` per byte |
| `e as Field`, `e as Uint<..>` (enum) | `Enum.toField e`, `Enum.toUint e` | nothing |
| `x as E` (enum) | `x.toEnum E` | a check that `x` names a variant |
| `b as Uint<..>` (Boolean) | `b.toUint` (a `Uint 1`) | nothing |
| `x as Boolean` | `x.toBoolean` | `x != 0` |

These are compactc's instructions, less a `copy` compactc makes of a value it
checks; `Vector<n, Uint<8>> as Bytes<n>` uses a `mul` and an `add` per byte
where compactc uses one `reconstitute_field` (which costs more rows: it range
checks its operands again). `Bytes<n> as Field` for n ≥ 32 is not supported:
compactc checks that the value does not overflow the field, and the IR has no
expression for that check; the circuit is rejected with that message.
`Examples/Casts.lean` compares each cast with compactc's output.

A numeral is accepted wherever a `Uint` or `Field` is expected. One that does
not fit its `Uint` is reported when the circuit is checked. A `Field` numeral
(and `Field.ofNat`, `Field.ofString`) is reduced modulo the field size: with
`p` the modulus, `p + 1` is the field element `1`.

## Operators

Comparisons and boolean connectives on circuit values carry a trailing dot,
because Lean's own produce `Prop` or `Bool`:

`<.` `<=.` `>.` `>=.` `==.` `!=.` `&&.` `||.` `!.`

`==.` and `!=.` work on every circuit type. Ordering works on `Uint`.
`select c a b` picks between two values; so does `if c then a else b` on a
circuit `Boolean` (with `open Damp`), also in a plain `def`.

`==.` compares element by element, as compactc does: on a `Maybe` it compares
the flags and the payloads, so two absent values with different payloads are
different (`Maybe.none` always has the zero payload, so this only shows with a
`Maybe` built by hand or by a witness).

A comparison of a `Uint` with a literal past 2^248 − 1 (`x <. 2^250`) is
rejected when the circuit is checked, even where its answer is known: the
literal is itself a `Uint`, and no `Uint` may exceed the limit.

### Short-circuit evaluation

As in Compact, `a &&. b` and `a ||. b` evaluate `b` only when it is reached,
and a conditional evaluates only the branch taken: a witness call, ledger
operation or `require` in the part not reached does not happen, and the circuit
runs it under that guard, as compactc does.

```lean
-- Compact: assert(state == State.commit && private_state() == Private.initial, "x");
require ((← state.read) ==. State.commit &&. (← private_state) ==. Private.initial) "x"
```

`private_state` is called only when the state is `commit`. Precisely, inside a
`do` block (a circuit body, or any `do`), before Lean lifts the `(← …)`s of a
statement out of it:

| Written | Built as |
|---|---|
| `a &&. b`, `b` contains `(← …)` | `b` under the guard `a`; the result is `select a b false` (`Boolean.andThen`) |
| `a ||. b`, `b` contains `(← …)` | `b` under `!a`; the result is `select a true b` (`Boolean.orElse`) |
| `if c then x else y` (expression, `open Damp`), `x` or `y` contains `(← …)` | `x` under `c`, `y` under `!c`, results selected (`cond`); on a Lean `Bool` or `Prop`, only the branch taken runs |
| `select c x y`, `x` or `y` contains `(← …)` | the same as the `if` |
| `if% c then t else e`, a branch that is not a `do` block contains `(← …)` | the action runs inside its branch, under its guard |
| any of these without `(← …)` in the lazy part | unchanged: the operands are values, which have no effects (`a &&. b` is `Boolean.and a b`) |

The left operand and the condition are evaluated first, unconditionally. The
rewrite is syntactic: it sees a `(← …)` written in the operand. A value
computed earlier and passed in is just a value, so `const v ← w` followed by
`a &&. v ==. 0` calls `w` unconditionally, as the order of the statements says;
likewise any function's arguments, `Boolean.and a (← w)` included, are
evaluated before the call. `Boolean.andThen a (do …)`, `Boolean.orElse` and
`cond` can be called directly.

## Statements

| Form | Meaning |
|---|---|
| `const x := e` | compute `e` once, here, and call it `x` |
| `const x ← action` | the same for the result of an action |
| `const (a, b) := e`, `const ⟨a, b⟩ ← action` | the same for a tuple or structure, naming its parts (nested tuples and `⟨…⟩` of names and `_`) |
| `let x := e` | only a Lean name: `e` is computed where it is first used |
| `require c "message"` | fail the transaction unless `c` holds |
| `if% c then a else b` | both branches are built; effects are guarded by `c` |
| `if c then a else b` | the same when `c` is a circuit `Boolean`, as the last statement of a block; may assign `let mut` variables. As an expression whose type is a value (not `CircuitM _`) it is `select c a b`, lazy in its branches' actions (see "Short-circuit evaluation") |
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
| `interface T where …` | a contract type: another contract's circuits, callable through a `T` |
| `contract name` | the ledger, constructor, circuits and contract types declared in this namespace |

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
| `MerkleTree d α`, `HistoricMerkleTree d α` | `insert` and its variants, `checkRoot`, `isFull`, `resetToDefault`; paths below |

### Merkle tree paths

A circuit checks membership in a tree with a path it is given, as in Compact:
`MerkleTreePath n α` (fields `leaf : α` and `path : Vector MerkleTreePathEntry n`;
an entry has `sibling : MerkleTreeDigest` and `goesLeft : Boolean`) is an
ordinary value, so it can come from a witness, an argument or a `Cell`.
`merkleTreePathRoot p : CircuitM MerkleTreeDigest` computes the root it leads
to, hashing the leaf as `insert` does (`merkleTreePathRootNoLeafHash` for a
`MerkleTreePath n (Bytes 32)` whose leaf is already a hash); it emits what
compactc emits for the library circuit of the same name, except compactc's
`copy` of the leaf digest.

```lean
-- Compact: const path = disclose(context$path_of(pk));
--          assert(path.is_some && tree.checkRoot(disclose(merkleTreePathRoot<10, Bytes<32>>(path.value)))
--                 && pk == path.value.leaf, "not a member");
witness context_path_of (pk : Bytes 32) : Maybe (MerkleTreePath 10 (Bytes 32))
...
  const path := disclose (← context_path_of pk)
  require (path.isSome &&. (← tree.checkRoot (disclose (← merkleTreePathRoot path.value))) &&.
           pk ==. path.value.leaf) "not a member"
```

In JS a path is what compactc's `ledger(state).tree.findPathForLeaf(leaf)` returns:
`{ leaf, path: [{ sibling: { field }, goes_left }, …] }`.

A map's values may themselves be ledger types; `(← m.lookup k)` then gives a
handle to operate on. Kernel operations: `Kernel.self`, `Kernel.checkpoint`,
and the block-time checks. `docs/ledger-types.md` has the full list.

## Coins and tokens

`Damp/Lang/Tokens.lean` (part of `import Damp`) has Compact's token library under
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

## Calling other contracts

A contract type (Compact's `contract Adder { … }`) lists the circuits another
contract must export, with their types. A value of that type is the address of
such a contract; its circuits are methods on it.

```lean
interface Adder where
  addTo (x : Field) : Field
  clear : Unit

ledger
  adder : Cell Adder
  last : Cell Field

constructor (a : Adder) := adder.write (disclose a)

circuit bump (x : Field) : Field := do
  const r ← (← adder.read).addTo (disclose x)
  last.write r          -- a call's result is public: no `disclose`
  return r

circuit via (a : Adder) (x : Field) : Field := (disclose a).addTo (disclose x)
```

| Form | Meaning |
|---|---|
| `interface T where` + `f (a : A) … : R` lines | a contract type; `f : R` for a circuit with no arguments |
| `T` | a reference to a contract of that type, 32 bytes (`{ bytes }` in JS); usable as an argument, a constructor argument, ledger content, and with `==.` |
| `t.f a …` | call circuit `f` of the contract `t`: `CircuitM R` |

`contract` records the contract types declared in its namespace (or an
enclosing one) in `contract.json`; the executor needs them to run a call. As in
Compact, the arguments of a call, and the reference when it comes from an
argument or witness, need `disclose`, and so does a condition the call is made
under; the results do not. The called circuit runs on the user's machine with
the callee's own code: give midnight-js (or the runtime's circuit context) a
`moduleProvider` that maps the callee's address to its module, compactc's
`contract/index.js` or a Damp package. The callee may not use witnesses. See
[calls.md](calls.md).

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
| `--O2` | every optimization pass; a circuit may come out smaller than compactc's, with a different verifier key |

Each contract is written as `zkir/<circuit>.zkir` plus `contract.json`, which
the executor loads with `makeContract`.

## Proving things

A circuit is a Lean value, `f.circuit : IR.Circuit`, and `IR.Circuit.run`
gives it meaning: inputs, private transcript and public reads in; outputs and
public inputs out, or `none` if the run is rejected. `Damp/Proofs/Compiler.lean`
proves that the ZKIR the compiler ships evaluates, under a Lean port of
Midnight's evaluator, to that same meaning. So a theorem about
`f.circuit.run` is a theorem about what the shipped circuit accepts.
`Examples/Semantics.lean` has a small one.
