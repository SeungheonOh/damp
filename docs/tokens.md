# Coins and tokens

How Damp supports what a contract needs to hold and move value: Compact's
standard-library token types and functions (`Damp/Tokens.lean`), the kernel
operations under them (`Damp/Ledger.lean`, namespace `Kernel`), the
coin-storing ledger operations (`writeCoin`, `insertCoin`, `pushFrontCoin`,
also in `Damp/Tokens.lean`), two new Impact instruction forms
(`Damp/Impact.lean`), and the three built-in witnesses, which the executor
implements itself (`executor/src/executor.mjs`).

Every instruction encoding and sequence below was observed in compactc 0.36.1
output (`compactc.bin --skip-zk`, the `.zkir` files and the generated
`contract/index.js`) for `test/oracle/tokens.compact` and for small variants of
it. `compiler/standard-library.compact`, `compiler/midnight-ledger.ss` and
`compiler/midnight-natives.ss` of the 0.33 source and
`runtime/src/zswap.ts` (here: the installed `@midnight-ntwrk/compact-runtime`
0.21.0, `dist/zswap.js`) were read for intent only.

The regression evidence is `test/oracle/tokens.compact` and its Lean
counterpart `Examples/Tokens.lean`: 28 circuits, 19 with byte-identical
verifier keys and 9 whose difference is fully accounted for (see "Differences
from compactc"); 53 calls in `executor/test/calls.mjs` (9 of which must fail,
and both executors fail) with identical proof data, results, Zswap local
state after the call and final ledger state against compactc's module, each
completed call accepted by the ZKIR checker against the Damp circuit; and the
same calls replayed through the Lean definition of the executor
(`test/executor.sh`), all agreeing.

Notation as in `docs/ledger-types.md`: `impact` lines as their field elements,
hex as compactc prints them; `%x` a register; `{n: v}` a cell of `n` bytes.

## New instructions

The kernel's counting operations look up a map entry whose key was pushed
earlier, i.e. an `idx` whose last key is taken from the stack; the
coin-storing operations look up `[{1:1}, stack]` in the context (literal key,
then a stack key) and join two cells with a *cached* `concat`:

| Instruction | Encoding | Runtime op (compactc's `index.js`) | Seen in |
|---|---|---|---|
| `idxStack pre` | `0x60 + |pre|`, the keys of `pre`, `-0x01` | `{ idx: { cached: true, pushPath: false, path: [...pre as {tag:'value'}, { tag: 'stack' }] } }` | `0x60 -0x01` (mints, inc*, unshielded spend); `0x61 0x01 0x01 0x01 -0x01` (`writeCoin` etc.) |
| `concatCached n` | `0x17, n` | `{ concat: { cached: true, n } }` | `0x17 0x5b` (`writeCoin` etc., n = 91) |

So a stack key is encoded `-1` in place of a literal key's
`len, atoms…, values…`. Only the cached, non-path-pushing `idx` with literal
keys followed by one stack key occurs in compactc 0.36.1 output, so only that
form was added (`Impact.Op.idxStack`, `Impact.Op.concatCached`, their
`Op.encode`/`Op.mapM` cases, `Export.op` → `{"kind": "idxStack", "path"}` /
`{"kind": "concatCached", "n"}`, and `mapOp`/`encodeOp`/`runtimeOp` in the
executor). The case analyses over `Op` in `Damp/LedgerAgreement.lean`
(`Op.encode_mapM`, `Op.blank_mapM`, `Op.mapM_congr`),
`Damp/OptimizeExecutor.lean` (`Op.mapM_map`) and `Damp/OptimizeCorrect.lean`
(`Op.encode_map`) got an `idxStack` case each, mirroring their `idx` case;
`concatCached` is closed by the generic operand-free cases.

## Kernel operations

The effects of the transaction sit one below the contract state on the VM
stack; each coin operation brings them up with `swap 0`, updates one slot
(`idx cached pushPath [slot k]` … `ins cached 2`) and swaps back. The slots
observed:

| Slot | Effects field | Operations |
|---|---|---|
| 0 | claimed nullifiers (set) | `claimZswapNullifier` |
| 1 | claimed shielded receives (set) | `claimZswapCoinReceive` |
| 2 | claimed shielded spends (set) | `claimZswapCoinSpend` |
| 4 | shielded mints (map domain separator → amount) | `mintShielded` |
| 5 | unshielded mints | `mintUnshielded` |
| 6 | unshielded inputs (map token type → amount) | `incUnshieldedInputs` |
| 7 | unshielded outputs | `incUnshieldedOutputs` |
| 8 | claimed unshielded spends (map (token type, recipient) → amount) | `claimUnshieldedCoinSpend` |

The balances are slot 5 of the *context* (`dup 2`/`dup 3`).

| Op | Sequence |
|---|---|
| `claimIn k x` (claims) | `swap 0; idx cached pushPath [{1:k}]; push {32: x}; push null; ins cached 2; swap 0` |
| `addIn k key a` (mints, inc*, unshielded spend) | `swap 0; idx cached pushPath [{1:k}]; push key; dup 1; dup 1; member; push a; swap 0; neg; branch 4; dup 2; dup 2; idxStack; add; ins cached 2; swap 0` |
| `balance t` | `dup 2; idx cached [{1:5}]; dup 0; push t; member; branch 3; pop; push {16: 0}; jmp 1; idx cached [t]; popeq cached [bytes 16]` |
| `balanceLessThan t a` | the same up to the last `idx`, then `push {16: a}; lt; popeq cached [bytes 1]` |
| `balanceGreaterThan t a` | `push {16: a}; dup 3; idx cached [{1:5}]; dup 0; push t; member; branch 3; pop; push {16: 0}; jmp 1; idx cached [t]; lt; popeq cached [bytes 1]` |

Amounts: `{8: a}` for the two mints (`Uint<64>`), `{16: a}` for the rest
(`Uint<128>`). A token type `t` is `left<Bytes<32>, Bytes<32>>(color)`,
alignment `[bytes 1, bytes 32, bytes 32]`; the unshielded-spend key is the
token type followed by the recipient `Either<ContractAddress, UserAddress>`,
one cell of alignment `[1, 32, 32, 1, 32, 32]`.

Evidence (from `tokens.compact`):

- `kernel.claimZswapNullifier(nul)` (in `sendShielded`): `0x40 | 0x80 0x01 0x01 0x00 | 0x10 0x01 0x01 0x20 %h1 %h0 | 0x10 0x00 | 0xa2 | 0x40`
- `kernel.claimZswapCoinReceive(cm)` (in `receiveShielded`): the same with `0x80 0x01 0x01 0x01`
- `kernel.claimZswapCoinSpend(cm)` (in `mintShieldedToken`): the same with `0x80 0x01 0x01 0x02`
- `kernel.mintShielded(pad(32, "damp:token"), disclose(amount))`:
  `0x40 | 0x80 0x01 0x01 0x04 | 0x10 0x01 0x01 0x20 0x00 0x64616d703a746f6b656e | 0x31 | 0x31 | 0x18 | 0x10 0x01 0x01 0x08 %amount | 0x40 | 0x08 | 0x12 0x04 | 0x32 | 0x32 | 0x60 -0x01 | 0x14 | 0xa2 | 0x40`
- `kernel.mintUnshielded(...)`: the same with `0x80 0x01 0x01 0x05`
- `kernel.claimUnshieldedCoinSpend(left(color), right(disclose(who)), amount)` (in `mintUnshieldedToken`):
  `0x40 | 0x80 0x01 0x01 0x08 | 0x10 0x01 0x06 0x01 0x20 0x20 0x01 0x20 0x20 0x01 %c1 %c0 0x00 0x00 0x00 0x00 0x00 %who1 %who2 | 0x31 | 0x31 | 0x18 | 0x10 0x01 0x01 0x10 %amount | 0x40 | 0x08 | 0x12 0x04 | 0x32 | 0x32 | 0x60 -0x01 | 0x14 | 0xa2 | 0x40`
- `kernel.incUnshieldedOutputs(left(color), amount)` (in `sendUnshielded`):
  `0x40 | 0x80 0x01 0x01 0x07 | 0x10 0x01 0x03 0x01 0x20 0x20 0x01 %c0 %c1 0x00 0x00 | 0x31 | 0x31 | 0x18 | 0x10 0x01 0x01 0x10 %amount | 0x40 | 0x08 | 0x12 0x04 | 0x32 | 0x32 | 0x60 -0x01 | 0x14 | 0xa2 | 0x40`
- `kernel.incUnshieldedInputs`: the same with `0x80 0x01 0x01 0x06` (`receiveUnshielded`)
- `kernel.balance(left(color))` (`unshieldedBalance`):
  `0x32 | 0x60 0x01 0x01 0x05 | 0x30 | 0x10 0x01 0x03 0x01 0x20 0x20 0x01 %c0 %c1 0x00 0x00 | 0x18 | 0x12 0x03 | 0x0b | 0x10 0x01 0x01 0x10 0x00 | 0x13 0x01 | 0x60 0x03 0x01 0x20 0x20 0x01 %c0 %c1 0x00 0x00 | 0x0d 0x01 0x10 %r`
- `kernel.balanceLessThan(left(color), disclose(amount))`: the same through the last `idx`, then `0x10 0x01 0x01 0x10 %amount | 0x01 | 0x0d 0x01 0x01 %r`
- `kernel.balanceGreaterThan(...)`: `0x10 0x01 0x01 0x10 %amount | 0x33 | 0x60 0x01 0x01 0x05 | 0x30 | … | 0x60 0x03 … | 0x01 | 0x0d 0x01 0x01 %r`
  (`unshieldedBalanceGte`/`Lte` are `cond_select r 0 1` after the read.)

## Types

In `Damp/Ledger.lean`, beside `ContractAddress` (the kernel's signatures need
them): `Uint128`, `UserAddress {bytes}`, `Either α β` (`isLeft`, `left`,
`right`; JS `{is_left, left, right}`, struct name `Either`) and
`TokenType = Either (Bytes 32) (Bytes 32)`. In `Damp/Tokens.lean`, declared with
`struct` as a user would: `ZswapCoinPublicKey {bytes}`,
`ShieldedCoinInfo {nonce, color, value : Uint128}`,
`QualifiedShieldedCoinInfo {…, mt_index : Uint64}`,
`ShieldedSendResult {change : Maybe ShieldedCoinInfo, sent}` and the internal
`CoinPreimage {domain_sep : Bytes 21, info, dataType, data}`; and the
constructors `left x`, `right y` (Compact's `left<A, B>`, `right<A, B>`).

## Library functions

Each follows `standard-library.compact` statement for statement; where the
order of instructions mattered for the verifier key, the Damp definition says
so. Hashes as observed:

- `coinCommitment(coin, recipient)`: `persistent_hash` of alignment
  `[b21, b32, b32, b16, b1, b32]`, inputs `"midnight:zswap-cc[v1]"`, nonce
  (2 limbs), color (2), value, `is_left`, `is_left ? left.bytes : right.bytes`
  (two `cond_select`s when the recipient is not constant).
- `coinNullifier(coin, addr)`: the same with `"midnight:zswap-cn[v1]"`,
  `is_left` 0 and the contract address.
- `tokenType(ds, addr)`: `persistent_hash` of `[b32, b32, b32]` over
  `pad(32, "midnight:derive_token")`, `ds`, `addr` (a `persistentCommit`).
- `evolveNonce(i, n)` and the nonces in `sendShielded`/`mergeCoin`:
  `transient_hash` of `"midnight:kernel:nonce_evolve" as Field` (or
  `…/2` for change), `i` where present, `degradeToTransient(n)`; then
  `div_mod_power_of_two … bits 248` for `upgradeFromTransient`. compactc
  surrounds these with `copy` instructions Damp does not emit; the keys agree.

| Function | Compact (abridged) | Damp |
|---|---|---|
| `nativeToken` | `pad(32, "")` | `Bytes.pad 32 ""`; `native` writes `0x11 0x01 0x01 0x20 0x00 0x00` |
| `tokenType` | `persistentCommit([ds, addr.bytes], pad(32, "midnight:derive_token"))` | `persistentCommit #v[ds, addr.bytes] (Bytes.pad 32 …)` |
| `mintShieldedToken` | `const coin = {nonce, color: tokenType(ds, kernel.self()), value}; kernel.mintShielded(ds, value); createZswapOutput(coin, r); const cm = coinCommitment(coin, r); kernel.claimZswapCoinSpend(cm); if (!r.is_left && r.right.bytes == kernel.self().bytes) kernel.claimZswapCoinReceive(cm)` | same order; `!r.is_left` bound before `cm` and the second `kernel.self()` read guarded by it (below) |
| `evolveNonce` | `upgradeFromTransient(transientHash([…nonce_evolve, index, degradeToTransient(nonce)]))` | same |
| `shieldedBurnAddress` | `left(default)` | `left (Value.zero ZswapCoinPublicKey)` |
| `receiveShielded` | `const r = right(kernel.self()); createZswapOutput(coin, r); kernel.claimZswapCoinReceive(coinCommitment(coin, r))` | same |
| `sendShielded` | self read; `createZswapInput`; claim nullifier; `const change = input.value - value`; `const output = {…}`; `createZswapOutput`; claim spend of `coinCommitment(output, r)`; if `r` is this contract, claim receive of `coinCommitment(output, r)`; if `change == 0` none else a change coin to self, claimed spent and received | same, the commitment computed once |
| `sendImmediateShielded` | `sendShielded(upcast(input), …)` (`mt_index: 0`) | same |
| `mergeCoin` | two inputs and nullifiers, `assert(a.color == b.color, …)`, nonce, `(a.value + b.value) as Uint<128>`, output to self, claimed spent and received | same (`castTo`, after the nonce, as compactc orders it) |
| `mergeCoinImmediate` | `mergeCoin(a, upcast(b))` | same |
| `mintUnshieldedToken` | `kernel.mintUnshielded(ds, amount); const color = tokenType(ds, kernel.self()); kernel.claimUnshieldedCoinSpend(left(color), r, amount); if (r.is_left && r.left.bytes == kernel.self().bytes) kernel.incUnshieldedInputs(left(color), amount)` | same; the second self read guarded by `is_left` (`cond`) |
| `sendUnshielded` | `incUnshieldedOutputs`; `claimUnshieldedCoinSpend`; the same self check and `incUnshieldedInputs` | same |
| `receiveUnshielded` | `incUnshieldedInputs(left(color), amount)` | same |
| `unshieldedBalance`, `…Lt`, `…Gte`, `…Gt`, `…Lte` | `kernel.balance…(left(color), …)`, `!` for Gte/Lte | same |

Instruction order that had to be reproduced:

- **Short-circuit `&&`.** In `if (!r.is_left && r.right.bytes == kernel.self().bytes)`
  compactc reads `kernel.self()` only when the left side holds: the read's
  `public_input`s and `impact`s are guarded by `!r.is_left`, and the condition
  is `cond_select(r.is_left, 0, eq)`. For a constant recipient the read is
  gone entirely (`mint` to `left(…)`). Damp's library guards the read the
  same way (`underGuard`, `cond`).
- **Where `!r.is_left` is computed.** In `mintTo` (recipient not constant)
  compactc computes `cond_select(r.is_left, 0, 1)` right after the
  `mintShielded` impacts, before the commitment's `cond_select`s, although the
  source uses it only after the spend claim; the ternary in `coinCommitment`
  evidently computes it as the guard of its else branch and the later use
  shares it. `mintShieldedToken` binds `notLeft` at that point; without it
  `mintTo`'s key differed.
- **The spend commitment in `sendShielded` is bound** (`const cm`): with a
  constant `left` recipient (`burn`) the receive is under guard 0, which the
  optimizer can only drop when its operands cannot fail; a bound commitment is
  a variable, a persistent hash is not.

`mintTo`, `mintSelf`, `pay`, `payImm`, `mintUTo` and `sendU` take recipients
that are run-time values or this contract, so both the constant-folded and the
guarded forms of the self checks are compiled and compared.

## Storing a received coin: `writeCoin`, `insertCoin`, `pushFrontCoin`

These are ledger operations on fields holding `QualifiedShieldedCoinInfo`
(`compiler/midnight-ledger.ss`, "update-with-coin-check"). They take a
`ShieldedCoinInfo` and its recipient, push the coin's commitment, look it up
in context slot 1 (the commitment indices of the transaction's Zswap outputs:
`idx cached [{1:1}, stack]`), push the coin, and `concat cached 91` the coin
with the index found, giving the qualified coin, which is stored. The
`mt_index` is therefore determined by the ledger when the transaction runs,
not by the circuit: there is no `popeq`, the circuit only commits to the
instructions. In Damp (`Damp/Tokens.lean`): `Cell.writeCoin`,
`Map.insertCoin`, `Set.insertCoin`, `LedgerList.pushFrontCoin`, all built on
`CoinStore.qualify depth coin recipient`
= `dup depth; push {32: coinCommitment coin recipient}; idxStack [{1:1}]; push coin; swap 0; concatCached 91`.

| Op (field at path `f`, `L = |f|`) | Sequence |
|---|---|
| `Cell.writeCoin coin r` | `push {1: f}; qualify 3; ins false 1` |
| `Map.insertCoin k coin r` | `idx pushPath f; push k; qualify (3 + 2L); ins false 1; ins cached L` |
| `Set.insertCoin coin r` | `idx pushPath f; qualify (2 + 2L); push! null; ins false 1; ins cached L` |
| `LedgerList.pushFrontCoin coin r` | `idx pushPath f; dup 0; idx [{1:2}]; addi 1; push! [null, null, null]; push {1:0}; qualify (5 + 2L); ins cached 1; swap 0; push {1:2}; swap 0; ins cached 1; swap 0; push {1:1}; swap 0; ins cached (L+1)` |

Evidence (`held.writeCoin(disclose(coin), right(kernel.self()))` at field 6,
after `receiveShielded`):
```
persistent_hash [b21,b32,b32,b16,b1,b32] ("midnight:zswap-cc[v1]", coin, 0x00, %data.12, %data.13) -> %hash.15 %hash.16
0x10 0x01 0x01 0x01 0x06 | 0x33 | 0x10 0x01 0x01 0x20 %hash.16 %hash.15 | 0x61 0x01 0x01 0x01 -0x01
0x10 0x01 0x03 0x20 0x20 0x10 %coin.0 … %coin.4 | 0x40 | 0x17 0x5b | 0x91
```
`heldMap.insertCoin(k, …)` (field 7): `0x70 0x01 0x01 0x07 | 0x10 0x01 0x01 -0x02 %k | 0x35 | … | 0x17 0x5b | 0x91 | 0xa1`;
`nested.lookup(k).insertCoin(j, …)` (L = 2): `0x71 … %k | 0x10 … %j | 0x37 | … | 0x91 | 0xa2`;
`heldSet.insertCoin(…)`: `0x70 0x01 0x01 0x08 | 0x34 | … | 0x17 0x5b | 0x11 0x00 | 0x91 | 0xa1`;
`heldList.pushFrontCoin(…)`: `0x70 0x01 0x01 0x09 | 0x30 | 0x50 0x01 0x01 0x02 | 0x0e 0x01 | 0x11 0x33 0x00 0x00 0x00 | 0x10 0x01 0x01 0x01 0x00 | 0x37 | … | 0x17 0x5b | 0xa1 | 0x40 | 0x10 0x01 0x01 0x01 0x02 | 0x40 | 0xa1 | 0x40 | 0x10 0x01 0x01 0x01 0x01 | 0x40 | 0xa2`
(first observed in a scratch contract with the fields at indices 0–4; the
oracle contract has them at 6–9).

**The executor side.** compactc's generated JS guards each of these with
`__compactRuntime.hasCoinCommitment(context, coin, recipient) ? queryLedgerState(…) : throw CompactError("Coin commitment not found. Check the coin has been received (or call 'createZswapOutput')")`;
the index itself comes from the runtime's VM executing the `idx` on the
context, whose commitment indices `createZswapOutput` filled in
(`QueryContext.insertCommitment(cm, currentIndex)`). Damp's executor needs
nothing new: the built-in `createZswapOutput` fills the same indices, and the
ledger oracle runs the same `idx`. When the commitment is absent the runtime
refuses the `idx` (`expected a cell, received null`), which is the ledger
oracle returning `none` in `Exec.step`: the call fails at that statement, as
compactc's fails at its pre-check (call `keepOnly`, both fail). The message
differs; nothing else does, and `Damp/Executor.lean` needed no change.

Disclosure: the coin and recipient are ledger operands, so a private coin
needs `disclose`, as in compactc (the oracle contract discloses them as
compactc requires).

## Built-in witnesses

`ownPublicKey(): ZswapCoinPublicKey`, `createZswapInput(QualifiedShieldedCoinInfo): []`
and `createZswapOutput(ShieldedCoinInfo, Either<ZswapCoinPublicKey, ContractAddress>): []`
are witnesses whose implementation is the runtime's. compactc's module calls
`__compactRuntime.ownPublicKey(context)`,
`__compactRuntime.createZswapInput(context, coin)` and
`__compactRuntime.createZswapOutput(context, coin, recipient)`, and pushes
the result's aligned value onto `privateTranscriptOutputs` (an empty
`{value: [], alignment: []}` for the two that return nothing). In the
circuit, `ownPublicKey` is a pair of `private_input`s with `constrain_bits`
8/248; the other two produce no instruction at all.

In Damp they are ordinary `askWitness` calls with reserved names
(`Damp/Tokens.lean`), so to the definition of the executor (`Exec.step`,
unchanged) they are witnesses like any other. The executor answers them
itself (`builtinWitness` in `executor.mjs`): it rebuilds the JS arguments from
their field elements with the fixed shapes (requiring them to convert back to
exactly those elements), and when the statement commits runs the runtime
function on the call's context, which updates
`context.callContext.currentZswapLocalState` (and, for an output, the query
context's commitment indices) exactly as compactc's module does. `makeContract`
refuses user witnesses with these names; the generated TypeScript
declarations leave them out of `Witnesses`. `executor/test/run.mjs` compares
`currentZswapLocalState` after every completed call with compactc's.

## Disclosure

compactc's verdicts, each from a one-circuit variant of `tokens.compact`
(argument not wrapped in `disclose`):

| Variant | compactc 0.36.1 |
|---|---|
| `receiveShielded(coin)` | error: "might disclose a link between a coin receive and the coin with the commitment given by a hash of the witness value" |
| `mintShieldedToken(…, amount, disclose(n), …)` | error ("the value of a token mint") |
| `mintShieldedToken(…, n, …)` (nonce) | error ("… commitment given by a hash of the witness value") |
| `mintShieldedToken(…, left(to))` | error (same) |
| `sendShielded(treasury, to, …)`, `(…, value)` | error |
| `mergeCoin(treasury, b)` | error ("a claim of nullifier … given by a hash") |
| `nonce = evolveNonce(i, nonce)` | error ("a converted form of a hash of the witness value") |
| `sendUnshielded(color, amount, …)`, `mintUnshieldedToken(…, to)`, `unshieldedBalanceLt(color, amount)` | error |
| `receiveShielded(w())` (`w` a witness) | error |
| `createZswapOutput(coin, …)` with `coin` an argument | accepted (`discloses nothing`) |
| `tokenType(ds, kernel.self())` with `ds` an argument, written to the ledger | accepted (a commitment) |
| `owner = ownPublicKey()`, `return ownPublicKey()` | accepted |

Decision: the library adds no `disclose` of its own except on
`ownPublicKey`'s result. Commitments and nullifiers are `persistentHash`es,
which in Damp, as in Compact, do not clear taint, so a private coin, nonce,
value or recipient reaching a kernel claim, a mint or a guard makes the
circuit fail Damp's disclosure check unless the caller wrapped it in
`disclose`; `tokenType` is a `persistentCommit`, which clears it in both;
witness *arguments* are not checked in Damp, matching
`createZswapInput`/`createZswapOutput`'s `discloses nothing`; and
`ownPublicKey` is wrapped in `disclose` inside the library because compactc
does not treat its result as witness data. So user code needs `disclose`
exactly where the variants above show compactc demands it.
`Examples/Tokens.lean` mirrors `tokens.compact`'s `disclose`s one for one.

## Differences from compactc

`pay` and `payImm` (`sendShielded` / `sendImmediateShielded` with a recipient
that is not a constant `left`, whose `change` is stored) do not get
compactc's verifier key, for two reasons, both in the emitter:

1. **Repeated persistent hash.** `sendShielded` calls
   `coinCommitment(output, recipient)` twice (spend claim, receive claim).
   compactc emits two identical `persistent_hash` + `bytes_into_natives`
   pairs; Damp's emitter shares syntactically equal expressions (the same
   known difference as for Merkle-tree leaves in `docs/ledger-types.md`), and
   its optimizer removes copies and `disclose` markers, so no library-level
   rewriting can produce a second hash.
2. **A select on a copied constant.** For the `change` result compactc emits
   `cond_select(change == 0, 0, t)` where `t` is a `copy` of `0x00` (the zero
   top byte of the change coin's `upgradeFromTransient`). Damp has the
   constant and folds `select c 0 0` to `0`.

Both only remove instructions computing values compactc already has, so the
circuits accept the same calls (the executor checks agree: same proof data,
results, Zswap state). `test/oracle.sh` checks that these are the *only*
differences: for circuits listed in `test/oracle/known-differences` it
rewrites compactc's ZKIR with `test/zkir-normalize.py` (drop a repeated
`persistent_hash` and its `bytes_into_natives`; replace `copy` of a constant
by the constant and fold a `cond_select` between equal constants), compiles
that with `zkir-v3`, and requires Damp's key; it prints `ok~` for them. Both
pass. Matching exactly would need the emitter not to share persistent hashes
across statements and to emit `copy` for `upgradeFromTransient`'s zero.

A third difference comes with the coin-storing operations. compactc computes
their commitment with its built-in `rt-coin-commit`, not the library's
`coinCommitment`, and does not fold the recipient select when the recipient is
a constant: for `right(kernel.self())` it emits
`cond_select(0x00, 0x00, %self)` for each of the two limbs. Damp folds the
constant condition (its optimizer, and `select` on a known `Boolean`).
`test/zkir-normalize.py` replaces a `cond_select` with a constant bit by the
branch it picks.

Circuits with a documented difference (`test/oracle/known-differences`):
`pay`, `payImm`, `spend` (1, 2, 3); `keep`, `keepMap`, `keepSet`, `keepList`
(3); `mergeKept`, `mergeHeld` (2, 3). All give `ok~`: compactc's circuit with
exactly these differences undone has Damp's key. `burn`, `keepOnly` (a
run-time recipient: no constant select) and every other circuit match byte
for byte.

## Skipped

- `claimContractCall` (contract-to-contract calls) and the shielded/dust token
  forms of `TokenType` other than `left(color)`: not used by any standard-library
  token function.
- `insertCoin` on a `Map` whose values are ledger ADTs (only plain
  `QualifiedShieldedCoinInfo` values exist in Compact), and `writeCoin` on a
  cell nested in a map (Compact has no such cells).
- `ownPublicKey` and the `create*` built-ins are not offered as user witnesses
  with other shapes; their shapes are fixed.

## On the network

`deploy/src/tokens.mjs`, against the local network (details and full log
excerpt in `deploy/DEPLOY-NOTES.md`, section "Tokens"). Deploying all 20
circuits at once is refused by the node ("Transaction would exhaust the block
limits"); with the 8 circuits used, every call succeeded with real proofs:
`whoami` returned the wallet's coin public key; `mint(1000, …)` to the
wallet's coin public key and `mintU(500, …)` to its unshielded address made
the wallet show shielded `3b35…bf8a: 1000` and unshielded `ef33…73fc: 500`
(the contract's two `tokenType`s); `deposit` of 100 of that token was
balanced by the wallet from its own coin (it then showed 900); `mintUTo(40,
self)` and `sendU(15, wallet)` left the contract with an on-chain unshielded
balance of 25, which `balU` returned, and the wallet with 515.

Holding a coin (`deploy/src/hold.mjs`, details in `deploy/DEPLOY-NOTES.md`,
"Holding a coin"): `keep` (receive a coin the wallet pays for and store it
with `writeCoin`) succeeded every time; the indexer showed the stored coin
qualified with the ledger's real Merkle-tree index (30, 36, 39, 42). Once,
`mergeHeld` spent that stored coin, merged it with a fresh one and stored the
result (index 31; wallet 700 → 650). `spend` (`sendShielded` of the stored
coin with change) was rejected by the node in every run, and `mergeHeld` in
three of four, with `guaranteed execution would fail: ran out of gas budget`
(`1010 … Custom error: 104`), and identically so for compactc's own build of
the same circuits, whose local gas costs equal the executor's. So sending
part of a held coin back to the wallet was not observed on chain; the
obstacle is in how the transaction's gas budget is derived, not in Damp.
