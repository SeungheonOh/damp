# A model of the ledger VM

Damp's ledger types (`Damp/Lang/Ledger.lean`) compile each operation to a fixed
sequence of Impact VM instructions (`Damp/IR/Impact.lean`). Those sequences
were copied from compactc's output and checked by running them
([ledger-types.md](ledger-types.md)), but nothing in Lean said what the
instructions *do*. `Damp/Ledger/` is a Lean model of Midnight's on-chain VM on
the fragment Damp emits; `test/vm.sh` checks it against the real VM; and
`Damp/Proofs/Ledger/` proves what Damp's `Cell`, `Counter`, `Map` and `Set`
operations do against it, as well as `LedgerList`, the Merkle trees, kernel
reads, maps inside maps, every kernel operation that writes the effects, the
token library's operations, and the cross-contract call assumption
`--ledger-opt` relies on.

| File | Contents |
|---|---|
| `Damp/Ledger/Vm.lean` | State values, aligned values, the read cache, the stack; every instruction (`ROp.exec`), programs (`runR`); Damp's `Op Fr` to the VM's instructions (`Op.toR`), `Op.run`, `runOps` |
| `Damp/Ledger/Query.lean` | `QueryContext::query` (`query`), the effects' decoding, and the ledger oracle Damp's executor is given (`ledgerOracle`, `oracles`) |
| `Damp/Ledger/Merkle.lean` | The root of a bounded Merkle tree (`merkleHooks`), for the `root` instruction |
| `Damp/Proofs/Ledger/Basic.lean` | `emitted` (the instructions an operation emits), shared lemmas |
| `Damp/Proofs/Ledger/{Cell,Counter,Map,Nested,List,MerkleSpec,Kernel}.lean` | The theorems below |
| `Damp/Proofs/Ledger/Effects.lean` | The kernel operations that write the effects: claims, mints, unshielded inputs, outputs and spends, contract calls |
| `Damp/Proofs/Ledger/Tokens.lean` | The token library (`Damp/Lang/Tokens.lean`) composed from them; the balance read |
| `Damp/Proofs/Ledger/Calls.lean` | The cross-contract call assumption, stated (`CallIsolated`) and used (`runC_eq_run`, `Pass.SoundLedger.runC`) |
| `Damp/Proofs/Ledger/Limbs.lean` | Byte strings over 31 bytes: the write-then-read round trip for every alignment |
| `Damp/Proofs/Ledger/Executor.lean` | The executor's theorems instantiated with the modelled ledger |
| `Damp/Proofs/Interface/LedgerLogic.lean` | A program logic for circuit bodies run by the executor, ledger and witnesses included (`XRuns`) |
| `Examples/LedgerProofs.lean` | Contract-level theorems about `vault.spend` and `counter.bump`, end to end |
| `Test/Vm.lean`, `executor/test/vm-vectors.mjs`, `test/vm.sh` | The differential test |
| `executor/test/call-isolation.mjs`, `test/calls-isolation.sh` | The call assumption tested on the runtime |

## The authority

The Rust implementation in midnightntwrk/midnight-ledger at tag
`onchain-runtime-4.0.2`, the version of `@midnightntwrk/onchain-runtime-v4`
(4.0.2) the executor runs: `onchain-vm/src/vm.rs` (`run_program_internal`,
one match arm per instruction, cited in `Vm.lean` per instruction),
`onchain-state/src/state.rs`, `base-crypto/src/fab/` (aligned values, their
conversions and serialized sizes), `onchain-runtime/src/context.rs`
(`QueryContext::query`, `to_vm_stack`, the effects' encoding) and
`transient-crypto/src/merkle_tree.rs` (tree roots).

## What is modelled

* **Values.** State values: null, cells, maps (lists of entries with distinct
  keys), arrays, bounded Merkle trees (height and leaf hashes). An aligned
  value is an alignment and its atoms; an atom, a byte string without trailing
  zeros (Rust normalises them), is the natural number it encodes little-endian,
  so atom equality is number equality. Fitting an alignment
  (`AlignmentAtom::fits`), the `u8`/`u64`/`bool`/hash decodings, and
  serialized sizes (for `eq`'s 64-byte limit and `concat`'s bound) are
  modelled exactly.
* **The stack**, with each entry's strength (strong values may be stored) and
  cache key.
* **The read cache** (`Cache`, `InnerCache`, `CacheKey`): which parts of the
  initial stack a cached `idx`, `ins` or `rem` may touch. Weak initial values
  (the call context and the effects) are fully cached; the contract state
  starts uncached, and a path becomes cached once an `idx` has visited it.
  A cached instruction on an unvisited path fails as in Rust. (Disabling the
  cache check in the model makes about 800 test vectors disagree.)
* **Every instruction Damp emits**: `lt eq type size and or neg log root pop
  popeq addi subi push branch jmp add sub concat member rem dup swap idx ins
  ckpt`, with every failure `run_program_internal` reports: running off the
  stack, type errors, `u64` overflow and underflow, out-of-range array and
  tree indices, cache misses, oversized operands, jumping past the end, the
  stack height limit.
* **Program decoding**: Damp's `Op Fr` becomes the VM's instruction the way
  the executor does it (`runtimeOp`, `alignedOfFields`); as in the runtime,
  the whole program is decoded before it runs, so an operand that does not fit
  its alignment, or an `addi`/`subi` immediate of 2^32 or more, fails the request.
* **Queries** (`query`): the stack `[context, effects, state]` (context and
  effects weak); the program must leave three values, the state strong; the
  effects are decoded into their typed Rust values and re-encoded
  (`TryFrom<VmValue> for Effects`), all nine slots: the hash sets (0 to 2,
  `HashOutput -> ()`), the claimed contract calls (3, `(u64,
  ContractAddress, HashOutput, Fr) -> ()`), the mints (4, 5, `HashOutput ->
  u64`), the unshielded inputs and outputs (6, 7, `TokenType -> u128`) and
  spends (8, `(TokenType, PublicAddress) -> u128`). A key or value that is not
  a well-formed value of its type fails the query (a `TokenType` or
  `PublicAddress` whose unused side is not empty, a tag out of range, an `Fr`
  not below the modulus, a wrong number of atoms, an amount too wide); keys
  are re-encoded with the type's alignment, a null value becomes the
  default (`effectKey`, `effectValue` in `Query.lean`).
  Entry order: a map is a list in the model, unordered in the runtime. The
  decoding keeps the entries it keeps in their order (`effectMap`; when two
  decode to one key, the later wins), so decoding twice is decoding once
  (`decodeEffects_idem`) and every state a successful query leaves is well
  formed (`query_wf`, `ledgerOracle_wf` in `Damp/Proofs/Ledger/OptEffects.lean`).
  An earlier version rebuilt each map in reverse, so a query flipped the order
  of every effects map, and removing one query changed the final state as a
  list, though not as a set.
* **The ledger oracle** (`ledgerOracle`): each `popeq`'s value read back as
  field elements under the alignment the instruction states (the executor's
  `fieldsOfAligned`), in program order.
* **Merkle roots** (`merkleHooks`): empty subtrees have root 0, a leaf its hash
  "degraded" to a field element (low 31 bytes), a node the transient (Poseidon)
  hash of its children's roots, using `Damp/Crypto/Poseidon.lean`.

## What is abstracted

* **Gas.** Not modelled: Damp's executor runs queries without a gas limit.
* **Merkle roots** are a parameter of the VM model (`Hooks.root`), so the
  theorems hold for any root function; `merkleHooks` is the real one, used by
  the test.
* **Duplicate effect keys.** When two entries of one effects map decode to
  the same typed key (the same atoms under two alignments), the runtime's
  `HashMap` keeps one of them in its own iteration order; the model keeps the
  one later in its list. The test has such a vector (different values) and
  they agree, but the order is not modelled in general. Damp never writes a
  key under two alignments.
* `log` pops its operand; its events and size bound are not modelled (Damp
  never emits `log`). `rem` on a Merkle tree is modelled but not validated
  (never emitted). The 2^15-byte bound on pushed cells is not checked.
  Atoms are assumed normalised; `Compress` atoms (not normalised by Rust)
  never occur in Damp's ledger instructions.
* The VM's `noop` and `new` are not in Damp's instruction set and not modelled.

## Validation

`test/vm.sh` (about a minute; `VM_REUSE=1` reuses the contract builds):

1. `lake exe damp-examples build/vm-ledger/lean` writes every example
   contract's `contract.json`.
2. `executor/test/vm-vectors.mjs` wraps the runtime's
   `QueryContext.prototype.query` and runs calls of all 18 example contracts
   through the executor (the calls of the ZKIR differential test, then every
   circuit with zero and with small arguments): about 790 ledger requests,
   676 distinct (state, program) pairs. These are exactly the instruction
   sequences Damp emits, operands evaluated, with the state they ran on. From
   each it derives variants: each instruction dropped; adjacent ones swapped;
   prefixes; `cached` and `pushPath` flipped; the first key changed;
   immediates set to 0, 1, 65535, 2^32-1, 2^32, 2^32+1 and 2^53 (the last three
rejected by the runtime as not `u32`); `addi` and `subi` exchanged; `dup`
   and `swap` offsets, branch and jump skips and `ins` counts changed; `concat`
   bounds changed; pushed values given a one-byte alignment, `u64::MAX`, or
   null; a `popeq` or `pop` appended; the program doubled; and the field it
   first indexes replaced by null, an empty map, `u64::MAX`, `u64::MAX - 1`,
   2^32, a 16-byte 2^64, a field element, an array, a Merkle tree, or a map
   with an extra entry. It adds 36 synthetic programs for corners the examples
   do not reach (`eq` on long values, `concat` at its bound, `type` and `size`
   of every kind of value, tree insertion and indexing out of range, cached
   `idx` before and after a visit, stack keys, a weak state returned, the
   effects replaced), and 36 more writing entries into effects slots 3, 6, 7 and
8 with well-formed and ill-formed keys and values (an `Either` with both sides
set, tags 2 and 3, a 33-byte hash, an `Fr` equal to the modulus, `u64` and
`u128` overflows, three, five or seven atoms, a map as value, other
alignments, one key under two alignments), and 58 running the kernel's
effect-writing sequences exactly as Damp emits them (`claimIn`, `addIn`,
`claimContractCall`) on effects that already hold entries (a query context
left by an earlier query): a claim repeated, a call claimed third and with
its sequence number taken, an addition to an existing entry with sums
`2^64 - 1` and `2^64`, a present `u128` amount of `2^100` or an addition of
`2^64` (both fail: the VM adds `u64`s), two additions in one query, keys with
both sides set, and every slot written in one transaction. The calls include `tokens.mintUTo`
and `tokens.sendU` with one-sided and two-sided `Either` arguments. Each runs
through the real VM twice: `runProgram` (final
   stack with strengths, values read) and `QueryContext.query` (new state,
   effects, values read).
3. `lake exe damp-vm-test` runs the model on every vector and compares
   success, every stack value and strength, the values read, and (for
   queries) the new state and effects; any difference, the effects included,
   is a disagreement. Maps and tree leaves compare as sets.

Result (the count varies by a few vectors between runs, since some example
calls sample random values):

```
26995 vectors (12421 succeed in the real VM)
VM (runProgram):         26995 agree, 0 disagree
query (QueryContext):    26995 agree, 0 disagree (779 rejected by the runtime's typed decoding of the effects)
effects after a query:   6793 of 6793 successful queries agree
ALL AGREE
```

`executor/test/either-both.mjs` checks the same rejection end to end: the
executor and compactc's code both fail `tokens.mintUTo` with a two-sided
`Either`.

What had to change to get there. The instruction semantics, written from
`vm.rs`, agreed with the real VM on every vector from the first run. The
disagreements were all outside it:

* `root` was at first left to the hook, so the 762 vectors reaching it could
  not be compared; `Damp/Ledger/Merkle.lean` now computes the real root, and
  they agree.
* The query layer at first checked only the effects' outer shape and kept
  them as left: 64 queries the runtime rejects were accepted, and 111
  successful queries left differently encoded effects. Modelling the typed
  decoding of slots 0 to 2, 4 and 5 brought these to 62 and 33; modelling
  slots 3 and 6 to 8 as well brought both to 0 on the first run.

That the comparison has teeth was checked by breaking the model on purpose:
swapping `lt`'s operands and disabling cache checks makes 1329 vectors
disagree; disabling the cache checks alone, 873.

## Theorems

All in `namespace Damp.Ledger`, about `emitted op` (the instructions the real
definition in `Damp/Lang/Ledger.lean` emits, taken by running it), evaluated
as the executor sends them (`Exec.request p env`), run through
`ledgerOracle H` for any root hook `H`. The ledger state `σ` is well formed
(`σ.WF`: its effects are as the runtime re-encodes them, now for all nine
slots; the field specifications did not have to change when the decoding of
all nine slots was modelled, since they do not write the effects, but `WF`
now holds of fewer states; the effect-writing ones of `Effects.lean` rely on
it) and its contract
state is `.array fields`; the field is top level (`path = [fieldKey index]`),
so its index is below 256. Each theorem has the form
`∃ req, (emitted op).bind (Exec.request p env) = some req ∧ ledgerOracle H req σ = ...`.
No `sorry`; axioms are `propext`, `Quot.sound` (and `Classical.choice` via the
executor's ZKIR theorem).

`Cell` (`Damp/Proofs/Ledger/Cell.lean`), `x : α` evaluating to `vs`, which the VM stores as `v`
(`AV.ofFields (alignOf α) vs = some v`):

* `Cell.write_spec`: `ledgerOracle H req σ = some ([], σ.setField c.index (.cell v))`.
* `Cell.write_frame`: the result differs from `σ` only in field `c.index`
  (every other field, the context and the effects unchanged).
* `Cell.read_spec`: if `fields[c.index]? = some (.cell w)` and
  `fieldsOf (alignOf α) w.atoms = some ys`, then `= some (ys, σ)`: the
  ledger is unchanged.
* `Cell.write_read`: after `write x`, `read` returns exactly `vs`, for a type
  whose alignment is single-limb (`SingleLimb`: no byte string over 31 bytes),
  via `fieldsOf_ofFields` (the executor's two conversions are inverse there).
* `Cell.write_read_ranges` (`Limbs.lean`): the same for every alignment Damp
  derives from a type (`Ty.LimbsAgree`: all but `Bytes 0` and `Uint`s past
  Compact's limit), given that `vs` passes the type's range checks
  (`rangesHold (Value.ranges α) vs`), via `fieldsOf_ofFields_ranges`.
  `bytes32_ones`: 32 bytes `0xff` are the limbs `[0xff, 2^248 - 1]`, stored as
  the atom `2^256 - 1` and read back unchanged.
* `Cell.resetToDefault_spec`: as `write_spec` for `Value.zero α`.

`Counter` (`Counter.lean`), field `c.index` holding `.cell ⟨a, [n]⟩` with
`n < 2^64`, an amount evaluating to `k`. The VM's `addi`/`subi` immediates are
`u32`: the runtime rejects 2^32 or more while decoding the program (tested),
so the whole request fails. The `_total` theorems make no assumption on `k`;
the others assume `k.val < 2^32` (true of a range-checked `Uint16`):

* `Counter.increment_total`: `= if k.val < 2^32 ∧ n + k.val < 2^64 then some ([], σ.setField c.index (.cell (AV.ofU64 (n + k.val)))) else none`.
* `Counter.decrement_total`: `= if k.val < 2^32 ∧ k.val ≤ n then some ([], σ.setField c.index (.cell (AV.ofU64 (n - k.val)))) else none`.
* `Counter.lessThan_total`: `= if t.val < 2^64 then some ([Fr.ofBool (decide (n < t.val))], σ) else none`.

* `Counter.increment_spec`: `= if n + k.val < 2^64 then some ([], σ.setField c.index (.cell (AV.ofU64 (n + k.val)))) else none`.
* `Counter.decrement_spec`: `= if k.val ≤ n then some ([], σ.setField c.index (.cell (AV.ofU64 (n - k.val)))) else none`.
* `Counter.read_spec`: `= some ([Fr.ofNat n], σ)`.
* `Counter.lessThan_spec`: threshold `t` with `t.val < 2^64`: `= some ([Fr.ofBool (decide (n < t.val))], σ)`.
* `Counter.resetToDefault_spec`: `= some ([], σ.setField c.index (.cell (AV.ofU64 0)))`, whatever the field held.
* `Counter.increment_read`: increment by `k` without overflow, then read: `[Fr.ofNat (n + k.val)]`.

`Map` and `Set` (`Map.lean`), field holding `.map m`, key `k` evaluating to
`ks` and stored as `kv`:

* `Map.insert_spec`: `.map (assocSet kv (.cell vv) m)`; `Set.insert_spec`: `.map (assocSet kv .null m)`.
* `Map.remove_spec`, `Set.remove_spec`: `.map (assocErase kv m)`.
* `Map.member_spec`, `Set.member_spec`: `some ([Fr.ofBool (assocGet kv m).isSome], σ)`.
* `Map.size_spec`, `Set.size_spec`: `some ([Fr.ofNat m.length], σ)` (for `m.length < 2^64`).
* `Map.lookup_spec`: with `assocGet kv m = some (.cell w)`: the field elements of `w`, ledger unchanged;
  `Map.lookup_absent`: with `assocGet kv m = none`, the request fails.
* `Map.insert_lookup`: insert then lookup of the same key returns the value inserted (single-limb value type).
* Map algebra: `assocGet_assocSet_self`, `assocGet_assocSet_ne`, `assocGet_assocErase_self`
  (keys distinct), `assocGet_assocErase_ne`, `length_assocSet_of_none`, `length_assocSet_of_some`.

`Nested.lean`:

* `Map.isEmpty_spec`, `Set.isEmpty_spec`: `some ([Fr.ofBool (decide (m.length = 0))], σ)` (for `m.length < 2^64`).
* `Map.insertDefault_spec` (plain values): `.map (assocSet kv (.cell z) m)`, `z` the
  type's zero value as stored; `Map.insertDefault_counter_spec`: `.map (assocSet kv (.cell (AV.ofU64 0)) m)`.
* A `Counter` inside a `Map` (`(← mp.lookup k)`, path `[fieldKey i, k]`), the
  entry for `kv` holding `⟨a, [n]⟩`: `Map.counter_increment_spec` (`if n + j < 2^64
  then some ([], σ.setField i (.map (assocSet kv (.cell (AV.ofU64 (n + j))) m))) else none`)
  and `Map.counter_read_spec` (`some ([Fr.ofNat n], σ)`); `Map.counter_increment_total` drops the
  `2^32` assumption (`if j < 2^32 ∧ n + j < 2^64 then ... else none`).
* A `Map` inside a `Map` (`(← mp.lookup k)`, path `[fieldKey i, k]`), the entry for `kv` holding
  `.map m₂`, inner key stored as `kv₂`: `Map.map_insert_spec` (`.map (assocSet kv (.map (assocSet kv₂
  (.cell vv) m₂)) m)`), `Map.map_remove_spec` (`assocErase kv₂ m₂`), `Map.map_member_spec`
  (`[Fr.ofBool (assocGet kv₂ m₂).isSome]`), `Map.map_lookup_spec` (the stored value's field elements),
  `Map.map_size_spec` (`[Fr.ofNat m₂.length]`); the reads leave the ledger unchanged.

`List.lean`. A list is stored as linked arrays `[head, tail, length]`;
`listRepr xs` is the state of the list of stored elements `xs`
(`listRepr [] = [null, null, 0]`, `listRepr (x :: xs) = [x, listRepr xs, xs.length + 1]`):

* `LedgerList.pushFront_spec`: `listRepr xs` becomes `listRepr (xv :: xs)` (for `xs.length + 1 < 2^64`).
* `LedgerList.popFront_spec`: `listRepr (y :: ys)` becomes `listRepr ys`; `LedgerList.popFront_nil`: popping
  the empty list sets the field to `null` (what the emitted program does).
* `LedgerList.head_nil`: the field elements of `Maybe.none`; `LedgerList.head_cons`: `Fr.ofBool true :: vs`
  (`vs` the head's field elements), given `y.size ≤ maxAlignedSize (alignOf α)` (the runtime's bound on the
  `concat` building `some y`) and `2 + maxAlignedSize (alignOf α) ≤ cellBound`.
* `LedgerList.length_spec` (`[Fr.ofNat xs.length]`), `LedgerList.isEmpty_spec` (`[Fr.ofBool (decide (xs = []))]`),
  `LedgerList.resetToDefault_spec` (`listRepr []`).

`MerkleSpec.lean`. A `MerkleTree d α` field holds `[.bmt d leaves, firstFree]`, a historic one also
`.map past`. **The hash:** the VM model takes the root from the hook `H.root`; the theorems hold for every
`H` and assume nothing about the hash (no collision resistance): `checkRoot` is stated as equality with the
hook's root. With `merkleHooks` (Poseidon over the degraded leaf hashes, `Merkle.lean`) the `_merkle`
corollary states it with `merkleRootAt`.

* `MerkleTree.insertHash_spec` (`insert x` is `insertHash (leafHash x)` by definition): with `ff < 2^d` and
  `ff + 1 < 2^64` the field becomes `[.bmt d (assocSet ff x leaves), .cell (AV.ofU64 (ff + 1))]`;
  `MerkleTree.insertHash_full`: with `d < 64` and `2^d ≤ ff` the request fails.
* `MerkleTree.isFull_spec` (`d < 64`): `[Fr.ofBool (decide (2^d ≤ ff))]`.
* `MerkleTree.checkRoot_spec`: with `H.root d leaves = some ρ`, `ρ.size ≤ 64`:
  `[Fr.ofBool (decide (⟨[.field], [rv.val]⟩ = ρ))]`; `MerkleTree.checkRoot_merkle`:
  `ledgerOracle merkleHooks req σ = some ([Fr.ofBool (decide (rv = merkleRootAt leaves d 0))], σ)`.
* `HistoricMerkleTree.insertHash_spec`: as above, and the root `ρ'` of the new leaves
  (`H.root d (assocSet ff x leaves) = some ρ'`) is added: `.map (assocSet ρ' .null past)`.
* `HistoricMerkleTree.checkRoot_spec`: `[Fr.ofBool (assocGet ⟨[.field], [rv.val]⟩ past).isSome]`.
* `HistoricMerkleTree.resetHistory_spec`: the past roots become `.map [(ρ, .null)]`, `ρ` the current root.

`Kernel.lean`, the call context an array `cfs` (0: own address, 2: block time `τ < 2^64`):

* `Kernel.self_spec`: `some (ys, σ)`, `ys` the address cell read as `[bytes 32]`.
* `blockTimeLt_spec`: `= if tv.val < 2^64 then some ([Fr.ofBool (decide (τ < tv.val))], σ) else none`;
  `blockTimeGt_spec`: the same with `tv.val < τ`; `emitted_blockTimeGte`, `emitted_blockTimeLte`: they send
  the requests of `blockTimeLt`, `blockTimeGt` (the negation is in the circuit).
* `effectEntry_spend_both_sides`, `decodeEffects_spend_both_sides`: effects whose slot 8 holds a key whose
  `PublicAddress` has both sides non-zero do not decode, so a query leaving them fails.

`Effects.lean`, the kernel operations that write the effects. The effects of
a well-formed state are `.array es`, nine maps; the theorem for slot `i` takes
`es[i]? = some (.map m)`. Each gives the oracle's answer: nothing is read, and
the new state is `{ σ with effects := .array (es.set i (.map m')) }`, so the
contract state and the call context are unchanged and only slot `i` changes.
`m'` is written with `assocSet` (an existing entry for the key replaced in
place, a new one added at the end) in the form the runtime re-encodes
(`decodeEffects_set`). Keys are the atoms the request carries: `kv` with
`AV.ofFields [.bytes 32] ks = some kv` for a `Bytes 32` (any hash the circuit
computed; nothing is assumed about it):

* `Kernel.claimZswapNullifier_spec`, `Kernel.claimZswapCoinReceive_spec`,
  `Kernel.claimZswapCoinSpend_spec` (slots 0, 1, 2):
  `= some ([], { σ with effects := .array (es.set i (.map (assocSet kv .null m))) })`. They never fail.
* `Kernel.claimContractCall_spec` (slot 3), the address, entry point and
  commitment stored as `kv` (`[bytes 32, bytes 32, field]`):
  `= if m.length < 2^64 then some ([], { σ with effects := .array (es.set 3 (.map (assocSet ⟨alignContractCall, m.length :: kv.atoms⟩ .null m))) }) else none`:
  the key is the sequence number (the number of claims before) and the triple.
* The additions, `addReq_spec` (slots 4 to 8): with `old` the entry's amount
  (`effAmount m kv`, 0 when absent) and `a` the amount,
  `= if (assocGet kv m).isNone ∨ old + a < 2^64 then some ([], { σ with effects := .array (es.set i (.map (assocSet kv (amountCell i (old + a)) m))) }) else none`,
  `amountCell` the runtime's `u64` (slots 4, 5) or `u128` (6 to 8). The VM
  adds with `u64` arithmetic even for the `u128` amounts: an absent entry
  takes any amount below `2^128`, an existing one fails unless the sum fits
  64 bits (the runtime agrees: the new vectors above). Instances:
  `Kernel.mintShielded_spec` (4), `Kernel.mintUnshielded_spec` (5),
  `Kernel.incUnshieldedInputs_spec` (6), `Kernel.incUnshieldedOutputs_spec`
  (7), `Kernel.claimUnshieldedCoinSpend_spec` (8), for a key that is a
  well-formed `TokenType` (`tokenTypeOk`) or `(TokenType, PublicAddress)`
  (`spendKeyOk`); with one that is not, `Kernel.incUnshieldedInputs_badKey`,
  `Kernel.incUnshieldedOutputs_badKey`, `Kernel.claimUnshieldedCoinSpend_badKey`
  (`addReq_badKey`): `= none`. An amount too wide for its alignment fails the
  request (`addReq_wide`).
* `Kernel.checkpoint_spec`: `ckpt` reads nothing and changes nothing (`= some ([], σ)`).

`Tokens.lean`, the token library. **No hash fact is assumed**: commitments,
nullifiers and token types are whatever the circuit computes with the
executor's `Prims`; the theorems take their field elements as given.

* `tokenKey_left`: `left c`, the key of every unshielded operation, is stored
  as `(1, c, 0)`, a well-formed `TokenType`, so those operations never fail on
  their key; `spendKey_left`: the spend key `(left c, r)` is well formed
  exactly when `r` is a well-formed `PublicAddress`
  (`sendUnshielded_badRecipient`: otherwise the request fails).
* `receiveUnshielded_runs`, end to end through the executor (`XRuns`): under a
  guard that holds, it completes exactly when `(1, c, 0)` is new in slot 6 or
  the sum fits 64 bits, keeps the private state, and leaves
  `{ σ with effects := .array (es.set 6 …) }`.
* `addReq_seq`, `sendUnshielded_requests`, `mintUnshielded_requests`: the two
  additions of `sendUnshielded` (slots 7 and 8) and of `mintUnshieldedToken`
  (5 and 8) in sequence: they succeed exactly when each does on its own map,
  and then both slots are updated.
* `claims_compose`: any sequence of Zswap claims (32-byte keys, slots 0 to 2;
  what `receiveShielded`, `sendShielded`, `mergeCoin` and `mintShieldedToken`
  claim) never fails and adds each key to its slot.
* `EffectsOnly`: every effect-writing kernel request changes neither the
  contract state nor the call context (`claimReq_effectsOnly`,
  `addReq_effectsOnly`, `callClaimReq_effectsOnly`), and neither does any
  sequence of them (`effectsOnly_chain`, which also keeps `WF`).
* `Kernel.balance_spec`: the balance of a token type when the transaction
  started (context slot 5): `[0]` when absent, the entry read as `u128`
  otherwise; the ledger unchanged.

`Calls.lean`, the call assumption: see "Cross-contract calls" below.

`Executor.lean`: `oracles_ledger`, `run_accepted_vm`, `run_accepted_by_zkir_vm`
(`Exec.run_accepted` and `Exec.run_accepted_by_zkir` with `oracles H w`, the
executor whose ledger is the modelled VM).

## Running a circuit against the ledger: `XRuns`

`Damp/Proofs/Interface/LedgerLogic.lean`. `Runs` (`Interface/Logic.lean`)
describes a circuit body under the IR semantics, where a witness call reads the
private transcript and a ledger operation the public one. `XRuns p O m s st ok Q`
describes what the *executor* (`Exec.steps` with oracles `O`, e.g. `oracles H w`)
does with the statements `m` builds from `s`, started in `st`: it completes
exactly when `ok`, changes the environment only at fresh variables, and then
`Q r env w l` holds (stably in the environment) of the result, the private
state `w` and the ledger state `l` afterwards. Rules:

* `XRuns.lift`: a `Runs` description of a computation building only quiet
  statements (bindings, asserts, range checks: `Quiet`, with lemmas for
  `require`, `val`, `Uint.sub`, `nameGuard`, `when_`, `cond`, ...) is an `XRuns`
  one that keeps both oracle states, since the executor runs quiet statements
  exactly as the semantics does (`steps_quiet`). The pure rules are reused, not
  re-proved.
* `XRuns.bind`, `XRuns.bind'`, `XRuns.seq` (the first result and builder state
  named), `XRuns.pure`, `XRuns.conseq`.
* `XRuns.ledgerOp`, `XRuns.ledgerRead`: a ledger operation under a guard that
  holds, given the oracle's answer `res` to its request in every environment
  agreeing below the counter (the specifications above have this form; `read_req`
  and `op_req` in `Examples/LedgerProofs.lean` convert); it completes exactly when
  the answer has the right width, and the result means the values read.
  `ReadOps.popeq_last` discharges the side condition of every reading operation.
* `XRuns.ledgerOp_off`, `XRuns.ledgerRead_off`: under a guard that is off the
  oracle is not asked (`Exec.step`'s inactive branch), the ledger is unchanged
  and the reads are zero.
* `XRuns.askWitness`, `XRuns.askWitness_off`: a witness call, parameterized by
  the oracle's answer to the arguments: it completes exactly when the answer has
  the type's width and passes its range checks; the result means the answer.
* `XRuns.underGuard`, `XRuns.when_`, `XRuns.cond` (`if%`, branches with
  effects, each described in every state it may be built in, `XBranchCtx`; the
  `else` branch from the state the `then` branch left, for each `then` result).
* `mkCircuit_exec`, `mkCircuit_exec_of_XRuns`: from a description of a circuit
  function's body to `Exec.run` of the circuit `mkCircuit` builds.

## Contract-level theorems

`Examples/LedgerProofs.lean`, about circuits written in the surface syntax, run
by `Exec.run p (oracles H w)` on the circuit the build ships (`c.circuit.optimize`,
transferred from `c.circuit` with `Exec.optimize_correct`), ending with
`Exec.run_accepted_by_zkir`:

* `spend_shipped` (`vault.spend`): with the key witness answering `ks` (whose
  persistent hash has limbs `hk`) and a ledger holding a 32-byte owner `X`, a
  32-bit limit `L` and a 64-bit counter `n`, the call completes iff
  `amount ≤ 65535 ∧ hk = Bytes.limbVals 2 X ∧ n + amount < 2^64 ∧ n + amount ≤ L`;
  then it outputs nothing, leaves the witness's private state, sets the counter
  to `n + amount` (`σ.setField 2 (.cell (AV.ofU64 (n + amount)))`), and the
  emitted ZKIR accepts the recorded proof data.
* `bump_shipped` (`counter.bump`, ledger operations under nested `if%`): the
  call completes iff `x ≤ 65535`, `go` and `stop` are 0 or 1, and
  `go = 1 → n + x < 2^64 ∧ x < 500`; then it outputs the counter (`n + x` if
  `go`, else `n`), leaves the private state, and the ledger is `bumpLedger σ n x
  go stop` (if `go`: counter `n + x`, and `total := x` unless `stop`; else
  unchanged); and the emitted ZKIR accepts.

## Byte strings over 31 bytes

A `Bytes n` with `n > 31` is `L = ceil(n/31)` limbs in a circuit (most
significant first; the first holds `n - 31(L-1)` bytes, the others 31), one
`n`-byte atom in a cell. The executor joins limbs with shift-and-or keeping `n`
bytes (`limbsToBytes`, modelled by `atomOfFields`) and splits them back
(`bytesToLimbs`, `fieldsOfAtom`). For limbs in range the join is exact and the
round trip is the identity (`fieldsOf_ofFields_ranges`); the former restriction
to single-limb alignments was a limitation of the proof only. Checked through
the real runtime by `executor/test/bytes-limbs.mjs`: `bytes.store` with 64 bytes
`0xff` (three limbs, the first 16 bits) reads back the value, matches compactc's
result and proof data, and the ZKIR accepts; `vault`'s constructor with 32 bytes
`0xff` gives compactc's initial state and reads back; a `Cell (Bytes 32)`
written with a hash is read back through `popeq` unchanged.

Out-of-range limbs (which no `Bytes` from the typed interface has: arguments
and witness results are range-checked, hashes, constants and ledger reads are
built in range) are not rejected but cut to `n` bytes, by the executor and by
the model alike, where a single-limb atom that does not fit fails the request.
Such a value can only come from a `Bytes` built from raw expressions; its call
completes in the executor but the transcript the circuit declares (the
untruncated limbs) differs from what the VM stored, so no proof would verify.
Rejecting it in `alignedOfFields` (and `AV.ofFields`) would make the two cases
uniform. `Bytes 0` takes no field element in a circuit but one in the executor's
conversion (`atomWidth` is at least 1), so a ledger cell of `Bytes 0` (or a
structure containing one) cannot be written.

## Cross-contract calls

To the executor's definition a call of another contract is a witness
(`docs/calls.md`): `Exec.step` asks `O.witness`, whose type
(`String → List Fr → ω → Option (List Fr × ω)`) gives it neither the caller's
ledger state nor a way to return one, so `Exec.run` threads the caller's
ledger state unchanged across the call (`step_witness_ledger`,
`step_bind_ledger`; the claim that follows changes only effects slot 3,
`Kernel.claimContractCall_spec`). `--ledger-opt`'s theorem
(`Pass.SoundLedger`) is about that executor. The real executor runs the
callee (`callWitness` in `executor/src/executor.mjs`).

`Damp/Proofs/Ledger/Calls.lean` states the assumption. `runC` is the executor
whose calls are answered by the most general call oracle
`C : String → List Fr → ω → σ → Option (List Fr × ω × σ)`, given the caller's
ledger state and returning one (every other statement as `Exec.step`). The
assumption:

```lean
def CallIsolated (C : CallOracle ω σ) (c : String → List Fr → ω → Option (List Fr × ω)) : Prop :=
  ∀ n args w l, C n args w l = (c n args w).map fun (r, w') => (r, w', l)
```

the answer and the private state do not depend on the caller's ledger state,
and it comes back unchanged (contract state, effects and call context). Under
it, `runC_eq_run`: `runC p C O = Exec.run p (O.withCalls c)`, so every theorem
about `Exec.run` applies; in particular `Pass.SoundLedger.runC`: a pass sound
against the ledger keeps outputs, private transcript, private state and
ledger state of `runC`, against the modelled ledger, from a well-formed state,
for every isolated call oracle.

`test/calls-isolation.sh` tests the assumption on the runtime. It logs every
query of every contract taking part in a call (`QueryContext.prototype.query`
wrapped: address, instructions, contract state and effects before and
after) and checks that each contract's queries thread: each starts from the
contract state and effects its previous query left. The one exception is the
runtime's own claim of a call made by a Damp caller, which the executor
undoes and the caller's circuit makes again from the same state with the same
instructions; the check recognises it and counts it. Contracts of
`Examples/Calls.lean`, run by Damp's executor, and `back`, compiled by compactc
from the script (it calls `bump` of the contract stored in its ledger):

| call | outcome |
|---|---|
| `caller.bump(5)`: the callee (`adder`) writes its own state | completes; caller 4 queries, 1 undone runtime claim; caller's state and effects the same across the call |
| `caller.twice(1, 2)`: one callee twice | completes; the second call sees what the first left in the callee; caller unchanged across both |
| `top.go(9)`: `top → relay → adder` | completes; `top` and `relay` (caller and callee) unchanged across their calls |
| `back.addTo(7)`: `back` (compactc) `→ caller.bump` (Damp, as a callee) `→ adder` | completes; all three thread |
| `caller.via(back, 4)`: `caller → back → caller`, re-entrant | refused: "Contract re-entrancy detected" (the runtime's `assertNoReentrancy`), before the inner `caller.bump` runs; nothing of the call survives |
| `caller.via(caller, 4)`: a contract calling itself | refused the same way |

and a forged log, in which the caller's state changes during the call, is
reported (the check has teeth). So re-entrancy cannot change the caller's
state mid-call: the runtime refuses it (compact-runtime 0.21.0, the version
the executor runs). This is a test of the runtime the executor uses, not a
proof; and it says nothing of a runtime that would allow re-entry.

## Not done, and what would make it easier

* No theorems yet for a `Set` inside a `Map`, Merkle `insertHashIndex`, or
  ADTs nested deeper than a counter or map in a map. The specifications are
  for top-level fields (`path = [fieldKey i]`) plus those two nestings.
* The shielded token operations (`mintShieldedToken`, `sendShielded`,
  `mergeCoin`, `receiveShielded`) and `sendUnshielded` / `mintUnshieldedToken`
  are stated at the level of the ledger requests they send
  (`Tokens.lean`), not end to end through the executor: that needs `XRuns`
  rules for zero-width witnesses (`createZswap*`) and their `if%` / `cond`
  bodies. `receiveUnshielded` is end to end. `balanceLessThan` and
  `balanceGreaterThan` have no theorem (they compare with `lt`, `u64` only).
* The coin-storing operations (`Cell.writeCoin`, `Map.insertCoin`,
  `Set.insertCoin`, `LedgerList.pushFrontCoin`, reading the context's
  commitment indices) have no theorem.
* The duplicate-key ordering gap (above, "What is abstracted") remains.
* A `popeq` carries Damp's own alignment, under which the executor reads the
  value back; the VM does not check it against the value's alignment, so the
  read-back theorems take the stored value's atoms as given.
