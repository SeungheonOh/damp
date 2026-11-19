# Ledger types and kernel operations

What `Damp/Lang/Ledger.lean` supports beyond `Cell`, `Counter`, `Map` and `Set`
basics, how each operation is compiled, and the compactc 0.36.1 output it was
copied from. Every Impact sequence and encoding below was observed in
`compactc.bin --skip-zk` output (the `.zkir` and the generated
`contract/index.js`); `compiler/midnight-ledger.ss` and
`compiler/zkir-v3-passes/reduce-to-zkir.ss` from the 0.33 source were read
for intent only. The regression evidence is `test/oracle/structures.compact`
and `test/oracle/structures_nested.compact` with their Lean counterparts
`Examples/Structures.lean` and `Examples/StructuresNested.lean`: identical
verifier keys for all 14 circuits, and identical proof data, results and
initial state from the executor (`executor/test/run.mjs`).

Notation. ZKIR `impact` lines are written as their field elements, hex as
compactc prints them (immediates are little-endian hex). `f` is the ledger
path of the value (`[field index]` for a top-level field, longer inside a
map), `L` its length, `k` a key. `push v` is `push false`, `push! v` is
`push true` (to storage). `{8: x}` is a cell holding `x` with alignment
`[bytes 8]`; `{1: n}` a one-byte cell, used for array slots and context
slots as well as field indices.

## Encodings added to `Damp/IR/Impact.lean`

| Instruction | Encoding | First seen in |
|---|---|---|
| `branch skip` | `0x12, skip` | `List.head` (`0x12 0x04`), `MerkleTree.insertIndex` (`0x12 0x02`) |
| `jmp skip` | `0x13, skip` | same (`0x13 0x02`) |
| `concat n` (uncached) | `0x16, n` | `List.head` (`0x16 0x26` for `Field`) |
| `pushState s v` | `0x10`/`0x11`, then `v` | see below |

State values (`StateLit`), as the operand of a push: the tag's low nibble is
the kind, the high nibble a count.

| Value | Encoding | Seen as |
|---|---|---|
| null | `0x00` | `0x11 0x00` (`Set.insert`, already used) |
| cell | `0x01`, alignment, values | `0x11 0x01 0x01 0x08 0x00` |
| empty map | `0x02` | `Map.resetToDefault`: `0x11 0x02` |
| array of n | `16n + 3`, elements | `List.resetToDefault`: `0x11 0x33 0x00 0x00 0x01 0x01 0x08 0x00` |
| empty bounded Merkle tree of depth d | `16d + 4` | `MerkleTree<4,_>.resetToDefault`: `0x11 0x23 0x44 0x01 0x01 0x08 0x00` |

compactc 0.36.1 crashes (`failed assertion (and (fixnum? n) (fx<= 0 n 15))`
in `reduce-to-zkir.ss`) when a circuit pushes an empty tree of depth 16 or
more, i.e. `resetToDefault` on `MerkleTree<20, _>`. Damp reports a build error
for that case. Trees of any depth work as fields (their initial state is set
up in JS) and for every other operation.

Already-present encodings that the new operations rely on, re-observed:
`subi` `0x0f`, `lt` `0x01`, `eq` `0x02`, `type` `0x03`, `neg` `0x08`,
`root` `0x0a`, `pop` `0x0b`, `member` `0x18`, `ckpt` `0xff`, `idx` with
`cached = true` (`0x60 + len - 1`), multi-key `idx` (`0x72 …` for three keys).

The executor maps each to the runtime op compactc's JS uses:
`{branch: {skip}}`, `{jmp: {skip}}`, `{concat: {cached: false, n}}`, and
`StateValue.newNull/newCell/newMap(new StateMap())/newArray().arrayPush(…)/
newBoundedMerkleTree(new StateBoundedMerkleTree(d))` for state values.

## Resetting, generally

`resetToDefault` on any ADT at path `f` (and `Map.insertDefault` of an ADT
value, which has the same shape one level down):

```
[idx pushPath (all but last of f)]     -- only when L > 1
push (last of f)
push! <initial state>
[extra]                                 -- HistoricMerkleTree only
ins false 1
[ins cached (L - 1)]                    -- only when L > 1
```

Top level, `Counter` (`count.resetToDefault()`, field 0):
`0x10 0x01 0x01 0x01 0x00 | 0x11 0x01 0x01 0x08 0x00 | 0x91`.
Nested, `mc.lookup(k).lookup(j).resetToDefault()` on
`Map<Field, Map<Field, Counter>>`:
`0x71 0x01 0x01 0x00 0x01 -0x02 %k | 0x10 0x01 0x01 -0x02 %j | 0x11 0x01 0x01 0x08 0x00 | 0x91 | 0xa2`.

## Cell

| Op | Sequence |
|---|---|
| `resetToDefault` | same as `write (Value.zero α)`: `push {key}; push! {zero}; ins false 1` |

`f.resetToDefault()` on `Field` at index 1:
`0x10 0x01 0x01 0x01 0x01 | 0x11 0x01 0x01 -0x02 0x00 | 0x91`.

## Counter

| Op | Sequence |
|---|---|
| `decrement n` | `idx pushPath f; subi n; ins cached L` |
| `lessThan t` | `dup 0; idx f; push {8: t}; lt; popeq cached [bytes 1]` |
| `resetToDefault` | reset with `{8: 0}` |

`c.decrement(disclose(n))`: `0x70 0x01 0x01 0x00 | 0x0f %n | 0xa1`.
`c.lessThan(disclose(n))`: `0x30 | 0x50 0x01 0x01 0x00 | 0x10 0x01 0x01 0x08 %n | 0x01 | 0x0d 0x01 0x01 %t`.
A decrement below zero fails in the runtime (`arithmetic overflow`) for both
executors; tested.

## Map and Set

| Op | Sequence |
|---|---|
| `Map.insertDefault k` | `idx pushPath f; push k; push! <initial of value>; ins false 1; ins cached L` |
| `Map.resetToDefault`, `Set.resetToDefault` | reset with the empty map |

For a plain value type `insertDefault` is `insert k 0`:
`m.insertDefault(k)` on `Map<Uint<16>, Field>` at index 2:
`0x70 0x01 0x01 0x02 | 0x10 0x01 0x01 0x02 %k | 0x11 0x01 0x01 -0x02 0x00 | 0x91 | 0xa1`.
`m.resetToDefault()`: `0x10 0x01 0x01 0x01 0x02 | 0x11 0x02 | 0x91` (a set: the same with its index).

## List (`LedgerList` in Lean)

Stored as `[head, tail, length]`, the empty list `[null, null, {8: 0}]`
(compactc's `initialState` pushes exactly that array).

| Op | Sequence |
|---|---|
| `pushFront x` | `idx pushPath f; dup 0; idx [{1:2}]; addi 1; push! [cell x, null, null]; swap 0; push {1:2}; swap 0; ins cached 1; swap 0; push {1:1}; swap 0; ins cached (L+1)` |
| `popFront` | `idx pushPath f; idx [{1:1}]; ins cached L` |
| `head` | `dup 0; idx f; idx [{1:0}]; dup 0; type; push {1:1}; eq; branch 4; push {1:1}; swap 0; concat (2 + maxAlignedSize T); jmp 2; pop; push {[1, T]: 0, zero}; popeq cached [bytes 1, T]` |
| `length` | `dup 0; idx f; idx [{1:2}]; popeq cached [bytes 8]` |
| `isEmpty` | `dup 0; idx f; idx [{1:1}]; type; push {1:1}; eq; popeq cached [bytes 1]` |
| `resetToDefault` | reset with `[null, null, {8: 0}]` |

`l.pushFront(disclose(x))` on `List<Field>` at index 0:
```
0x70 0x01 0x01 0x00 | 0x30 | 0x50 0x01 0x01 0x02 | 0x0e 0x01
0x11 0x33 0x01 0x01 -0x02 %x 0x00 0x00 | 0x40 | 0x10 0x01 0x01 0x01 0x02 | 0x40 | 0xa1
0x40 | 0x10 0x01 0x01 0x01 0x01 | 0x40 | 0xa2
```
`l.head()`:
```
0x30 | 0x50 0x01 0x01 0x00 | 0x50 0x01 0x01 0x00 | 0x30 | 0x03 | 0x10 0x01 0x01 0x01 0x01 | 0x02
0x12 0x04 | 0x10 0x01 0x01 0x01 0x01 | 0x40 | 0x16 0x26 | 0x13 0x02 | 0x0b
0x10 0x01 0x02 0x01 -0x02 0x00 0x00 | 0x0d 0x02 0x01 -0x02 %t0 %t1
```
The `concat` size is compactc's `2 + maxAlignedSize(T.alignment())`, a JS
expression in `index.js` and a constant in the ZKIR. Observed constants:
`0x26` for `Field`, `0x27` for `Bytes<32>`, `0x09` for `Uint<16>`. Damp's
`maxAlignedSize` reproduces the runtime's: 2 plus 34 per field atom and
`n + 2 + max 1 (bytes to write n)` per `n`-byte atom, checked against
`rt.maxAlignedSize` for bytes 0..20000 and for multi-atom alignments.

## MerkleTree and HistoricMerkleTree

Stored as `[tree, firstFree]`, historic as `[tree, firstFree, pastRoots]`.
A leaf is `persistentHash` under the alignment `[bytes 6, T]` of
`"mdn:lh"` followed by the value:
```
persistent_hash alignment [bytes 6, field] inputs ["0x6d646e3a6c68", %x]
bytes_into_natives -> %h0 %h1      (pushed as %h1 %h0: high limb first)
```
compactc does not share this hash between two inserts of the same value;
Damp's emitter shares syntactically equal hashes, so the examples insert
different values (see "Differences" below).

| Op | Sequence |
|---|---|
| `insert x` / `insertHash h` | `idx pushPath f; idx pushPath [{1:0}]; dup 2; idx [{1:1}]; push! {32: leaf}; ins false 1; ins cached 1; idx pushPath [{1:1}]; addi 1;` then `ins cached (L+1)` |
| `insertIndex x i` / `insertHashIndex h i` | `idx pushPath f; idx pushPath [{1:0}]; push {8:i}; push! {32: leaf}; ins false 2; idx pushPath [{1:1}]; push {8:i}; addi 1; dup 1; dup 1; lt; branch 2; pop; jmp 2; swap 0; pop; ins false 1;` then `ins cached L` |
| `insertIndexDefault i` | `insertIndex` of the zero value (hash of constants, computed in the circuit) |
| `isFull` | `dup 0; idx f; idx [{1:1}]; push {8: 2^depth}; lt; neg; popeq cached [bytes 1]` |
| `checkRoot r` | `dup 0; idx f; idx [{1:0}]; root; push {field: r}; eq; popeq cached [bytes 1]` |
| `resetToDefault` | reset with `[tree(depth), {8: 0}]` |

Historic: the same, except
- after `insert`/`insertHash` the tail is `ins cached 1; R; ins cached (L+1)`,
  and after the `insertIndex` family `R; ins cached (L+1)`, where `R`
  records the new root: `idx pushPath [{1:2}]; dup 2; idx [{1:0}]; root; push! null; ins false 1`;
- `checkRoot r` is `dup 0; idx f; idx [{1:2}]; push {field: r}; member; popeq cached [bytes 1]`;
- `resetHistory` is `idx pushPath f; push {1:2}; push! {}; dup 2; idx [{1:0}]; root; push! null; ins cached (L+2)`;
- `resetToDefault` uses the extra `idx pushPath [{1:2}]; dup 2; idx [{1:0}]; root; push! null; ins cached 2`
  before `ins false 1`, and the initial state of a top-level field gets the
  same treatment in compactc's `initialState` (the executor reproduces it).
  `insertDefault` into a `Map<_, HistoricMerkleTree>` does *not* record the
  root (observed: `0x70 … | 0x10 … %k | 0x11 0x33 0x44 0x01 0x01 0x08 0x00 0x02 | 0x91 | 0xa1`).

Evidence, `MerkleTree<4, Field>` at index 1:
- `t.insert(disclose(x))`: `0x70 0x01 0x01 0x01 | 0x70 0x01 0x01 0x00 | 0x32 | 0x50 0x01 0x01 0x01 | 0x11 0x01 0x01 0x20 %h1 %h0 | 0x91 | 0xa1 | 0x70 0x01 0x01 0x01 | 0x0e 0x01 | 0xa2`
- `t.insertIndex(disclose(x), disclose(i))`: `0x70 … 0x01 | 0x70 … 0x00 | 0x10 0x01 0x01 0x08 %i | 0x11 0x01 0x01 0x20 %h1 %h0 | 0x92 | 0x70 0x01 0x01 0x01 | 0x10 0x01 0x01 0x08 %i | 0x0e 0x01 | 0x31 | 0x31 | 0x01 | 0x12 0x02 | 0x0b | 0x13 0x02 | 0x40 | 0x0b | 0x91 | 0xa1`
- `t.isFull()`: `0x30 | 0x50 0x01 0x01 0x01 | 0x50 0x01 0x01 0x01 | 0x10 0x01 0x01 0x08 0x10 | 0x01 | 0x08 | 0x0d 0x01 0x01 %t` (depth 20: `0x000010`)
- `t.checkRoot(disclose(r))`: `0x30 | 0x50 0x01 0x01 0x01 | 0x50 0x01 0x01 0x00 | 0x0a | 0x10 0x01 0x01 -0x02 %r | 0x02 | 0x0d 0x01 0x01 %t`
- `HistoricMerkleTree<4, Field>` at 2, `h.resetHistory()`: `0x70 0x01 0x01 0x02 | 0x10 0x01 0x01 0x01 0x02 | 0x11 0x02 | 0x32 | 0x50 0x01 0x01 0x00 | 0x0a | 0x11 0x00 | 0xa3`

`MerkleTreeDigest` (`{field: Field}`) and `ContractAddress`
(`{bytes: Bytes<32>}`) are provided as Lean structures with the struct shapes
compactc's JS uses.

Not circuit operations in Compact, so skipped: `root`, `firstFree`,
`pathForLeaf`, `findPathForLeaf`, `history`. A circuit that proves
membership takes a `MerkleTreePath<n, T>` from a witness (the leaf plus `n`
`{sibling: MerkleTreeDigest, goes_left: Boolean}` entries) and recomputes the
root with `merkleTreePathRoot`, then calls `checkRoot`. That needs the
standard library's path-root circuit (transient hashes over the path), which
is ordinary circuit code, not ledger code, and was not done here.

## Kernel

| Op | Sequence |
|---|---|
| `Kernel.self` | `dup 2; idx cached [{1:0}]; popeq cached [bytes 32]` |
| `Kernel.checkpoint` | `ckpt` |
| `blockTimeLt t` | `dup 2; idx cached [{1:2}]; push {8:t}; lt; popeq cached [bytes 1]` |
| `blockTimeGt t` | `push {8:t}; dup 3; idx cached [{1:2}]; lt; popeq cached [bytes 1]` |
| `blockTimeGte t`, `blockTimeLte t` | `not` of `Lt`, `Gt` (a `cond_select r 0 1` after the read, as in compactc) |

`kernel.self()`: `0x32 | 0x60 0x01 0x01 0x00 | 0x0d 0x01 0x20 %a0 %a1`.
`blockTimeLt(disclose(t))`: `0x32 | 0x60 0x01 0x01 0x02 | 0x10 0x01 0x01 0x08 %t | 0x01 | 0x0d 0x01 0x01 %r`.
`blockTimeGt(disclose(t))`: `0x10 0x01 0x01 0x08 %t | 0x33 | 0x60 0x01 0x01 0x02 | 0x01 | 0x0d 0x01 0x01 %r`.
`kernel.checkpoint()`: `0xff` (JS: `'ckpt'`).

The coin operations (`balance*`, `claim*`, `mint*`, `inc*Inputs/Outputs`) and
the new instruction they need (`idx` keyed from the stack) are in
[tokens.md](tokens.md), as are `writeCoin`, `insertCoin` and `pushFrontCoin`
(and the `idx` with literal and stack keys, and cached `concat`, they need).

## Maps of ledger ADTs

`Map<K, V>` where `V` is `Counter`, `Map`, `Set`, `List`, `MerkleTree` or
`HistoricMerkleTree`. In Lean, `(← m.lookup k)` returns a handle whose `path`
is `m.path ++ [k]` and emits nothing, exactly as compactc emits nothing for
`m.lookup(k)` until an operation is applied; all the sequences above are
written against `f` and `L`, and the counts were observed at `L = 1, 2, 3`:

- `mc.lookup(k).lookup(j).increment(n)`: `0x72 0x01 0x01 0x00 0x01 -0x02 %k 0x01 -0x02 %j | 0x0e %n | 0xa3`
- `ml.lookup(k).pushFront(x)` (`List` at L = 2) ends with `0xa3` (`L+1`); `mt.lookup(k).insert(x)` ends with `0xa3`, `mt.lookup(k).insertIndex(x, i)` with `0xa2`; `mh.lookup(k).resetHistory()` with `0xa4`
- `mc.insertDefault(k)` on `Map<Field, Map<Field, Counter>>`: `0x70 0x01 0x01 0x00 | 0x10 0x01 0x01 -0x02 %k | 0x11 0x02 | 0x91 | 0xa1`
- `ms.lookup(k).remove(x)`: `0x71 0x01 0x01 0x01 0x01 -0x02 %k | 0x10 0x01 0x01 -0x02 %x | 0x19 | 0xa2`

The exported contract describes such a field as `{"kind": "mapOf", "key",
"value": <kind>}`; its initial state is an empty map.

## Differences from compactc

- Persistent-hash sharing: inserting the same value twice into Merkle trees
  in one circuit computes the leaf hash twice in compactc and once in Damp
  (the emitter shares equal expressions). The circuits are equivalent but the
  verifier keys differ; the examples avoid the case.
- `resetToDefault` on a tree of depth over 15 is rejected by Damp; compactc
  crashes on it.
- `List` is called `LedgerList` in Lean, to leave Lean's `List` alone.
- `Map.lookup` on an ADT value is a `CircuitM` action (`(← m.lookup k).op`)
  rather than a pure expression, so that one `lookup` serves both plain and
  ADT values.
