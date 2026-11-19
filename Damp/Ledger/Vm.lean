/-
A model of Midnight's on-chain VM (the "Impact" VM) on the fragment Damp emits.

The authority is the Rust implementation in midnightntwrk/midnight-ledger at
tag `onchain-runtime-4.0.2` (the version of `@midnightntwrk/onchain-runtime-v4`
the executor runs):

* `onchain-vm/src/vm.rs`, `run_program_internal`: the semantics of every
  instruction (cited per instruction below as `vm.rs`);
* `onchain-state/src/state.rs`: `StateValue`;
* `base-crypto/src/fab/*.rs`: aligned values (`AlignedValue`, `ValueAtom`),
  their conversions (`conversions.rs`) and serialized sizes (`serialize.rs`);
* `onchain-runtime/src/context.rs`, `QueryContext::query`: how a request is
  run against a contract (modelled in `Damp/Ledger/Query.lean`).

The model is validated against the real VM by a differential test
(`test/vm.sh`, `Test/Vm.lean`, `executor/test/vm-vectors.mjs`), see
`docs/ledger-model.md`.

## What is modelled exactly

* State values: null, cells, maps, arrays, bounded Merkle trees (as their
  height and leaf hashes).
* Aligned values: an alignment and its atoms. An atom is a byte string with no
  trailing zero byte (Rust normalises them, `ValueAtom::normalize`), so it is
  represented by the natural number those bytes encode little-endian. Two atoms
  are equal exactly when their numbers are.
* The stack, with each entry's strength (strong values may be stored, weak ones
  may not) and its cache key.
* The read cache (`Cache`, `InnerCache`, `CacheKey` in `vm.rs`): which parts of
  the initial stack values a cached instruction may touch. A cached `idx`,
  `ins` or `rem` fails on a miss exactly as in Rust.
* Failure: every case where `run_program_internal` returns an error is `none`,
  including running off the stack, type errors, arithmetic overflow, out of
  range indices, cache misses, oversized `concat`/`eq` operands, and jumping
  past the end of the program.
* The `read` events of `popeq` (in gathering mode, `ResultModeGather`), in order.

## What is abstracted

* Gas: not modelled. The runtime is run without a gas limit by Damp's executor
  (`QueryContext.query(ops, costModel, gasLimit)` with no limit), so it never
  fails for gas.
* Merkle tree roots: the `root` instruction is a parameter of the model
  (`Hooks.root`), since computing it needs the tree's (Poseidon) node hashes.
  Inserting leaves, indexing, `size` and `type` of trees are modelled.
* `log`: pops its operand; the events it emits and the 512 kB bound on its
  serialization are not modelled (Damp never emits `log`).
* `rem` on a Merkle tree (Damp never emits it): modelled as overwriting the
  leaf with the zero hash, failing out of range; not validated.
* The stack height limit (2^16) is checked; the cell size bound (2^15 bytes)
  on pushed cells is not.
* Atoms are assumed normalised and aligned values well formed (every value the
  executor builds is; a `Compress` atom, which Rust does not normalise, never
  occurs in a Damp ledger instruction).
* The `noop` and `new` instructions are not in Damp's instruction set
  (`Damp/IR/Impact.lean`) and are not modelled.

## From Damp's instructions to the VM's

`Op Fr` (Damp's instructions, operands evaluated) is turned into the VM's own
instructions (`ROp`) the way the executor does it (`runtimeOp` and
`alignedOfFields` in `executor/src/executor.mjs`): each aligned operand's field
elements become atoms, and the runtime checks each value against its
alignment while decoding the program. As in the runtime, the whole program is
decoded before any instruction runs, so an invalid operand anywhere makes the
request fail.
-/
import Damp.IR.Impact
import Damp.Field

namespace Damp.Ledger
open Damp.Zkir (AlignAtom)
open Damp.Impact

/-! ## Aligned values -/

/-- An `AlignedValue`: an alignment and one atom per alignment atom, each atom
    the little-endian number its (normalised) bytes encode. -/
structure AV where
  align : List AlignAtom
  atoms : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- The number of bytes of a normalised atom: no trailing zero bytes, so 0 has none. -/
def byteLen (x : Nat) : Nat := if x = 0 then 0 else x.log2 / 8 + 1

/-- `AlignmentAtom::fits` (`base-crypto/src/fab/encoding.rs`) on a normalised atom. -/
def atomFits : AlignAtom → Nat → Bool
  | .bytes n, x => x < 2 ^ (8 * n)
  | .field, x => byteLen x ≤ 64
  | .compress, _ => true

/-- `Alignment::fits`, for alignments made of atoms (the only ones Damp uses). -/
def AV.valid (v : AV) : Bool :=
  v.align.length == v.atoms.length && (v.align.zip v.atoms).all fun (a, x) => atomFits a x

/-- `From<u64> for AlignedValue`: alignment `[bytes 8]`. -/
def AV.ofU64 (n : Nat) : AV := ⟨[.bytes 8], [n]⟩
/-- `From<u8>`: alignment `[bytes 1]`. -/
def AV.ofU8 (n : Nat) : AV := ⟨[.bytes 1], [n]⟩
/-- `From<bool>`: one byte, `0x01` or the empty atom. -/
def AV.ofBool (b : Bool) : AV := ⟨[.bytes 1], [if b then 1 else 0]⟩
/-- `From<HashOutput>`: alignment `[bytes 32]`. -/
def AV.ofHash (h : Nat) : AV := ⟨[.bytes 32], [h]⟩

/-- `TryFrom<&ValueSlice> for u64` (`conversions.rs`): exactly one atom, read as
    a `u128` (at most 16 bytes) and then narrowed to `u64`. -/
def AV.toU64 (v : AV) : Option Nat :=
  match v.atoms with
  | [x] => if x < 2 ^ 64 then some x else none
  | _ => none

/-- `TryFrom<&ValueSlice> for u8`. -/
def AV.toU8 (v : AV) : Option Nat :=
  match v.atoms with
  | [x] => if x < 2 ^ 8 then some x else none
  | _ => none

/-- `TryFrom<&ValueSlice> for bool`: a `u8` that is 0 or 1. -/
def AV.toBool (v : AV) : Option Bool :=
  match v.atoms with
  | [0] => some false
  | [1] => some true
  | _ => none

/-- `TryFrom<&ValueSlice> for HashOutput`: one atom of at most 32 bytes. -/
def AV.toHash (v : AV) : Option Nat :=
  match v.atoms with
  | [x] => if x < 2 ^ 256 then some x else none
  | _ => none

/-! ### Serialized sizes (`base-crypto/src/fab/serialize.rs`) -/

/-- `flagged_int_size`. -/
def flaggedIntSize (i : Nat) : Nat :=
  if i ≤ 31 then 1 else if i ≤ 4095 then 2 else if i ≤ 2 ^ 19 - 1 then 3 else 1000

/-- `ValueAtom::serialized_size`, for a normalised atom. -/
def atomSize (x : Nat) : Nat :=
  if byteLen x = 1 ∧ x < 32 then flaggedIntSize x else flaggedIntSize (byteLen x) + byteLen x

def alignAtomSize : AlignAtom → Nat
  | .bytes n => flaggedIntSize n
  | .field | .compress => 1

/-- `Serializable::serialized_size` for `AlignedValue`: the value, then the alignment. -/
def AV.size (v : AV) : Nat :=
  let value := match v.atoms with
    | [x] => atomSize x
    | xs => flaggedIntSize xs.length + (xs.map atomSize).sum
  let align := match v.align with
    | [a] => alignAtomSize a
    | as => flaggedIntSize as.length + (as.map alignAtomSize).sum
  value + align

/-! ## State values (`onchain-state/src/state.rs`, `StateValue`) -/

inductive SV where
  | null
  | cell (v : AV)
  /-- A map, as a list of entries with distinct keys (order irrelevant). -/
  | map (entries : List (AV × SV))
  | array (elems : List SV)
  /-- A bounded Merkle tree: its height and its leaves (index, hash). -/
  | bmt (height : Nat) (leaves : List (Nat × Nat))
  deriving Repr, Inhabited

/-- `StateValue::as_cell`. -/
def SV.asCell : SV → Option AV
  | .cell v => some v
  | _ => none

/-- Replace or add an entry of an association list. -/
def assocSet {κ ν : Type} [DecidableEq κ] (k : κ) (v : ν) : List (κ × ν) → List (κ × ν)
  | [] => [(k, v)]
  | (k', v') :: rest => if k' = k then (k, v) :: rest else (k', v') :: assocSet k v rest

/-- Remove an entry of an association list. -/
def assocErase {κ ν : Type} [DecidableEq κ] (k : κ) : List (κ × ν) → List (κ × ν)
  | [] => []
  | (k', v') :: rest => if k' = k then rest else (k', v') :: assocErase k rest

/-- Look up an entry of an association list. -/
def assocGet {κ ν : Type} [DecidableEq κ] (k : κ) : List (κ × ν) → Option ν
  | [] => none
  | (k', v) :: rest => if k' = k then some v else assocGet k rest

/-! ## The read cache (`Cache`, `InnerCache`, `CacheKey` in `vm.rs`) -/

/-- `InnerCache`: `full` is `InnerCache(None)`, everything below is cached;
    `part` maps keys to the cached parts below them. -/
inductive CTree where
  | full
  | part (children : List (AV × CTree))
  deriving Inhabited

/-- `Cache::visit` on one root: mark the path as visited; whether it was. -/
def CTree.visit : CTree → List AV → CTree × Bool
  | .full, _ => (.full, true)
  | .part cs, [] => (.part cs, true)
  | .part cs, k :: ks =>
      match assocGet k cs with
      | some c => let r := c.visit ks; (.part (assocSet k r.1 cs), r.2)
      | none => let r := (CTree.part []).visit ks; (.part (assocSet k r.1 cs), false)

/-- `Cache::contains` on one root. -/
def CTree.contains : CTree → List AV → Bool
  | .full, _ => true
  | .part _, [] => true
  | .part cs, k :: ks =>
      match assocGet k cs with
      | some c => c.contains ks
      | none => false

/-- `Cache::get` on one root. -/
def CTree.get : CTree → List AV → CTree
  | .full, _ => .full
  | .part cs, [] => .part cs
  | .part cs, k :: ks =>
      match assocGet k cs with
      | some c => c.get ks
      | none => .part []

/-- `CacheKey`: `none` is `CacheKey(None)` (fully cached), `some (n, path)` the
    part of initial value (cache root) `n` at `path`. -/
abbrev CKey := Option (Nat × List AV)

def CKey.push (k : CKey) (key : AV) : CKey := k.map fun (n, p) => (n, p ++ [key])

/-- The cache: one tree per root, indexed from 0. -/
abbrev Cache := List CTree

def Cache.visit (c : Cache) : CKey → Cache × Bool
  | none => (c, true)
  | some (n, p) =>
      match c[n]? with
      | none => (c, false)
      | some t => let r := t.visit p; (c.set n r.1, r.2)

def Cache.contains (c : Cache) : CKey → Bool
  | none => true
  | some (n, p) =>
      match c[n]? with
      | none => false
      | some t => t.contains p

def Cache.get (c : Cache) : CKey → CTree
  | none => .full
  | some (n, p) =>
      match c[n]? with
      | none => .part []
      | some t => t.get p

/-- `Cache::key_for`: a fully cached tree needs no root; any other becomes a new one. -/
def Cache.keyFor (c : Cache) : CTree → Cache × CKey
  | .full => (c, none)
  | t => (c ++ [t], some (c.length, []))

/-! ## The machine -/

/-- A stack entry: a value, its strength (`ValueStrength::Strong`), its cache key. -/
structure Entry where
  val : SV
  strong : Bool
  key : CKey
  deriving Inhabited

structure VmState where
  /-- The stack, top first. -/
  stack : List Entry
  cache : Cache
  /-- The values `popeq` read, in order. -/
  reads : List AV := []
  deriving Inhabited

/-- `run_program_step_limited`'s set-up: `initial` lists the values bottom
    first with their strengths; value `i` gets cache root `i`, fully cached if
    it is weak. -/
def VmState.init (initial : List (SV × Bool)) : VmState where
  stack := ((initial.zipIdx).map fun ((v, strong), i) => ({ val := v, strong, key := some (i, []) } : Entry)).reverse
  cache := initial.map fun (_, strong) => if strong then .part [] else .full

/-- The VM's own instructions (`onchain-vm/src/ops.rs`, `Op`), in gathering
    mode (a `popeq` carries no expected result). -/
inductive Key where
  | value (v : AV)
  | stack
  deriving Inhabited

inductive ROp where
  | lt | eq | type | size | and | or | neg | log | root | pop
  | popeq (cached : Bool)
  | addi (imm : Nat)
  | subi (imm : Nat)
  | push (storage : Bool) (value : SV)
  | branch (skip : Nat)
  | jmp (skip : Nat)
  | add | sub
  | concat (cached : Bool) (n : Nat)
  | member
  | rem (cached : Bool)
  | dup (n : Nat)
  | swap (n : Nat)
  | idx (cached pushPath : Bool) (path : List Key)
  | ins (cached : Bool) (n : Nat)
  | ckpt
  deriving Inhabited

/-- How many stack entries an instruction needs (`stack_req` in `vm.rs`). -/
def ROp.stackReq : ROp → Nat
  | .push .. | .jmp _ | .ckpt => 0
  | .type | .size | .neg | .log | .root | .pop | .popeq _ | .addi _ | .subi _ | .branch _ => 1
  | .lt | .eq | .and | .or | .add | .sub | .concat .. | .member | .rem _ => 2
  | .dup n => n + 1
  | .swap n => n + 2
  | .idx _ _ path => (path.filter fun | .stack => true | _ => false).length + 1
  | .ins _ n => 2 * n + 1

/-- What the model leaves open: the root of a bounded Merkle tree of a given
    height with given leaves (`MerkleTree::root`). -/
structure Hooks where
  root : Nat → List (Nat × Nat) → Option AV

/-- `CELL_BOUND` (`onchain-state/src/state.rs`). -/
def cellBound : Nat := 2 ^ 15

/-- `MAX_STACK_HEIGHT` (`vm.rs`). -/
def maxStackHeight : Nat := 2 ^ 16

section Exec
variable (H : Hooks)

namespace VmState
def pop (s : VmState) : Option (Entry × VmState) :=
  match s.stack with
  | e :: es => some (e, { s with stack := es })
  | [] => none

def push (s : VmState) (e : Entry) : VmState := { s with stack := e :: s.stack }

/-- Push a freshly computed value: strong, with cache key `None`. -/
def pushNew (s : VmState) (v : SV) : VmState := s.push { val := v, strong := true, key := none }

def popCell (s : VmState) : Option (AV × VmState) := do
  let (e, s) ← s.pop
  let v ← e.val.asCell
  pure (v, s)

def popU64 (s : VmState) : Option (Nat × VmState) := do
  let (v, s) ← s.popCell
  let x ← v.toU64
  pure (x, s)

def popBool (s : VmState) : Option (Bool × VmState) := do
  let (v, s) ← s.popCell
  let b ← v.toBool
  pure (b, s)
end VmState

/-- `idx` (the free function in `vm.rs`): one step down `curr` along `key`. -/
def idxOne (cache : Cache) (curr : Entry) (key : AV) (cached : Bool) : Option (Cache × Entry) := do
  let ck := curr.key.push key
  let (cache, found) := cache.visit ck
  if cached && !found then none
  let res ← match curr.val with
    | .array es => do
        let i ← key.toU8
        es[i]?
    | .map m => some ((assocGet key m).getD .null)
    | .bmt h leaves => do
        let i ← key.toU64
        if h < 64 ∧ 2 ^ h ≤ i then none
        else some (match assocGet i leaves with
          | some hash => .cell (AV.ofHash hash)
          | none => .null)
    | _ => none
  pure (cache, { val := res, strong := curr.strong, key := ck })

/-- The walk of `Op::Idx` along the refined path. -/
def idxWalk (cached pushPath : Bool) : List Entry → VmState → Entry → Option VmState
  | [], s, curr => some (s.push curr)
  | key :: keys, s, curr => do
      let s := if pushPath then (s.push curr).push { key with key := none } else s
      let k ← key.val.asCell
      let (cache, curr) ← idxOne s.cache curr k cached
      idxWalk cached pushPath keys { s with cache } curr

/-- The merge of cache trees in `Op::Ins`. -/
def insCache (container : CTree) (key : AV) (inserted : CTree) : CTree :=
  match container, inserted with
  | .full, .full => .full
  | .full, t => .part [(key, t)]
  | .part m, t => .part (assocSet key t m)

/-- The loop of `Op::Ins`: insert `curr` into the container below it, `n` times. -/
def insLoop (cached : Bool) : Nat → VmState → Entry → CTree → Option (VmState × Entry × CTree)
  | 0, s, curr, cc => some (s, curr, cc)
  | n + 1, s, curr, cc => do
      let (key, s) ← s.pop
      let (container, s) ← s.pop
      let k ← key.val.asCell
      let hit := s.cache.contains (container.key.push k)
      let isArray := match container.val with | .array _ => true | _ => false
      if cached && !hit && !isArray then none
      let next ← match container.val with
        | .array es => do
            let i ← k.toU8
            if i < es.length then some (SV.array (es.set i curr.val)) else none
        | .map m => some (SV.map (assocSet k curr.val m))
        | .bmt h leaves => do
            let i ← k.toU64
            if h < 64 ∧ 2 ^ h ≤ i then none
            else do
              let c ← curr.val.asCell
              let hash ← c.toHash
              some (SV.bmt h (assocSet i hash leaves))
        | _ => none
      let curr : Entry := { val := next, strong := curr.strong && container.strong, key := curr.key }
      let cc := insCache (s.cache.get container.key) k cc
      insLoop cached n s curr cc

/-- `Op::Type`'s tag. -/
def typeTag : SV → Option Nat
  | .cell _ => some 0
  | .null => some 1
  | .map _ => some 2
  | .array es => if es.length > 16 then none else some (3 + es.length * 8)
  | .bmt h _ => some ((4 + (h - 1) * 8) % 256)

/-- One instruction (`run_program_internal`, one iteration of the loop): the
    state after it and how many of the following instructions to skip. The
    stack requirement is checked first, as in Rust. -/
def ROp.exec (s : VmState) (op : ROp) : Option (VmState × Nat) := do
  if s.stack.length < op.stackReq then none
  match op with
  -- vm.rs `Lt`: pops b then a, both u64.
  | .lt => do
      let (b, s) ← s.popU64
      let (a, s) ← s.popU64
      pure (s.pushNew (.cell (AV.ofBool (decide (a < b)))), 0)
  -- vm.rs `Eq` and `fn eq`: operands of over 64 serialized bytes compare unequal
  -- to short ones, and two long ones are an error.
  | .eq => do
      let (a, s) ← s.popCell
      let (b, s) ← s.popCell
      let r ← match decide (a.size ≤ 64), decide (b.size ≤ 64) with
        | false, false => none
        | true, true => some (decide (a = b))
        | _, _ => some false
      pure (s.pushNew (.cell (AV.ofBool r)), 0)
  -- vm.rs `Type`.
  | .type => do
      let (e, s) ← s.pop
      let t ← typeTag e.val
      pure (s.pushNew (.cell (AV.ofU8 t)), 0)
  -- vm.rs `Size`: entries of a map, height of a tree, length of an array.
  | .size => do
      let (e, s) ← s.pop
      let n ← match e.val with
        | .map m => some m.length
        | .bmt h _ => some h
        | .array es => some es.length
        | _ => none
      pure (s.pushNew (.cell (AV.ofU64 n)), 0)
  -- vm.rs `And`, `Or`, `Neg`: booleans.
  | .and => do
      let (a, s) ← s.popBool
      let (b, s) ← s.popBool
      pure (s.pushNew (.cell (AV.ofBool (a && b))), 0)
  | .or => do
      let (a, s) ← s.popBool
      let (b, s) ← s.popBool
      pure (s.pushNew (.cell (AV.ofBool (a || b))), 0)
  | .neg => do
      let (a, s) ← s.popBool
      pure (s.pushNew (.cell (AV.ofBool !a)), 0)
  -- vm.rs `Log`: events not modelled.
  | .log => do
      let (_, s) ← s.pop
      pure (s, 0)
  -- vm.rs `Root`: the root of a tree, through the hook.
  | .root => do
      let (e, s) ← s.pop
      let r ← match e.val with
        | .bmt h leaves => H.root h leaves
        | _ => none
      pure (s.pushNew (.cell r), 0)
  -- vm.rs `Pop`.
  | .pop => do
      let (_, s) ← s.pop
      pure (s, 0)
  -- vm.rs `Popeq` with `ResultModeGather`: record the cell read. `cached` has no effect.
  | .popeq _ => do
      let (v, s) ← s.popCell
      pure ({ s with reads := s.reads ++ [v] }, 0)
  -- vm.rs `Addi`, `fn add`: u64 arithmetic, overflow is an error.
  | .addi imm => do
      let (a, s) ← s.popU64
      if a + imm < 2 ^ 64 then pure (s.pushNew (.cell (AV.ofU64 (a + imm))), 0) else none
  -- vm.rs `Subi`, `fn sub`: going below zero is an error.
  | .subi imm => do
      let (a, s) ← s.popU64
      if imm ≤ a then pure (s.pushNew (.cell (AV.ofU64 (a - imm))), 0) else none
  -- vm.rs `Push`: strong when pushed to storage, weak otherwise.
  | .push storage v => pure (s.push { val := v, strong := storage, key := none }, 0)
  -- vm.rs: `Branch` pops its condition at the end of the step; it skips unless
  -- the condition is exactly one empty atom (false).
  | .branch skip => do
      let (v, s) ← s.popCell
      pure (s, if v.atoms = [0] then 0 else skip)
  | .jmp skip => pure (s, skip)
  -- vm.rs `Add`: a (top) + b; `Sub`: b - a.
  | .add => do
      let (a, s) ← s.popU64
      let (b, s) ← s.popU64
      if a + b < 2 ^ 64 then pure (s.pushNew (.cell (AV.ofU64 (a + b))), 0) else none
  | .sub => do
      let (a, s) ← s.popU64
      let (b, s) ← s.popU64
      if a ≤ b then pure (s.pushNew (.cell (AV.ofU64 (b - a))), 0) else none
  -- vm.rs `Concat`, `fn concat`: b (below) then a (top), bounded by `n` serialized bytes.
  | .concat _ n => do
      if n > cellBound then none
      let (a, s) ← s.popCell
      let (b, s) ← s.popCell
      if a.size + b.size ≤ n then
        pure (s.pushNew (.cell ⟨b.align ++ a.align, b.atoms ++ a.atoms⟩), 0)
      else none
  -- vm.rs `Member`: maps only.
  | .member => do
      let (k, s) ← s.popCell
      let (e, s) ← s.pop
      let r ← match e.val with
        | .map m => some (assocGet k m).isSome
        | _ => none
      pure (s.pushNew (.cell (AV.ofBool r)), 0)
  -- vm.rs `Rem`: the container keeps its strength and cache key.
  | .rem cached => do
      let (k, s) ← s.popCell
      let (c, s) ← s.pop
      if cached && !(s.cache.contains (c.key.push k)) then none
      let next ← match c.val with
        | .map m => some (SV.map (assocErase k m))
        | .bmt h leaves => do
            let i ← k.toU64
            if h < 64 ∧ 2 ^ h ≤ i then none else some (SV.bmt h (assocSet i 0 leaves))
        | _ => none
      pure (s.push { c with val := next }, 0)
  -- vm.rs `Dup`: a copy of entry `n` (0 the top), cache key included.
  | .dup n => do
      let e ← s.stack[n]?
      pure (s.push e, 0)
  -- vm.rs `Swap`: the top and entry `n + 1`.
  | .swap n => do
      let top ← s.stack[0]?
      let other ← s.stack[n + 1]?
      pure ({ s with stack := (s.stack.set 0 other).set (n + 1) top }, 0)
  -- vm.rs `Idx`: stack keys are popped first (the first one from the top), then
  -- the container; literal keys are weak cells.
  | .idx cached pushPath path => do
      let nStack := (path.filter fun | .stack => true | _ => false).length
      let stackKeys := s.stack.take nStack
      let s := { s with stack := s.stack.drop nStack }
      let refined := (path.foldl (fun (acc : List Entry × List Entry) k =>
        match k with
        | .stack => match acc.2 with
          | e :: rest => (acc.1 ++ [e], rest)
          | [] => (acc.1, [])
        | .value v => (acc.1 ++ [{ val := .cell v, strong := false, key := none }], acc.2))
        ([], stackKeys)).1
      let (curr, s) ← s.pop
      let s ← idxWalk cached pushPath refined s curr
      pure (s, 0)
  -- vm.rs `Ins`.
  | .ins cached n => do
      let (curr, s) ← s.pop
      let cc := s.cache.get curr.key
      let (s, curr, cc) ← insLoop cached n s curr cc
      let (cache, k) := s.cache.keyFor cc
      pure ({ s with cache, stack := { curr with key := k } :: s.stack }, 0)
  | .ckpt => pure (s, 0)

/-- Run a program (`run_program_internal`'s loop): after each instruction, skip
    as it says, failing if that runs past the end, or if the stack grew too high. -/
def runR : List ROp → VmState → Option VmState
  | [], s => some s
  | op :: rest, s => do
      let (s', k) ← op.exec H s
      if k > rest.length then none
      if s'.stack.length > maxStackHeight then none
      runR (rest.drop k) s'
termination_by ops => ops.length
decreasing_by simp_wf; omega

end Exec

/-! ## Damp's instructions as the VM's -/

/-- The number of field elements an atom occupies in a circuit: `ceil(n / 31)`
    for `n` bytes (at least one), one for a field element. -/
def atomWidth : AlignAtom → Nat
  | .bytes n => max 1 ((n + 30) / 31)
  | .field | .compress => 1

/-- Field elements to an atom (`alignedOfFields` in `executor.mjs`): more than
    31 bytes are limbs, most significant first, joined (`limbsToBytes`, which
    keeps `n` bytes); anything else is the one element's value. -/
def atomOfFields : AlignAtom → List Fr → Nat
  | .bytes n, limbs =>
      if n > 31 then (limbs.foldl (fun x l => (x <<< 248) ||| l.val) 0) % 2 ^ (8 * n)
      else (limbs.headD 0).val
  | _, limbs => (limbs.headD 0).val

/-- An aligned value from field elements, as the executor builds it; `none`
    when there are too few elements or the result does not fit its alignment
    (the runtime rejects it). Extra elements are ignored, as in the executor. -/
def AV.ofFields : List AlignAtom → List Fr → Option AV
  | [], _ => some ⟨[], []⟩
  | a :: as, vals =>
      if vals.length < atomWidth a then none
      else if !atomFits a (atomOfFields a (vals.take (atomWidth a))) then none
      else do
        let rest ← AV.ofFields as (vals.drop (atomWidth a))
        pure ⟨a :: rest.align, atomOfFields a (vals.take (atomWidth a)) :: rest.atoms⟩

def AV.ofAligned (v : Aligned Fr) : Option AV := AV.ofFields v.align v.vals

/-- The field elements of an atom read back (`fieldsOfAligned` in
    `executor.mjs`): limbs for more than 31 bytes (`bytesToLimbs`), otherwise
    the atom as one element (`valueToBigInt`, which must give a field element). -/
def fieldsOfAtom : AlignAtom → Nat → Option (List Fr)
  | .bytes n, x =>
      if n > 31 then
        let x := x % 2 ^ (8 * n)
        let count := (n + 30) / 31
        some ((List.range count).map fun j => Fr.ofNat ((x >>> (248 * (count - 1 - j))) % 2 ^ 248))
      else if h : x < Fr.modulus then some [⟨x, h⟩] else none
  | _, x => if h : x < Fr.modulus then some [⟨x, h⟩] else none

/-- The field elements a `popeq` with alignment `align` reads from `v`: one
    group per atom of `align` (the read value's own alignment is not
    consulted, as in the executor); `none` if `v` has too few atoms. -/
def fieldsOf : List AlignAtom → List Nat → Option (List Fr)
  | [], _ => some []
  | _ :: _, [] => none
  | a :: as, x :: xs => do
      let f ← fieldsOfAtom a x
      let rest ← fieldsOf as xs
      pure (f ++ rest)

mutual
/-- A state value written literally into an instruction (`stateValueOf` in `executor.mjs`). -/
def SV.ofLit : StateLit Fr → Option SV
  | .null => some .null
  | .cell v => return .cell (← AV.ofAligned v)
  | .emptyMap => some (.map [])
  | .array es => return .array (← SV.ofLitList es)
  | .emptyMerkleTree d => some (.bmt d [])
def SV.ofLitList : List (StateLit Fr) → Option (List SV)
  | [] => some []
  | e :: es => return (← SV.ofLit e) :: (← SV.ofLitList es)
end

/-- `addi`/`subi` immediates are `u32` in the VM; the runtime rejects larger ones. -/
def immOf (x : Fr) : Option Nat := if x.val < 2 ^ 32 then some x.val else none

/-- Damp's instruction as the VM's (`runtimeOp` in `executor.mjs`). -/
def Op.toR : Op Fr → Option ROp
  | .lt => some .lt | .eq => some .eq | .type => some .type | .size => some .size
  | .and => some .and | .or => some .or | .neg => some .neg | .log => some .log
  | .root => some .root | .pop => some .pop | .add => some .add | .sub => some .sub
  | .member => some .member | .ckpt => some .ckpt
  | .popeq cached _ _ => some (.popeq cached)
  | .addi i => return .addi (← immOf i)
  | .subi i => return .subi (← immOf i)
  | .push storage v => return .push storage (.cell (← AV.ofAligned v))
  | .pushNull storage => some (.push storage .null)
  | .rem cached => some (.rem cached)
  | .dup n => some (.dup n)
  | .swap n => some (.swap n)
  | .idx cached pushPath path => return .idx cached pushPath ((← path.mapM AV.ofAligned).map .value)
  | .ins cached n => some (.ins cached n)
  | .pushState storage v => return .push storage (← SV.ofLit v)
  | .branch n => some (.branch n)
  | .jmp n => some (.jmp n)
  | .concat n => some (.concat false n)
  | .idxStack pre => return .idx true false ((← pre.mapM AV.ofAligned).map .value ++ [.stack])
  | .concatCached n => some (.concat true n)

/-- One of Damp's instructions on its own. -/
def Op.run (H : Hooks) (s : VmState) (op : Op Fr) : Option VmState := do
  let r ← Op.toR op
  let (s, _) ← r.exec H s
  pure s

/-- A program of Damp's instructions: decoded as a whole, then run. -/
def runOps (H : Hooks) (ops : List (Op Fr)) (s : VmState) : Option VmState := do
  let rops ← ops.mapM Op.toR
  runR H rops s

end Damp.Ledger
