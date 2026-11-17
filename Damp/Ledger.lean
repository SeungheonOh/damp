/-
Ledger state types and their operations, as Impact instruction sequences.

The sequences follow `compiler/midnight-ledger.ss` in the Compact compiler and
were checked against compactc 0.36.1 output; `docs/ledger-types.md` records
the evidence for each. Every handle has an `index`, the top-level field it
lives under, and a `path`, the keys from the contract's state down to it:
`[index]` for a top-level field, longer for an ADT held in a `Map`.
-/
import Damp.Contract

namespace Damp
open IR Impact

inductive LedgerKind where
  | cell (shape : Shape)
  | counter
  | map (key value : Shape)
  /-- A map whose values are themselves ledger ADTs. -/
  | mapOf (key : Shape) (value : LedgerKind)
  | set (elem : Shape)
  | list (elem : Shape)
  | merkleTree (depth : Nat) (elem : Shape)
  | historicMerkleTree (depth : Nat) (elem : Shape)
  deriving Inhabited

structure LedgerField where
  name : String
  index : Nat
  kind : LedgerKind
  deriving Inhabited

/-- Types that can be declared as ledger fields. -/
class LedgerType (τ : Type) where
  /-- The handle for the field at this position. -/
  ofIndex : Nat → τ
  decl : τ → String → LedgerField

/-- The key selecting top-level ledger field `index`. -/
def fieldKey (index : Nat) : Aligned Expr :=
  { align := [.bytes 1], vals := [.const index] }

/-- The keys from the contract's state down to a ledger value. -/
abbrev LedgerPath := List (Aligned Expr)

/-- Element `i` of a ledger ADT that is stored as an array (`List`, the Merkle
    trees), and the kernel's slots: the same one-byte key as a field index. -/
private def slot (i : Nat) : Aligned Expr := fieldKey i

/-- A `Uint<64>` operand, as compactc writes counters, lengths and indices. -/
private def u64 (e : Expr) : Aligned Expr := { align := [.bytes 8], vals := [e] }

private def alignOf (α : Type) [Value α] : List Zkir.AlignAtom := (Value.tys α).map Ty.align

private def alignedOf [Value α] (x : α) : Aligned Expr :=
  { align := alignOf α, vals := Value.toExprs x }

private def ledgerOp (reads : List Var) (ops : List (Op Expr)) : CircuitM Unit := do
  emit (.ledger (← currentGuard) reads ops)

/-- Run `ops`, whose `popeq` reads a value of type `α`. -/
private def ledgerRead (α : Type) [Value α] (mkOps : List Expr → List (Op Expr)) : CircuitM α := do
  let vs ← (List.range (Value.width α)).mapM fun _ => freshVar
  let es := vs.map Expr.var
  ledgerOp vs (mkOps es)
  return Value.ofExprs es

/-- `ins cached n`, left out when `n = 0` (compactc's `suppress-zero`). -/
private def insCached (n : Nat) : List (Op Expr) := if n = 0 then [] else [.ins true n]

/-- Replace the value at `path` by `init`: every `resetToDefault`. `extra` runs
    with the new value on top of the stack, before it is stored. -/
private def resetOps (path : LedgerPath) (init : StateLit Expr) (extra : List (Op Expr) := []) :
    List (Op Expr) :=
  let parent := path.dropLast
  (if parent.isEmpty then [] else [.idx false true parent]) ++
  [.push false (path.getLast?.getD default), .pushState true init] ++ extra ++
  [.ins false 1] ++ insCached parent.length

/-! ## Cell -/

/-- A ledger field holding one value of type `α`. -/
structure Cell (α : Type) where
  index : Nat

instance [Value α] : LedgerType (Cell α) where
  ofIndex i := ⟨i⟩
  decl c name := { name, index := c.index, kind := .cell (Value.shape α) }

namespace Cell
def read [Value α] (c : Cell α) : CircuitM α :=
  ledgerRead α fun es => [
    .dup 0,
    .idx false false [fieldKey c.index],
    .popeq false (alignOf α) es]

def write [Value α] (c : Cell α) (x : α) : CircuitM Unit :=
  ledgerOp [] [
    .push false (fieldKey c.index),
    .push true (alignedOf x),
    .ins false 1]

/-- Write the type's default (all-zero) value: the same instructions as `write`. -/
def resetToDefault [Value α] (c : Cell α) : CircuitM Unit :=
  c.write (Value.zero α)
end Cell

/-! ## Counter -/

structure Counter where
  index : Nat
  path : LedgerPath := [fieldKey index]

instance : LedgerType Counter where
  ofIndex i := { index := i }
  decl c name := { name, index := c.index, kind := .counter }

namespace Counter
def increment (c : Counter) (amount : Uint16) : CircuitM Unit :=
  ledgerOp [] [
    .idx false true c.path,
    .addi amount.expr,
    .ins true c.path.length]

def read (c : Counter) : CircuitM Uint64 :=
  ledgerRead Uint64 fun es => [
    .dup 0,
    .idx false false c.path,
    .popeq true [.bytes 8] es]

/-- Fails the transaction if the counter would go below zero. -/
def decrement (c : Counter) (amount : Uint16) : CircuitM Unit :=
  ledgerOp [] [
    .idx false true c.path,
    .subi amount.expr,
    .ins true c.path.length]

def lessThan (c : Counter) (threshold : Uint64) : CircuitM Boolean :=
  ledgerRead Boolean fun es => [
    .dup 0,
    .idx false false c.path,
    .push false (u64 threshold.expr),
    .lt,
    .popeq true [.bytes 1] es]

def initial : StateLit Expr := .cell (u64 (.const 0))

def resetToDefault (c : Counter) : CircuitM Unit :=
  ledgerOp [] (resetOps c.path initial)
end Counter

/-! ## Map values

A map holds either plain values or other ledger ADTs. For an ADT, `lookup`
emits nothing: it names the nested value, and its operations run on the longer
path, as in Compact's `m.lookup(k).increment(1)`. -/

/-- What a `Map` can hold. -/
class MapValue (ν : Type) where
  /-- How the value is described in the exported contract; a plain value is a `.cell`. -/
  kind : LedgerKind
  /-- What `insertDefault` stores. -/
  initial : StateLit Expr
  /-- `lookup` of `key` in the map at `path` (whose top-level field is `index`). -/
  lookup : Nat → LedgerPath → Aligned Expr → CircuitM ν

instance [Value ν] : MapValue ν where
  kind := .cell (Value.shape ν)
  initial := .cell (alignedOf (Value.zero ν))
  lookup _ path k := ledgerRead ν fun es => [
    .dup 0,
    .idx false false path,
    .idx false false [k],
    .popeq false (alignOf ν) es]

instance : MapValue Counter where
  kind := .counter
  initial := Counter.initial
  lookup i path k := pure { index := i, path := path ++ [k] }

/-- The kind of a map from `key` to values of kind `value`. -/
def mapKind (key : Shape) : LedgerKind → LedgerKind
  | .cell sh => .map key sh
  | k => .mapOf key k

/-! ## Map -/

/-- A ledger map from `κ` to `ν`: plain values, or ledger ADTs (`MapValue`). -/
structure Map (κ ν : Type) where
  index : Nat
  path : LedgerPath := [fieldKey index]

instance [Value κ] [MapValue ν] : LedgerType (Map κ ν) where
  ofIndex i := { index := i }
  decl m name := { name, index := m.index, kind := mapKind (Value.shape κ) (MapValue.kind ν) }

instance [Value κ] [MapValue ν] : MapValue (Map κ ν) where
  kind := mapKind (Value.shape κ) (MapValue.kind ν)
  initial := .emptyMap
  lookup i path k := pure { index := i, path := path ++ [k] }

namespace Map
variable [Value κ]

def member (m : Map κ ν) (k : κ) : CircuitM Boolean :=
  ledgerRead Boolean fun es => [
    .dup 0,
    .idx false false m.path,
    .push false (alignedOf k),
    .member,
    .popeq true [.bytes 1] es]

/-- The value at `k`. For a plain value the transaction fails if `k` is
    absent; for a nested ADT this only names it. -/
def lookup [MapValue ν] (m : Map κ ν) (k : κ) : CircuitM ν :=
  MapValue.lookup m.index m.path (alignedOf k)

def insert [Value ν] (m : Map κ ν) (k : κ) (v : ν) : CircuitM Unit :=
  ledgerOp [] [
    .idx false true m.path,
    .push false (alignedOf k),
    .push true (alignedOf v),
    .ins false 1,
    .ins true m.path.length]

def remove (m : Map κ ν) (k : κ) : CircuitM Unit :=
  ledgerOp [] [
    .idx false true m.path,
    .push false (alignedOf k),
    .rem false,
    .ins true m.path.length]

def size (m : Map κ ν) : CircuitM Uint64 :=
  ledgerRead Uint64 fun es => [
    .dup 0,
    .idx false false m.path,
    .size,
    .popeq true [.bytes 8] es]

def isEmpty (m : Map κ ν) : CircuitM Boolean :=
  ledgerRead Boolean fun es => [
    .dup 0,
    .idx false false m.path,
    .size,
    .push false { align := [.bytes 8], vals := [.const 0] },
    .eq,
    .popeq true [.bytes 1] es]

/-- Store the value type's default at `k`: zero for a plain value, the
    initial state for an ADT. For a plain value these are the instructions of
    `insert k 0`. -/
def insertDefault [MapValue ν] (m : Map κ ν) (k : κ) : CircuitM Unit :=
  ledgerOp [] [
    .idx false true m.path,
    .push false (alignedOf k),
    .pushState true (MapValue.initial ν),
    .ins false 1,
    .ins true m.path.length]

/-- Make the map empty. -/
def resetToDefault (m : Map κ ν) : CircuitM Unit :=
  ledgerOp [] (resetOps m.path .emptyMap)
end Map

/-! ## Set -/

/-- A ledger set of `α`. -/
structure Set (α : Type) where
  index : Nat
  path : LedgerPath := [fieldKey index]

instance [Value α] : LedgerType (Set α) where
  ofIndex i := { index := i }
  decl s name := { name, index := s.index, kind := .set (Value.shape α) }

instance [Value α] : MapValue (Set α) where
  kind := .set (Value.shape α)
  initial := .emptyMap
  lookup i path k := pure { index := i, path := path ++ [k] }

namespace Set
variable [Value α]

def member (s : Set α) (x : α) : CircuitM Boolean :=
  ledgerRead Boolean fun es => [
    .dup 0,
    .idx false false s.path,
    .push false (alignedOf x),
    .member,
    .popeq true [.bytes 1] es]

def insert (s : Set α) (x : α) : CircuitM Unit :=
  ledgerOp [] [
    .idx false true s.path,
    .push false (alignedOf x),
    .pushNull true,
    .ins false 1,
    .ins true s.path.length]

def remove (s : Set α) (x : α) : CircuitM Unit :=
  ledgerOp [] [
    .idx false true s.path,
    .push false (alignedOf x),
    .rem false,
    .ins true s.path.length]

def size (s : Set α) : CircuitM Uint64 :=
  ledgerRead Uint64 fun es => [
    .dup 0,
    .idx false false s.path,
    .size,
    .popeq true [.bytes 8] es]

def isEmpty (s : Set α) : CircuitM Boolean :=
  ledgerRead Boolean fun es => [
    .dup 0,
    .idx false false s.path,
    .size,
    .push false { align := [.bytes 8], vals := [.const 0] },
    .eq,
    .popeq true [.bytes 1] es]

/-- Make the set empty. -/
def resetToDefault (s : Set α) : CircuitM Unit :=
  ledgerOp [] (resetOps s.path .emptyMap)
end Set

/-! ## Standard library types -/

/-- Compact's `ContractAddress`: a structure holding 32 bytes. -/
structure ContractAddress where
  bytes : Bytes 32
  deriving Inhabited

instance : Value ContractAddress where
  shape := .struct "ContractAddress" ["bytes"] [.prim (.bytes 32)]
  toExprs a := a.bytes.limbs
  ofExprs xs := ⟨⟨xs.take (byteLimbs 32)⟩⟩

instance : CmpEq ContractAddress ContractAddress := ⟨valueEq⟩

/-- Compact's `MerkleTreeDigest`: a Merkle tree root, one field element. -/
structure MerkleTreeDigest where
  field : Field
  deriving Inhabited

instance : Value MerkleTreeDigest where
  shape := .struct "MerkleTreeDigest" ["field"] [.prim .field]
  toExprs d := [d.field.expr]
  ofExprs xs := ⟨⟨xs.headD (.const 0)⟩⟩

instance : CmpEq MerkleTreeDigest MerkleTreeDigest := ⟨valueEq⟩

/-- Compact's `Uint<128>`, the type of shielded coin values and unshielded amounts. -/
abbrev Uint128 := Uint 340282366920938463463374607431768211455

/-- Compact's `UserAddress`: the address of an unshielded-token holder, 32 bytes. -/
structure UserAddress where
  bytes : Bytes 32
  deriving Inhabited

instance : Value UserAddress where
  shape := .struct "UserAddress" ["bytes"] [.prim (.bytes 32)]
  toExprs a := a.bytes.limbs
  ofExprs xs := ⟨⟨xs.take (byteLimbs 32)⟩⟩

instance : CmpEq UserAddress UserAddress := ⟨valueEq⟩

/-- Compact's `Either<A, B>`: a flag and both values; the one not chosen is zero. -/
structure Either (α β : Type) where
  isLeft : Boolean
  left : α
  right : β

instance [Value α] [Value β] : Value (Either α β) where
  shape := .struct "Either" ["is_left", "left", "right"] [.prim .bool, Value.shape α, Value.shape β]
  toExprs e := e.isLeft.expr :: Value.toExprs e.left ++ Value.toExprs e.right
  ofExprs xs :=
    let (l, rest) := Value.take α xs.tail
    ⟨⟨xs.headD (.const 0)⟩, l, Value.ofExprs rest⟩

instance [Value α] [Value β] : CmpEq (Either α β) (Either α β) := ⟨valueEq⟩

/-- How the kernel names a token type: `left(color)` for an unshielded token
    (Compact's `TokenType`, an `Either<Bytes<32>, Bytes<32>>`). -/
abbrev TokenType := Either (Bytes 32) (Bytes 32)

/-- The largest encoded size of a value with this alignment, as the runtime's
    `maxAlignedSize` computes it: 2, plus 34 per field element and `n + 2 + k`
    per `n`-byte atom, `k` the bytes needed to write `n` (at least 1). Checked
    against the runtime for byte lengths 0 to 20000. -/
def maxAlignedSize (align : List Zkir.AlignAtom) : Nat :=
  2 + (align.map fun
    | .bytes n => n + 2 + max 1 ((bitLen n + 7) / 8)
    | .field | .compress => 34).sum

/-! ## List

Stored as `[head, tail, length]`; the empty list is `[null, null, 0]`. Named
`LedgerList` so as not to shadow Lean's `List`. -/

/-- Compact's `List<α>`: a ledger list, pushed and popped at the front. -/
structure LedgerList (α : Type) where
  index : Nat
  path : LedgerPath := [fieldKey index]

namespace LedgerList
def initial : StateLit Expr := .array [.null, .null, .cell (u64 (.const 0))]
end LedgerList

instance [Value α] : LedgerType (LedgerList α) where
  ofIndex i := { index := i }
  decl l name := { name, index := l.index, kind := .list (Value.shape α) }

instance [Value α] : MapValue (LedgerList α) where
  kind := .list (Value.shape α)
  initial := LedgerList.initial
  lookup i path k := pure { index := i, path := path ++ [k] }

namespace LedgerList
variable [Value α]

def pushFront (l : LedgerList α) (x : α) : CircuitM Unit :=
  ledgerOp [] [
    .idx false true l.path,
    .dup 0,
    .idx false false [slot 2],
    .addi (.const 1),
    .pushState true (.array [.cell (alignedOf x), .null, .null]),
    .swap 0,
    .push false (slot 2),
    .swap 0,
    .ins true 1,
    .swap 0,
    .push false (slot 1),
    .swap 0,
    .ins true (l.path.length + 1)]

/-- Replace the list by its tail. -/
def popFront (l : LedgerList α) : CircuitM Unit :=
  ledgerOp [] [
    .idx false true l.path,
    .idx false false [slot 1],
    .ins true l.path.length]

/-- The first element, if there is one. -/
def head (l : LedgerList α) : CircuitM (Maybe α) :=
  ledgerRead (Maybe α) fun es => [
    .dup 0,
    .idx false false l.path,
    .idx false false [slot 0],
    .dup 0,
    .type,
    .push false (slot 1),
    .eq,
    .branch 4,
    .push false (slot 1),
    .swap 0,
    .concat (2 + maxAlignedSize (alignOf α)),
    .jmp 2,
    .pop,
    .push false (alignedOf (Maybe.none : Maybe α)),
    .popeq true (alignOf (Maybe α)) es]

def length (l : LedgerList α) : CircuitM Uint64 :=
  ledgerRead Uint64 fun es => [
    .dup 0,
    .idx false false l.path,
    .idx false false [slot 2],
    .popeq true [.bytes 8] es]

def isEmpty (l : LedgerList α) : CircuitM Boolean :=
  ledgerRead Boolean fun es => [
    .dup 0,
    .idx false false l.path,
    .idx false false [slot 1],
    .type,
    .push false (slot 1),
    .eq,
    .popeq true [.bytes 1] es]

def resetToDefault (l : LedgerList α) : CircuitM Unit :=
  ledgerOp [] (resetOps l.path initial)
end LedgerList

/-! ## Merkle trees

A `MerkleTree` is stored as `[tree, firstFree]`, a `HistoricMerkleTree` as
`[tree, firstFree, pastRoots]`. Leaves are hashed in the circuit with the
persistent hash under the domain separator `mdn:lh`. Reading the root or a
path is not a circuit operation in Compact (they are TypeScript-only); a
circuit that needs a path takes it from a witness. -/

/-- The hash a value is stored under in a Merkle tree. -/
def leafHash [Value α] (x : α) : Bytes 32 :=
  let align := .bytes 6 :: alignOf α
  let xs := (Bytes.pad 6 "mdn:lh").limbs ++ Value.toExprs x
  ⟨[.phash true align xs, .phash false align xs]⟩

/-- Compact's `MerkleTree<depth, α>`. -/
structure MerkleTree (depth : Nat) (α : Type) where
  index : Nat
  path : LedgerPath := [fieldKey index]

/-- Compact's `HistoricMerkleTree<depth, α>`: also remembers past roots. -/
structure HistoricMerkleTree (depth : Nat) (α : Type) where
  index : Nat
  path : LedgerPath := [fieldKey index]

namespace MerkleTreeOps

/-- The initial state; a historic tree also has an (empty) map of past roots. -/
def initial (depth : Nat) (historic : Bool) : StateLit Expr :=
  .array ([.emptyMerkleTree depth, .cell (u64 (.const 0))] ++ if historic then [.emptyMap] else [])

/-- Store `leaf` at the first free index and advance it; `finish` writes the
    tree back. -/
def insertAt (path : LedgerPath) (leaf : Bytes 32) (finish : List (Op Expr)) : List (Op Expr) :=
  [.idx false true path,
   .idx false true [slot 0],
   .dup 2,
   .idx false false [slot 1],
   .push true (alignedOf leaf),
   .ins false 1,
   .ins true 1,
   .idx false true [slot 1],
   .addi (.const 1)] ++ finish

/-- Store `leaf` at index `i` and raise the first free index past it. -/
def insertIndexAt (path : LedgerPath) (leaf : Bytes 32) (i : Uint64) (finish : List (Op Expr)) :
    List (Op Expr) :=
  [.idx false true path,
   .idx false true [slot 0],
   .push false (u64 i.expr),
   .push true (alignedOf leaf),
   .ins false 2,
   .idx false true [slot 1],
   .push false (u64 i.expr),
   .addi (.const 1),
   .dup 1,
   .dup 1,
   .lt,
   .branch 2,
   .pop,
   .jmp 2,
   .swap 0,
   .pop,
   .ins false 1] ++ finish

/-- Record the current root among the past roots (with the tree array on top
    of the stack). -/
def recordRoot : List (Op Expr) :=
  [.idx false true [slot 2],
   .dup 2,
   .idx false false [slot 0],
   .root,
   .pushNull true,
   .ins false 1]

def isFull (path : LedgerPath) (depth : Nat) (es : List Expr) : List (Op Expr) :=
  [.dup 0,
   .idx false false path,
   .idx false false [slot 1],
   .push false (u64 (.const (2 ^ depth))),
   .lt,
   .neg,
   .popeq true [.bytes 1] es]

def checkDepth (depth : Nat) : CircuitM Unit := do
  unless depth ≤ 15 do
    buildError s!"resetToDefault on a Merkle tree of depth {depth}: compactc 0.36.1 can only \
      encode an empty tree of depth at most 15 in a circuit"
end MerkleTreeOps

instance [Value α] : LedgerType (MerkleTree depth α) where
  ofIndex i := { index := i }
  decl t name := { name, index := t.index, kind := .merkleTree depth (Value.shape α) }

instance [Value α] : LedgerType (HistoricMerkleTree depth α) where
  ofIndex i := { index := i }
  decl t name := { name, index := t.index, kind := .historicMerkleTree depth (Value.shape α) }

instance [Value α] : MapValue (MerkleTree depth α) where
  kind := .merkleTree depth (Value.shape α)
  initial := MerkleTreeOps.initial depth false
  lookup i path k := pure { index := i, path := path ++ [k] }

/-- Unlike a top-level field or `resetToDefault`, `insertDefault` of a historic
    tree into a map does not record the empty root (as compactc 0.36.1 emits it). -/
instance [Value α] : MapValue (HistoricMerkleTree depth α) where
  kind := .historicMerkleTree depth (Value.shape α)
  initial := MerkleTreeOps.initial depth true
  lookup i path k := pure { index := i, path := path ++ [k] }

namespace MerkleTree
open MerkleTreeOps
variable [Value α]

def insertHash (t : MerkleTree depth α) (h : Bytes 32) : CircuitM Unit :=
  ledgerOp [] (insertAt t.path h [.ins true (t.path.length + 1)])

def insert (t : MerkleTree depth α) (x : α) : CircuitM Unit :=
  t.insertHash (leafHash x)

def insertHashIndex (t : MerkleTree depth α) (h : Bytes 32) (i : Uint64) : CircuitM Unit :=
  ledgerOp [] (insertIndexAt t.path h i [.ins true t.path.length])

def insertIndex (t : MerkleTree depth α) (x : α) (i : Uint64) : CircuitM Unit :=
  t.insertHashIndex (leafHash x) i

/-- Store the hash of the default value at `i`, which emulates removing a leaf. -/
def insertIndexDefault (t : MerkleTree depth α) (i : Uint64) : CircuitM Unit :=
  t.insertIndex (Value.zero α) i

def isFull (t : MerkleTree depth α) : CircuitM Boolean :=
  ledgerRead Boolean (MerkleTreeOps.isFull t.path depth)

/-- Whether `r` is the tree's current root. -/
def checkRoot (t : MerkleTree depth α) (r : MerkleTreeDigest) : CircuitM Boolean :=
  ledgerRead Boolean fun es => [
    .dup 0,
    .idx false false t.path,
    .idx false false [slot 0],
    .root,
    .push false (alignedOf r),
    .eq,
    .popeq true [.bytes 1] es]

def resetToDefault (t : MerkleTree depth α) : CircuitM Unit := do
  checkDepth depth
  ledgerOp [] (resetOps t.path (initial depth false))
end MerkleTree

namespace HistoricMerkleTree
open MerkleTreeOps
variable [Value α]

def insertHash (t : HistoricMerkleTree depth α) (h : Bytes 32) : CircuitM Unit :=
  ledgerOp [] (insertAt t.path h ([.ins true 1] ++ recordRoot ++ [.ins true (t.path.length + 1)]))

def insert (t : HistoricMerkleTree depth α) (x : α) : CircuitM Unit :=
  t.insertHash (leafHash x)

def insertHashIndex (t : HistoricMerkleTree depth α) (h : Bytes 32) (i : Uint64) : CircuitM Unit :=
  ledgerOp [] (insertIndexAt t.path h i (recordRoot ++ [.ins true (t.path.length + 1)]))

def insertIndex (t : HistoricMerkleTree depth α) (x : α) (i : Uint64) : CircuitM Unit :=
  t.insertHashIndex (leafHash x) i

def insertIndexDefault (t : HistoricMerkleTree depth α) (i : Uint64) : CircuitM Unit :=
  t.insertIndex (Value.zero α) i

def isFull (t : HistoricMerkleTree depth α) : CircuitM Boolean :=
  ledgerRead Boolean (MerkleTreeOps.isFull t.path depth)

/-- Whether `r` is the current root or a remembered past one. -/
def checkRoot (t : HistoricMerkleTree depth α) (r : MerkleTreeDigest) : CircuitM Boolean :=
  ledgerRead Boolean fun es => [
    .dup 0,
    .idx false false t.path,
    .idx false false [slot 2],
    .push false (alignedOf r),
    .member,
    .popeq true [.bytes 1] es]

/-- Forget the past roots, keeping only the current one. -/
def resetHistory (t : HistoricMerkleTree depth α) : CircuitM Unit :=
  ledgerOp [] [
    .idx false true t.path,
    .push false (slot 2),
    .pushState true .emptyMap,
    .dup 2,
    .idx false false [slot 0],
    .root,
    .pushNull true,
    .ins true (t.path.length + 2)]

def resetToDefault (t : HistoricMerkleTree depth α) : CircuitM Unit := do
  checkDepth depth
  ledgerOp [] (resetOps t.path (initial depth true)
    [.idx false true [slot 2], .dup 2, .idx false false [slot 0], .root, .pushNull true, .ins true 2])
end HistoricMerkleTree

/-! ## Kernel

Operations on the transaction's context rather than on a ledger field. The
context sits two below the contract state on the VM stack, hence `dup 2`; the
effects (what the transaction claims, mints and moves) one below, which the
coin operations bring to the top with `swap 0`. Each sequence is the one
compactc 0.36.1 emits (`docs/tokens.md` has the evidence). -/

namespace Kernel

/-- The address of this contract. -/
def self : CircuitM ContractAddress :=
  ledgerRead ContractAddress fun es => [
    .dup 2,
    .idx true false [slot 0],
    .popeq true [.bytes 32] es]

/-- Commit the effects so far: later failures no longer undo them. -/
def checkpoint : CircuitM Unit :=
  ledgerOp [] [.ckpt]

/-- Add `key` to the set held in effects slot `k`. -/
private def claimIn (k : Nat) (key : Bytes 32) : CircuitM Unit :=
  ledgerOp [] [
    .swap 0,
    .idx true true [slot k],
    .push false (alignedOf key),
    .pushNull false,
    .ins true 2,
    .swap 0]

/-- Add `amount` to the entry `key` of the map held in effects slot `k`,
    creating the entry if it is absent. -/
private def addIn (k : Nat) (key : Aligned Expr) (amount : Aligned Expr) : CircuitM Unit :=
  ledgerOp [] [
    .swap 0,
    .idx true true [slot k],
    .push false key,
    .dup 1,
    .dup 1,
    .member,
    .push false amount,
    .swap 0,
    .neg,
    .branch 4,
    .dup 2,
    .dup 2,
    .idxStack [],
    .add,
    .ins true 2,
    .swap 0]

/-- Require the transaction to contain the nullifier `n`, claimed by no other call. -/
def claimZswapNullifier (n : Bytes 32) : CircuitM Unit := claimIn 0 n

/-- Require the transaction to contain an output with commitment `cm`, which this
    call claims as received. -/
def claimZswapCoinReceive (cm : Bytes 32) : CircuitM Unit := claimIn 1 cm

/-- Require the transaction to contain an output with commitment `cm`, which this
    call claims as spent (created) by the contract. -/
def claimZswapCoinSpend (cm : Bytes 32) : CircuitM Unit := claimIn 2 cm

/-- Mint `amount` shielded coins of the token type derived from this contract's
    address and `domainSep`. -/
def mintShielded (domainSep : Bytes 32) (amount : Uint64) : CircuitM Unit :=
  addIn 4 (alignedOf domainSep) (u64 amount.expr)

/-- Mint `amount` unshielded coins of the token type derived from this
    contract's address and `domainSep`. -/
def mintUnshielded (domainSep : Bytes 32) (amount : Uint64) : CircuitM Unit :=
  addIn 5 (alignedOf domainSep) (u64 amount.expr)

private def u128 (e : Expr) : Aligned Expr := { align := [.bytes 16], vals := [e] }

/-- Authorise `amount` unshielded coins of `tokenType` to go to `recipient`. -/
def claimUnshieldedCoinSpend (tokenType : TokenType) (recipient : Either ContractAddress UserAddress)
    (amount : Uint128) : CircuitM Unit :=
  addIn 8 (alignedOf (tokenType, recipient)) (u128 amount.expr)

/-- Count `amount` unshielded coins of `tokenType` as leaving the contract. -/
def incUnshieldedOutputs (tokenType : TokenType) (amount : Uint128) : CircuitM Unit :=
  addIn 7 (alignedOf tokenType) (u128 amount.expr)

/-- Count `amount` unshielded coins of `tokenType` as coming into the contract. -/
def incUnshieldedInputs (tokenType : TokenType) (amount : Uint128) : CircuitM Unit :=
  addIn 6 (alignedOf tokenType) (u128 amount.expr)

/-- Record, in effects slot 3 (the claimed contract calls), a call of the
    circuit whose entry point is `entryPoint` on the contract at `address`, with
    communication commitment `comm`: Compact's
    `kernel.claimContractCall(address, entryPoint, comm)`. The key is the
    triple appended to the set's current size (`concat cached 160`); the ledger
    matches it against the called contract's own transcript. The sequence is
    the one compactc 0.36.1 emits for every cross-contract call
    (`docs/calls.md`). -/
def claimContractCall (address : ContractAddress) (entryPoint : Bytes 32) (comm : Field) :
    CircuitM Unit :=
  ledgerOp [] [
    .swap 0,
    .idx true true [slot 3],
    .dup 0,
    .size,
    .push false { align := [.bytes 32, .bytes 32, .field],
                  vals := address.bytes.limbs ++ entryPoint.limbs ++ [comm.expr] },
    .concatCached 160,
    .pushNull false,
    .ins true 2,
    .swap 0]

/-- Push the contract's balance of `tokenType` (0 if it has none), with the
    context `depth` below the top of the stack. -/
private def balanceOps (depth : Nat) (tokenType : TokenType) : List (Op Expr) :=
  [.dup depth,
   .idx true false [slot 5],
   .dup 0,
   .push false (alignedOf tokenType),
   .member,
   .branch 3,
   .pop,
   .push false (u128 (.const 0)),
   .jmp 1,
   .idx true false [alignedOf tokenType]]

/-- The contract's balance of `tokenType` when the transaction started. -/
def balance (tokenType : TokenType) : CircuitM Uint128 :=
  ledgerRead Uint128 fun es => balanceOps 2 tokenType ++ [.popeq true [.bytes 16] es]

/-- Whether the contract's balance of `tokenType` is below `amount`. -/
def balanceLessThan (tokenType : TokenType) (amount : Uint128) : CircuitM Boolean :=
  ledgerRead Boolean fun es =>
    balanceOps 2 tokenType ++ [.push false (u128 amount.expr), .lt, .popeq true [.bytes 1] es]

/-- Whether the contract's balance of `tokenType` is above `amount`. -/
def balanceGreaterThan (tokenType : TokenType) (amount : Uint128) : CircuitM Boolean :=
  ledgerRead Boolean fun es =>
    [.push false (u128 amount.expr)] ++ balanceOps 3 tokenType ++ [.lt, .popeq true [.bytes 1] es]

end Kernel

/-- Whether the block time is before `t` (seconds). -/
def blockTimeLt (t : Uint64) : CircuitM Boolean :=
  ledgerRead Boolean fun es => [
    .dup 2,
    .idx true false [slot 2],
    .push false (u64 t.expr),
    .lt,
    .popeq true [.bytes 1] es]

/-- Whether the block time is after `t`. -/
def blockTimeGt (t : Uint64) : CircuitM Boolean :=
  ledgerRead Boolean fun es => [
    .push false (u64 t.expr),
    .dup 3,
    .idx true false [slot 2],
    .lt,
    .popeq true [.bytes 1] es]

/-- Whether the block time is at or after `t`. -/
def blockTimeGte (t : Uint64) : CircuitM Boolean := return (← blockTimeLt t).not

/-- Whether the block time is at or before `t`. -/
def blockTimeLte (t : Uint64) : CircuitM Boolean := return (← blockTimeGt t).not

end Damp
