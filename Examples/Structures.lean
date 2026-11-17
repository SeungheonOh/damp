import Damp

/-! The Lean counterpart of `test/oracle/structures.compact`: the remaining
operations on counters, cells, maps and sets, ledger lists, Merkle trees and
the kernel operations that need no coins. -/
namespace Examples.Structures
open Damp

ledger
  count : Counter
  total : Cell Field
  book : Map Uint16 Field
  tags : Set Field
  queue : LedgerList Field
  tree : MerkleTree 4 Field
  hist : HistoricMerkleTree 4 (Bytes 32)
  owner : Cell ContractAddress

circuit tick (n : Uint16) (limit : Uint64) (reset : Boolean) : Boolean := do
  count.increment (disclose n)
  count.decrement 1
  total.write (disclose n).toField
  const below ← count.lessThan (disclose limit)
  if% disclose reset then do
    count.resetToDefault
    total.resetToDefault
  return below

circuit books (k : Uint16) (clear : Boolean) : Uint64 := do
  book.insertDefault (disclose k)
  tags.insert (disclose k).toField
  if% disclose clear then do
    book.resetToDefault
    tags.resetToDefault
  book.size

circuit enqueue (x : Field) : Maybe Field := do
  queue.pushFront (disclose x)
  queue.head

circuit dequeue : Uint64 := do
  const h ← queue.head
  if% !.(← queue.isEmpty) then queue.popFront
  if% h.isSome &&. h.value ==. (0 : Field) then queue.resetToDefault
  queue.length

circuit plant (x y : Field) (i : Uint64) (h : Bytes 32) : Boolean := do
  tree.insert (disclose x)
  tree.insertIndex (disclose y) (disclose i)
  tree.insertHash (disclose h)
  tree.insertHashIndex (disclose h) (disclose i)
  tree.insertIndexDefault (disclose i)
  tree.isFull

circuit check (r : MerkleTreeDigest) (wipe : Boolean) : Boolean := do
  const ok ← tree.checkRoot (disclose r)
  if% disclose wipe then tree.resetToDefault
  return ok

circuit record (x y h : Bytes 32) (i : Uint64) (r : MerkleTreeDigest) (mode : Uint8) : Boolean := do
  hist.insert (disclose x)
  hist.insertHash (disclose h)
  hist.insertIndex (disclose y) (disclose i)
  hist.insertHashIndex (disclose h) (disclose i)
  hist.insertIndexDefault (disclose i)
  const ok ← hist.checkRoot (disclose r)
  const full ← hist.isFull
  if% disclose mode ==. 1 then hist.resetHistory
  if% disclose mode ==. 2 then hist.resetToDefault
  return ok &&. !.full

circuit stamp (t : Uint64) : Vector Boolean 4 := do
  owner.write (← Kernel.self)
  Kernel.checkpoint
  const a ← blockTimeLt (disclose t)
  const b ← blockTimeGte (disclose t)
  const c ← blockTimeGt (disclose t)
  const d ← blockTimeLte (disclose t)
  return #v[a, b, c, d]

contract structures

end Examples.Structures
