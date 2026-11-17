import Damp

/-! The Lean counterpart of `test/oracle/structures_nested.compact`: maps whose
values are ledger ADTs, so that ledger paths have more than one key. `lookup`
on such a map emits nothing; the nested operation runs on the longer path. -/
namespace Examples.StructuresNested
open Damp

ledger
  votes : Map Field Counter
  groups : Map Uint16 (Map Field Counter)
  members : Map Field (Set Field)
  queues : Map Field (LedgerList Field)
  trees : Map Field (MerkleTree 4 Field)
  hists : Map Field (HistoricMerkleTree 4 Field)

circuit vote (k : Field) (n : Uint16) : Uint64 := do
  let k := disclose k
  if% !.(← votes.member k) then votes.insertDefault k
  (← votes.lookup k).increment (disclose n)
  (← votes.lookup k).decrement 1
  (← votes.lookup k).read

circuit group (g : Uint16) (k : Field) (limit : Uint64) (reset : Boolean) : Boolean := do
  let g := disclose g
  let k := disclose k
  if% !.(← groups.member g) then groups.insertDefault g
  let inner ← groups.lookup g
  if% !.(← inner.member k) then inner.insertDefault k
  (← inner.lookup k).increment 3
  const below ← (← inner.lookup k).lessThan (disclose limit)
  if% disclose reset then do
    (← inner.lookup k).resetToDefault
    inner.remove k
  if% (← inner.isEmpty) then inner.resetToDefault
  return below

circuit join (k x : Field) (leave : Boolean) : Uint64 := do
  let k := disclose k
  if% !.(← members.member k) then members.insertDefault k
  let s ← members.lookup k
  s.insert (disclose x)
  if% disclose leave then s.remove (disclose x)
  const empty ← s.isEmpty
  if% empty then s.resetToDefault
  s.size

circuit enqueue (k x : Field) : Maybe Field := do
  let k := disclose k
  if% !.(← queues.member k) then queues.insertDefault k
  let q ← queues.lookup k
  q.pushFront (disclose x)
  const h ← q.head
  if% (← q.length) >. 2 then q.popFront
  if% (← q.isEmpty) then q.resetToDefault
  return h

circuit grow (k x : Field) (i : Uint64) (r : MerkleTreeDigest) (wipe : Boolean) : Boolean := do
  let k := disclose k
  if% !.(← trees.member k) then trees.insertDefault k
  let t ← trees.lookup k
  t.insert (disclose x)
  t.insertIndex (disclose x + 1) (disclose i)
  const ok ← t.checkRoot (disclose r)
  const full ← t.isFull
  if% disclose wipe then t.resetToDefault
  return ok ||. full

circuit hgrow (k x : Field) (i : Uint64) (r : MerkleTreeDigest) (mode : Uint8) : Boolean := do
  let k := disclose k
  if% !.(← hists.member k) then hists.insertDefault k
  let t ← hists.lookup k
  const ok ← t.checkRoot (disclose r)
  t.insert (disclose x)
  t.insertIndex (disclose x + 1) (disclose i)
  const full ← t.isFull
  if% disclose mode ==. 1 then t.resetHistory
  if% disclose mode ==. 2 then t.resetToDefault
  return ok &&. !.full

contract structures_nested

end Examples.StructuresNested
