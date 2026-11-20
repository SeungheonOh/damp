import Damp

/-! `bench/compact/adt_merkle.compact` (Compact's examples/adt/tests/merkletree_field.compact and
historicmerkletree_field.compact as one program). -/
namespace Bench.AdtMerkle
open Damp

ledger
  path : Cell (MerkleTreePath 4 Field)
  merkleTree : MerkleTree 4 Field
  fakeRoot : MerkleTree 2 Field
  merkleTreeSmall : MerkleTree 2 Field
  partialTree : MerkleTree 4 Field
  historicMerkleTree : HistoricMerkleTree 4 Field
  historicMerkleTreeSmall : HistoricMerkleTree 2 Field
  historicPartialTree : HistoricMerkleTree 4 Field

circuit test : Unit := do
  const digest ← merkleTreePathRoot (← path.read)
  require ((← merkleTree.checkRoot digest) ==. .true) "valid root"
  require ((← merkleTree.checkRoot digest) ==. .false) "invalid root"
  const hash := Bytes.pad 32 "hash"
  merkleTree.insertHash hash
  merkleTree.insertHashIndex hash 2
  merkleTree.insertIndex 7 1
  merkleTree.insertIndexDefault 3
  for i in [0:4] do
    merkleTreeSmall.insert (Field.ofNat i)
  require ((← merkleTreeSmall.isFull) ==. .true) "tree is full"
  require ((← partialTree.isFull) ==. .false) "tree is not full"
  partialTree.insert 42
  partialTree.resetToDefault
  require ((← partialTree.isFull) ==. .false) "tree is not full"
  partialTree.insert 100

circuit test_historic : Unit := do
  const digest ← merkleTreePathRoot (← path.read)
  historicMerkleTree.insert 42
  require ((← historicMerkleTree.checkRoot digest) ==. .true) ""
  const digest2 ← merkleTreePathRoot (← path.read)
  require ((← historicMerkleTree.checkRoot digest2) ==. .false) ""
  historicMerkleTree.insert 100
  const hash := Bytes.pad 32 "hash"
  historicMerkleTree.insertHash hash
  historicMerkleTree.insertHashIndex hash 2
  historicMerkleTree.insertIndex 200 1
  historicMerkleTree.insertIndexDefault 3
  for i in [0:4] do
    historicMerkleTreeSmall.insert (Field.ofNat i)
  require ((← historicMerkleTreeSmall.isFull) ==. .true) ""
  require ((← historicPartialTree.isFull) ==. .false) ""
  historicMerkleTree.resetHistory
  historicMerkleTree.resetToDefault
  require ((← historicMerkleTree.isFull) ==. .false) ""
  historicMerkleTree.insert 500

contract adt_merkle

end Bench.AdtMerkle
