/-
The root of a bounded Merkle tree, filling in `Hooks.root` of the VM model.

`MerkleTree::rehash` and `MerkleTreeNode::root` in
`transient-crypto/src/merkle_tree.rs` (tag `onchain-runtime-4.0.2`): an empty
subtree (`Stub`) has root 0; a leaf, the "degraded" leaf hash
(`degrade_to_transient`: the low 31 bytes of the 32-byte hash, as a field
element); a node, `transient_hash [left, right]`. A subtree holding any leaf,
even one whose hash is zero, is a node. The `root` instruction pushes the
result as a cell aligned `[field]` (`Aligned for MerkleTreeDigest`,
`transient-crypto/src/fab.rs`).

The transient hash is Damp's Poseidon (`Damp/Crypto/Poseidon.lean`), which is
itself checked against the runtime by `test/semantics.sh`. The differential
test of the VM (`test/vm.sh`) runs with these hooks.
-/
import Damp.Ledger.Vm
import Damp.Crypto.Poseidon

namespace Damp.Ledger

/-- The root of the subtree of height `h` whose first leaf index is `base`. -/
def merkleRootAt (leaves : List (Nat × Nat)) : Nat → Nat → Fr
  | 0, base => match assocGet base leaves with
    | some hash => Fr.ofNat (hash % 2 ^ 248)
    | none => 0
  | h + 1, base =>
      if leaves.any (fun (i, _) => base ≤ i && i < base + 2 ^ (h + 1)) then
        Crypto.transientHash [merkleRootAt leaves h base, merkleRootAt leaves h (base + 2 ^ h)]
      else 0

/-- The hooks with the real Merkle root. -/
def merkleHooks : Hooks where
  root h leaves := some ⟨[.field], [(merkleRootAt leaves h 0).val]⟩

end Damp.Ledger
