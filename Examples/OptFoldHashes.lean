import Damp
import Damp.Optimize.FoldHashes

/-! Checks on folding hashes and `divmod` of constants (`Circuit.foldHashes`,
`Circuit.foldDivmod`), run by the build.

`Circuit.foldDivmod` is proved sound (`Circuit.foldDivmod_sound`);
`Circuit.foldHashes p` only relative to the hash functions `p` it folds with
(`Circuit.foldHashes_soundFor` in `Damp/Proofs/Optimize/FoldHashes.lean`). The
checks below show each rule firing, each side condition blocking it, and that
with other hash functions the folded circuit computes something else, which is
why `foldHashes` is not `Pass.Sound`. -/
namespace Examples.OptFoldHashes
open Damp Damp.IR

/-- Toy hash functions, different from Midnight's. -/
def toy : Zkir.Prims where
  transientHash xs := xs.foldl (· + ·) 7
  persistentHash _ xs := some (List.replicate 32 (xs.length % 256))
  transientCommit xs r := xs.foldl (· + ·) r

/-- A circuit with inputs `0..n-1`, a body and outputs. -/
private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

def observe (p : Zkir.Prims) (c : Circuit) (inputs : List Fr) : Option (List Nat) :=
  (c.run p inputs [] []).map fun o => o.outputs.map (·.val)

/-- The expressions bound by a circuit's statements, in order. -/
private def binds (c : Circuit) : List Expr :=
  c.body.toList.filterMap fun | .bind _ _ e => some e | _ => none

/-! ### `divmod` -/

private def dm := mk 1
  [.bind 1 "q" (.divmod true 8 (.const 1000)),
   .bind 2 "r" (.divmod false 8 (.const 1000)),
   .bind 3 "big" (.divmod true 249 (.const 1000)),
   .bind 4 "x" (.divmod true 8 (.var 0))]
  [.var 1, .var 2]

-- 1000 = 3·256 + 232; a `divmod` above 248 bits fails and is left alone; so is
-- one of a variable.
#guard binds (Circuit.foldDivmod dm) ==
  [.const 3, .const 232, .divmod true 249 (.const 1000), .divmod true 8 (.var 0)]
-- The circuit fails (because of `big`), before and after.
#guard observe toy dm [5] == none
#guard observe toy (Circuit.foldDivmod dm) [5] == none

/-! ### Hashes -/

private def hs := mk 1
  [.bind 1 "h" (.hash [.const 1, .const 2]),
   .bind 2 "hx" (.hash [.const 1, .var 0]),
   .bind 3 "lo" (.phash false [.field] [.const 5]),
   .bind 4 "hi" (.phash true [.field] [.const 5])]
  [.var 1, .var 2, .var 3, .var 4]

-- Folded with the toy functions: `hash [1, 2]` is 7 + 1 + 2; `phash` of one
-- element is 32 bytes of 1, read as `bytesToNatives` reads them; a hash of a
-- variable stays.
#guard binds (Circuit.foldHashes toy hs) ==
  [.const 10, .hash [.const 1, .var 0],
   canon ((Zkir.bytesToNatives (List.replicate 32 1)).getD 0 0),
   canon ((Zkir.bytesToNatives (List.replicate 32 1)).getD 1 0)]
-- At the functions it folded with, nothing observable changes ...
#guard observe toy (Circuit.foldHashes toy hs) [4] == observe toy hs [4]
#guard observe Crypto.prims (Circuit.foldHashes Crypto.prims hs) [4] == observe Crypto.prims hs [4]
-- ... but with other hash functions the folded circuit computes something else:
-- the reason `foldHashes` is only `Pass.SoundFor`.
#guard observe Crypto.prims (Circuit.foldHashes toy hs) [4] != observe Crypto.prims hs [4]

-- A persistent hash whose inputs do not fit the alignment fails, and stays:
-- 256 is not one byte.
private def bad := mk 0 [.bind 1 "h" (.phash false [.bytes 1] [.const 256])] [.var 1]
#guard binds (Circuit.foldHashes Crypto.prims bad) == [.phash false [.bytes 1] [.const 256]]
#guard observe Crypto.prims bad [] == none

/-! ### A contract: a Merkle leaf of a literal -/

ledger
  tree : MerkleTree 2 Field

/-- The leaf of `7` is a persistent hash of constants. -/
circuit addSeven : Unit := do
  tree.insert 7

contract optFoldHashes

/-- Number of ZKIR instructions of the emitted circuit (0 if it cannot be emitted). -/
def size (c : Circuit) : Nat :=
  match Emit.circuit c with
  | .ok src => src.instructions.size
  | .error _ => 0

-- `--O3` computes the leaf at compile time: `persistent_hash` and
-- `bytes_into_natives` are gone.
#guard size addSeven.circuit.optimizeMax + 2 ≤ size addSeven.circuit.optimizeFull

end Examples.OptFoldHashes
