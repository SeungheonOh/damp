import Damp
import Damp.Optimize.HashRanges

/-! Checks on dropping range checks that a later persistent hash implies
(`Circuit.hashRanges`, `--O3`), run by the build.

`Circuit.hashRanges` is proved sound relative to hash functions that refuse
inputs that do not fit their alignment (`Circuit.hashRanges_soundFor` for
`Damp.Crypto.prims`, in `Damp/Proofs/Optimize/HashRanges.lean`). The checks
below show each rule firing, each side condition blocking it (with the input
that the naive rewrite would wrongly accept), and that with hash functions that
do not check the alignment the rewritten circuit accepts more, which is why
the pass is not `Pass.Sound`. -/
namespace Examples.OptHashRanges
open Damp Damp.IR

/-- Toy hash functions that accept any input. -/
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

def observe (p : Zkir.Prims) (c : Circuit) (inputs priv : List Fr) : Option (List Nat) :=
  (c.run p inputs priv []).map fun o => o.outputs.map (·.val)

/-- The range checks of a circuit, and the ranges of its witness results. -/
private def checks (c : Circuit) : List (Expr × Range) :=
  c.body.toList.flatMap fun
    | .constrain e r => [(e, r)]
    | .witness _ _ _ outs _ => outs.filterMap fun (v, r) => r.map (Expr.var v, ·)
    | _ => []

/-- `Bytes<32>` as a hash reads it: one byte, then 31 bytes. -/
private def b32 : List Zkir.AlignAtom := [.bytes 32]

private def big : Fr := Fr.ofNat (2 ^ 248)
private def ok : Fr := Fr.ofNat 12345

/-! ### A circuit argument: `constrain`s dropped -/

-- `x1` (the top byte) and `x0` (the low 31 bytes) are range checked and then
-- hashed as a `Bytes<32>`: both checks go.
private def arg := mk 2
  [.constrain (.var 1) (.bits 8), .constrain (.var 0) (.bits 248),
   .bind 2 "h" (.phash false b32 [.var 1, .var 0])]
  [.var 2]
#guard checks (Circuit.hashRanges arg) == []
-- With Damp's hash: the same result on a fitting input, and a value the
-- dropped check refused still fails, now at the hash.
#guard observe Crypto.prims (Circuit.hashRanges arg) [ok, 1] [] == observe Crypto.prims arg [ok, 1] []
#guard observe Crypto.prims arg [big, 1] [] == none
#guard observe Crypto.prims (Circuit.hashRanges arg) [big, 1] [] == none
-- With hash functions that do not check the alignment the rewritten circuit
-- accepts `2^248`: why the pass is only sound relative to Damp's hash.
#guard observe toy arg [big, 1] [] == none
#guard (observe toy (Circuit.hashRanges arg) [big, 1] []).isSome

/-! ### Side conditions -/

-- A check narrower than the slot stays: 300 fits 248 bits, not 8.
private def narrow := mk 1
  [.constrain (.var 0) (.bits 8), .bind 1 "h" (.phash false b32 [.const 0, .var 0])]
  [.var 1]
#guard checks (Circuit.hashRanges narrow) == [(.var 0, .bits 8)]
#guard (observe Crypto.prims (mk 1 [narrow.body[1]!] [.var 1]) [Fr.ofNat 300] []).isSome
#guard observe Crypto.prims narrow [Fr.ofNat 300] [] == none

-- A variable rebound between the check and the hash: the check stays. On
-- `x0 = 2^248` the original fails at the check; without it the hash would
-- read the new value 5 and succeed.
private def rebound := mk 1
  [.constrain (.var 0) (.bits 248), .bind 0 "y" (.const 5),
   .bind 1 "h" (.phash false b32 [.const 0, .var 0])]
  [.var 1]
#guard checks (Circuit.hashRanges rebound) == [(.var 0, .bits 248)]
#guard observe Crypto.prims rebound [big] [] == none
#guard (observe Crypto.prims (mk 1 rebound.body.toList.tail [.var 1]) [big] []).isSome

-- A hash only in a witness call's arguments is not evaluated by the circuit:
-- the check stays.
private def onlyArg := mk 1
  [.constrain (.var 0) (.bits 248),
   .witness (.const 1) "w" [.phash false b32 [.const 0, .var 0]] [] (.tuple [])]
  []
#guard checks (Circuit.hashRanges onlyArg) == [(.var 0, .bits 248)]

-- A ledger statement's operands are evaluated after its reads are bound, so
-- an operand hashing a variable the statement reads does not count.
private def readThenHash := mk 1
  [.constrain (.var 0) (.bits 248),
   .ledger (.const 1) [0] [.popeq false [.field] [.var 0],
     .push false ⟨[.field], [.phash false b32 [.const 0, .var 0]]⟩]]
  []
#guard checks (Circuit.hashRanges readThenHash) == [(.var 0, .bits 248)]
-- ... while an operand hashing something else does.
private def hashInLedger := mk 2
  [.constrain (.var 1) (.bits 248),
   .ledger (.const 1) [0] [.popeq false [.field] [.var 0],
     .push false ⟨[.field], [.phash false b32 [.const 0, .var 1]]⟩]]
  []
#guard checks (Circuit.hashRanges hashInLedger) == []

/-! ### Witness results: ranges dropped -/

-- A secret key read from a witness and hashed: both ranges go.
private def wit := mk 0
  [.witness (.const 1) "sk" [] [(0, some (.bits 8)), (1, some (.bits 248))] (.prim (.bytes 32)),
   .bind 2 "pk" (.phash false b32 [.var 0, .var 1])]
  [.var 2]
#guard checks (Circuit.hashRanges wit) == []
#guard observe Crypto.prims (Circuit.hashRanges wit) [] [1, ok] == observe Crypto.prims wit [] [1, ok]
#guard observe Crypto.prims (Circuit.hashRanges wit) [] [1, big] == none
#guard observe Crypto.prims (Circuit.hashRanges wit) [] [Fr.ofNat 256, ok] == none

-- A result variable that occurs again later in the same call keeps its range:
-- the later one is what the hash reads.
private def twice := mk 0
  [.witness (.const 1) "w" [] [(0, some (.bits 248)), (0, none)] (.tuple []),
   .bind 1 "h" (.phash false b32 [.const 0, .var 0])]
  [.var 1]
#guard checks (Circuit.hashRanges twice) == [(.var 0, .bits 248)]

/-! ### A contract -/

ledger
  owner : Cell (Bytes 32)

witness secretKey : Bytes 32

/-- Publish the hash of a secret key: Compact range checks the key's two
    limbs (8 and 248 bits) when the witness returns it; the hash checks them
    again. -/
circuit claim : Unit := do
  const sk ← secretKey
  owner.write (disclose (persistentHash #v[sk, Bytes.pad 32 "opt:hash-ranges"]))

contract optHashRanges

/-- Number of ZKIR instructions of the emitted circuit (0 if it cannot be emitted). -/
def size (c : Circuit) : Nat :=
  match Emit.circuit c with
  | .ok src => src.instructions.size
  | .error _ => 0

-- `--O3` drops the key's two `constrain_bits` (64 rows of the proof system's
-- table); `--O2` keeps them.
#guard size claim.circuit.optimizeMax + 2 = size claim.circuit.optimizeFull
#guard checks claim.circuit.optimizeFull != []
#guard checks claim.circuit.optimizeMax == []

end Examples.OptHashRanges
