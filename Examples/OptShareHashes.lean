import Damp

/-! Checks on one hash for both arms of a conditional (`Circuit.shareSelects`,
`Circuit.shareGuarded`, `--O3`), run by the build.

Both are proved sound for Damp's hash functions (`Circuit.shareSelects_soundFor`,
`Circuit.shareGuarded_soundFor` for `Damp.Crypto.prims`, in
`Damp/Proofs/Optimize/ShareHashes.lean`). The checks below show the rules
firing, their side conditions blocking them, and, with toy hash functions that
refuse some input regardless of its alignment, that the rewrite of a
persistent hash is not sound for every choice of hash functions: the original
fails on the hash of the arm not taken, the rewritten circuit does not compute
it. For the transient hash it is (`shareSel_hash_eval`). -/
namespace Examples.OptShareHashes
open Damp Damp.IR

/-- Toy hash functions whose persistent hash refuses any input list holding a 5. -/
def toy : Zkir.Prims where
  transientHash xs := xs.foldl (· + ·) 7
  persistentHash _ xs := if xs.any (· == 5) then none else some (List.replicate 32 (xs.length % 256))
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

/-- How many hashes the expressions of a circuit's outputs contain. -/
private partial def hashes : Expr → Nat
  | .phash _ _ xs | .hash xs => 1 + (xs.map hashes).foldl (· + ·) 0
  | .select c a b => hashes c + hashes a + hashes b
  | .add a b | .mul a b | .eq a b | .lt _ a b => hashes a + hashes b
  | .neg a | .disclose a | .divmod _ _ a => hashes a
  | _ => 0
private def outHashes (c : Circuit) : Nat := (c.outputs.map hashes).foldl (· + ·) 0

private def b32 : List Zkir.AlignAtom := [.bytes 32]
private def two : List Zkir.AlignAtom := [.bytes 32, .bytes 32]

/-! ### The conditional of two hashes -/

-- `select c (H [x0, x1, RED]) (H [x0, x1, BLUE])`: one hash, the domain
-- separator selected.
private def red : Expr := .const 1000
private def blue : Expr := .const 2000
private def sel := mk 3 []
  [.select (.var 2) (.phash false two [.var 0, .var 1, .const 0, red])
     (.phash false two [.var 0, .var 1, .const 0, blue])]
#guard outHashes sel == 2
#guard outHashes (Circuit.shareSelects sel) == 1
#guard observe Crypto.prims (Circuit.shareSelects sel) [1, 2, 1] == observe Crypto.prims sel [1, 2, 1]
#guard observe Crypto.prims (Circuit.shareSelects sel) [1, 2, 0] == observe Crypto.prims sel [1, 2, 0]
#guard observe Crypto.prims sel [1, 2, 0] != observe Crypto.prims sel [1, 2, 1]
-- An input that does not fit fails both, and so does a condition that is
-- not 0 or 1.
private def big : Fr := Fr.ofNat (2 ^ 248)
#guard observe Crypto.prims sel [1, big, 1] == none
#guard observe Crypto.prims (Circuit.shareSelects sel) [1, big, 1] == none
#guard observe Crypto.prims (Circuit.shareSelects sel) [1, 2, 2] == none

-- Not for every hash function: with `toy`, which refuses a 5, the original
-- fails on the arm not taken; the rewrite does not.
private def toySel := mk 2 []
  [.select (.var 1) (.phash false [.field, .field] [.var 0, .const 5])
     (.phash false [.field, .field] [.var 0, .const 6])]
#guard outHashes (Circuit.shareSelects toySel) == 1
#guard observe toy toySel [3, 0] == none
#guard (observe toy (Circuit.shareSelects toySel) [3, 0]).isSome

-- Side condition: inputs that differ in something other than constants stay
-- two hashes (the arm not taken could fail on its own).
private def varDiff := mk 3 []
  [.select (.var 2) (.phash false b32 [.const 0, .var 0]) (.phash false b32 [.const 0, .var 1])]
#guard outHashes (Circuit.shareSelects varDiff) == 2
-- ... and so do constants that do not fit their byte slot (the first element
-- of a `Bytes<32>` is one byte).
private def wide := mk 2 []
  [.select (.var 1) (.phash false b32 [.const 300, .var 0]) (.phash false b32 [.const 1, .var 0])]
#guard outHashes (Circuit.shareSelects wide) == 2
#guard observe Crypto.prims wide [5, 0] == none

-- The transient hash cannot fail: any inputs, exact for every hash function.
private def tr := mk 3 []
  [.select (.var 2) (.hash [.var 0, .const 7]) (.hash [.var 1, .const 7])]
#guard outHashes (Circuit.shareSelects tr) == 1
#guard observe toy (Circuit.shareSelects tr) [3, 4, 1] == observe toy tr [3, 4, 1]
#guard observe toy (Circuit.shareSelects tr) [3, 4, 0] == observe toy tr [3, 4, 0]
#guard observe toy (Circuit.shareSelects tr) [3, 4, 2] == none

-- A chain 32 deep: the rewrite is bottom up and never copies an input, so the
-- result is as large as the original.
private def nested : Nat → Expr
  | 0 => .var 0
  | n + 1 => .select (.var 1) (.hash [nested n, .const 1]) (.hash [.var 0, .const 2])
#guard outHashes (Circuit.shareSelects (mk 2 [] [nested 32])) == 32

/-! ### Ledger operands under complementary guards (`coracle.start`'s shape) -/

ledger
  state : Cell Field
  redKey : Cell (Bytes 32)
  blueKey : Cell (Bytes 32)

witness secretKey : Bytes 32

circuit start : Unit := do
  const sk ← secretKey
  if% (← state.read) ==. (0 : Field) then do
    redKey.write (disclose (persistentHash #v[sk, Bytes.pad 32 "opt:red"]))
  else do
    blueKey.write (disclose (persistentHash #v[sk, Bytes.pad 32 "opt:blue"]))

contract optShareHashes

/-- Number of `persistent_hash` instructions of the emitted circuit. -/
def persistentHashes (c : Circuit) : Nat :=
  match Emit.circuit c with
  | .ok src => (src.instructions.filter fun | .persistentHash .. => true | _ => false).size
  | .error _ => 0

#guard persistentHashes start.circuit.optimizeFull == 2
#guard persistentHashes start.circuit.optimizeMax == 1
#guard persistentHashes (Circuit.shareGuarded start.circuit.optimizeFull) == 1

-- The same public inputs and outcome, for both branches, and a key that does
-- not fit is refused by both.
private def key : List Fr := [7, 12345]
private def runStart (c : Circuit) (st : Fr) (k : List Fr) :=
  (c.run Crypto.prims [] k [st]).map Zkir.Outcome.observable
#guard runStart start.circuit.optimizeMax 0 key == runStart start.circuit 0 key
#guard runStart start.circuit.optimizeMax 1 key == runStart start.circuit 1 key
#guard (runStart start.circuit 1 key).isSome
#guard runStart start.circuit.optimizeMax 0 [7, big] == none
#guard runStart start.circuit 0 [7, big] == none

end Examples.OptShareHashes
