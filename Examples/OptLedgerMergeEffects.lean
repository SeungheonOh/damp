import Damp
import Damp.Optimize.LedgerMerge
import Damp.Ledger.Merkle

/-! Checks on `Circuit.ledgerMerge` when the first program writes the effects
(`Damp/Optimize/LedgerMerge.lean`: `effKeyOk`, `effValOk`, `idxv`, `insv`).

Between two requests the runtime decodes the effects into typed values and
re-encodes them (`decodeEffects`); inside one request the second program would
see them as the first left them. The analysis tags the effects `dec` (in the
re-encoded form) at the start of a request and keeps the tag through a write
of an entry whose key and value are already in the slot's form: a 32-byte hash
mapped to null in slots 0 to 2 (`Kernel.claimZswapNullifier`,
`claimZswapCoinReceive`, `claimZswapCoinSpend`), a 32-byte hash mapped to a
`u64` cell in slots 4 and 5 (`Kernel.mintShielded`, `mintUnshielded`, whose
`add` makes a `u64` cell). Then the first program may be merged with what
follows (`ledgerOracle_merge`, `Damp/Proofs/Ledger/OptMerge.lean`). These checks
show the merge firing, each condition stopping it, and runs through the
executor against the VM model giving the same results and failures. -/
namespace Examples.OptLedgerMergeEffects
open Damp Damp.IR Damp.Impact Damp.Ledger

private def one : Expr := .const 1
private def slot (i : Nat) : Aligned Expr := fieldKey i
private def h32 (e : Expr) : Aligned Expr := ⟨[.bytes 32], [.const 0, e]⟩
private def u64 (e : Expr) : Aligned Expr := ⟨[.bytes 8], [e]⟩

/-- `claimIn i` of `Damp/Lang/Ledger.lean`: `key ↦ null` in the set of slot `i`. -/
private def claimOps (i : Nat) (key : Aligned Expr) : List (Op Expr) :=
  [.swap 0, .idx true true [slot i], .push false key, .pushNull false, .ins true 2, .swap 0]
/-- `addIn i` of `Damp/Lang/Ledger.lean`: add `amt` at `key` in the map of slot `i`. -/
private def addOps (i : Nat) (key amt : Aligned Expr) : List (Op Expr) :=
  [.swap 0, .idx true true [slot i], .push false key, .dup 1, .dup 1, .member, .push false amt, .swap 0, .neg,
   .branch 4, .dup 2, .dup 2, .idxStack [], .add, .ins true 2, .swap 0]
/-- A cell write of field `i`. -/
private def wrOps (i : Nat) (e : Expr) : List (Op Expr) :=
  [.push false (fieldKey i), .push true ⟨[.field], [e]⟩, .ins false 1]
/-- A cell read of field `i`. -/
private def rdOps (i v : Nat) : List (Op Expr) := [.dup 0, .idx false false [fieldKey i], .popeq false [.field] [.var v]]

private def L (ops : List (Op Expr)) (rs : List Var := []) : Stmt := .ledger one rs ops

/-! ### The analysis -/

-- claims of slots 0 to 2 and mints of slots 4 and 5 keep the effects decoded
#guard mergeable (claimOps 0 (h32 (.var 0))) (claimOps 1 (h32 (.var 0)))
#guard mergeable (claimOps 2 (h32 (.var 0))) (wrOps 1 (.var 0))
#guard mergeable (addOps 4 (h32 (.var 0)) (u64 (.var 1))) (claimOps 0 (h32 (.var 0)))
#guard mergeable (addOps 5 (h32 (.var 0)) (u64 (.var 1))) (addOps 5 (h32 (.var 0)) (u64 (.var 1)))
#guard mergeable (claimOps 0 (h32 (.var 0)) ++ addOps 4 (h32 (.var 0)) (u64 (.const 3))) (rdOps 1 10)
-- a constant key or amount in the slot's form
#guard mergeable (claimOps 0 ⟨[.bytes 32], [.const 0, .const 7]⟩) (wrOps 1 (.var 0))
#guard mergeable (addOps 4 (h32 (.var 0)) (u64 (.const 3))) (wrOps 1 (.var 0))

-- the key is not of the slot's type: a `TokenType` (slots 6 to 8 are decoded only if its atoms are
-- a well-formed `TokenType`, which the analysis cannot see), or a hash of another width
#guard !mergeable (addOps 6 ⟨[.bytes 1, .bytes 32, .bytes 32], [.const 0, .const 0, .var 0, .const 0]⟩
  ⟨[.bytes 16], [.var 1]⟩) (wrOps 1 (.var 0))
#guard !mergeable (claimOps 0 ⟨[.bytes 16], [.var 0]⟩) (wrOps 1 (.var 0))
-- slot 3 (claimed contract calls): its keys are not hashes
#guard !mergeable (claimOps 3 (h32 (.var 0))) (wrOps 1 (.var 0))
-- the value is not of the slot's type: null in a mint map, a 16-byte amount in slot 4 (re-encoded as 8)
#guard !mergeable (claimOps 4 (h32 (.var 0))) (wrOps 1 (.var 0))
#guard !mergeable (addOps 4 (h32 (.var 0)) ⟨[.bytes 16], [.var 1]⟩) (wrOps 1 (.var 0))
-- the map of slot 1 written back into slot 2
#guard !mergeable [.swap 0, .idx true true [slot 1], .push false (h32 (.var 0)), .pushNull false, .ins true 1,
  .push false (slot 2), .swap 0, .ins true 1, .swap 0] (wrOps 1 (.var 0))
-- the effects replaced by something else
#guard !mergeable [.swap 0, .pop, .pushState false (.array []), .swap 0] (wrOps 1 (.var 0))

/-! ### The pass -/

private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

private def shape (c : Circuit) : String :=
  String.ofList (c.body.toList.map fun | .ledger .. => 'L' | .bind .. => 'B' | .witness .. => 'W' | _ => 'A')
private def after (c : Circuit) : String := shape c.ledgerMerge

#guard after (mk 2 [L (claimOps 0 (h32 (.var 0))), L (claimOps 1 (h32 (.var 0))), L (claimOps 2 (h32 (.var 0))),
  L (addOps 5 (h32 (.var 0)) (u64 (.var 1))), L (rdOps 1 10) [10]] [.var 10]) == "L"
-- `TokenType` keys: not merged after
#guard after (mk 2 [L (addOps 6 ⟨[.bytes 1, .bytes 32, .bytes 32], [.const 0, .const 0, .var 0, .const 0]⟩
  ⟨[.bytes 16], [.var 1]⟩), L (wrOps 1 (.var 0))] []) == "LL"
-- never moved above a witness that changes the query context (`createZswapOutput` inserts its
-- commitment into the call context, which the next statement may read), or a contract call
#guard after (mk 2 [L (claimOps 0 (h32 (.var 0))), .witness one "createZswapOutput" [.var 0] [] (.tuple []),
  L (wrOps 1 (.var 0))] []) == "LWL"
#guard after (mk 2 [L (claimOps 0 (h32 (.var 0))), .witness one "call:I.c" [.var 0] [] (.tuple []),
  L (wrOps 1 (.var 0))] []) == "LWL"
-- other witnesses are crossed
#guard after (mk 2 [L (claimOps 0 (h32 (.var 0))), .witness one "w" [.var 0] [] (.tuple []),
  L (wrOps 1 (.var 0))] []) == "LW"

/-! ### Runs through the executor against the VM model -/

private def eff₀ : SV := .array ((List.range 9).map fun i =>
  if i = 4 then .map [(⟨[.bytes 32], [7]⟩, .cell ⟨[.bytes 8], [2 ^ 64 - 2]⟩)] else .map [])

private def σ₀ : LedgerState where
  context := .array [.cell ⟨[.bytes 32], [12345]⟩, .null, .cell (AV.ofU64 7)]
  effects := eff₀
  state := .array [.null, .cell ⟨[.field], [3]⟩, .cell ⟨[.field], [4]⟩]

#guard decodeEffects σ₀.effects matches some _

private def noWitness : String → List Fr → Unit → Option (List Fr × Unit) := fun _ _ _ => some ([], ())

private def run (c : Circuit) (inputs : List Nat) : String :=
  match Exec.run Crypto.prims (oracles merkleHooks noWitness) c (inputs.map Fr.ofNat) () σ₀ with
  | none => "fails"
  | some r => reprStr (r.outputs.map (·.val), r.priv.map (·.val), r.pub.map (·.val), r.ledger.state,
      r.ledger.context, r.ledger.effects)
-- the executor's whole result, public transcript included, is the same
private def same (c : Circuit) (inputs : List Nat) : Bool := run c inputs == run c.ledgerMerge inputs

-- claims, a mint at a new key, a read: merged, same result
private def c1 := mk 2 [L (claimOps 0 (h32 (.var 0))), L (claimOps 1 (h32 (.var 0))),
  L (addOps 5 (h32 (.var 0)) (u64 (.var 1))), L (addOps 5 (h32 (.var 0)) (u64 (.var 1))), L (wrOps 2 (.var 1)),
  L (rdOps 1 10) [10]] [.var 10]
#guard after c1 == "L"
#guard run c1 [5, 6] != "fails"
#guard same c1 [5, 6]
-- the same claim twice (the second replaces the first entry)
private def c2 := mk 2 [L (claimOps 0 (h32 (.var 0))), L (claimOps 0 (h32 (.var 0))), L (rdOps 1 10) [10]] [.var 10]
#guard after c2 == "L"
#guard same c2 [5, 6]
-- a mint at a present key that overflows `u64`: fails, merged or not
private def c3 := mk 2 [L (addOps 4 (h32 (.var 0)) (u64 (.var 1))), L (wrOps 1 (.var 0))] []
#guard after c3 == "L"
#guard run c3 [7, 5] == "fails"
#guard same c3 [7, 5]
-- at a present key within range, and at an absent one
#guard run c3 [7, 1] != "fails"
#guard same c3 [7, 1]
#guard same c3 [8, 2 ^ 64 - 1]
-- an amount too wide for its alignment: the request fails, merged or not
#guard run c3 [8, 2 ^ 64] == "fails"
#guard same c3 [8, 2 ^ 64]
-- a write of a field that does not exist after the claims: fails, merged or not
private def c4 := mk 2 [L (claimOps 2 (h32 (.var 0))), L (wrOps 9 (.var 0))] []
#guard after c4 == "L"
#guard run c4 [5, 6] == "fails"
#guard same c4 [5, 6]

/-! ### Size: a chain of 32 claims, each with a write, is one request -/

private def chain (n : Nat) : Circuit :=
  mk 2 ((List.range n).flatMap fun i => [L (claimOps (i % 3) (h32 (.add (.var 0) (.const i)))), L (wrOps 1 (.var 1))]) []
#guard after (chain 32) == "L"
#guard same (chain 32) [5, 6]
#guard ((chain 400).ledgerMerge.body.toList.map fun s => match s with | .ledger _ _ ops => ops.length | _ => 0).all
  (· ≤ maxMergeOps)

end Examples.OptLedgerMergeEffects
