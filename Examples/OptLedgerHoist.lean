import Damp
import Damp.Optimize.LedgerHoist
import Damp.Ledger.Merkle

/-! Checks on `Circuit.ledgerHoist` (`Damp/Optimize/LedgerHoist.lean`): a read
of the call context moves up, above other ledger statements, to an earlier
ledger statement with the same guard that it can be merged with; then
`Circuit.ledgerMerge` makes the two one request.

The pass is proved sound against the modelled ledger
(`Circuit.ledgerHoist_soundLedger`, `Damp/Proofs/Optimize/LedgerHoist.lean`).
These checks show it firing, each side condition stopping it, runs through the
executor against the VM model giving the same outputs, private state and ledger
state (`ledgerObservable`; the public transcript is reordered), and a chain of
32 reads within its window. -/
namespace Examples.OptLedgerHoist
open Damp Damp.IR Damp.Impact Damp.Ledger

private def key (i : Nat) : Aligned Expr := fieldKey i
private def one : Expr := .const 1

/-- `Cell.read` of field `i` into `v`, under guard `g`. -/
private def rd (g : Expr) (i v : Nat) : Stmt :=
  .ledger g [v] [.dup 0, .idx false false [key i], .popeq false [.field] [.var v]]
/-- `Cell.write` of `e` to field `i`, under guard `g`. -/
private def wr (g : Expr) (i : Nat) (e : Expr) : Stmt :=
  .ledger g [] [.push false (key i), .push true ⟨[.field], [e]⟩, .ins false 1]
/-- A read of the call context (slot `i`), cached (the context is fully cached). -/
private def ctx (g : Expr) (i v : Nat) : Stmt :=
  .ledger g [v] [.dup 2, .idx true false [key i], .popeq false [.bytes 8] [.var v]]

private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

private def shape (c : Circuit) : String :=
  String.ofList (c.body.toList.map fun s =>
    if s.ctxRead then 'C' else match s with
    | .ledger .. => 'L' | .bind .. => 'B' | .witness .. => 'W' | _ => 'A')
private def hoisted (c : Circuit) : String := shape c.ledgerHoist
private def merged (c : Circuit) : String := shape (c.ledgerHoist.ledgerMerge)

/-! ### The pass -/

-- the context read moves above two statements with another guard, next to the first read
private def c1 := mk 1 [rd one 1 10, rd (.var 0) 2 11, wr (.var 0) 3 (.var 0), ctx one 2 12]
  [.var 10, .var 11, .var 12]
#guard hoisted c1 == "LCLL"
#guard merged c1 == "LL"
-- without the pass, the merge cannot reach it
#guard shape c1.ledgerMerge == "LLC"
-- also above statements that are not ledger statements
private def c2 := mk 1 [rd one 1 10, .bind 20 "t" (.add (.var 10) (.const 1)), wr (.var 0) 3 (.var 20),
  ctx one 2 12] [.var 12, .var 20]
#guard hoisted c2 == "LCBL"
-- a read of the contract state does not move (it may see a write between)
#guard hoisted (mk 1 [rd one 1 10, wr (.var 0) 1 (.var 0), rd one 1 11] [.var 10, .var 11]) == "LLL"
-- another guard
#guard hoisted (mk 1 [rd one 1 10, wr (.var 0) 3 (.var 0), ctx (.var 0) 2 12] [.var 12]) == "LLC"
-- the read's guard uses what a statement between binds
#guard hoisted (mk 12 [rd (.var 11) 1 10, .bind 11 "t" (.const 0), ctx (.var 11) 2 12] [.var 12]) == "LBC"
#guard hoisted (mk 12 [rd (.var 11) 1 10, .bind 13 "t" (.const 0), ctx (.var 11) 2 12] [.var 12]) == "LCB"
-- a statement between uses what the read binds (here: the read's variable written back)
#guard hoisted (mk 1 [rd one 1 10, wr (.var 0) 3 (.var 12), ctx one 2 12] [.var 12]) == "LLC"
-- a witness that changes the query context in the runtime (`createZswapOutput`), or a contract call
#guard hoisted (mk 1 [rd one 1 10, .witness one "createZswapOutput" [.var 0] [] (.tuple []), ctx one 2 12]
  [.var 12]) == "LWC"
#guard hoisted (mk 1 [rd one 1 10, .witness one "call:I.c" [.var 0] [] (.tuple []), ctx one 2 12]
  [.var 12]) == "LWC"
-- the two would not merge: a first program that leaves a weak value as the state
#guard hoisted (mk 1 [.ledger one [] [.pop, .pushNull false], wr (.var 0) 3 (.var 0), ctx one 2 12]
  [.var 12]) == "LLC"

/-! ### Runs through the executor against the VM model -/

private def σ₀ : LedgerState where
  context := .array [.cell ⟨[.bytes 32], [12345]⟩, .null, .cell (AV.ofU64 7)]
  effects := .array (List.replicate 9 (.map []))
  state := .array [.null, .cell ⟨[.field], [3]⟩, .cell ⟨[.field], [4]⟩, .cell ⟨[.field], [5]⟩]

private def noWitness : String → List Fr → Unit → Option (List Fr × Unit) := fun _ _ _ => some ([], ())

private def run (c : Circuit) (inputs : List Nat) : String :=
  match Exec.run Crypto.prims (oracles merkleHooks noWitness) c (inputs.map Fr.ofNat) () σ₀ with
  | none => "fails"
  | some r => reprStr (r.ledgerObservable.1.map (·.val), r.priv.map (·.val), r.ledger.state, r.ledger.context,
      r.ledger.effects)
private def same (c : Circuit) (inputs : List Nat) : Bool :=
  run c inputs == run c.ledgerHoist inputs && run c inputs == run c.ledgerHoist.ledgerMerge inputs

#guard run c1 [1] != "fails"
#guard same c1 [1]
#guard same c1 [0]
#guard same c2 [1]
-- a write of a field that does not exist between: fails, hoisted or not
private def c3 := mk 1 [rd one 1 10, wr (.var 0) 9 (.var 0), ctx one 2 12] [.var 12]
#guard hoisted c3 == "LCL"
#guard run c3 [1] == "fails"
#guard same c3 [1]
#guard same c3 [0]
-- a context read that fails (no slot 5): fails, hoisted or not
private def c4 := mk 1 [rd one 1 10, wr (.var 0) 3 (.var 0), ctx one 5 12] [.var 12]
#guard hoisted c4 == "LCL"
#guard run c4 [1] == "fails"
#guard same c4 [1]

/-! ### Size: 32 context reads, each behind a write under another guard -/

private def chain (n : Nat) : Circuit :=
  mk 1 (rd one 1 1000 :: (List.range n).flatMap fun i => [wr (.var 0) 3 (.var 0), ctx one 2 (100 + i)])
    ((List.range n).map fun i => .var (100 + i))
-- each read joins the previous read (`LCLLCC…`), and the merge then needs 33 requests, not 65
#guard (hoisted (chain 32)).take 6 == "LCLLCC"
#guard (merged (chain 32)).length == 33
#guard (shape (chain 32).ledgerMerge).length == 65
#guard same (chain 32) [1]
#guard same (chain 32) [0]

end Examples.OptLedgerHoist
